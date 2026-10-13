#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# joint.py -- plan-dubC2 milestone M1, experiment X1: REFERENCE implementation
# of the joint (q-adic x odd-residue x interval-cell) subshift  G(P, K, D)  for
#
#       x_n = [ xi (p/q)^n + nu ]  ("nearest integer" when nu = 1/2,
#                                   "floor"           when nu = 0),
#       q x_{n+1} = p x_n + s_n,   s_n = the carry.
#
# This is the *reference* of the R-6 two-implementation discipline: every
# interval computation here is done in exact `fractions.Fraction`, the core
# peel is a worklist algorithm, and the SCC decomposition is scipy's
# (Tarjan, compiled).  The sibling `joint.c` uses integer-only rational
# arithmetic, an alternating bitset peel and a hand-written iterative Tarjan.
# The two must agree on every number reported by `--summary`.
#
# ---------------------------------------------------------------- the model --
#
# Put z_n = xi (p/q)^n and y_n = { z_n + nu } in [0,1), so z_n + nu = x_n + y_n.
# From q x_{n+1} = p x_n + s_n one gets, with w := (p-q) nu,
#
#       q y_{n+1} = p y_n - w - s_n,          y_{n+1} = (p y_n - w - s_n)/q,
#
# so the letter s is admissible at y iff  y in Dom(s) := [ (s+w)/p, (s+q+w)/p )
# intersected with [0,1); these windows tile [0,1) inside each residue class of
# s mod q.  The alphabet is  S(p/q, nu) = { s in Z : Dom(s) nonempty }.
#
# ------------------------------------------------------------- the graph -----
#
# States  (u, r, c):
#   u in Z/q^K            -- the q-adic coordinate (q is assumed prime).
#                            If q in P we demand u != 0 mod q.
#   r in prod_{l in Q} Z/l, Q = { l in P : l does not divide q } -- demand r_l != 0.
#   c in {0,...,D-1}      -- the cell [c/D, (c+1)/D) of [0,1).
#
# Edges, labelled s in S(p/q,nu):
#   (carry)   p u + s = 0 mod q                      [ s = -p x_n mod q ]
#   (q-adic)  u' = ((p ut + s)/q) mod q^K  for SOME lift ut of u mod q^(K+1)
#             -- the sound stationary over-approximation of the level-consuming
#                exact map; it pins u' only mod q^(K-1).
#   (avoid q) u' != 0 mod q   when q in P
#   (residue) r'_l = q^{-1}(p r_l + s) mod l,  r'_l != 0   for every l in Q
#   (cell)    C := [c/D,(c+1)/D) meets Dom(s), and c' meets  T_s(C n Dom(s)).
#
# Soundness (plan sec.4.1): if x_n avoids P for all n >= N then
# n |-> (x_n mod q^K, x_n mod prod Q, cell_D(y_n)) is an infinite path in G
# whose labels are the true carries.  Over-approximation only ever ADDS paths,
# so certificates are one-sided: they prove unavoidability, never avoidability.
# `--sound` runs the empirical check of this lemma on real orbits.
#
# ------------------------------------------------------------- the verdict ---
#
# Peel to the bi-infinite core (alternating forward/backward fixpoint), then
#   C(P) HOLDS  <=>  every cyclic SCC of the core is a simple cycle
#               <=>  no core vertex has >= 2 successors inside its own SCC
#               <=>  rho(core) = 1 exactly.
# By [DN05] Lemma 2 (= Z32.not_isEventuallyPeriodic_carry, proved nu-generally
# in this corpus) no real orbit has an eventually periodic carry word, so
# C(P) HOLDS is exactly the certificate that P is unavoidable.
#
# Usage:
#   ./joint.py --pq 3 2 --nu 1/2 --P 2,5,7,11 --K 2 --k 6 [--summary] [--dump f]
#   ./joint.py --preset dn05-53 | --preset dn05-75 | --preset fs67-32
#   ./joint.py --pq 3 2 --nu 1/2 --P 2,3 --branch-table     # sec.1.1, exact
#   ./joint.py --pq 3 2 --nu 1/2 --P 2,5,7,11 --K 2 --k 4 --sound 2000

import argparse
import json
import sys
from fractions import Fraction

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components


# --------------------------------------------------------------------------
# alphabet and branch table, in exact rationals
# --------------------------------------------------------------------------

def alphabet(p, q, nu):
    """S(p/q, nu) = { s : Dom(s) n [0,1) nonempty }, with Dom as above."""
    w = Fraction(p - q) * nu
    out = []
    s = -(p + q + 2)
    while s <= p + q + 2:
        lo, hi = dom(p, q, nu, s)
        if lo < hi:
            out.append(s)
        s += 1
    assert out and out == list(range(out[0], out[-1] + 1)), (out, w)
    return out


def dom(p, q, nu, s):
    """Dom(s) n [0,1) as a pair of Fractions [lo, hi)."""
    w = Fraction(p - q) * nu
    lo = max(Fraction(0), (Fraction(s) + w) / p)
    hi = min(Fraction(1), (Fraction(s + q) + w) / p)
    return lo, hi


def branch_map(p, q, nu, s, y):
    """T_s(y) = (p y - w - s)/q."""
    w = Fraction(p - q) * nu
    return (Fraction(p) * y - w - s) / q


def print_branch_table(p, q, nu):
    w = Fraction(p - q) * nu
    print(f"# branch table for base {p}/{q}, nu = {nu}   (w = (p-q)nu = {w})")
    print(f"# alphabet S({p}/{q},{nu}) = {alphabet(p,q,nu)}")
    print(f"{'s':>4}  {'x_n mod q':>9}  {'domain of y_n':>21}  {'image':>21}")
    for s in alphabet(p, q, nu):
        lo, hi = dom(p, q, nu, s)
        ilo = branch_map(p, q, nu, s, lo)
        ihi = branch_map(p, q, nu, s, hi)
        xmod = (-s * pow(p, -1, q)) % q if q > 1 else 0
        print(f"{s:>4}  {xmod:>9}  [{str(lo):>9}, {str(hi):>9})  "
              f"[{str(ilo):>9}, {str(ihi):>9})")


# --------------------------------------------------------------------------
# per-coordinate transition tables
# --------------------------------------------------------------------------

def cell_table(p, q, nu, D, letters):
    """For each letter s and cell c, the contiguous range [j0, j1) of target
    cells.  Exact Fraction arithmetic; empty ranges are marked j0 = j1 = -1."""
    tab = {}
    for s in letters:
        dlo, dhi = dom(p, q, nu, s)
        rng = np.full((D, 2), -1, dtype=np.int64)
        # only cells meeting [dlo,dhi) can fire
        c0 = int(dlo * D)                       # floor, dlo >= 0
        c1 = -((-dhi * D).__ceil__()) if False else None
        c1 = int(dhi * D) if (dhi * D).denominator == 1 else int(dhi * D) + 1
        for c in range(max(0, c0), min(D, c1)):
            a = max(Fraction(c, D), dlo)
            b = min(Fraction(c + 1, D), dhi)
            if a >= b:
                continue
            ilo = branch_map(p, q, nu, s, a) * D
            ihi = branch_map(p, q, nu, s, b) * D
            j0 = int(ilo) if ilo >= 0 else -((-ilo).__ceil__())
            j0 = ilo.__floor__()
            j1 = ihi.__ceil__()
            j0 = max(0, j0)
            j1 = min(D, j1)
            if j0 < j1:
                rng[c, 0] = j0
                rng[c, 1] = j1
        tab[s] = rng
    return tab


def qadic_table(p, q, K, avoid_q, letters):
    """For each letter s: list of (u, u') with u ranging over the allowed
    residues mod q^K.  Sound over-approximation via all q lifts mod q^(K+1)."""
    qK, qK1 = q ** K, q ** (K + 1)
    us = [u for u in range(qK) if not (avoid_q and u % q == 0)]
    tab = {}
    for s in letters:
        succ = {}
        for u in us:
            if (p * u + s) % q != 0:
                continue
            outs = []
            for j in range(q):
                ut = u + j * qK
                t = (p * ut + s) % qK1
                assert t % q == 0
                u2 = (t // q) % qK
                if avoid_q and u2 % q == 0:
                    continue
                outs.append(u2)
            if outs:
                succ[u] = sorted(set(outs))
        tab[s] = succ
    return tab, us


def residue_table(p, q, Q, letters):
    """Mixed-radix residue coordinate over Q = { l in P : l !| q }.
    r'_l = q^{-1}(p r_l + s) mod l, all coordinates nonzero."""
    if not Q:
        return {s: np.zeros(1, dtype=np.int64) for s in letters}, 1, [0]
    radices = [l - 1 for l in Q]              # nonzero residues per prime
    R = 1
    for x in radices:
        R *= x
    # index <-> tuple of residues in {1,...,l-1}
    def to_tuple(i):
        t = []
        for l in Q:
            t.append(i % (l - 1) + 1)
            i //= (l - 1)
        return tuple(t)

    def to_index(t):
        i, mul = 0, 1
        for l, v in zip(Q, t):
            i += (v - 1) * mul
            mul *= (l - 1)
        return i

    qinv = [pow(q, -1, l) for l in Q]
    tab = {}
    for s in letters:
        arr = np.full(R, -1, dtype=np.int64)
        for i in range(R):
            t = to_tuple(i)
            t2 = []
            ok = True
            for l, qi, v in zip(Q, qinv, t):
                v2 = (qi * (p * v + s)) % l
                if v2 == 0:
                    ok = False
                    break
                t2.append(v2)
            if ok:
                arr[i] = to_index(tuple(t2))
        tab[s] = arr
    return tab, R, list(range(R))


# --------------------------------------------------------------------------
# graph construction (product of the three coordinate tables)
# --------------------------------------------------------------------------

class Graph:
    __slots__ = ("n", "src", "dst", "lab", "D", "R", "us", "uidx", "meta")


def build(p, q, nu, P, K, D):
    letters = alphabet(p, q, nu)
    avoid_q = q in P
    Q = sorted(l for l in P if q % l != 0)
    assert all(q % l != 0 or l == q for l in P), "composite q with prime in P"
    ctab = cell_table(p, q, nu, D, letters)
    utab, us = qadic_table(p, q, K, avoid_q, letters)
    rtab, R, _ = residue_table(p, q, Q, letters)
    uidx = {u: i for i, u in enumerate(us)}
    U = len(us)
    n = U * R * D

    src_l, dst_l, lab_l = [], [], []
    cellidx = np.arange(D, dtype=np.int64)
    for s in letters:
        crng = ctab[s]
        live_c = np.flatnonzero(crng[:, 0] >= 0)
        if live_c.size == 0:
            continue
        rmap = rtab[s]
        live_r = np.flatnonzero(rmap >= 0)
        if live_r.size == 0:
            continue
        for u, u2s in utab[s].items():
            iu = uidx[u]
            for u2 in u2s:
                iu2 = uidx[u2]
                # product over live_r x live_c
                for c in live_c:
                    j0, j1 = int(crng[c, 0]), int(crng[c, 1])
                    ncell = j1 - j0
                    base_s = (iu * R + live_r) * D + c
                    base_d = (iu2 * R + rmap[live_r]) * D
                    for j in range(j0, j1):
                        src_l.append(base_s)
                        dst_l.append(base_d + j)
                        lab_l.append(np.full(live_r.size, s, dtype=np.int8))
    src = np.concatenate(src_l) if src_l else np.zeros(0, dtype=np.int64)
    dst = np.concatenate(dst_l) if dst_l else np.zeros(0, dtype=np.int64)
    lab = np.concatenate(lab_l) if lab_l else np.zeros(0, dtype=np.int8)

    g = Graph()
    g.n, g.src, g.dst, g.lab = n, src, dst, lab
    g.D, g.R, g.us, g.uidx = D, R, us, uidx
    g.meta = dict(p=p, q=q, nu=str(nu), P=sorted(P), Q=Q, K=K, D=D,
                  letters=letters, U=len(us), R=R, avoid_q=avoid_q)
    return g


# --------------------------------------------------------------------------
# core peel + SCC census
# --------------------------------------------------------------------------

def peel(g):
    """Alternating forward/backward fixpoint.  Worklist over degrees."""
    alive_e = np.ones(g.src.size, dtype=bool)
    alive_v = np.ones(g.n, dtype=bool)
    while True:
        outd = np.bincount(g.src[alive_e], minlength=g.n)
        ind = np.bincount(g.dst[alive_e], minlength=g.n)
        dead = alive_v & ((outd == 0) | (ind == 0))
        if not dead.any():
            break
        alive_v &= ~dead
        alive_e &= alive_v[g.src] & alive_v[g.dst]
    return alive_v, alive_e


def census(g, alive_v, alive_e):
    """Compact the core, run scipy's SCC, return the C(P) census."""
    idx = np.flatnonzero(alive_v)
    n = idx.size
    res = dict(nodes_total=int(g.n), edges_total=int(g.src.size),
               core_nodes=int(n), core_edges=int(alive_e.sum()))
    if n == 0:
        res.update(sccs=0, cyclic_sccs=0, largest_cyclic=0, branch_nodes=0,
                   branch_sccs=0, all_simple=True, verdict="EMPTY CORE",
                   lam=0.0)
        return res, idx, None, None, None, None
    remap = np.full(g.n, -1, dtype=np.int64)
    remap[idx] = np.arange(n)
    s = remap[g.src[alive_e]]
    d = remap[g.dst[alive_e]]
    lb = g.lab[alive_e]
    A = csr_matrix((np.ones(s.size, dtype=np.int8), (s, d)), shape=(n, n))
    ncc, lab = connected_components(A, directed=True, connection="strong")
    same = lab[s] == lab[d]
    in_scc_out = np.bincount(s[same], minlength=n)
    cyclic = np.unique(lab[s[same]]) if same.any() else np.empty(0, int)
    branch_nodes = np.flatnonzero(in_scc_out >= 2)
    branch_sccs = np.unique(lab[branch_nodes]) if branch_nodes.size else np.empty(0, int)
    sizes = np.bincount(lab, minlength=ncc)
    epc = np.bincount(lab[s[same]], minlength=ncc)
    all_simple = bool(np.all(epc[cyclic] == sizes[cyclic])) if cyclic.size else True
    res.update(sccs=int(ncc), cyclic_sccs=int(cyclic.size),
               largest_cyclic=int(sizes[cyclic].max()) if cyclic.size else 0,
               branch_nodes=int(branch_nodes.size),
               branch_sccs=int(branch_sccs.size),
               all_simple=all_simple)
    res["verdict"] = ("C(P) HOLDS" if branch_sccs.size == 0 and all_simple
                      else "C(P) FAILS")
    res["lam"] = spectral_radius(A, lab, sizes, cyclic, all_simple, s, d)
    return res, idx, lab, s, d, lb


def perron(nloc, edges):
    """Perron root of one strongly connected 0-1-multigraph, by power iteration
    on B = A + I (primitive, so the iteration converges) with a
    Collatz-Wielandt bracket;  rho(A) = rho(B) - 1.  A simple cycle gives
    exactly 1 in one step, with no floating point drift."""
    if nloc == 0 or not edges:
        return 0.0
    v = np.ones(nloc, dtype=np.float64)
    src = np.array([e[0] for e in edges], dtype=np.int64)
    dst = np.array([e[1] for e in edges], dtype=np.int64)
    hi = float(nloc)
    for _ in range(200000):
        w = v + np.bincount(src, weights=v[dst], minlength=nloc)
        rat = w / v
        lo, hi = float(rat.min()), float(rat.max())
        v = w / w.max()
        if hi - lo <= 1e-13 * hi:
            break
    return hi - 1.0


def spectral_radius(A, lab, sizes, cyclic, all_simple, s, d):
    """rho(core) = max over the cyclic SCCs of the Perron root of that SCC."""
    if cyclic.size == 0:
        return 0.0
    best = 0.0
    same = lab[s] == lab[d]
    ss, dd = s[same], d[same]
    for c in cyclic:
        vs = np.flatnonzero(lab == c)
        loc = {int(v): i for i, v in enumerate(vs)}
        es = [(loc[int(a)], loc[int(b)])
              for a, b in zip(ss.tolist(), dd.tolist()) if lab[a] == c]
        best = max(best, perron(vs.size, es))
    return best


def cycle_report(g, idx, lab, s, d, lb, limit=40):
    """For every cyclic SCC that is a simple cycle, return its length, the
    periodic carry word it forces, and the cells it visits.  This is the shape
    data G-3 checks: [DN05]'s 5/3 proof says the core is (A^2 B^2)^infty."""
    if lab is None:
        return []
    n = idx.size
    same = lab[s] == lab[d]
    ss, dd, ll = s[same], d[same], lb[same]
    ncc = int(lab.max()) + 1
    sizes = np.bincount(lab, minlength=ncc)
    epc = np.bincount(lab[ss], minlength=ncc)
    cyclic = np.unique(lab[ss]) if ss.size else np.empty(0, int)
    nxt = {}
    for a, b, l in zip(ss.tolist(), dd.tolist(), ll.tolist()):
        nxt.setdefault(a, []).append((b, l))
    out = []
    for c in cyclic:
        if epc[c] != sizes[c]:
            out.append(dict(scc=int(c), size=int(sizes[c]),
                            edges=int(epc[c]), word=None))
            continue
        vs = np.flatnonzero(lab == c)
        v0 = int(vs[0])
        word, cells, v = [], [], v0
        for _ in range(int(sizes[c])):
            b, l = nxt[v][0]
            word.append(int(l))
            cells.append(int(idx[v]) % g.D)
            v = b
        assert v == v0
        out.append(dict(scc=int(c), size=int(sizes[c]), edges=int(epc[c]),
                        word=word, cells=cells,
                        states=[decode(g, int(idx[x])) for x in
                                np.flatnonzero(lab == c)[:limit]]))
    return out


def decode(g, i):
    c = i % g.D
    i //= g.D
    r = i % g.R
    u = g.us[i // g.R]
    return (u, r, c)


# --------------------------------------------------------------------------
# label determinization -- the refinement M1 had to add to the plan's K-per
# --------------------------------------------------------------------------
#
# dubC1's state graph was pure residues, so a state cycle WAS a carry cycle and
# "every cyclic SCC is a simple cycle" was the right test.  With interval cells
# that is no longer true: an expanding branch T_s widens a cell by the factor
# p/q and the grid rounds the image up to the next cell, so a genuine periodic
# ORBIT appears in the graph as a tube of width ~1/(p/q - 1) cells around it.
# The tube branches -- but every branch carries the SAME letter, so the carry
# word is still forced.  Refining k does not shrink the tube (its width is a
# number of cells, not a length), which is exactly what the 7/5 ladder showed.
#
# The criterion [DN05] Lemma 2 actually needs is about the CARRY word, so test
# it there.  For each cyclic SCC C of the core, run the subset construction on
# the induced labelled subgraph starting from S_0 = C.  Determinization changes
# neither the language nor its soundness -- it is the same set of label words,
# presented right-resolvingly.  In a right-resolving presentation a simple
# cycle forces its label word, so
#
#   C_det(P):  for every cyclic SCC C of the core, every cyclic SCC of the
#              core of det(C) is a simple cycle
#
# says exactly "every infinite path has eventually periodic carry word", which
# is what Z32.not_isEventuallyPeriodic_carry contradicts.  C(P) (state form)
# implies C_det(P); the converse fails, and 7/5 is the witness.

def determinize_scc(vs, adj_by_label, cap=200000):
    """Subset construction on the induced subgraph of the vertex set `vs`,
    started from S_0 = vs.  Returns (states, edges, hit_cap)."""
    inside = set(int(v) for v in vs)
    start = frozenset(inside)
    seen = {start: 0}
    order = [start]
    edges = []            # (state index, label, state index)
    head = 0
    while head < len(order):
        S = order[head]
        head += 1
        i = seen[S]
        for s, adj in adj_by_label.items():
            T = set()
            for v in S:
                for w in adj.get(v, ()):
                    if w in inside:
                        T.add(w)
            if not T:
                continue
            T = frozenset(T)
            j = seen.get(T)
            if j is None:
                if len(order) >= cap:
                    return order, edges, True
                j = len(order)
                seen[T] = j
                order.append(T)
            edges.append((i, s, j))
    return order, edges, False


def _peel_simple(n, edges):
    """Alternating forward/backward peel on a small explicit edge list."""
    alive = set(range(n))
    E = list(edges)
    while True:
        outs = set(a for a, _, b in E if a in alive and b in alive)
        ins = set(b for a, _, b in E if a in alive and b in alive)
        dead = alive - (outs & ins)
        if not dead:
            break
        alive -= dead
    E = [(a, s, b) for a, s, b in E if a in alive and b in alive]
    return alive, E


def _scc_simple(alive, E):
    """Kosaraju on a small explicit edge list; returns component labels."""
    adj, radj = {}, {}
    for a, _, b in E:
        adj.setdefault(a, []).append(b)
        radj.setdefault(b, []).append(a)
    seen, order = set(), []
    for v in alive:
        if v in seen:
            continue
        stack = [(v, iter(adj.get(v, ())))]
        seen.add(v)
        while stack:
            x, it = stack[-1]
            for y in it:
                if y not in seen:
                    seen.add(y)
                    stack.append((y, iter(adj.get(y, ()))))
                    break
            else:
                order.append(x)
                stack.pop()
    comp, c = {}, 0
    for v in reversed(order):
        if v in comp:
            continue
        stack = [v]
        comp[v] = c
        while stack:
            x = stack.pop()
            for y in radj.get(x, ()):
                if y not in comp:
                    comp[y] = c
                    stack.append(y)
        c += 1
    return comp, c


def _rho_small(alive, inside, comp):
    """rho of the recurrent part of the determinized automaton -- the honest
    entropy of the CARRY-word subshift.  The state-graph lambda over-counts,
    because it also counts the interval tube around each orbit."""
    best = 0.0
    if not inside:
        return 0.0
    for c in set(comp[a] for a, _, _ in inside):
        vs = sorted(v for v in alive if comp.get(v) == c)
        loc = {v: i for i, v in enumerate(vs)}
        es = [(loc[a], loc[b]) for a, l, b in inside if comp[a] == c and comp[b] == c]
        best = max(best, perron(len(vs), es))
    return best


def det_census(g, idx, lab, s, d, lb, cap=200000):
    """Run C_det(P) on every cyclic SCC of the core."""
    if lab is None:
        return dict(det_verdict="EMPTY CORE", det_sccs=0, det_branch=0,
                    det_states=0, det_words=[])
    n = idx.size
    same = lab[s] == lab[d]
    ss, dd, ll = s[same], d[same], lb[same]
    ncc = int(lab.max()) + 1
    cyclic = np.unique(lab[ss]) if ss.size else np.empty(0, int)
    adj_by_label = {}
    for a, b, l in zip(ss.tolist(), dd.tolist(), ll.tolist()):
        adj_by_label.setdefault(int(l), {}).setdefault(int(a), []).append(int(b))
    tot_states = tot_branch = 0
    words, capped, lam_det = [], False, 0.0
    for c in cyclic:
        vs = np.flatnonzero(lab == c)
        sub = {l: {v: [w for w in ws if lab[w] == c]
                   for v, ws in a.items() if lab[v] == c}
               for l, a in adj_by_label.items()}
        sub = {l: {v: ws for v, ws in a.items() if ws} for l, a in sub.items()}
        sub = {l: a for l, a in sub.items() if a}
        order, edges, hit = determinize_scc(vs, sub, cap)
        capped |= hit
        alive, E = _peel_simple(len(order), edges)
        tot_states += len(alive)
        comp, nc = _scc_simple(alive, E)
        inside = [(a, l, b) for a, l, b in E if comp[a] == comp[b]]
        outdeg = {}
        for a, l, b in inside:
            outdeg[a] = outdeg.get(a, 0) + 1
        branch = [v for v, k in outdeg.items() if k >= 2]
        tot_branch += len(branch)
        lam_det = max(lam_det, _rho_small(alive, inside, comp))
        if not branch:
            for a, l, b in inside:                       # extract the words
                pass
            # each cyclic component is a simple cycle: read its label word
            cyc = {}
            for a, l, b in inside:
                cyc.setdefault(comp[a], []).append((a, l, b))
            nxt = {a: (b, l) for a, l, b in inside}
            for cc, es in cyc.items():
                v0 = es[0][0]
                w, v = [], v0
                for _ in range(len(es)):
                    v, l = nxt[v][0], nxt[v][1]
                    w.append(l)
                    if v == v0:
                        break
                words.append(dict(scc=int(c), det_cycle_len=len(w), word=w))
    return dict(det_lam=lam_det,
                det_verdict=("C_det(P) HOLDS" if tot_branch == 0 and not capped
                             else ("CAP" if capped else "C_det(P) FAILS")),
                det_branch=int(tot_branch), det_states=int(tot_states),
                det_words=words)


def cycle_witness(g, idx, lab, s, d):
    """If C(P) fails, produce a branching core vertex and two distinct cycles
    through it (the explicit avoider-generating witness)."""
    n = idx.size
    same = lab[s] == lab[d]
    in_scc_out = np.bincount(s[same], minlength=n)
    bn = np.flatnonzero(in_scc_out >= 2)
    if bn.size == 0:
        return None
    v = int(bn[0])
    adj = {}
    for a, b in zip(s[same], d[same]):
        adj.setdefault(int(a), []).append(int(b))
    outs = adj[v][:2]
    paths = []
    for start in outs:
        # BFS back to v inside the SCC
        prev, frontier = {start: None}, [start]
        while frontier and v not in prev:
            nf = []
            for x in frontier:
                for y in adj.get(x, ()):
                    if y not in prev:
                        prev[y] = x
                        nf.append(y)
            frontier = nf
        if v not in prev:
            continue
        path, x = [], v
        while x is not None:
            path.append(int(idx[x]))
            x = prev[x]
        paths.append([int(idx[v])] + list(reversed(path)))
    return dict(vertex=int(idx[v]), cycles=paths)


# --------------------------------------------------------------------------
# soundness self-test (R-3): real orbits must be paths in G
# --------------------------------------------------------------------------

def sound_check(p, q, nu, P, K, D, g, nxi=40, nmax=300, seed=1):
    """Take exact rational xi, iterate x_n = [xi (p/q)^n + nu] with integer
    arithmetic, and check that every step whose window avoids P is an edge of G."""
    import random
    rnd = random.Random(seed)
    letters = set(alphabet(p, q, nu))
    avoid_q = q in P
    Q = sorted(l for l in P if q % l != 0)
    us, uidx = g.us, g.uidx
    R, Dc = g.R, g.D
    edges = set(zip(g.src.tolist(), g.dst.tolist()))
    qK = q ** K
    nun, nud = nu.numerator, nu.denominator

    def ridx(x):
        i, mul = 0, 1
        for l in Q:
            v = x % l
            if v == 0:
                return None
            i += (v - 1) * mul
            mul *= (l - 1)
        return i

    checked = steps = 0
    for _ in range(nxi):
        A = rnd.randrange(1, 10 ** 6)
        B = rnd.randrange(1, 10 ** 6)
        num, den = A * nud + nun * B, B * nud       # xi + nu = num/den at n=0
        # x_n = floor(xi (p/q)^n + nu) = floor((A p^n nud + nun B q^n)/(B q^n nud))
        prev = None
        for n in range(nmax):
            N = A * pow(p, n) * nud + nun * B * pow(q, n)
            Dd = B * pow(q, n) * nud
            x = N // Dd
            y = Fraction(N - x * Dd, Dd)
            if avoid_q and x % q == 0:
                prev = None
                continue
            ri = ridx(x)
            if ri is None:
                prev = None
                continue
            st = (uidx[x % qK] * R + ri) * Dc + int(y * Dc)
            if prev is not None:
                steps += 1
                if (prev, st) not in edges:
                    return dict(ok=False, at=n, prev=prev, st=st, A=A, B=B)
            prev = st
            checked += 1
    return dict(ok=True, states=checked, steps=steps)


# --------------------------------------------------------------------------

PRESETS = {
    # G-3(b): [DN05] Thm 4(ii)  --  nearest integer to xi (5/3)^n, P = {2,3}
    "dn05-53":  dict(p=5, q=3, nu="1/2", P="2,3",      K=2, k=6),
    # G-3(c): [DN05] Thm 4(iii) --  nearest integer to xi (7/5)^n, P = {2,3,5,11}
    "dn05-75":  dict(p=7, q=5, nu="1/2", P="2,3,5,11", K=2, k=4),
    # G-3(d): [DN05] Thm 1 via [FS67] -- floor of xi (3/2)^n, P = {2,5,7,11}
    "fs67-32":  dict(p=3, q=2, nu="0",   P="2,5,7,11", K=2, k=10),
    # the target: nearest integer to xi (3/2)^n
    "target-32": dict(p=3, q=2, nu="1/2", P="2,5,7,11", K=2, k=10),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preset", choices=sorted(PRESETS))
    ap.add_argument("--pq", nargs=2, type=int, metavar=("P", "Q"))
    ap.add_argument("--nu", default="1/2")
    ap.add_argument("--P", default="2")
    ap.add_argument("--K", type=int, default=None)
    ap.add_argument("--k", type=int, default=None)
    ap.add_argument("--D", type=int, default=0, help="override cell count")
    ap.add_argument("--branch-table", action="store_true")
    ap.add_argument("--sound", type=int, default=0, metavar="NXI")
    ap.add_argument("--summary", action="store_true", help="one JSON line")
    ap.add_argument("--dump", default="", help="write core edge list")
    ap.add_argument("--witness", action="store_true")
    ap.add_argument("--cycles", action="store_true")
    ap.add_argument("--det", action="store_true",
                    help="also run the label-determinized C_det(P) test")
    a = ap.parse_args()

    if a.preset:
        d = PRESETS[a.preset]
        p, q = d["p"], d["q"]
        nu = Fraction(d["nu"])
        P = set(int(t) for t in d["P"].split(","))
        K = d["K"] if a.K is None else a.K
        k = d["k"] if a.k is None else a.k
    else:
        if not a.pq:
            ap.error("--pq or --preset required")
        p, q = a.pq
        nu = Fraction(a.nu)
        P = set(int(t) for t in a.P.split(","))
        K = 2 if a.K is None else a.K
        k = 4 if a.k is None else a.k

    # D = p * nud * q^k  keeps every branch breakpoint on a cell boundary
    D = a.D if a.D else p * nu.denominator * q ** k

    if a.branch_table:
        print_branch_table(p, q, nu)
        return

    g = build(p, q, nu, P, K, D)
    alive_v, alive_e = peel(g)
    res, idx, lab, s, d, lb = census(g, alive_v, alive_e)
    res.update(g.meta)
    res["impl"] = "py"
    res["k"] = k

    if a.sound:
        res["sound"] = sound_check(p, q, nu, P, K, D, g, nxi=a.sound)

    if a.dump and idx is not None and idx.size:
        with open(a.dump, "w") as f:
            f.write(f"{idx.size}\n")
            for x, y in zip(s.tolist(), d.tolist()):
                f.write(f"{x} {y}\n")

    if a.witness and res["verdict"] == "C(P) FAILS":
        res["witness"] = cycle_witness(g, idx, lab, s, d)

    if a.cycles:
        res["cycles"] = cycle_report(g, idx, lab, s, d, lb)

    if a.det:
        res.update(det_census(g, idx, lab, s, d, lb))

    if a.summary:
        print(json.dumps(res, sort_keys=True, default=str))
    else:
        for key in ("p", "q", "nu", "P", "Q", "K", "k", "D", "letters", "U", "R",
                    "nodes_total", "edges_total", "core_nodes", "core_edges",
                    "sccs", "cyclic_sccs", "largest_cyclic", "branch_nodes",
                    "branch_sccs", "all_simple", "lam", "verdict",
                    "det_states", "det_branch", "det_lam", "det_verdict"):
            if key in res:
                print(f"{key:>15} : {res[key]}")
        if "sound" in res:
            print(f"{'soundness':>15} : {res['sound']}")
        if "witness" in res:
            print(f"{'witness':>15} : {res['witness']}")
        for dw in res.get("det_words", []):
            print(f"{'det cycle':>15} : SCC {dw['scc']:>4} len "
                  f"{dw['det_cycle_len']:>4}  word {dw['word']}")
        for cy in res.get("cycles", []):
            w = cy["word"]
            print(f"{'cycle SCC ' + str(cy['scc']):>15} : size {cy['size']:>4} "
                  f"edges {cy['edges']:>4}  word "
                  f"{'BRANCHING' if w is None else w}")


if __name__ == "__main__":
    main()
