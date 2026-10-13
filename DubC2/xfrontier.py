#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xfrontier.py -- plan-dubC2-transform, T5(iii): the zero-entropy frontier left by X-H.
#
# X-H (xhorse.py) left 13 minimal prime sets uncovered on 4 rows (5/4 at nu = 0, -1, 1/2 and
# 7/5 at nu = 0).  This driver decides each of them with the EXACT FOLLOWER AUTOMATON of the
# pseudo-orbit model (the model of xhorse.Model, DubC2.Gen.PseudoOrbit):
#
#   state = (set of current residues mod l, for each l in PM;  current y-interval [lo, hi)),
#   start = (all nonzero residues; [0, 1)),
#   s-edge: residues r -> q^{-1}(p r + s) mod l (zeros dropped), [lo, hi) -> f_s[lo, hi) cap [0, 1)
#           with f_s(y) = (p y - s - (p - q) nu)/q; the edge is absent if a set or the interval
#           becomes empty.
#
# The labelled paths from the start are exactly the admissible finite letter words, and the
# future of a word depends only on its state.  When the automaton is finite (the interval
# endpoints are forward orbits of 0 and 1 and here these orbits are finite or leave [0, 1)):
#   * every nontrivial SCC a simple cycle  =>  every infinite admissible word is eventually
#     periodic (zero entropy, countable): the hypothesis of the completeness question T5(iv).
#     Then sweep D for a GenCert certificate (gencert.fast_verdict = the Lean semantics).
#   * some SCC with two cycles  =>  read two closed walks W1, W2 at a branching state, raise them
#     to powers that fix the state's residue sets pointwise, take K = hull of their periodic points;
#     if h_Wi(K) in K the pair is a horseshoe witness (xhorse format, rechecked by xhorse.recheck,
#     emitted by `xhorse.py --emit` into DubC2/HorseshoeAtlas.lean).
#
# Controls: the certified atlas cells (xhorse.controls' list) must give finite automata with
# simple SCCs only.
#
# Usage:
#   xfrontier.py --cells               # classify the 13 cells, horseshoes + D sweep
#   xfrontier.py --controls            # certified cells: simple SCCs only
# Output: DubC2/data/transform/xh/xh_frontier.jsonl  (witness records, read by xhorse --emit)
#         DubC2/data/transform/xh/xz_frontier.jsonl  (one classification record per cell)

import argparse
import itertools
import json
import math
import os
import sys
import time
from collections import deque
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xhorse as xh  # noqa: E402

OUT = xh.OUT


# ------------------------------------------------------------------ the follower automaton

def follower(m, cap=300_000):
    """exact follower automaton of the model m (xhorse.Model); (states, adj, cut)."""
    def step(st, s):
        lo, hi = st[-1]
        lo2 = max(Fraction(0), (m.p * lo - s - m.c) / m.q)
        hi2 = min(Fraction(1), (m.p * hi - s - m.c) / m.q)
        if lo2 >= hi2:
            return None
        res = []
        for l, msk in zip(m.PM, st[:-1]):
            qi, n = m.qi[l], 0
            for r in range(1, l):
                if msk >> r & 1:
                    r2 = (m.p * r + s) * qi % l
                    if r2:
                        n |= 1 << r2
            if not n:
                return None
            res.append(n)
        return tuple(res) + ((lo2, hi2),)
    s0 = tuple(m.full[l] for l in m.PM) + ((Fraction(0), Fraction(1)),)
    idx, states, adj = {s0: 0}, [s0], []
    i = 0
    while i < len(states):
        e = []
        for s in m.alph:
            t = step(states[i], s)
            if t is None:
                continue
            if t not in idx:
                idx[t] = len(states)
                states.append(t)
                if len(states) > cap:
                    return states, adj, True
            e.append((s, idx[t]))
        adj.append(e)
        i += 1
    return states, adj, False


def sccs(n, adj):
    index, low, on, st, out, c = [None] * n, [0] * n, [False] * n, [], [], [0]
    for v0 in range(n):
        if index[v0] is not None:
            continue
        work = [(v0, 0)]
        while work:
            v, k = work.pop()
            if k == 0:
                index[v] = low[v] = c[0]
                c[0] += 1
                st.append(v)
                on[v] = True
            nb = [t for _, t in adj[v]]
            if k < len(nb):
                work.append((v, k + 1))
                w = nb[k]
                if index[w] is None:
                    work.append((w, 0))
                elif on[w]:
                    low[v] = min(low[v], index[w])
                continue
            for w in nb:
                if on[w]:
                    low[v] = min(low[v], low[w])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop()
                    on[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
    return out


def primitive(w):
    k = next(k for k in range(1, len(w) + 1)
             if len(w) % k == 0 and w[:k] * (len(w) // k) == w)
    p = w[:k]
    return min(tuple(p[i:] + p[:i]) for i in range(k))


def classify(states, adj):
    """(simple, primitive cycles of the simple SCCs, branching SCCs)"""
    simple, cyc, branching = True, set(), []
    for C in sccs(len(states), adj):
        S = set(C)
        e = sum(1 for v in C for _, w in adj[v] if w in S)
        if e == 0:
            continue
        if e > len(C):
            simple = False
            branching.append(C)
            continue
        v, w = C[0], []
        while True:
            (s, t), = [(s, t) for s, t in adj[v] if t in S]
            w.append(s)
            v = t
            if v == C[0]:
                break
        cyc.add(primitive(w))
    return simple, sorted(cyc, key=lambda c: (len(c), c)), branching


# ------------------------------------------------------------------ horseshoes from a branching SCC

def closed_walks(adj, S, v):
    """for each in-SCC out-edge of v, a shortest closed walk at v starting with it"""
    out = []
    for s0, t0 in adj[v]:
        if t0 not in S:
            continue
        prev, dq = {t0: None}, deque([t0])
        while dq:
            u = dq.popleft()
            if u == v:
                break
            for s, w in adj[u]:
                if w in S and w not in prev:
                    prev[w] = (u, s)
                    dq.append(w)
        if v not in prev:
            continue
        word, u = [], v
        while prev[u] is not None:
            u, s = prev[u]
            word.append(s)
        out.append([s0] + word[::-1])
    return out


def periodic_point(m, W):
    al, be = Fraction(1), Fraction(0)
    for s in W:
        al, be = al * Fraction(m.p, m.q), (m.p * be - s - m.c) / m.q
    return be / (1 - al)


def word_state(m, W):
    st = tuple((1, 0, m.full[l]) for l in m.PM)
    for s in W:
        st = m.step_masks(st, s)
        if st is None:
            return None
    return st


def residue_orbits(m, res, W):
    """per prime: {r: length of the orbit of r under the residue map of W}, r in the state's set"""
    out = []
    for l, msk in zip(m.PM, res):
        qi, d = m.qi[l], {}

        def f(r):
            for s in W:
                r = (m.p * r + s) * qi % l
            return r
        for r in range(1, l):
            if msk >> r & 1:
                o, t = 1, f(r)
                while t != r:
                    t, o = f(t), o + 1
                d[r] = o
        out.append(d)
    return out


def horseshoe(m, states, adj, branching, max_pairs=400):
    """the shortest horseshoe witness (xhorse format) read off the branching SCCs, or None.
    W_i = c_i^{k_i}, k_i = lcm over the primes of the orbit length of a chosen start residue r_l
    (the r_l minimizing |W_1| + |W_2|, primewise greedy), K = hull of the two periodic points."""
    best, tried = None, 0
    for C in branching:
        S = set(C)
        for v in C:
            if sum(1 for _, w in adj[v] if w in S) < 2:
                continue
            cs = closed_walks(adj, S, v)
            for c1, c2 in itertools.combinations(cs, 2):
                tried += 1
                if tried > max_pairs:
                    return best
                res = states[v][:-1]
                o1, o2 = residue_orbits(m, res, c1), residue_orbits(m, res, c2)
                cands = [sorted(d1, key=lambda r: (len(c1) * d1[r] + len(c2) * d2[r]))
                         for d1, d2 in zip(o1, o2)]
                k1 = k2 = 1
                for d1, d2, cr in zip(o1, o2, cands):
                    r = min(cr, key=lambda r: len(c1) * math.lcm(k1, d1[r])
                            + len(c2) * math.lcm(k2, d2[r]))
                    k1, k2 = math.lcm(k1, d1[r]), math.lcm(k2, d2[r])
                W1, W2 = tuple(c1 * k1), tuple(c2 * k2)
                if W1 + W2 == W2 + W1:
                    continue
                y1, y2 = periodic_point(m, W1), periodic_point(m, W2)
                K = (min(y1, y2), max(y1, y2))
                if not (0 <= K[0] and K[1] < 1):
                    continue
                if not (m.horse_ok(W1, K) and m.horse_ok(W2, K)):
                    continue
                st1, st2 = word_state(m, W1), word_state(m, W2)
                if st1 is None or st2 is None:
                    continue
                S1, S2 = m.fixed_sets(st1), m.fixed_sets(st2)
                if S1 is None or S2 is None or any(not (a & b) for a, b in zip(S1, S2)):
                    continue
                r0, M = m.crt(S1, S2)
                wit = dict(r0=r0, M=M, W1=list(W1), W2=list(W2), K=[str(K[0]), str(K[1])])
                if best is None or len(W1) + len(W2) < len(best["W1"]) + len(best["W2"]):
                    best = wit
    return best


# ------------------------------------------------------------------ branching witnesses (Branch.lean)

def branch_witness(m, states, adj, branching, max_pairs=400):
    """the shortest `DubC2.Gen.BranchWitness` read off a branching state v: closed walks c1, c2 at v
    with different first letters, powers A = c1^k1, B = c2^k2 fixing one residue per prime, words
    w1 = AB, w2 = BA, interval I = the state's [lo, hi) (each word maps I onto itself)."""
    best, tried = None, 0
    for C in branching:
        S = set(C)
        for v in C:
            if sum(1 for _, w in adj[v] if w in S) < 2:
                continue
            cs = closed_walks(adj, S, v)
            for c1, c2 in itertools.combinations(cs, 2):
                tried += 1
                if tried > max_pairs:
                    return best
                res = states[v][:-1]
                o1, o2 = residue_orbits(m, res, c1), residue_orbits(m, res, c2)
                k1 = k2 = 1
                rr = []
                for d1, d2 in zip(o1, o2):
                    r = min(d1, key=lambda r: len(c1) * math.lcm(k1, d1[r])
                            + len(c2) * math.lcm(k2, d2[r]))
                    k1, k2 = math.lcm(k1, d1[r]), math.lcm(k2, d2[r])
                    rr.append(r)
                A, B = list(c1) * k1, list(c2) * k2
                R, Mod = 0, 1
                for l, r in zip(m.PM, rr):
                    t = ((r - R) * pow(Mod, -1, l)) % l
                    R, Mod = R + Mod * t, Mod * l
                lo, hi = states[v][-1]
                wit = dict(R=R, w1=A + B, w2=B + A, lo=str(lo), hi=str(hi))
                if best is None or len(wit["w1"]) < len(best["w1"]):
                    best = wit
    return best


def back(m, w, y):
    """the inverse composition h_w(y), last letter first"""
    for s in reversed(w):
        y = (m.q * y + s + m.c) / m.p
    return y


def lean_fw(p, q, c, s, y):
    return (p * y - s - c) / q


def lean_branch_ok(p, q, a, b, PM, Pq, wit):
    """Python mirror of `DubC2.Gen.branchOK`"""
    c = Fraction((p - q) * a, b)
    R, w1, w2 = wit["R"], wit["w1"], wit["w2"]
    lo, hi = Fraction(wit["lo"]), Fraction(wit["hi"])

    def walk(l, r, w, i):
        inv = xh.lean_inv(q, l)
        for s in w[:i]:
            r = ((p * r + s) * inv) % l
        return r

    def ifold(w, I):
        for s in w:
            I = (max(Fraction(0), lean_fw(p, q, c, s, I[0])), min(Fraction(1), lean_fw(p, q, c, s, I[1])))
        return I

    def word_ok(w):
        for l in PM:
            r = R % l
            if walk(l, r, w, len(w)) != r or any(walk(l, r, w, i) == 0 for i in range(len(w))):
                return False
        if any(s % l == 0 for l in Pq for s in w):
            return False
        J = ifold(w, (lo, hi))
        return J[0] <= lo and hi <= J[1]

    return (len(w1) > 0 and len(w1) == len(w2) and w1 != w2
            and all(l >= 2 and q * xh.lean_inv(q, l) % l == 1 for l in PM)
            and 0 <= lo < hi <= 1 and word_ok(w1) and word_ok(w2))


def run_branch():
    """branching witnesses on every cell of xz_frontier.jsonl whose automaton branches"""
    out = []
    for line in open(os.path.join(OUT, "xz_frontier.jsonl")):
        r = json.loads(line)
        if r.get("simple") is not False:
            continue
        p, q, nu, P = r["p"], r["q"], r["nu"], r["P"]
        m = xh.Model(p, q, nu, P)
        states, adj, cut = follower(m)
        simple, cyc, branching = classify(states, adj)
        wit = branch_witness(m, states, adj, branching)
        nuf = Fraction(nu)
        ok = bool(wit) and lean_branch_ok(p, q, nuf.numerator, nuf.denominator, m.PM, m.Pq, wit)
        # boundary-degenerate iff both inverse compositions fix the excluded endpoint hi (then no
        # coded concatenation is realized by a pseudo-orbit; note §12)
        deg = None
        if wit:
            hi = Fraction(wit["hi"])
            deg = all(back(m, w, hi) == hi for w in (wit["w1"], wit["w2"]))
        rec = dict(p=p, q=q, nu=nu, P=P, witness=wit, lean_ok=ok, degenerate=deg,
                   L=len(wit["w1"]) if wit else None)
        out.append(rec)
        print(json.dumps({k: v for k, v in rec.items() if k != "witness"}), flush=True)
    with open(os.path.join(OUT, "xb_frontier.jsonl"), "w") as f:
        for rec in out:
            f.write(json.dumps(rec) + "\n")


def emit_branch(path, maxlen):
    """the branching witnesses of xb_frontier.jsonl (maximal sets, words <= maxlen) as Lean"""
    recs = [json.loads(l) for l in open(os.path.join(OUT, "xb_frontier.jsonl"))]
    recs = [r for r in recs if r["lean_ok"] and r["L"] <= maxlen]
    recs = [r for r in recs if not any((t["p"], t["q"], t["nu"]) == (r["p"], r["q"], r["nu"])
                                       and set(r["P"]) < set(t["P"]) for t in recs)]
    out = ["/-",
           "(C) 2026 Ralf Stephan, in collaboration with Claude Code.",
           "Released under CC0 1.0 Universal (public-domain dedication).",
           "See https://creativecommons.org/publicdomain/zero/1.0/",
           "-/",
           "import DubC2.Branch",
           "",
           "/-!",
           "# Branching witnesses on the frontier cells (generated)",
           "",
           "Generated by `DubC2/xfrontier.py --emit-branch` from `DubC2/data/transform/xh/"
           "xb_frontier.jsonl`:",
           "for each branching follower automaton of note §11, two loops at one state, raised to "
           "residue-fixing",
           "powers, and the state's interval.  These cells are also killed by horseshoes "
           "(`HorseshoeFrontier.lean`);",
           "the instances show that `DubC2.Gen.branchOK` is met by the generator's data.  "
           "Statements about the",
           "certificate method, not about the orbits.",
           "-/",
           "",
           "namespace DubC2.Gen.BranchFrontier",
           "",
           "open DubC2.Gen",
           ""]
    for r in recs:
        p, q, nu, P, wit = r["p"], r["q"], Fraction(r["nu"]), r["P"], r["witness"]
        a, b = nu.numerator, nu.denominator
        PM = [l for l in P if q % l]
        Pq = [l for l in P if q % l == 0]
        name = f"b{p}_{q}_{xh.nu_tag(nu)}_P" + "_".join(map(str, P))
        out.append(f"/-- Branching witness at `{p}/{q}`, `ν = {nu}`, "
                   f"`𝒫 = {{{', '.join(map(str, P))}}}` (words of length {len(wit['w1'])}). -/")
        out.append(f"def {name} : List BranchWitness :=")
        out.append("  [⟨" + xh.lean_list(PM) + ", " + xh.lean_list(Pq) + f", {wit['R']},\n    "
                   + xh.lean_list(wit["w1"]) + ",\n    " + xh.lean_list(wit["w2"]) + ",\n    "
                   + xh.lean_q(wit["lo"]) + ", " + xh.lean_q(wit["hi"]) + "⟩]")
        out.append("")
        out.append(f"/-- No certificate for `{p}/{q}`, `ν = {nu}`, with primes inside "
                   f"`{{{', '.join(map(str, P))}}}`. -/")
        out.append('@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]')
        out.append(f"theorem {name}_branch : ∀ w ∈ {name}, ∀ (P : Params) (C : Cert), P.p = {p} →")
        out.append(f"    P.q = {q} → P.a = {a} → P.b = {b} → (∀ l ∈ P.PM, l ∈ w.PM) →")
        out.append("    (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C :=")
        out.append("  not_checked_of_branchRow (by decide +kernel)")
        out.append("")
        print(f"{name}: words of length {len(wit['w1'])}")
    out.append("end DubC2.Gen.BranchFrontier")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")


# ------------------------------------------------------------------ certificate sweep over D

def d_sweep(p, q, nu, P, cap, det_limit=60_000):
    """smallest D (powers of q first, then a ladder) with a GenCert certificate, M*D <= cap"""
    import gencert
    nu = Fraction(nu)
    a, b = nu.numerator, nu.denominator
    M = math.prod(l for l in P if q % l)
    Ds = sorted({q ** k for k in range(1, 12)} | {q ** k * j for k in range(1, 6) for j in (2, 3)}
                | {4, 5, 6, 8, 10, 12, 15, 16, 20, 24, 25, 30, 32, 40, 48, 50, 60, 64})
    log = []
    for D in Ds:
        if M * D > cap:
            break
        r = gencert.fast_verdict(p, q, a, b, P, D, det_limit=det_limit)
        log.append((D, None if r is None else r["ok"]))
        if r and r["ok"]:
            return D, r, log
    return None, None, log


# ------------------------------------------------------------------ exactness at D_F (note §12)

def run_exact(nmax=12, cap_md=3_000_000):
    """on the control cells with the smallest M*D_F: the subset construction of the cell graph at
    D_F = common denominator of the follower intervals' endpoints, from ALL vertices (gencert.certify
    without core), has as many states as the follower automaton, and certifies"""
    import gencert
    seen, rows = set(), []
    for line in open(os.path.join(OUT, "xh_controls.jsonl")):
        r = json.loads(line)
        key = (r["p"], r["q"], r["nu"], tuple(r["P"]))
        if key in seen:
            continue
        seen.add(key)
        m = xh.Model(r["p"], r["q"], r["nu"], r["P"])
        st, adj, cut = follower(m)
        if cut:
            continue
        DF = math.lcm(*{e.denominator for x in st for e in x[-1]})
        rows.append((math.prod(l for l in r["P"] if r["q"] % l) * DF, key, len(st), DF))
    rows.sort()
    with open(os.path.join(OUT, "xz_exact.jsonl"), "w") as f:
        for MD, (p, q, nu, P), nF, DF in rows[:nmax]:
            if MD > cap_md:
                continue
            nuf = Fraction(nu)
            g = gencert.Model(p, q, nuf.numerator, nuf.denominator, list(P), DF)
            cert, err = gencert.certify(g, use_core=False, limit=500_000)
            rec = dict(p=p, q=q, nu=nu, P=list(P), follower_states=nF, DF=DF, MD=MD,
                       det_states=None if err else len(cert["sets"]),
                       ok=None if err else cert["ok"])
            f.write(json.dumps(rec) + "\n")
            print(json.dumps(rec), flush=True)


# ------------------------------------------------------------------ drivers

ROWS = [(5, 4, "0"), (5, 4, "-1"), (5, 4, "1/2"), (7, 5, "0")]


def xh_killed():
    """the X-H-killed prime sets of the open rows (length-bounded search, not this driver)"""
    import glob
    killed = {}
    for fn in glob.glob(os.path.join(OUT, "xh_*.jsonl")):
        if "frontier" in fn or "controls" in fn:
            continue
        for line in open(fn):
            r = json.loads(line)
            if r.get("witness") and (r.get("recheck") or [False])[0]:
                killed.setdefault((r["p"], r["q"], str(Fraction(r["nu"]))), []).append(set(r["P"]))
    return killed


def open_cells(killed, certified, decided):
    """minimal prime sets (primes <= 17) of the open rows that are neither inside a killed set
    (a horseshoe kills every subset) nor contain a certified set (a certificate for P is one
    for every superset), and not yet classified"""
    pr = xh.primes_upto(17)
    cells = []
    for key in ROWS:
        K, C = killed.get(key, []), certified.get(key, [])
        unc = [set(c) for k in range(1, len(pr) + 1) for c in itertools.combinations(pr, k)
               if not any(set(c) <= S for S in K) and not any(T <= set(c) for T in C)]
        cells += [key + (sorted(P),) for P in unc if not any(Q < P for Q in unc)
                  and key + (tuple(sorted(P)),) not in decided]
    return cells


def classify_cell(p, q, nu, P, cap_states, cap_md):
    t0 = time.time()
    m = xh.Model(p, q, nu, P)
    states, adj, cut = follower(m, cap_states)
    rec, wrec = dict(p=p, q=q, nu=nu, P=P, states=len(states), cut=cut, verdict="CUT"), None
    if not cut:
        simple, cyc, branching = classify(states, adj)
        dens = {e.denominator for st in states for e in st[-1]}
        rec.update(simple=simple, cycles=[list(c) for c in cyc],
                   max_den=max(dens), branching=len(branching))
        if simple:
            D, r, log = d_sweep(p, q, nu, P, cap_md)
            rec.update(verdict="CERTIFIED" if D else "ZERO-ENTROPY", D=D, cert=r, sweep=log)
        else:
            wit = horseshoe(m, states, adj, branching)
            rc = xh.recheck(p, q, nu, P, wit) if wit else None
            ok = bool(wit) and rc[0]
            rec.update(verdict="HORSESHOE" if ok else "BRANCHING",
                       L=(len(wit["W1"]), len(wit["W2"])) if wit else None)
            if ok:
                wrec = dict(p=p, q=q, nu=nu, P=P, lmax=None, witness=wit, recheck=rc,
                            engine=xh.engine_check(p, q, nu, P, wit, Ds=(None, 7 * p)),
                            source="follower")
    rec["secs"] = round(time.time() - t0, 1)
    return rec, wrec


def run_cells(cap_states, cap_md):
    """rounds until every set of the open rows is killed, certified, or undecided by verdict"""
    killed = xh_killed()
    certified, decided, recs, wrecs = {}, set(), [], []
    rnd = 0
    while True:
        cells = open_cells(killed, certified, decided)
        if not cells:
            break
        rnd += 1
        print(f"round {rnd}: {len(cells)} cells", flush=True)
        for p, q, nu, P in cells:
            rec, wrec = classify_cell(p, q, nu, P, cap_states, cap_md)
            rec["round"] = rnd
            recs.append(rec)
            decided.add((p, q, nu, tuple(P)))
            if rec["verdict"] == "CERTIFIED":
                certified.setdefault((p, q, nu), []).append(set(P))
            if wrec:
                wrecs.append(wrec)
                killed.setdefault((p, q, nu), []).append(set(P))
            print(json.dumps({k: v for k, v in rec.items() if k not in ("cert", "sweep")}),
                  flush=True)
    with open(os.path.join(OUT, "xh_frontier.jsonl"), "w") as fw:
        for w in wrecs:
            fw.write(json.dumps(w) + "\n")
    with open(os.path.join(OUT, "xz_frontier.jsonl"), "w") as fz:
        for r in recs:
            fz.write(json.dumps(r) + "\n")
    left = [r for r in recs if r["verdict"] not in ("CERTIFIED", "HORSESHOE")]
    print(f"DONE: {len(recs)} cells, undecided {[(r['p'], r['q'], r['nu'], r['P'], r['verdict']) for r in left]}")


def run_controls(cap_states):
    bad = 0
    import glob
    seen = set()
    for line in open(os.path.join(OUT, "xh_controls.jsonl")):
        r = json.loads(line)
        key = (r["p"], r["q"], r["nu"], tuple(r["P"]))
        if key in seen:
            continue
        seen.add(key)
        m = xh.Model(r["p"], r["q"], r["nu"], r["P"])
        states, adj, cut = follower(m, cap_states)
        simple = None if cut else classify(states, adj)[0]
        if simple is False:
            bad += 1
        print(json.dumps(dict(p=r["p"], q=r["q"], nu=r["nu"], P=r["P"], states=len(states),
                              cut=cut, simple=simple)), flush=True)
    print("CONTROL VIOLATIONS:", bad)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cells", action="store_true")
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--states", type=int, default=300_000)
    ap.add_argument("--md", type=int, default=2_000_000, help="cap on M*D in the D sweep")
    ap.add_argument("--branch", action="store_true",
                    help="branching witnesses (Branch.lean) on the branching cells")
    ap.add_argument("--emit-branch", default="", help="write them as Lean (DubC2/BranchFrontier.lean)")
    ap.add_argument("--maxlen", type=int, default=100)
    ap.add_argument("--exact", action="store_true",
                    help="det at D_F = follower automaton, on the smallest control cells")
    args = ap.parse_args()
    if args.controls:
        run_controls(args.states)
    if args.cells:
        run_cells(args.states, args.md)
    if args.branch:
        run_branch()
    if args.exact:
        run_exact()
    if args.emit_branch:
        emit_branch(args.emit_branch, args.maxlen)


if __name__ == "__main__":
    main()
