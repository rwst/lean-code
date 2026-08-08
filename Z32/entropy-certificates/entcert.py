#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# entcert.py -- plan-B10 WP3: entropy certificates for the model system of
# `Z32/ModelEntropy.lean` on an anchored window `[0, ell)`, `ell <= 1/2`.
#
# WHAT THE CERTIFICATE IS
#
# The model orbit is  2 y_{n+1} = 3 y_n - s_n  with every y_n in [0, ell).  For
# ell <= 1/2 the carry is forced into {0,1} and the whole system is the greedy
# 3/2-transformation restricted to the window.  A length-k *cylinder* -- the set
# of starting points realising a given carry word -- is an interval, and its
# image under the composed map is an interval whose LEFT endpoint is always 0
# (verified independently, `entcheck2.py` pattern: 8 windows to depth 16, zero
# cells with a nonzero left endpoint).  So a cylinder's entire future is
# determined by ONE rational number, its image's right endpoint t; call that the
# cylinder's *type*.  Types transform by
#
#     t  --s-->  min(ell, (3t - s)/2)          (kept iff the result is > 0)
#
# and -- this is the empirical fact that makes the whole thing work -- for every
# rational ell < 1/2 the reachable type set is FINITE (measured: all 300+
# windows of the [0.4, 0.5] grid, sizes 3..936; only ell = 1/2 itself, where the
# types are Flatto's aperiodic f^k(1)/2, is infinite -- and that case is
# `Z32/FlattoCount.lean`).
#
# The type graph is therefore a finite labelled digraph whose length-k words are
# EXACTLY the length-k carry words of the window: no over-approximation, both
# bounds available.  Scaled by one common denominator D (t = a/D, ell = L/D) the
# transition is pure integer arithmetic with no division,
#
#     2 * child  =  min(2L, 3a - sD),
#
# which is what `Z32.EntropyCert.TypeCert.ok` checks by kernel `decide`.
#
# On top of the graph the script emits two vector certificates in the sense of
# `ForMathlib/Combinatorics/PathGrowth.lean`:
#
#   upper   b * sum_{a -> c} v c  <=  a * v a      for every state, v >= m > 0
#   lower   a' * v' a  <=  b' * sum_{a -> c} v' c  for every state, v' >= 0
#
# giving  log(a'/b')  <=  phi_model([0,ell))  <=  log(a/b).  The upper vector is
# a truncated Neumann series (sum_k lam^-k M^k 1, positive because lam > rho);
# the lower one is the Perron vector of the root's strongly connected component,
# extended by ZERO off that component -- which is what lets the lower row
# inequality hold at every state of the ambient graph without a sub-digraph.
#
# WHY NOT THE MESH CERTIFICATE the plan asked for: measured, and dead.  A block
# graph on a uniform mesh with the BlockCert `hits` edge test over-counts by a
# factor ~2 per step that refinement does not remove (the image of a cell is 1.5
# cells wide, so it meets 2 of them whatever the mesh): lambda = 2.000000 at
# EVERY N from 2 to 1000 for the Z-cell, and 1.68..2.05 for band windows -- all
# of them worse than the free bound log(3/2) that monotonicity plus
# `Z32.Flatto.phiModel_zCell` already give.  See the header of
# `Z32/EntropyCert.lean` for the table.
#
#   ./entcert.py <num> <den> [--scale S] [--iters K] [--quiet]
#   ./entcert.py --grid                 # the atlas grid, one data line each
#   ./entcert.py --lean <num> <den>     # emit the Lean TypeCert term

import sys
from fractions import Fraction as F
from math import gcd, log

CARRIES = (0, 1)            # forced, for ell <= 1/2


# ---------------------------------------------------------------- the type graph

def type_graph(ell, cap=200000):
    """Reachable types from the root `ell`, with their labelled children."""
    seen, frontier, kids = {ell}, [ell], {}
    while frontier:
        t = frontier.pop()
        e = []
        for s in CARRIES:
            c = min(ell, (3 * t - s) / 2)
            if c > 0:
                e.append((s, c))
                if c not in seen:
                    seen.add(c)
                    frontier.append(c)
                    if len(seen) > cap:
                        raise RuntimeError(f"type set exceeds {cap} for ell={ell}")
        kids[t] = e
    return sorted(seen), kids


def scale(ell, states, kids):
    """One common denominator D; returns (D, L, int states, int edges)."""
    D = ell.denominator
    for t in states:
        D = D * t.denominator // gcd(D, t.denominator)
    L = int(ell * D)
    ia = {t: int(t * D) for t in states}
    for t in states:
        assert t * D == ia[t], (t, D)
    edges = []
    for t in states:
        for (s, c) in kids[t]:
            # the identity the kernel will check
            assert 2 * ia[c] == min(2 * L, 3 * ia[t] - s * D), (t, s, c)
            edges.append((ia[t], s, ia[c]))
    assert 2 * L <= D, "the window must lie in [0,1/2]"
    return D, L, [ia[t] for t in states], edges


# ------------------------------------------------------------------- the spectrum

def rows_of(states, edges):
    idx = {a: i for i, a in enumerate(states)}
    rows = [[] for _ in states]
    for (u, _, w) in edges:
        rows[idx[u]].append(idx[w])
    return idx, rows


def counts(rows, root, kmax):
    """exact word counts N_k from `root` (big integers)."""
    n = len(rows)
    v = [1] * n
    out = [1]
    for _ in range(kmax):
        v = [sum(v[j] for j in r) for r in rows]
        out.append(v[root])
    return out


def rho_estimate(rows, root, kmax=400):
    N = counts(rows, root, kmax)
    k = kmax
    while k > 2 and N[k] == N[k - 1]:
        k -= 1
    if N[k - 1] == 0:
        return 1.0
    # a ratio of two exact integers, several hundred terms in: accurate to ~1e-12
    return float(F(N[k], N[k - 1]))


def power_iterate(rows, k):
    """v = M^k 1, EXACTLY, in big integers, then divided by the gcd.

    Collatz-Wielandt: max_i (Mv)_i/v_i >= rho >= min_i (Mv)_i/v_i for any
    positive v, and for v = M^k 1 both ratios converge to rho geometrically.
    Working in exact integers means the emitted bracket is limited only by k --
    no rounding enters anywhere, so no floating point is in the trust chain."""
    v = [1] * len(rows)
    for _ in range(k):
        v = [sum(v[j] for j in r) for r in rows]
    g = 0
    for x in v:
        g = gcd(g, x)
    return [x // g for x in v] if g > 1 else v


def sccs(rows):
    """Tarjan, iterative."""
    n = len(rows)
    index = [None] * n
    low = [0] * n
    on = [False] * n
    stack, out, counter = [], [], [0]
    for root in range(n):
        if index[root] is not None:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter[0]
                counter[0] += 1
                stack.append(v)
                on[v] = True
            recurse = False
            for i in range(pi, len(rows[v])):
                w = rows[v][i]
                if index[w] is None:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                elif on[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
            work.pop()
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return out


# ------------------------------------------------------------------ the two vectors

def upper_vector(rows, lam, iters, sc):
    """v = sum_{k<K} lam^-k M^k 1 (positive since lam > rho), then integers."""
    n = len(rows)
    v = [1.0] * n
    acc = [1.0] * n
    for _ in range(iters):
        v = [sum(v[j] for j in r) / lam for r in rows]
        acc = [x + y for x, y in zip(acc, v)]
        if max(acc) > 1e250:
            break
    mn = min(acc)
    return [max(1, round(sc * x / mn)) for x in acc]


def lower_vector(rows, comp, iters, sc):
    """Perron vector of the root's SCC by power iteration; 0 off the component."""
    n = len(rows)
    inc = [False] * n
    for i in comp:
        inc[i] = True
    v = [1.0 if inc[i] else 0.0 for i in range(n)]
    for _ in range(iters):
        w = [0.0] * n
        for i in comp:
            w[i] = sum(v[j] for j in rows[i] if inc[j])
        mx = max(w)
        if mx == 0:
            break
        v = [x / mx for x in w]
    pos = [v[i] for i in comp if v[i] > 0]
    mn = min(pos) if pos else 1.0
    out = [0] * n
    for i in comp:
        out[i] = max(1, round(sc * v[i] / mn))
    return out


def exact_upper(rows, v):
    """the best rational lam with b*(Mv) <= a*v : max over rows."""
    best = F(0)
    for i, r in enumerate(rows):
        best = max(best, F(sum(v[j] for j in r), v[i]))
    return best


def exact_lower(rows, v):
    """the best rational lam' with a'*v <= b'*(Mv) : min over rows where v > 0."""
    best = None
    for i, r in enumerate(rows):
        if v[i] == 0:
            continue
        q = F(sum(v[j] for j in r), v[i])
        best = q if best is None else min(best, q)
    return best if best is not None else F(0)


# ------------------------------------------------------------------------ assembly

def build(num, den, iters=None, digits=20, prec=8):
    """`digits` caps the size of the emitted weights: the power-iterate is run
    just long enough that the largest weight has that many decimal digits."""
    ell = F(num, den)
    if not (0 < ell <= F(1, 2)):
        raise SystemExit("need 0 < num/den <= 1/2")
    states_q, kids = type_graph(ell)
    D, L, states, edges = scale(ell, states_q, kids)
    idx, rows = rows_of(states, edges)
    root = idx[L]
    rho = rho_estimate(rows, root)

    comp = next(c for c in sccs(rows) if root in c)
    k = iters if iters is not None else max(4, int(digits * log(10) / log(rho)))
    v = power_iterate(rows, k)
    while max(v) > 10 ** (digits + 2) and k > 4:
        k = int(k * 0.8)
        v = power_iterate(rows, k)
    lam_up, lam_lo = exact_upper(rows, v), exact_lower(rows, v)

    # Round OUTWARDS to `prec` decimals, so the shipped ratios are readable
    # literals.  Both row inequalities are monotone in the ratio, so a larger
    # upper and a smaller lower are still certified -- re-verified below.
    P = 10 ** prec
    up = F((lam_up * P).__ceil__(), P)
    lo = F((lam_lo * P).__floor__(), P)
    for i, r in enumerate(rows):
        rs = sum(v[j] for j in r)
        assert up.denominator * rs <= up.numerator * v[i], ("upper row", i)
        assert lo.numerator * v[i] <= lo.denominator * rs, ("lower row", i)

    return dict(ell=ell, D=D, L=L, states=states, edges=edges, rows=rows,
                root=root, rho=rho, v=v, k=k, lam_up=up, lam_lo=lo,
                exact_up=lam_up, exact_lo=lam_lo,
                scc=len(comp), counts=counts(rows, root, 12))


def datline(c):
    return (f"ell={c['ell']} states={len(c['states'])} edges={len(c['edges'])} "
            f"Ddigits={len(str(c['D']))} scc={c['scc']} k={c['k']} "
            f"rho in [{c['lam_lo']}, {c['lam_up']}] "
            f"phi_lo={log(float(c['lam_lo'])):.10f} phi_up={log(float(c['lam_up'])):.10f} "
            f"counts={c['counts'][:9]}")


def lean(c, name):
    st = ", ".join(f"({a}, {w})" for a, w in zip(c['states'], c['v']))
    ed = ", ".join(f"({u}, {s}, {w})" for (u, s, w) in c['edges'])
    return f"""/-- Entropy certificate for the window `[0, {c['ell']})`: {len(c['states'])} states,
{len(c['edges'])} edges, common denominator `{c['D']}`.  Generated by
`Z32/entcert.py {c['ell'].numerator} {c['ell'].denominator}`. -/
def {name} : TypeCert where
  D := {c['D']}
  L := {c['L']}
  st := [{st}]
  ed := [{ed}]
  a := {c['lam_up'].numerator}
  b := {c['lam_up'].denominator}
  a' := {c['lam_lo'].numerator}
  b' := {c['lam_lo'].denominator}
  m := {min(c['v'])}
  M := {max(c['v'])}
"""


GRID = [(2, 5), (5, 12), (13, 32), (7, 16), (9, 20), (11, 24), (23, 48),
        (63, 128), (47, 96), (127, 256), (255, 512), (511, 1024)]

if __name__ == "__main__":
    args = sys.argv[1:]
    if not args or args[0] == "--grid":
        print("# plan-B10 WP3: exact type-graph entropy certificates, base 3/2")
        print("# phi_lo <= phi_model([0,ell)) <= phi_up ; free bound log(3/2) = 0.4054651081")
        for (n, d) in GRID:
            try:
                print(datline(build(n, d)))
            except RuntimeError as e:
                print(f"ell={F(n,d)} SKIPPED: {e}")
    elif args[0] == "--lean":
        n, d = int(args[1]), int(args[2])
        nm = args[3] if len(args) > 3 else f"cert{n}_{d}"
        print(lean(build(n, d), nm))
    else:
        n, d = int(args[0]), int(args[1])
        c = build(n, d)
        print(datline(c))
