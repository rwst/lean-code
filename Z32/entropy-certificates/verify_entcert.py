#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# verify_entcert.py -- plan-B10 WP3: an INDEPENDENT re-check of the entropy
# certificates emitted by `Z32/entcert.py`, in the `verify_atlas.py` pattern
# (plan risk R-5: correlated single-author error is the dominant risk).
#
# Nothing here shares code with the generator except the certificate itself,
# which is the artifact under test.  Four checks, each by a deliberately
# different route:
#
#  (V1) THE GRAPH IS THE RIGHT GRAPH.  The generator builds the type set by a
#       forward closure on right endpoints.  Here the cylinders are enumerated
#       as FULL intervals [lo,hi) -- both endpoints, exact Fractions, no
#       right-endpoint assumption -- to depth `d`, and the distinct images are
#       collected.  This re-derives the state set and simultaneously tests the
#       "left endpoint is always 0" fact the type coordinate rests on.
#
#  (V2) THE SCALING IS FAITHFUL.  Every emitted state a is checked to be
#       D * (a rational type), and every emitted edge to satisfy the integer
#       identity 2c = min(2L, 3a - sD) that the Lean `ok` will check -- plus
#       COMPLETENESS (no true edge missing) and CLOSURE (no target off the state
#       list), which are the two halves soundness needs.
#
#  (V3) THE WORD COUNTS AGREE.  Brute-force cylinder counts (V1's enumeration)
#       against path counts in the emitted graph, for every length up to `d`.
#       These are the numbers `phi_model` is the growth rate of, so agreement
#       here is what makes the whole certificate mean anything.
#
#  (V4) THE BRACKET IS HONEST.  The two row inequalities are re-checked in exact
#       integer arithmetic, and the resulting bracket [a'/b', a/b] is checked to
#       contain the growth rate measured independently as the ratio of two exact
#       big-integer word counts at depth ~400.
#
#   ./verify_entcert.py                 # the whole grid
#   ./verify_entcert.py <num> <den> [<depth>]

import sys
from fractions import Fraction as F
from math import log

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import entcert                                    # the artifact under test


def cylinders(ell, depth):
    """(V1) full-interval enumeration; returns per-depth counts and the images."""
    cells = [(F(0), ell)]
    counts, images, left_bad = [1], {ell}, 0
    for _ in range(depth):
        nxt = []
        for (lo, hi) in cells:
            for s in (0, 1):
                a = max(F(0), (3 * lo - s) / 2)
                b = min(ell, (3 * hi - s) / 2)
                if a < b:
                    if a != 0:
                        left_bad += 1
                    nxt.append((a, b))
                    images.add(b)
        cells = nxt
        counts.append(len(cells))
    return counts, images, left_bad


def check(num, den, depth=14, verbose=True):
    ell = F(num, den)
    c = entcert.build(num, den)
    D, L, st, ed, v = c['D'], c['L'], c['states'], c['edges'], c['v']
    fails = []

    def want(cond, msg):
        if not cond:
            fails.append(msg)

    # ---- V1
    counts, images, left_bad = cylinders(ell, depth)
    want(left_bad == 0, f"V1: {left_bad} cylinders with a nonzero left endpoint")
    want(images <= {F(a, D) for a in st},
         "V1: brute-force enumeration reaches a type the certificate omits")
    want(F(L, D) == ell, f"V1: L/D = {F(L,D)} != {ell}")

    # ---- V2
    want(0 < D and 0 < L and 2 * L <= D, "V2: window not inside [0,1/2]")
    want(L in st, "V2: the root state is missing")
    want(len(set(st)) == len(st), "V2: duplicate states")
    for a in st:
        want(0 < a <= L, f"V2: state {a} outside (0,L]")
    for (u, s, w) in ed:
        want(u in st and w in st, f"V2: edge ({u},{s},{w}) leaves the state list")
        want(s in (0, 1), f"V2: edge label {s} outside the forced alphabet")
        want(0 < w, f"V2: edge ({u},{s},{w}) has a nonpositive target")
        want(2 * w == min(2 * L, 3 * u - s * D),
             f"V2: edge ({u},{s},{w}) breaks the transition identity")
    for a in st:
        for s in (0, 1):
            ch = min(2 * L, 3 * a - s * D)
            listed = [e for e in ed if e[0] == a and e[1] == s]
            if ch > 0:
                want(len(listed) == 1,
                     f"V2: state {a} label {s} has {len(listed)} edges, want 1")
            else:
                want(not listed, f"V2: state {a} label {s} listed but empty")

    # ---- V3
    idx = {a: i for i, a in enumerate(st)}
    rows = [[] for _ in st]
    for (u, s, w) in ed:
        rows[idx[u]].append(idx[w])
    vec, paths = [0] * len(st), [1]
    vec[idx[L]] = 1
    # count paths FROM the root by pushing mass forward along reversed rows
    fwd = [1] * len(st)
    for k in range(1, depth + 1):
        fwd = [sum(fwd[j] for j in r) for r in rows]
        paths.append(fwd[idx[L]])
    want(paths == counts,
         f"V3: path counts {paths[:9]} != cylinder counts {counts[:9]}")

    # ---- V4
    up, lo = c['lam_up'], c['lam_lo']
    for i, r in enumerate(rows):
        rs = sum(v[j] for j in r)
        want(up.denominator * rs <= up.numerator * v[i],
             f"V4: upper row {i} fails")
        want(lo.numerator * v[i] <= lo.denominator * rs,
             f"V4: lower row {i} fails")
    want(min(v) > 0, "V4: a weight is zero")
    big = [1] * len(st)
    for _ in range(400):
        big = [sum(big[j] for j in r) for r in rows]
    prev = [1] * len(st)
    for _ in range(399):
        prev = [sum(prev[j] for j in r) for r in rows]
    growth = F(big[idx[L]], prev[idx[L]])
    want(lo <= growth <= up,
         f"V4: measured growth {float(growth):.12f} outside [{float(lo)}, {float(up)}]")

    if verbose:
        tag = "OK  " if not fails else "FAIL"
        print(f"{tag} ell={str(ell):10s} states={len(st):4d} edges={len(ed):4d} "
              f"phi in [{log(float(lo)):.10f}, {log(float(up)):.10f}]  "
              f"counts={counts[:9]}")
        for f in fails:
            print(f"       !! {f}")
    return fails


if __name__ == "__main__":
    if len(sys.argv) >= 3:
        bad = check(int(sys.argv[1]), int(sys.argv[2]),
                    int(sys.argv[3]) if len(sys.argv) > 3 else 14)
        sys.exit(1 if bad else 0)
    total = 0
    for (n, d) in entcert.GRID:
        total += len(check(n, d, 12))
    print(f"\n{'ALL CERTIFICATES VERIFIED' if not total else str(total)+' FAILURES'}")
    sys.exit(1 if total else 0)
