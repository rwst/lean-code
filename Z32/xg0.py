#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""xg0.py -- the three experiments opened by gate G-0 of `plans/plan-z32-transform.html`:

  X-KP   [KP18] Cor. 18's union  U = [0,1/6) u [1/3,2/3)  -- Mahler's problem reduced to
         its emptiness, so the engine MUST fail; the point is the manner of failure.
  X-D19  [Dub19] Thm 1.2's window  [8/57, 805/1539)  at 3/2, length 31/81 -- does the
         corpus subsume a 2019 printed theorem, or does the hand proof beat the engine?
  X-238  the two-cell family  ||.|| < c  against the corrected printed bound 0.238117...
         of [Dub06JNT] (Bugeaud, Tract 193, Thm 3.14).

Everything here is exact `Fraction`/integer arithmetic; the block-certificate search reuses
`gencert.py`'s own routines, so a "CYCLE" verdict below is the same object `BlockCert.lean`
rechecks with `decide`.

  python3 xg0.py kp | d19 | twocell | all
"""
import sys
from fractions import Fraction as F
from itertools import product
from math import log

import gencert as g
import horseshoe as hs

CARR = (-2, -1, 0, 1)          # atlas.c's e = -s convention


# --------------------------------------------------------------- exact pruning

def merge(iv):
    iv = sorted(iv)
    out = []
    for a, b in iv:
        if out and out[-1][1] >= a:
            if out[-1][1] < b:
                out[-1] = (out[-1][0], b)
        else:
            out.append((a, b))
    return out


def prune(S, U):
    o = []
    for a, b in S:
        for e in CARR:
            lo, hi = max((2 * a - e) / 3, F(0)), min((2 * b - e) / 3, F(1))
            if lo < hi:
                o.append((lo, hi))
    r = []
    for a, b in merge(o):
        for c, d in U:
            l, h = max(a, c), min(b, d)
            if l < h:
                r.append((l, h))
    return merge(r)


def edges(S):
    E = []
    for i, (a, b) in enumerate(S):
        for e in CARR:
            lo, hi = (3 * a + e) / 2, (3 * b + e) / 2
            for j, (c, d) in enumerate(S):
                if d > lo and c < hi:
                    E.append((i, e, j))
    return E


def anatomy(U, depth, label):
    print(f"--- {label}")
    print("    U =", " ".join(f"[{a},{b})" for a, b in U),
          " |U| =", sum(b - a for a, b in U))
    S, prev = list(U), None
    for k in range(1, depth + 1):
        S = prune(S, U)
        m = sum(b - a for a, b in S)
        print(f"    level {k:3d}  components {len(S):6d}  measure {float(m):.10g}")
        if not S:
            print(f"    KILL at depth {k}")
            return None
        if S == prev:
            print(f"    FIXED POINT: S_{k} = S_{k-1}, invariant forever")
            break
        prev = S
    return S


def cert_probe(G, nums, maxdepth=40, cap=1200, ranked=True):
    """Capped replay of `gencert.py`, default (hull-merge) or rank-stratified."""
    U = [(F(nums[i], G), F(nums[i + 1], G)) for i in range(0, len(nums), 2)]
    lv = [U]
    for k in range(1, maxdepth + 1):
        S = g.prune(lv[-1], U)
        lv.append(S)
        if not S:
            return ("KILL", k, 0, None)
        if len(S) > cap:
            return ("CAP", k, len(S), None)
        D = G * 3 ** k
        if ranked:
            r = g.ranks_of(D, g.scale(S, D))
            if r is not None:
                return ("CYCLE", k, len(S), max(r) + 1)
        else:
            H = g.blocks_fixpoint(S)
            if g.outdeg(H) <= 1:
                return ("CYCLE", k, len(H), None)
    return ("FAT", maxdepth, len(lv[-1]), None)


# ------------------------------------------------------------------ the orbits

def orbits_upto(P):
    """Every periodic orbit of the interval model of period <= P, with the two-cell
    threshold  c_entry = max over the orbit of ||.||  at which it enters ||.|| < c."""
    seen = {}
    for p in range(1, P + 1):
        den = 3 ** p - 2 ** p
        for w in product(CARR, repeat=p):
            y0 = F(-sum(3 ** (p - 1 - i) * 2 ** i * w[i] for i in range(p)), den)
            if not 0 <= y0 < 1:
                continue
            y, orb, ok = y0, [], True
            for i in range(p):
                orb.append(y)
                y = (3 * y + w[i]) / 2
                if not 0 <= y < 1:
                    ok = False
                    break
            if not ok or y != y0:
                continue
            key = frozenset(orb)
            seen.setdefault(key, (len(key), max(min(z, 1 - z) for z in key)))
    return sorted(((per, thr, tuple(sorted(k))) for k, (per, thr) in seen.items()),
                  key=lambda r: (r[1], r[0]))


# ------------------------------------------------------------------ X-KP

KP = [(F(0), F(1, 6)), (F(1, 3), F(2, 3))]
KPHOLD = [(F(0), F(1, 15)), (F(1, 3), F(2, 5)), (F(5, 9), F(3, 5))]


def x_kp():
    print("=" * 78)
    print("X-KP  --  [KP18] Cor. 18:  Z(U) = empty  <=>  Mahler's conjecture,  |U| = 1/2")
    print("=" * 78)
    anatomy(KP, 40, "pruning of U = [0,1/6) u [1/3,2/3)")
    print("--- the limit hold set, checked to BE exactly invariant (no engine needed)")
    print("    H =", " ".join(f"[{a},{b})" for a, b in KPHOLD),
          " |H| =", sum(b - a for a, b in KPHOLD))
    print("    H subset U :", all(any(c <= a and b <= d for c, d in KP) for a, b in KPHOLD))
    print("    prune(H,H) == H :", prune(KPHOLD, KPHOLD) == KPHOLD)
    A = [[0] * 3 for _ in range(3)]
    for (i, _, j) in edges(KPHOLD):
        A[i][j] += 1
    print("    transition matrix (rows = from):", A)
    print("    char. poly x*(x^2-x-1)  =>  spectral radius = golden ratio 1.6180339...")
    tr = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    print("    periodic points of period dividing n  (= tr A^n, the LUCAS numbers):")
    row = []
    for n in range(1, 17):
        tr = [[sum(tr[i][k] * A[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
        row.append(sum(tr[i][i] for i in range(3)))
    print("      ", row)
    print("--- block certificate: refused in both modes")
    for ranked in (False, True):
        print(f"    {'ranked ' if ranked else 'default'}: {cert_probe(6, [0,1,2,4], 60, 400, ranked)}")
    print("--- horseshoe certificates (the positive side of the phi_model ledger)")
    for L in range(1, 9):
        n, best = hs.best_at(KP, L)
        if best is None:
            print(f"    L={L}: {n:3d} admissible periodic words, no horseshoe")
            continue
        K, S = best
        D = 6
        for z in (K[0], K[1]):
            D = D * z.denominator // __import__("math").gcd(D, z.denominator)
        Ui = [(int(a * D), int(b * D)) for a, b in KP]
        A0, B0 = int(K[0] * D), int(K[1] * D)
        print(f"    L={L}: {n:3d} admissible words | N={len(S):3d} K=[{K[0]},{K[1]}] D={D} "
              f"rate=log({len(S)})/{L}={log(len(S))/L:.4f} "
              f"| Horse.ok replay {hs.check_cert(D,3,2,Ui,A0,B0,[list(w) for w in sorted(S)])}"
              f" | brute-force bad concatenations {hs.validate(D,3,2,Ui,A0,B0,[list(w) for w in sorted(S)],2)}")
    print("=> log N / L -> log(golden ratio) = 0.4812118...;  infinitely many periodic orbits,")
    print("   so M7 Theorem B forbids EVERY block certificate, archimedean or product, at every")
    print("   level.  Mahler's conjecture is out of reach of this certificate family, provably.")


# ------------------------------------------------------------------ X-D19

def x_d19():
    print("=" * 78)
    print("X-D19  --  [Dub19] Thm 1.2's window [8/57, 805/1539) at 3/2, length 31/81")
    print("=" * 78)
    U = [(F(216, 1539), F(805, 1539))]
    S = anatomy(U, 14, "pruning (components grow by exactly one per level, forever)")
    print("--- hold set at level 14 and its transitions")
    for i, (a, b) in enumerate(S):
        print(f"    I{i:2d} = [{a},{b})  ~ [{float(a):.9f},{float(b):.9f})")
    for (i, e, j) in edges(S):
        print(f"    I{i} --e={e}--> I{j}")
    print("--- the mechanism: the LEFT endpoint is a preimage of the 3-cycle")
    print("    8/57 --e=0--> ", (3 * F(8, 57) + 0) / 2, " = 4/19, a point of the 3-cycle")
    print("    3-cycle {4/19, 6/19, 9/19}, denominator 3^3-2^3 = 19 -- the same cycle as the")
    print("    corpus's own certified window [1/6,13/24) (Z32.ZSet_three_two_sixth_3_8)")
    print("--- certificate probes")
    print("    half-open, default:", cert_probe(1539, [216, 805], 60, 400, False))
    print("    half-open, ranked :", cert_probe(1539, [216, 805], 60, 400, True))
    print("--- endpoint slack: move the LEFT endpoint by one unit of 1/1539")
    for lo in (216, 217, 218, 220):
        print(f"    [{lo}/1539, 805/1539) len {float(F(805-lo,1539)):.6f} :",
              cert_probe(1539, [lo, 805], 40, 400, False))
    print("--- endpoint slack: shrink the RIGHT endpoint instead (does nothing)")
    for hi in (804, 800, 790, 780):
        print(f"    [216/1539, {hi}/1539) len {float(F(hi-216,1539)):.6f} :",
              cert_probe(1539, [216, hi], 40, 400, False))


# ------------------------------------------------------------------ X-238

def x_twocell():
    print("=" * 78)
    print("X-238  --  the two-cell family  ||.|| < c,  U_c = [0,c) u [1-c,1)")
    print("=" * 78)
    print("--- periodic orbits by the c at which they enter U_c  (exact, period <= 12)")
    for per, thr, pts in orbits_upto(12):
        if thr < F(1, 4):
            print(f"    period {per:3d}   c_entry = {thr} = {float(thr):.9f}   "
                  f"{[str(p) for p in pts][:6]}{'...' if len(pts) > 6 else ''}")
    print("--- certificate probes, DEFAULT (hull-merge) mode: the 1/5 ceiling of the paper")
    for G, a in ((100, 20), (100, 21), (100, 23), (1000, 238)):
        print(f"    c={a}/{G} = {a/G:<9}: {cert_probe(G, [0, a, G-a, G], 40, 400, False)}")
    print("--- certificate probes, RANK-STRATIFIED mode: the ceiling moves to 0.2381")
    for G, a in ((100, 21), (100, 22), (100, 23), (1000, 235), (1000, 238),
                 (10000, 2381), (10000, 2385), (10000, 2390), (100, 25), (3, 1)):
        print(f"    c={a}/{G} = {a/G:<9}: {cert_probe(G, [0, a, G-a, G], 26, 1200, True)}")
    print("=> the certified ceiling is 0.2381, against 1/5 in the shipped paper and")
    print("   0.238117... in print ([Dub06JNT] via Bugeaud Tract 193 Thm 3.14).")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("kp", "all"):
        x_kp()
    if what in ("d19", "all"):
        x_d19()
    if what in ("twocell", "238", "all"):
        x_twocell()
