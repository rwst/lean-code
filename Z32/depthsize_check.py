#!/usr/bin/env python3
"""plan-z32-transform milestone M5(a): the depth-size bound, numerically (R-5 bridge).

`Z32/DepthSize.lean` proves, for every valid unranked block certificate with funnel depth
K = c.levels.length, block count B = c.blocks.length and hole delta = |[0,1) \\ U|,

    (i)   |T_k|     >= 1 - (k+1) delta        the funnel loses at most delta per level
    (ii)  |T_{K+j}| <= B (q/p)^j              past depth K the certificate confines it
    (iii) 1 <= 2 delta (K + 2 + log_{p/q} 2B) the two, compared at K+j and optimised in j

on the EXACT funnel T_0 = U, T_{k+1} = U cap f^{-1}(T_k).  This script recomputes all three on
the largeness records, with exact rational arithmetic and an independent funnel: the funnel, the
certifier and the measures come from `xu.py`, the Lean file shares no code with any of it.

It also reports the slack -- the ratio of the record's true delta to the floor the bound puts on
it -- which is the honest reading of the theorem: one to two orders of magnitude at today's sizes,
and a statement about a FAMILY (C-8's delta_P <= C(q/p)^{cP}), not about a single set.

Exact arithmetic throughout; a few seconds.
"""
import sys
from fractions import Fraction as Fr
from math import log

sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
import xu

JMAX = 12            # how far past the certifying depth to test the contraction bound
CAP = 34             # funnel depth cap for the certifier (the 60-cell record needs 20)

# the records, as (N, endpoint pairs over N) -- the same lists `reproduce.sh` feeds `gencert.py`
RECORDS = [
    ("25/36  (certUnion2536)", 36, [0, 3, 4, 11, 16, 24, 25, 27, 30, 32, 33, 36]),
    ("17/24  (certUnion7083)", 48, [0, 2, 3, 9, 10, 11, 12, 16, 17, 18, 20, 21, 23, 34,
                                    36, 37, 38, 40, 41, 45, 46, 47]),
]

# the two wider records, for the arithmetic of (iii) only: their funnels are re-verified in X-U
# (`xu.py` section F), and only K, B and |U| enter the headline
WIDE = [("43/60  (engine)", 20, 433, Fr(43, 60)), ("89/120 (engine)", 29, 2526, Fr(89, 120))]


def meas(ivs):
    return sum(b - a for a, b in ivs)


def headline(K, B, delta, p=3, q=2):
    """2 delta (K + 2 + log_{p/q} 2B), and the floor it puts on delta"""
    L = log(2 * B) / log(p / q)
    return 2 * float(delta) * (K + 2 + L), 1 / (2 * (K + 2 + L))


def main():
    bad = 0
    for name, N, flat in RECORDS:
        pairs = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
        U = xu.norm(xu.ivs_from_pairs(N, pairs))
        r = xu.certify(U, cap=CAP)
        K, B = r["kh"], r["blocks"]
        delta = 1 - meas(U)
        print(f"== {name}: |U| = {meas(U)}, delta = {delta}, K = {K}, B = {B}")
        T = [U]
        for _ in range(K + JMAX):
            T.append(xu.inter(U, xu.preimage(T[-1], 3, 2)))
        # (i) the expansion half, in both the forms the Lean file states
        v1 = v2 = 0
        for k in range(len(T) - 1):
            if meas(xu.preimage(T[k], 3, 2)) < meas(T[k]):
                v1 += 1
            if meas(T[k + 1]) < meas(T[k]) - delta:
                v2 += 1
        v3 = sum(1 for k in range(len(T)) if meas(T[k]) < 1 - (k + 1) * delta)
        print(f"   (i)   |f^-1(S)| >= |S| on the funnel, k = 0..{len(T)-2}: {v1} violations")
        print(f"         |T_{{k+1}}| >= |T_k| - delta, k = 0..{len(T)-2}: {v2} violations")
        print(f"         |T_k| >= 1 - (k+1) delta, k = 0..{len(T)-1}: {v3} violations")
        bad += v1 + v2 + v3
        # (ii) the contraction half
        print("   (ii)   j   |T_{K+j}|      B (2/3)^j")
        for j in range(JMAX + 1):
            lhs, rhs = meas(T[K + j]), B * Fr(2, 3) ** j
            ok = lhs <= rhs
            bad += 0 if ok else 1
            print(f"         {j:3d}   {float(lhs):.9f}   {float(rhs):12.6f}   "
                  f"{'ok' if ok else 'VIOLATION'}")
        # (iii) the headline
        h, floor = headline(K, B, delta)
        bad += 0 if h >= 1 else 1
        print(f"   (iii)  2 delta (K+2+log_(3/2) 2B) = {h:.4f} >= 1: "
              f"{'ok' if h >= 1 else 'VIOLATION'}   "
              f"floor on delta {floor:.6f} vs actual {float(delta):.6f}, slack {h:.2f}x")

    print("== the two wider records: the headline only (their funnels are checked in X-U)")
    for name, K, B, m in WIDE:
        h, floor = headline(K, B, 1 - m)
        bad += 0 if h >= 1 else 1
        print(f"   {name}: K = {K}, B = {B}, delta = {float(1-m):.6f}, "
              f"headline {h:.4f}, floor {floor:.6f}, slack {h:.2f}x")

    print("VERDICT:", "depth-size bound holds on every record"
          if bad == 0 else f"{bad} VIOLATIONS")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
