#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""m3schema.py -- milestone M3 of `plans/plan-z32-transform.html`: the depth-K
certificate schema.

Experiment X-P (`xp.py`) decomposed the two residual eps-bands of gate G-1 and found
the decomposition base-independent.  This script checks the closed form that explains
that, in four independent ways.

  (A) THE CRITERION.  Run the two-branch map from the window's own left endpoint,

          w_0 = 0,   q*w_{i+1} = p*(w_i + eps - j),   j in {0,1},

      and stop the first time w_K lands in the hole  q/p - eps <= w_K <= 1 - eps
      (right end closed).  `escape_depth` returns that K.  Claim: it is exactly the
      depth at which the corpus's block certificate closes.

  (B) THE LEAN FILE.  `lean_escape` and `lean_low_band` transcribe `Z32.Escape` and
      `Z32.LowBand` of `Z32/DepthKSchema.lean` field by field, and are checked against
      (A) and against the funnel engine.  This is the R-5 bridge.

  (C) THE ROTATION.  `block_rank`, `low_count`, `high_count` transcribe the Lean
      definitions; the claim proved in Lean is that the rank of the image is a cyclic
      rotation of the rank, and that the rank decides the branch.

  (D) THE LITERATURE.  [Bug04] Lemma 3 (Bugeaud, Acta Arith. 114 (2004) 301-311,
      papers/Bugeaud2004.pdf) lists the certified parameter intervals in closed form,

          J_b^a(g) = [ (P + g^b) / D , (P + g^{b-1}) / D ],
          P = sum_{k=1}^{b-1} eps_{-k}(a/b) g^k,   D = 1 + g + ... + g^{b-1},

      with g = q/p and eps_{-k} the characteristic Sturmian sequence of a/b.  Checked
      here against (A): the J_b^a tile the certified eps, b = K+1, and a = N_R + 1.
      `Z32.LowBand ... K` is J_{K+1}^1.

  python3 m3schema.py
"""
import sys
import time
from fractions import Fraction as Fr

import gencert as g
import xp

BASES = [(5, 2), (7, 2), (9, 2), (10, 3), (11, 3), (4, 3), (13, 2), (17, 4), (3, 2), (26, 5)]


# ------------------------------------------------------------- (A) the criterion

def marked_orbit(p, q, e, cap=400):
    """(K, [w_0..w_K]) with the CLOSED escape test, or (None, w) if it never escapes."""
    w = [Fr(0)]
    for i in range(cap):
        x = w[-1]
        if q <= p * (x + e) and x + e <= 1:          # hole, right end closed
            return i, w
        if p * (x + e) < q:
            w.append(Fr(p * (x + e), q))
        else:
            w.append(Fr(p * (x + e - 1), q))
    return None, w


def escape_depth(p, q, e, cap=400):
    return marked_orbit(p, q, e, cap)[0]


# --------------------------------------------- (B) transcription of the Lean file

def lean_escape(p, q, e, K, w):
    """`Z32.Escape p q e K w`, field by field."""
    if w[0] != 0:
        return False
    if not all(0 <= w[i] for i in range(K + 1)):                     # nonneg
        return False
    if not all(w[i] < 1 for i in range(K)):                          # lt_one
        return False
    for i in range(K):                                               # step
        lo = (p * (w[i] + e) < q and q * w[i + 1] == p * (w[i] + e))
        hi = (1 <= w[i] + e and q * w[i + 1] == p * (w[i] + e - 1))
        if not (lo or hi):
            return False
    return q <= p * (w[K] + e) and w[K] + e <= 1                     # hit_lo, hit_hi


def lean_low_band(p, q, e, K):
    """`Z32.LowBand p q e K`."""
    return (Fr(q) ** (K + 1) * (p - q) <= p * e * (Fr(p) ** (K + 1) - Fr(q) ** (K + 1))
            and e * (Fr(p) ** (K + 1) - Fr(q) ** (K + 1)) <= Fr(q) ** K * (p - q))


def lean_low_orbit(p, q, e, i):
    """`Z32.lowOrbit p q e i`, by the recursion."""
    x = Fr(0)
    for _ in range(i):
        x = Fr(p) * (x + e) / q
    return x


# ------------------------------------------------------ (C) the rank and rotation

def block_rank(w, K, x):
    return sum(1 for i in range(K + 1) if w[i] <= x)


def low_count(p, q, e, w, K):
    return sum(1 for i in range(K) if p * (w[i] + e) < q)


def high_count(p, q, e, w, K):
    return sum(1 for i in range(K) if not p * (w[i] + e) < q)


# ------------------------------------------------------------ (D) [Bug04] Lemma 3

def sturm(a, b, k):
    """eps_{-k}(a/b) = [-k a/b] - [-(k+1) a/b], the characteristic Sturmian sequence."""
    import math
    return math.floor(Fr(-k * a, b)) - math.floor(Fr(-(k + 1) * a, b))


def bug04_J(p, q, b, a):
    """[Bug04] Lemma 3's interval J_b^a(q/p), closed at both ends."""
    gam = Fr(q, p)
    P = sum(sturm(a, b, k) * gam ** k for k in range(1, b))
    D = sum(gam ** k for k in range(b))
    return ((P + gam ** b) / D, (P + gam ** (b - 1)) / D)


# ----------------------------------------------------------------------- the runs

def run():
    t0 = time.time()
    print("== (A) the escape depth IS the block-certificate depth ==")
    print("   funnel engine `xp.scalar_eps` vs. `escape_depth`, both residual bands")
    tot = bad = 0
    for (p, q) in BASES:
        for name, lo, hi in (("LOW", Fr(0), Fr(q * q, p * (p + q))),
                             ("HIGH", Fr(q, p + q), Fr(q, p))):
            for i in range(1, 81):
                e = lo + Fr(i, 81) * (hi - lo)
                d = xp.scalar_eps(p, q, e, cap=80)
                K = escape_depth(p, q, e)
                tot += 1
                if d != K:
                    bad += 1
                    print(f"   MISMATCH ({p},{q}) eps={e} funnel={d} escape={K}")
    print(f"   {tot} eps at {len(BASES)} bases, mismatches: {bad}")

    print()
    print("== (B) the Lean transcription ==")
    print("   `Z32.Escape` on the orbit computed by (A); `Z32.LowBand` => escape at K")
    tot = bad = 0
    for (p, q) in BASES:
        for name, lo, hi in (("LOW", Fr(0), Fr(q * q, p * (p + q))),
                             ("HIGH", Fr(q, p + q), Fr(q, p))):
            for i in range(1, 41):
                e = lo + Fr(i, 41) * (hi - lo)
                K, w = marked_orbit(p, q, e)
                tot += 1
                if K is None or not lean_escape(p, q, e, K, w):
                    bad += 1
    print(f"   Escape holds on {tot - bad} of {tot} band points; failures: {bad}")
    tot = bad = 0
    for (p, q) in BASES:
        for K in range(0, 9):
            for t in (Fr(0), Fr(1, 7), Fr(1, 2), Fr(6, 7), Fr(1)):
                lo = Fr(q ** (K + 1) * (p - q), p * (p ** (K + 1) - q ** (K + 1)))
                hi = Fr(q ** K * (p - q), p ** (K + 1) - q ** (K + 1))
                e = lo + t * (hi - lo)
                tot += 1
                if not lean_low_band(p, q, e, K):
                    bad += 1
                    continue
                w = [lean_low_orbit(p, q, e, i) for i in range(K + 1)]
                if not lean_escape(p, q, e, K, w):
                    bad += 1
    print(f"   LowBand endpoints+interior: {tot} points, LowBand => Escape failures: {bad}")
    m1band = all(lean_low_band(p, q, e, 1)
                 == (q * q <= p * (p + q) * e and (p + q) * e <= q)
                 for (p, q) in BASES for e in (Fr(i, 300) for i in range(301)))
    m1zero = all(lean_low_band(p, q, e, 0) == (q <= p * e and e <= 1)
                 for (p, q) in BASES for e in (Fr(i, 300) for i in range(301)))
    print(f"   LowBand K=1 == the G-1 closed band: {m1band};  K=0 == q <= p*eps: {m1zero}")

    print()
    print("== (C) the rank rotation, and that the rank decides the branch ==")
    tot = bad = 0
    for (p, q) in BASES:
        for name, lo, hi in (("LOW", Fr(0), Fr(q * q, p * (p + q))),
                             ("HIGH", Fr(q, p + q), Fr(q, p))):
            for i in range(1, 21):
                e = lo + Fr(i, 21) * (hi - lo)
                K, w = marked_orbit(p, q, e)
                if K is None:
                    continue
                NL, NR = low_count(p, q, e, w, K), high_count(p, q, e, w, K)
                l, r = Fr(q, p) - e, 1 - e
                pts = set(w[:K]) | {Fr(0)}
                for t in range(150):
                    for a2, b2 in ((Fr(0), l), (r, Fr(1))):
                        pts.add(a2 + Fr(t, 150) * (b2 - a2))
                for v in pts:
                    if not (0 <= v < 1):
                        continue
                    if p * (v + e) < q:
                        v2, expect = Fr(p * (v + e), q), block_rank(w, K, v) + NR + 1
                    elif 1 <= v + e:
                        v2, expect = Fr(p * (v + e - 1), q), block_rank(w, K, v) - NL
                    else:
                        continue
                    tot += 2
                    if block_rank(w, K, v2) != expect:
                        bad += 1
                    if (p * (v + e) < q) != (block_rank(w, K, v) <= NL):
                        bad += 1
    print(f"   {tot} checks (rotation + branch dichotomy), violations: {bad}")

    print()
    print("== (D) [Bug04] Lemma 3: the certified eps are exactly the J_b^a(q/p) ==")
    print("   b = K+1 (blocks), a = N_R+1 (the rotation number a/b)")
    tot = bad = 0
    rows = []
    for (p, q) in BASES:
        loc = 0
        for b in range(1, 10):
            for a in range(1, b + 1):
                from math import gcd
                if gcd(a, b) != 1:
                    continue
                J0, J1 = bug04_J(p, q, b, a)
                for t in (Fr(1, 5), Fr(1, 2), Fr(4, 5)):
                    e = J0 + t * (J1 - J0)
                    K, w = marked_orbit(p, q, e)
                    tot += 1
                    if K is None:
                        bad += 1
                        continue
                    NR = high_count(p, q, e, w, K)
                    if K + 1 != b or NR + 1 != a:
                        bad += 1
                        print(f"   MISMATCH ({p},{q}) a/b={a}/{b} eps={e} K={K} NR={NR}")
                loc += 1
        rows.append((p, q, loc))
    print(f"   {tot} interior points over the a/b with b <= 9, mismatches: {bad}")
    same = all(bug04_J(p, q, K + 1, 1)
               == (Fr(q ** (K + 1) * (p - q), p * (p ** (K + 1) - q ** (K + 1))),
                   Fr(q ** K * (p - q), p ** (K + 1) - q ** (K + 1)))
               for (p, q) in BASES for K in range(0, 12))
    print(f"   Z32.LowBand ... K  ==  J_(K+1)^1(q/p)  at all bases, K <= 11: {same}")

    print()
    print("== coverage of the residual bands by the all-low family (Z32.LowBand) ==")
    print("   base   LOW band    covered by K<=40      share")
    for (p, q) in BASES:
        band = Fr(q * q, p * (p + q))
        cov = Fr(0)
        for K in range(1, 41):
            lo = Fr(q ** (K + 1) * (p - q), p * (p ** (K + 1) - q ** (K + 1)))
            hi = Fr(q ** K * (p - q), p ** (K + 1) - q ** (K + 1))
            if K >= 2:
                cov += hi - lo
        print(f"   ({p:2d},{q}) {float(band):.9f}  {float(cov):.9f}  {float(cov / band):.6f}")

    print()
    print("== the two Lean instances at (5,2) ==")
    for K, lo, hi, nm in ((2, Fr(8, 195), Fr(4, 39), "ZSet_five_two_depth_two"),
                          (3, Fr(16, 1015), Fr(8, 203), "ZSet_five_two_depth_three")):
        inside = 0 < lo and hi < Fr(4, 35)
        ok = all(escape_depth(5, 2, lo + Fr(i, 50) * (hi - lo)) == K for i in range(51))
        print(f"   {nm}: eps in [{lo}, {hi}], inside the LOW band (0,4/35): {inside}, "
              f"escapes at K={K} throughout: {ok}")
    print()
    print(f"   total {time.time() - t0:.1f}s", file=sys.stderr)


if __name__ == "__main__":
    run()
