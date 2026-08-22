#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""B6(i) of plans/report3-BB13.html -- the abc-quality ledger, measured.

Tier (i) of strategy B6 is a conditional benchmark: under a cap q_max on the
abc quality of the triples the frame produces,

    w + D  <=  (2*log2(3/2) - (log2 3)/q_max) * a + log2(12),

which at the empirical record q_max = 1.63 gives min(w, D) <= 0.0988 a -- 3.75
times better than the best known unconditional row, 0.371 a ([Zud07]).

Notation (all exact integer arithmetic):

    m_a = round((3/2)^a) = (2*3^a + 2^a) >> (a+1)
    k_a = 3^a - m_a 2^a,     w = v_2(m_a),     D = max{d : 2^d |k_a| < (3/2)^a}
    the frame triple   A + B = C  with  A = m_a 2^a,  B = k_a,  C = 3^a
    its content        g_a = gcd(m_a, 3^a) = 3^{v_3(m_a)}
    primitive triple   (A/g, B/g, C/g);   rad(ABC) is the same for both
    quality            q(a) = log(C/g) / log(rad(ABC))

Blocks
  [A] the five exceptions as abc triples -- primitive vs raw quality (the raw
      reading at a = 3 has "quality" 1.8393 > 1.63 and would refute the
      report's own hypothesis: the triple must be taken primitive)
  [B] the family's own ledger: q(a) for a <= AMAX, its record and top ten
  [C] the price list: cap q_max -> slope, against the known rows
  [D] the Lean constants: the 65/41 route vs exact real arithmetic
  [E] the core inequality rad * 2^{w+D+2a} * g^2 <= 12 * 3^{2a}, checked exactly
  [F] what a deep fibre would force: the quality demanded by depth d at a
  [G] the circularity, quantified: the ledger slope vanishes at
      q* = log3/(2 log(3/2)) = 1.354755..., the quality the frame's own
      triples attain

Usage:  python3 BB13/b6_ledger.py [AMAX]      (default 140; ~10 s)

The Lean side of the same work is BB13/QualityLedger.lean; its module docstring
quotes the numbers produced here.
"""
import sys
import time
from math import gcd, log, log2

from sympy import factorint

LOG2_3 = log2(3.0)          # 1.5849625007211562
LOG2_32 = log2(1.5)         # 0.5849625007211562
QSTAR = log(3.0) / (2.0 * log(1.5))   # 1.3547552...


def mnum(a):
    """round((3/2)^a), exactly."""
    return (2 * 3 ** a + 2 ** a) >> (a + 1)


def kres(a):
    """k_a = 3^a - m_a 2^a."""
    return 3 ** a - mnum(a) * 2 ** a


def v2(n):
    n = abs(n)
    if n == 0:
        return 0
    return (n & -n).bit_length() - 1


def darm(a):
    """D(a) = max{d : 2^d |k_a| < (3/2)^a} = max{d : 2^(d+a) |k_a| < 3^a}."""
    k = abs(kres(a))
    if k == 0:
        return 0
    d = 0
    while (1 << (d + 1 + a)) * k < 3 ** a:
        d += 1
    return d if (1 << (d + a)) * k < 3 ** a else -1


def rad(n):
    r = 1
    for p in factorint(abs(n)):
        r *= p
    return r


def rad_frame(m, k):
    """rad(A*B*C) for A = m 2^a, B = k, C = 3^a: the primes of m, of k, and 2, 3.

    Factoring m and |k| separately is the whole point -- the product is a
    ~2a-digit number no general-purpose factoriser will touch.
    """
    primes = {2, 3} | set(factorint(m)) | set(factorint(abs(k)))
    r = 1
    for p in primes:
        r *= p
    return r


def frame(a):
    """(A, B, C, g, radical, primitive quality, raw quality)."""
    m = mnum(a)
    k = kres(a)
    A, B, C = m * 2 ** a, k, 3 ** a
    g = gcd(m, 3 ** a)
    R = rad_frame(m, k)
    qp = log(C // g) / log(R) if R > 1 and C // g > 1 else 0.0
    qr = log(C) / log(R) if R > 1 and C > 1 else 0.0
    return A, B, C, g, R, qp, qr


def is_failure(a):
    return (1 << a) * abs(kres(a)) < 3 ** a


EXC = [1, 2, 3, 4, 7]


def main():
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 140
    t0 = time.time()

    # ---------------------------------------------------------------- [A]
    print("[A] the five exceptions as abc triples")
    print("      a |          A |     B |          C |  g |     rad | q_prim |  q_raw")
    for a in EXC:
        A, B, C, g, R, qp, qr = frame(a)
        print(f"    {a:3d} | {A:10d} | {B:5d} | {C:10d} | {g:2d} | {R:7d} |"
              f" {qp:6.4f} | {qr:6.4f}")
    A, B, C, g, R, qp, qr = frame(3)
    print(f"    the raw reading at a = 3 is log({C})/log({R}) = {qr:.4f} > 1.63:")
    print(f"    the content is g = {g}, the primitive triple is "
          f"{A//g} + {B//g} = {C//g}, of quality {qp:.4f}")
    print(f"    -> the ledger hypothesis is only true of the *primitive* triple")

    # ---------------------------------------------------------------- [B]
    print(f"\n[B] the family's own ledger, a <= {amax}")
    qs = []
    for a in range(1, amax + 1):
        _, _, _, _, _, qp, _ = frame(a)
        qs.append((qp, a))
    qs.sort(reverse=True)
    rec, arec = qs[0]
    print(f"    record over the family: q = {rec:.4f} at a = {arec}"
          f"   (margin to 1.63: {1.63 - rec:.4f})")
    print("    top ten:  " + ",  ".join(f"a={a} q={q:.4f}" for q, a in qs[:10]))
    mean = sum(q for q, _ in qs) / len(qs)
    above1 = sum(1 for q, _ in qs if q > 1.0)
    ranks = {a: i + 1 for i, (_, a) in enumerate(qs)}
    print(f"    mean quality {mean:.4f};  {above1} of {amax} exceed 1.0")
    print("    ranks of the five exceptions: "
          + ", ".join(f"a={a} -> #{ranks[a]}" for a in EXC))
    A, B, C, g, R, qp, _ = frame(arec)
    print(f"    the record triple: {A} = {C} + {-B}, i.e. 3^{arec} + {-B} = {A},"
          f" rad = {R}")
    print(f"    -> the family already sits within {1.63 - rec:.3f} of the global"
          f" abc record 1.6299; the 1.63 cap is NOT a safe assumption")

    # ---------------------------------------------------------------- [C]
    print("\n[C] the price list: what a cap q_max buys")
    print("      q_max | slope(w+D) | slope(min) | verdict")
    for q in [1.2, 4 / 3, QSTAR, 1.4, 1.5, 1.5463, 1.63, 2.0, 3.0, 3.6879, 4.0]:
        s = 2 * LOG2_32 - LOG2_3 / q
        v = ("bounds a itself" if s <= 0 else
             "beats [Zud07] 0.371a" if s / 2 < 0.37008 else
             "beats [Hab03] 0.385a" if s / 2 < 0.38497 else "buys nothing")
        print(f"    {q:7.5f} | {s:10.5f} | {s/2:10.5f} | {v}")
    s163 = 2 * LOG2_32 - LOG2_3 / 1.63
    print(f"    the report's row: q_max = 1.63 -> w+D <= {s163:.5f} a,"
          f" min <= {s163/2:.5f} a  (report: 0.0988)")
    print(f"    threshold q* = log3/(2 log(3/2)) = {QSTAR:.7f};"
          f"  break-even with [Zud07]: q = {LOG2_3/(2*LOG2_32 - 2*0.37008):.4f}")

    # ---------------------------------------------------------------- [D]
    print("\n[D] the Lean constants (rational route log2 3 < 65/41) vs exact reals")
    print(f"    exact:  w+D <= {s163:.5f} a + {log2(12):.4f}")
    print(f"    65/41:  6683(w+D) <= 1324 a + 23961, i.e."
          f" w+D <= {1324/6683:.5f} a + {23961/6683:.4f}")
    bad = [a for a in range(0, 200001)
           if 10 * ((1324 * a + 23961) // 6683) > 2 * a + 35]
    print(f"    'record_ledger_cap' 10(w+D) <= 2a+35 holds for every a <= 2*10^5:"
          f" {len(bad) == 0}")
    bad2 = [a for a in range(0, 200001)
            if 10 * (((1324 * a + 23961) // 6683) // 2) > a + 17]
    print(f"    'record_fibre_cap'  10 d    <= a+17  (d = min):"
          f" {len(bad2) == 0}")
    # the 4/3 threshold: 41*4*2a <= 82*4 + 65*(4 + 5a)  <=>  3a <= 588
    N, M = 4, 3
    are = N * log2(12) / (2 * N - (2 * N - M) * LOG2_3)
    print(f"    'exception_le_of_quality' a <= {588 // 3} at q_max = 4/3"
          f"   (exact real arithmetic: a <= {are:.1f})")
    # the 13/10 threshold: 82*13 + 65*(13 + 16a) <= 41*26a
    thr = min(a for a in range(1, 400) if 82 * 13 + 65 * (13 + 16 * a) <= 41 * 26 * a)
    thr_exact = min(a for a in range(1, 400)
                    if 13 * log2(12) + 16 * a * LOG2_3 <= 26 * a)
    print(f"    'exception_quality' quality >= 13/10 from a >= {thr}"
          f"   (exact real arithmetic: a >= {thr_exact})")

    # ---------------------------------------------------------------- [E]
    print(f"\n[E] the two halves of 'frameRad_core', checked exactly")
    print(f"    E1  rad(ABC) <= 6*mu*kappa  (mu = m_a/(2^w g), kappa = |k_a|/g),"
          f" a <= {amax}")
    viol, tight = 0, 0
    for a in range(1, amax + 1):
        m, k = mnum(a), kres(a)
        g = gcd(m, 3 ** a)
        w = v2(m)
        mu, kappa = m // (2 ** w * g), abs(k) // g
        R = rad_frame(m, k)
        if R > 6 * mu * kappa:
            viol += 1
        if R == 6 * mu * kappa:
            tight += 1
    print(f"        violations: {viol};  equality (mu, kappa squarefree and"
          f" coprime to 6): {tight} of {amax}")
    print("    E2  rad * 2^(w+D+2a) * g^2 <= 12 * 3^(2a) at the five exceptions")
    print("          a | w | D |            lhs |            rhs | slack (bits)")
    for a in EXC:
        m, k = mnum(a), kres(a)
        g = gcd(m, 3 ** a)
        w, D = v2(m), darm(a)
        R = rad_frame(m, k)
        lhs = R * 2 ** (w + D + 2 * a) * g * g
        rhs = 12 * 3 ** (2 * a)
        print(f"        {a:3d} | {w} | {D} | {lhs:14d} | {rhs:14d} |"
              f" {log2(rhs / lhs):7.3f}")
    print("    (the hypothesis at D = 0 IS the exception condition, so the core"
          " speaks about E;")
    print("     the slack is the non-squarefree part of mu*kappa, which the"
          " radical bound cannot see)")

    # ---------------------------------------------------------------- [F]
    print("\n[F] what a fibre of depth d at a would force (g = 1)")
    print("           a |   d |  quality forced")
    for a in [10 ** 3, 10 ** 4, 10 ** 6]:
        for frac in [0.05, 0.0988, 0.15, 0.20]:
            d = int(frac * a)
            den = 2 * LOG2_32 * a + log2(12) - 2 * d
            q = LOG2_3 * a / den
            print(f"    {a:8d} | {d:5d} |  {q:8.4f}"
                  + ("   <- above the abc record 1.6299" if q > 1.6299 else ""))

    # ---------------------------------------------------------------- [G]
    print("\n[G] the circularity, quantified")
    print(f"    ledger slope vanishes at q* = {QSTAR:.7f} = log3/(2 log(3/2))")
    print("    unconditional lower bound for the quality of an exception"
          " (from [E]'s inequality):")
    print("        q >= 1.58496 a / (1.16993 a + 3.585 - (w+D)) -> q* as a -> oo")
    for a in EXC:
        w, D = v2(mnum(a)), darm(a)
        lb = LOG2_3 * a / (2 * LOG2_32 * a + log2(12) - (w + D))
        _, _, _, _, _, qp, _ = frame(a)
        print(f"      a = {a}: bound {lb:.4f}, measured {qp:.4f}")
    for a in [74, 10 ** 2, 10 ** 3, 10 ** 6]:
        lb = LOG2_3 * a / (2 * LOG2_32 * a + log2(12))
        print(f"      a = {a}: bound {lb:.4f}"
              + ("  (>= 13/10, the Lean constant)" if lb >= 1.3 else ""))
    print("    so: 'deep fibres are high-quality triples' and 'a quality cap"
          " bounds fibres'")
    print("    are the same statement -- the ledger is a benchmark, not a"
          " mechanism.")

    print(f"\n    [{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
