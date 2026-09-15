#!/usr/bin/env python3
"""
T-T (2026-08-24) -- Newhouse thickness as a death certificate for the support route.

Machinery imported from old-plans/plan-dubD1O5.html section 4.1 (Newhouse gap lemma,
[CHM02] section 4 / [PT93] 4.2, in the form corrected by that plan's 2026-08-22 pass:
product >= 1 gives "C-K CONTAINS an interval"; the translate/gap condition upgrades it
to "C-K IS an interval").

Object: X(alpha) = (C - K) mod 1, the confinement set of plan-1061 section 2.1(a).
  C = digit Cantor set, two pieces of ratio 1/alpha, gap (alpha-2)/alpha  -> tau_C = 1/(alpha-2)
  K = {sum_m c_m delta_m}, c_m = (abar-1) abar^m, ratio rho = |abar|      -> tau_K = rho/(1-2rho)

Theorem T (degree 2): tau_C * tau_K >= 1  =>  X(alpha) = T, i.e. NO gap certificate exists.

Three blocks:
  (1) side conditions of the gap lemma, over the whole quadratic Pisot family
  (2) thickness product vs. an independent FFT recomputation of the gap (cross-checks M0 6.2)
  (3) the unit corollary and the two infinite full-support families
No claim of the converse: the lemma is sufficient for death, never necessary.
"""
import math
import numpy as np


def subsums(coeffs):
    """all sums of subsets of `coeffs`, as a flat array"""
    v = np.zeros(1)
    for c in coeffs:
        v = np.concatenate([v, v + c])
    return v


def gap_of_X(a, b, M=20, MK=20, N=1 << 20):
    """Longest hole of X(alpha)=(C-K) mod 1 for x^2-ax-b, by outer cover + FFT.

    Over-approximates X, so any hole reported is genuine. Independent of BB61/m0_*.
    """
    disc = a * a + 4 * b
    al = (a + math.sqrt(disc)) / 2
    ab = (a - math.sqrt(disc)) / 2
    rho = abs(ab)
    C = subsums([(al - 1) * al ** -(k) for k in range(1, M + 1)])
    wC = al ** -M                                          # exact tail bound for C
    K = subsums([(ab - 1) * ab ** m for m in range(MK)])
    eK = abs(ab - 1) * rho ** MK / (1 - rho)               # exact tail bound for K
    A = np.zeros(N, bool); A[((C % 1.0) * N).astype(np.int64) % N] = True
    B = np.zeros(N, bool); B[((K % 1.0) * N).astype(np.int64) % N] = True
    corr = np.fft.irfft(np.fft.rfft(A.astype(float)) * np.conj(np.fft.rfft(B.astype(float))), N)
    occ = corr > 0.5
    dil = int(math.ceil((wC + 2 * eK) * N)) + 2            # absorb interval widths + rounding
    for s in range(-dil, dil + 1):
        occ |= np.roll(occ, s)
    if occ.all():
        return al, rho, 0.0
    idx = np.flatnonzero(occ)
    return al, rho, (np.diff(np.concatenate([idx, [idx[0] + N]])) - 1).max() / N


def quadratic_family():
    """every irreducible quadratic Pisot x^2-ax-b with alpha>2 and 0<rho<1/2"""
    out = []
    for a in range(1, 40):
        for b in range(-40, 41):
            if b == 0:
                continue
            disc = a * a + 4 * b
            if disc <= 0:
                continue
            s = math.isqrt(disc)
            if s * s == disc:
                continue                                   # reducible
            al = (a + math.sqrt(disc)) / 2
            rho = abs((a - math.sqrt(disc)) / 2)
            if al > 2 and 0 < rho < 0.5:
                out.append((al, a, b, rho))
    return sorted(out)


def taus(al, rho):
    return 1 / (al - 2), rho / (1 - 2 * rho)


# ---- (1) the gap lemma's two side conditions, over the whole family ---------------
fam = quadratic_family()
mA = mB = float("inf")
for al, a, b, rho in fam:
    ab = math.copysign(rho, -b)                            # alpha*abar = -b
    diamK = (1 + rho) / (1 - rho) if ab < 0 else 1.0
    gapK = abs(ab - 1) * (1 - 2 * rho) / (1 - rho)
    mA = min(mA, diamK - (al - 2) / al)                    # diam K > max gap of C
    mB = min(mB, 1.0 - gapK)                               # diam C > max gap of K
print(f"(1) side conditions over {len(fam)} quadratic Pisot alpha>2, rho<1/2:")
print(f"    min (diam K - gap_max C) = {mA:.6f}   [M0's no-go 2, verbatim]")
print(f"    min (diam C - gap_max K) = {mB:.6f}")
print("    both > 0 => whenever tau_C*tau_K >= 1, C-K IS an interval of length >= 2 => X = T\n")

# ---- (2) thickness product vs. independent FFT gap; cross-check against M0 6.2 ----
M0 = {(2, 1): "none", (3, -1): "none", (3, 1): "none", (4, -1): "0.05256",
      (4, 1): "0.03444", (4, 2): "none", (5, 2): "0.00028", (6, -2): "0.00521"}
print("(2) thickness product vs. gap  (M0 column = note-1061-M0.html section 6.2)")
print(f"    {'min poly':<12}{'alpha':>9}{'rho':>8}{'tau_C':>8}{'tau_K':>8}{'product':>9}{'gap':>11}   M0")
for (a, b), m0 in sorted(M0.items(), key=lambda t: (t[0][0] + math.sqrt(t[0][0] ** 2 + 4 * t[0][1])) / 2):
    al, rho, g = gap_of_X(a, b)
    tC, tK = taus(al, rho)
    mp = f"X^2-{a}X{'-' if b > 0 else '+'}{abs(b)}"
    flag = " <= DEAD" if tC * tK >= 1 else ""
    print(f"    {mp:<12}{al:9.4f}{rho:8.4f}{tC:8.3f}{tK:8.3f}{tC*tK:9.3f}{g:11.5f}   {m0}{flag}")
print("    every product>=1 row has gap 0; every gapped row has product<1.")
print("    X^2-3X-1: product 0.589 and still no gap -- the converse is FALSE, do not assert it.\n")

# ---- (3) the unit corollary and the two infinite families ------------------------
print("(3) Corollary T1 -- units: tau_C = tau_K <=> rho = 1/alpha <=> |b| = 1; product = (alpha-2)^-2")
for al, a, b, rho in fam:
    if abs(b) == 1 and al < 6:
        p = (al - 2) ** -2
        print(f"    alpha={al:8.4f}  X^2-{a}X{'-' if b > 0 else '+'}1   product={p:8.4f}"
              + ("   FULL SUPPORT (proved)" if p >= 1 else ""))
print("    => exactly two quadratic Pisot units in (2,3]: 1+sqrt2 and (3+sqrt5)/2.\n")

print("(3) Corollary T2 -- two infinite full-support families, product decreasing to 1+")
print(f"    {'k':>5}  {'min poly':<18}{'alpha':>12}{'rho':>10}{'product':>10}   gap(FFT)")
for k in [2, 3, 4, 5, 20, 100, 1000]:
    for a, b in [(2 * k, k), (2 * k + 1, -k)]:
        al = (a + math.sqrt(a * a + 4 * b)) / 2
        rho = abs(b) / al
        tC, tK = taus(al, rho)
        g = f"{gap_of_X(a, b)[2]:.7f}" if k <= 5 else "  (not run)"
        mp = f"X^2-{a}X{'-' if b > 0 else '+'}{abs(b)}"
        print(f"    {k:>5}  {mp:<18}{al:12.3f}{rho:10.6f}{tC*tK:10.6f}   {g}")

print("\nCEILING: thickness is a property of C(alpha) as a compact subset of R, so L0-6 (xvi)")
print("([Rau70]) bars it from ever PROVING 10.61. This prunes Route D / X8; it is not an engine.")
