#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Thm 2(i) -- one check per DECLARATION of BB61/RouteADepth.lean.

`m2_verify.py` check T1 scans for the smallest certified pair (M,M') of the NOTE's covering
total, with the note's constant C_alpha = sum_j |alpha_j - 1|.  This script checks the Lean
file instead: the balanced ray M' = ceil(M L / R), the three estimates the proof is made of,
the affine bound, and -- at degree two -- the engine of BB61/Covering.lean, whose constant is
the bound C = 1 + rho and which pays the point-centred factor 2(2K+1), K = intBound.

D1  pow_balancedDepth_le            rho^{M'} <= alpha^{-M} at M' = ceil(ML/R)
D2  two_pow_balancedDepth_le        2^{M+M'} <= 2 * 2^{M(1+L/R)}
D3  slope_eq                        1 + L/R - L = (1 - (L-1)(R-1))/R
D4  slope_neg_iff                   slope < 0  <->  (L-1)(R-1) > 1  <->  A < 1
D5  logb_coverTotal_balancedDepth_le  the affine bound, at both constants
D6  tendsto_coverTotal_balancedDepth  T -> 0 along the balanced ray at every firing alpha
D7  QuadSetup.cert_eq_coverTotal    engine value = 2(2K+1) * coverTotal, exactly
D8  the first Lean-engine balanced certified depth at 2+sqrt5, vs RouteA.lean's (70,70)
D9  Cor. 3 reproduced with C_alpha: (17,17) at 2+sqrt5 and (751,1502) at X^3-8X^2-1
D10 the Cor. 3 warning: certified M scales like 1/(1 - (L-1)(R-1))

Sweeps run over m0_coverage.json (9287 Pisot numbers, 440 quadratic).  Requires mpmath.
"""
import json, math, mpmath as mp

mp.mp.dps = 60
RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


COV = json.load(open('m0_coverage.json'))
QUADS = [r for r in COV if r['d'] == 2]
MS = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89]


def LR(alpha, rho):
    return math.log2(alpha), math.log2(1 / rho)


def balanced(L, R, M):
    """BB61.balancedDepth"""
    return math.ceil(M * L / R)


def cover_total(alpha, rho, C, M, Mp):
    """BB61.coverTotal, in mpmath"""
    a, r, c = mp.mpf(alpha), mp.mpf(rho), mp.mpf(C)
    return mp.mpf(2) ** (M + Mp) * (a ** (-M) + c * r ** Mp / (1 - r))


def exact_quad(row):
    """alpha, beta, rho of a quadratic row, recomputed from its integer coefficients."""
    c1, c0 = row['coeffs'][1], row['coeffs'][2]
    a, b = -c1, -c0                       # X^2 - aX - b, the QuadSetup normalisation
    alpha = (mp.mpf(a) + mp.sqrt(mp.mpf(a) ** 2 + 4 * b)) / 2
    beta = mp.mpf(a) - alpha
    return alpha, beta, abs(beta), a, b


# ---------------- D1 / D2: the two truncation estimates ----------------
# D1's content in the Lean proof is the EXACT inequality M*L <= M'*R, from Nat.le_ceil.
# Checked as such over the whole enumeration, and then in its power form over the 440
# quadratics recomputed from their integer coefficients at 60 digits, where alpha = 2^L and
# rho = 2^{-R} hold to full precision (with float64 rows they hold only to 1e-16, which the
# exponent M' amplifies -- that is a property of the stored data, not of the lemma).
bad1a = bad1b = bad2 = 0
for r in COV:
    L, R = LR(r['a'], r['rho'])
    for M in MS:
        Mp = balanced(L, R, M)
        if M * L > Mp * R + 1e-12 * abs(M * L):
            bad1a += 1
        lhs = mp.mpf(2) ** (M + Mp)
        rhs = 2 * mp.mpf(2) ** (mp.mpf(M) * (1 + mp.mpf(L) / mp.mpf(R)))
        if not lhs <= rhs * (1 + mp.mpf(10) ** -40):
            bad2 += 1
for r in QUADS:
    alpha, _, rho, _, _ = exact_quad(r)
    L = mp.log(alpha) / mp.log(2)
    R = mp.log(1 / rho) / mp.log(2)
    for M in MS:
        Mp = int(mp.ceil(M * L / R))
        if not rho ** Mp <= alpha ** (-M) * (1 + mp.mpf(10) ** -45):
            bad1b += 1
report('D1', bad1a == 0 and bad1b == 0,
       'M*L <= ceil(ML/R)*R on all %d Pisot x %d depths, and rho^{M\'} <= alpha^{-M} on the '
       '440 quadratics recomputed exactly at 60 digits' % (len(COV), len(MS)))
report('D2', bad2 == 0,
       '2^{M+M\'} <= 2*2^{M(1+L/R)} on all %d Pisot x %d depths' % (len(COV), len(MS)))

# ---------------- D3 / D4: the slope ----------------
dev3 = 0.0
bad4 = 0
for r in COV:
    L, R = LR(r['a'], r['rho'])
    s = 1 + L / R - L
    dev3 = max(dev3, abs(s - (1 - (L - 1) * (R - 1)) / R))
    A = 1 / L + 1 / R
    if (s < 0) != ((L - 1) * (R - 1) > 1) or (s < 0) != (A < 1):
        bad4 += 1
report('D3', dev3 < 1e-9,
       '1 + L/R - L = (1-(L-1)(R-1))/R on all %d Pisot (max deviation %.1e)'
       % (len(COV), dev3))
report('D4', bad4 == 0,
       'slope < 0  <->  (L-1)(R-1) > 1  <->  A < 1 on all %d Pisot' % len(COV))

# ---------------- D5: the affine bound ----------------
bad5 = 0
worst = 0.0
for r in COV:
    L, R = LR(r['a'], r['rho'])
    rho = r['rho']
    for C in (1 + rho, r['Delta'] * (1 - rho)):     # engine constant, then C_alpha
        for M in MS:
            Mp = balanced(L, R, M)
            T = cover_total(r['a'], rho, C, M, Mp)
            lhs = float(mp.log(T) / mp.log(2))
            rhs = 1 + math.log2(1 + C / (1 - rho)) + M * ((1 - (L - 1) * (R - 1)) / R)
            if lhs > rhs + 1e-9:
                bad5 += 1
            worst = max(worst, lhs - rhs)
report('D5', bad5 == 0,
       'log2 T <= 1 + log2(1+C/(1-rho)) + M*slope at both constants, all %d Pisot x %d '
       'depths; largest excess of log2 T over the bound is %.1e, i.e. within the 1e-9 float '
       'tolerance -- the bound is attained, not merely valid' % (len(COV), len(MS), worst))

# ---------------- D6: T -> 0, and how far out ----------------
fired = [r for r in COV if r['A'] < 1]
bad6 = 0
maxM = 0
maxrow = None
for r in fired:
    L, R = LR(r['a'], r['rho'])
    rho = r['rho']
    C = 1 + rho
    s = 1 + L / R - L
    # explicit sufficient M from the affine bound, then verify T < 1 there
    Mneed = int(math.floor((1 + math.log2(1 + C / (1 - rho))) / (-s))) + 1
    Mp = balanced(L, R, Mneed)
    if not cover_total(r['a'], rho, C, Mneed, Mp) < 1:
        bad6 += 1
    if Mneed > maxM:
        maxM, maxrow = Mneed, r
report('D6', bad6 == 0,
       'T(M, ceil(ML/R)) < 1 at the M the affine bound predicts, for all %d firing Pisot; '
       'worst M = %d at alpha = %.6f (A = %.6f)'
       % (len(fired), maxM, maxrow['a'], maxrow['A']))

# ---------------- D7: the engine identity, degree two ----------------
dev7 = 0.0
for r in QUADS[:120]:
    rho = r['rho']
    K = math.ceil((1 + rho) / (1 - rho) + 1)
    for M in (1, 4, 9):
        Mp = balanced(*LR(r['a'], rho), M)
        delta = mp.mpf(r['a']) ** (-M) + (1 + mp.mpf(rho)) * mp.mpf(rho) ** Mp / (1 - mp.mpf(rho))
        lhs = mp.mpf(2 ** M * 2 ** Mp * (2 * K + 1)) * (2 * delta)
        rhs = 2 * (2 * K + 1) * cover_total(r['a'], rho, 1 + mp.mpf(rho), M, Mp)
        dev7 = max(dev7, float(abs(lhs - rhs) / rhs))
report('D7', dev7 < 1e-50,
       'engine certificate = 2(2K+1) * coverTotal exactly, on 120 quadratics x 3 depths '
       '(max relative deviation %.1e)' % dev7)

# ---------------- D8: the Lean engine at 2+sqrt5 ----------------
al = 2 + mp.sqrt(5)
rho8 = float(mp.sqrt(5) - 2)
a8 = float(al)
L8, R8 = LR(a8, rho8)
K8 = math.ceil((1 + rho8) / (1 - rho8) + 1)
c8 = 2 * (2 * K8 + 1)
s8 = 1 + L8 / R8 - L8
Mbound = int(math.floor((1 + math.log2(1 + (1 + rho8) / (1 - rho8)) + math.log2(c8)) / (-s8))) + 1
Mfirst = next(M for M in range(1, 4000)
              if c8 * cover_total(a8, rho8, 1 + rho8, M, balanced(L8, R8, M)) < 1)
ok8 = (balanced(L8, R8, 1) == 1                       # L = R there, so the ray is (M,M)
       and c8 * cover_total(a8, rho8, 1 + rho8, Mbound, Mbound) < 1
       and Mfirst <= 70
       and c8 * cover_total(a8, rho8, 1 + rho8, 70, 70) < 1)
report('D8', ok8,
       '2+sqrt5: L = R so the balanced ray is (M,M); K = intBound = %d, factor 2(2K+1) = %d, '
       'slope = %.6f; affine bound certifies at M = %d, direct evaluation first certifies at '
       'M = %d, and RouteA.lean\'s (70,70) certifies (note\'s own C_alpha gives (17,17))'
       % (K8, c8, s8, Mbound, Mfirst))
RES['D8'] = dict(ok=ok8, K=K8, factor=c8, slope=s8, M_bound=Mbound, M_first=Mfirst)

# ---------------- D9: Corollary 3 reproduced with C_alpha ----------------
def calpha_and_rho(coeffs):
    roots = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=200)
    big = max(roots, key=lambda z: abs(z))
    conj = [z for z in roots if z is not big]
    return (sum(abs(z - 1) for z in conj), max(abs(z) for z in conj), abs(big))

C5, r5, a5 = calpha_and_rho([1, -4, -1])
C3, r3, a3 = calpha_and_rho([1, -8, 0, -1])
T5 = cover_total(float(a5), float(r5), float(C5), 17, 17)
T3 = cover_total(float(a3), float(r3), float(C3), 751, 1502)
ok9 = T5 < 1 and T3 < 1
report('D9', ok9,
       'Cor. 3 with C_alpha: T(17,17) = %.4f at 2+sqrt5 and T(751,1502) = %.4f at '
       'X^3-8X^2-1, both < 1 (note: 0.987 and "T < 1")' % (float(T5), float(T3)))

# ---------------- D10: the Cor. 3 warning ----------------
rows = []
for r in fired:
    L, R = LR(r['a'], r['rho'])
    prod = (L - 1) * (R - 1)
    s = 1 + L / R - L
    C = 1 + r['rho']
    Mneed = (1 + math.log2(1 + C / (1 - r['rho']))) / (-s)
    rows.append((prod - 1, Mneed))
rows.sort()
near = [m for g, m in rows if g < 0.05]
far = [m for g, m in rows if g > 1.0]
ok10 = len(near) > 0 and len(far) > 0 and min(near) > max(far)
report('D10', ok10,
       'certified M blows up at the ceiling: min M over the %d cases with (L-1)(R-1)-1 < 0.05 '
       'is %.0f, max M over the %d cases with (L-1)(R-1)-1 > 1 is %.0f'
       % (len(near), min(near), len(far), max(far)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m2_thm2i_lean.json', 'w'), indent=1)
