#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Prop. 1 / Cor. 6 -- one check per DECLARATION of BB61/RouteANormalForm.lean.

`m2_verify.py` checks P3 and C6 in the note's own coordinates (rho, |N(alpha)|).  The Lean
file states them in the coordinates of the `QuadSetup` structure instead: the conjugate is
`beta = a - alpha` (so `rho = |beta|`) and the norm enters as the constant coefficient `b`
of `X^2 - aX - b` (so `|N| = |b|`).  This script re-runs the sweep through those, so that a
sign or an off-by-one in the translation cannot hide:

L1  routeAExponent_eq_inv_add_inv          A(alpha) = 1/L + 1/R, L = log2 alpha, R = log2 1/rho
L2  one_lt_logAlpha_iff                    L > 1 iff alpha > 2
L3  routeAExponent_lt_one_iff_*            the four-way equivalence of Proposition 1
L4  routeAExponent_mul_logAlpha            A(alpha) * L = 1 + L/R
L5  one_lt_div_sub_one / div_sub_one_lt_*  the threshold L/(L-1): > 1, strictly decreasing, -> 1
L6  abs_beta_eq_div                        |beta| = |b| / alpha at degree two
L7  logRhoInv_eq_sub                       R = L - log2 |b|
L8  routeAExponent_lt_one_iff_quadratic    Corollary 6
L9  routeAExponent_lt_one_iff_four_lt      Corollary 6 at units: A < 1 iff alpha > 4
L10 one_lt_logRhoInv_of_lt_one             A < 1 forces R > 1

Sweeps run over m0_coverage.json (9287 Pisot numbers, 440 of them quadratic).  The
quadratic rows are recomputed from their integer coefficients at 60 decimal digits, so L6
and L7 test the identities and not the stored floats.  Requires mpmath.
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


def L2(x):
    return math.log2(x)


# ---------------- L1: the exponent is 1/L + 1/R ----------------
dev = 0.0
for r in COV:
    Lg, R = L2(r['a']), L2(1 / r['rho'])
    dev = max(dev, abs((1 / Lg + 1 / R) - r['A']))
report('L1', dev < 1e-9,
       'A = 1/L + 1/R on all %d Pisot (max deviation %.1e)' % (len(COV), dev))

# ---------------- L2: L > 1 iff alpha > 2 ----------------
bad = sum(1 for r in COV if (L2(r['a']) > 1) != (r['a'] > 2))
report('L2', bad == 0,
       'L > 1 iff alpha > 2 on all %d Pisot (all of which have alpha > 2)' % len(COV))

# ---------------- L3: the four-way equivalence ----------------
bad_nf = bad_th = bad_rho = 0
for r in COV:
    Lg, R = L2(r['a']), L2(1 / r['rho'])
    A = 1 / Lg + 1 / R
    if ((Lg - 1) * (R - 1) > 1) != (A < 1):
        bad_nf += 1
    if (Lg / (Lg - 1) < R) != (A < 1):
        bad_th += 1
    if (r['rho'] < 2 ** (-(Lg / (Lg - 1)))) != (A < 1):
        bad_rho += 1
report('L3', bad_nf == bad_th == bad_rho == 0,
       'A<1 <-> (L-1)(R-1)>1 <-> R > L/(L-1) <-> rho < 2^{-L/(L-1)} on all %d Pisot'
       % len(COV))

# ---------------- L4: A * L = 1 + L/R ----------------
dev = 0.0
for r in COV:
    Lg, R = L2(r['a']), L2(1 / r['rho'])
    A = 1 / Lg + 1 / R
    dev = max(dev, abs(A * Lg - (1 + Lg / R)))
report('L4', dev < 1e-9,
       'A * log2 alpha = 1 + L/R on all %d Pisot (max deviation %.1e)' % (len(COV), dev))

# ---------------- L5: the threshold L/(L-1) ----------------
thr = [(L2(r['a']), L2(r['a']) / (L2(r['a']) - 1)) for r in COV]
above = all(t > 1 for _, t in thr)
srt = sorted(set(thr))
anti = all(srt[i][1] > srt[i + 1][1] for i in range(len(srt) - 1))
tail = [float(mp.mpf(L) / (mp.mpf(L) - 1)) for L in (10, 100, 1000, 10 ** 6)]
to_one = all(tail[i] > tail[i + 1] > 1 for i in range(len(tail) - 1)) and tail[-1] - 1 < 1e-5
report('L5', above and anti and to_one,
       'threshold L/(L-1) > 1 on all %d Pisot, strictly decreasing in L, and -> 1 '
       '(value %.9f at L = 10^6)' % (len(COV), tail[-1]))

# ---------------- L6/L7/L8/L9: degree two, recomputed exactly ----------------
dev6 = dev7 = 0.0
bad8 = bad9 = 0
nunits = 0
for r in QUADS:
    c1, c0 = r['coeffs'][1], r['coeffs'][2]
    a, b = -c1, -c0                       # X^2 - aX - b, the `QuadSetup` normalisation
    disc = mp.mpf(a) ** 2 + 4 * b
    alpha = (mp.mpf(a) + mp.sqrt(disc)) / 2
    beta = mp.mpf(a) - alpha              # `QuadSetup.beta`
    dev6 = max(dev6, float(abs(abs(beta) - abs(mp.mpf(b)) / alpha)))
    Lg = mp.log(alpha) / mp.log(2)
    R = mp.log(1 / abs(beta)) / mp.log(2)
    dev7 = max(dev7, float(abs(R - (Lg - mp.log(abs(mp.mpf(b))) / mp.log(2)))))
    A = 1 / Lg + 1 / R
    fires = A < 1
    if ((Lg - 1) * (Lg - mp.log(abs(mp.mpf(b))) / mp.log(2) - 1) > 1) != fires:
        bad8 += 1
    if abs(b) == 1:
        nunits += 1
        if fires != (alpha > 4):
            bad9 += 1

report('L6', dev6 < 1e-45,
       '|beta| = |b| / alpha on all %d quadratics (max deviation %.1e)' % (len(QUADS), dev6))
report('L7', dev7 < 1e-45,
       'R = L - log2 |b| on all %d quadratics (max deviation %.1e)' % (len(QUADS), dev7))
report('L8', bad8 == 0,
       'Cor 6: A<1 <-> (log2 alpha - 1)(log2(alpha/|b|) - 1) > 1 on all %d quadratics'
       % len(QUADS))
report('L9', bad9 == 0,
       'Cor 6 at units: A<1 <-> alpha > 4 on all %d quadratic units' % nunits)

# ---------------- L10: A < 1 forces R > 1 ----------------
fired = [r for r in COV if r['A'] < 1]
bad = sum(1 for r in fired if not L2(1 / r['rho']) > 1)
report('L10', bad == 0,
       'A < 1 forces R > 1: holds at all %d firing Pisot numbers of the enumeration'
       % len(fired))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m2_prop1_lean.json', 'w'), indent=1)
