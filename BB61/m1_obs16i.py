#!/usr/bin/env python3
"""M1 Observation 16(i): the two one-sided Erdos products and their limits.

Companion of `BB61/WeylProduct.lean`, which proves in Lean that along a ladder
`h_k` of the recurrence `X^2 - aX - b`

    futProd(h_k)  = prod_{j>=1} |cos(pi h_k (alpha-1) alpha^-j)|  ->  biProd(A)
    pastProd(h_k) = prod_{m>=0} |cos(pi h_k (beta-1) beta^m)|     ->  biProd(B)   [needs |b|=1]

where A = shapeFut = f0(alpha-1)/(alpha-beta), B = shapePast = f0(beta-1)/(alpha-beta),
f0 = h1 - beta h0, e0 = h1 - alpha h0, and biProd(x) = prod_{n in Z} |cos(pi x alpha^n)|.

The three things checked here:

  (1) the two Lean limits are the actual limits (`tendsto_futProd`, `tendsto_pastProd`);
  (2) `biProd(B) = biProd(A')` with A' = shapeFutC = -e0(alpha-1)/(alpha-beta)
      (`biProd_shapePast_eq_shapeFutC`) -- the reflection at a unit;
  (3) THE CORRECTION.  Observation 16(i) as stated in the note -- "the future factor and
      the past factor converge to the SAME value" -- is FALSE for a general ladder.  It
      holds exactly when biProd(lambda(alpha-1)) = biProd(lambda'(alpha-1)), for which
      lambda' = +-alpha^s lambda suffices (`biProd_shapePast_eq_of_pow`); the note's two
      witnesses (lambda = 1 and lambda = 1/2 at alpha = 1+sqrt2) both have lambda' = lambda,
      i.e. 2h1 = a h0.  At alpha = (3+sqrt13)/2 with the ladder 1, 4, 13, 43, 142, ...
      the two limits are 0.4004074010 and 0.0126597907.

Double precision is useless here (h_k ~ alpha^k needs ~k*log10(alpha) guard digits, the
F10 trap of note-1061-M1 section 7); everything runs in mpmath at precision set from k.

Writes m1_obs16i.json.
"""
import json
import math
from mpmath import mp, mpf, sqrt, cos, pi, log


def ncos(x):
    return abs(cos(pi * x))


def setup(a, b, kmax):
    """(alpha, beta) at a precision that carries alpha^kmax."""
    disc = a * a + 4 * b
    al0 = (a + math.sqrt(disc)) / 2.0
    mp.dps = int(90 + 2 * kmax * math.log10(al0))
    al = (mpf(a) + sqrt(mpf(disc))) / 2
    return al, mpf(a) - al


def ladder(a, b, h0, h1, kmax):
    h = [h0, h1]
    for _ in range(2, kmax + 1):
        h.append(a * h[-1] + b * h[-2])
    return h


def fut_prod(H, al, tol=mpf('1e-50')):
    J = int(float(log(mpf(abs(H)) * abs(al - 1) / tol) / log(al))) + 5
    p = mpf(1)
    for j in range(1, J + 1):
        p *= ncos(H * (al - 1) / al**j)
    return p


def past_prod(H, al, be, tol=mpf('1e-50')):
    M = int(float(log(mpf(abs(H)) * abs(be - 1) / tol) / log(1 / abs(be)))) + 5
    p = mpf(1)
    for m in range(0, M + 1):
        p *= ncos(H * (be - 1) * be**m)
    return p


def bi_prod(x, al, tol=mpf('1e-50')):
    """prod_{n in Z} |cos(pi x alpha^n)|, truncated where both tails are within tol of 1."""
    N = int(70 / math.log10(float(al))) + 8
    p = mpf(1)
    for n in range(-N, N + 1):
        p *= ncos(x * al**n)
    return p


def shapes(a, b, h0, h1, al, be):
    f0 = h1 - be * h0
    e0 = h1 - al * h0
    return (f0 * (al - 1) / (al - be),        # A  = shapeFut  = lambda (alpha-1)
            f0 * (be - 1) / (al - be),        # B  = shapePast = lambda (beta-1)
            -e0 * (al - 1) / (al - be),       # A' = shapeFutC = lambda'(alpha-1)
            e0, f0)


CASES = [
    # (a, b, h0, h1, label)   -- X^2 - aX - b, norm N(alpha) = -b
    (2,  1, 2, 2, '1+sqrt2, trace ladder'),
    (2,  1, 1, 2, '1+sqrt2, Pell 1,2,5,12'),
    (3,  1, 2, 3, '(3+sqrt13)/2, trace ladder'),
    (3,  1, 1, 4, '(3+sqrt13)/2, ladder 1,4,13,43'),
    (5,  1, 2, 5, '(5+sqrt29)/2, trace ladder'),
    (1,  1, 2, 1, 'golden, Lucas 2,1,3,4,7'),
    (1,  1, 1, 3, 'golden, ladder 1,3,4,7,11'),
    (4, -1, 2, 4, '2+sqrt3, trace ladder'),
    (4, -1, 1, 4, '2+sqrt3, ladder 1,4,15,56'),
    (4, -1, 3, 7, '2+sqrt3, ladder 3,7,25,93'),
    (5,  2, 2, 5, 'NON-UNIT X^2-5X-2, trace'),
    (4,  2, 2, 4, 'NON-UNIT X^2-4X-2, trace'),
]

KMAX = 40
out = []
print('%-32s %5s %6s %18s %18s %18s' %
      ('case', 'N(a)', "l'=l?", 'futProd(h_k)', 'pastProd(h_k)', 'biProd(A)'))
for a, b, h0, h1, label in CASES:
    al, be = setup(a, b, KMAX)
    h = ladder(a, b, h0, h1, KMAX)
    A, B, Ac, e0, f0 = shapes(a, b, h0, h1, al, be)
    unit = abs(b) == 1
    sym = (2 * h1 == a * h0)                      # e0 = -f0, i.e. lambda' = lambda
    F = fut_prod(h[KMAX], al)
    Pp = past_prod(h[KMAX], al, be)
    bA, bB, bAc = bi_prod(A, al), bi_prod(B, al), bi_prod(Ac, al)
    rec = dict(label=label, a=a, b=b, h0=h0, h1=h1, norm=-b, unit=unit, lam_sym=sym,
               alpha=float(al), futProd=float(F), pastProd=float(Pp),
               biProd_A=float(bA), biProd_B=float(bB), biProd_Ac=float(bAc),
               err_fut=float(abs(F - bA)), err_past=float(abs(Pp - bB)),
               err_reflect=float(abs(bB - bAc)), gap=float(abs(bA - bB)))
    out.append(rec)
    print('%-32s %5d %6s %18.14f %18.14f %18.14f' %
          (label, -b, 'yes' if sym else 'no', float(F), float(Pp), float(bA)))

print()
verdict = {}
# the profiles settle at rate rho^{2k} (`abs_future_band` of BB61/Plateau.lean), so the
# tolerance at rung KMAX has to be measured in rho^{2*KMAX}, not in machine epsilon.
def tol(r):
    return 1000 * abs(r['a'] - r['alpha']) ** (2 * KMAX)

# (1) tendsto_futProd -- unconditional, unit or not
bad = [r['label'] for r in out if r['err_fut'] > tol(r)]
verdict['tendsto_futProd'] = dict(
    kind='futProd(h_k) -> biProd(shapeFut), every alpha', ok=not bad, failures=bad,
    worst_ratio=max(r['err_fut'] / tol(r) for r in out))

# (2) tendsto_pastProd -- at a unit only; and the hypothesis |b| = 1 is necessary
uni = [r for r in out if r['unit']]
non = [r for r in out if not r['unit']]
bad = [r['label'] for r in uni if r['err_past'] > tol(r)]
verdict['tendsto_pastProd'] = dict(
    kind='pastProd(h_k) -> biProd(shapePast), needs |b|=1', ok=not bad, failures=bad,
    worst_ratio=max(r['err_past'] / tol(r) for r in uni))
verdict['unit_hypothesis_needed'] = dict(
    kind='off a unit the past factor collapses to 0, biProd(B) does not',
    ok=all(r['pastProd'] < 1e-8 < r['biProd_B'] for r in non),
    non_unit=[(r['label'], r['pastProd'], r['biProd_B']) for r in non])

# (3) the reflection biProd(B) = biProd(A') at a unit
bad = [r['label'] for r in uni if r['err_reflect'] > 1e-40]
verdict['biProd_shapePast_eq_shapeFutC'] = dict(
    kind="biProd(B) = biProd(A') at a unit", ok=not bad, failures=bad,
    worst=max(r['err_reflect'] for r in uni))

# (4) Observation 16(i): holds when lambda' = lambda, FAILS in general
good = [r for r in uni if r['lam_sym']]
bad = [r for r in uni if not r['lam_sym']]
verdict['obs16i_when_sym'] = dict(
    kind='2h1 = a h0  =>  the two limits agree', ok=all(r['gap'] < 1e-40 for r in good),
    worst=max(r['gap'] for r in good))
witness = max(bad, key=lambda r: r['gap'])
verdict['obs16i_false_in_general'] = dict(
    kind='(i) as stated is FALSE without 2h1 = a h0',
    ok=witness['gap'] > 1e-3, witness=witness['label'],
    futLimit=witness['biProd_A'], pastLimit=witness['biProd_B'], gap=witness['gap'],
    note='norm +1 ladders still agree for every h, by past_eq_future')

# norm +1 agrees for every ladder, symmetric or not (past_eq_future)
plus = [r for r in uni if r['norm'] == 1]
verdict['norm_plus_one_always'] = dict(
    kind='b = -1: futProd = pastProd at EVERY mode, no limit involved',
    ok=all(abs(r['futProd'] - r['pastProd']) < 1e-40 for r in plus),
    worst=max(abs(r['futProd'] - r['pastProd']) for r in plus))

# (5) the rate: |futProd(h_k) - biProd(A)| falls by rho^2 per rung (abs_future_band)
rates = []
for a, b, h0, h1, label in CASES:
    al, be = setup(a, b, KMAX)
    h = ladder(a, b, h0, h1, KMAX)
    A = shapes(a, b, h0, h1, al, be)[0]
    bA = bi_prod(A, al)
    ds = [abs(fut_prod(h[k], al) - bA) for k in (KMAX - 8, KMAX - 4, KMAX)]
    if min(ds) > 0:
        # measured exponent p in  d_k ~ rho^{p k};  the theory says p = 2
        ps = [float(log(ds[i + 1] / ds[i]) / (4 * log(abs(be)))) for i in range(2)]
        rates.append(dict(label=label, exponents=ps))
verdict['rate_rho_2k'] = dict(
    kind='|futProd(h_k) - biProd(A)| ~ rho^{2k} (abs_future_band)',
    ok=all(abs(x - 2.0) < 0.05 for r in rates for x in r['exponents']),
    rates=rates)

for name, v in verdict.items():
    print('%-34s %-52s %s' % (name, v['kind'], 'OK' if v['ok'] else 'FAIL'))

json.dump(dict(cases=out, verdict=verdict), open('m1_obs16i.json', 'w'), indent=1)
print('\n[results written to m1_obs16i.json]')
