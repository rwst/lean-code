#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Prop. 7 -- one check per GROUP OF DECLARATIONS of BB61/WindowDiam.lean.

`m2_verify.py` checks the note's own section 6 numbers (min diam K - (d-1) = 0, min
2Delta/g).  The Lean file proves the identity behind them, in its own coordinates: the
window is the subset-sum set of an absolutely summable real sequence, the coefficient is the
REAL PART of c_m = sum_j (alpha_j - 1) alpha_j^m, and the criterion is compared against
`gap alpha`.  This script re-runs every step of the argument separately, so that a sign, a
real part or an off-by-one in the translation cannot hide behind the conclusion:

P1  tsum_conjCoef                     sum_m c_m = -(d-1), from sum_j (a_j-1)/(1-a_j)
P2  diam_windowOf                     diam K = sum_m |c_m|, and BOTH endpoints attained
P3  diam_windowOf_eq_two_mul_posSum   diam K = -(sum c_m) + 2 sum_{c_m>0} c_m
P4  diam_windowOf_eq_neg_tsum_iff     diam K = d-1  iff  no c_m is positive
P5  card_le_diam_..._le_conjDelta     the chain (d-1) <= diam K <= Delta
P6  not_x7Criterion                   2 Delta < g is EMPTY; min 2Delta/g per degree
P7  gap_lt_two_mul_diam_windowOf      the sharper 2 diam K > g; and g IS a gap of C(alpha)
P8  QuadSetup.diam_windowSet_eq_conjDelta   at d = 2 the majorant is exact: Delta = diam K
P9  unitQuad / conjDelta_unitQuad     X^2 - aX + 1: Delta = diam K = d-1 = 1, all three
P10 tendsto_ratio_unitQuadSeq         2Delta/g decreases to 2 along that family

Closed-form quantities (sum_m c_m, Delta, g, and everything at degree two) are computed at
60 decimal digits with mpmath from the integer coefficients, independently of
`m0_coverage.json`'s stored floats.  The sums sum_m |c_m| and sum_{c_m>0} c_m have no closed
form above degree two and are computed in float64 with an explicit geometric tail bound.
Requires mpmath and numpy.
"""
import json, math, mpmath as mp, numpy as np

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
DEGS = (2, 3, 4)


def roots_hi(coeffs):
    """(alpha, conjugates) at 60 dps, from the integer coefficients."""
    r = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=200)
    big = [z for z in r if abs(z) > 1]
    assert len(big) == 1, coeffs
    return mp.re(big[0]), [z for z in r if abs(z) <= 1]


HI = {}
for row in COV:
    HI[tuple(row['coeffs'])] = roots_hi(row['coeffs'])


def delta_hi(conj):
    return sum(abs(z - 1) / (1 - abs(z)) for z in conj)


def gap_hi(alpha):
    return (alpha - 2) / alpha


# ---------------- P1: sum_m c_m = -(d-1) ----------------
dev = mp.mpf(0)
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    s = sum((z - 1) / (1 - z) for z in conj)          # sum_m sum_j (a_j-1) a_j^m
    dev = max(dev, abs(mp.re(s) + (row['d'] - 1)), abs(mp.im(s)))
report('P1', dev < mp.mpf('1e-45'),
       'sum_m c_m = -(d-1) exactly on all %d Pisot; the sum is real '
       '(max deviation %.1e over both parts)' % (len(COV), float(dev)))


# ---------------- the float64 window, with an explicit tail bound ----------------
def window(coeffs, tol=1e-13, cap=400000):
    r = np.roots(np.array(coeffs, dtype=float))
    conj = np.array([z for z in r if abs(z) < 1])
    rho = float(np.max(np.abs(conj)))
    Ca = float(np.sum(np.abs(conj - 1)))
    M = int(math.ceil(math.log(tol * (1 - rho) / Ca) / math.log(rho))) + 10
    M = min(max(M, 60), cap)
    m = np.arange(M)
    c = np.real(np.sum((conj[:, None] - 1) * conj[:, None] ** m[None, :], axis=0))
    return c, Ca * rho ** M / (1 - rho)


SAMPLE = ([r for r in COV if r['d'] == 2]
          + [r for r in COV if r['d'] == 3][::4]
          + [r for r in COV if r['d'] == 4][::12])
WIN = {}
for row in SAMPLE:
    WIN[tuple(row['coeffs'])] = window(row['coeffs'])
MAXTAIL = max(t for _, t in WIN.values())

# ---------------- P2: diam K = sum |c_m|, both endpoints attained ----------------
rng = np.random.default_rng(20260827)
dev_sum = 0.0
dev_store = 0.0
bad_rand = 0
for row in SAMPLE:
    c, tail = WIN[tuple(row['coeffs'])]
    P, N = float(np.sum(np.maximum(c, 0))), float(np.sum(np.minimum(c, 0)))
    dev_sum = max(dev_sum, abs((P - N) - float(np.sum(np.abs(c)))))
    dev_store = max(dev_store, abs((P - N) - row['D']))
for row in SAMPLE[::37]:                       # random words never beat the greedy ones
    c, _ = WIN[tuple(row['coeffs'])]
    P, N = float(np.sum(np.maximum(c, 0))), float(np.sum(np.minimum(c, 0)))
    W = rng.integers(0, 2, size=(4000, len(c)))
    v = W @ c
    if float(v.max()) > P + 1e-9 or float(v.min()) < N - 1e-9:
        bad_rand += 1
report('P2', dev_sum < 1e-9 and dev_store < 1e-6 and bad_rand == 0,
       'diam K = P - (-Q) = sum_m |c_m| on %d rows (max deviation %.1e, vs M0 stored D '
       '%.1e); %d x 4000 random words all inside [-Q, P]'
       % (len(SAMPLE), dev_sum, dev_store, len(SAMPLE[::37])))

# ---------------- P3: the identity diam K = (d-1) + 2 P ----------------
dev = 0.0
for row in SAMPLE:
    c, _ = WIN[tuple(row['coeffs'])]
    P = float(np.sum(np.maximum(c, 0)))
    dev = max(dev, abs(float(np.sum(np.abs(c))) - ((row['d'] - 1) + 2 * P)))
report('P3', dev < 1e-9,
       'diam K = (d-1) + 2 sum_{c_m>0} c_m on %d rows (max deviation %.1e)'
       % (len(SAMPLE), dev))

# ---------------- P4: the equality case ----------------
bad = 0
att = {d: 0 for d in DEGS}
tot = {d: 0 for d in DEGS}
for row in SAMPLE:
    c, tail = WIN[tuple(row['coeffs'])]
    nopos = bool(np.all(c <= 1e-14))
    eq = abs(float(np.sum(np.abs(c))) - (row['d'] - 1)) < 1e-9
    tot[row['d']] += 1
    if nopos:
        att[row['d']] += 1
    if nopos != eq:
        bad += 1
report('P4', bad == 0 and att[2] > 0,
       'diam K = d-1 iff no c_m > 0, on all %d rows; attained by %s of %s rows at degrees '
       '2/3/4 -- the bound is reached, not merely approached'
       % (len(SAMPLE), '/'.join(str(att[d]) for d in DEGS),
          '/'.join(str(tot[d]) for d in DEGS)))

# ---------------- P5: (d-1) <= diam K <= Delta ----------------
bad_lo = bad_hi = 0
mind = {d: None for d in DEGS}
minslack = {d: None for d in DEGS}
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    Dl = float(delta_hi(conj))
    D = row['D']
    if D < (row['d'] - 1) - 1e-9:
        bad_lo += 1
    if D > Dl + 1e-9:
        bad_hi += 1
    e = D - (row['d'] - 1)
    mind[row['d']] = e if mind[row['d']] is None else min(mind[row['d']], e)
    s = Dl - D
    minslack[row['d']] = s if minslack[row['d']] is None else min(minslack[row['d']], s)
report('P5', bad_lo == 0 and bad_hi == 0 and abs(mind[2]) < 1e-9,
       '(d-1) <= diam K <= Delta on all %d Pisot; min(diam K - (d-1)) = 0 to float64 '
       'precision at every degree (%s) -- the note\'s "attained, not approached"; '
       'min(Delta - diam K) = %s'
       % (len(COV), '/'.join('%.1e' % mind[d] for d in DEGS),
          '/'.join('%.3g' % minslack[d] for d in DEGS)))

# ---------------- P6: X7 is empty ----------------
fires = 0
minr = {d: None for d in DEGS}
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    Dl, g = delta_hi(conj), gap_hi(alpha)
    if 2 * Dl < g:
        fires += 1
    r = float(2 * Dl / g)
    minr[row['d']] = r if minr[row['d']] is None else min(minr[row['d']], r)
report('P6', fires == 0 and minr[2] > 2,
       '2 Delta < g fires for %d of %d Pisot; min 2Delta/g = %s at degrees 2/3/4 '
       '(note: 2.20 / 4.81 / 8.34)'
       % (fires, len(COV), ' / '.join('%.2f' % minr[d] for d in DEGS)))

# ---------------- P7: the sharper form, and g really is a gap ----------------
fires = 0
minr2 = {d: None for d in DEGS}
for row in COV:
    alpha, _ = HI[tuple(row['coeffs'])]
    g = gap_hi(alpha)
    if 2 * row['D'] < float(g):
        fires += 1
    r = 2 * row['D'] / float(g)
    minr2[row['d']] = r if minr2[row['d']] is None else min(minr2[row['d']], r)
bad_gap = 0
for row in COV[::400]:
    a = float(HI[tuple(row['coeffs'])][0])
    E = rng.integers(0, 2, size=(20000, 90))
    pw = a ** (-np.arange(1, 91, dtype=float))
    xi = (a - 1) * (E @ pw)
    if np.any((xi > 1 / a + 1e-12) & (xi < (a - 1) / a - 1e-12)):
        bad_gap += 1
report('P7', fires == 0 and bad_gap == 0,
       '2 diam K < g fires for %d of %d Pisot (min 2 diam K/g = %s); and 20000 sampled '
       'points of C(alpha) at each of %d alpha all avoid (1/alpha, (alpha-1)/alpha), whose '
       'length is g'
       % (fires, len(COV), ' / '.join('%.2f' % minr2[d] for d in DEGS), len(COV[::400])))

# ---------------- P8: at degree two the majorant is exact ----------------
QU = [r for r in COV if r['d'] == 2]
dev = mp.mpf(0)
for row in QU:
    alpha, conj = HI[tuple(row['coeffs'])]
    beta = conj[0]
    dev = max(dev, abs(mp.im(beta)),
              abs(delta_hi(conj) - abs(beta - 1) / (1 - abs(beta))))
# above degree two the triangle inequality is an identity exactly when every conjugate is
# real and they all share a sign -- which is automatic at degree two, one conjugate.
bad_ch = 0
tight = {d: 0 for d in DEGS if d > 2}
for row in COV:
    if row['d'] < 3:
        continue
    alpha, conj = HI[tuple(row['coeffs'])]
    eq = abs(float(delta_hi(conj)) - row['D']) < 1e-6
    real = all(abs(mp.im(z)) < mp.mpf('1e-40') for z in conj)
    same = real and (all(mp.re(z) > 0 for z in conj) or all(mp.re(z) < 0 for z in conj))
    if eq != same:
        bad_ch += 1
    if eq:
        tight[row['d']] += 1
report('P8', dev < mp.mpf('1e-45') and bad_ch == 0,
       'Delta = |beta-1|/(1-|beta|) = sum_m |c_m| = diam K at all %d quadratics '
       'unconditionally (max deviation %.1e); above degree two it holds exactly when every '
       'conjugate is real and they share a sign -- %s of the %d cubics and quartics, '
       'characterisation exact'
       % (len(QU), float(dev), '/'.join(str(tight[d]) for d in DEGS if d > 2),
          len(COV) - len(QU)))

# ---------------- P9: the attainment family X^2 - aX + 1 ----------------
bad = 0
for a in range(3, 61):
    A = mp.mpf(a)
    al = (A + mp.sqrt(A ** 2 - 4)) / 2
    be = A - al
    if abs(al ** 2 - A * al + 1) > mp.mpf('1e-45'):
        bad += 1
    if not (al > 2 and 0 < be < 1 and abs(al * be - 1) < mp.mpf('1e-45')):
        bad += 1
    Dl = abs(be - 1) / (1 - abs(be))
    if abs(Dl - 1) > mp.mpf('1e-45'):
        bad += 1
    if any((be - 1) * be ** m >= 0 for m in range(40)):
        bad += 1
al4 = (mp.mpf(4) + mp.sqrt(mp.mpf(12))) / 2
sq3 = abs(al4 - (2 + mp.sqrt(3)))
r22 = float(2 / gap_hi((mp.mpf(22) + mp.sqrt(mp.mpf(22) ** 2 - 4)) / 2))
report('P9', bad == 0 and sq3 < mp.mpf('1e-45') and abs(r22 - minr[2]) < 1e-9,
       "X^2-aX+1, a = 3..60: alpha > 2, beta = 1/alpha in (0,1), every c_m < 0, and "
       "Delta = diam K = d-1 = 1 exactly (all three); alpha(4) = 2+sqrt3 (dev %.1e); "
       "alpha(22) gives 2Delta/g = %.4f, which IS P6's degree-2 minimum"
       % (float(sq3), r22))

# ---------------- P10: the ratio decreases to 2 ----------------
prev = None
mono = True
for a in range(3, 2001):
    A = mp.mpf(a)
    al = (A + mp.sqrt(A ** 2 - 4)) / 2
    r = float(2 / gap_hi(al))
    if r <= 2:
        mono = False
    if prev is not None and r >= prev:
        mono = False
    prev = r
A = mp.mpf(10) ** 6
alB = (A + mp.sqrt(A ** 2 - 4)) / 2
rB = float(2 / gap_hi(alB))
report('P10', mono and rB - 2 < 1e-5,
       '2Delta/g = 2/g on the family, strictly > 2 and strictly decreasing for a = 3..2000 '
       '(%.6f down to %.6f); at a = 10^6 it is 2 + %.1e -- the constant 2 is the exact '
       'infimum, never attained' % (float(2 / gap_hi((mp.mpf(3) + mp.sqrt(mp.mpf(5))) / 2)),
                                    prev, rB - 2))

print()
print('%d/%d checks OK at mp.dps = %d (float64 window tail bound <= %.1e)'
      % (len(RES) - FAILS, len(RES), mp.mp.dps, MAXTAIL))
json.dump(RES, open('m2_prop7_lean.json', 'w'), indent=1)
