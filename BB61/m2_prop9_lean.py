#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Prop. 9 -- one check per GROUP OF DECLARATIONS of BB61/Raster.lean and
BB61/GapSqrtThree.lean.

Proposition 9 has two halves and the checks below follow them.  The completeness half is an
accounting of lengths, so what is verified is the accounting: what a raster does to a set in
each direction, and the constants.  The converse half is M0 sec 6.2's certificate at
alpha = 2+sqrt3, which the Lean file proves at depth (2,2) exact in Z[sqrt3] rather than at
M0's depth (11,9) on 2^21 bins -- so what is verified is that the depth-2 object really is the
same certificate, with the same gap, and that depth 1 is genuinely not enough.

P1  bin / binIdx / occSet             the raster model: bins are the fibres of floor(x*G),
                                      S <= occSet(S), and occSet(S) gains < 1/G
P2  exists_zeroRun                    completeness at a given resolution: the alignment loss
                                      is exactly 2 bins and never more
P3  exists_certified_gap              the composed accounting (b-a-2e)*G - 4, against a
                                      brute-force raster over random covers
P4  gap_pos_of_resolution             the note's arithmetic: 2^3 > 6, and the sharper 4/G
P5  tPart_expand / neg_sPart_expand    the ONE-SIDED depth-2 errors at 2+sqrt3, and why the
                                      engine's two-sided `delta 2 2` cannot be used
P6  lend / covThree                   the nine intervals, exact in Z[sqrt3]
P7  covThree_inter_gapIoo_eq_empty    the 18 comparisons, TWO OF THEM EQUALITIES (zero margin)
P8  gap_two_add_sqrt3                 the gap is M0 sec 6.2's: length 11*sqrt3-19 = 0.052559
                                      at 0.60770, reproduced by M0's own raster method; and
                                      depth 1 gives NO gap
P9  exists_zeroRun_two_add_sqrt3      the run at every G >= 100 (threshold 76.10), and at
                                      M0's G = 2^21
P10 routeA_subset_X8_strict           Route A blind at 2+sqrt3 (A = 1.0526) but the
                                      certificate exists => Route A is a PROPER subset of X8

Everything is computed at 60 decimal digits with mpmath, plus exact sympy arithmetic in
Z[sqrt3] where the Lean proof is exact.  Requires mpmath and sympy.
"""
import json, math, random
from fractions import Fraction
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


# ---------------------------------------------------------------- the raster model
def binIdx(G, x):
    return math.floor(x * G)


def occupied(G, pts):
    return set(binIdx(G, p) for p in pts)


random.seed(9)

# P1: bins are the fibres of floor(x*G); S <= occSet(S); occSet(S) gains less than 1/G
ok1 = True
worst_gain = 0.0
for G in (7, 64, 1000, 1 << 12):
    for _ in range(4000):
        x = random.uniform(-3.0, 3.0)
        i = binIdx(G, x)
        # x lies in bin i = [i/G, (i+1)/G) and in no other
        ok1 &= (i / G <= x < (i + 1) / G)
        ok1 &= binIdx(G, x) == i
    # a point of an occupied bin is within 1/G of the set
    S = [random.uniform(0, 1) for _ in range(200)]
    occ = occupied(G, S)
    for _ in range(2000):
        x = random.uniform(0, 1)
        if binIdx(G, x) in occ:
            d = min(abs(x - y) for y in S if binIdx(G, y) == binIdx(G, x))
            worst_gain = max(worst_gain, d * G)
            ok1 &= d < 1.0 / G
    ok1 &= all(binIdx(G, y) in occ for y in S)          # S <= occSet(S)
report('P1', ok1,
       'bins ARE the fibres of floor(x*G) at G = 7, 64, 1000, 4096 (24000 points); '
       'S <= occSet(S) always, and every point of an occupied bin is within 1/G of S '
       '(worst observed %.4f/G, bound 1/G)' % worst_gain)

# P2: completeness at a given resolution -- the alignment loss is exactly 2 bins
ok2 = True
worst_loss = -1e9
for _ in range(6000):
    G = random.choice([16, 97, 512, 4096])
    a = random.uniform(0, 0.7)
    b = a + random.uniform(1e-4, 0.3)
    # S placed entirely outside (a,b), so (a,b) misses occSet(S) except for raster bleed
    S = [random.uniform(-0.5, 1.5) for _ in range(80)]
    S = [y for y in S if not (a - 1.0 / G <= y <= b + 1.0 / G)]
    occ = occupied(G, S)
    lo, hi = math.floor(a * G) + 1, math.ceil(b * G) - 1
    ell = max(hi - lo, 0)
    if any(j in occ for j in range(lo, lo + ell)):
        continue                                        # not a clean gap; skip
    ok2 &= ell >= (b - a) * G - 2                       # the Lean bound
    worst_loss = max(worst_loss, ell - ((b - a) * G - 2))
    if ell > 0:
        ok2 &= lo / G >= a and (lo + ell) / G <= b      # the run sits inside (a,b)
report('P2', ok2,
       'the run i = floor(a*G)+1, length ceil(b*G)-1-i always satisfies '
       'ell >= (b-a)*G - 2 and lies inside (a,b) over 6000 random (G, a, b); the alignment '
       'loss never exceeds 2 bins (slack from the bound at most %.3f)' % worst_loss)

# P3: the composed accounting (b-a-2e)*G - 4
ok3 = True
worst3 = -1e9
for _ in range(4000):
    G = random.choice([64, 401, 2048])
    e = random.uniform(0, 0.02)
    a = random.uniform(0, 0.5)
    b = a + random.uniform(2 * e + 8.0 / G, 0.4)
    cov = [random.uniform(-0.3, 1.3) for _ in range(60)]
    cov = [y for y in cov if not (a <= y <= b)]         # a genuine gap in Cov
    imp = [y + random.uniform(-e, e) for y in cov]      # Imp over-approximates Cov by e
    occ = occupied(G, imp)
    lo, hi = math.floor((a + e + 1.0 / G) * G) + 1, math.ceil((b - e - 1.0 / G) * G) - 1
    ell = max(hi - lo, 0)
    ok3 &= not any(j in occ for j in range(lo, lo + ell))
    ok3 &= ell >= (b - a - 2 * e) * G - 4
    worst3 = max(worst3, ell - ((b - a - 2 * e) * G - 4))
report('P3', ok3,
       'with Cov <= Imp <= Cov+[-e,e], the run found after shrinking by e+1/G is empty and '
       'has ell >= (b-a-2e)*G - 4 over 4000 random instances (slack at most %.3f); the note '
       'spends 6/G where 4/G suffices' % worst3)

# P4: the note's arithmetic, 2^3 > 6
ok4 = True
mn4, mn6 = 1e9, 1e9
for W in range(0, 40):
    for t in (0, 1, 17, 100, 200, 300, 330, 333):
        T = Fraction(t, 1000)
        if 3 * T >= 1:
            continue
        G = Fraction(2) ** (W + 3) / (1 - 3 * T)
        base = (1 - 3 * T) / Fraction(2) ** W
        ok4 &= base - 6 / G > 0                        # the note's own bound
        ok4 &= base - 6 / G >= base / 4                # ... which is base/4
        ok4 &= base - 4 / G >= base / 2                # the sharper Lean bound
        mn6 = min(mn6, float((base - 6 / G) / (base / 4)))
        mn4 = min(mn4, float((base - 4 / G) / (base / 2)))
report('P4', ok4,
       'at G = 2^(W+3)/(1-3T) the note\'s (1-3T)2^-W - 6/G is positive and at least a QUARTER '
       'of the guaranteed gap (ratio >= %.6f over 40 x 8 (W,T)), and the sharper - 4/G is at '
       'least a HALF (ratio >= %.6f)' % (mn6, mn4))

# ------------------------------------------------- the depth-2 certificate at 2+sqrt3
s3 = sp.sqrt(3)
alE, beE = 2 + s3, 2 - s3
w2E, w1E, epsE = sp.simplify(alE - 1) / alE, sp.simplify(alE - 1) / alE ** 2, beE ** 2
w2E, w1E, epsE = sp.simplify(w2E), sp.simplify(w1E), sp.simplify(epsE)
gapLoE, gapHiE = 11 - 6 * s3, 5 * s3 - 8
al = mp.mpf(2) + mp.sqrt(3)
be = 1 / al
w2, w1, eps = 1 - be, (1 - be) * be, be ** 2
gapLo, gapHi = 11 - 6 * mp.sqrt(3), 5 * mp.sqrt(3) - 8


def tpart(eps_word, n, depth=200):
    """t_n = (alpha-1) sum_{k>=0} eps_{n+k} alpha^{-(k+1)}."""
    return (al - 1) * sum(eps_word[n + k] * al ** (-(k + 1)) for k in range(depth)
                          if n + k < len(eps_word))


def spart(eps_word, n):
    """S_n by the recursion S_{m+1} = beta S_m + (beta-1) eps_m."""
    S = mp.mpf(0)
    for m in range(n):
        S = be * S + (be - 1) * eps_word[m]
    return S


# P5: the one-sided depth-2 errors, and why the engine's `delta 2 2` is unusable
random.seed(21)
maxt, mint, maxs, mins = -mp.inf, mp.inf, -mp.inf, mp.inf
for _ in range(3000):
    L = 260
    word = [random.randint(0, 1) for _ in range(L)]
    n = random.randint(0, 40)
    t = tpart(word, n)
    r = t - (w2 * word[n] + w1 * word[n + 1])
    maxt, mint = max(maxt, r), min(mint, r)
    S = spart(word, n)
    d1 = word[n - 1] if n >= 1 else 0
    d0 = word[n - 2] if n >= 2 else 0
    r2 = -S - (w2 * d1 + w1 * d0)
    maxs, mins = max(maxs, r2), min(mins, r2)
delta22 = al ** (-2) + (1 + abs(be)) * abs(be) ** 2 / (1 - abs(be))
report('P5', mint >= -mp.mpf('1e-50') and maxt <= eps + mp.mpf('1e-50')
       and mins >= -mp.mpf('1e-50') and maxs <= eps + mp.mpf('1e-50')
       and 2 * delta22 > gapHi - gapLo,
       'the depth-2 remainders are ONE-SIDED and lie in [0, beta^2] = [0, %.7f]: future in '
       '[%.2e, %.7f], past in [%.2e, %.7f] over 3000 random (word, n).  The engine\'s '
       'two-sided delta(2,2) = %.6f is %.1fx the half-gap %.6f, so BB61/Covering.lean\'s '
       'bound cannot see this certificate'
       % (float(eps), float(mint), float(maxt), float(mins), float(maxs), float(delta22),
          float(2 * delta22 / (gapHi - gapLo)), float((gapHi - gapLo) / 2)))

# P6: the nine left endpoints, exact in Z[sqrt3]
lendE = {(p, q): sp.expand(sp.simplify(w2E * p + w1E * q)) for p in range(3) for q in range(3)}
wid = sp.expand(sp.simplify(2 * epsE))
expected = {(0, 0): 0, (0, 1): 3 * s3 - 5, (0, 2): 6 * s3 - 10, (1, 0): s3 - 1,
            (1, 1): 4 * s3 - 6, (1, 2): 7 * s3 - 11, (2, 0): 2 * s3 - 2,
            (2, 1): 5 * s3 - 7, (2, 2): 8 * s3 - 12}
ok6 = all(sp.simplify(lendE[k] - expected[k]) == 0 for k in expected)
ok6 &= sp.simplify(wid - (14 - 8 * s3)) == 0
ok6 &= sp.simplify(w2E - (s3 - 1)) == 0 and sp.simplify(w1E - (3 * s3 - 5)) == 0
report('P6', ok6,
       'the nine left endpoints are exactly {0, 3r-5, 6r-10, r-1, 4r-6, 7r-11, 2r-2, 5r-7, '
       '8r-12} with r = sqrt3, the width is exactly 14-8r = %.7f, and the two depth-2 '
       'weights are r-1 and 3r-5 -- all exact in Z[sqrt3], no floating point'
       % float(wid.evalf(40)))

# P7: the 18 comparisons, two of them equalities
margins = {}
ok7 = True
for p in range(3):
    for q in range(3):
        L, R = lendE[(p, q)], sp.expand(lendE[(p, q)] + wid)
        for m in (0, 1):
            lo, hi = sp.expand(L - m), sp.expand(R - m)
            # [lo, hi] must miss the OPEN interval (gapLo, gapHi)
            left = sp.simplify(hi - gapLoE)     # <= 0 means "entirely to the left"
            right = sp.simplify(lo - gapHiE)    # >= 0 means "entirely to the right"
            good = (left <= 0) or (right >= 0)
            ok7 &= bool(good)
            margins[(p, q, m)] = float(min(abs(left.evalf(40)), abs(right.evalf(40))))
zero_margin = [k for k, v in margins.items() if v < 1e-30]
ok7 &= len(zero_margin) == 2
report('P7', ok7,
       'all 18 shifted intervals miss the OPEN gap; exactly 2 do so with margin zero -- '
       '%s, where 2(r-1)+14-8r = 12-6r = 1+gapLo and 2(r-1)+3r-5 = 5r-7 = 1+gapHi are '
       'EQUALITIES.  Smallest nonzero margin %.6f'
       % (sorted(zero_margin), min(v for v in margins.values() if v > 1e-30)))

# P8: the gap is M0's, and depth 1 is not enough
segs = []
for p in range(3):
    for q in range(3):
        L = float((lendE[(p, q)]).evalf(40))
        R = L + float(wid.evalf(40))
        for m in (0, 1):
            lo, hi = max(L - m, 0.0), min(R - m, 1.0)
            if hi > lo:
                segs.append((lo, hi))
segs.sort()
merged = []
for lo, hi in segs:
    if merged and lo <= merged[-1][1] + 1e-12:
        merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
    else:
        merged.append((lo, hi))
gaps = [(merged[j][1], merged[j + 1][0] - merged[j][1]) for j in range(len(merged) - 1)]
# depth 1: alphabet {0, w2}, error beta on each side
segs1 = []
for p in range(3):
    L = p * float(w2)
    R = L + 2 * float(be)
    for m in (0, 1, 2):
        lo, hi = max(L - m, 0.0), min(R - m, 1.0)
        if hi > lo:
            segs1.append((lo, hi))
segs1.sort()
m1 = []
for lo, hi in segs1:
    if m1 and lo <= m1[-1][1] + 1e-12:
        m1[-1] = (m1[-1][0], max(m1[-1][1], hi))
    else:
        m1.append((lo, hi))
gaps1 = [(m1[j][1], m1[j + 1][0] - m1[j][1]) for j in range(len(m1) - 1)]
glen = float((gapHiE - gapLoE).evalf(40))
# and the conclusion itself: real orbit points never land in either gap.
# {xi alpha^n} at n = 250 needs ~145 digits just to exist, so this runs at dps 400 with
# words of length 650; the recursion {xi alpha^(n+1)} = {{xi alpha^n} alpha} is exact.
random.seed(77)
hits = 0
npts = 0
_dps = mp.mp.dps
mp.mp.dps = 400
alH = mp.mpf(2) + mp.sqrt(3)
gl, gh = 11 - 6 * mp.sqrt(3), 5 * mp.sqrt(3) - 8
g0lo = mp.mpf(gaps[0][0])
g0hi = g0lo + mp.mpf(gaps[0][1])
for _ in range(80):
    word = [random.randint(0, 1) for _ in range(650)]
    y = (alH - 1) * sum(word[k] * alH ** (-(k + 1)) for k in range(650))
    for _n in range(250):
        npts += 1
        if (g0lo < y < g0hi) or (gl < y < gh):
            hits += 1
        y = mp.frac(y * alH)
mp.mp.dps = _dps

report('P8', len(gaps) == 2 and abs(gaps[1][1] - glen) < 1e-12
       and abs(gaps[0][1] - glen) < 1e-12 and abs(gaps[1][0] - float(gapLo)) < 1e-12
       and len(gaps1) == 0 and hits == 0,
       'the depth-(2,2) covering leaves EXACTLY two gaps, both of length 11r-19 = %.7f, at '
       '%.5f and %.5f -- M0 sec 6.2 reports 0.052558 at 0.3397 and 0.6077.  At depth 1 the '
       'covering fills the circle (%d gaps), so depth 2 is the FIRST depth that certifies.  '
       '%d orbit points {xi alpha^n} (80 random xi in C(alpha), n < 250, at dps 400): %d '
       'landings in '
       'either gap' % (glen, gaps[0][0], gaps[1][0], len(gaps1), npts, hits))

# P9: the raster run at G >= 100, and at M0's 2^21
r = glen / 2
thr = 4.0 / glen
ok9 = True
runs = {}
for G in (100, 1 << 12, 1 << 21):
    lo = math.floor((float(gapLo) + 1.0 / G) * G) + 1
    hi = math.ceil((float(gapHi) - 1.0 / G) * G) - 1
    ell = max(hi - lo, 0)
    runs[G] = ell
    ok9 &= ell >= 2 * r * G - 4 and ell >= 1
ok9 &= 76.0 < thr < 77.0

report('P9', ok9,
       'the zero run is nonempty from G > 4/(gapHi-gapLo) = %.2f on (the Lean file states G >= 100); at '
       'G = 100 it is %d bin(s), at 2^12 it is %d, and at M0\'s 2^21 it is %d bins = %.6f, '
       'against the true gap %.6f' % (thr, runs[100], runs[1 << 12], runs[1 << 21],
                                      runs[1 << 21] / float(1 << 21), glen))

# P10: Route A is blind at 2+sqrt3, so the containment is strict
A_alpha = mp.log(2) / mp.log(al) + mp.log(2) / mp.log(1 / abs(be))
rows = json.load(open('m0_coverage.json'))
units = [rw for rw in rows if rw['d'] == 2 and abs(rw['coeffs'][2]) == 1]
bad = [rw for rw in units if (rw['A'] < 1) != (rw['a'] > 4)]
row3 = [rw for rw in rows if rw['coeffs'] == [1, -4, 1]]
report('P10', A_alpha > 1 and abs(A_alpha - mp.mpf('1.0526')) < mp.mpf('1e-3')
       and len(bad) == 0 and len(row3) == 1 and abs(row3[0]['A'] - float(A_alpha)) < 1e-9,
       'A(2+sqrt3) = %.6f > 1, so Route A does NOT fire, while the certificate above does: '
       'Route A is a PROPER subset of X8.  On all %d quadratic units of the enumeration the '
       'Route A criterion is exactly alpha > 4 (M2 Cor. 6), %d exceptions'
       % (float(A_alpha), len(units), len(bad)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m2_prop9_lean.json', 'w'), indent=1)
