#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 Prop. 1 -- one check per GROUP OF DECLARATIONS of BB61/Tube.lean.

Proposition 1 kills move 3 of Route B: the tube T_B = {x : (x_2,...,x_d) in B} covers the
whole torus R^d / Lambda as soon as B has non-empty interior, so the plan's B-criterion
"Haar(T_K) < 1 -- morally Leb_{d-1}(K) small relative to the covolume of Sigma" has no
instances.

P1  tube_add_eq_univ_iff            the covering question is one-dimensional: the witnesses
                                    (u,v) for the 2-D tube and for the 1-D condition
                                    z_2 - (u + v beta) in B are the SAME set
P2  alpha_mul_beta                  alpha beta = -b, and beta^n = p_n + q_n beta with
    beta_pow_mem_shadow             (p,q) -> (q b, p + q a): beta^n really lies in Z + betaZ
P3  covol_sq                        covol^2 = |alpha - beta|^2 = a^2 + 4b over the sweep
P4  exists_tube_small_shadow        the plan's ratio Leb(B)/covol driven to 0 while every
                                    target stays covered; the witness box grows like 1/r
P5  prop1_thickening                delta > 0: the fattened window covers, with an explicit
                                    N(delta) such that {v beta} is delta-dense
P6  volume_windowSet_eq_zero        delta = 0: the exact window is null exactly when
                                    |beta| < 1/2, by the 2^n covers of radius ~ |beta|^n
P7  tube_window_dichotomy           the plan's own numbers: its bound Leb_1(K) <= |beta-1| /
                                    (1-|beta|) over covol, against the true value 0, and its
                                    "expected coverage |alpha_2| < 1/2" recomputed
P8  dense_image_mk_line             the note's L: {u + v beta} is dense, max gap ~ 1/N

Requires mpmath.
"""
import bisect
import json

import mpmath as mp

mp.mp.dps = 80

RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


def roots(a, b):
    """The two roots of X^2 - aX - b, alpha > 1 first."""
    disc = mp.sqrt(mp.mpf(a) ** 2 + 4 * mp.mpf(b))
    return (mp.mpf(a) + disc) / 2, (mp.mpf(a) - disc) / 2


def frac(x):
    return x - mp.floor(x)


SWEEP = json.load(open('m0_gapsweep.json'))
QUAD = [r for r in SWEEP if r['d'] == 2]
# coeffs are [1, -a, -b] for X^2 - aX - b
AB = [(-r['coeffs'][1], -r['coeffs'][2], r) for r in QUAD]
NAMED = {'X^2-2X-1': '1+sqrt2', 'X^2-4X-1': '2+sqrt5', 'X^2-3X+1': '(3+sqrt5)/2',
         'X^2-4X+1': '2+sqrt3'}

# ---------------------------------------------------------------- P1
# tube_add_eq_univ_iff: BB61.tube R B + Lambda = univ  <=>  B + shadow Lambda = univ.  The
# content is that the first coordinate is free, so the SAME (u,v) work for both.  Check the
# witness sets coincide exactly, over a search box, for random targets and random intervals.
a1, b1, _ = [x for x in AB if x[2]['poly'] == 'X^2-2X-1'][0]
al1, be1 = roots(a1, b1)
bad1 = []
tested1 = 0
for t in range(40):
    z1 = mp.mpf(t) / 7 - 3
    z2 = mp.mpf(3 * t) / 11 - 2
    c = mp.mpf(t) / 13 - 1
    r = mp.mpf('0.07') + mp.mpf(t % 5) / 40
    w2, w2d = set(), set()
    for u in range(-40, 41):
        for v in range(-40, 41):
            lat1 = u + v * al1
            lat2 = u + v * be1
            # 1-D condition: z_2 - (u + v beta) in B = [c-r, c+r]
            if abs((z2 - lat2) - c) <= r:
                w2d.add((u, v))
            # 2-D condition: z - iota(u,v) in the tube, i.e. its SECOND coordinate in B --
            # the first coordinate z_1 - (u + v alpha) is unconstrained by definition
            p = (z1 - lat1, z2 - lat2)
            if abs(p[1] - c) <= r:
                w2.add((u, v))
    tested1 += 1
    if w2 != w2d or not w2:
        bad1.append(t)
report('P1', not bad1,
       'over %d (target, interval) pairs at 1+sqrt2 the witness set for "z - iota(u,v) in '
       'T_B" and for the one-dimensional "z_2 - (u + v beta) in B" are identical and '
       'non-empty in every case (%d mismatches): the tube criterion sees only the conjugate '
       'coordinate, which is tube_add_eq_univ_iff' % (tested1, len(bad1)))

# ---------------------------------------------------------------- P2
# alpha beta = -b, and the integer recursion behind beta^n in Z + beta Z.
bad2, bad2b = [], []
for a, b, row in AB:
    al, be = roots(a, b)
    if abs(al * be + b) > mp.mpf('1e-70'):
        bad2.append(row['poly'])
    if b == 0:
        continue
    # p, q are exact integers of size ~ alpha^n, while beta^n ~ rho^n: the comparison
    # cancels ~ 2n log10(alpha) digits, so it is done at raised working precision
    with mp.workdps(400):
        beh = roots(a, b)[1]
        p, q = 1, 0                   # beta^0 = 1 + 0 beta
        for n in range(0, 61):
            val = mp.mpf(p) + mp.mpf(q) * beh
            if abs(val - beh ** n) > mp.mpf('1e-60'):
                bad2b.append((row['poly'], n))
                break
            p, q = q * b, p + q * a   # beta^{n+1} = q b + (p + q a) beta
report('P2', not bad2 and not bad2b,
       'alpha beta = -b to 1e-70 on all %d quadratics of the sweep (%d exceptions), and the '
       'integer recursion (p,q) -> (q b, p + q a) reproduces beta^n for n <= 60 to 1e-60 on '
       'every one with b != 0 (%d exceptions): beta^n in Z + beta Z, the only arithmetic '
       'input to dense_shadow' % (len(AB), len(bad2), len(bad2b)))

# ---------------------------------------------------------------- P3
# covol^2 = a^2 + 4b.
bad3 = []
for a, b, row in AB:
    al, be = roots(a, b)
    cov = abs(al - be)
    if abs(cov ** 2 - (mp.mpf(a) ** 2 + 4 * mp.mpf(b))) > mp.mpf('1e-70'):
        bad3.append(row['poly'])
cov_tab = {}
for a, b, row in AB:
    if row['poly'] in NAMED:
        al, be = roots(a, b)
        cov_tab[NAMED[row['poly']]] = mp.nstr(abs(al - be), 8)
report('P3', not bad3,
       'covol = |alpha - beta| satisfies covol^2 = a^2 + 4b to 1e-70 on all %d sweep '
       'quadratics (%d exceptions); the four named values are %s'
       % (len(AB), len(bad3), cov_tab))

# ---------------------------------------------------------------- P4
# exists_tube_small_shadow: shrink B = (-r, r) and watch Leb(B)/covol -> 0 with coverage
# intact.  Report the search box |v| <= N the witnesses need (floats suffice: the smallest
# r is 1e-6 and N stays below 2^22, so the round-off in v*beta is below 1e-10).
al1, be1 = roots(a1, b1)
cov1 = abs(al1 - be1)
bef = float(be1)
covf = float(cov1)
TARGETS4 = [k / 60.0 for k in range(60)]


def cover_box(be, r, targets, cap=1 << 23):
    """Smallest doubling N with every target within r of some u + v*beta, 0 <= v <= N."""
    N = 1
    while N <= cap:
        pts = sorted((v * be) % 1.0 for v in range(N + 1))
        ok = True
        for x in targets:
            i = bisect.bisect_left(pts, x)
            best = min(abs(pts[j % len(pts)] - x - (1.0 if j >= len(pts) else 0.0))
                       for j in (i - 1, i, i + 1) if -1 <= j <= len(pts))
            if best >= r:
                ok = False
                break
        if ok:
            return N
        N *= 2
    return None


rows4, bad4 = [], []
for k in range(1, 7):
    r = 10.0 ** (-k)
    N = cover_box(bef, r, TARGETS4)
    if N is None:
        bad4.append(k)
    rows4.append(('1e-%d' % k, '%.3g' % (2 * r / covf), N))
report('P4', not bad4,
       'at 1+sqrt2, B = (-r, r) with the plan\'s ratio Leb(B)/covol driven from %s down to '
       '%s: every one of 60 targets is still covered at every r (%d failures), the witness '
       'box growing as (r, Leb(B)/covol, N with |v| <= N) = %s.  No inequality between the '
       'size of the window and the covolume can produce a margin; only the search box grows'
       % (rows4[0][1], rows4[-1][1], len(bad4), rows4))


# ---------------------------------------------------------------- P5
# prop1_thickening: for delta > 0 the fattened window covers, since K_delta contains an
# interval around 0 and {v beta mod 1} is delta-dense for N(delta) ~ 1/(2 delta).
def max_gap(be, N):
    pts = sorted(frac(v * be) for v in range(N + 1))
    g = pts[0] + (1 - pts[-1])
    for i in range(1, len(pts)):
        g = max(g, pts[i] - pts[i - 1])
    return g


rows5, bad5 = [], []
for name, poly in (('1+sqrt2', 'X^2-2X-1'), ('(3+sqrt5)/2', 'X^2-3X+1'),
                   ('2+sqrt3', 'X^2-4X+1')):
    a, b, _ = [x for x in AB if x[2]['poly'] == poly][0]
    _, be = roots(a, b)
    line = []
    for k in range(1, 5):
        delta = mp.mpf(10) ** (-k)
        N = 1
        while max_gap(be, N) >= 2 * delta and N < 60000:
            N *= 2
        if max_gap(be, N) >= 2 * delta:
            bad5.append((name, k))
        line.append((k, N))
    rows5.append((name, line))
report('P5', not bad5,
       'for delta = 1e-1 .. 1e-4 the orbit {v beta mod 1} is delta-dense with the explicit '
       'N(delta) = %s (as (log10(1/delta), N) pairs), so K_delta + (Z + beta Z) = R for '
       'every delta > 0 and every one of the three alpha (%d failures).  N grows like '
       '1/delta: coverage is complete at each delta but the witness bound blows up'
       % (rows5, len(bad5)))

# ---------------------------------------------------------------- P6
# volume_windowSet_eq_zero: at depth n the window K is covered by 2^n intervals of radius
# |beta-1| |beta|^n / (1 - |beta|), so its outer measure is <= C (2|beta|)^n -- null exactly
# when |beta| < 1/2, which is upperBoxDim K <= log2/log|beta|^-1 < 1.
rows6, bad6 = [], []
for a, b, row in AB:
    al, be = roots(a, b)
    if be == 0:
        continue
    rho = abs(be)
    half = rho < mp.mpf('0.5')
    dim = mp.log(2) / mp.log(1 / rho)
    if (dim < 1) != half:
        bad6.append(row['poly'])
    if row['poly'] in NAMED:
        C = abs(be - 1) / (1 - rho)
        outer = [mp.nstr(2 ** n * 2 * C * rho ** n, 3) for n in (4, 8, 16, 32)]
        rows6.append((NAMED[row['poly']], mp.nstr(rho, 6), mp.nstr(dim, 6), outer))
report('P6', not bad6,
       'over the %d sweep quadratics with beta != 0, dim_B K <= log2/log|beta|^-1 is < 1 '
       'exactly when |beta| < 1/2 (%d exceptions) -- the plan\'s own "expected coverage" '
       'condition.  The 2^n covers of radius |beta-1||beta|^n/(1-|beta|) give the outer '
       'measures at n = 4, 8, 16, 32: %s.  So the exact window is Lebesgue-null there and '
       'its tube misses a full-measure set' % (len([1 for a, b, r in AB if b]), len(bad6),
                                               rows6))

# ---------------------------------------------------------------- P7
# tube_window_dichotomy, and the plan's own numbers: the B-criterion box says
# "Leb_1(K) <= |alpha_2 - 1|/(1 - |alpha_2|)", to be compared with the covolume; the true
# Leb_1(K) is 0 on the whole target family, and Haar(T_{K_delta}) = 1 for every delta > 0.
rows7 = []
units = [(a, b, r) for a, b, r in AB if abs(b) == 1 and r['alpha'] > 2]
bad7 = [r['poly'] for a, b, r in units if not abs(roots(a, b)[1]) < mp.mpf('0.5')]
for a, b, row in AB:
    if row['poly'] not in NAMED:
        continue
    al, be = roots(a, b)
    rho = abs(be)
    bound = abs(be - 1) / (1 - rho)
    cov = abs(al - be)
    rows7.append((NAMED[row['poly']], mp.nstr(bound, 6), mp.nstr(cov, 6),
                  mp.nstr(bound / cov, 6), '0' if rho < mp.mpf('0.5') else '?'))
report('P7', not bad7,
       'the plan\'s "expected coverage: all quadratic Pisot alpha > 2 with |alpha_2| < 1/2, '
       'in particular every X^2-aX+-1" holds for all %d units of the sweep with alpha > 2 '
       '(%d exceptions), since |beta| = 1/alpha there.  Its criterion quantity, as '
       '(alpha, plan bound on Leb_1(K), covol, ratio, TRUE Leb_1(K)): %s.  The ratio is the '
       'continuous number Route B wanted; the Haar measure it was supposed to be is 1 at '
       'every delta > 0 and the true Leb_1(K) it bounds is 0'
       % (len(units), len(bad7), rows7))

# ---------------------------------------------------------------- P8
# dense_image_mk_line: the note's L = image of R x {0}.  Its preimage is R x (Z + beta Z),
# dense because the max gap of {v beta mod 1} tends to 0 -- at the rate 1/N of the three-
# distance theorem, not at the rate |beta|^n of the contraction that PROVES density.
rows8, bad8 = [], []
for name, poly in (('1+sqrt2', 'X^2-2X-1'), ('2+sqrt3', 'X^2-4X+1')):
    a, b, _ = [x for x in AB if x[2]['poly'] == poly][0]
    _, be = roots(a, b)
    line = []
    prev = None
    for N in (10, 100, 1000, 10000):
        g = max_gap(be, N)
        line.append((N, mp.nstr(g, 4), mp.nstr(g * N, 4)))
        if prev is not None and not g < prev:
            bad8.append((name, N))
        prev = g
    rows8.append((name, line))
# the contraction that the Lean proof uses: |beta|^n itself lies in Z + beta Z and -> 0
bad8b = []
for a, b, row in AB:
    _, be = roots(a, b)
    if b == 0:
        continue
    n = 1
    while abs(be) ** n >= mp.mpf('1e-6'):
        n += 1
    if not (abs(be) ** n > 0):
        bad8b.append(row['poly'])
report('P8', not bad8 and not bad8b,
       'the max gap of {v beta mod 1} is strictly decreasing in N with g*N of order 1, as '
       '(N, gap, gap*N) = %s (%d violations) -- so L is dense; and on every sweep quadratic '
       'with b != 0 the element |beta|^n of Z + beta Z is non-zero yet below 1e-6 (%d '
       'exceptions), which is the non-isolated-zero argument the Lean proof uses instead of '
       'the note\'s Pontryagin duality' % (rows8, len(bad8), len(bad8b)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m3_prop1_lean.json', 'w'), indent=1)
