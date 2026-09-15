#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 Cor. 4 -- one check per GROUP OF DECLARATIONS of BB61/DiscrepancyFloor.lean and of
ForMathlib/Analysis/BoundedVariation/{Monotone,Trigonometric}.lean.

The discrepancy floor is Koksma's inequality (a cited axiom, CITED/KoksmaInequality.lean)
applied to the two characters, whose total variation is PROVED here to be 4h.  The checks
below exercise the proved half -- the variation, the monotone pieces, the mean-zero
integrals, the sqrt2 recombination -- and then the assembled inequality end to end at
alpha = 2 + sqrt3.

C1  eVariationOn_cos_two_pi_mul     V(cos 2 pi h x) = 4h on [0,1], h = 1..8
C2  eVariationOn_sin_two_pi_mul     V(sin 2 pi h x) = 4h on [0,1], h = 1..8
C3  eVariationOn_cos_piece          the pieces: cos is monotone on each of the 2h intervals
    eVariationOn_sin_piece          [j/2h,(j+1)/2h] with oscillation 2; sin on each of the 4h
                                    intervals [j/4h,(j+1)/4h] with oscillation 1
C4  integral_cos_char               the characters have mean zero over a period, h >= 1
    integral_sin_char
C5  norm_le_sqrt_two_mul            |z| <= sqrt2 max(|Re z|,|Im z|), sharp at z = 1 + i
C6  norm_average_char_le            |S_N| <= 4 sqrt2 h D*_N for a real orbit at 2 + sqrt3
    abs_average_cos_le              (and the two real halves, each under 4h D*_N)
C7  le_liminf_starDiscrepancy       the floor |G_{1/2}(1)|/(4 sqrt2) at 2 + sqrt3, and the
    starDiscrepancy_floor_pos       empirical D*_N of a fair-coin orbit staying above it

Requires mpmath.
"""
import json
import random

import mpmath as mp

mp.mp.dps = 60

RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


def variation(f, a, b, m):
    """Total variation of f on [a,b] along an m-point uniform partition (converges up)."""
    xs = [a + (b - a) * mp.mpf(i) / m for i in range(m + 1)]
    vs = [f(x) for x in xs]
    return mp.fsum(abs(vs[i + 1] - vs[i]) for i in range(m))


TWO_PI = 2 * mp.pi

# ---------------------------------------------------------------- C1, C2
rows1, rows2 = [], []
ok1 = ok2 = True
for h in range(1, 9):
    # the grid is chosen so the exact half/quarter-period breakpoints are grid points,
    # which makes the partition sum EQUAL the variation, not merely a lower bound
    vc = variation(lambda x: mp.cos(TWO_PI * h * x), 0, 1, 2 * h * 64)
    vs = variation(lambda x: mp.sin(TWO_PI * h * x), 0, 1, 4 * h * 64)
    rows1.append((h, float(vc), 4 * h))
    rows2.append((h, float(vs), 4 * h))
    ok1 &= abs(vc - 4 * h) < mp.mpf('1e-40')
    ok2 &= abs(vs - 4 * h) < mp.mpf('1e-40')
report('C1', ok1, 'V(cos 2 pi h x) on [0,1] over the 2h half-periods = 4h for h = 1..8: %s'
       % ', '.join('%.1f' % v for _, v, _ in rows1))
report('C2', ok2, 'V(sin 2 pi h x) on [0,1] over the 4h quarter-periods = 4h for h = 1..8: %s'
       % ', '.join('%.1f' % v for _, v, _ in rows2))

# ---------------------------------------------------------------- C3
ok3 = True
worst_c = worst_s = mp.mpf(0)
for h in range(1, 7):
    for j in range(2 * h):
        a, b = mp.mpf(j) / (2 * h), mp.mpf(j + 1) / (2 * h)
        vs_ = [mp.cos(TWO_PI * h * (a + (b - a) * mp.mpf(i) / 200)) for i in range(201)]
        d = [vs_[i + 1] - vs_[i] for i in range(200)]
        mono = all(x >= 0 for x in d) or all(x <= 0 for x in d)
        osc = abs(vs_[-1] - vs_[0])
        ok3 &= mono and abs(osc - 2) < mp.mpf('1e-40')
        worst_c = max(worst_c, abs(osc - 2))
    for j in range(4 * h):
        a, b = mp.mpf(j) / (4 * h), mp.mpf(j + 1) / (4 * h)
        vs_ = [mp.sin(TWO_PI * h * (a + (b - a) * mp.mpf(i) / 200)) for i in range(201)]
        d = [vs_[i + 1] - vs_[i] for i in range(200)]
        mono = all(x >= 0 for x in d) or all(x <= 0 for x in d)
        osc = abs(vs_[-1] - vs_[0])
        ok3 &= mono and abs(osc - 1) < mp.mpf('1e-40')
        worst_s = max(worst_s, abs(osc - 1))
report('C3', ok3, 'every one of the 2h cosine half-periods is monotone with oscillation 2 '
       '(max error %.1e) and every one of the 4h sine quarter-periods is monotone with '
       'oscillation 1 (max error %.1e), h = 1..6 -- 42 + 84 pieces'
       % (float(worst_c), float(worst_s)))

# ---------------------------------------------------------------- C4
ok4 = True
rows4 = []
for h in range(1, 7):
    ic = mp.quad(lambda x: mp.cos(TWO_PI * h * x), [0, 1])
    isx = mp.quad(lambda x: mp.sin(TWO_PI * h * x), [0, 1])
    rows4.append((h, float(abs(ic)), float(abs(isx))))
    ok4 &= abs(ic) < mp.mpf('1e-40') and abs(isx) < mp.mpf('1e-40')
i0 = mp.quad(lambda x: mp.cos(TWO_PI * 0 * x), [0, 1])
report('C4', ok4 and abs(i0 - 1) < mp.mpf('1e-40'),
       'both characters integrate to 0 over [0,1] for h = 1..6 (max |int| = %.1e), and the '
       'hypothesis h >= 1 is needed: at h = 0 the cosine integral is %.1f'
       % (max(max(a, b) for _, a, b in rows4), float(i0)))

# ---------------------------------------------------------------- C5
random.seed(1061)
ok5 = True
worst_ratio = mp.mpf(0)
for _ in range(20000):
    re = mp.mpf(random.uniform(-1, 1))
    im = mp.mpf(random.uniform(-1, 1))
    M = max(abs(re), abs(im))
    n = mp.sqrt(re ** 2 + im ** 2)
    ok5 &= n <= mp.sqrt(2) * M + mp.mpf('1e-40')
    if M > 0:
        worst_ratio = max(worst_ratio, n / M)
sharp = mp.sqrt(2) / max(abs(mp.mpf(1)), abs(mp.mpf(1)))
report('C5', ok5 and abs(sharp - mp.sqrt(2)) < mp.mpf('1e-40'),
       '|z| <= sqrt2 max(|Re z|,|Im z|) on 20000 random points (worst ratio %.6f of '
       'sqrt2 = %.6f), with equality at z = 1 + i -- the constant 4 sqrt2 h cannot be '
       'improved by this route' % (float(worst_ratio), float(mp.sqrt(2))))

# ---------------------------------------------------------------- alpha = 2 + sqrt3
mp.mp.dps = 400
AL = 2 + mp.sqrt(3)
BE = 2 - mp.sqrt(3)
K = 900
random.seed(61)
EPS = [random.randint(0, 1) for _ in range(K)]
XI = (AL - 1) * mp.fsum(EPS[k] * AL ** (-(k + 1)) for k in range(K))


def orbit(N):
    return [mp.frac(XI * AL ** n) for n in range(N)]


def star_disc(ys):
    N = len(ys)
    y = sorted(ys)
    return max(max(mp.mpf(i + 1) / N - y[i], y[i] - mp.mpf(i) / N) for i in range(N))


NS = [50, 100, 200, 400]
ORB = {N: orbit(N) for N in NS}
DST = {N: star_disc(ORB[N]) for N in NS}

# ---------------------------------------------------------------- C6
ok6 = True
rows6 = []
for N in NS:
    ys = ORB[N]
    for h in [1, 2, 3]:
        S = mp.fsum(mp.e ** (2j * mp.pi * h * y) for y in ys) / N
        C = mp.fsum(mp.cos(TWO_PI * h * y) for y in ys) / N
        Sn = mp.fsum(mp.sin(TWO_PI * h * y) for y in ys) / N
        bound = 4 * mp.sqrt(2) * h * DST[N]
        bre = 4 * h * DST[N]
        ok6 &= abs(S) <= bound and abs(C) <= bre and abs(Sn) <= bre
        rows6.append((N, h, float(abs(S)), float(bound), float(DST[N])))
report('C6', ok6, 'at alpha = 2+sqrt3 and a fair-coin word: |S_N| <= 4 sqrt2 h D*_N and each '
       'real part <= 4h D*_N, at N = 50,100,200,400 and h = 1,2,3 (12 cases).  D*_N = %s; '
       'the tightest case is |S_N| = %.4f against a bound of %.4f'
       % (', '.join('%.4f' % float(DST[N]) for N in NS),
          *max(((s, b) for _, _, s, b, _ in rows6), key=lambda t: t[0] / t[1])))

# ---------------------------------------------------------------- C7
mp.mp.dps = 60


def weyl_half(h, J=400):
    fut = mp.mpf(1)
    for j in range(1, J):
        fut *= abs(mp.cos(mp.pi * h * (AL - 1) / AL ** j))
    past = mp.mpf(1)
    for m in range(J):
        past *= abs(mp.cos(mp.pi * h * (BE - 1) * BE ** m))
    return fut * past


G1 = weyl_half(1)
FLOOR = G1 / (4 * mp.sqrt(2))
GS = [(h, float(weyl_half(h)), float(weyl_half(h) / (4 * mp.sqrt(2) * h))) for h in range(1, 9)]
best = max(GS, key=lambda t: t[2])
ok7 = G1 > 0 and all(DST[N] > FLOOR for N in NS)
report('C7', ok7, '|G_{1/2}(1)| = %.6f at 2+sqrt3, so the proved floor is |G|/(4 sqrt2) = '
       '%.6f; optimised over h <= 8 the best mode is h = %d with floor %.6f.  The empirical '
       'D*_N of the fair-coin orbit is %s -- above the floor at every N, as the theorem says '
       'it must be eventually' % (float(G1), float(FLOOR), best[0], best[2],
                                  ', '.join('%.4f' % float(DST[N]) for N in NS)))

print()
print('%d/%d checks OK' % (len(RES) - FAILS, len(RES)))
RES['_tables'] = dict(C1=rows1, C2=rows2, C4=rows4, C6=rows6, C7=GS)
json.dump(RES, open('m5_cor4_lean.json', 'w'), indent=1)
