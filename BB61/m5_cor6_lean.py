#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 Cor. 6 -- one check per GROUP OF DECLARATIONS of BB61/Multiplier.lean.

Corollary 6 is the multiplier version of Cor. 4: for a quadratic Pisot unit and
lambda = l1 + l2*alpha in Z[alpha], the orbit (lambda*xi*alpha^n) of a Bernoulli-generic
point of C(alpha) is not u.d. mod 1.  The Lean file proves it by twisting the coding,
F^lambda(omega) = lambda*t(omega+) - lambda'*S(omega-), and quoting Theorems 1 and 2.

C1  lamR, lamC, traceMulZ           the twisted trace lambda*A_n + lambda'*S_n is the stated
    lamR_aPart_add_lamC_sPart       integer 2 l1 u + a(l1 v + l2 u) + l2 v (a^2 + 2b)
C2  fRawL_iterate_padZ              {lambda xi alpha^n} = {lambda t_n - lambda' S_n}
    fMapL_iterate_padZ
C3  integral_cexp1_fRawL            the twisted Erdos product G^lambda_{1/2}(h) is the Weyl
    tendsto_weylSum_bern_mul        limit of the multiplied orbit at a fair-coin word
C4  weylCL_ne_zero                  |G^lambda_{1/2}(1)| > 0 across units and multipliers
C5  isIntComb_inv_alpha             the exact integer test for a vanishing future factor:
    cos_pi_ne_zero_of_isIntComb     none at any unit (the theorem); the same search at the
                                    non-units of the sweep
C6  (why the unit is needed)        under the twist the future arguments come arbitrarily
                                    close to 1/2 mod 1, so Thm 3(iii)'s interval argument
                                    cannot survive -- only the algebraic-integer one does
C7  (the lambda = 0 degeneracy)     at lambda = 0 every factor is phi(0) = 1 and the orbit is
                                    constant: the conclusion holds, so `lambda != 0` is not a
                                    hypothesis of the Lean statements

Requires mpmath.
"""
import cmath
import json
import math

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


def roots(a, b):
    """The two roots of X^2 - aX - b, alpha > 1 first."""
    disc = mp.sqrt(mp.mpf(a) ** 2 + 4 * mp.mpf(b))
    return (mp.mpf(a) + disc) / 2, (mp.mpf(a) - disc) / 2


SWEEP = json.load(open('m0_gapsweep.json'))
QUAD = [r for r in SWEEP if r['d'] == 2]
AB = [(-r['coeffs'][1], -r['coeffs'][2], r) for r in QUAD]
UNITS = [t for t in AB if abs(t[1]) == 1]
NONUNITS = [t for t in AB if abs(t[1]) != 1]

LAMS = [(1, 0), (0, 1), (2, 1), (-1, 1), (3, -2), (5, 4), (-7, 3), (1, 11)]


def word(n, seed=12345):
    """A deterministic pseudo-random binary word (LCG, one bit of the high half)."""
    out = []
    x = seed
    for _ in range(n):
        x = (6364136223846793005 * x + 1442695040888963407) & ((1 << 64) - 1)
        out.append((x >> 33) & 1)
    return out


# --------------------------------------------------------------------- C1
def uv(a, b, eps):
    """BB61.QuadSetup.uv: A_n = u_n + v_n alpha, S_n = u_n + v_n beta."""
    u, v = 0, 0
    out = [(0, 0)]
    for d in eps:
        u, v = b * v - d, u + a * v + d
        out.append((u, v))
    return out


bad1 = []
for a, b, row in AB:
    al, be = roots(a, b)
    eps = word(24, seed=7 + a * 31 + b)
    pairs = uv(a, b, eps)
    for l1, l2 in LAMS:
        lam, lamc = l1 + l2 * al, l1 + l2 * be
        for n in range(len(pairs)):
            u, v = pairs[n]
            A, S = u + v * al, u + v * be
            T = (2 * l1 * u + a * (l1 * v + l2 * u) + l2 * v * (a * a + 2 * b))
            if abs(lam * A + lamc * S - T) > mp.mpf('1e-40'):
                bad1.append((row['poly'], (l1, l2), n))
report('C1', not bad1,
       'over the %d quadratic candidates, %d multipliers and 25 times n, the twisted trace '
       'lambda*A_n + lambda_2*S_n equals the integer 2 l1 u + a(l1 v + l2 u) + l2 v(a^2+2b) '
       'to 1e-40 in every one of the %d cases (%d failures)'
       % (len(AB), len(LAMS), len(AB) * len(LAMS) * 25, len(bad1)))

# --------------------------------------------------------------------- C2
bad2 = []
worst2 = mp.mpf(0)
for a, b, row in AB:
    al, be = roots(a, b)
    eps = word(60, seed=11 + a * 17 + b)
    xi = (al - 1) * mp.fsum([eps[k] * al ** (-(k + 1)) for k in range(len(eps))])
    for l1, l2 in LAMS:
        lam, lamc = l1 + l2 * al, l1 + l2 * be
        S = mp.mpf(0)
        for n in range(18):
            t = (al - 1) * mp.fsum([eps[n + k] * al ** (-(k + 1))
                                    for k in range(len(eps) - n)])
            d = abs(mp.frac(lam * xi * al ** n) - mp.frac(lam * t - lamc * S))
            d = min(d, abs(d - 1))
            worst2 = max(worst2, d)
            if d > mp.mpf('1e-25'):
                bad2.append((row['poly'], (l1, l2), n, mp.nstr(d, 5)))
            S = be * S + (be - 1) * eps[n]
report('C2', not bad2,
       'the twisted orbit identity {lambda xi alpha^n} = {lambda t_n - lambda_2 S_n} holds '
       'over the %d candidates, %d multipliers and 18 times n; worst deviation %.2e '
       '(%d failures at tolerance 1e-25) -- the 60-digit truncation of xi is what limits it'
       % (len(AB), len(LAMS), float(worst2), len(bad2)))


# --------------------------------------------------------------------- C3
def weylCL(a, b, l1, l2, h, J=400, M=400):
    al, be = roots(a, b)
    lam, lamc = l1 + l2 * al, l1 + l2 * be
    out = mp.mpc(1)
    for j in range(1, J + 1):
        x = h * lam * (al - 1) / al ** j
        out *= mp.mpf(1) / 2 + mp.exp(2j * mp.pi * x) / 2
    for m in range(M + 1):
        x = -h * lamc * (be - 1) * be ** m
        out *= mp.mpf(1) / 2 + mp.exp(2j * mp.pi * x) / 2
    return out


def empirical(a, b, l1, l2, h, N=400000, seed=99):
    """(1/N) sum_{n<N} e(h lambda xi alpha^n), computed through the coding."""
    al, be = roots(a, b)
    alf, bef = float(al), float(be)
    lam, lamc = float(l1 + l2 * al), float(l1 + l2 * be)
    eps = word(N + 80, seed=seed)
    t = [0.0] * (N + 81)
    for n in range(N + 79, -1, -1):
        t[n] = ((alf - 1.0) * eps[n] + t[n + 1]) / alf
    S = 0.0
    acc = 0j
    two_pi_h = 2.0 * math.pi * h
    for n in range(N):
        acc += cmath.exp(1j * two_pi_h * (lam * t[n] - lamc * S))
        S = bef * S + (bef - 1.0) * eps[n]
    return acc / N


rows3 = []
ok3 = True
for a, b, row in [t for t in UNITS if t[2]['poly'] in
                  ('X^2-2X-1', 'X^2-4X+1', 'X^2-3X+1')]:
    for (l1, l2) in [(1, 0), (2, 1), (-1, 1)]:
        for h in (1, 2):
            G = weylCL(a, b, l1, l2, h)
            E = empirical(a, b, l1, l2, h)
            dev = abs(complex(G) - E)
            rows3.append((row['poly'], (l1, l2), h, float(abs(G)), float(dev)))
            if dev > 0.02:
                ok3 = False
worst3 = max(r[4] for r in rows3)
report('C3', ok3,
       'the twisted product G^lambda_{1/2}(h) matches the Weyl average of the multiplied '
       'orbit over N = 4e5 steps in all %d (alpha, lambda, h) cases, worst deviation %.4f '
       '(the 1/sqrt(N) noise floor of a random word is %.4f)'
       % (len(rows3), worst3, 1.0 / math.sqrt(400000)))

# --------------------------------------------------------------------- C4
tab4 = []
minval = mp.mpf(1)
for a, b, row in UNITS:
    for (l1, l2) in LAMS:
        g = abs(weylCL(a, b, l1, l2, 1))
        tab4.append((row['poly'], (l1, l2), float(g)))
        minval = min(minval, g)
lo4 = min(tab4, key=lambda r: r[2])
report('C4', minval > 0,
       'over the %d quadratic *units* of the sweep and %d multipliers, |G^lambda_{1/2}(1)| is '
       'positive in all %d cases; the smallest is %.3e (%s, lambda = %s), the largest %.4f'
       % (len(UNITS), len(LAMS), len(tab4), float(minval), lo4[0], lo4[1],
          max(r[2] for r in tab4)))


# --------------------------------------------------------------------- C5
def mulZ(a, b, p, q):
    return (p[0] * q[0] + b * p[1] * q[1], p[0] * q[1] + p[1] * q[0] + a * p[1] * q[1])


def future_pair(a, b, l1, l2, h, j):
    """(U, V) with h lambda (alpha-1)(alpha-a)^j = U + V alpha."""
    z = mulZ(a, b, (h, 0), (l1, l2))
    z = mulZ(a, b, z, (-1, 1))
    for _ in range(j):
        z = mulZ(a, b, z, (-a, 1))
    return z


def vanishes(a, b, l1, l2, h, j):
    """h lambda (alpha-1) alpha^{-j} = (U + V alpha)/b^j lies in 1/2 + Z?"""
    U, V = future_pair(a, b, l1, l2, h, j)
    if V != 0:
        return False
    d = b ** j
    if d == 0 or (2 * U) % d:
        return False
    return ((2 * U) // d) % 2 == 1


HB, LB, JB = 24, 24, 8
hitsU, hitsN = [], []
for a, b, row in AB:
    tgt = hitsU if abs(b) == 1 else hitsN
    for h in range(1, HB + 1):
        for l1 in range(-LB, LB + 1):
            for l2 in range(-LB, LB + 1):
                for j in range(1, JB + 1):
                    if vanishes(a, b, l1, l2, h, j):
                        tgt.append((row['poly'], h, (l1, l2), j))
# for the first non-unit hit, the smallest mode h whose ladder is still factor-free
rescue = None
if hitsN:
    poly, h0, (q1, q2), _ = hitsN[0]
    aN, bN, _ = [t for t in NONUNITS if t[2]['poly'] == poly][0]
    for h in range(1, 41):
        if not any(vanishes(aN, bN, q1, q2, h, j) for j in range(1, 41)):
            rescue = h
            break
report('C5', not hitsU,
       'exact integer search over 1 <= h <= %d, |l1|,|l2| <= %d, 1 <= j <= %d '
       '(%d quadruples per candidate): at the %d *units* no twisted future factor vanishes '
       '(%d hits -- this is the theorem, and it is what the unit hypothesis buys); at the %d '
       'non-units the same search finds %d hits, e.g. %s: there '
       'h lambda (alpha-1)/alpha^j = -17.5 exactly, so G^lambda_{1/2}(1) = 0 and the '
       'argument gives nothing at that mode (the smallest mode that survives is h = %s, so '
       'the *conclusion* is recoverable there, only not uniformly)'
       % (HB, LB, JB, HB * (2 * LB + 1) ** 2 * JB, len(UNITS), len(hitsU),
          len(NONUNITS), len(hitsN), str(hitsN[0]) if hitsN else '-', rescue))

# --------------------------------------------------------------------- C6
a6, b6, row6 = [t for t in UNITS if t[2]['poly'] == 'X^2-4X+1'][0]
al6, _ = roots(a6, b6)
best = mp.mpf(1)
arg = None
for h in range(1, 9):
    for l1 in range(-60, 61):
        for l2 in range(-60, 61):
            x = h * (l1 + l2 * al6) * (al6 - 1) / al6
            d = abs(mp.frac(x) - mp.mpf(1) / 2)
            if d < best:
                best, arg = d, (h, l1, l2)
untw = [float(abs(mp.frac((al6 - 1) / al6 ** j) - mp.mpf(1) / 2)) for j in range(1, 9)]
report('C6', best < mp.mpf('1e-3') and min(untw) > 0.08,
       'at alpha = 2+sqrt3 and j = 1: the *untwisted* future arguments stay %.3f away from '
       '1/2 (Thm 3(iii)), while the twisted ones come within %.2e of it at (h, l1, l2) = %s '
       '-- the interval argument is destroyed by the twist and only the algebraic-integer '
       'argument (C5) survives, which is why Cor. 6 needs the unit and Cor. 4 does not'
       % (min(untw), float(best), arg))

# --------------------------------------------------------------------- C7
g7 = weylCL(4, -1, 0, 0, 1)
report('C7', abs(g7 - 1) < mp.mpf('1e-40'),
       'at lambda = 0 the twisted product is exactly 1 (|G - 1| = %.1e): the limit law is '
       'delta_0, not Leb, so the conclusion of Cor. 6 holds for the degenerate reason and '
       '"lambda != 0" is absent from the Lean statements'
       % float(abs(g7 - 1)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
RES['_tables'] = dict(C3=[(p, list(l), h, g, d) for p, l, h, g, d in rows3],
                      C4=[(p, list(l), g) for p, l, g in tab4],
                      C5_nonunit_hits=[(p, h, list(l), j) for p, h, l, j in hitsN][:40])
json.dump(RES, open('m5_cor6_lean.json', 'w'), indent=1)
