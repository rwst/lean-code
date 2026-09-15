#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 Thms 7-8 + Cor. 10 -- one check per GROUP OF DECLARATIONS of BB61/{Folding,TailEvent}.lean.

Theorem 7 says that at a quadratic unit of norm +1 the past ladder IS the future ladder shifted
by one, and draws three conclusions the corpus did not have: K = -C(alpha) (so the factor map is
a plain SUM and X(alpha) = (C+C) mod 1), G_p(h) is a perfect square at EVERY p, and at norm -1
the past ladder carries (alpha+1) instead of (alpha-1).  Theorem 8 says U(alpha) is a tail event
and Corollary 10 that a counterexample to 10.61 could not be isolated.

C1  wVal_eq_neg_piVal              the window value is MINUS the Cantor value (norm +1)
    windowSet_eq_neg
C2  fRaw_eq_add, confSet_eq_add    the factor map is pi(omega+) + pi(omega-)
C3  pastProdC_eq_futProdC          G_p(h) = (future product)^2 at every p and every h
    weylC_eq_sq
C4  cCoef_eq_of_norm_neg_one       at norm -1 the ladder is (-1)^{m+1}(alpha+1)/alpha^{m+1}, and
                                   the two products are then NOT equal -- M1 F9's hypothesis
                                   ("a quadratic unit") was too weak
C5  abs_orbit_sub_int_le           flipping digit k moves xi alpha^n by something within
                                   |beta-1||beta|^{n-k-1} of an integer
C6  abs_piVal_graft_sub_le         grafting at depth k moves the point by at most alpha^{-k}
C7  mem_udWords_iff_of_agree_from  the two Weyl sums of two eventually-equal words merge

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


SWEEP = json.load(open('m0_gapsweep.json'))
QUAD = [r for r in SWEEP if r['d'] == 2]
# X^2 - aX - b  with coeffs [1, -a, -b];  N(alpha) = alpha*beta = -b
SETUPS = []
for r in QUAD:
    a, b = -r['coeffs'][1], -r['coeffs'][2]
    disc = mp.sqrt(mp.mpf(a) ** 2 + 4 * mp.mpf(b))
    al = (mp.mpf(a) + disc) / 2
    be = (mp.mpf(a) - disc) / 2
    SETUPS.append((r['poly'], a, b, al, be))
PLUS = [s for s in SETUPS if s[2] == -1]      # N(alpha) = +1
MINUS = [s for s in SETUPS if s[2] == 1]      # N(alpha) = -1

K = 220
random.seed(1061)


def word(n=K + 40):
    return [random.randint(0, 1) for _ in range(n)]


def piVal(al, eps):
    return (al - 1) * mp.fsum(eps[k] * al ** (-(k + 1)) for k in range(K))


def cCoef(be, m):
    return (be - 1) * be ** m


def wVal(be, delta):
    return mp.fsum(cCoef(be, m) * delta[m] for m in range(K))


def phi(p, x):
    return (1 - p) + p * mp.e ** (2j * mp.pi * x)


def futProdC(al, p, h, J=400):
    out = mp.mpc(1)
    for j in range(J):
        out *= phi(p, h * (al - 1) / al ** (j + 1))
    return out


def pastProdC(be, p, h, M=400):
    out = mp.mpc(1)
    for m in range(M):
        out *= phi(p, -(h * cCoef(be, m)))
    return out


# --------------------------------------------------------------------- C1
worst1, arg1 = mp.mpf(0), None
for name, a, b, al, be in PLUS:
    for _ in range(4):
        d = word()
        dev = abs(wVal(be, d) + piVal(al, d))
        if dev > worst1:
            worst1, arg1 = dev, name
report('C1', worst1 < mp.mpf('1e-40'),
       'at the %d quadratic units of norm +1, the window value of a digit word is exactly minus '
       'its Cantor value, w(delta) = -pi(delta) -- so K = -C(alpha): worst deviation %.1e (at %s) '
       'over 4 random words each' % (len(PLUS), float(worst1), arg1))

# --------------------------------------------------------------------- C2
worst2, arg2 = mp.mpf(0), None
lo2, hi2 = mp.mpf(10), mp.mpf(-10)
for name, a, b, al, be in PLUS:
    for _ in range(4):
        u, v = word(), word()
        fraw = piVal(al, u) - wVal(be, v)
        dev = abs(fraw - (piVal(al, u) + piVal(al, v)))
        lo2, hi2 = min(lo2, fraw), max(hi2, fraw)
        if dev > worst2:
            worst2, arg2 = dev, name
report('C2', worst2 < mp.mpf('1e-40') and lo2 >= 0 and hi2 <= 2,
       'the factor map is then a plain sum, F(omega) = pi(omega+) + pi(omega-): worst deviation '
       '%.1e (at %s); the sampled range sits in [%.4f, %.4f] subset [0,2] = C+C, as confSet_eq_add '
       'requires' % (float(worst2), arg2, float(lo2), float(hi2)))

# --------------------------------------------------------------------- C3
worst3, arg3 = mp.mpf(0), None
rows3 = []
for name, a, b, al, be in PLUS[:4]:
    for p in [mp.mpf('0.5'), mp.mpf('0.3'), mp.mpf('0.72')]:
        for h in [1, 2, 5]:
            f = futProdC(al, p, h)
            g = pastProdC(be, p, h)
            dev = abs(f - g)
            if dev > worst3:
                worst3, arg3 = dev, (name, float(p), h)
            rows3.append((name, float(p), h, float(abs(f * g)), float(abs(f ** 2))))
report('C3', worst3 < mp.mpf('1e-30'),
       'the past product equals the future product FACTOR BY FACTOR at every p and every h, so '
       'G_p(h) = (prod_j phi_p(h(alpha-1)alpha^{-j}))^2: worst |past - future| = %.1e over 36 '
       '(alpha, p, h) triples (at %s)' % (float(worst3), arg3))

# --------------------------------------------------------------------- C4
worst4, arg4 = mp.mpf(0), None
sep4, argsep = mp.mpf(0), None
for name, a, b, al, be in MINUS:
    for m in range(12):
        dev = abs(cCoef(be, m) - (-1) ** (m + 1) * (al + 1) / al ** (m + 1))
        if dev > worst4:
            worst4, arg4 = dev, (name, m)
    f = futProdC(al, mp.mpf('0.5'), 1)
    g = pastProdC(be, mp.mpf('0.5'), 1)
    if abs(f - g) > sep4:
        sep4, argsep = abs(f - g), name
report('C4', worst4 < mp.mpf('1e-40') and sep4 > mp.mpf('1e-3'),
       'at the %d units of norm -1 the past ladder is (-1)^{m+1}(alpha+1)/alpha^{m+1} instead '
       '(worst deviation %.1e at %s), and there the two products genuinely DIFFER -- '
       'max |past - future| = %.4f at %s, which is why "a quadratic unit" was too weak a '
       'hypothesis for M1 F9' % (len(MINUS), float(worst4), arg4, float(sep4), argsep))

# --------------------------------------------------------------------- C5
worst5, arg5 = mp.mpf(0), None


def traceZ(a, b, m):
    """T_m = 2u_m + a v_m for (alpha-1)alpha^m = u_m + v_m alpha."""
    u, v = -1, 1
    for _ in range(m):
        u, v = b * v, u + a * v
    return 2 * u + a * v


for name, a, b, al, be in SETUPS[:12]:
    for k in [0, 1, 3, 7]:
        eps = word()
        eps2 = list(eps)
        eps2[k] = 1 - eps2[k]
        c = eps[k] - eps2[k]
        for n in range(k + 1, k + 26):
            m = n - (k + 1)
            diff = (piVal(al, eps) - piVal(al, eps2)) * al ** n
            T = c * traceZ(a, b, m)
            lhs = abs(diff - T)
            rhs = abs(be - 1) * abs(be) ** m
            if rhs > 0:
                ratio = lhs / rhs
                if ratio > worst5:
                    worst5, arg5 = ratio, (name, k, n)
report('C5', worst5 <= 1 + mp.mpf('1e-20'),
       'flipping the k-th digit moves xi alpha^n to within |beta-1||beta|^{n-k-1} of the integer '
       '+-T_{n-k-1}: worst ratio lhs/bound = %.6f over 12 setups x 4 flip positions x 25 times '
       '(at %s) -- the bound is an EQUALITY, which is abs_sub_trace' % (float(worst5), arg5))

# --------------------------------------------------------------------- C6
worst6, arg6 = mp.mpf(0), None
for name, a, b, al, be in SETUPS[:12]:
    for k in [1, 4, 9, 16]:
        d, e0 = word(), word()
        graft = d[:k] + e0[k:]
        lhs = abs(piVal(al, graft) - piVal(al, d))
        rhs = al ** (-k)
        if rhs > 0:
            ratio = lhs / rhs
            if ratio > worst6:
                worst6, arg6 = ratio, (name, k)
report('C6', worst6 <= 1 + mp.mpf('1e-20'),
       'grafting a word onto a prefix of depth k moves the point by at most alpha^{-k}: worst '
       'ratio %.4f over 48 (alpha, k) pairs (at %s) -- this is the density modulus of Cor. 10'
       % (float(worst6), arg6))

# --------------------------------------------------------------------- C7
# The whole of Theorem 8 is that the DIFFERENCE of the two orbits returns to Z geometrically.
# That difference depends only on the finitely many flipped digits, so it is exact; the orbits
# themselves are not, since alpha^N overflows any fixed precision.
mp.mp.dps = 400
name, a, b, al, be = [t for t in PLUS if t[0] == 'X^2-4X+1'][0]
disc = mp.sqrt(mp.mpf(a) ** 2 + 4 * mp.mpf(b))
al, be = (mp.mpf(a) + disc) / 2, (mp.mpf(a) - disc) / 2
FLIP = 6
delta = [1, -1, 1, 1, -1, 1]                      # the flipped digits, +-1
dsep = (al - 1) * mp.fsum(delta[k] * al ** (-(k + 1)) for k in range(FLIP))
cn = []
for n in range(0, 90):
    y = dsep * al ** n
    cn.append(abs(y - mp.nint(y)))
bound_ok = all(cn[n] <= mp.fsum(abs(be - 1) * abs(be) ** (n - k - 1)
                                for k in range(FLIP) if n >= k + 1) + mp.mpf('1e-40')
               for n in range(FLIP, 90))
S = mp.fsum(cn)
rows7 = [(NN, float(2 * mp.pi * S / NN)) for NN in [200, 800, 3200, 12800]]
# a direct check at small N, where the orbits themselves are still computable
KK = 300
eps = [random.randint(0, 1) for _ in range(KK + 60)]
eps2 = list(eps)
for k in range(FLIP):
    eps2[k] = 1 - eps2[k]
x1 = (al - 1) * mp.fsum(eps[k] * al ** (-(k + 1)) for k in range(KK + 60))
x2 = (al - 1) * mp.fsum(eps2[k] * al ** (-(k + 1)) for k in range(KK + 60))
direct = []
for NN in [50, 100, 200]:
    s1 = mp.fsum([mp.e ** (2j * mp.pi * (x1 * al ** n)) for n in range(NN)]) / NN
    s2 = mp.fsum([mp.e ** (2j * mp.pi * (x2 * al ** n)) for n in range(NN)]) / NN
    direct.append((NN, float(abs(s1 - s2)), float(2 * mp.pi * S / NN)))
mp.mp.dps = 60
report('C7', bound_ok and cn[60] < mp.mpf('1e-25') and all(d <= bd for _, d, bd in direct),
       'two words differing in their first %d digits at alpha = 2+sqrt3: the orbit difference '
       'returns to Z at the proved rate (||d alpha^n|| = %.1e at n = 60), so it is summable '
       '(sum = %.4f) and the two Weyl sums differ by at most 2 pi sum / N = %s at '
       'N = 200, 800, 3200, 12800 -- one word is u.d. iff the other is.  Directly computed at '
       'N = 50, 100, 200 (400 digits): %s, each under its bound'
       % (FLIP, float(cn[60]), float(S), ', '.join('%.2e' % v for _, v in rows7),
          ', '.join('%.2e' % d for _, d, _ in direct)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
RES['_tables'] = dict(C3=rows3[:12], C7=rows7, C7_direct=direct)
json.dump(RES, open('m5_thm78_lean.json', 'w'), indent=1)
