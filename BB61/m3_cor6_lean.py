#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 Cor. 6 -- one check per GROUP OF DECLARATIONS of BB61/LadderScope.lean.

Corollary 6 is the scope restriction on the trace-ladder reduction: tau-bar_* lambda = Leb
constrains lambda-hat(gamma) exactly on gamma in alpha^Z * (Z \\ {0}), so the ladders a proof
by contradiction may use are h * Tr_m with h in Z and nothing else.  It is aimed at M1's
finding F8, which prescribed "maximise over gamma in d^-1 / alpha^Z" after measuring the
half-ladder at 1+sqrt2 to be worth a factor 452.

C1  two_dvd_trForm_iff              Tr(Z[alpha]) subset 2Z <=> 2 | a, over the sweep, by
    half_trForm_eq                  brute force over the order against the trace form
C2  halfLad, two_mul_halfLad        2 H_k = T_k, and M1's F8 ladders reproduced exactly
C3  traceSeqZ, traceSeqZ_cast       the two-sided ladder T_n = alpha^n + beta^n, n in Z,
                                    including T_{-m} = (-b)^m T_m at a unit
C4  two_dvd_traceSeqZ               the parity obstruction: every n * T_{k+j} is even,
    not_intOrbitLadder_halfLad      the half-ladder is odd at 0, exhaustive search finds no
                                    (n, j) realising it
C5  silver_not_intOrbitLadder       M1's F8 plateau table recomputed -- the 452 at 1+sqrt2
    twoAddSqrt3_not_intOrbitLadder  and the 3.6 the other way at 2+sqrt3
C6  tendsto_futureCoeff_orbit       one constraint per alpha-orbit: the ladder limit does not
                                    depend on the entry point j
C7  no_half_character               e(x/2) does not descend to R/Z, e(hx) does
C8  (the stated caveat)             parity is an obstruction, not a classification: lad 2 4
                                    at 1+sqrt2 is even throughout and still not in the orbit

Requires mpmath.
"""
import json

import mpmath as mp

mp.mp.dps = 120

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
    al = (mp.mpf(a) + disc) / 2
    be = (mp.mpf(a) - disc) / 2
    return al, be


def lad(a, b, h0, h1, n):
    """BB61.QuadSetup.lad, as integers."""
    out = [h0, h1]
    while len(out) <= n:
        out.append(a * out[-1] + b * out[-2])
    return out[: n + 1]


def traceSeq(a, b, n):
    return lad(a, b, 2, a, n)


def halfLad(a, b, c, n):
    return lad(a, b, 1, c, n)


def traceSeqZ(a, b, n, depth=80):
    """BB61.QuadSetup.traceSeqZ: T_n for n in Z, T_{-m} = (-b)^m T_m."""
    if n >= 0:
        return traceSeq(a, b, n)[n]
    m = -n
    return (-b) ** m * traceSeq(a, b, m)[m]


SWEEP = json.load(open('m0_gapsweep.json'))
QUAD = [r for r in SWEEP if r['d'] == 2]
# coeffs are [1, -a, -b] for X^2 - aX - b
AB = [(-r['coeffs'][1], -r['coeffs'][2], r) for r in QUAD]

# ---------------------------------------------------------------- C1
# Tr(u + v alpha) = 2u + av; Tr(Z[alpha]) subset 2Z iff 2 | a.  Brute force over a box of the
# order, then compare with the criterion, then check the concrete half_trForm_eq identity.
bad1 = []
half_ok = []
for a, b, row in AB:
    brute = all((2 * u + a * v) % 2 == 0 for u in range(-6, 7) for v in range(-6, 7))
    crit = (a % 2 == 0)
    if brute != crit:
        bad1.append(row['poly'])
    if crit:
        half_ok.append(row['poly'])
# half_trForm_eq: (Tr(u+v alpha))/2 = u + cv exactly, at 100 digits
bad1b = []
for a, b, row in AB:
    if a % 2:
        continue
    c = a // 2
    al, be = roots(a, b)
    for u in range(-4, 5):
        for v in range(-4, 5):
            lhs = ((u + v * al) + (u + v * be)) / 2
            if abs(lhs - (u + c * v)) > mp.mpf('1e-100'):
                bad1b.append((row['poly'], u, v))
report('C1', not bad1 and not bad1b,
       'over the %d quadratic candidates of the sweep, Tr(Z[alpha]) subset 2Z agrees with '
       '2 | a with %d exceptions, and Tr(u+v alpha)/2 = u + cv to 1e-100 with %d exceptions; '
       'the half frequency gamma = 1/2 is legal at %d of them, including X^2-2X-1 (1+sqrt2) '
       'and X^2-4X+1 (2+sqrt3), and illegal at e.g. X^2-3X+1 ((3+sqrt5)/2, a = 3 odd)'
       % (len(AB), len(bad1), len(bad1b), len(half_ok)))

# ---------------------------------------------------------------- C2
# 2 H_k = T_k, over every 2|a candidate; and M1's F8 table reproduced verbatim.
bad2 = []
for a, b, row in AB:
    if a % 2:
        continue
    c = a // 2
    T = traceSeq(a, b, 30)
    H = halfLad(a, b, c, 30)
    if any(2 * H[k] != T[k] for k in range(31)):
        bad2.append(row['poly'])
f8 = {
    'X^2-2X-1': dict(T=[2, 2, 6, 14, 34, 82, 198, 478], H=[1, 1, 3, 7, 17, 41, 99, 239]),
    'X^2-4X+1': dict(T=[2, 4, 14, 52, 194, 724, 2702], H=[1, 2, 7, 26, 97, 362, 1351]),
}
bad2b = []
for poly, want in f8.items():
    a, b, _ = [x for x in AB if x[2]['poly'] == poly][0]
    c = a // 2
    if traceSeq(a, b, len(want['T']) - 1) != want['T']:
        bad2b.append((poly, 'T'))
    if halfLad(a, b, c, len(want['H']) - 1) != want['H']:
        bad2b.append((poly, 'H'))
report('C2', not bad2 and not bad2b,
       '2 H_k = T_k for k <= 30 on all %d even-trace candidates (%d exceptions), and M1 F8 '
       'table reproduced exactly (%d exceptions): 1+sqrt2 has T = 2,2,6,14,34,82,198,478 and '
       'H = 1,1,3,7,17,41,99,239; 2+sqrt3 has T = 2,4,14,52,194,724,2702 and '
       'H = 1,2,7,26,97,362,1351'
       % (len([1 for a, b, r in AB if a % 2 == 0]), len(bad2), len(bad2b)))

# ---------------------------------------------------------------- C3
# The two-sided ladder: T_n = alpha^n + beta^n for n in Z, at a quadratic unit.
UNITS = [(a, b, r) for a, b, r in AB if abs(b) == 1]
worst3 = mp.mpf(0)
bad3 = []
for a, b, row in UNITS:
    al, be = roots(a, b)
    for n in range(-25, 26):
        lhs = mp.mpf(traceSeqZ(a, b, n))
        rhs = al ** n + be ** n
        d = abs(lhs - rhs)
        worst3 = max(worst3, d)
        if d > mp.mpf('1e-80'):
            bad3.append((row['poly'], n))
report('C3', len(UNITS) > 0 and not bad3,
       'on the %d quadratic units of the sweep, T_n = alpha^n + beta^n for every n in '
       '[-25, 25] -- the backwards half being T_{-m} = (-b)^m T_m -- worst deviation %.2e, '
       '%d exceptions' % (len(UNITS), float(worst3), len(bad3)))

# ---------------------------------------------------------------- C4
# The parity obstruction, and an exhaustive search for a realisation of the half-ladder.
bad4 = []
found = []
for a, b, row in AB:
    if a % 2 or abs(b) != 1:
        continue
    c = a // 2
    H = halfLad(a, b, c, 12)
    # every n * T_{k+j} is even
    for n in range(-40, 41):
        for j in range(-12, 13):
            if (n * traceSeqZ(a, b, j)) % 2 != 0:
                bad4.append((row['poly'], n, j))
    # exhaustive: is H = n * T_{.+j} for some n, j?
    for n in range(-400, 401):
        if n == 0:
            continue
        for j in range(-20, 21):
            if all(H[k] == n * traceSeqZ(a, b, k + j) for k in range(6)):
                found.append((row['poly'], n, j))
report('C4', not bad4 and not found,
       'over the %d even-trace units: every n * T_{k+j} is even (%d exceptions over '
       '|n| <= 40, |j| <= 12), the half-ladder is odd at k = 0, and an exhaustive search over '
       '0 < |n| <= 400, |j| <= 20 finds no (n, j) with H_k = n T_{k+j} (%d hits) -- the '
       'half-frequency 1/2 is outside alpha^Z (Z \\ {0})'
       % (len([1 for a, b, r in AB if a % 2 == 0 and abs(r['coeffs'][2]) == 1]),
          len(bad4), len(found)))


# ---------------------------------------------------------------- C5
# M1's F8 plateau table: |Phi_h| for the Bernoulli(1/2) measure is the two-sided Erdos
# product, |Phi_h| = prod_{j>=1} |cos(pi h (alpha-1) alpha^-j)| * prod_{m>=0} |cos(pi h
# (beta-1) beta^m)|.
def phiAbs(a, b, h, jmax=400, mmax=400):
    al, be = roots(a, b)
    h = mp.mpf(h)
    out = mp.mpf(1)
    for j in range(1, jmax + 1):
        out *= abs(mp.cos(mp.pi * h * (al - 1) * al ** (-j)))
        if out == 0:
            return out
    for m in range(0, mmax + 1):
        out *= abs(mp.cos(mp.pi * h * (be - 1) * be ** m))
    return out


def plateau(a, b, h0, h1, k=26):
    return phiAbs(a, b, lad(a, b, h0, h1, k)[k])


want5 = {
    'X^2-2X-1': (mp.mpf('7.6370923e-5'), mp.mpf('3.4511464e-2')),
    'X^2-4X+1': (mp.mpf('8.2320916e-2'), mp.mpf('2.2641698e-2')),
}
got5 = {}
bad5 = []
for poly, (wT, wH) in want5.items():
    a, b, _ = [x for x in AB if x[2]['poly'] == poly][0]
    c = a // 2
    pT = plateau(a, b, 2, a)
    pH = plateau(a, b, 1, c)
    got5[poly] = (pT, pH)
    if abs(pT - wT) / wT > mp.mpf('2e-6') or abs(pH - wH) / wH > mp.mpf('2e-6'):
        bad5.append(poly)
rat_silver = got5['X^2-2X-1'][1] / got5['X^2-2X-1'][0]
rat_sqrt3 = got5['X^2-4X+1'][0] / got5['X^2-4X+1'][1]
report('C5', not bad5 and abs(rat_silver - 452) < 1 and abs(rat_sqrt3 - 3.6) < 0.1,
       "M1's F8 plateaux recomputed at rung 26: at 1+sqrt2 the trace ladder gives %.7e and "
       'the half-ladder %.7e, a factor %.1f (note: 452); at 2+sqrt3 the order reverses, '
       '%.7e against %.7e, a factor %.2f (note: 3.6).  This is the quantity Cor. 6 declares '
       'unusable at 1+sqrt2'
       % (float(got5['X^2-2X-1'][0]), float(got5['X^2-2X-1'][1]), float(rat_silver),
          float(got5['X^2-4X+1'][0]), float(got5['X^2-4X+1'][1]), float(rat_sqrt3)))


# ---------------------------------------------------------------- C6
# tendsto_futureCoeff_orbit: the future-marginal coefficient along n T_{k+j} converges to the
# same limit for every entry point j.
def nuAbs(a, b, N, jmax=400):
    al, be = roots(a, b)
    N = mp.mpf(N)
    out = mp.mpf(1)
    for j in range(1, jmax + 1):
        out *= abs(mp.cos(mp.pi * N * (al - 1) * al ** (-j)))
    return out


spread6 = mp.mpf(0)
rows6 = []
for poly in ('X^2-2X-1', 'X^2-4X+1'):
    a, b, _ = [x for x in AB if x[2]['poly'] == poly][0]
    for n in (1, 2, 3):
        vals = [nuAbs(a, b, n * traceSeqZ(a, b, 24 + j)) for j in (-4, -2, 0, 2, 4)]
        full = phiAbs(a, b, n * traceSeqZ(a, b, 24))
        s = max(vals) - min(vals)
        spread6 = max(spread6, s)
        rows6.append((poly, n, float(s), float(full)))
report('C6', spread6 < mp.mpf('1e-8'),
       'entering the alpha-orbit at j in {-4,-2,0,2,4} gives the same future-marginal limit: '
       'worst spread %.2e over 2 alphas and n in {1,2,3} -- an orbit carries one constraint, '
       'not infinitely many (at 1+sqrt2, n=1 the common value is %.7e)'
       % (float(spread6), rows6[0][3]))

# ---------------------------------------------------------------- C7
# e(x/2) does not descend to R/Z; e(hx) does.
bad7 = []
for t in range(1, 40):
    x = mp.mpf(t) / 7
    if abs(mp.e ** (mp.pi * 1j * (x + 1)) + mp.e ** (mp.pi * 1j * x)) > mp.mpf('1e-100'):
        bad7.append(('half', t))
    for h in (1, 2, -3):
        d = abs(mp.e ** (2 * mp.pi * 1j * h * (x + 1)) - mp.e ** (2 * mp.pi * 1j * h * x))
        if d > mp.mpf('1e-100'):
            bad7.append(('int', t, h))
report('C7', not bad7,
       'e(x/2) = exp(i pi x) changes sign under x -> x+1 at all %d sample points (so it is '
       'not a function on R/Z), while e(hx) is unchanged for h in {1,2,-3}: %d exceptions.  '
       'This is why tau-bar_* lambda = Leb constrains the integer frequencies and nothing else'
       % (39, len(bad7)))

# ---------------------------------------------------------------- C8
# The stated caveat: parity is an obstruction, not a classification.
a, b, _ = [x for x in AB if x[2]['poly'] == 'X^2-2X-1'][0]
L = lad(a, b, 2, 4, 12)
all_even8 = all(v % 2 == 0 for v in L)
hits8 = [(n, j) for n in range(-400, 401) if n
         for j in range(-20, 21)
         if all(L[k] == n * traceSeqZ(a, b, k + j) for k in range(6))]
report('C8', all_even8 and not hits8,
       'at 1+sqrt2 the ladder lad 2 4 = %s is even throughout (%s) yet an exhaustive search '
       'over 0 < |n| <= 400, |j| <= 20 finds no (n, j) realising it (%d hits): its frequency '
       'is (1+alpha)/2, not in alpha^Z Z.  Evenness certifies inadmissibility, it does not '
       'decide membership -- the limitation the Lean module doc states'
       % (L[:6], all_even8, len(hits8)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m3_cor6_lean.json', 'w'), indent=1)
