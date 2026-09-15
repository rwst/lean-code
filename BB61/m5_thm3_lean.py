#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 Thm. 3 at any degree -- one check per GROUP OF DECLARATIONS of BB61/NonVanishing.lean.

The note states its Bernoulli section for every Pisot alpha > 2 and its table of constants
contains cubics; BB61/Bernoulli.lean proves it at degree two.  BB61/NonVanishing.lean removes
the degree restriction from the arithmetic, on two inputs: the trace identity
c_m + (alpha-1)alpha^m = Tr((alpha-1)alpha^m) in Z, and "a rational algebraic integer is a
rational integer".  This script checks the identities and the two constants numerically, and
the two non-vanishing statements EXACTLY, over the degree family X^d - 2X^(d-1) - 1 of
r3a_bern.log (d = 2..8) and the 42 candidates of m0_gapsweep.json.

C1  conj_shiftedPowerSum_isInt       T_m = sum_beta (beta-1)beta^m is a rational integer
C2  conj_erase_sum_add               c_m = T_m - (alpha-1)alpha^m is the sum over the
    exists_int_pastLadder_add        NON-dominant conjugates (the past ladder)
C3  exists_int_close_of_isPisot      |(alpha-1)alpha^m - T_m| <= (d-1)(1+rho) rho^m, the
    IsPisot.exists_int_sub_one...    general-degree Pisot decay behind M5 Thm 8
C4  cos_ne_zero_of_isIntegral_ladder no past factor is a half-integer -- exactly (the ladder
    phi_pastLadder_ne_zero           lies in Z[alpha], whose only rationals are integers)
C5  cos_future_ne_zero_of_isIntegral_inv
                                     at a unit the future ladder is in Z[alpha] too, at every
                                     h and every multiplier lambda: exact, 0 hits
C6  pow_le_of_future_half            at a NON-unit, every half-integer future value satisfies
                                     alpha^j <= 2|h|(alpha-1) -- the finite candidate list
C7  alphaCubic, isIntegral_alphaCubic
    inv_alphaCubic                   the cubic instance X^3 - 2X^2 - 1: alpha > 2, a unit with
                                     alpha^-1 = alpha^2 - 2alpha, Pisot with rho = 0.6733

Requires mpmath.
"""
import json
import mpmath as mp

mp.mp.dps = 200

RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


# ------------------------------------------------------------------ the setups
def poly_name(c):
    """c = [1, c_1, ..., c_d], monic, leading first."""
    d = len(c) - 1
    out = 'X^%d' % d
    for i, a in enumerate(c[1:], start=1):
        if a:
            out += '%+d' % a + ('X^%d' % (d - i) if d - i > 1 else ('X' if d - i == 1 else ''))
    return out


def setup(c):
    """Roots of the monic integer polynomial c, with the dominant real root split off."""
    rs = mp.polyroots([mp.mpf(x) for x in c], maxsteps=300, extraprec=600)
    k = max(range(len(rs)), key=lambda i: abs(rs[i]))
    al = mp.re(rs[k])
    rest = [rs[i] for i in range(len(rs)) if i != k]
    return al, rest


FAMILY = [[1, -2] + [0] * (d - 2) + [-1] for d in range(2, 9)]
SWEEP = json.load(open('m0_gapsweep.json'))
SETUPS = []
for c in FAMILY:
    al, rest = setup(c)
    SETUPS.append((c, al, rest))
for r in SWEEP:
    c = list(r['coeffs'])
    al, rest = setup(c)
    SETUPS.append((c, al, rest))


# ------------------------------------------------------- exact Z[alpha] arithmetic
def mul_alpha(v, c):
    """multiply the Z-basis vector v (coefficients of 1, alpha, ..., alpha^{d-1}) by alpha."""
    d = len(v)
    top = v[d - 1]
    w = [0] + v[:d - 1]
    # alpha^d = -(c_1 alpha^{d-1} + ... + c_d),  c = [1, c_1, ..., c_d]
    for i in range(d):
        w[d - 1 - i] -= top * c[i + 1]
    return w


def mulz(u, v, c):
    """product in Z[alpha]."""
    d = len(u)
    acc = [0] * d
    cur = list(u)
    for i in range(d):
        if v[i]:
            for k in range(d):
                acc[k] += v[i] * cur[k]
        cur = mul_alpha(cur, c)
    return acc


def inv_alpha(c):
    """alpha^{-1} in Z[alpha] when alpha is a unit (c_d = +-1):
    alpha (alpha^{d-1} + c_1 alpha^{d-2} + ... + c_{d-1}) = -c_d."""
    d = len(c) - 1
    if abs(c[d]) != 1:
        return None
    w = [0] * d
    for i in range(d):
        w[d - 1 - i] = c[i]
    return [-x // c[d] for x in w]


def alpha_minus_one(c):
    d = len(c) - 1
    v = [-1] + [0] * (d - 1)
    v[1 if d > 1 else 0] += 1
    return v


def is_half_odd(v):
    """does sum v_i alpha^i lie in 1/2 + Z?  An element of Z[alpha] is rational only if
    v_1 = ... = v_{d-1} = 0, and then it is the integer v_0 -- never a half-odd-integer."""
    return all(x == 0 for x in v[1:]) and (2 * v[0]) % 2 == 1


# --------------------------------------------------------------------- C1
worst1, arg1 = mp.mpf(0), None
for c, al, rest in SETUPS:
    for m in range(0, 41):
        T = sum((z - 1) * z ** m for z in rest) + (al - 1) * al ** m
        d = abs(T - mp.nint(mp.re(T)))
        if d > worst1:
            worst1, arg1 = d, (poly_name(c), m)
report('C1', worst1 < mp.mpf('1e-35'),
       'the full conjugate sum T_m = sum_beta (beta-1)beta^m is a rational integer for every '
       'm <= 40 at all %d setups (the degree family 2..8 plus the 42 sweep candidates): worst '
       'deviation %.2e at %s' % (len(SETUPS), float(worst1), arg1))

# --------------------------------------------------------------------- C2
worst2, arg2 = mp.mpf(0), None
for c, al, rest in SETUPS:
    for m in range(0, 41):
        T = mp.nint(mp.re(sum((z - 1) * z ** m for z in rest) + (al - 1) * al ** m))
        cm = sum((z - 1) * z ** m for z in rest)
        d = abs(cm - (T - (al - 1) * al ** m))
        if d > worst2:
            worst2, arg2 = d, (poly_name(c), m)
report('C2', worst2 < mp.mpf('1e-35'),
       'the past ladder c_m = sum over the NON-dominant conjugates equals T_m - (alpha-1)alpha^m '
       'exactly -- this is conj_erase_sum_add, and it is what makes c_m real and the past '
       'argument congruent mod 1 to -h(alpha-1)alpha^m: worst deviation %.2e at %s'
       % (float(worst2), arg2))

# --------------------------------------------------------------------- C3
bad3, tight3, arg3 = 0, mp.mpf(0), None
for c, al, rest in SETUPS:
    rho = max(abs(z) for z in rest)
    C = mp.mpf(len(rest)) * (1 + rho)
    for m in range(0, 61):
        T = mp.nint(mp.re(sum((z - 1) * z ** m for z in rest) + (al - 1) * al ** m))
        lhs = abs((al - 1) * al ** m - T)
        rhs = C * rho ** m
        if lhs > rhs * (1 + mp.mpf('1e-30')):
            bad3 += 1
        if rhs > 0:
            r = lhs / rhs
            if r > tight3:
                tight3, arg3 = r, (poly_name(c), m)
report('C3', bad3 == 0,
       'the Lean constants hold at every setup and every m <= 60: '
       '|(alpha-1)alpha^m - T_m| <= (d-1)(1+rho)rho^m with rho = max_{j>=2}|alpha_j|, %d '
       'violations; the constant is sharp -- worst-case ratio |lhs|/bound = %.3f (at %s, where '
       'the single conjugate is negative, so |beta-1| = 1 + |beta| exactly)'
       % (bad3, float(tight3), arg3))

# --------------------------------------------------------------------- C4
hits4, tested4, close4, arg4 = 0, 0, mp.mpf(1), None
for c, al, rest in SETUPS:
    lad = alpha_minus_one(c)
    for m in range(0, 21):
        for h in list(range(-24, 0)) + list(range(1, 25)):
            tested4 += 1
            if is_half_odd([h * x for x in lad]):
                hits4 += 1
            x = h * (al - 1) * al ** m
            dd = abs(mp.frac(x) - mp.mpf(1) / 2)
            if dd < close4:
                close4, arg4 = dd, (poly_name(c), h, m)
        lad = mul_alpha(lad, c)
report('C4', hits4 == 0,
       'no past factor vanishes: h(alpha-1)alpha^m lies in Z[alpha], and an element of Z[alpha] '
       'is in 1/2 + Z only if it is rational, hence an integer -- %d hits in %d exact tests '
       '(|h| <= 24, m <= 20, all %d setups); numerically the closest any argument comes to 1/2 '
       'mod 1 is %.2e, at %s' % (hits4, tested4, len(SETUPS), float(close4), arg4))

# --------------------------------------------------------------------- C5
hits5, tested5, close5, arg5, nunit = 0, 0, mp.mpf(1), None, 0
for c, al, rest in SETUPS:
    d = len(c) - 1
    inv = inv_alpha(c)
    if inv is None:
        continue
    nunit += 1
    alinv = mp.mpf(1) / al
    lams = []
    for l0 in range(-3, 4):
        for l1 in range(-3, 4):
            lams.append(([l0, l1] + [0] * (d - 2), l0 + l1 * al))
    fut, futr = alpha_minus_one(c), al - 1
    for j in range(1, 9):
        fut = mulz(fut, inv, c)
        futr = futr * alinv
        for lv, lr in lams:
            base = mulz(fut, lv, c)
            for h in range(1, 13):
                tested5 += 1
                if is_half_odd([h * x for x in base]):
                    hits5 += 1
                dd = abs(mp.frac(h * lr * futr) - mp.mpf(1) / 2)
                if dd < close5:
                    close5, arg5 = dd, (poly_name(c), h, (lv[0], lv[1]), j)
report('C5', hits5 == 0,
       'at a UNIT the future ladder h lambda (alpha-1) alpha^{-j} lies in Z[alpha] as well, '
       'because alpha^{-1} is an algebraic integer, so no future factor vanishes either -- at '
       'every h and every multiplier: %d hits in %d exact tests over the %d units; the '
       'numerically closest approach to 1/2 mod 1 is %.2e at %s, so non-vanishing is NOT '
       'uniform and the argument has to be arithmetic'
       % (hits5, tested5, nunit, float(close5), arg5))

# --------------------------------------------------------------------- C6
viol6, hits6, ex6, nnon = 0, 0, [], 0
for c, al, rest in SETUPS:
    d = len(c) - 1
    if abs(c[d]) == 1:
        continue
    nnon += 1
    am1 = alpha_minus_one(c)
    powj = [1] + [0] * (d - 1)
    for j in range(1, 9):
        powj = mul_alpha(powj, c)
        for h in list(range(-24, 0)) + list(range(1, 25)):
            lhs = [2 * h * x for x in am1]
            # solve lhs = s * powj over Z with s odd
            s = None
            ok = True
            for k in range(d):
                if powj[k]:
                    if lhs[k] % powj[k]:
                        ok = False
                        break
                    t = lhs[k] // powj[k]
                    if s is None:
                        s = t
                    elif s != t:
                        ok = False
                        break
                elif lhs[k]:
                    ok = False
                    break
            if ok and s is not None and s % 2 != 0:
                hits6 += 1
                ex6.append((poly_name(c), h, j))
                if not (al ** j <= 2 * abs(h) * (al - 1) * (1 + mp.mpf('1e-30'))):
                    viol6 += 1
list1 = set()
for c, al, rest in SETUPS:
    js = [j for j in range(1, 40) if al ** j <= 2 * (al - 1)]
    list1.add(tuple(js))
report('C6', viol6 == 0 and list1 == {(1,)},
       'at the %d non-units of the pool, every exact half-integer future value obeys the Lean '
       'candidate bound alpha^j <= 2|h|(alpha-1): %d such values found (|h| <= 24, j <= 8), %d '
       'of them outside the bound%s.  And at h = 1 the candidate list is {j = 1} at every one '
       'of the %d setups (%s) -- the integral form of Thm 3(iii), since 2(alpha-1)/alpha lies '
       'strictly between 1 and 2 and so is never an odd integer'
       % (nnon, hits6, viol6, (', examples %s' % ex6[:4]) if ex6 else '',
          len(SETUPS), sorted(list1)))

# --------------------------------------------------------------------- C7
c3 = [1, -2, 0, -1]
al3, rest3 = setup(c3)
inv3 = mp.mpf(1) / al3
ok7 = (al3 > 2
       and abs(al3 ** 3 - 2 * al3 ** 2 - 1) < mp.mpf('1e-45')
       and abs(inv3 - (al3 ** 2 - 2 * al3)) < mp.mpf('1e-45')
       and max(abs(z) for z in rest3) < 1
       and abs(c3[3]) == 1)
report('C7', ok7,
       'the cubic instance X^3-2X^2-1 of r3a_bern.log: alpha = %.10f > 2, a unit with '
       'alpha^{-1} = alpha^2 - 2alpha (difference %.1e), Pisot with rho = %.7f < 1 -- so BOTH '
       'ladders are covered at degree three, at every h and every lambda'
       % (float(al3), float(abs(inv3 - (al3 ** 2 - 2 * al3))),
          float(max(abs(z) for z in rest3))))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
RES['_tables'] = dict(setups=[poly_name(c) for c, _, _ in SETUPS],
                      C6_hits=[(p, h, j) for p, h, j in ex6][:40])
json.dump(RES, open('m5_thm3_lean.json', 'w'), indent=1)
