#!/usr/bin/env python3
"""M1 Corollary 5: the lower bound on rho, and the ceiling alpha > 2^d.

The note's clause, formalised in `BB61/RouteACeiling.lean`:

    for d >= 2,   rho >= alpha^{-1/(d-1)}   and therefore   A(alpha) >= d log2 / log alpha,

so Route A -- which needs A(alpha) < 1 -- can fire only when alpha > 2^d.  The proof is
one line, 1 <= |N(alpha)| = alpha * prod_{j>=2}|alpha_j| <= alpha * rho^{d-1}, the first
inequality because N(alpha) = +- p(0) is a nonzero rational integer.

This script checks the statement, the sharpness, and the two consequences over the monic
integer polynomials of degree 2 and 3 whose roots are a real alpha > 1 with every other
root inside the open unit disc (the Pisot condition; irreducibility is NOT assumed, and
is not needed -- the constant term is a nonzero integer either way).

Writes m1_cor5.json.
"""
import json
import math
import numpy as np
from mpmath import mp, mpf, log as mplog, polyroots

mp.dps = 30
L2 = math.log(2.0)


def refine(rec):
    """Recompute alpha, rho and A(alpha) at 30 digits.  np.roots is good to about 1e-8
    on a cubic, which is not enough to see that min A(alpha) log2 alpha is *exactly* d."""
    r = polyroots([mpf(c) for c in rec['coeffs']], maxsteps=200, extraprec=200)
    idx = max(range(len(r)), key=lambda i: abs(r[i]))
    alpha = r[idx].real if hasattr(r[idx], 'real') else r[idx]
    rest = [z for i, z in enumerate(r) if i != idx]
    rho = max(abs(z) for z in rest)
    if rho >= 1 - mpf('1e-25'):
        # a conjugate of modulus exactly one (e.g. a rational root +-1): np.roots can
        # report it as 0.9999999999999998.  Not a Pisot number; drop it.
        return None
    rec['alpha'] = float(alpha)
    rec['rho'] = float(rho)
    rec['alpha_mp'] = alpha
    rec['rho_mp'] = rho
    rec['A'] = float(mplog(2) / mplog(alpha) + mplog(2) / mplog(1 / rho))
    rec['Alog2'] = float(1 + mplog(alpha) / mplog(1 / rho))
    prod = alpha
    for z in rest:
        prod = prod * abs(z)
    rec['normprod'] = float(prod)
    return rec


def analyse(coeffs):
    """coeffs = [1, c_{d-1}, ..., c_0] (monic, descending).  Returns None unless the
    polynomial has a single real root alpha > 1 and all other roots of modulus < 1."""
    c0 = int(coeffs[-1])
    if c0 == 0:
        return None
    r = np.roots(np.array(coeffs, dtype=float))
    big = [z for z in r if abs(z) > 1.0]
    if len(big) != 1:
        return None
    a = big[0]
    if abs(a.imag) > 1e-9 or a.real <= 1.0:
        return None
    alpha = float(a.real)
    # remove exactly one occurrence of the distinguished root
    idx = int(np.argmax(np.abs(r)))
    rest = [z for i, z in enumerate(r) if i != idx]
    rho = max(abs(z) for z in rest)
    if rho >= 1.0:
        return None
    d = len(coeffs) - 1
    A = L2 / math.log(alpha) + L2 / math.log(1.0 / rho)
    return dict(d=d, coeffs=[int(x) for x in coeffs], c0=c0, alpha=alpha, rho=rho,
                A=A, Alog2=A * math.log(alpha) / L2,
                normprod=alpha * float(np.prod([abs(z) for z in rest])),
                unit=(abs(c0) == 1))


def enumerate_quadratics(amax=40):
    out = []
    for a in range(-amax, amax + 1):
        for b in range(-amax, amax + 1):
            if a * a + 4 * b <= 0:
                continue
            rec = analyse([1.0, -a, -b])
            if rec is not None:
                rec['a'], rec['b'] = a, b
                out.append(rec)
    return out


def enumerate_cubics(cmax=12):
    out = []
    for c2 in range(-cmax, cmax + 1):
        for c1 in range(-cmax, cmax + 1):
            for c0 in range(-cmax, cmax + 1):
                rec = analyse([1.0, -c2, -c1, -c0])
                if rec is not None:
                    out.append(rec)
    return out


quads = [x for x in (refine(r) for r in enumerate_quadratics()) if x is not None]
cubs = [x for x in (refine(r) for r in enumerate_cubics()) if x is not None]
print('enumerated: %d quadratic, %d cubic (roots refined to %d digits)'
      % (len(quads), len(cubs), mp.dps))

TOL = 1e-20

verdict = {}

# ---- 1. the norm bound 1 <= alpha rho^{d-1}, and its exact form 1 <= |N| = |c_0| ----
worst = float(min(r['alpha_mp'] * r['rho_mp'] ** (r['d'] - 1) for r in quads + cubs))
worstN = max(abs(r['normprod'] - abs(r['c0'])) for r in quads + cubs)
verdict['norm_bound'] = dict(
    kind='1 <= alpha rho^(d-1)  (one_le_mul_pow_of_monic_int)',
    ok=bool(worst >= 1.0 - TOL and worstN < 1e-18),
    min_alpha_rho_pow=worst, max_prod_minus_c0=worstN)

# ---- 2. rho >= alpha^{-1/(d-1)}, the note's shape ----
slack = float(min(r['rho_mp'] - r['alpha_mp'] ** (mpf(-1) / (r['d'] - 1))
                  for r in quads + cubs))
verdict['rho_lower_bound'] = dict(
    kind='rho >= alpha^{-1/(d-1)}  (rpow_neg_inv_le_of_one_le_mul_pow)',
    ok=bool(slack >= -TOL), min_slack=slack)

# ---- 3. A(alpha) log2 alpha >= d, sharp, with equality exactly at the units ----
q_min = min(r['Alog2'] for r in quads)
c_min = min(r['Alog2'] for r in cubs)
q_eq_units = all((abs(r['Alog2'] - 2.0) < 1e-15) == r['unit'] for r in quads)
# a cubic attains d exactly when it is a unit with two conjugates of equal modulus
c_eq = [r for r in cubs if abs(r['Alog2'] - 3.0) < 1e-15]
verdict['ceiling_sharp'] = dict(
    kind='A(alpha) log2 alpha >= d, min = d exactly  (routeA_ge_of_one_le_mul_pow)',
    ok=bool(abs(q_min - 2.0) < 1e-15 and abs(c_min - 3.0) < 1e-15
            and q_min >= 2.0 - TOL and c_min >= 3.0 - TOL and q_eq_units
            and all(r['unit'] for r in c_eq)),
    quad_min=q_min, cubic_min=c_min, quad_equality_iff_unit=bool(q_eq_units),
    cubic_equality_cases=len(c_eq))

# ---- 4. the ceiling: A < 1 forces alpha > 2^d ----
fireq = [r for r in quads if r['A'] < 1.0]
firec = [r for r in cubs if r['A'] < 1.0]
verdict['ceiling'] = dict(
    kind='A(alpha) < 1  =>  alpha > 2^d  (two_pow_natDegree_lt_of_routeA_lt_one)',
    ok=bool(all(r['alpha'] > 4.0 for r in fireq) and all(r['alpha'] > 8.0 for r in firec)),
    quad_firing=len(fireq), cubic_firing=len(firec),
    quad_min_alpha=(min(r['alpha'] for r in fireq) if fireq else None),
    cubic_min_alpha=(min(r['alpha'] for r in firec) if firec else None))

# ---- 5. the hard slice 2 < alpha <= 4 is untouched ----
slice_hits = [r for r in quads + cubs if 2.0 < r['alpha'] <= 4.0 and r['A'] < 1.0]
verdict['hard_slice'] = dict(
    kind='no alpha in (2,4] has A < 1  (one_le_routeAExponent_of_alpha_le_four)',
    ok=bool(len(slice_hits) == 0), hits=len(slice_hits),
    in_slice=len([r for r in quads + cubs if 2.0 < r['alpha'] <= 4.0]))

# ---- 6. Route A never fires at alpha <= 2 (the d = 1 reading) ----
low = [r for r in quads + cubs if r['alpha'] <= 2.0 and r['A'] < 1.0]
verdict['never_below_two'] = dict(
    kind='A(alpha) < 1  =>  alpha > 2  (two_lt_alpha_of_routeAExponent_lt_one)',
    ok=bool(len(low) == 0), hits=len(low))

# ---- 7. degree two: alpha |beta| = |b| exactly, so rho = 1/alpha iff |b| = 1 ----
worstq = float(max(abs(r['alpha_mp'] * r['rho_mp'] - abs(r['b'])) for r in quads))
eq_iff_unit = all((abs(r['rho_mp'] - 1 / r['alpha_mp']) < mpf('1e-20')) == r['unit']
                  for r in quads)
verdict['degree_two_identity'] = dict(
    kind='alpha |beta| = |b|, so rho = 1/alpha iff |b| = 1  (one_le_alpha_mul_abs_beta)',
    ok=bool(worstq < 1e-18 and eq_iff_unit), max_defect=worstq,
    equality_iff_unit=bool(eq_iff_unit))

for name, v in verdict.items():
    print('%-22s %-64s %s' % (name, v['kind'], 'OK' if v['ok'] else 'FAIL'))

print()
print('smallest quadratic where Route A fires: alpha = %.10f  (%s)'
      % (verdict['ceiling']['quad_min_alpha'],
         min(fireq, key=lambda r: r['alpha'])['coeffs']))
print('smallest cubic    where Route A fires: alpha = %.10f  (%s)'
      % (verdict['ceiling']['cubic_min_alpha'],
         min(firec, key=lambda r: r['alpha'])['coeffs']))

for r in quads + cubs:
    for k in ('alpha_mp', 'rho_mp', 'prod_mp'):
        r.pop(k, None)

json.dump(dict(n_quadratic=len(quads), n_cubic=len(cubs), verdict=verdict),
          open('m1_cor5.json', 'w'), indent=1)
print('\n[results written to m1_cor5.json]')
