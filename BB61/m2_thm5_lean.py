#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Thm 5 -- one check per DECLARATION of BB61/RouteAFamily.lean.

The Lean proof of Theorem 5(i) does NOT follow the note's: Mathlib has no Rouche's theorem, so
the root count is done with the product of the moduli of all the roots (the constant term is
-1) plus two one-line bounds.  This script checks that argument step by step on the actual
polynomials, and then the parts of the note that the file states.

F1  exists_root_Ioo                 the real root of X^d - aX^{d-1} - 1 lies in (a, a+1)
F2  le_norm_of_one_le_norm          |z| >= 1  =>  |z| >= a - 1/2
F3  inv_le_norm_pow_of_norm_lt_one  |z| < 1   =>  |z|^{d-1} >= 1/(a+1)
F4  card_big_roots_eq_one           exactly one root of modulus >= 1, and it is simple
F5  the counting inequality          (a-1/2)^{2(d-1)} > (a+1)^{d-2}; and why a-1 is not enough
F6  norm_le_familyConjBound         a|z|^{d-1} <= 2, i.e. |z| <= (2/a)^{1/(d-1)}
F7  routeA_family_lt_one            a >= 2^{d+1} => A(alpha) < 1; plus the note's d=4,5,6 rows
F8  familyQuad_*                    d=2: rho = 1/alpha, A<1 iff a>=4, alpha_{2,4} = 2+sqrt5
F9  norm_sq_mul_eq_one_cubic        d=3: |z|^2 alpha = 1, A log2 alpha = 3, A<1 iff a>=8
F10 familyPoly_irreducible          the trinomial is irreducible over Q

Requires mpmath; F10 additionally requires sympy.
"""
import math, json, mpmath as mp

mp.mp.dps = 60
RES = {}
FAILS = 0

DS = [2, 3, 4, 5, 6, 7, 8]
AS = [3, 4, 5, 7, 8, 9, 16, 17, 32, 33, 64, 65, 129]


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


def roots_of(d, a):
    """all complex roots of X^d - a X^{d-1} - 1, at 60 digits"""
    coeffs = [mp.mpf(1), mp.mpf(-a)] + [mp.mpf(0)] * (d - 2) + [mp.mpf(-1)]
    return mp.polyroots(coeffs, maxsteps=500, extraprec=500)


CASES = [(d, a) for d in DS for a in AS]
ROOTS = {(d, a): roots_of(d, a) for (d, a) in CASES}


def big_real(d, a):
    """the root of largest modulus (the Pisot number)"""
    return max(ROOTS[(d, a)], key=lambda z: abs(z))


# ---------------- F1: the real root in (a, a+1) ----------------
bad = 0
for (d, a) in CASES:
    al = big_real(d, a)
    if abs(mp.im(al)) > mp.mpf(10) ** -40 or not (a < mp.re(al) < a + 1):
        bad += 1
report('F1', bad == 0,
       'the largest root is real and lies in (a, a+1) in all %d cases (d in %s, a in %s)'
       % (len(CASES), DS, AS))

# ---------------- F2 / F3: the two one-line bounds ----------------
bad2 = bad3 = 0
worst2 = mp.inf
worst3 = mp.inf
for (d, a) in CASES:
    for z in ROOTS[(d, a)]:
        if abs(z) >= 1:
            if abs(z) < a - mp.mpf(1) / 2 - mp.mpf(10) ** -40:
                bad2 += 1
            worst2 = min(worst2, abs(z) - (a - mp.mpf(1) / 2))
        else:
            if abs(z) ** (d - 1) < 1 / mp.mpf(a + 1) - mp.mpf(10) ** -40:
                bad3 += 1
            worst3 = min(worst3, abs(z) ** (d - 1) - 1 / mp.mpf(a + 1))
report('F2', bad2 == 0,
       '|z| >= 1 forces |z| >= a - 1/2 on every root of every case (tightest slack %.3e)'
       % float(worst2))
report('F3', bad3 == 0,
       '|z| < 1 forces |z|^{d-1} >= 1/(a+1) on every root of every case (tightest slack %.3e)'
       % float(worst3))

# ---------------- F4: exactly one big root, and it is simple ----------------
bad = 0
for (d, a) in CASES:
    big = [z for z in ROOTS[(d, a)] if abs(z) >= 1]
    if len(big) != 1:
        bad += 1
    # simplicity: the other roots are well separated from it
    al = big_real(d, a)
    if min(abs(z - al) for z in ROOTS[(d, a)] if z is not al) < mp.mpf(10) ** -20:
        bad += 1
    # the product of all moduli is 1 (the constant term is -1)
    prod = mp.mpf(1)
    for z in ROOTS[(d, a)]:
        prod *= abs(z)
    if abs(prod - 1) > mp.mpf(10) ** -40:
        bad += 1
report('F4', bad == 0,
       'exactly one root of modulus >= 1, simple, and the product of all moduli is 1, '
       'in all %d cases' % len(CASES))

# ---------------- F5: the counting inequality, and why a-1 is not enough ----------------
sharp_ok = weak_at_three = True
for d in range(2, 40):
    for a in range(3, 200):
        if not (mp.mpf(a - 0.5) ** (2 * (d - 1)) > mp.mpf(a + 1) ** (d - 2)):
            sharp_ok = False
# with the cruder bound a-1 the same chain gives (a-1)^2 <= a+1, which at a=3 is 4 <= 4:
weak_at_three = (mp.mpf(3 - 1) ** 2 == mp.mpf(3 + 1))
report('F5', sharp_ok and weak_at_three,
       '(a-1/2)^{2(d-1)} > (a+1)^{d-2} for 2<=d<40, 3<=a<200 -- the contradiction of the Lean '
       'count; with the cruder bound a-1 the chain degenerates to 4 <= 4 at a = 3, which is '
       'why the second pass to a - 1/2 is in the proof')

# ---------------- F6: the conjugate bound ----------------
bad = 0
worst = mp.mpf(0)
for (d, a) in CASES:
    al = big_real(d, a)
    for z in ROOTS[(d, a)]:
        if z is al:
            continue
        if a * abs(z) ** (d - 1) > 2 + mp.mpf(10) ** -40:
            bad += 1
        if abs(z) > (mp.mpf(2) / a) ** (mp.mpf(1) / (d - 1)) + mp.mpf(10) ** -40:
            bad += 1
        worst = max(worst, a * abs(z) ** (d - 1))
report('F6', bad == 0,
       'a|z|^{d-1} <= 2 and |z| <= (2/a)^{1/(d-1)} for every conjugate in all %d cases '
       '(largest a|z|^{d-1} seen: %.6f)' % (len(CASES), float(worst)))


def A_of(d, a):
    al = big_real(d, a)
    rho = max(abs(z) for z in ROOTS[(d, a)] if z is not al)
    L = mp.log(abs(al)) / mp.log(2)
    R = mp.log(1 / rho) / mp.log(2)
    return 1 / L + 1 / R, L, R, mp.re(al), rho


# ---------------- F7: the criterion, and the note's own d=4,5,6 rows ----------------
bad = 0
for (d, a) in CASES:
    if a >= 2 ** (d + 1):
        if not A_of(d, a)[0] < 1:
            bad += 1
note_rows = {}
ok7 = bad == 0
for d in (4, 5, 6):
    for a in (2 ** d, 2 ** d + 1):
        A = float(A_of(d, a)[0]) if (d, a) in ROOTS else None
        if A is None:
            ROOTS[(d, a)] = roots_of(d, a)
            A = float(A_of(d, a)[0])
        note_rows['%d,%d' % (d, a)] = A
    ok7 &= note_rows['%d,%d' % (d, 2 ** d)] > 1 and note_rows['%d,%d' % (d, 2 ** d + 1)] < 1
report('F7', ok7,
       "a >= 2^{d+1} gives A < 1 in every case; and the note's rows reproduce -- "
       'A(d=4,a=16)=%.5f, a=17: %.5f; A(d=5,a=32)=%.5f, a=33: %.5f; A(d=6,a=64)=%.5f, a=65: %.5f'
       % tuple(note_rows['%d,%d' % (d, a)] for d in (4, 5, 6) for a in (2 ** d, 2 ** d + 1)))
RES['F7'] = dict(ok=ok7, note_rows=note_rows)

# ---------------- F8: degree two ----------------
bad = 0
for a in range(1, 60):
    if (2, a) not in ROOTS:
        ROOTS[(2, a)] = roots_of(2, a)
    A, L, R, al, rho = A_of(2, a)
    if abs(rho - 1 / al) > mp.mpf(10) ** -40:
        bad += 1                                  # rho = 1/alpha exactly
    if (A < 1) != (a >= 4):
        bad += 1                                  # the exact threshold
    if abs(al - (a + mp.sqrt(mp.mpf(a) ** 2 + 4)) / 2) > mp.mpf(10) ** -40:
        bad += 1                                  # familyQuad's closed form
a3 = float(A_of(2, 3)[3])
a4 = float(A_of(2, 4)[3])
ok8 = bad == 0 and a3 < 4 < a4 and abs(a4 - (2 + math.sqrt(5))) < 1e-12
report('F8', ok8,
       'd=2: rho = 1/alpha exactly, alpha = (a+sqrt(a^2+4))/2, and A<1 iff a>=4, for 1<=a<60; '
       'alpha_{2,3} = %.4f < 4 < %.4f = alpha_{2,4} = 2+sqrt5' % (a3, a4))

# ---------------- F9: degree three ----------------
bad = 0
for a in range(3, 60):
    if (3, a) not in ROOTS:
        ROOTS[(3, a)] = roots_of(3, a)
    A, L, R, al, rho = A_of(3, a)
    small = [z for z in ROOTS[(3, a)] if abs(z) < 1]
    if len(small) != 2 or abs(mp.im(small[0])) < mp.mpf(10) ** -20:
        bad += 1                                  # a genuine complex pair
    for z in small:
        if abs(abs(z) ** 2 * al - 1) > mp.mpf(10) ** -40:
            bad += 1                              # |z|^2 alpha = 1
    if abs(A * L - 3) > mp.mpf(10) ** -40:
        bad += 1                                  # ON the Prop. 4 ceiling
    if (A < 1) != (a >= 8):
        bad += 1
a7 = float(A_of(3, 7)[3])
a8 = float(A_of(3, 8)[3])
ok9 = bad == 0 and a7 < 8 < a8
report('F9', ok9,
       'd=3: the two conjugates are a complex pair with |z|^2 alpha = 1, A log2 alpha = 3 '
       '(on the Prop. 4 ceiling) and A<1 iff a>=8, for 3<=a<60; alpha_{3,7} = %.4f < 8 < %.4f '
       '= alpha_{3,8}' % (a7, a8))

# ---------------- F10: irreducibility ----------------
try:
    import sympy
    X = sympy.Symbol('X')
    bad = 0
    for (d, a) in [(d, a) for d in DS for a in (3, 4, 5, 8, 9, 16, 17)]:
        p = sympy.Poly(X ** d - a * X ** (d - 1) - 1, X)
        if not p.is_irreducible:
            bad += 1
    report('F10', bad == 0,
           'X^d - aX^{d-1} - 1 is irreducible over Q in all %d checked (d,a)'
           % len([(d, a) for d in DS for a in (3, 4, 5, 8, 9, 16, 17)]))
except ImportError:
    report('F10', False, 'sympy not available')

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m2_thm5_lean.json', 'w'), indent=1)
