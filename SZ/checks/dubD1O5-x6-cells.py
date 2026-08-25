# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X6 for plan-dubD1O5: independent re-implementation of the generic cover game formalised
# in SZ/Slice.lean, SZ/SliceHygiene.lean and SZ/Cells.lean --- the four cells
# m in {5,6,7,8} of Theorem B.  Shares no code with the Lean development, and none with
# X0/X1/X3/X4/X5.
#
# What it pins:
#   * the two gap conditions 2 <= U and 2 sqrt m - e <= U, and the translate
#     sigma = (2 k0 + M) sqrt m - 2j in (0, U), for each cell;
#   * the cover invariant 0 <= w_k <= m U at every one of 2000 steps, and every digit
#     in Ev = {0, 2, ..., e};
#   * that the rule of SZ/Slice.lean --- largest even b with b sqrt m <= w, then least
#     even a clearing the window --- coincides with the abstract description of the
#     paper's Remark 5.1, "smallest admissible a, then largest b" (both are computed
#     here, independently, and compared);
#   * the witness xi = (2j + <a>)/m to 25 exact decimals against the table of
#     paper-dubD1O5.tex Section 6.1;
#   * all floors [xi sqrt m ^ n], n = 1..200, even AND determined (no straddles);
#   * tail hygiene: for odd m (e = m-1) the counts of a_i != e and b_i != 0; for even m
#     (e = m-2) that every digit is already <= m-2, so hygiene is not needed.
#
# Arithmetic: exact.  States are integer pairs (P, Q) meaning (P + Q sqrt m)/(m-1);
# comparisons via the integer comparator P^2 vs m Q^2; reals as Fraction with a rigorous
# m^-N tail; floors via math.isqrt with an explicit correction loop.  No floats decide
# anything.

from fractions import Fraction
import math

# ---------------------------------------------------------------- exact sign in Z[sqrt m]

def sgn(P, Q, m):
    """sign of P + Q sqrt(m), for integers P, Q and non-square m."""
    if P == 0 and Q == 0:
        return 0
    if P >= 0 and Q >= 0:
        return 1
    if P <= 0 and Q <= 0:
        return -1
    d = P * P - m * Q * Q
    assert d != 0, "sqrt m would be rational"
    return 1 if ((P > 0) == (d > 0)) else -1

# ------------------------------------------------------------------------ the cells

CELLS = [
    # m, e, j, k0, the 25 decimals of xi from paper-dubD1O5.tex Section 6.1
    (5, 4, 2, 1, "0.8960002460904113337184490"),
    (6, 4, 3, 1, "1.0018433448290415598230006"),
    (7, 6, 3, 1, "0.8639261417201230285459622"),
    (8, 6, 3, 1, "0.8179408610740451796987635"),
]

def gaps_ok(m, e):
    """2 <= U and 2 sqrt m - e <= U, with U = e(1+sqrt m)/(m-1)."""
    # U - 2 >= 0  <=>  (e - 2(m-1)) + e sqrt m >= 0
    g1 = sgn(e - 2 * (m - 1), e, m) >= 0
    # U - (2 sqrt m - e) >= 0  <=>  (e + e(m-1)) + (e - 2(m-1)) sqrt m >= 0
    g2 = sgn(e + e * (m - 1), e - 2 * (m - 1), m) >= 0
    return g1, g2

# ------------------------------------------------------------------------ the two rules

def rule_formula(P, Q, m, e):
    """SZ/Slice.lean: largest even b <= e with b sqrt m <= w, then least even a >= 0
    with w - a - b sqrt m <= U.  State is w = (P + Q sqrt m)/(m-1)."""
    b = None
    for cand in range(e, -1, -2):
        if sgn(P, Q - cand * (m - 1), m) >= 0:      # w - b sqrt m >= 0
            b = cand
            break
    assert b is not None
    a = None
    for cand in range(0, e + 1, 2):
        # U - (w - a - b sqrt m) >= 0
        if sgn(e - P + cand * (m - 1), e - Q + b * (m - 1), m) >= 0:
            a = cand
            break
    assert a is not None, "cover failed"
    return a, b

def rule_paper(P, Q, m, e):
    """paper Section 5.1: among admissible offsets, smallest a, then largest b."""
    best = None
    for a in range(0, e + 1, 2):
        for b in range(e, -1, -2):
            lo = sgn(P - a * (m - 1), Q - b * (m - 1), m) >= 0
            hi = sgn(e - P + a * (m - 1), e - Q + b * (m - 1), m) >= 0
            if lo and hi:
                best = (a, b)
                break
        if best is not None:
            break
    assert best is not None, "cover failed"
    return best

# ------------------------------------------------------------------------ the greedy

def run(m, e, j, k0, N):
    P, Q = -2 * j * m * (m - 1), m * (2 * k0 * (m - 1) + e)
    A, B = [], []
    for _ in range(N):
        # invariant 0 <= w <= m U
        assert sgn(P, Q, m) >= 0, "state below 0"
        assert sgn(m * e - P, m * e - Q, m) >= 0, "state above mU"
        a, b = rule_formula(P, Q, m, e)
        assert (a, b) == rule_paper(P, Q, m, e), "the two rules disagree"
        assert a % 2 == 0 and 0 <= a <= e and b % 2 == 0 and 0 <= b <= e
        A.append(a)
        B.append(b)
        P, Q = m * (P - a * (m - 1)), m * (Q - b * (m - 1))
    return A, B

# ------------------------------------------------------------------------ floors

def floors_even(m, xlo, xhi, nmax):
    """[xi sqrt m ^ n] for n = 1..nmax, from rigorous bounds on xi; reports failures."""
    bad = []
    for n in range(1, nmax + 1):
        s, half = (n // 2, n % 2 == 1)
        vals = []
        for x in (xlo, xhi):
            c = x * Fraction(m) ** s
            if not half:
                vals.append(c.numerator // c.denominator)
            else:
                num, den = c.numerator, c.denominator
                f = math.isqrt(m * num * num // (den * den))
                while (f + 1) ** 2 * den * den <= m * num * num:
                    f += 1
                while f * f * den * den > m * num * num:
                    f -= 1
                vals.append(f)
        if vals[0] != vals[1]:
            bad.append((n, "STRADDLE"))
        elif vals[0] % 2 != 0:
            bad.append((n, vals[0]))
    return bad

# ------------------------------------------------------------------------ main

N = 2000
print("X6 --- the four cells m in {5,6,7,8} of Theorem B (paper-dubD1O5.tex)\n")
for (m, e, j, k0, decimals) in CELLS:
    g1, g2 = gaps_ok(m, e)
    assert g1 and g2, (m, "gap conditions")
    # sigma in (0, U):  sigma = ((2k0(m-1)+e) sqrt m - 2j(m-1))/(m-1)
    sP, sQ = -2 * j * (m - 1), 2 * k0 * (m - 1) + e
    assert sgn(sP, sQ, m) > 0, (m, "sigma <= 0")
    assert sgn(e - sP, e - sQ, m) > 0, (m, "sigma >= U")
    A, B = run(m, e, j, k0, N)
    # xi = (2j + <a>)/m with a rigorous m^-N tail
    x = sum(Fraction(A[i], m ** (i + 1)) for i in range(N))
    tail = Fraction(e, (m - 1)) * Fraction(1, m ** N)
    xilo = (2 * j + x) / m
    xihi = (2 * j + x + tail) / m
    # 25 exact decimals
    d = 25
    lo = (xilo * 10 ** d).numerator // (xilo * 10 ** d).denominator
    hi = (xihi * 10 ** d).numerator // (xihi * 10 ** d).denominator
    assert lo == hi, (m, "xi not determined to 25 places")
    got = f"{lo // 10**d}.{str(lo % 10**d).zfill(d)}"
    ok = (got == decimals)
    bad = floors_even(m, xilo, xihi, 200)
    ne_e = sum(1 for a in A if a != e)
    ne_0 = sum(1 for b in B if b != 0)
    hyg = "free (e = m-2)" if e <= m - 2 else f"a!=e: {ne_e}/{N}, b!=0: {ne_0}/{N}"
    print(f"m = {m}: e = {e}, j = {j}, gaps ok, sigma in (0,U), {N} steps clean")
    print(f"   xi = {got}   {'MATCHES paper table' if ok else 'MISMATCH: ' + decimals}")
    print(f"   floors n=1..200: {'all even, all determined' if not bad else bad}")
    print(f"   hygiene: {hyg}")
    assert ok and not bad
    if e <= m - 2:
        assert max(A) <= m - 2 and max(e - b for b in B) <= m - 2
    else:
        assert ne_e > 0 and ne_0 > 0
print("\nall four cells: PASS")
