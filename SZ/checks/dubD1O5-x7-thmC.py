# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X7 for plan-dubD1O5: independent re-implementation of the general-`p` cover game
# formalised in SZ/Slice.lean + SZ/SliceHygiene.lean + SZ/ThmC.lean (Theorem C of
# paper-dubD1O5.tex), sharing no code with the Lean development and none with X0/X1/X3/X6.
#
# What it pins, for every row of the paper's Section 7 table:
#   * the branch hypotheses of Theorem C, and (branch (ii)) the derived m > p^2;
#   * the two gap conditions p <= U and p sqrt m - e <= U of Theorem 4.1;
#   * the translate j = ceil((T-U)/p) of Lemma 3.3 -- against the j printed in the paper;
#   * the cover invariant 0 <= w <= mU and the digit alphabet {0,p,...,e}, at 2000 steps;
#   * the witness xi to 20 exact decimals, against the paper's table;
#   * the integral parts floor(xi sqrt m^n) for n = 1..6 against the table, and for
#     n <= 200: divisible by p AND unambiguously determined (no straddles).
#
# Arithmetic: exact.  States live in Q + Q sqrt m and are compared by the integer
# comparator P^2 vs m Q^2; the reals are Fractions with a rigorous m^-N tail; floors via
# math.isqrt with an explicit correction loop.  No float decides anything.

from fractions import Fraction as F
import math

# ---------------------------------------------------------------- comparator

def sgn(P, Q, m):
    """sign of P + Q*sqrt(m), P,Q rational, m a non-square positive integer."""
    if P == 0 and Q == 0:
        return 0
    if P >= 0 and Q >= 0:
        return 1
    if P <= 0 and Q <= 0:
        return -1
    d = P * P - m * Q * Q
    assert d != 0, "P + Q sqrt m = 0 with m non-square"
    return (1 if d > 0 else -1) if P > 0 else (-1 if d > 0 else 1)

def isqrt_frac(c, m):
    """floor(c * sqrt m) for a rational c >= 0."""
    num, den = c.numerator, c.denominator
    f = math.isqrt(m * num * num // (den * den))
    while (f + 1) ** 2 * den * den <= m * num * num:
        f += 1
    while f * f * den * den > m * num * num:
        f -= 1
    return f

# ---------------------------------------------------------------- the rule

class Cell:
    def __init__(self, p, m, branch):
        assert m >= 3 and p >= 2
        assert math.isqrt(m) ** 2 != m, "m must not be a square"
        self.p, self.m, self.branch = p, m, branch
        self.e = p * ((m - 1) // p)                 # largest multiple of p that is <= m-1
        self.M = F(self.e, m - 1)
        # U = M(1 + sqrt m)  as the pair (M, M) in Q + Q sqrt m
        self.Up, self.Uq = self.M, self.M
        if branch == 1:
            assert (m - 1) % p == 0 and p * p <= m
            assert self.e == m - 1
        elif branch == 0:
            # Remark 7.1: the covering induction and the translate need only U > p,
            # which on branch (i) reads m > (p-1)^2.  Between (p-1)^2 and p^2 the
            # construction runs but Proposition 5.4 does not apply -- hygiene is open.
            assert (m - 1) % p == 0 and (p - 1) ** 2 < m < p * p
            assert self.e == m - 1
        else:
            assert m % p == 0
            assert self.e == m - p
            # the window inequality, exactly: p(m-1) < (m-p)(1+sqrt m)
            assert sgn(F(m - p) - F(p * (m - 1)), F(m - p), m) > 0
            # ... and its consequence m > p^2 (paper Section 7)
            assert m > p * p, "branch (ii) must force m > p^2"
        # gap conditions of Theorem 4.1: p <= U and p sqrt m - e <= U
        assert sgn(self.Up - p, self.Uq, m) >= 0, "gap 1 (p <= U) fails"
        assert sgn(self.Up + self.e, self.Uq - p, m) >= 0, "gap 2 fails"

    def bsel(self, P, Q):
        b, t = 0, self.p
        while t <= self.e and sgn(P, Q - t, self.m) >= 0:
            b, t = t, t + self.p
        return b

    def asel(self, P, Q, b):
        # smallest multiple a of p with (v - U) - a <= 0, v = w - b sqrt m
        vp, vq = P - self.Up, Q - b - self.Uq          # v - U
        if sgn(vp, vq, self.m) <= 0:
            return 0
        a = self.p
        while sgn(vp - a, vq, self.m) > 0:
            a += self.p
            assert a <= self.e + self.p, "greedy escaped the alphabet"
        return a

    def run(self, j, k0, N):
        p, m = self.p, self.m
        P, Q = F(-p * j * m), m * (F(p * k0) + self.M)   # w0 = m sigma
        A, B = [], []
        for k in range(N):
            b = self.bsel(P, Q)
            a = self.asel(P, Q, b)
            assert a % p == 0 and 0 <= a <= self.e, (k, a)
            assert b % p == 0 and 0 <= b <= self.e, (k, b)
            A.append(a); B.append(b)
            P, Q = m * (P - a), m * (Q - b)
            # cover invariant 0 <= w <= mU
            assert sgn(P, Q, m) >= 0, ("w < 0", k)
            assert sgn(F(m) * self.Up - P, F(m) * self.Uq - Q, m) >= 0, ("w > mU", k)
        return A, B

    def translate(self, k0):
        """j = ceil((T-U)/p) with T = (p k0 + M) sqrt m, exactly."""
        p, m = self.p, self.m
        Tp, Tq = F(0), F(p * k0) + self.M
        Dp, Dq = Tp - self.Up, Tq - self.Uq          # T - U
        # smallest integer j with p*j >= T - U ; then check strictness and the window
        j = 0
        while sgn(Dp - p * j, Dq, m) > 0:
            j += 1
        assert sgn(Dp - p * j, Dq, m) < 0, "T - U = p j : impossible by irrationality"
        assert sgn(Tp - p * j, Tq, m) > 0, "sigma <= 0"
        return j

# ---------------------------------------------------------------- the table

TABLE = [
    # p,  m, branch, j, xi (20 decimals from the paper), floors n=1..6
    (3, 10, 1, 3, "0.96006939603936630600", [3, 9, 30, 96, 303, 960]),
    (3, 12, 2, 4, "1.02289606837742417779", [3, 12, 42, 147, 510, 1767]),
    (4, 17, 1, 4, "0.97053751681712857019", [4, 16, 68, 280, 1156, 4768]),
    (5, 26, 1, 5, "0.98376108969646594364", [5, 25, 130, 665, 3390, 17290]),
    # Remark 7.1: the construction runs below the hygiene threshold too (p^2-p+1 <= m < p^2)
    (3,  7, 0, 3, "1.29588921264222346083", [3, 9, 24, 63, 168, 444]),
]

N = 2000
NFLOOR = 200
DEC = 20
ok = True

for (p, m, branch, j_paper, xi_paper, floors_paper) in TABLE:
    C = Cell(p, m, branch)
    k0 = 1
    j = C.translate(k0)
    tag_j = "MATCH" if j == j_paper else "MISMATCH(paper %d)" % j_paper
    A, B = C.run(j, k0, N)

    # xi = (p j + x)/m with x = sum A[i] m^{-(i+1)}
    x_lo = sum(F(A[i], m ** (i + 1)) for i in range(N))
    x_hi = x_lo + F(1, m ** N)
    xi_lo, xi_hi = (F(p * j) + x_lo) / m, (F(p * j) + x_hi) / m
    d_lo = (xi_lo.numerator * 10 ** DEC) // xi_lo.denominator
    d_hi = (xi_hi.numerator * 10 ** DEC) // xi_hi.denominator
    exact = (d_lo == d_hi)
    s = str(d_lo).rjust(DEC + 1, "0")
    xi_str = "%s.%s" % (s[:-DEC], s[-DEC:])
    tag_xi = "MATCH" if (exact and xi_str == xi_paper) else \
             ("ambiguous" if not exact else "MISMATCH(paper %s)" % xi_paper)

    # floors, n = 1..NFLOOR, exact and two-sided
    bad = []
    got = []
    for n in range(1, NFLOOR + 1):
        s_exp = n // 2
        half = (n % 2 == 1)
        vals = []
        for xv in (xi_lo, xi_hi):
            c = xv * F(m ** s_exp)
            vals.append(isqrt_frac(c, m) if half else c.numerator // c.denominator)
        if vals[0] != vals[1]:
            bad.append((n, "STRADDLE")); continue
        if vals[0] % p != 0:
            bad.append((n, vals[0]))
        if n <= 6:
            got.append(vals[0])
    tag_fl = "MATCH" if got == floors_paper else "MISMATCH(paper %s)" % floors_paper

    good = (tag_j == "MATCH") and (tag_xi == "MATCH") and (tag_fl == "MATCH") and not bad
    ok = ok and good
    label = "branch(%d)" % branch if branch else "Rmk 7.1 "
    print("p=%d m=%2d %s  e=%2d  M=%-6s  j=%d [%s]" %
          (p, m, label, C.e, str(C.M), j, tag_j))
    print("    xi = %s...  [%s]" % (xi_str, tag_xi))
    print("    floors n=1..6: %s [%s]" % (got, tag_fl))
    print("    n=1..%d: %s" % (NFLOOR,
          ("all divisible by %d, all determined" % p) if not bad else ("PROBLEMS %s" % bad[:5])))
    print("    a-stream: %d/%d at the top digit e; b-stream: %d/%d at 0"
          % (A.count(C.e), N, B.count(0), N))
    print("    -> %s" % ("PASS" if good else "FAIL"))
    print()

print("all rows:", "PASS" if ok else "FAIL")
