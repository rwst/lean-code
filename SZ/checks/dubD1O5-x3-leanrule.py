# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X3 for plan-dubD1O5 (milestone M2): independent re-implementation of the selection rule
# formalised in SZ/CoverGame.lean (`pick`: prefer a = 0, then prefer b = 2), sharing no
# code with the Lean development and none with X0/X1.
#
# What it pins:
#   * the witness this rule produces --- xi = 1.3416089979611266516309894306526154258451...
#     which is NOT the X0/X1 witness 1.341665814942779748832194927978... (both are valid;
#     the translate equation has a Cantor set of solutions and the preference order picks
#     one of them);
#   * the cover invariant 0 <= W k <= 3 + 3 sqrt3, asserted at every one of 2000 steps;
#   * lemma L1 empirically: zeros in the a-stream, twos in the b-stream, longest runs;
#   * all floors [xi sqrt3^n], n = 1..1000, even AND determined (no straddles).
#
# Arithmetic: exact.  Z[sqrt 3] comparisons via the integer comparator p^2 vs 3q^2;
# the reals as Fraction with a rigorous 3^-N tail; floors via math.isqrt with an
# explicit correction loop.  No floats decide anything.

# Rigorous pin of the Lean witness: exact rationals + exact integer floor tests.
from fractions import Fraction
import math

def sign3(p, q):
    if p == 0 and q == 0: return 0
    if p >= 0 and q >= 0: return 1
    if p <= 0 and q <= 0: return -1
    d = p*p - 3*q*q
    assert d != 0
    return 1 if (p > 0) == (d > 0) else -1

def pick(p, q):
    if sign3(p-1, q-1) <= 0: return (0, 0)
    if sign3(p, q-2)   <  0: return (2, 0)
    if sign3(p-1, q-3) <= 0: return (0, 2)
    return (2, 2)

def run(N):
    p, q = -12, 9
    A, B = [], []
    for k in range(N):
        a, b = pick(p, q); A.append(a); B.append(b)
        p, q = 3*(p-a), 3*(q-b)
        # invariant check: 0 <= w <= 3+3sqrt3  i.e. sign3(p,q)>=0 and sign3(3-p,3-q)>=0
        assert sign3(p, q) >= 0, k
        assert sign3(3-p, 3-q) >= 0, k
    return A, B

for N in (400, 600, 800):
    A, B = run(N)
    x  = sum(Fraction(A[i], 3**(i+1)) for i in range(N))
    xi = (4 + x) / 3
    # exact decimal expansion of xi to 40 places, with the tail bounded by 3^-N
    lo = xi
    hi = xi + Fraction(1, 3**N) / 3        # (4+x)/3 with x <= X_N + 3^-N
    d_lo = (lo.numerator * 10**40) // lo.denominator
    d_hi = (hi.numerator * 10**40) // hi.denominator
    tag = "EXACT" if d_lo == d_hi else "ambiguous"
    s = str(d_lo).rjust(41, "0")
    print(f"N={N}: xi = {s[:-40]}.{s[-40:]}   [{tag}]")

A, B = run(2000)
# L1 empirically
print()
print(f"a-stream: {A.count(0)} zeros / 2000, longest all-2 run "
      f"{max(len(r) for r in ''.join(map(str,A)).split('0'))}")
print(f"b-stream: {B.count(2)} twos  / 2000, longest all-0 run "
      f"{max(len(r) for r in ''.join(map(str,B)).split('2'))}")

# floors n = 1..1000, exact integer arithmetic
N = 2000
x  = sum(Fraction(A[i], 3**(i+1)) for i in range(N))
xlo, xhi = x, x + Fraction(1, 3**N)
odd = []
for n in range(1, 1001):
    s = n // 2
    def fl(xv, half):
        c = (4 + xv) / 3 * Fraction(3**s)
        if not half:
            return c.numerator // c.denominator
        num, den = c.numerator, c.denominator
        f = math.isqrt(3 * num * num // (den * den))
        while (f+1)**2 * den * den <= 3*num*num: f += 1
        while f*f * den * den > 3*num*num:       f -= 1
        return f
    half = (n % 2 == 1)
    if half: s = (n - 1) // 2
    a1, a2 = fl(xlo, half), fl(xhi, half)
    if a1 != a2:
        odd.append((n, "STRADDLE")); continue
    if a1 % 2 != 0: odd.append((n, a1))
print()
print("n = 1..1000: odd floors or straddles ->", odd if odd else "NONE (all even, all determined)")
