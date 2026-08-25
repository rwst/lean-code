#!/usr/bin/env python3
"""plan-dubD1 gate G-3: the R-6 *second* implementation, plus experiment X1.

(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).

This is deliberately an independent re-implementation of `plans/dubD1-x0-checks.py`.
It shares no code and, more importantly, no *representation*:

  * the first implementation works inside ``Z[sqrt 2]`` and decides every floor by an
    exact comparison of integer squares (``isqrt``);
  * this one never forms the quadratic-integer coordinates at all.  It builds a certified
    dyadic *enclosure* ``[L, H] / 2^P`` of the real number ``xi * alpha^n`` by interval
    arithmetic on scaled integers, and reads the floor off only when the enclosure
    separates two consecutive integers.  If it does not, the precision is doubled and the
    computation restarts, so a wrong answer cannot be produced by rounding.

Nothing here uses the identity ``floor(xi*alpha^n) = b*U_{n-1} - [n even]``; the orbit is
computed from the definition and the identity is *tested* against it (block [A]).

Blocks
  [A] Theorem A at ``alpha = 1 + sqrt 2``, ``xi = (2 - sqrt 2)/4``: floors even, and equal
      to ``P_{n-1} - [n even]``, for ``n <= 2000``.
  [B] the exact ``(a,b)`` scan, ``1 <= b <= a <= 20``: the design works **iff** ``a`` is
      even and ``b`` is odd.  Both directions observed, not derived: every failure is
      witnessed by an explicit ``n`` with an odd floor.
  [C] the mod-``m`` designs of Theorem C (``a = 0``, ``b = 1`` mod ``m``).
  [D] the golden-mean lattice obstruction, and the general mod-2 annihilator statement.
  [E] the exact Theorem-E atlas in degrees 3-5: Sturm-isolated roots over Q, irreducibility
      by exhaustive monic-factor search over Z, and the four hypotheses of Theorem E.
      Headline question: does the criterion catch any ``alpha < 3``?

Everything is exact: Fractions and integers only.  No floating point anywhere.
Runtime ~1 min.
"""

import sys
from fractions import Fraction
from itertools import product

# ----------------------------------------------------------------------------
# certified dyadic interval arithmetic on positive reals
# ----------------------------------------------------------------------------


def isqrt_newton(n: int) -> int:
    """floor(sqrt n) for n >= 0, by Newton on integers (own code, not stdlib)."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            break
        x = y
    while x * x > n:
        x -= 1
    while (x + 1) * (x + 1) <= n:
        x += 1
    return x


def sqrt_enclosure(D: int, P: int):
    """(L, H) with L/2^P <= sqrt D <= H/2^P and H = L + 1."""
    L = isqrt_newton(D << (2 * P))
    return L, L + 1


def imul(u, v, P):
    """interval product of two non-negative scaled intervals, rounded outwards."""
    (ul, uh), (vl, vh) = u, v
    return ((ul * vl) >> P, -((-(uh * vh)) >> P))


def floor_of(u, P):
    """the floor of any real in the interval, or None if not determined."""
    ul, uh = u
    a = ul >> P if ul >= 0 else -((-ul + (1 << P) - 1) >> P)
    b = uh >> P if uh >= 0 else -((-uh + (1 << P) - 1) >> P)
    return a if a == b else None


def orbit_floors(a: int, b: int, nmax: int):
    """floor(xi * alpha^n), n = 0..nmax, for  P = x^2 - a x - b,  xi = 1/2 - a/(2 sqrt D).

    alpha = (a + sqrt D)/2 with D = a^2 + 4b;  xi = -conj(alpha)/(alpha - conj(alpha)).
    Computed from these definitions by certified interval arithmetic only.
    """
    D = a * a + 4 * b
    P = 4 * nmax * max(2, D.bit_length()) // 2 + 256
    while True:
        SL, SH = sqrt_enclosure(D, P)
        one = 1 << P
        # alpha = (a + sqrt D)/2
        al = (a * one + SL) // 2
        ah = -((-(a * one + SH)) // 2)
        # xi = 1/2 - a/(2 sqrt D):  a/(2 sqrt D) enclosed by dividing by the sqrt bounds
        # upper bound of a/(2 sqrt D) uses the LOWER bound of sqrt D, and conversely.
        hi_q = -((-(a * one * one)) // (2 * SL))          # >= a/(2 sqrt D) * 2^P
        lo_q = (a * one * one) // (2 * SH)                # <= a/(2 sqrt D) * 2^P
        xl, xh = one // 2 - hi_q, one // 2 - lo_q
        if xl <= 0:
            P *= 2
            continue
        out, cur, ok = [], (xl, xh), True
        for _ in range(nmax + 1):
            f = floor_of(cur, P)
            if f is None:
                ok = False
                break
            out.append(f)
            cur = imul(cur, (al, ah), P)
        if ok:
            return out
        P *= 2


def lucas(a: int, b: int, m: int):
    """U_0..U_m for U_{k+2} = a U_{k+1} + b U_k, U_0 = 0, U_1 = 1."""
    U = [0, 1]
    while len(U) <= m:
        U.append(a * U[-1] + b * U[-2])
    return U


# ----------------------------------------------------------------------------
# [A] Theorem A
# ----------------------------------------------------------------------------

def block_A():
    print("[A] Theorem A: alpha = 1 + sqrt 2, xi = (2 - sqrt 2)/4")
    N = 2000
    fl = orbit_floors(2, 1, N)
    odd = [(n, v) for n, v in enumerate(fl) if v % 2]
    print(f"    floors n=0..{N} computed by interval arithmetic; odd values: {len(odd)}")
    # test the closed form against the independently computed floors
    U = lucas(2, 1, N + 1)          # Pell numbers P_m = U_m(2,1)
    pred = [(U[n - 1] if n >= 1 else 1) - (1 if n % 2 == 0 else 0) for n in range(N + 1)]
    bad = [n for n in range(N + 1) if pred[n] != fl[n]]
    print(f"    closed form  P_(n-1) - [n even]  (P_(-1) := 1): mismatches {len(bad)}")
    print(f"    first terms: {fl[:9]}")
    return len(odd) == 0 and not bad


# ----------------------------------------------------------------------------
# [B] the exact (a,b) scan
# ----------------------------------------------------------------------------

def block_B(amax=20, nmax=60):
    print(f"[B] exact (a,b) scan, 1 <= b <= a <= {amax}, n <= {nmax}")
    works, fails, mism = [], [], []
    for a in range(1, amax + 1):
        for b in range(1, a + 1):
            D = a * a + 4 * b
            if isqrt_newton(D) ** 2 == D:
                continue                        # reducible: alpha rational
            fl = orbit_floors(a, b, nmax)
            alleven = all(v % 2 == 0 for v in fl)
            predicted = (a % 2 == 0) and (b % 2 == 1)
            if alleven != predicted:
                mism.append((a, b, alleven, predicted))
            if alleven:
                works.append((a, b))
            else:
                first = next(n for n, v in enumerate(fl) if v % 2)
                fails.append((a, b, first))
    print(f"    design works for {len(works)} pairs, fails for {len(fails)}")
    print(f"    works  = {works}")
    print(f"    a even and b odd = {[(a, b) for (a, b) in works]}"
          f" -- criterion mismatches: {mism}")
    fs = ", ".join(f"({a},{b}):n={n}" for a, b, n in fails[:12])
    print(f"    first odd floor at each failure (sample): {fs}")
    # the closed form on the whole family, as a second consistency test
    bad = []
    for a, b in works + [(x, y) for x, y, _ in fails]:
        fl = orbit_floors(a, b, 40)
        U = lucas(a, b, 41)
        pred = [(b * U[n - 1] if n >= 1 else 1) - (1 if n % 2 == 0 else 0)
                for n in range(41)]
        if pred != fl:
            bad.append((a, b))
    print(f"    closed form  b*U_(n-1) - [n even]  over the whole family: mismatches {bad}")
    return not mism and not bad


# ----------------------------------------------------------------------------
# [C] Theorem C: total divisibility designs
# ----------------------------------------------------------------------------

def block_C(nmax=400):
    print(f"[C] Theorem C: a = 0, b = 1 (mod m)  ==>  m | floor(xi alpha^n), n <= {nmax}")
    rows = []
    for m in range(2, 8):
        for a in range(m, 3 * m + 1, m):
            for b in range(1, a + 1):
                if b % m != 1 % m:
                    continue
                D = a * a + 4 * b
                if isqrt_newton(D) ** 2 == D:
                    continue
                fl = orbit_floors(a, b, nmax)
                ok = all(v % m == 0 for v in fl)
                rows.append((m, a, b, ok))
    bad = [r for r in rows if not r[3]]
    for m, a, b, ok in rows[:10]:
        print(f"    m={m} (a,b)=({a},{b}): all divisible = {ok}")
    print(f"    {len(rows)} designs tested, failures: {bad}")
    return not bad


# ----------------------------------------------------------------------------
# [D] the mod-2 lattice obstruction
# ----------------------------------------------------------------------------

def block_D():
    print("[D] the mod-2 annihilator criterion")
    # alternating pattern (1,0,1,0,...) solves T_{n+2} = a T_{n+1} + b T_n mod 2
    # iff  (x+1)^2 | x^2 - a x - b  in F_2[x], i.e. iff a even and b odd.
    rows = []
    for a in range(0, 6):
        for b in range(0, 6):
            seq = [1, 0]
            for _ in range(12):
                seq.append((a * seq[-1] + b * seq[-2]) % 2)
            alt = all(seq[i] == (1 if i % 2 == 0 else 0) for i in range(len(seq)))
            # (x+1)^2 = x^2 + 1 in F_2[x];  x^2 - a x - b = x^2 + a x + b mod 2
            lat = (a % 2 == 0) and (b % 2 == 1)
            rows.append((a, b, alt, lat))
    bad = [r for r in rows if r[2] != r[3]]
    print(f"    (1,0)^inf admissible <=> (x+1)^2 | P mod 2 : mismatches {bad}")
    # golden mean control
    seq = [1, 0]
    for _ in range(10):
        seq.append((seq[-1] + seq[-2]) % 2)
    print(f"    golden mean a=b=1: orbit of the seed (1,0) mod 2 = {seq[:9]} (period 3)")
    fl = orbit_floors(1, 1, 40)
    print(f"    and indeed floor(xi phi^n) for the design xi: {fl[:10]} "
          f"(odd values present: {any(v % 2 for v in fl)})")
    return not bad


# ----------------------------------------------------------------------------
# [E] the exact Theorem-E atlas, degrees 3-5
# ----------------------------------------------------------------------------

def poly_eval(c, x):
    """c = [c_0, ..., c_d] ascending, evaluate at Fraction/int x."""
    r = 0
    for a in reversed(c):
        r = r * x + a
    return r


def poly_derivative(c):
    return [i * c[i] for i in range(1, len(c))] or [0]


def poly_divmod(u, v):
    """exact division of Q-polynomials (ascending), returns (q, r)."""
    u = [Fraction(x) for x in u]
    v = [Fraction(x) for x in v]
    while v and v[-1] == 0:
        v.pop()
    q = [Fraction(0)] * max(0, len(u) - len(v) + 1)
    while len(u) >= len(v) and any(x != 0 for x in u):
        while u and u[-1] == 0:
            u.pop()
        if len(u) < len(v):
            break
        k = len(u) - len(v)
        f = u[-1] / v[-1]
        q[k] = f
        for i in range(len(v)):
            u[k + i] -= f * v[i]
        u.pop()
    while u and u[-1] == 0:
        u.pop()
    return q, u


def sturm_chain(c):
    """Sturm chain of a squarefree Q-polynomial (ascending coefficients)."""
    chain = [[Fraction(x) for x in c], [Fraction(x) for x in poly_derivative(c)]]
    while True:
        _, r = poly_divmod(chain[-2], chain[-1])
        if not r or all(x == 0 for x in r):
            break
        chain.append([-x for x in r])
    return chain


def sign_changes(chain, x):
    s, prev = 0, 0
    for p in chain:
        v = poly_eval(p, x)
        if v == 0:
            continue
        sg = 1 if v > 0 else -1
        if prev != 0 and sg != prev:
            s += 1
        prev = sg
    return s


def count_roots(chain, lo, hi):
    """number of distinct real roots in (lo, hi]."""
    return sign_changes(chain, lo) - sign_changes(chain, hi)


def is_squarefree(c):
    g = c[:]
    d = poly_derivative(c)
    a, b = [Fraction(x) for x in g], [Fraction(x) for x in d]
    while b and any(x != 0 for x in b):
        _, r = poly_divmod(a, b)
        a, b = b, r
    return len(a) <= 1


def isolate_roots(c, M):
    """isolate all real roots of a squarefree poly in (-M, M]; returns rational intervals."""
    chain = sturm_chain(c)
    total = count_roots(chain, Fraction(-M), Fraction(M))
    todo, out = [(Fraction(-M), Fraction(M), total)], []
    while todo:
        lo, hi, k = todo.pop()
        if k == 0:
            continue
        if k == 1:
            out.append((lo, hi))
            continue
        mid = (lo + hi) / 2
        k1 = count_roots(chain, lo, mid)
        todo.append((lo, mid, k1))
        todo.append((mid, hi, k - k1))
    return sorted(out), total


def refine(c, lo, hi, width):
    """bisect an isolating interval (lo, hi] until hi - lo < width."""
    flo = poly_eval(c, lo)
    while hi - lo >= width:
        mid = (lo + hi) / 2
        fm = poly_eval(c, mid)
        if fm == 0:
            return mid, mid
        if (flo < 0) != (fm < 0):
            hi = mid
        else:
            lo, flo = mid, fm
    return lo, hi


def monic_factors_exist(c, d, M):
    """True iff the monic integer poly c (ascending, degree d) has a nonconstant monic
    integer factor of degree <= d//2.  Roots have modulus <= M, so a degree-k monic
    factor has |coefficient_j| <= binom(k, j) M^(k-j)."""
    from math import comb
    for k in range(1, d // 2 + 1):
        ranges = []
        for j in range(k):                      # coefficients of x^j, j = 0..k-1
            bnd = comb(k, j) * M ** (k - j)
            ranges.append(range(-bnd, bnd + 1))
        for tup in product(*ranges):
            g = list(tup) + [1]
            q, r = poly_divmod(c, g)
            if not r or all(x == 0 for x in r):
                if all(x.denominator == 1 for x in q):
                    return True
    return False


def mod2_ok(c):
    """(x+1)^2 = x^2 + 1 divides P in F_2[x] ?"""
    c2 = [x % 2 for x in c]
    _, r = poly_divmod(c2, [1, 0, 1])
    return not r or all(Fraction(x) % 2 == 0 for x in r)


def cheap_pisot_filter(c, d, B):
    """necessary integer conditions for: exactly one root in (1, B), all others in (-1, 1).

    P(1) = prod(1 - alpha_j) < 0;  P(B) > 0;  (-1)^d P(-1) > 0;  P(0) = c_0 != 0."""
    if c[0] == 0:
        return False
    if poly_eval(c, 1) >= 0:
        return False
    if poly_eval(c, B) <= 0:
        return False
    return (poly_eval(c, -1) > 0) if d % 2 == 0 else (poly_eval(c, -1) < 0)


def theoremE_check(c, degree, M):
    """full certified test of Theorem E's hypotheses on a monic integer polynomial.

    Returns (alpha_lo, alpha_hi, a2_lo, a2_hi) if P is irreducible, totally real, Pisot,
    and satisfies (i) alpha_2 real negative with |alpha_2| > |alpha_3|; else None.
    Hypothesis (ii) is checked by the caller (mod2_ok)."""
    if not is_squarefree(c):
        return None
    roots, total = isolate_roots(c, M)
    if total != degree:
        return None                                  # not totally real
    rr = [refine(c, lo, hi, Fraction(1, 10 ** 6)) for lo, hi in roots]
    big = [(lo, hi) for lo, hi in rr if lo > 1]
    small = [(lo, hi) for lo, hi in rr if hi < 1 and lo > -1]
    if len(big) != 1 or len(small) != degree - 1:
        return None
    if monic_factors_exist(c, degree, M):
        return None                                  # reducible
    mods = sorted(((max(abs(lo), abs(hi)), min(abs(lo), abs(hi)), lo, hi)
                   for lo, hi in small), reverse=True)
    hi2, lo2, l2, h2 = mods[0]
    if h2 >= 0:                                      # alpha_2 must be real negative
        return None
    if degree > 2 and lo2 <= mods[1][0]:             # strict domination |a_2| > |a_3|
        return None
    return big[0][0], big[0][1], l2, h2


def atlas(degree, cmax):
    """display atlas: all Theorem-E instances with |c_i| <= cmax."""
    hits = []
    for tup in product(*[range(-cmax, cmax + 1) for _ in range(degree)]):
        c = list(tup) + [1]
        if c[0] == 0 or not mod2_ok(c):
            continue
        M = 1 + max(abs(x) for x in c[:-1])
        res = theoremE_check(c, degree, M)
        if res:
            hits.append((tuple(c),) + res)
    return hits


def sym_bounds(degree, B):
    """|e_k| <= C(d-1,k-1) B + C(d-1,k) for one root in (1,B) and d-1 roots in (-1,1).

    Returns the per-coefficient bounds for c_(d-k), k = 1..d."""
    from math import comb
    d = degree
    return [comb(d - 1, k - 1) * B + comb(d - 1, k) for k in range(1, d + 1)]


def sweep_below(degree, B=3):
    """EXHAUSTIVE sweep of Theorem-E instances with alpha < B, in the totally real class.

    The coefficient ranges are forced by alpha < B and |alpha_j| < 1, so the sweep is
    complete: no instance can escape it."""
    bnds = sym_bounds(degree, B)                     # bounds on |c_(d-1)|, ..., |c_0|
    ranges = [range(-bnds[degree - 1 - j], bnds[degree - 1 - j] + 1)
              for j in range(degree)]                # ascending c_0 .. c_(d-1)
    tested = kept = 0
    hits = []
    for tup in product(*ranges):
        c = list(tup) + [1]
        tested += 1
        if not cheap_pisot_filter(c, degree, B) or not mod2_ok(c):
            continue
        kept += 1
        M = 1 + max(abs(x) for x in c[:-1])
        res = theoremE_check(c, degree, M)
        if res and res[1] < B:
            hits.append((tuple(c),) + res)
    return bnds, tested, kept, hits


def block_E():
    print("[E] exact Theorem-E atlas (Sturm isolation over Q + exhaustive monic-factor")
    print("    irreducibility test).  Scope: the totally real class, where every")
    print("    hypothesis is exactly decidable.")
    allhits = []
    for degree, cmax in ((3, 6), (4, 3), (5, 2)):
        hits = atlas(degree, cmax)
        allhits += [(degree,) + h for h in hits]
        print(f"    display atlas, degree {degree}, |c_i| <= {cmax}: {len(hits)} instances")
        for c, alo, ahi, l2, h2 in sorted(hits, key=lambda t: t[1]):
            poly = "x^%d" % degree + "".join(
                f" {'+' if c[i] > 0 else '-'} {abs(c[i])}x^{i}"
                for i in range(degree - 1, -1, -1) if c[i])
            print(f"      {poly:<34} alpha = {float(alo):.6f}..  "
                  f"alpha_2 = {float(l2):.6f}..  P(1) = {poly_eval(list(c), 1)}")
    print()
    print("    EXHAUSTIVE sweep for alpha < 3 (coefficient ranges forced by the root")
    print("    locations, so nothing can escape):")
    total_below = []
    for degree in (2, 3, 4):
        bnds, tested, kept, hits = sweep_below(degree, 3)
        total_below += hits
        print(f"      degree {degree}: |c_(d-k)| <= {bnds}; {tested} polynomials swept, "
              f"{kept} survived the cheap filters, {len(hits)} instances with alpha < 3")
    print(f"    *** instances with alpha < 3, degrees 2-4: {len(total_below)}")
    for c, alo, ahi, l2, h2 in total_below:
        d = len(c) - 1
        poly = "x^%d" % d + "".join(
            f" {'+' if c[i] > 0 else '-'} {abs(c[i])}x^{i}"
            for i in range(d - 1, -1, -1) if c[i])
        print(f"        {poly:<22} alpha = {float(alo):.9f}..")
    # the named boundary case: tribonacci satisfies (ii) but has complex alpha_2
    tri = [-1, -1, -1, 1]
    _, tot = isolate_roots(tri, 3)
    print(f"    boundary case x^3 - x^2 - x - 1 (tribonacci): (x+1)^2 | P mod 2 = "
          f"{mod2_ok(tri)}, real roots = {tot} of 3, so alpha_2 is complex and (i) fails.")
    print("    (degree 5 not swept exhaustively: ~4.7e6 polynomials; the display atlas at")
    print("     |c_i| <= 2 is empty.)")
    return allhits, total_below


# ----------------------------------------------------------------------------

def main():
    ok = True
    ok &= block_A(); print()
    ok &= block_B(); print()
    ok &= block_C(); print()
    ok &= block_D(); print()
    block_E()
    print()
    print("ALL CONSISTENCY CHECKS PASSED" if ok else "*** MISMATCH ***")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
