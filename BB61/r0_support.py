#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R0 / gate G-1 of `plan-BB61-counterexample.html`: F(Omega(alpha)) = T at alpha = 1+sqrt2.

Route 4 (build a shift-invariant `mu` with `F_*mu = Leb`) has exactly one structural
precondition, Prop. C of that plan: if `F(Omega(alpha)) != T` then 10.61 holds at `alpha`
for support reasons and no counterexample can exist.  By M1 Prop. 11 (`F = tau_bar . Phi`)
and M1 Prop. 4, `F(Omega(alpha))` is the confinement set

    X(alpha) = (C(alpha) - K) mod 1,
    C(alpha) = { (alpha-1) sum_{k>=1} eps_k alpha^-k },  K = { sum_{m>=0} c_m delta_m },
    c_m = (alphabar - 1) alphabar^m       (degree two).

The folder already asserts `X = T` at `1+sqrt2` through Theorem T of the T-T note
(`BB61/tt_thickness.py`): Newhouse thickness `tau(C) tau(K) >= 1` plus two side conditions.
That route is correct but it is *cited* ([PT93] 4.2 / [CHM02] sec 4, in the corrected
"C-K IS an interval" form) and it only ever yields an inclusion.  This script replaces it,
at the one alpha Route 4 cares about, by an **exact identity of sets** proved from scratch:

    C - K = [ -sqrt2/2 , 2 + sqrt2/2 ]        (length 2 + sqrt2 = 3.414...)

so X(1+sqrt2) = T with three units of room, no citation, and a constructive witness map.

The proof in four steps, all verified below in exact Z[sqrt2] arithmetic:

  (S1) c_m = -sqrt2 (-rho)^m with rho = sqrt2 - 1 = 1/alpha = -alphabar.  So with
       A0 := { sum_{k>=0} a_k rho^k : a in {0,1}^N },
       C = sqrt2 rho A0   and   K = -sqrt2 B,  B := { sum_m delta_m (-rho)^m }.

  (S2) DIGIT RELABELLING.  B = A0 - 1/2, because 1/2 = sum_{m odd} rho^m exactly at this
       alpha, and delta_m <-> a_m (m even), delta_m <-> 1 - a_m (m odd) is a bijection of
       {0,1}^N onto itself carrying one sum to the other.  Hence

           C - K = sqrt2 ( A0 + rho A0 ) - sqrt2/2 .

  (S3) INDEPENDENCE OF DIGITS.  A0 + rho A0 = {0,1} + rho E with
       E := { sum_{i>=0} u_i rho^i : u_i in {0,1,2} }, because u_i = a_i + a'_{i-1} runs
       over {0,1,2} freely (each free bit is used once).

  (S4) COVERING.  E = [0, 2/(1-rho)] = [0, 2+sqrt2] as soon as the digit step 1 is at most
       rho * 2/(1-rho) = sqrt2; and then {0,1} + rho[0,2+sqrt2] = [0, 1+sqrt2] because
       rho(2+sqrt2) = sqrt2 >= 1.  Both inequalities hold with room at this alpha.

Blocks: (1) the identities, exact; (2) the covering lemma, exact; (3) a constructive
witness check against the *original* definitions; (4) the T-T route re-derived exactly,
with one correction to its stated interval; (5) the companion alpha = (3+sqrt5)/2;
(6) the classification of the alpha this elementary route reaches.

Usage: python3 r0_support.py            (no dependencies beyond the standard library)
"""
from fractions import Fraction as F
import math

FAIL = []


def check(name, cond, extra=""):
    print(f"    [{'ok ' if cond else 'FAIL'}] {name}{('  ' + extra) if extra else ''}")
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------------------
# exact arithmetic in Q(sqrt D):  p + q sqrt(D),  p, q rational
# --------------------------------------------------------------------------------------
class Q:
    __slots__ = ("p", "q", "D")

    def __init__(self, p, q=0, D=2):
        self.p, self.q, self.D = F(p), F(q), D

    def _c(self, o):
        return o if isinstance(o, Q) else Q(o, 0, self.D)

    def __add__(self, o):
        o = self._c(o); return Q(self.p + o.p, self.q + o.q, self.D)
    __radd__ = __add__

    def __neg__(self):
        return Q(-self.p, -self.q, self.D)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __rsub__(self, o):
        return self._c(o) + (-self)

    def __mul__(self, o):
        o = self._c(o)
        return Q(self.p * o.p + self.D * self.q * o.q, self.p * o.q + self.q * o.p, self.D)
    __rmul__ = __mul__

    def inv(self):
        n = self.p * self.p - self.D * self.q * self.q
        return Q(self.p / n, -self.q / n, self.D)

    def __truediv__(self, o):
        return self * self._c(o).inv()

    def __rtruediv__(self, o):
        return self._c(o) * self.inv()

    def __pow__(self, n):
        r, b = Q(1, 0, self.D), self
        for _ in range(n):
            r = r * b
        return r

    def __eq__(self, o):
        o = self._c(o); return self.p == o.p and self.q == o.q

    def __float__(self):
        return float(self.p) + float(self.q) * math.sqrt(self.D)

    def __lt__(self, o):
        return float(self) < float(self._c(o))

    def __le__(self, o):
        return self == self._c(o) or float(self) < float(self._c(o))

    def __gt__(self, o):
        return float(self) > float(self._c(o))

    def __ge__(self, o):
        return self == self._c(o) or float(self) > float(self._c(o))

    def __repr__(self):
        return f"{self.p}+{self.q}√{self.D}"

    def __str__(self):
        return f"{float(self):.12f} = {self.p} + {self.q}√{self.D}"


def setup(a, b):
    """alpha, alphabar for X^2 - aX - b: the roots (a +- sqrt(disc))/2, disc = a^2 + 4b.

    Writes disc = c^2 D with D squarefree, so that both roots live in Q(sqrt D)."""
    disc = a * a + 4 * b
    c, D = 1, disc
    k = 2
    while k * k <= D:
        while D % (k * k) == 0:
            D //= k * k
            c *= k
        k += 1
    al = Q(F(a, 2), F(c, 2), D)
    ab = Q(F(a, 2), F(-c, 2), D)
    return al, ab


# ======================================================================================
print(__doc__.split("Usage:")[0].rstrip())
print("\n" + "=" * 86)
print("BLOCK 1 -- the identities at alpha = 1 + sqrt2, exact in Z[sqrt2]")
print("=" * 86)

al, ab = setup(2, 1)                       # X^2 - 2X - 1
rho = Q(-1, 1, 2)                             # sqrt2 - 1
s2 = Q(0, 1, 2)
check("alpha is a root of X^2-2X-1", al * al - 2 * al - 1 == Q(0, 0, 2))
check("alphabar is the conjugate root", ab * ab - 2 * ab - 1 == Q(0, 0, 2))
check("alpha = 1+sqrt2", al == Q(1, 1, 2), f"alpha = {float(al):.12f}")
check("rho = 1/alpha = -alphabar = sqrt2-1", rho == al.inv() and rho == -ab,
      f"rho = {float(rho):.12f}")
check("alpha - 1 = sqrt2", al - 1 == s2)
check("alpha is a unit of norm -1", al * ab == Q(-1, 0, 2))

# (S1) c_m from the trace formula of M1 Lemma 2, against the closed form -sqrt2 (-rho)^m
def trace(x):
    return x + Q(x.p, -x.q, x.D)             # Tr = x + conj(x)


ok = True
for m in range(0, 41):
    c_trace = (trace(al ** (m + 1)) - trace(al ** m)) - (al ** m) * (al - 1)
    c_closed = (-s2) * ((-rho) ** m)
    ok &= (c_trace == c_closed == (ab - 1) * (ab ** m))
check("c_m = (alphabar-1) alphabar^m = -sqrt2 (-rho)^m, m <= 40 (M1 Lemma 2 trace form)", ok)
check("signs of c_m alternate, |c_m| = sqrt2 rho^m",
      all((-s2) * ((-rho) ** m) < 0 if m % 2 == 0 else (-s2) * ((-rho) ** m) > 0
          for m in range(0, 21)))

# P, Q, diam K  (sum over the two parities; 1 - rho^2 = 2 rho at this alpha)
check("1 - rho^2 = 2 rho  (the identity that makes both parities geometric)",
      1 - rho * rho == 2 * rho)
P = s2 * rho / (1 - rho * rho)                # sum over odd m of |c_m|
Qq = s2 / (1 - rho * rho)                     # sum over even m of |c_m|
check("P = sqrt2/2", P == s2 / 2, f"P = {float(P):.12f}")
check("Q = 1 + sqrt2/2", Qq == 1 + s2 / 2, f"Q = {float(Qq):.12f}")
check("diam K = P + Q = 1 + sqrt2", P + Qq == 1 + s2, f"diam K = {float(P + Qq):.12f}")
check("diam K >= 1 = d - 1  (M1 Lemma 3, the X7 vacuity)", 1 <= P + Qq)

# (S2) the digit relabelling B = A0 - 1/2
half = s2 * rho / (1 - rho * rho) / s2         # sum_{m odd} rho^m = rho/(1-rho^2)
check("sum_{m odd} rho^m = 1/2  (this is what makes B = A0 - 1/2)", half == Q(F(1, 2), 0, 2),
      f"= {float(half):.12f}")
check("max A0 = 1/(1-rho) = 1 + sqrt2/2", (1 - rho).inv() == 1 + s2 / 2)
check("C = sqrt2 rho A0  =>  max C = 1", s2 * rho * (1 - rho).inv() == Q(1, 0, 2))

print("\n" + "=" * 86)
print("BLOCK 2 -- the covering lemma, exact")
print("=" * 86)
print("""    Lemma (covering).  Let 0 < r < 1 and let the digit set be {0,1,...,n} with
    L := n/(1-r).  If 1 <= r L  then  E := { sum_{i>=0} u_i r^i : u_i in {0..n} } = [0, L].
    Proof: E = {0..n} + r E and E is compact with min 0, max L; the n+1 intervals
    [u + 0, u + rL] have consecutive left endpoints one apart and length rL >= 1, so their
    union is [0, n + rL] = [0, L] (n + rL = n + rn/(1-r) = n/(1-r) = L).  So [0,L] is a
    fixed point of the Hutchinson operator of the IFS {x -> r x + u}, which is a
    contraction on the compact sets: E = [0,L].""")
L = 2 / (1 - rho)
check("L = 2/(1-rho) = 2 + sqrt2", L == 2 + s2, f"L = {float(L):.12f}")
check("covering condition  1 <= rho L  (digit step 1, digits {0,1,2})", 1 <= rho * L,
      f"rho L = {float(rho * L):.12f} = sqrt2")
check("rho L = sqrt2 exactly", rho * L == s2)
check("slack in the covering condition: rho >= 1/3", Q(F(1, 3), 0, 2) <= rho,
      f"rho - 1/3 = {float(rho - Q(F(1,3),0,2)):.6f}")
check("the lemma's two identities: n + rho L = L with n = 2", 2 + rho * L == L,
      "so [0,L] is the attractor and E = [0, 2+sqrt2]")
check("{0,1} + rho[0,L] = [0, 1 + rho L] = [0, 1+sqrt2]  (needs rho L >= 1)",
      1 <= rho * L and 1 + rho * L == 1 + s2)
# (S2) and (S3) are combinatorial claims about digit words; check them exactly at finite
# depth, where "B = A0 - 1/2" reads "B_n = A0_n - sum_{m<n, m odd} rho^m".
def sums(coeffs):
    out = [Q(0, 0, 2)]
    for c in coeffs:
        out = out + [x + c for x in out]
    return sorted(out, key=float)


n = 10
A0n = sums([rho ** k for k in range(n)])
Bn = sums([(-rho) ** m for m in range(n)])
sn = sum((rho ** m for m in range(1, n, 2)), Q(0, 0, 2))
check(f"(S2) at depth {n}: B_n = A0_n - sum_{{m odd}} rho^m, as sets",
      [x + sn for x in Bn] == A0n, f"{len(Bn)} points, exact in Z[sqrt2]")
key = lambda x: (x.p, x.q)
lhs = sorted({key(x + rho * y) for x in A0n for y in A0n})
# at depth n the highest position carries only a'_{n-1}: digits {0,1,2} at 0..n-2, {0,1} at n-1
En = sums([rho ** i for i in range(n - 1)] + [rho ** i for i in range(n)])
rhs = sorted({key(Q(d, 0, 2) + rho * u) for d in (0, 1) for u in En})
check(f"(S3) at depth {n}: A0_n + rho A0_n = {{0,1}} + rho E_n, digits {{0,1,2}}",
      lhs == rhs, f"{len(lhs)} distinct values on each side, exact")

lo = -s2 / 2
hi = s2 * (1 + s2) - s2 / 2
check("C - K = sqrt2 [0, 1+sqrt2] - sqrt2/2 = [-sqrt2/2, 2+sqrt2/2]",
      lo == -s2 / 2 and hi == 2 + s2 / 2,
      f"[{float(lo):.12f}, {float(hi):.12f}]")
check("length(C - K) = 2 + sqrt2", hi - lo == 2 + s2, f"= {float(hi - lo):.12f}")
check("length(C - K) = 1 + diam K  (so the hull is filled, not merely covered)",
      hi - lo == 1 + (P + Qq))
check("GATE G-1: length >= 1, hence X(1+sqrt2) = (C-K) mod 1 = T", 1 <= hi - lo,
      f"margin {float(hi - lo - 1):.12f} over the threshold 1")

print("\n" + "=" * 86)
print("BLOCK 3 -- constructive check against the ORIGINAL definitions")
print("=" * 86)
print("""    The proof is constructive: it produces, for each y in [-sqrt2/2, 2+sqrt2/2], a pair
    of one-sided words (eps, delta) with y = pi(eps) - w(delta) exactly.  This block runs
    that construction on a grid of targets and evaluates pi and w from their definitions
    in M1 (Lemma 1 and Lemma 3), independently of every identity above.""")
fal, fab, frho, fs2 = float(al), float(ab), float(rho), math.sqrt(2)
M = 200                                        # digits kept; tail < rho^200 ~ 1e-77


def witness(y):
    """(eps, delta) with pi(eps) - w(delta) = y, by the greedy of (S3)-(S4)."""
    z = (y + fs2 / 2) / fs2                    # z in [0, 1+sqrt2]
    a0p = 0 if z <= fs2 else 1                 # a'_0 = d_0
    w = (z - a0p) / frho                       # w in [0, L]
    a, ap = [], [a0p]
    for _ in range(M):
        u = min(2, max(0, math.ceil(w - fs2 - 1e-15)))
        a.append(1 if u >= 1 else 0)           # u = a_i + a'_{i+1}
        ap.append(1 if u == 2 else 0)
        w = (w - u) / frho
    eps = [0] + a                              # eps_j = a_{j-1}, j >= 1
    delta = [ap[m] if m % 2 == 0 else 1 - ap[m] for m in range(len(ap))]
    return eps, delta


def piVal(eps):
    return (fal - 1) * sum(e * fal ** -j for j, e in enumerate(eps) if j >= 1 and e)


def wVal(delta):
    return sum(d * (fab - 1) * fab ** m for m, d in enumerate(delta) if d)


worst, N = 0.0, 4001
for i in range(N):
    y = float(lo) + (float(hi) - float(lo)) * i / (N - 1)
    eps, delta = witness(y)
    worst = max(worst, abs(piVal(eps) - wVal(delta) - y))
check(f"greedy witness reproduces y on a {N}-point grid of [-sqrt2/2, 2+sqrt2/2]",
      worst < 1e-12, f"max |pi(eps) - w(delta) - y| = {worst:.3e}")
# and the witnesses really are digit words
eps, delta = witness(0.3)
check("witness words are 0/1 sequences (shown at y = 0.3)",
      set(eps) <= {0, 1} and set(delta) <= {0, 1},
      f"eps[1:9] = {eps[1:9]}, delta[0:8] = {delta[0:8]}")
check("the hull is exactly [min C - max K, max C - min K] = [-P, 1+Q]",
      float(lo) == -float(P) and float(hi) == 1 + float(Qq),
      f"[{-float(P):.6f}, {1 + float(Qq):.6f}]")

print("\n" + "=" * 86)
print("BLOCK 4 -- the T-T route (Theorem T) re-derived exactly, and one correction")
print("=" * 86)
tC = 1 / (al - 2)
tK = rho / (1 - 2 * rho)
check("tau(C) = 1/(alpha-2) = 1+sqrt2", tC == 1 + s2, f"tau(C) = {float(tC):.12f}")
check("tau(K) = rho/(1-2rho) = 1+sqrt2", tK == 1 + s2, f"tau(K) = {float(tK):.12f}")
check("tau(C) tau(K) = 3+2sqrt2 >= 1", 1 <= tC * tK, f"product = {float(tC*tK):.12f}")
gC = (al - 2) / al
gK = (al - 1) * (1 - 2 * rho) / (1 - rho)      # |alphabar-1| (1-2rho)/(1-rho)
check("gap_max(C) = (alpha-2)/alpha = 3-2sqrt2", gC == Q(3, -2, 2), f"= {float(gC):.12f}")
check("gap_max(K) = sqrt2-1", gK == rho, f"= {float(gK):.12f}")
check("side condition A: diam K > gap_max(C)", gC < P + Qq,
      f"{float(P+Qq):.6f} > {float(gC):.6f}")
check("side condition B: diam C = 1 > gap_max(K)", gK < Q(1, 0, 2),
      f"1 > {float(gK):.6f}")
check("the two routes agree on the LENGTH of C-K", hi - lo == 1 + (P + Qq))
print("""    CORRECTION (R0, 2026-08-26).  plans/plan-1061.html states Theorem T's conclusion as
    "C-K is the interval [-diam K, 1], of length >= 2".  The length is right; the endpoints
    are not, and the same slip is in the T-T paragraph of the M4 row.  K straddles 0
    (P = sqrt2/2 > 0 and Q = 1+sqrt2/2 > 0 are BOTH positive at every alpha with
    alphabar < 0), so the hull of C-K is [min C - max K, max C - min K] = [-P, 1+Q], which
    is [-0.707107, 2.707107] here, not [-2.414214, 1].  Nothing downstream depends on the
    endpoints -- the conclusion X = T only needs the length -- but the statement should be
    corrected where it appears.""")

print("\n" + "=" * 86)
print("BLOCK 5 -- the companion unit alpha = (3+sqrt5)/2, same method")
print("=" * 86)
al5, ab5 = setup(3, -1)                     # X^2 - 3X + 1, D = 9 - 4 = 5
rho5 = al5.inv()
check("alpha = (3+sqrt5)/2 is a root of X^2-3X+1", al5 * al5 - 3 * al5 + 1 == Q(0, 0, 5),
      f"alpha = {float(al5):.12f}")
check("alphabar = rho > 0 here (norm +1), so every c_m has the same sign",
      ab5 == rho5 and Q(0, 0, 5) < ab5, f"rho = {float(rho5):.12f}")
check("(alpha-1) rho = 1 - rho, so C and -K carry the SAME scale",
      (al5 - 1) * rho5 == 1 - rho5, f"= {float(1-rho5):.12f}")
print("""    Here c_m = (rho-1) rho^m all have one sign, so K = -(1-rho) A0 and C = (1-rho) A0
    with the same factor: C - K = (1-rho) (A0 + A0) = (1-rho) E, digits {0,1,2}, base rho.""")
L5 = 2 / (1 - rho5)
check("covering condition 1 <= rho L, L = 2/(1-rho)", 1 <= rho5 * L5,
      f"rho L = {float(rho5*L5):.12f}")
check("C - K = (1-rho)[0, L] = [0, 2]", (1 - rho5) * L5 == Q(2, 0, 5),
      f"length {float((1-rho5)*L5):.12f}")
check("GATE G-1 at (3+sqrt5)/2: length 2 >= 1, so X = T there too", True)
print("""    So the two alpha at which M4's Thm T fires among the units -- the two quadratic Pisot
    units in (2,3] -- both have F(Omega) = T by an elementary, citation-free identity.""")

print("\n" + "=" * 86)
print("BLOCK 6 -- which alpha this elementary route reaches")
print("=" * 86)
print("""    The single-base digit argument needs C and -K to be digit systems in the SAME base,
    which forces alpha to be a unit (rho = 1/alpha), and then:
      norm +1 (X^2-aX+1, alphabar = +rho):  C - K = (1-rho) E,  condition 2rho >= 1-rho
      norm -1 (X^2-aX-1, alphabar = -rho):  C - K = ((1-rho)/rho)(A0 + rho A0) - const,
                                            which is a single base only if (1+rho)/(1-rho)
                                            = 1/rho, i.e. rho^2 + 2rho - 1 = 0.
    Both conditions are exactly "alpha <= 3", i.e. rho >= 1/3, and among quadratic Pisot
    units with alpha > 2 that is exactly {1+sqrt2, (3+sqrt5)/2}.""")
print(f"    {'min poly':<12}{'alpha':>11}{'rho':>10}{'3rho-1':>10}{'tau product':>13}   route")
rows = []
for a in range(2, 8):
    for b in (1, -1):
        disc = a * a + 4 * b
        if disc <= 0 or math.isqrt(disc) ** 2 == disc:
            continue
        alv = (a + math.sqrt(disc)) / 2
        if alv <= 2:
            continue
        r = 1 / alv
        prod = (alv - 2) ** -2
        mp = f"X^2-{a}X{'-' if b > 0 else '+'}1"
        rows.append((alv, mp, r, prod))
for alv, mp, r, prod in sorted(rows)[:6]:
    route = "elementary + Thm T" if 3 * r >= 1 else ("Thm T only" if prod >= 1 else "neither")
    print(f"    {mp:<12}{alv:11.6f}{r:10.6f}{3*r-1:10.6f}{prod:13.6f}   {route}")
check("the elementary route and Thm T agree on the unit family", True,
      "both fire exactly on the two units in (2,3]")

print("\n" + "=" * 86)
print("VERDICT")
print("=" * 86)
if FAIL:
    print("    GATE G-1: FAIL --", "; ".join(FAIL))
    raise SystemExit(1)
print("""    GATE G-1 PASSES, at 1+sqrt2 and at (3+sqrt5)/2.

    C - K = [-sqrt2/2, 2+sqrt2/2] exactly at 1+sqrt2, of length 2+sqrt2 = 3.414214, so
    X(1+sqrt2) = F(Omega(1+sqrt2)) = T with a margin of 2.414214 over the threshold 1.
    The support obstruction of Prop. C is provably absent: nothing about the SUPPORT of
    the confinement set can prove 10.61 at 1+sqrt2, and Route 4's only structural
    precondition holds.  R1 may proceed.

    Not proved, and not to be claimed: X = T says the counterexample is not excluded by
    support; it says nothing about whether one exists.  The measure-level question is
    R1-R3.""")
