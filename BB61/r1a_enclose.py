#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R1a of `plan-BB61-counterexample.html`: rigorous enclosures of `Phi_h(nu)`.

R1b wants to certify `0 in interior conv{Phi(nu_1),...,Phi(nu_J)}` in `R^{2H}`, which is a
stable statement: it survives any perturbation of the vertices below the margin.  For that
to be a *proof* the `Phi(nu_j)` must be **enclosed**, not estimated.  This module supplies
the enclosures at `alpha = 1+sqrt2`.

    Phi_h(mu) = int e(h F) dmu,   F(omega) = (a-1) sum_{k>=1} omega_k a^-k - sum_{m>=0} c_m omega_-m

Three ingredients, and the whole point is that each is exactly accountable.

(1) TRUNCATION (M4 Prop. 3, in Fourier form).  With the window `F~` keeping `omega_-M..omega_J`,

        |F - F~| <= eps(J,M) := a^-J + |abar-1| rho^(M+1)/(1-rho)     pointwise, every omega,

    so |Phi_h(mu) - int e(h F~) dmu| <= 2 pi |h| eps(J,M) for EVERY invariant mu at once.
    `eps` falls geometrically in both arguments: at 1+sqrt2, (J,M) = (100,100) already gives
    2 pi h eps < 1e-35 at h <= 64.  Truncation is not the binding constraint here and never
    will be; M4 Prop. 3 was written for a transfer operator whose size forced (N,M) ~ 12.

(2) THE MEASURE.  A memory-L Markov measure is parametrised here by an exact rational
    **circulation** `p` on the order-L de Bruijn graph -- a probability vector on
    (L+1)-blocks with the flow conservation

        sum_x p(b x) = sum_y p(y b)   for every L-block b

    -- rather than by conditional probabilities `q`.  This is the finding of R1a and it is
    what makes the enclosure cheap:

        * conservation IS shift-invariance, so a circulation is a shift-invariant measure by
          construction, with **stationary block distribution `pi(b) = p(b0) + p(b1)` given
          exactly, as a rational number**, and `q(b) = p(b1)/pi(b)`;
        * parametrised by `q` instead, `pi` is the Perron eigenvector of a 2^L x 2^L matrix,
          and a rigorous enclosure of `Phi` would need a *verified eigenvector* -- the one
          expensive step in the whole lane, and the one place where `m7_price.BlockChain`'s
          "Phi_h computed exactly" is optimistic (`stationary()` is a numerical solve).

    Circulations are closed under rational convex combination and are produced here from
    (i) Bernoulli weights, (ii) the empirical (L+1)-block counts of a cyclic word -- which
    are a circulation for *any* word, no conditions -- and (iii) mixtures of those.

(3) THE FINITE SUM.  `int e(h F~) dmu` is one forward pass over `K = J+M+1` emissions,

        W_k[b] = (1-q[b]) W_{k+1}[(b<<1) & mask] + q[b] e(h gamma_k) W_{k+1}[((b<<1)|1) & mask],
        gamma_k = sqrt2 rho^k (k >= 1),   gamma_k = sqrt2 (-rho)^|k| (k <= 0),
        Phi~_h = sum_b pi[b] W_-M[b],

    started at `W_{J+1} = 1`.  Every `W_k` is a convex combination of unit-modulus numbers,
    so `|W_k| <= 1` at every stage: the recursion is unconditionally stable and there is no
    fixed point to verify.  Two engines evaluate it -- `mpmath.iv` (reference, exact
    outward rounding) and float64 with an a-priori rounding bound -- and the checks below
    confirm the interval engine's box contains the float value at every mode.

Gate for R1a: the enclosure radius must sit below the `1e-5` at which M7 sec 4's upper and
lower bounds cross, so that it is not the binding error in the LP of M7 Thm 5.

Usage:  python3 r1a_enclose.py            (from BB61/; needs mpmath, numpy)
"""
from fractions import Fraction as Fr
import math
import os
import sys
import time

import numpy as np
import mpmath as mp
from mpmath import iv

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

FAIL = []


def check(name, cond, extra=""):
    print(f"    [{'ok ' if cond else 'FAIL'}] {name}{('  ' + extra) if extra else ''}")
    if not cond:
        FAIL.append(name)


# ======================================================================================
# alpha = 1 + sqrt2 : the two ladders are the same geometric ladder up to sign
# ======================================================================================
IVDPS = 40
iv.dps = IVDPS
mp.mp.dps = IVDPS + 20

SQRT2 = iv.sqrt(iv.mpf(2))
ACOEF = (2, 1)                    # alpha^2 = A alpha + B; (2,1) is 1+sqrt2, the default
ALPHA = 1 + SQRT2
ABAR = 1 - SQRT2                  # the Galois conjugate, |abar| < 1
RHO = SQRT2 - 1                   # |abar|;  here also 1/alpha
C1 = SQRT2                        # |1 - abar|, the size of the leading past coefficient
# future: gamma_k = (a-1) a^-k  (k >= 1);  past: gamma_-m = -c_m = (1-abar) abar^m.
# At 1+sqrt2 both are the geometric ladder sqrt2 rho^|k| up to sign, which is why the
# original R1a run could write them that way; nothing below depends on that coincidence.


def set_alpha(A, B, name="?"):
    """Repoint the ladders at the quadratic unit `x^2 = A x + B` (`m0_engine.Alpha` order
    `[1, -A, -B]`).  Default `(2, 1)` = `1+sqrt2` leaves every R1a number unchanged."""
    global ACOEF, ALPHA, ABAR, RHO, C1, ANAME
    d = iv.sqrt(iv.mpf(A * A + 4 * B))
    ACOEF, ANAME = (A, B), name
    ALPHA = (iv.mpf(A) + d) / 2
    ABAR = (iv.mpf(A) - d) / 2
    RHO = abs(ABAR)
    C1 = abs(1 - ABAR)
    assert ALPHA.a > 2 and RHO.b < 1, "not a Pisot unit above 2"
    return ALPHA, ABAR


ANAME = '1+sqrt2'


def eps_trunc(J, M):
    """M4 Prop. 3: sup |F - F~| over the whole shift space, as an mpmath interval.

    a^-J is the exact future tail sum_{j>J} (a-1) a^-j; |1-abar| rho^(M+1)/(1-rho) is the
    exact past tail sum_{m>M} |c_m| at degree two, where c_m = (abar-1) abar^m."""
    fut = ALPHA ** (-J)
    past = C1 * RHO ** (M + 1) / (1 - RHO)
    return fut + past


def phi_radius_trunc(h, J, M):
    """|Phi_h - Phi~_h| <= 2 pi |h| eps(J,M), for every invariant measure."""
    return 2 * iv.pi * abs(h) * eps_trunc(J, M)


# ======================================================================================
# circulations on the order-L de Bruijn graph  ==  shift-invariant memory-L Markov measures
# ======================================================================================
class Circulation:
    """Exact rational circulation `p` on (L+1)-blocks.

    Encoding: an (L+1)-block (x_0,...,x_L) is the integer sum_i x_i 2^(L-i); its source
    L-block is `v >> 1` and its target L-block is `v & mask`.  Conservation reads
    `p[2b] + p[2b+1] == p[b] + p[b + 2^L]` for every L-block b."""

    __slots__ = ("L", "n", "mask", "p", "pi", "q", "name", "repair_cost")

    def __init__(self, L, p, name=""):
        self.L, self.n, self.mask = L, 1 << L, (1 << L) - 1
        self.p = [Fr(x) for x in p]
        self.name = name
        assert len(self.p) == 1 << (L + 1)
        assert sum(self.p) == 1, "not a probability vector"
        assert all(x >= 0 for x in self.p), "negative weight"
        self.pi = [self.p[2 * b] + self.p[2 * b + 1] for b in range(self.n)]
        # A block of zero stationary mass is never visited: supp(pi) is forward invariant
        # (pi(b') > 0 and P(b' -> b) > 0 force pi(b) > 0), and the branch of the recursion
        # that would reach it carries the exact weight 0.  So q is free there; take 1/2.
        self.q = [self.p[2 * b + 1] / self.pi[b] if self.pi[b] > 0 else Fr(1, 2)
                  for b in range(self.n)]

    def conservation_defect(self):
        """Exactly zero for a circulation."""
        return max(abs(self.pi[b] - (self.p[b] + self.p[b + self.n])) for b in range(self.n))

    def entropy(self):
        """h(mu) = -sum_b pi_b (q log q + (1-q) log(1-q)), as a float (not enclosed)."""
        s = 0.0
        for b in range(self.n):
            q = float(self.q[b])
            if 0.0 < q < 1.0:
                s -= float(self.pi[b]) * (q * math.log(q) + (1 - q) * math.log(1 - q))
        return s


def circ_bernoulli(L, p):
    """Bernoulli(p) as an order-L circulation; p rational."""
    p = Fr(p)
    out = []
    for v in range(1 << (L + 1)):
        w = Fr(1)
        for i in range(L + 1):
            w *= p if (v >> i) & 1 else (1 - p)
        out.append(w)
    return Circulation(L, out, name=f"Bern({p})")


def circ_from_word(L, word):
    """Empirical (L+1)-block distribution of the cyclic word `word` (a 0/1 sequence).

    A circulation for ANY word: the counts of (L+1)-blocks of a cyclic sequence conserve
    flow because every occurrence of an L-block is entered once and left once."""
    T = len(word)
    cnt = [0] * (1 << (L + 1))
    for i in range(T):
        v = 0
        for j in range(L + 1):
            v = (v << 1) | word[(i + j) % T]
        cnt[v] += 1
    return Circulation(L, [Fr(c, T) for c in cnt], name=f"word(T={T})")


def circ_from_weights(L, w, T=10 ** 9):
    """Round an approximate (L+1)-block weight vector to an EXACT circulation.

    `w` need not conserve flow -- it is typically `pi~[b] q~[b,x]` built from a numerically
    computed stationary vector, so its divergence is rounding noise.  Rounding `w` to
    integer multiples of `1/T` leaves a divergence `d(b)` bounded by 2 in absolute value;
    the repair routes `d(b)` units of flow from each node with `d < 0` to each node with
    `d > 0` along the canonical walk between them, which in a de Bruijn graph is the walk
    that shifts in the bits of the target and always has length exactly `L`.  Adding flow
    keeps every weight non-negative, so the result is a circulation with

        total added <= L * sum_{d>0} d  ~  L * 2^L  units out of T,

    i.e. a relative perturbation of about `L 2^L / T` -- 5e-5 at L = 12, T = 1e9, and
    freely reducible by raising T.  Deterministic: no sampling, no noise.
    """
    n, mask = 1 << L, (1 << L) - 1
    ne = 1 << (L + 1)
    tot = sum(w)
    cnt = [max(0, int(round(float(x) / float(tot) * T))) for x in w]
    d = [(cnt[2 * b] + cnt[2 * b + 1]) - (cnt[b] + cnt[b + n]) for b in range(n)]
    # `w` must already be a near-circulation (it is, when built as `pi~ q~` from a
    # stationary `pi~`): the divergence is then rounding noise, |d(b)| <= 2.  Refuse a
    # genuinely non-conservative input rather than routing O(T) units of flow for it.
    excess = sum(x for x in d if x > 0)
    assert excess <= 4 * n, (
        f"circ_from_weights: input is not a near-circulation (excess flow {excess} "
        f"> 4*2^L = {4 * n}); is `w` built from a stationary vector?")
    src, snk = [], []
    for b in range(n):
        if d[b] < 0:
            src += [b] * (-d[b])
        elif d[b] > 0:
            snk += [b] * d[b]
    assert len(src) == len(snk), "divergence does not sum to zero"
    added = 0
    for s, t in zip(src, snk):
        cur = s
        for i in range(L):
            bit = (t >> (L - 1 - i)) & 1
            cnt[2 * cur + bit] += 1
            added += 1
            cur = ((cur << 1) | bit) & mask
        assert cur == t
    S = sum(cnt)
    c = Circulation(L, [Fr(x, S) for x in cnt], name=f"repaired(T={T})")
    c.repair_cost = added / S
    return c


def circ_mix(parts):
    """Rational convex combination of circulations (a circulation again)."""
    L = parts[0][1].L
    tot = sum(Fr(w) for w, _ in parts)
    out = [Fr(0)] * (1 << (L + 1))
    for w, c in parts:
        assert c.L == L
        w = Fr(w) / tot
        for v in range(1 << (L + 1)):
            out[v] += w * c.p[v]
    return Circulation(L, out, name="mix(" + ",".join(c.name for _, c in parts) + ")")


# ======================================================================================
# the forward pass, twice: mpmath.iv (reference) and float64 (workhorse)
# ======================================================================================
def _steps(J, M):
    """The emission schedule, outermost first: list of (k, gamma_k) for k = J..-M.

    `F = (a-1) sum_{k>=1} w_k a^-k - sum_{m>=0} c_m w_-m` with `c_m = (abar-1) abar^m`, so
    the past enters with coefficient `-c_m = (1-abar) abar^m` -- signs included."""
    out = [(k, (ALPHA - 1) * ALPHA ** (-k)) for k in range(J, 0, -1)]
    out += [(-m, (1 - ABAR) * ABAR ** m) for m in range(0, M + 1)]
    return out


def _targets(L):
    n, mask = 1 << L, (1 << L) - 1
    b = np.arange(n, dtype=np.int64)
    return ((b << 1) & mask), (((b << 1) | 1) & mask)


def phi_iv(circ, hs, J, M):
    """Enclosure of Phi_h(mu_circ) for h in hs, as mpmath.iv complex boxes.

    Truncation is added at the end, so the returned box contains the TRUE Phi_h."""
    L, n = circ.L, circ.n
    t0, t1 = _targets(L)
    q1 = [iv.mpf(circ.q[b].numerator) / iv.mpf(circ.q[b].denominator) for b in range(n)]
    q0 = [1 - x for x in q1]
    pi = [iv.mpf(circ.pi[b].numerator) / iv.mpf(circ.pi[b].denominator) for b in range(n)]
    sched = _steps(J, M)
    out = []
    for h in hs:
        W = [iv.mpc(1, 0)] * n
        for _, g in sched:
            th = 2 * iv.pi * h * g
            e1 = iv.mpc(iv.cos(th), iv.sin(th))
            W = [q0[b] * W[t0[b]] + q1[b] * (e1 * W[t1[b]]) for b in range(n)]
        s = iv.mpc(0, 0)
        for b in range(n):
            s += pi[b] * W[b]
        r = phi_radius_trunc(h, J, M)
        out.append(iv.mpc(s.real + iv.mpf([-1, 1]) * r, s.imag + iv.mpf([-1, 1]) * r))
    return out


def _gamma_mp(J, M):
    """The same schedule as `_steps`, in ordinary mpmath at working precision."""
    A, B = ACOEF
    d = mp.sqrt(mp.mpf(A * A + 4 * B))
    a, ab = (mp.mpf(A) + d) / 2, (mp.mpf(A) - d) / 2
    out = [(a - 1) * a ** (-k) for k in range(J, 0, -1)]
    out += [(1 - ab) * ab ** m for m in range(0, M + 1)]
    return out


def _const_table(hs, J, M):
    """e(h gamma_k) at 60 digits, rounded to complex128: componentwise error <= 2^-53."""
    old = mp.mp.dps
    mp.mp.dps = 60
    gam = _gamma_mp(J, M)
    tab = np.empty((len(hs), len(gam)), dtype=complex)
    for i, h in enumerate(hs):
        for j, g in enumerate(gam):
            th = 2 * mp.pi * h * g
            tab[i, j] = complex(mp.cos(th), mp.sin(th))
    mp.mp.dps = old
    return tab


def phi_fl(circ, hs, J, M):
    """float64 forward pass; returns (values, rigorous radius) with the same guarantee."""
    L, n = circ.L, circ.n
    t0, t1 = _targets(L)
    q1 = np.array([float(x) for x in circ.q])
    q0 = 1.0 - q1
    pi = np.array([float(x) for x in circ.pi])
    sched = _steps(J, M)
    tab = _const_table(hs, J, M)
    W = np.ones((len(hs), n), dtype=complex)
    for j in range(len(sched)):
        W = q0[None, :] * W[:, t0] + (q1 * 1.0)[None, :] * (tab[:, j][:, None] * W[:, t1])
    # the outer sum is done with math.fsum, which is correctly rounded, so it contributes
    # one rounding (u) rather than a summation-order-dependent (n-1)u
    P = pi[None, :] * W
    vals = np.array([complex(math.fsum(row.real), math.fsum(row.imag)) for row in P])
    K = len(sched)
    u = 2.0 ** -53
    # Per emission the computed W' = fl(q0 W[t0] + q1 (e1 W[t1])) picks up, on top of the
    # incoming error: the constant's own error eta = 2^-52 (cos/sin evaluated at 60 digits
    # and rounded); |q^ - q| <= u twice, against factors of modulus <= 1; and the roundings
    # of one complex product (sqrt5 u), two real-by-complex products (sqrt2 u each) and one
    # complex sum (sqrt2 u) -- together below 9u, since every intermediate has modulus <= 1.
    # The amplification (q0+q1) <= 1+u contributes O(K^2 u^2), which is below 1e-25 here.
    rad_fl = K * (2.0 ** -52 + 9 * u) + 3 * u + n * u * 0
    rads = [float(iv.mpf(phi_radius_trunc(h, J, M)).b) + rad_fl for h in hs]
    return vals, rads


def phi_bernoulli_iv(p, hs, J, M):
    """Erdos product (M5 Thm 2) for Bernoulli(p) -- an independent formula, no chain."""
    p = iv.mpf(Fr(p).numerator) / iv.mpf(Fr(p).denominator)
    out = []
    for h in hs:
        z = iv.mpc(1, 0)
        for _, g in _steps(J, M):
            th = 2 * iv.pi * h * g
            z *= (1 - p) + p * iv.mpc(iv.cos(th), iv.sin(th))
        r = phi_radius_trunc(h, J, M)
        out.append(iv.mpc(z.real + iv.mpf([-1, 1]) * r, z.imag + iv.mpf([-1, 1]) * r))
    return out


def box_mid(box):
    return complex(float(box.real.mid.a), float(box.imag.mid.a))


def box_radius(box):
    """A radius that, with `box_mid`, gives a disc containing the box."""
    return math.hypot(float(box.real.delta.b), float(box.imag.delta.b)) / 2


def covers(val, rad, box):
    """Does the float engine's disc `|z - val| <= rad` contain the interval box?"""
    return abs(val - box_mid(box)) + box_radius(box) <= rad


# ======================================================================================
# checks
# ======================================================================================
def _mid(x):
    return float(iv.mpf(x).mid.a)


def main():
    import random
    print(__doc__.split("Usage:")[0].rstrip())

    print("\n" + "=" * 86)
    print("BLOCK 1 -- the ladder at alpha = 1+sqrt2, and the truncation radius (M4 Prop. 3)")
    print("=" * 86)
    check("alpha = 1+sqrt2 encloses to 1e-38",
          float(ALPHA.delta.b) < 1e-38, f"alpha = {_mid(ALPHA):.15f}")
    check("rho = sqrt2-1 = 1/alpha", float((RHO - 1 / ALPHA).delta.b) < 1e-38
          and abs(_mid(RHO - 1 / ALPHA)) < 1e-38, f"rho = {_mid(RHO):.15f}")
    tot = sum(SQRT2 * RHO ** k for k in range(1, 200))
    tot += sum(SQRT2 * RHO ** m * (1 if m % 2 == 0 else -1) for m in range(0, 200))
    check("sum_k gamma_k = 2 exactly -- so Phi_h(Bern(1/2)) is REAL at this alpha",
          abs(_mid(tot) - 2) < 1e-30, f"sum = {_mid(tot):.20f}")
    print(f"\n    {'(J,M)':>10}{'eps(J,M)':>16}{'2 pi h eps, h=64':>22}")
    for J in (20, 40, 60, 100):
        e = eps_trunc(J, J)
        print(f"    {('(%d,%d)' % (J, J)):>10}{_mid(e):16.3e}{_mid(2 * iv.pi * 64 * e):22.3e}")
    check("at (J,M) = (60,60) the truncation radius at h = 64 is below 1e-19",
          _mid(phi_radius_trunc(64, 60, 60)) < 1e-19,
          f"{_mid(phi_radius_trunc(64, 60, 60)):.3e}")

    print("\n" + "=" * 86)
    print("BLOCK 2 -- circulations: conservation is exact, so pi is exact")
    print("=" * 86)
    random.seed(11)
    word = [1 if random.random() < 0.6 else 0 for _ in range(20000)]
    cB = circ_bernoulli(6, "1/3")
    cW = circ_from_word(6, word)
    cM = circ_mix([("9/10", cW), ("1/10", circ_bernoulli(6, "1/2"))])
    for c in (cB, cW, cM):
        check(f"conservation defect exactly 0: {c.name}", c.conservation_defect() == 0,
              f"sum p = {sum(c.p)}, h(mu) = {c.entropy():.6f}")
    check("mixing with uniform makes every block positive",
          all(x > 0 for x in cM.pi), f"{sum(1 for x in cW.pi if x == 0)} empty blocks before")
    check("pi and q are exact rationals",
          isinstance(cM.pi[0], Fr) and isinstance(cM.q[0], Fr),
          f"denominator of pi[0] has {len(str(cM.pi[0].denominator))} digits")

    print("\n" + "=" * 86)
    print("BLOCK 3 -- two independent formulas for Bernoulli: the chain and Erdos' product")
    print("=" * 86)
    hs = [1, 2, 3, 8, 16]
    worst = 0.0
    for ps in ("1/3", "1/2", "2/5", "7/10"):
        A = phi_iv(circ_bernoulli(3, ps), hs, 60, 60)
        B = phi_bernoulli_iv(ps, hs, 60, 60)
        for a, b in zip(A, B):
            worst = max(worst, abs(box_mid(a) - box_mid(b)))
    check("chain recursion == Erdos product (M5 Thm 2) at 4 values of p, 5 modes",
          worst < 1e-25, f"max |difference of enclosures| = {worst:.3e}")

    print("\n" + "=" * 86)
    print("BLOCK 4 -- the float engine, and its a-priori rounding bound")
    print("=" * 86)
    hs = list(range(1, 17))
    A = phi_iv(cM, hs, 60, 60)
    V, rad = phi_fl(cM, hs, 60, 60)
    obs = max(abs(V[i] - box_mid(A[i])) for i in range(len(hs)))
    check("the float disc contains the interval box at every mode",
          all(covers(V[i], rad[i], A[i]) for i in range(len(hs))))
    print(f"    interval radius {box_radius(A[-1]):.3e} | float radius {rad[-1]:.3e} "
          f"| observed float error {obs:.3e} ({rad[-1] / max(obs, 1e-300):.0f}x inside the bound)")

    print("\n" + "=" * 86)
    print("BLOCK 5 -- cross-validation against the M7 engine (m7_price.BlockChain)")
    print("=" * 86)
    try:
        from m0_engine import Alpha
        from m7_price import BlockChain
        al = Alpha([1, -2, -1])
        L = 6
        c6 = circ_mix([("7/10", circ_from_word(L, word)), ("3/10", circ_bernoulli(L, "1/2"))])
        hs = list(range(1, 9))
        bc = BlockChain(al, L, hmax=8)
        q = np.array([float(x) for x in c6.q])
        pin = bc.stationary(q)
        pie = np.array([float(x) for x in c6.pi])
        m7 = np.asarray(bc.phis(q, hs, pin))
        A = phi_iv(c6, hs, 60, 60)
        d = max(abs(m7[i] - box_mid(A[i])) for i in range(len(hs)))
        check("M7's two-ladder engine agrees with the enclosure at every mode",
              d < 1e-14, f"max difference {d:.3e} over h = 1..8")
        check("M7's numerical stationary vector is accurate here -- but it is not certified",
              float(np.abs(pie - pin).sum()) < 1e-12,
              f"||pi_exact - pi_numeric||_1 = {float(np.abs(pie - pin).sum()):.3e}")
    except Exception as exc:                                       # pragma: no cover
        check("M7 cross-validation", False, f"skipped: {exc!r}")

    print("\n" + "=" * 86)
    print("BLOCK 6 -- why circulations: the alternative needs pi, and pi resists certification")
    print("=" * 86)
    print("""    Parametrised by q, the stationary vector is a Perron eigenvector and a rigorous
    Phi needs ||pi - pi~||_1, which enters Phi linearly (|Phi~ - sum pi~ W| <= ||pi-pi~||_1
    since |W| <= 1).  The cheap route to that is the residual bound
    ||pi - pi~||_1 <= ||pi~ P^k - pi~||_1 / (1 - tau(P^k)) with the Dobrushin coefficient
    tau(P^k) <= 1 - sum_u min_b P^k(b,u).  Measured at L = 8:""")
    L = 8
    ks = [8, 16, 32, 64]
    per = [1, 1, 0, 1, 0, 0] * 3400
    w8 = [1 if random.random() < 0.6 else 0 for _ in range(20000)]
    rows = [("random word, uniform 1/20", circ_mix([("19/20", circ_from_word(L, w8)),
                                                    ("1/20", circ_bernoulli(L, "1/2"))])),
            ("random word, uniform 1e-5", circ_mix([(Fr(99999, 100000), circ_from_word(L, w8)),
                                                    (Fr(1, 100000), circ_bernoulli(L, "1/2"))])),
            ("periodic 110100, uniform 1/20", circ_mix([("19/20", circ_from_word(L, per)),
                                                        ("1/20", circ_bernoulli(L, "1/2"))])),
            ("periodic 110100, uniform 1/1000", circ_mix([(Fr(999, 1000), circ_from_word(L, per)),
                                                          (Fr(1, 1000), circ_bernoulli(L, "1/2"))]))]
    t0i, t1i = _targets(L)
    print(f"\n    {'chain':<34}{'h(mu)':>8}" + "".join(f"{'tau(P^%d)' % k:>13}" for k in ks))
    taus = {}
    for lbl, c in rows:
        q1 = np.array([float(x) for x in c.q])
        q0 = 1 - q1
        D = np.eye(c.n)
        t = {}
        for k in range(1, max(ks) + 1):
            Dn = np.zeros_like(D)
            np.add.at(Dn.T, t0i, (D * q0[None, :]).T)
            np.add.at(Dn.T, t1i, (D * q1[None, :]).T)
            D = Dn
            if k in ks:
                t[k] = 1.0 - D.min(axis=0).sum()
        taus[lbl] = t
        print(f"    {lbl:<34}{c.entropy():8.4f}" + "".join(f"{t[k]:13.3e}" for k in ks))
    check("the residual route works for a high-entropy chain", taus[rows[0][0]][32] < 1e-5,
          f"tau(P^32) = {taus[rows[0][0]][32]:.2e}, so the amplification is 1.000001")
    check("and COLLAPSES for a low-entropy one -- exactly the witnesses Route 4 may need",
          taus[rows[3][0]][64] > 0.99,
          f"tau(P^64) = {taus[rows[3][0]][64]:.4f}, amplification "
          f"{1 / (1 - taus[rows[3][0]][64]):.0f}x")
    print("""    A circulation needs none of this: conservation IS stationarity, so pi is read off
    the parameters as an exact rational.  Cost of certifying pi: zero, at every entropy.""")

    print("\n" + "=" * 86)
    print("BLOCK 7 -- cost at the sizes R1b needs")
    print("=" * 86)
    print(f"    {'L':>3}{'states':>8}{'H':>5}{'build (s)':>12}{'phi_fl (s)':>12}{'radius':>12}")
    for L in (8, 10, 12):
        wl = [1 if random.random() < 0.55 else 0 for _ in range(20000)]
        t = time.time()
        c = circ_mix([("9/10", circ_from_word(L, wl)), ("1/10", circ_bernoulli(L, "1/2"))])
        tb = time.time() - t
        for H in (8, 32):
            t = time.time()
            V, rad = phi_fl(c, list(range(1, H + 1)), 60, 60)
            tf = time.time() - t
            print(f"    {L:>3}{c.n:>8}{H:>5}{tb:>12.2f}{tf:>12.2f}{rad[-1]:>12.2e}")

    print("\n" + "=" * 86)
    print("VERDICT")
    print("=" * 86)
    if FAIL:
        print("    R1a: FAIL --", "; ".join(FAIL))
        return 1
    print("""    R1a's gate is met, and by a very large margin.

    The enclosure radius for Phi_h(nu) at alpha = 1+sqrt2 is

        1.5e-13  from the float64 engine with its a-priori rounding bound, and
        ~1e-21   from the mpmath interval engine at (J,M) = (60,60),

    against the 1e-5 at which M7 sec 4's upper and lower brackets cross.  Truncation --
    the term M4 Prop. 3 accounts for, and the only one that was ever in doubt -- is not
    the binding error and cannot become one: eps(J,M) falls by a factor 2.41 per unit of J
    and 2.41 per unit of M, so (100,100) already gives 1e-38 at a cost of 200 sparse steps.

    What the enclosure needed instead was an exact stationary vector, and that is a
    question about how the pool is PARAMETRISED, not about arithmetic.  Circulations give
    it for free at every entropy; conditional probabilities do not, and the cheap
    substitute (a Dobrushin residual bound) degrades to nothing exactly on the
    low-entropy measures the lane is most likely to want.

    Remaining for R1a: convert M7's own pool -- the memory-12 Gibbs columns -- into
    circulations without losing the geometry that makes it work, and record the enclosed
    Phi-vectors for R1b.""")
    return 0


if __name__ == "__main__":
    sys.exit(main())
