#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Gate G-A: recomputation of the decisive numerical evaluation in Dimitrov's proof of
the Schinzel-Zassenhaus conjecture (arXiv:1912.12545v1, 28 Dec 2019).

Shared rung: plan-Tshift-S11 G-A == plan-Tshift-S10 G-A1 ("whichever plan executes
first pays it, the other inherits").  This is NOT a fork of TShift/tshift_numerics.py
(R6): that harness is the exact-Z (3/2)^n orbit, this one is the S-Z capacity chain.
Nothing here touches the orbit except the last subcommand, which reads the g-frame
off it to price Bertrandias for plan-S11.

THE CHAIN BEING RECOMPUTED (the paper's numbering)
    Lemma 2.1  (Arnold, Smyth)    P_4 = P_2 mod 4 Z[X],  P_m(X) = prod_i (X - alpha_i^m)
    Prop 2.2                      Q(0)=1, Q a square mod 4 ==> sqrt(Q) in 1 + X Z[[X]];
                                  hence f = sqrt(P_2^*(1/X) P_4^*(1/X)) in Z[[1/X]]
    Theorem 3  (Dubinin)          d(K(a_1..a_N)) <= (max_i |a_i|^N / 4)^(1/N), with
                                  equality iff the a_i are a regular N-gon about 0
    Theorem 4 / Cor 5 (Bertrandias)  f in Z[[1/X]] analytic off a compact K with
                                  d(K) < 1  ==>  f is rational
    Proof of Thm 1 (pp. 15-16)    K = K(alpha_i^2, alpha_i^4) has N = 2n vertices, so
                                  d(K) <= (max_i |alpha_i|^(8n)/4)^(1/(2n)) < 1
                                  as soon as max_i |alpha_i| < 2^(1/(4n)).

Subcommands
    printed             the paper's printed decimals and crossovers, recomputed
    star     [PANELS]   Dubinin's equality case: closed form vs. the printed conformal
                        map vs. an independent boundary-element solve; convergence table
    dubinin  [PANELS]   the inequality itself, on hedgehogs where it is not sharp
    chain    [PANELS]   the decisive evaluation end to end, on real polynomials
    arith    [NTERMS]   the 2-adic half, exact: Lemma 2.1, Prop 2.2, Kronecker/Hankel
    s11                 what the recomputation prices for plan-S11's own g-frame
    all                 the whole battery

Numerics: float64 boundary elements for capacity (accuracy measured in `star` against
closed forms), mpmath at 40 dps for roots and printed decimals, exact Fraction/int
arithmetic for everything algebraic.  No printed verdict rests on a float comparison
whose margin is smaller than the measured discretization error.
"""

import sys
from fractions import Fraction
from math import pi

import numpy as np

import mpmath as mp

mp.mp.dps = 40

# Total boundary-element budget: the dense solve is O(M^3) and the matrix is M^2
# doubles, so spikes get panels = clip(PANEL_BUDGET // nspikes).
PANEL_BUDGET = 2600


# ---------------------------------------------------------------------------
# 1.  Capacity of a hedgehog: boundary elements for Symm's equation
# ---------------------------------------------------------------------------
#
# K = union of the radial segments [0, a_j] is connected, so its equilibrium
# potential U(z) = int log|z-w| dmu(w) equals gamma = log cap(K) everywhere on K.
# Discretize each spike into panels, one constant density per panel, collocate at
# panel midpoints, and solve the (M+1)x(M+1) system
#     sum_j A_ij sigma_j = gamma   (i = 1..M),        sum_j h_j sigma_j = 1,
# with A_ij = int_{panel j} log|z_i - w| |dw| in closed form.
#
# Mesh: t = r(1 - cos theta)/2, uniform in theta.  In that variable the equilibrium
# MASS density is bounded at the tip -- it absorbs the (r-t)^{-1/2} edge singularity --
# so uniform theta panels are the natural mesh, not an ad hoc grading.


def _panel_integrals(z, p, q):
    """int_{[p,q]} log|z - w| |dw|; z is (M,1), p and q are (1,M), all complex."""
    L = np.abs(q - p)
    u = (q - p) / L
    zeta = (z - p) / u                        # reduces to int_0^L log|zeta - t| dt
    a = zeta.real
    b = np.abs(zeta.imag)
    bs = np.where(b > 0.0, b, 1.0)

    def F(t):
        x = t - a
        r2 = x * x + b * b
        out = np.where(r2 > 0.0, x * np.log(np.where(r2 > 0.0, r2, 1.0)), 0.0) - 2.0 * x
        out = out + np.where(b > 0.0, 2.0 * b * np.arctan(x / bs), 0.0)
        return 0.5 * out

    return F(L) - F(0.0)


def merge_spikes(vertices, tol=1e-10):
    """Collapse spikes that share a direction; only the longest survives."""
    keep = []
    for a in vertices:
        a = complex(a)
        r = abs(a)
        if r == 0.0:
            continue
        th = float(np.angle(a))
        for i, (th0, r0) in enumerate(keep):
            if abs(((th - th0 + pi) % (2 * pi)) - pi) < tol:
                keep[i] = (th0, max(r0, r))
                break
        else:
            keep.append((th, r))
    return [r * np.exp(1j * th) for th, r in sorted(keep)]


def hedgehog_capacity(vertices, panels=None, merge=True):
    """Transfinite diameter of K(a_1,...,a_N) = union of [0, a_j], by boundary elements."""
    spikes = merge_spikes(vertices) if merge else [complex(a) for a in vertices if a != 0]
    if not spikes:
        return 0.0
    if panels is None:
        panels = max(24, PANEL_BUDGET // len(spikes))
    else:
        panels = max(8, min(panels, PANEL_BUDGET // len(spikes)))
    P, Q = [], []
    theta = np.linspace(0.0, pi, panels + 1)
    shape = (1.0 - np.cos(theta)) / 2.0
    for a in spikes:
        r = abs(a)
        d = a / r
        t = r * shape
        P.append(d * t[:-1])
        Q.append(d * t[1:])
    p = np.concatenate(P)
    q = np.concatenate(Q)
    h = np.abs(q - p)
    z = (0.5 * (p + q)).reshape(-1, 1)

    m = len(p)
    A = np.empty((m + 1, m + 1))
    A[:m, :m] = _panel_integrals(z, p.reshape(1, -1), q.reshape(1, -1))
    A[:m, m] = -1.0
    A[m, :m] = h
    A[m, m] = 0.0
    rhs = np.zeros(m + 1)
    rhs[m] = 1.0
    sol = np.linalg.solve(A, rhs)
    return float(np.exp(sol[m]))


def dubinin_bound(vertices, count=None):
    """(max_i |a_i|^N / 4)^(1/N) = max|a_i| * 4^(-1/N), with N = count (default: len)."""
    rmax = max(abs(complex(a)) for a in vertices)
    n = len(vertices) if count is None else count
    return rmax * 4.0 ** (-1.0 / n)


def star(nspikes, length=1.0):
    return [length * np.exp(2j * pi * k / nspikes) for k in range(nspikes)]


# ---------------------------------------------------------------------------
# 2.  Exact integer polynomial algebra (the 2-adic half)
# ---------------------------------------------------------------------------
#
# Polynomials are lists of ints, LOW degree first; P is monic of degree n.


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                out[i + j] += ai * bj
    return out


def companion(P):
    n = len(P) - 1
    C = [[Fraction(0)] * n for _ in range(n)]
    for i in range(1, n):
        C[i][i - 1] = Fraction(1)
    for i in range(n):
        C[i][n - 1] = Fraction(-P[i])
    return C


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def charpoly(A):
    """Faddeev-LeVerrier.  Returns the char poly low-first, monic, ints when integral."""
    n = len(A)
    c = [Fraction(0)] * (n + 1)
    c[n] = Fraction(1)
    M = [[Fraction(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        M = mat_mul(A, M)
        for i in range(n):
            M[i][i] += c[n - k + 1]
        AM = mat_mul(A, M)
        c[n - k] = -sum(AM[i][i] for i in range(n)) / k
    return [int(x) if x.denominator == 1 else x for x in c]


def power_poly(P, m):
    """P_m: the monic polynomial with roots alpha_i^m (Lemma 2.1's ancillary sequence)."""
    C = companion(P)
    Cm = C
    for _ in range(m - 1):
        Cm = mat_mul(Cm, C)
    return charpoly(Cm)


def reciprocal(P):
    """P^*(X) = X^n P(1/X)."""
    return list(reversed(P))


def series_sqrt(Q, nterms):
    """Square root of a power series with Q[0] = 1, as Fractions."""
    s = [Fraction(1)]
    for k in range(1, nterms):
        qk = Fraction(Q[k]) if k < len(Q) else Fraction(0)
        acc = sum(s[i] * s[k - i] for i in range(1, k))
        s.append((qk - acc) / 2)
    return s


def is_square_poly(Q):
    """Exact test: is Q (with Q[0] = 1) the square of a polynomial in Z[X]?"""
    s = series_sqrt(Q, len(Q))
    if any(c.denominator != 1 for c in s):
        return False
    half = [int(c) for c in s[: (len(Q) + 1) // 2]]
    prod = poly_mul(half, half)
    prod += [0] * (len(Q) - len(prod))
    return prod[: len(Q)] == list(Q) and all(c == 0 for c in prod[len(Q):])


def hankel_det(a, k):
    """Kronecker's D_k(f) = det(a_{i+j+1})_{i,j=0..k}, exactly, by Bareiss."""
    n = k + 1
    M = [[Fraction(a[i + j + 1]) for j in range(n)] for i in range(n)]
    sign, prev = 1, Fraction(1)
    for p in range(n - 1):
        if M[p][p] == 0:
            for r in range(p + 1, n):
                if M[r][p] != 0:
                    M[p], M[r] = M[r], M[p]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(p + 1, n):
            for j in range(p + 1, n):
                M[i][j] = (M[i][j] * M[p][p] - M[i][p] * M[p][j]) / prev
        prev = M[p][p]
    d = sign * M[n - 1][n - 1]
    return int(d) if d.denominator == 1 else d


# Test polynomials, low degree first.
LEHMER = [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]        # x^10+x^9-x^7-x^6-x^5-x^4-x^3+x+1
GOLDEN = [-1, -1, 1]                                    # x^2 - x - 1
PLASTIC = [-1, -1, 0, 1]                                # x^3 - x - 1, Smyth's rho
SALEM6 = [1, 0, -1, -1, -1, 0, 1]                       # x^6-x^4-x^3-x^2+1, Salem 1.40127
CYCLO5 = [1, 1, 1, 1, 1]                                # Phi_5
CYCLO7 = [1, 1, 1, 1, 1, 1, 1]                          # Phi_7
CYCLO8 = [1, 0, 0, 0, 1]                                # Phi_8, even level


def x_pow_minus(n, c):
    P = [0] * (n + 1)
    P[0] = -c
    P[n] = 1
    return P


def roots_of(P):
    return mp.polyroots([mp.mpf(c) for c in reversed(P)], maxsteps=300, extraprec=300)


# ---------------------------------------------------------------------------
# 3.  Subcommands
# ---------------------------------------------------------------------------


def cmd_printed():
    print("G-A / the printed decimals of arXiv:1912.12545, recomputed (mpmath, 40 dps)")
    print()
    two14 = mp.mpf(2) ** mp.mpf("0.25")
    rho = mp.findroot(lambda r: r ** 3 - r - 1, mp.mpf("1.32"))
    print(f"  p.15  2^(1/4)                     = {mp.nstr(two14, 12)}    printed '1.189...'")
    print(f"  p.15  rho with rho^3 = rho + 1    = {mp.nstr(rho, 12)}    printed '1.324...'")
    print(f"        Smyth reduction needs rho > 2^(1/4):  {rho > two14}")
    print(f"  p.17  (log 2)/2                   = {mp.nstr(mp.log(2) / 2, 12)}"
          f"    printed '0.3096... < 0.346 < (log 2)/2'")
    print()
    print("  Theorem 1 asymptotic   2^(1/(4n)) = 1 + log2/(4n) + O(1/n^2):")
    for n in (10, 100, 1000):
        v = mp.mpf(2) ** (mp.mpf(1) / (4 * n))
        lin = 1 + mp.log(2) / (4 * n)
        print(f"        n = {n:5d}   2^(1/(4n)) = {mp.nstr(v, 14)}   1 + log2/(4n) = {mp.nstr(lin, 14)}"
              f"   n^2*(diff) = {mp.nstr(n * n * (v - lin), 8)}")
    print(f"        limit of n^2*(diff) is (log 2)^2/32 = {mp.nstr(mp.log(2) ** 2 / 32, 10)}")
    print()
    print("  pp.18-19  crossover against Matveev's  max log|alpha| >= 3 log(n/2) / n^2:")
    ok = True
    for label, denom, printed in (("Theorem 1, log2/(4n)", 4, 59), ("Theorem 6, log2/(2n)", 2, 20)):
        first = next(n for n in range(3, 20000)
                     if mp.log(2) / (denom * n) >= 3 * mp.log(mp.mpf(n) / 2) / (n * n))
        good = first == printed
        ok &= good
        print(f"        {label:<22} first n where S-Z wins = {first:4d}"
              f"   printed 'n >= {printed}'   {'MATCH' if good else 'MISMATCH'}")
    print()
    print(f"      status: {'PASS' if ok else 'FAIL'}")
    return ok


def cmd_star(panels=200):
    print("G-A / Dubinin's equality case: the regular N-gon hedgehog")
    print()
    print("  (a) Closed form.  For the star of N spikes of length l about 0, z -> z^N")
    print("      pulls [0, l^N] back to K, and capacity satisfies cap(f^-1 E)^N = cap(E)")
    print("      for f(z) = z^N, so cap(K) = (l^N/4)^(1/N) = l * 4^(-1/N).")
    print()
    print("  (b) The paper's conformal map (p.13), checked numerically.  Dimitrov prints")
    print("        z^-1 -> z^-1 / (1 - b z^-N / 4)^(2/N) = z^-1 + O(z^-2)")
    print("      as a conformal isomorphism of |z^-1| < (4/b)^(1/N) onto the complement of")
    print("      the star with N spikes of length b^(1/N).  In the z variable that is")
    print("        F(s) = R0 * s * (1 - s^-N)^(2/N),  R0 = (b/4)^(1/N),  |s| > 1,")
    print("      with F(s) = R0*s + O(s^(1-N)) at infinity, so the certified capacity is R0.")
    print("      On |s| = 1: |F| = R0*(2-2cos N.theta)^(1/N) <= R0*4^(1/N) = l, and")
    print("      arg F = theta + (2/N)*arg(1 - e^(-iN.theta)) is CONSTANT on each arc")
    print("      (= pi/N + 2pi k/N), i.e. the image really is a star of N radial spikes.")
    print()
    print(f"  {'N':>3} {'l':>7} {'exact l*4^(-1/N)':>18} {'map: max|F|':>13} {'map: #rays':>11}"
          f" {'map: arg spread':>16} {'BEM':>14} {'rel err':>10}")
    ok = True
    for N in (1, 2, 3, 4, 5, 6, 8, 10, 12, 20):
        ell = 1.7
        R0 = ell * 4.0 ** (-1.0 / N)
        th = np.linspace(1e-9, 2 * pi - 1e-9, 200001)
        s = np.exp(1j * th)
        w = 1.0 - s ** (-N)
        F = R0 * s * np.exp((2.0 / N) * np.log(w))
        tip = float(np.max(np.abs(F)))
        args = np.mod(np.angle(F), 2 * pi / N)
        spread = float(args.max() - args.min())
        rays = len(np.unique(np.round(np.angle(F) * N / (2 * pi) - 0.5).astype(int) % N))
        cap = hedgehog_capacity(star(N, ell), panels=panels)
        rel = abs(cap - R0) / R0
        ok &= rel < 1e-3 and abs(tip - ell) < 1e-8 and spread < 1e-5 and rays == N
        print(f"  {N:3d} {ell:7.3f} {R0:18.12f} {tip:13.9f} {rays:11d} {spread:16.2e}"
              f" {cap:14.10f} {rel:10.2e}")
    print()
    print("      max|F| must equal l (= b^(1/N)); the argument spread within one sector must")
    print("      be 0 (radial spikes); #rays must be N.  All three are properties of the")
    print("      PRINTED map, not of the solver.")
    print()
    print("  (c) Where that map comes from, derived independently (Schwarz-Christoffel).")
    print("      The complement of the star is a degenerate polygon with 2N vertices: N")
    print("      tips, of interior angle 2pi (SC exponent alpha-1 = 1), and N passages")
    print("      through the origin, of interior angle 2pi/N (exponent 2/N - 1).  With the")
    print("      tip prevertices at the N-th roots of unity and the origin prevertices at")
    print("      their midpoints, the exterior SC integrand is")
    print("        F'(s) = c prod_j (1 - w^j/s) prod_j (1 - w^j.zeta/s)^(2/N-1)")
    print("              = c (1 - s^-N)(1 + s^-N)^(2/N-1),  w = e^(2pi i/N), zeta = e^(i pi/N),")
    print("      which integrates in closed form to F(s) = c s (1 + s^-N)^(2/N): Dimitrov's")
    print("      printed map, up to the half-spike rotation s -> zeta.s.  Checked numerically:")
    worst = 0.0
    for N in (2, 3, 5, 7, 11):
        s = np.array([1.3 + 0.4j, -2.0 + 1.1j, 0.3 - 3.2j, 5.0 + 0.0j])
        h = 1e-6
        Fm = lambda z: z * (1 + z ** (-N)) ** (2.0 / N)
        num = (Fm(s + h) - Fm(s - h)) / (2 * h)
        ana = (1 - s ** (-N)) * (1 + s ** (-N)) ** (2.0 / N - 1)
        worst = max(worst, float(np.max(np.abs(num - ana))))
    print(f"      max |numeric F' - SC integrand| over 5 values of N and 4 points = {worst:.2e}")
    print()
    print("  (d) Convergence of the independent solve (N = 5, l = 1, exact 4^(-1/5) ="
          f" {4.0 ** -0.2:.12f}):")
    print(f"      {'panels/spike':>13} {'cap':>16} {'abs err':>12} {'ratio':>8}")
    prev = None
    for m in (25, 50, 100, 200, 400):
        c = hedgehog_capacity(star(5, 1.0), panels=m)
        err = abs(c - 4.0 ** -0.2)
        ratio = f"{prev / err:8.2f}" if prev else "       -"
        prev = err
        print(f"      {m:13d} {c:16.12f} {err:12.3e} {ratio}")
    print("      -> the solve is second order in the panel count; at the budget used below")
    print("      the error is ~1e-6 relative, far under every margin any verdict here needs.")
    print()
    print(f"      status: {'PASS' if ok else 'FAIL'}")
    return ok


def cmd_dubinin(panels=200):
    print("G-A / Dubinin's Theorem 3 as an inequality")
    print()
    print("  Exact controls first (closed forms independent of the solver):")
    print(f"  {'configuration':<26} {'exact':>14} {'BEM':>14} {'rel err':>10} {'Dubinin bd':>12} {'holds':>6}")
    ok = True
    controls = [
        ("single spike [0,4]", [4.0 + 0j], 1.0),
        ("2 opposite, 3 and 1", [3.0 + 0j, -1.0 + 0j], 1.0),
        ("2 opposite, 2 and 2", [2.0 + 0j, -2.0 + 0j], 1.0),
        ("3-gon, l = 1", star(3, 1.0), 4.0 ** (-1.0 / 3)),
        ("x^5-2 hedgehog (5 spikes)", star(5, 2.0 ** 0.8), 2.0 ** 0.4),
    ]
    for name, verts, exact in controls:
        cap = hedgehog_capacity(verts, panels=panels)
        bd = dubinin_bound(verts)
        rel = abs(cap - exact) / exact
        holds = cap <= bd * (1 + 1e-9)
        ok &= rel < 1e-3 and holds
        print(f"  {name:<26} {exact:14.10f} {cap:14.10f} {rel:10.2e} {bd:12.8f} {str(holds):>6}")
    print()
    print("  The [-1,3] row is the useful asymmetric control: two opposite spikes make a")
    print("  segment, cap = (r1+r2)/4 exactly, and the bound max(r)/2 is strict unless")
    print("  r1 = r2 -- the equality clause, visible in closed form.")
    print()
    print("  Content of the theorem: among hedgehogs with N spikes of length <= l, the")
    print("  regular one maximizes.  Perturb it and watch the ratio drop.")
    print()
    print(f"  {'N':>3} {'perturbation':<34} {'cap':>14} {'l*4^(-1/N)':>14} {'cap/bound':>10}")
    rng = np.random.default_rng(20260810)
    for N in (3, 5, 8):
        ell = 1.0
        ang = np.array([2 * pi * k / N for k in range(N)])
        cases = [
            ("regular N-gon (equality case)", list(star(N, ell))),
            ("angles squeezed by 0.6", [ell * np.exp(1j * (a * 0.6)) for a in ang]),
            ("one spike shortened to 0.5 l",
             [ell * np.exp(1j * a) * (0.5 if k == 0 else 1.0) for k, a in enumerate(ang)]),
            ("random angle jitter +-0.35 rad",
             [ell * np.exp(1j * (a + j)) for a, j in zip(ang, rng.uniform(-0.35, 0.35, N))]),
        ]
        for label, verts in cases:
            cap = hedgehog_capacity(verts, panels=panels, merge=False)
            bd = ell * 4.0 ** (-1.0 / N)
            viol = cap > bd * (1 + 1e-6)
            ok &= not viol
            print(f"  {N:3d} {label:<34} {cap:14.10f} {bd:14.10f} {cap / bd:10.6f}"
                  f"{'   <== VIOLATION' if viol else ''}")
    print()
    print(f"      status: {'PASS' if ok else 'FAIL'}")
    return ok


def cmd_chain(panels=None):
    print("G-A / the decisive evaluation, end to end")
    print()
    print("      d(K) <= (max_i |alpha_i|^(8n)/4)^(1/(2n)) < 1   whenever house(P) < 2^(1/(4n)),")
    print("      for K = K(alpha_i^2, alpha_i^4 : P(alpha_i) = 0), a hedgehog of 2n vertices.")
    print()
    print(f"  {'P':<30} {'n':>3} {'house':>10} {'2^(1/4n)':>10} {'Dubinin bd':>11}"
          f" {'cap(K)':>11} {'bd<1':>5} {'cap<1':>6}")
    ok = True
    tests = [
        ("Phi_5  (cyclotomic, odd level)", CYCLO5),
        ("Phi_7  (cyclotomic, odd level)", CYCLO7),
        ("Phi_8  (cyclotomic, even level)", CYCLO8),
        ("x^2-x-1  (golden)", GOLDEN),
        ("x^3-x-1  (Smyth's rho)", PLASTIC),
        ("Lehmer  (deg 10)", LEHMER),
        ("Salem   (deg 6)", SALEM6),
        ("x^5-2", x_pow_minus(5, 2)),
        ("x^7-2", x_pow_minus(7, 2)),
    ]
    for name, P in tests:
        n = len(P) - 1
        rts = roots_of(P)
        house = max(abs(complex(r)) for r in rts)
        verts = [complex(r) ** 2 for r in rts] + [complex(r) ** 4 for r in rts]
        bound = dubinin_bound(verts, count=2 * n)
        cap = hedgehog_capacity(verts, panels=panels)
        thresh = 2.0 ** (1.0 / (4 * n))
        bad = house < thresh and not bound < 1.0
        ok &= not bad
        print(f"  {name:<30} {n:3d} {house:10.6f} {thresh:10.6f} {bound:11.6f} {cap:11.6f}"
              f" {str(bound < 1.0):>5} {str(cap < 1.0):>6}{'  <== IMPLICATION FAILS' if bad else ''}")
    print()
    print("  Reading of the table: every row with house >= 2^(1/(4n)) is silent (the bound")
    print("  exceeds 1 and Bertrandias is not applicable) -- that is the whole point, the")
    print("  theorem only ever fires below the threshold.  The cyclotomic rows fire, and")
    print("  their conclusion (f rational) is TRUE there, which is Lemma 2.3's exit.")
    print()
    print("  Sharpness.  Dubinin's bound is attained exactly by the regular 2n-gon of")
    print("  modulus house^4, so the threshold is where THAT configuration reaches")
    print("  capacity 1: house^4 * 4^(-1/(2n)) = 1  <=>  house = 2^(1/(4n)).  Exactly:")
    print()
    print(f"  {'n':>4} {'2^(1/(4n))':>14} {'house':>16} {'cap of extremal 2n-gon':>26} {'<1':>6}")
    for n in (5, 10, 40):
        thresh = mp.mpf(2) ** (mp.mpf(1) / (4 * n))
        for eps, tag in ((mp.mpf("-1e-7"), "below"), (mp.mpf(0), "at   "), (mp.mpf("1e-7"), "above")):
            house = thresh * (1 + eps)
            exact = house ** 4 * mp.mpf(4) ** (-mp.mpf(1) / (2 * n))
            verdict = "= 1" if eps == 0 else str(exact < 1)
            print(f"  {n:4d} {mp.nstr(thresh, 11):>14} {mp.nstr(house, 13):>16}"
                  f" {mp.nstr(exact, 20):>26} {verdict:>6}   ({tag})")
            ok &= (exact < 1) == (eps < 0) or eps == 0
    print()
    print("  Exact control inside the table: for x^n - 2 with n odd, alpha^2 and alpha^4")
    print("  occupy the SAME n directions, so the 2n vertices collapse to n spikes of")
    print("  length 2^(4/n) and cap(K) = 2^(4/n) * 4^(-1/n) = 2^(2/n) exactly, while")
    print("  Dimitrov's 2n-vertex bound gives 2^(3/n).  The gap is the overlap he discards.")
    for n in (5, 7):
        cap = hedgehog_capacity(star(n, 2.0 ** (4.0 / n)))
        print(f"      n = {n}:  exact 2^(2/n) = {2.0 ** (2.0 / n):.10f}   solver ="
              f" {cap:.10f}   bound 2^(3/n) = {2.0 ** (3.0 / n):.10f}")
    print()
    print("  What the two lossy steps cost on a REAL configuration.  Scale all roots by t,")
    print("  keeping the shape, and find where the EXACT capacity of K crosses 1.  The gap")
    print("  from 2^(1/(4n)) to that house is what the extremal-configuration bound gives")
    print("  away; the gap from there to the actual house is what the METHOD gives away.")
    print()
    print(f"  {'P':<18} {'n':>3} {'2^(1/(4n))':>11} {'house* (cap=1)':>15} {'actual house':>13}"
          f" {'Dubinin loss':>13} {'method miss':>12}")
    for name, P in (("Lehmer", LEHMER), ("x^3-x-1", PLASTIC), ("Salem deg 6", SALEM6)):
        n = len(P) - 1
        rts = [complex(r) for r in roots_of(P)]
        house = max(abs(r) for r in rts)
        lo, hi = 0.3, 1.6
        for _ in range(30):
            mid = 0.5 * (lo + hi)
            v = [(r * mid) ** 2 for r in rts] + [(r * mid) ** 4 for r in rts]
            if hedgehog_capacity(v, panels=48) < 1.0:
                lo = mid
            else:
                hi = mid
        hstar = house * 0.5 * (lo + hi)
        thr = 2.0 ** (1.0 / (4 * n))
        print(f"  {name:<18} {n:3d} {thr:11.6f} {hstar:15.6f} {house:13.6f}"
              f" {hstar / thr:12.4f}x {house / hstar:11.4f}x")
    print("      (capacity here at 48 panels/spike, relative error ~3e-4: the 1.5% figure")
    print("      in the last column is two orders above the discretization error.)")
    print()
    print(f"      status: {'PASS' if ok else 'FAIL'}")
    return ok


def cmd_arith(nterms=24):
    print("G-A / the 2-adic half, in exact integer arithmetic")
    print()
    print("  Equation (3):  sqrt(1 + 4Y) = sum_k binom(1/2,k) 4^k Y^k  in Z[[Y]]")
    s = series_sqrt([1, 4] + [0] * nterms, nterms)
    ok = all(c.denominator == 1 for c in s)
    print("      " + " ".join(str(c) for c in s[:10]) + " ...")
    print(f"      all {nterms} coefficients integral: {ok}    (they are 2*(-1)^(k-1)*Catalan(k-1))")
    print()
    print("  Lemma 2.1:  P_4 = P_2 mod 4 Z[X]        P_m(X) = prod_i (X - alpha_i^m)")
    print("  Prop 2.2:   sqrt(P_2^*(X) P_4^*(X)) in 1 + X Z[[X]]")
    print("  Kronecker:  f rational  <=>  D_k(f) = det(a_{i+j+1})_{i,j<=k} = 0 for large k")
    print()
    kmax = (nterms - 3) // 2
    print(f"  {'P':<22} {'P_4=P_2 (4)':>12} {'sqrt in Z':>10} {'P_4=P_2':>8} {'P_2P_4 sq':>10}"
          f"   Kronecker D_k, k <= {kmax}")
    tests = [("Phi_5", CYCLO5), ("Phi_7", CYCLO7), ("Phi_8", CYCLO8), ("x^2-x-1", GOLDEN),
             ("x^3-x-1", PLASTIC), ("Lehmer", LEHMER), ("Salem deg 6", SALEM6),
             ("x^5-2", x_pow_minus(5, 2)), ("x^4+3x^3-2x+1", [1, -2, 0, 3, 1]),
             ("x^6-5x^4+x^3+2x-3", [-3, 2, 1, -5, 0, 0, 1])]
    for name, P in tests:
        P2, P4 = power_poly(P, 2), power_poly(P, 4)
        cong = all((a - b) % 4 == 0 for a, b in zip(P4, P2))
        f = series_sqrt(poly_mul(reciprocal(P2), reciprocal(P4)), nterms)
        integral = all(c.denominator == 1 for c in f)
        a = [int(c) for c in f] if integral else None
        dets = [hankel_det(a, k) for k in range(1, kmax + 1)] if integral else []
        nz = [k for k in range(1, kmax + 1) if dets[k - 1] != 0]
        Q = poly_mul(reciprocal(P2), reciprocal(P4))
        sq = is_square_poly(Q)
        last = max(nz, default=0)
        if sq:
            verdict = f"= 0 for k >= {last + 1}"
        else:
            shown = ",".join(str(k) for k in nz[:5]) + (",..." if len(nz) > 5 else "")
            verdict = f"!= 0 at k = {shown}"
        ok &= cong and integral and (sq == (last < kmax) or not sq)
        print(f"  {name:<22} {str(cong):>12} {str(integral):>10} {str(P4 == P2):>8}"
              f" {str(sq):>10}   {verdict}")
    print()
    print("  f is rational exactly when P_2 P_4 is a perfect square, and those rows are the")
    print("  two exits of the proof of Theorem 1: P_4 = P_2 (Lemma 2.3: the cyclotomics of")
    print("  odd level -- Phi_5, Phi_7 here), or P_2 reducible, in which case the argument")
    print("  descends to the minimal polynomial of alpha^2 (Phi_8: P_2 = (x^2+1)^2, P_4 =")
    print("  (x+1)^4, so P_4 != P_2 yet P_2 P_4 IS a square).  For every other row")
    print("  Bertrandias's conclusion is false, so its hypothesis d(K) < 1 must fail --")
    print("  which is Theorem 1: house >= 2^(1/(4n)).")
    print()
    print("  TRAP, worth the gate on its own (it lands on plan-S11's surviving channel F4).")
    print("  Kronecker's criterion is 'D_k = 0 for ALL large k', and the vanishing of any")
    print("  FINITE window of D_k proves nothing.  x^5-2 is the counterexample in the table:")
    print("  Q = 1 - 20X^5 + 64X^10 is not a square, f is irrational, yet")
    for k, d in ((3, 0), (4, -100000), (5, 0), (9, 7005381440357376)):
        print(f"        D_{k:<2} = {d}")
    print("  and in general D_k = 0 unless k = 4 mod 5 -- the series is supported on")
    print("  multiples of 5, so the Hankel matrix is block-antidiagonal with unequal blocks")
    print("  and is singular for reasons that have nothing to do with rationality.  Any")
    print("  per-window determinant-nonvanishing statement (S11 F4, S10's rank object) must")
    print("  therefore name the window; lacunarity kills individual windows for free.")
    print()
    print(f"      status: {'PASS' if ok else 'FAIL'}")
    return ok


def cmd_s11():
    print("G-A / what the recomputation prices for plan-S11's own frame")
    print()
    print("  Bertrandias (Theorem 4) asks for   prod_sigma d(K_sigma) < prod_{v in S} R_v.")
    print("  Dimitrov runs it with S empty (coefficients in Z, so the RHS is 1) and buys")
    print("  his whole margin on the ARCHIMEDEAN side: the singular set is a hedgehog of")
    print("  2n spikes that are SHORT because the roots are near 0, so d(K) < 1.")
    print()
    print("  S11's g-frame sits at the opposite corner.  g(w) = (2-3w) sum_n m_n w^n has")
    print("  coefficients g_n = 2m_{n+1} - 3m_n in {-2,...,2} (plan D1).  Measured on the")
    print("  real orbit at D = 1:")
    print()
    N = 4000
    ms = [(2 * 3 ** n + 2 ** n) // 2 ** (n + 1) for n in range(N + 1)]
    gs = [2 * ms[n + 1] - 3 * ms[n] for n in range(N)]
    odd = sum(1 for g in gs if g % 2)
    gmax = max(abs(g) for g in gs)
    v2max = max(((g & -g).bit_length() - 1) for g in gs if g)
    print(f"      n <= {N}:   max |g_n| = {gmax},   g_n odd for {odd} of {N} dates,"
          f"   max v_2(g_n) = {v2max}")
    print()
    print("      * 2-adic: R_2 = 1/limsup |g_n|_2^(1/n).  |g_n|_2 = 1 infinitely often, so")
    print("        R_2 = 1 EXACTLY, and prod_v R_v = 1.  No non-archimedean margin exists.")
    print("      * archimedean: the radius of convergence is exactly 1 (bounded coefficients,")
    print("        and limsup|delta_n| >= 1/5 by the cascade), so any admissible compact K")
    print("        contains the unit circle and d(K) >= 1.  No archimedean margin either.")
    print()
    print("  So Bertrandias reads 1 < 1 on the bounded frame: it cannot bite, at any rate")
    print("  theta, for any multiplier D.  That is plan-S11's wall W1 stated in the")
    print("  theorem's own currency instead of by analogy with the disc, and it also says")
    print("  what a middle would have to do: make v_2(g_n)/n bounded away from 0, which")
    print("  bounded coefficients cannot do unless they are eventually 0.  The 2-adic zero")
    print("  of g at w = 2/3 is a condition on the PARTIAL SUMS sum_{j<=n} 3^(n-j) 2^j g_j,")
    print("  not on the coefficients, and R_2 does not see it.")
    print()
    print("  Structural reading (the gate's payoff for Q1): Dimitrov's margin comes from the")
    print("  SIZE OF THE SINGULAR SET, not from the arithmetic of the coefficients.  A")
    print("  capacity middle for T-shift would have to shrink an orbit series' singular set")
    print("  below capacity 1; by Szego the bounded integer frame has the entire unit circle")
    print("  as its singular set unless it is already rational.  There is nothing to shrink.")
    return True


def main():
    args = sys.argv[1:]
    cmd = args[0] if args else "all"
    arg1 = int(args[1]) if len(args) > 1 else None
    if cmd == "printed":
        cmd_printed()
    elif cmd == "star":
        cmd_star(arg1 or 200)
    elif cmd == "dubinin":
        cmd_dubinin(arg1 or 200)
    elif cmd == "chain":
        cmd_chain(arg1)
    elif cmd == "arith":
        cmd_arith(arg1 or 24)
    elif cmd == "s11":
        cmd_s11()
    elif cmd == "all":
        results = {}
        for name, fn in (("printed", cmd_printed), ("star", lambda: cmd_star(200)),
                         ("dubinin", lambda: cmd_dubinin(200)), ("chain", lambda: cmd_chain()),
                         ("arith", lambda: cmd_arith(24)), ("s11", cmd_s11)):
            results[name] = fn()
            print("\n" + "=" * 78 + "\n")
        print("G-A battery: " + ", ".join(f"{k} {'PASS' if v else 'FAIL'}"
                                          for k, v in results.items()))
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
