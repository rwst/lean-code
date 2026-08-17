#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
Gate G-A2: recomputation of the decisive printed inequalities of the Calegari-
Dimitrov-Tang arithmetic holonomy bounds (plan-Tshift-S10 WP-A, note-Tshift-S10-WPA).

Shared-rung bookkeeping: G-A1 (the capacity rung) was paid by plan-Tshift-S11 in
TShift/ga_hedgehog.py.  This file is the holonomy rung, and like that one it is a
GATE ARTIFACT, not a fork of TShift/tshift_numerics.py (R6 governs the exact-Z
(3/2)^n orbit harness; only the `s10` subcommand here touches the orbit, and it
recomputes what it needs from scratch in a few lines).

TARGETS (the papers' own numbering)
  [CDT-ICM]  Arithmetic holonomy bounds and effective Diophantine approximation,
             ICM 2026 proceedings (SIAM), arXiv:2510.04156v1.
             Thm 1.1 (Baker-Yu, the effective S-unit shape), Thm 2.1, Prop 2.4,
             Thm 2.6 (adelic quantitative master bound), Thm 5.1 (L(2,chi_-3)
             measure 24781), Thm 5.2 (2-adic zeta(5) measure 20), (5.1)-(5.8).
  [CDT-L]    The linear independence of 1, zeta(2), L(2,chi_-3), arXiv:2408.15403v2.
             Thm 2.5.1 = ICM Thm 2.1; Thm 8.0.1 (sharpest dimension bound);
             Ex 7.4.6/7.4.9, App A (the contour), (A.4.3), (A.5.1), (A.5.3).
  [CDT-U]    The unbounded denominators conjecture, JAMS 38 (2025) 627-702,
             arXiv:2109.09040v4.  Thm 2.0.1, Cor 2.0.5, (2.0.3), (2.0.7).

THE CHAIN BEING RECOMPUTED
  arithmetic side   denominator type  ->  tau(b) = m^-2 sum_i (2i-1) sigma_i   (exact rationals)
  archimedean side  conformal size    ->  log|phi'(0)|                        (exact rationals here)
                    growth            ->  Bost-Charles integral
                                          I(phi) = int int log|phi(z)-phi(w)| dmu dmu
                                          and its majorant, the rearrangement
                                          integral  J(phi) = int_0^1 2t (log|phi|)^* dt
  verdict           m <= I / (log|phi'(0)| + sum_p log R_p - tau)  <  m       (contradiction)
  quantitative      the same with  -(1-gamma)(2/kappa - (1-gamma)/kappa^2) log(1/rho)
                    in the denominator; solving for kappa is the printed measure.

Subcommands
    printed          the printed rationals and decimals, recomputed (exact where exact)
    zeta2   [N]      the 2-adic zeta(5) chain: (5.6)/(5.7)/(5.8) and the lune variant
    l2chi   [N]      the L(2,chi_-3) contour: (A.4.3), (A.5.1)-(A.5.3), ICM (5.1)
    s10              what the gate prices for T-shift (the two screens, the Baker wall)
    all              the whole battery

Numerics: exact Fraction/int for every printed rational; mpmath at 40 dps for the
printed decimals and for solving for kappa; float64 with an eta-reduction evaluation
of the Hauptmodul (validated against its q-series) for the two-dimensional integrals.
No verdict rests on a float margin smaller than the measured discretization error.
"""

import cmath
import math
import sys
from fractions import Fraction

import numpy as np

import mpmath as mp

mp.mp.dps = 40


# ---------------------------------------------------------------------------
# 0.  The printed rationals
# ---------------------------------------------------------------------------

# [CDT-L] (A.4.1): the contour parameters for the L(2,chi_-3) problem.
R_L = Fraction(77, 100)
C_L = Fraction(75, 10)
RS_L = [Fraction(91, 100), Fraction(6188, 10000),
        Fraction(55515, 100000), Fraction(772, 1000)]
THETAS_L = [Fraction(7977, 100000), Fraction(11543, 100000),
            Fraction(3525, 100000), Fraction(-783, 10000)]
SHRINK_L = Fraction(995, 1000)                      # [CDT-L] (A.4.2)

# [CDT-L] (A.4.3): the printed conformal radius |psi'(0)|.
PSI_PRIME_PRINTED = Fraction(5448339453535586608000000000,
                             8658833407565631122430056127)

# [CDT-L] (A.0.2): the denominators term for the 14-function configuration.
TAU_L = Fraction(16603, 3920)
# [CDT-L] Remark A.5.2: the 9-function configuration, tau(b') = 157/81.
TAU_L9 = Fraction(157, 81)

# [CDT-L] (A.5.1) / Ex 7.4.6 / (A.5.3), and [CDT-ICM] (5.1).
BC_L_PRINTED = mp.mpf("11.844")         # the Bost-Charles integral of the contour
RHO_INV_L = mp.mpf(11614)               # |rho^{-1}| bound, [CDT-ICM] section 5.1

# [CDT-ICM] section 5.2: the 2-adic zeta(5) data.
TAU_Z = Fraction(175, 36)               # tau(b) = (35/36)*5
LOG_R2_Z = 12 * mp.log(2)               # R_2 = 2^12 (Buzzard)


def _slit_radius(r):
    """[CDT-L] (A.3.2): conformal radius of D minus (-1,-r]."""
    return 4 * r / (1 + r) ** 2


def _lune_radius(c):
    """[CDT-L] (A.1.2): conformal radius of the lune L(c)."""
    return (c * c - 1) / (c * c + 1)


def psi_prime_exact():
    """[CDT-L] (A.4.3) recomputed as an exact rational."""
    out = SHRINK_L * R_L * _lune_radius(C_L)
    for r in RS_L:
        out *= _slit_radius(r)
    return out


def tau_of_b(sigmas):
    """[CDT-ICM] Thm 2.1 / [CDT-L] (2.5.2): tau(b) = m^-2 sum_i (2i-1) sigma_i."""
    m = len(sigmas)
    return Fraction(sum((2 * i - 1) * s for i, s in enumerate(sigmas, start=1)), m * m)


# ---------------------------------------------------------------------------
# 1.  The Hauptmodul, by eta reduction (validated against its q-series)
# ---------------------------------------------------------------------------

def eta_log(tau, nterms=200):
    """(log|eta(tau)|, arg eta(tau)) for Im tau > 0.

    SL2(Z) reduction to the standard fundamental domain (tracking the multiplier
    eta(tau+1) = e^{i pi/12} eta(tau), eta(-1/tau) = sqrt(-i tau) eta(tau)), then
    the q-product.  Needed because the naive q-product of x(q) is worthless as
    |q| -> 1, which is exactly where the tangency of Omega^circ sits.
    """
    lmod, arg = 0.0, 0.0
    t = complex(tau)
    for _ in range(4000):
        n = math.floor(t.real + 0.5)
        if n:
            t -= n
            arg += n * math.pi / 12.0
        if abs(t) < 1.0 - 1e-15:
            s = cmath.sqrt(-1j * t)
            lmod -= math.log(abs(s))
            arg -= cmath.phase(s)
            t = -1.0 / t
        else:
            break
    else:                                            # pragma: no cover
        raise RuntimeError(f"eta reduction did not terminate at tau = {tau}")
    q = cmath.exp(2j * math.pi * t)
    prod, qn = 1.0 + 0j, q
    for _ in range(nterms):
        prod *= 1.0 - qn
        qn *= q
        if abs(qn) < 1e-22:
            break
    val = cmath.exp(1j * math.pi * t / 12.0) * prod
    return lmod + math.log(abs(val)), arg + cmath.phase(val)


def x_log(w):
    """(log|x(w)|, arg x(w)) for the Gamma_0(2) Hauptmodul

        x(q) = q prod_{n>=1} (1+q^n)^24 = Delta(2 tau)/Delta(tau) = (eta(2tau)/eta(tau))^24,

    [CDT-ICM] (5.5).  Returned in logarithmic form: |x| underflows badly near the
    boundary.  ([CDT-L] (A.0.1) uses h = -256 x, i.e. log|h| = log 256 + log|x|.)
    """
    tau = cmath.log(w) / (2j * math.pi)
    l2, a2 = eta_log(2 * tau)
    l1, a1 = eta_log(tau)
    return 24 * (l2 - l1), 24 * (a2 - a1)


def x_series(q, nterms=400):
    """x(q) by its q-product; valid only for |q| bounded away from 1."""
    out, acc, qn = complex(q), 1.0 + 0j, complex(q)
    for _ in range(nterms):
        acc *= (1.0 + qn) ** 24
        qn *= q
        if abs(qn) < 1e-25:
            break
    return out * acc


# ---------------------------------------------------------------------------
# 2.  The two archimedean growth functionals
# ---------------------------------------------------------------------------

def bc_integral(L, A):
    """Bost-Charles integral  I = int int_{T^2} log|phi(z)-phi(w)| dmu dmu,
    from samples of phi on an N-point rotated grid given in polar log form
    (L = log|phi|, A = arg phi).

    Exact discrete identity behind the estimator: with q(z,w) := (phi(z)-phi(w))/(z-w),
    which extends continuously by q(z,z) = phi'(z),

        N^-2 sum_{j != k} log|phi_j - phi_k|
            = N^-2 sum_{j,k} log|q_jk| - N^-1 mean_j log|phi'(z_j)| + (log N)/N,

    since prod_{j != k}|z_j - z_k| = N^N for any rotated root-of-unity grid.  The
    diagonal term is dropped here (it is O(1/N) whenever log|phi'| is integrable
    and it is the only term that cannot be formed from boundary samples alone).
    """
    n = len(L)
    Lc = L[:, None]
    Lr = L[None, :]
    hi = np.maximum(Lc, Lr)
    lo = np.minimum(Lc, Lr)
    dA = A[:, None] - A[None, :]
    # log|phi_j - phi_k| = hi + log|1 - exp((lo-hi) + i dA)| (safe: lo - hi <= 0)
    z = np.exp((lo - hi) + 1j * dA)
    with np.errstate(divide="ignore"):
        pair = hi + np.log(np.abs(1.0 - z))
    np.fill_diagonal(pair, 0.0)
    return float(pair.sum()) / n ** 2 - math.log(n) / n


def rearrangement_integral(L):
    """J = int_0^1 2t (log|phi(e^{2 pi i t})|)^* dt, the increasing-rearrangement
    majorant of the Bost-Charles integral ([CDT-L] Prop 8.1.13, (2.5.5))."""
    n = len(L)
    s = np.sort(L)
    t = (np.arange(n) + 0.5) / n
    return float(np.sum(2 * t * s) / n)


def sup_log(L):
    """sup_T log|phi|, the crude numerator of [CDT-U] (2.0.3) / [CDT-ICM] (5.8)."""
    return float(np.max(L))


# ---------------------------------------------------------------------------
# 3.  Explicit conformal maps of [CDT-L] Appendix A
# ---------------------------------------------------------------------------

def lune(z, c):
    """[CDT-L] (A.1.1): the inverse lune map, D -> L(c), with lune(0) = 0 and
    lune'(0) = (c^2-1)/(c^2+1).

    The square-root argument (1+c^2)^2 (1+z)^2 - 16 c^2 z has its two zeros on the
    unit circle (their product is 1), so it is factored as (1+c^2)^2 (z-e^{i t})(z-e^{-i t})
    and each factor is taken with the principal branch: analytic on |z| < 1.
    """
    c2 = c * c
    cosk = -(2 - 16 * c2 / (1 + c2) ** 2) / 2
    if abs(cosk) > 1:                                # pragma: no cover
        raise ValueError(f"lune: unexpected real branch points at c = {c}")
    k = math.acos(cosk)
    e1, e2 = cmath.exp(1j * k), cmath.exp(-1j * k)
    root = (1 + c2) * np.sqrt(1 - z / e1) * np.sqrt(1 - z / e2) * np.sqrt(e1 * e2)
    return (z * (1 + c2) - 1 - c2 + root) / (2 * (c2 - 1))


def slit(z, r):
    """[CDT-L] (A.3.1): the conformal isomorphism D -> D minus (-1,-r], with
    slit(0) = 0 and slit'(0) = 4r/(1+r)^2.  Same branch treatment as `lune`."""
    p1 = (r + 1) ** 2
    cosk = (1 - 6 * r + r * r) / p1
    if abs(cosk) > 1:                                # pragma: no cover
        raise ValueError(f"slit: unexpected real branch points at r = {r}")
    k = math.acos(cosk)
    e1, e2 = cmath.exp(1j * k), cmath.exp(-1j * k)
    root = (1 + r) * np.sqrt(1 - z / e1) * np.sqrt(1 - z / e2) * np.sqrt(e1 * e2)
    num = p1 - 2 * (r - 1) ** 2 * z + p1 * z * z + (1 + r) * (z - 1) * root
    return num / (8 * r * z)


def psi_L(z, printed_order=False):
    """[CDT-L] (A.4.2): psi(z) = G(0.995 z) with

        G(z) = -R lune(-e^{2 pi i th_a} slit(e^{2 pi i th_b} slit(e^{2 pi i th_c}
                       slit(e^{2 pi i th_d} slit(z, r1), r2), r3), r4), c).

    Which printed theta sits at which of the four rotation slots is the one thing in
    Appendix A that the print does not fix unambiguously: read strictly by the
    nesting, the innermost rotation is e^{2 pi i theta_4} and the lune's is
    e^{2 pi i theta_1} (`printed_order=True` here).  That reading fails the paper's
    own Lemma A.4.4 -- it leaves five preimages of -1/72 inside psi(D) instead of
    one -- and gives a Bost-Charles integral of 12.113, whence (A.5.1) would read
    14.31 > 14 and Theorem A would not close.  The ascending assignment used by
    default (theta_1 innermost, theta_4 at the lune) is the unique one of the 24
    which excludes every bad preimage, and it reproduces the printed 11.844.
    """
    order = (3, 2, 1, 0) if printed_order else (0, 1, 2, 3)
    t = [float(THETAS_L[i]) for i in order]
    zz = float(SHRINK_L) * z
    r1, r2, r3, r4 = (float(r) for r in RS_L)
    w = slit(zz, r1)
    w = slit(cmath.exp(2j * math.pi * t[0]) * w, r2)
    w = slit(cmath.exp(2j * math.pi * t[1]) * w, r3)
    w = slit(cmath.exp(2j * math.pi * t[2]) * w, r4)
    w = lune(-cmath.exp(2j * math.pi * t[3]) * w, float(C_L))
    return -float(R_L) * w


def psi_Z_lune(z):
    """[CDT-ICM] section 5.2, the lune template.  The printed closed form is

        psi(z) = (2/3)((5^2+2^2)/(2(5^2-2^2)))(1 + z - sqrt(1 - 2(5^4-6*5^2*2^2+2^4)/(5^2+2^2)^2 z + z^2))
               = (14/29) z + ...,

    which is exactly  -(2/3) lune(-z, 5/2)  in the notation of (A.1.1) -- note the
    outer sign: it puts the removed bite on the positive real side, i.e. towards the
    cusp q = 1 where |x| blows up.  (With the opposite sign the numerator is 4.52,
    not 3.93: the sign is the whole content of the choice of contour.)
    """
    return -(2.0 / 3.0) * lune(-z, 2.5)


def psi_Z_circ(z):
    """[CDT-ICM] section 5.2, the circle template Omega^circ = {|z+2/5| <= 3/5},
    uniformized by z -> z/(2z+3); conformal radius 1/3."""
    return z / (2 * z + 3)


def deriv0(f, rad=1e-3, n=256):
    """f'(0) by the Cauchy integral (finite differences are worthless here: the
    composed contour map has huge higher Taylor coefficients)."""
    th = 2 * math.pi * (np.arange(n) + 0.5) / n
    vals = np.array([f(rad * cmath.exp(1j * t)) for t in th])
    return complex(np.mean(vals * np.exp(-1j * th)) / rad)


def richardson(vals):
    """Limit of a sequence with O(1/N) error sampled at N, 2N, 4N, ...: the last
    increment is c/(2N), so the limit is v[-1] + 2*(v[-1]-v[-2])."""
    return vals[-1] + 2 * (vals[-1] - vals[-2]) if len(vals) >= 2 else vals[-1]


def grid(n, offset=0.5):
    """N-point rotated root-of-unity grid (the rotation keeps z = -1 off the grid;
    prod_{j != k} |z_j - z_k| = N^N is rotation invariant)."""
    return np.exp(2j * math.pi * (np.arange(n) + offset) / n)


def integrals(psi, n, scale256=False, nofs=4):
    """(I, J, spread): Bost-Charles and rearrangement integrals, averaged over
    `nofs` grid rotations (each rotation is a legitimate estimator; the spread of
    the family is the honest error bar)."""
    Is, Js = [], []
    for k in range(nofs):
        L, A = phi_samples(psi, n, offset=(k + 0.5) / nofs, scale256=scale256)
        Is.append(bc_integral(L, A))
        Js.append(rearrangement_integral(L))
    return float(np.mean(Is)), float(np.mean(Js)), float(max(Is) - min(Is))


def phi_samples(psi, n, offset=0.5, scale256=False):
    """(log|phi|, arg phi) on the grid for phi = x(psi(.)) (or h = -256 x)."""
    zs = grid(n, offset)
    ws = np.array([psi(complex(z)) for z in zs])
    if np.max(np.abs(ws)) >= 1.0:                    # pragma: no cover
        raise ValueError("psi leaves the unit disc")
    out = [x_log(complex(w)) for w in ws]
    L = np.array([o[0] for o in out])
    A = np.array([o[1] for o in out])
    if scale256:
        L = L + math.log(256.0)
        A = A + math.pi                              # h = -256 x
    return L, A


def _x_series_c(q, nterms=600):
    out, acc, qn = complex(q), 1.0 + 0j, complex(q)
    for _ in range(nterms):
        acc *= (1.0 + qn) ** 24
        qn *= q
        if abs(qn) < 1e-30:
            break
    return out * acc


def _bad_preimages(lo=1e-3, hi=0.77, grid_n=120):
    """Solutions of h(q) = -1/72, i.e. x(q) = 1/18432, with lo < |q| < hi, by a
    grid of Newton starts.  Recomputes [CDT-L] Lemma A.4.4 from scratch."""
    target = 1.0 / 18432.0
    roots = []
    for a in np.linspace(-hi - 0.02, hi + 0.02, grid_n):
        for b in np.linspace(-hi - 0.02, hi + 0.02, grid_n):
            q = complex(a, b)
            if abs(q) > hi + 0.02:
                continue
            for _ in range(40):
                fq = _x_series_c(q) - target
                dq = (_x_series_c(q + 1e-7) - _x_series_c(q - 1e-7)) / 2e-7
                if dq == 0:
                    break
                step = fq / dq
                q -= step
                if abs(q) > hi + 0.05:
                    break
                if abs(step) < 1e-14:
                    break
            if abs(q) <= hi + 0.02 and abs(_x_series_c(q) - target) < 1e-18 \
                    and lo < abs(q) < hi:
                if not any(abs(q - r) < 1e-7 for r in roots):
                    roots.append(q)
    return sorted(roots, key=abs)


def _inside(pt, psi, n=4000):
    """Winding-number test for pt in psi(D) (psi is univalent, so the image is the
    interior of the closed curve psi(T))."""
    curve = np.array([psi(complex(z)) for z in grid(n)]) - pt
    return abs(float(np.sum(np.diff(np.unwrap(np.angle(curve)))))) > math.pi


# ---------------------------------------------------------------------------
# 4.  Solving the quantitative bounds for kappa
# ---------------------------------------------------------------------------

def kappa_from_bound(numer, denom0, gamma, log_rho_inv, m):
    """Smallest kappa for which the quantitative holonomy bound still contradicts m.

    [CDT-ICM] (2.5): m <= numer / (denom0 - (1-gamma)(2/kappa - (1-gamma)/kappa^2) log(1/rho)),
    so a contradiction (bound < m) holds iff

        denom0 - (1-gamma)(2/kappa - (1-gamma)/kappa^2) log(1/rho) > numer/m.

    Returns the threshold kappa* (the infimum of admissible kappa): every kappa > kappa*
    is an effective irrationality exponent, so the printed exponent is ceil(kappa*).
    """
    g = mp.mpf(1) - mp.mpf(gamma.numerator) / gamma.denominator
    target = mp.mpf(numer) / m

    def f(k):
        return mp.mpf(denom0) - g * (2 / k - g / k ** 2) * mp.mpf(log_rho_inv) - target

    lo = mp.mpf("1.0000001")
    while f(lo) > 0:                                 # pragma: no cover
        lo = (lo + 1) / 2
    hi = mp.mpf(4)
    for _ in range(200):
        if f(hi) > 0:
            break
        hi *= 2
    else:                                            # pragma: no cover
        return None
    return mp.findroot(f, (lo, hi), solver="bisect", tol=mp.mpf(10) ** -30)


# ---------------------------------------------------------------------------
# 5.  Subcommands
# ---------------------------------------------------------------------------

def cmd_printed(out=sys.stdout):
    p = lambda *a: print(*a, file=out)
    ok = []

    p("[A] Apery's decisive inequality, the paper's own framing device")
    p("    [CDT-L] (1.2.2): 4 log(sqrt 2 + 1) > 3")
    a = 4 * mp.log(mp.sqrt(2) + 1)
    p(f"      4 log(sqrt2+1)          = {mp.nstr(a, 20)}   (> 3: {a > 3})")
    # exact certificate, no float comparison: (1+sqrt2)^4 > e^3 <=> 17+12sqrt2 > e^3
    lhs = 17 + 12 * mp.sqrt(2)
    p(f"      (1+sqrt2)^4 = 17+12sqrt2 = {mp.nstr(lhs, 20)}  vs  e^3 = {mp.nstr(mp.e ** 3, 20)}")
    delta = (a - 3) / (a + 3)
    p(f"      delta = (4log(sqrt2+1)-3)/(4log(sqrt2+1)+3) = {mp.nstr(delta, 12)}")
    p(f"      1 + 1/delta = {mp.nstr(1 + 1 / delta, 12)}   [Apery's classical mu(zeta(3)) = 13.41782]")
    ok.append(("(1.2.2) and Apery's exponent", a > 3 and abs(1 + 1 / delta - mp.mpf("13.41782")) < 1e-5))

    p("")
    p("[B] The denominator terms tau(b), exactly ([CDT-ICM] Thm 2.1)")
    s9 = [0, 1] + [2] * 7
    t9 = tau_of_b(s9)
    p(f"    9 functions, sigma = {s9}:  tau(b) = {t9}  = {float(t9):.6f}"
      f"   [printed 157/81: {t9 == TAU_L9}]")
    ok.append(("tau(b) = 157/81", t9 == TAU_L9))
    p(f"    printed decomposition 27/80 + 191/49 = {Fraction(27,80)+Fraction(191,49)}"
      f"   [printed 16603/3920: {Fraction(27,80)+Fraction(191,49) == TAU_L}]")
    ok.append(("16603/3920 = 27/80 + 191/49", Fraction(27, 80) + Fraction(191, 49) == TAU_L))
    sz = [0] + [5] * 5
    tz = tau_of_b(sz)
    p(f"    zeta_2(5): sigma = {sz} (m=6, b=(0,5,5,5,5,5)):  tau(b) = {tz} = {float(tz):.6f}"
      f"   [printed 175/36 = (35/36)*5: {tz == TAU_Z}]")
    ok.append(("tau(b) = 175/36", tz == TAU_Z))

    p("")
    p("[C] The conformal radius of the L(2,chi_-3) contour, exactly ([CDT-L] (A.4.3))")
    pp = psi_prime_exact()
    p(f"    (995/1000) R (c^2-1)/(c^2+1) prod_i 4r_i/(1+r_i)^2")
    p(f"      recomputed = {pp.numerator}/{pp.denominator}")
    p(f"      printed    = {PSI_PRIME_PRINTED.numerator}/{PSI_PRIME_PRINTED.denominator}")
    p(f"      equal: {pp == PSI_PRIME_PRINTED}    decimal = {mp.nstr(mp.mpf(pp.numerator)/pp.denominator, 12)}"
      "   [printed 0.6292232680...]")
    ok.append(("(A.4.3) exact rational", pp == PSI_PRIME_PRINTED))

    p("")
    p("[D] The decisive quotient of [CDT-L] (A.5.1) / Ex 7.4.6")
    lphi = mp.log(256 * mp.mpf(pp.numerator) / pp.denominator)
    den = lphi - mp.mpf(TAU_L.numerator) / TAU_L.denominator
    p(f"    log|256 psi'(0)|        = {mp.nstr(lphi, 12)}   [printed 5.081...]")
    p(f"    - tau(b;e) = -16603/3920 = -{mp.nstr(mp.mpf(TAU_L.numerator)/TAU_L.denominator, 12)}")
    p(f"    denominator             = {mp.nstr(den, 12)}")
    for label, num, printed in (("(A.5.1), numerator 11.845", mp.mpf("11.845"), mp.mpf("13.9938")),
                                ("Ex 7.4.6, numerator 11.844", mp.mpf("11.844"), mp.mpf("13.99303"))):
        val = num / den
        good = abs(val - printed) < 5e-4
        p(f"    {label:28s}: {mp.nstr(val, 10)}   printed {printed}   [{'ok' if good else 'MISMATCH'}]"
          f"  (< 14: {val < 14})")
        ok.append((label, good and val < 14))

    p("")
    p("[E] The convexity savings of [CDT-L] Ex 7.4.6 (Thm 7.1.6, Bost-Charles characteristic)")
    m = 14
    rs = [mp.e ** mp.mpf(-1), mp.e ** mp.mpf("-0.5"), mp.e ** mp.mpf("-0.25"), mp.mpf(1)]
    # the l=1 example prints (L_{e^-1/2} . L) to five digits, the l=3 list to four
    That = [mp.mpf("9.8766"), mp.mpf("10.573"), mp.mpf("11.049"), mp.mpf("11.844")]
    al1 = (That[3] - mp.mpf("10.5739")) / (mp.log(rs[3]) - mp.log(rs[1]))
    p(f"    l = 1, r0 = e^-1/2:  alpha_1 = {mp.nstr(al1, 8)}   [printed 2.5410...]")
    sav1 = (al1 ** 2 * (mp.log(rs[3]) - mp.log(rs[1])) / m) / den
    p(f"      saving = {mp.nstr(sav1, 8)}   [printed 0.27243...]")
    p(f"      refined bound = {mp.nstr(mp.mpf('11.844')/den - sav1, 8)}   [printed 13.7206...]")
    p("      (the printed inputs carry 5 digits, so these agree to ~1e-4, not more)")
    ok.append(("Ex 7.4.6 alpha_1 and saving", abs(al1 - mp.mpf("2.5410")) < 2e-3
               and abs(sav1 - mp.mpf("0.27243")) < 5e-4))
    alphas = [(That[k] - That[k - 1]) / (mp.log(rs[k]) - mp.log(rs[k - 1])) for k in (1, 2, 3)]
    p("    l = 3, r = (e^-1, e^-1/2, e^-1/4, 1):  alpha = "
      + ", ".join(mp.nstr(a, 6) for a in alphas) + "   [printed 1.3943, 1.9018, 3.1802]")
    tot = sum(a ** 2 * (mp.log(rs[k]) - mp.log(rs[k - 1])) for k, a in zip((1, 2, 3), alphas))
    sav3 = (tot / m) / den
    p(f"      saving = {mp.nstr(sav3, 8)}   [printed 0.37171...]")
    p(f"      refined bound = {mp.nstr(mp.mpf('11.844')/den - sav3, 8)}   [printed 13.621...]")
    ok.append(("Ex 7.4.6 l=3 saving", abs(sav3 - mp.mpf("0.37171")) < 5e-5))

    p("")
    p("[F] The 9-function configurations, which do NOT close ([CDT-L] (A.5.3), Ex 7.4.9)")
    den9 = lphi - 2 * mp.mpf(TAU_L9.numerator) / TAU_L9.denominator
    p(f"    log|256 psi'(0)| - 2*157/81 = {mp.nstr(den9, 10)}")
    v = mp.mpf("11.844") / den9
    vr = mp.mpf("11.844") / (mp.mpf("5.081") - 2 * mp.mpf(TAU_L9.numerator) / TAU_L9.denominator)
    p(f"    (A.5.3): 11.844/... = {mp.nstr(v, 8)}  exact;  {mp.nstr(vr, 8)}  from the printed,")
    p(f"      rounded 5.081   [printed 9.833... -- i.e. computed from the rounded log; both > 9,")
    p(f"      so the conclusion 'not a contradiction' is unaffected]")
    ok.append(("(A.5.3) = 9.833 from the printed rounding",
               abs(vr - mp.mpf("9.833")) < 1e-3 and v > 9 and vr > 9))
    tot9 = sum(a ** 2 * (mp.log(rs[k]) - mp.log(rs[k - 1])) for k, a in zip((1, 2, 3), alphas))
    v9 = (mp.mpf("11.844") - tot9 / 9) / den9
    p(f"    Ex 7.4.9 (l=3, m=9): {mp.nstr(v9, 8)}   [printed 9.4203...]  (> 9, still no contradiction)")
    ok.append(("Ex 7.4.9 = 9.4203", abs(v9 - mp.mpf("9.4203")) < 2e-3 and v9 > 9))

    p("")
    for name, good in ok:
        p(f"    {'PASS' if good else 'FAIL'}  {name}")
    p(f"[printed] {sum(1 for _, g in ok if g)}/{len(ok)} checks pass")
    return all(g for _, g in ok)


def cmd_zeta2(nmax=2048, out=sys.stdout):
    p = lambda *a: print(*a, file=out)
    ok = []

    p("[A] The precursor bound, fully elementary ([CDT-ICM] (5.8))")
    p("    numerator   max_T log|phi| + sum_p log R_p, phi = x(z/(2z+3)), sup at z=1 -> q=1/5")
    num58 = mp.log(mp.mpf(1) / 5 * mp.nprod(lambda n: (1 + mp.mpf(5) ** -n) ** 24, [1, mp.inf])) + LOG_R2_Z
    den58 = -mp.log(3) + LOG_R2_Z - 5
    p(f"      log(x(1/5)) = {mp.nstr(mp.log(mp.mpf(1)/5*mp.nprod(lambda n: (1+mp.mpf(5)**-n)**24,[1,mp.inf])), 12)}")
    p(f"      numerator = {mp.nstr(num58, 12)}    denominator = -log 3 + 12 log 2 - 5 = {mp.nstr(den58, 12)}")
    v58 = num58 / den58
    p(f"      (5.8) = {mp.nstr(v58, 10)}   [printed 5.52667...]   (< 6: {v58 < 6})")
    ok.append(("(5.8) = 5.52667 < 6", abs(v58 - mp.mpf("5.52667")) < 5e-5 and v58 < 6))

    p("")
    p("[B] Validation of the Hauptmodul evaluation (eta reduction vs q-product)")
    worst = 0.0
    for q in (0.1, -0.3, 0.5j, 0.45 + 0.4j, -0.66, 0.66):
        L, A = x_log(complex(q))
        ser = x_series(complex(q))
        worst = max(worst, abs(math.exp(L) - abs(ser)) / abs(ser))
    p(f"    max relative disagreement on six test points: {worst:.2e}")
    ok.append(("eta route == q-product", worst < 1e-12))

    p("")
    p("[C] The circle template Omega^circ ([CDT-ICM] (5.6)), |phi\'(0)| = 1/3")
    p("    Omega^circ = {|z+2/5| <= 3/5} is internally tangent to |q| = 1 at the even cusp")
    p("    q = -1, so log|phi| is bounded but oscillates without a limit there (the boundary")
    p("    is a horocycle): the quadrature is O(1/N) at best, hence the error bars.")
    den56 = -mp.log(3) + LOG_R2_Z - mp.mpf(TAU_Z.numerator) / TAU_Z.denominator
    p("      N      I (Bost-Charles)   spread     J (rearrangement)")
    seq = []
    for n in (256, 512, 1024, 2048, 4096):
        if n > nmax:
            break
        I, J, sp = integrals(psi_Z_circ, n)
        seq.append(I)
        p(f"    {n:5d}  {I:16.6f}  {sp:9.1e}  {J:16.6f}")
    # the error here is oscillatory, not monotone (the horocycle boundary), so the
    # honest estimate is the mean of the finest grids with the spread as the bar --
    # Richardson would just amplify the oscillation.
    Iex = float(np.mean(seq[-2:]))
    p(f"    best estimate I = {Iex:.6f} +- {abs(seq[-1]-seq[-2]):.1e}    [printed 2.13322...]")
    p("    (this is the least accurate number in the battery, by two orders of magnitude)")
    ok.append(("(5.6) integral == printed 2.13322", abs(Iex - 2.13322) < 5e-3))
    p(f"    denominator -log 3 + 12 log 2 - 175/36 = {mp.nstr(den56, 12)}")
    for label, numer, printed in (("recomputed", mp.mpf(Iex) + LOG_R2_Z, None),
                                  ("printed", mp.mpf("2.13322") + LOG_R2_Z, mp.mpf("4.43206"))):
        val = numer / den56
        p(f"      {label:11s}: m <= {mp.nstr(val, 8)}"
          + (f"   [printed {printed}]" if printed else "") + f"   (< 6: {val < 6})")
        if printed is not None:
            ok.append(("(5.6) = 4.43206 < 6", abs(val - printed) < 5e-5 and val < 6))
    ok.append(("recomputed integral gives the same contradiction",
               (mp.mpf(Iex) + LOG_R2_Z) / den56 < 6))

    p("")
    p("[D] The irrationality measure from the circle template ([CDT-ICM] (5.7))")
    k = kappa_from_bound(mp.mpf("2.13322") + LOG_R2_Z, den56, Fraction(1, 6), LOG_R2_Z, 6)
    p(f"    gamma = 1/6, rho_2 = 2^-12:  kappa* = {mp.nstr(k, 10)}   [printed ~22.0724]")
    ok.append(("(5.7) kappa ~ 22.0724", abs(k - mp.mpf("22.0724")) < 5e-3))

    p("")
    p("[E] The lune template, which gives Theorem 5.2's printed exponent 20")
    d = deriv0(psi_Z_lune)
    p(f"    psi\'(0) = {d.real:.12f}   printed 14/29 = {14/29:.12f}")
    ok.append(("psi'(0) = 14/29", abs(d.real - 14 / 29) < 1e-10 and abs(d.imag) < 1e-10))
    den52 = (mp.log(14) - mp.log(29)) + LOG_R2_Z - mp.mpf(TAU_Z.numerator) / TAU_Z.denominator
    p(f"    denominator log(14/29) + 12 log 2 - 175/36 = {mp.nstr(den52, 12)}")
    p("      N      I (Bost-Charles)   spread     J (rearrangement)")
    seqI, seqJ = [], []
    for n in (256, 512, 1024, 2048, 4096):
        if n > nmax:
            break
        I, J, sp = integrals(psi_Z_lune, n)
        seqI.append(I)
        seqJ.append(J)
        p(f"    {n:5d}  {I:16.6f}  {sp:9.1e}  {J:16.6f}")
    p(f"    printed numerator 3.92881... is the REARRANGEMENT majorant, not the")
    p(f"    Bost-Charles integral: recomputed J = {seqJ[-1]:.6f}, I = {richardson(seqI):.6f}.")
    ok.append(("printed 3.92881 == rearrangement integral", abs(seqJ[-1] - 3.92881) < 1e-3))
    ok.append(("Bost-Charles integral is strictly smaller", richardson(seqI) < 3.92881))
    for label, val in (("printed J", mp.mpf("3.92881")), ("recomputed I", mp.mpf(richardson(seqI)))):
        kk = kappa_from_bound(val + LOG_R2_Z, den52, Fraction(1, 6), LOG_R2_Z, 6)
        p(f"      {label:14s} -> kappa* = {mp.nstr(kk, 8)}"
          + ("   [printed 19.7439 < 20 = Thm 5.2]" if label == "printed J" else
             "   (the true integral leaves a little slack in the printed 20)"))
        if label == "printed J":
            ok.append(("Thm 5.2: kappa < 19.7439 < 20",
                       abs(kk - mp.mpf("19.7439")) < 5e-3 and kk < 20))

    p("")
    p("[F] The same target by the classical route, for scale (Lai-Sprang-Zudilin,")
    p("    arXiv:2505.05005v2): an Apery-style construction for zeta_2(5) with")
    lsz = 16 * mp.log(2) / (8 * mp.log(2) - 5)
    p(f"      mu(zeta_2(5)) <= (16 log 2)/(8 log 2 - 5) = {mp.nstr(lsz, 10)}   [printed 20.342...]")
    p(f"    The holonomy route's 19.7439 beats it by a factor {mp.nstr(lsz / mp.mpf('19.7439'), 6)}")
    p("    -- 3.0%.  That is the measured size of the engine's advantage over the classical")
    p("    construction at the one target where both are in print (cf. S10's Q1, which needs")
    p("    a factor 2.30 in the same currency).")
    ok.append(("LSZ exponent 20.342", abs(lsz - mp.mpf("20.342")) < 1e-3))

    p("")
    for name, good in ok:
        p(f"    {'PASS' if good else 'FAIL'}  {name}")
    p(f"[zeta2] {sum(1 for _, g in ok if g)}/{len(ok)} checks pass")
    return all(g for _, g in ok)


def cmd_l2chi(nmax=2048, out=sys.stdout):
    p = lambda *a: print(*a, file=out)
    ok = []
    pp = psi_prime_exact()

    p("[A] The composed contour of [CDT-L] (A.4.2), rebuilt from (A.1.1) and (A.3.1)")
    for lab, po in (("ascending (used)", False), ("printed nesting", True)):
        d = deriv0(lambda z: psi_L(z, printed_order=po))
        p(f"    {lab:18s}: |psi'(0)| = {abs(d):.12f}   exact (A.4.3) = {float(pp):.12f}")
        ok.append((f"psi'(0) == (A.4.3), {lab}", abs(abs(d) - float(pp)) < 1e-10))
    p("    (the rotations have modulus one, so |psi'(0)| cannot tell the two readings apart)")
    ws = np.array([psi_L(complex(z)) for z in grid(4096)])
    p(f"    max |psi| on the grid = {np.max(np.abs(ws)):.6f}   (R = 77/100)")
    ok.append(("psi maps into the disc", np.max(np.abs(ws)) < 1.0))

    p("")
    p("[B] Lemma A.4.4, recomputed: the preimages of -1/72 under h = -256 x")
    f = lambda t: mp.mpf(256) * (mp.mpf(t) * mp.nprod(lambda n: (1 + mp.mpf(t) ** n) ** 24,
                                                      [1, mp.inf])) - mp.mpf(1) / 72
    r = mp.findroot(f, mp.mpf("0.00005"))
    p(f"    the real preimage: x = {mp.nstr(r, 12)}   [printed 0.0000541829...]")
    ok.append(("A.4.4 preimage 0.0000541829", abs(r - mp.mpf("0.0000541829")) < 1e-10))
    bad = _bad_preimages()
    p(f"    preimages with |q| < 1: the real one, {len(bad)} in the horoball at q = -1,")
    p(f"    and a pair at |q| = {max(abs(b) for b in _bad_preimages(hi=0.79)):.6f}"
      "   [printed 'at least 0.782767... > R = 77/100']")
    ok.append(("printed horoball bound 0.782767",
               abs(max(abs(b) for b in _bad_preimages(hi=0.79)) - 0.782767) < 1e-5))
    for lab, po in (("ascending (used)", False), ("printed nesting", True)):
        n_out = sum(1 for b in bad if not _inside(b, lambda z: psi_L(z, printed_order=po)))
        p(f"    {lab:18s}: {n_out}/{len(bad)} bad preimages excluded from psi(D)"
          + ("   <- Lemma A.4.4 holds" if n_out == len(bad) else "   <- Lemma A.4.4 FAILS"))
        ok.append((f"A.4.4 decides the reading, {lab}",
                   (n_out == len(bad)) == (po is False)))

    p("")
    p("[C] The Bost-Charles integral of the contour ([CDT-L] A.5, printed 11.844...)")
    p("      N      I (Bost-Charles)   spread     J (rearrangement)")
    seq = []
    for n in (256, 512, 1024, 2048, 4096):
        if n > nmax:
            break
        I, J, sp = integrals(psi_L, n, scale256=True)
        seq.append(I)
        p(f"    {n:5d}  {I:16.6f}  {sp:9.1e}  {J:16.6f}")
    Iex = richardson(seq)
    p(f"    Richardson limit I = {Iex:.6f}   [printed 11.844..., and (A.5.1) rounds it up to 11.845]")
    ok.append(("recomputed I == printed 11.844", abs(Iex - 11.8445) < 2e-3))

    p("")
    p("[D] The closing inequality (A.5.1)")
    lphi = mp.log(256 * mp.mpf(pp.numerator) / pp.denominator)
    den = lphi - mp.mpf(TAU_L.numerator) / TAU_L.denominator
    for label, num in (("recomputed", mp.mpf(Iex)), ("printed 11.845", mp.mpf("11.845"))):
        val = num / den
        p(f"    {label:15s}: m <= {mp.nstr(val, 10)}   (< 14: {val < 14})")
    ok.append(("the rebuilt contour closes below 14", mp.mpf(Iex) / den < 14))
    if nmax >= 1024:
        I2, _, _ = integrals(lambda z: psi_L(z, printed_order=True), min(nmax, 2048),
                             scale256=True)
        p(f"    for the printed nesting instead: I = {I2:.4f}  ->  m <= "
          f"{mp.nstr(mp.mpf(I2)/den, 8)}  (> 14: no contradiction)")
        ok.append(("printed nesting would not close", mp.mpf(I2) / den > 14))

    p("")
    p("[E] The effective measure of [CDT-ICM] Thm 5.1 (gamma = 1/2, |rho^-1| < 11614)")
    k = kappa_from_bound(mp.mpf("11.845"), den, Fraction(1, 2), mp.log(RHO_INV_L), 14)
    p(f"    kappa* = {mp.nstr(k, 12)}   ->  ceil = {int(mp.ceil(k))}   [printed exponent 24781]")
    ok.append(("Thm 5.1 exponent 24781", int(mp.ceil(k)) == 24781))

    p("")
    for name, good in ok:
        p(f"    {'PASS' if good else 'FAIL'}  {name}")
    p(f"[l2chi] {sum(1 for _, g in ok if g)}/{len(ok)} checks pass")
    return all(g for _, g in ok)


def cmd_s10(out=sys.stdout):
    p = lambda *a: print(*a, file=out)
    ok = []

    p("[A] The engine's effective flagship, in T-shift's coordinates")
    p("    [CDT-ICM] Thm 1.1: |1 - A gamma|_v <= H(gamma)^-eps  =>  h(gamma) <= C(K,v,Gamma,eps)(1+h(A)).")
    p("    T-shift at multiplier D: gamma = (3/2)^n in Gamma = <3/2>, A = m/D with m the")
    p("    nearest integer to D(3/2)^n, so |1 - A gamma| = ||D(3/2)^n||/m and H(gamma) = 3^n.")
    for theta, name in ((mp.mpf(2) / 3, "2/3 (T1/T4)"), (mp.mpf("0.5803"), "0.5803 (best known)")):
        eps = mp.log(3 / (2 * theta)) / mp.log(3)
        p(f"      theta = {name:20s} -> eps_0 = log(3/(2 theta))/log 3 = {mp.nstr(eps, 10)}")
    wall = mp.log(3) / mp.log(mp.mpf(3) / 2)
    p(f"    h(A) = n log(3/2) + O(log D) and h(gamma) = n log 3, so the conclusion bounds n")
    p(f"    only if  C < log 3 / log(3/2) = {mp.nstr(wall, 12)}.")
    p("    Verdict: the lane is open only for an effective constant below 2.7095 at eps = 0.738.")
    p("    [CDT-ICM] section 1 states the best known dependence is Baker-Wuestholz's product")
    p("    form (1.4) with an absolute numerical coefficient, and defers explicit constants")
    p("    for the holonomy route to future work -- so this wall is unpaid in either theory.")
    ok.append(("Baker wall = log3/log(3/2)", abs(wall - mp.mpf("2.709511")) < 1e-5))

    p("")
    p("[B] Screen 1 (WP0's non-degeneracy substitution)")
    p("    Proposition 1 at B = 1, Lambda = 2^n - |r| returns ||(3/2)^n|| exactly, so any")
    p("    candidate functional must be tested there.  The holonomy bounds cannot see it:")
    p("    their arithmetic input is a denominator type [1,...,b n]^sigma attached to a")
    p("    power series, not a pair of integer forms at one date; substituting a single date")
    p("    leaves tau(b) = 0 and the bound reads m <= I/log|phi'(0)|, independent of n.")
    p("    -> screen 1: PASSES vacuously (no date-dependent content to degenerate).")

    p("")
    p("[C] Screen 2 (S11 M2's interior-point test)")
    p("    ||D(3/2)^n|| = |G_n(2/3)|/2 is a value at one interior point of a disc.  The")
    p("    engine's arithmetic inputs are, at every place, radii and denominator types:")
    p(f"      2-adic input of [CDT-ICM] (5.6):  log R_2 = 12 log 2 = {mp.nstr(LOG_R2_Z, 10)}"
      "   (a radius, Buzzard)")
    p("      archimedean input: a conformal size and a Bost-Charles growth integral")
    p("    Both are germ/frame invariants; neither is sensitive to a value at one interior")
    p("    point.  -> screen 2: FAILS for the dimension-bound prong, exactly as S11 M2 (3)")
    p("    predicted; only the quantitative prong (Thm 2.6, whose output is an approximation")
    p("    inequality) has the right shape, and that prong is Thm 1.1's, priced in [A].")

    p("")
    p("[D] Measure currency: what shape the printed outputs have")
    p("    Effective outputs are power measures |eta - p/q|_v > C max(|p|,q)^-kappa with")
    p("    kappa = 24781 (L(2,chi_-3)), 20 (2-adic zeta(5)), 22.07 (the circle template).")
    p("    In T-shift's currency a fixed-exponent measure is an exponential floor, i.e. a")
    p("    T1-grade statement; T3 (sub-exponential, exp(-c n^beta)) needs kappa -> the")
    p("    Dirichlet boundary, and [CDT-ICM] after (2.4) states that even matching the")
    p("    classical measure is open ('It remains an open problem to give an eps-improvement")
    p("    over the usual irrationality measure in every single case').")
    p("    -> the report's 'the only item whose ceiling is T3' is not supported by print.")

    p("")
    p("[E] Free-zone cross-check of the same dictionary (report N3 / plan O-7)")
    for pp, qq in ((3, 2), (5, 2), (17, 4), (5, 3), (9, 4)):
        wall = mp.log(pp) / mp.log(mp.mpf(pp) / qq)
        p(f"    base {pp}/{qq}: Baker wall log p / log(p/q) = {mp.nstr(wall, 8):>10s}"
          f"   free zone (p > q^2): {pp > qq * qq}"
          + ("   (= the 3/2 wall: (9/4)^n = (3/2)^2n)" if (pp, qq) == (9, 4) else ""))
    p("    The wall is largest exactly where the problem is hard: 2.7095 at 3/2, and it")
    p("    drops below 2 in the free zone (5/2: 1.7565), where no second form is needed.")
    w32 = mp.log(3) / mp.log(mp.mpf(3) / 2)
    w52 = mp.log(5) / mp.log(mp.mpf(5) / 2)
    ok.append(("free-zone monotonicity of the wall", w52 < 2 < w32))

    p("")
    for name, good in ok:
        p(f"    {'PASS' if good else 'FAIL'}  {name}")
    p(f"[s10] {sum(1 for _, g in ok if g)}/{len(ok)} checks pass")
    return all(g for _, g in ok)


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 2048
    if cmd == "printed":
        good = cmd_printed()
    elif cmd == "zeta2":
        good = cmd_zeta2(n)
    elif cmd == "l2chi":
        good = cmd_l2chi(n)
    elif cmd == "s10":
        good = cmd_s10()
    elif cmd == "all":
        good = all([cmd_printed(), print() or cmd_zeta2(n), print() or cmd_l2chi(n),
                    print() or cmd_s10()])
    else:
        print(__doc__)
        return 2
    print(f"\n{'PASS' if good else 'FAIL'}  ({cmd})")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
