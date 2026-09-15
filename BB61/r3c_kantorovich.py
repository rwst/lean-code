#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R3c of `plan-BB61-counterexample.html`: Newton-Kantorovich existence in a ball, at the
best degree -- an EXACT `mu` in `K_H`, not a numerical one.

R3b drove `sup_{h<=H} |Phi~_h|` to the enclosure window's own floor at `d = 2,3,4` for every
`H <= 128` by Newton from Bernoulli, and left two gaps: the iteration is float, and it
reaches `1e-14`, not `0`.  R3c closes both.  The frame is the simplified (chord) Newton
operator, in the underdetermined setting `N = 2^L` parameters against `m = 2H` equations:

  THEOREM D.  Let `Phi : U -> R^m` be `C^1` on an open `U` in `R^N`, `xbar in U`,
  `Vb in R^{N x m}`, `B in R^{m x m}`, and put `G(xi) = Phi(xbar + Vb xi)`,
  `T(xi) = xi - B G(xi)`.  If for some `rho > 0`

     (i)   the box  { x : |x - xbar|_inf <= rho ||Vb||_{2->inf} }  lies in U,
     (ii)  kappa := sup over that box of || I - B DPhi(x) Vb ||_2  <  1,
     (iii) eta   := || B Phi(xbar) ||_2  <=  (1 - kappa) rho,

  then `T` maps the closed ball of radius `rho` into itself and is a `kappa`-contraction,
  so it has a unique fixed point `xi*`, `||xi*|| <= eta/(1-kappa)`; and if `B` is invertible
  then `Phi(xbar + Vb xi*) = 0` EXACTLY.

  Proof.  `T(xi) - T(xi') = (I - B integral_0^1 DG(xi' + t(xi-xi')) dt)(xi - xi')`, and every
  `DG(.) = DPhi(.) Vb` in the integrand is evaluated at a point of the box, so the operator
  norm of the bracket is at most `kappa`.  Then `||T(xi)|| <= kappa rho + ||T(0)|| =
  kappa rho + eta <= rho`.  Banach.  `G(xi*) = 0` because `B` is invertible.  []

THE POINT OF THE FRAME.  Both hypotheses are invariant under `Phi -> S Phi`, `B -> B S^{-1}`
for any invertible `S`: `eta` and `kappa` do not change.  So NO singular value of `DPhi`
occurs in Theorem D -- `s_{H,L}` enters only through the *choice* of `B`, and the best
choice `B = (A Vb)^{-1}`, `A = DPhi(xbar)`, gives

  eta <= ||Phi(xbar)|| / s_min,     kappa <= Lambda rho ||Vb||_{2->inf} / s_min,

so with `rho = 2 eta` the whole theorem holds as soon as

  ***   4 Lambda ||Vb||_{2->inf} ||Phi(xbar)|| / s_min^2  <=  1.   ***

`Lambda` is a Lipschitz constant for `DPhi` on the box.  That is sec 7.3's own gate
`residual / s_{H,L}` -- squared, and read at the NEWTON POINT rather than at Bernoulli.
R3b showed the ratio is the wrong statistic for the first step; here it is exactly the
right one for existence.  `||Phi(xbar)||` at the Newton point is `1e-14`, not `1.6e-3`.

WHAT IS CERTIFIED.  `Phi` here is the TRUE coefficient, not the windowed one: the window is
taken deep enough (`2 pi H eps(J,M) <= 1e-30`, R3a Theorem A) that truncation is below every
other term, and the residual bound carries it explicitly.  The stationary vector `pi(q)` is
enclosed by a Doeblin bound over `L` steps, the arithmetic by an a-priori running bound in
the style of `r1a_enclose.phi_fl`, and `Lambda` by Proposition E below.  What comes out is a
theorem: an exact shift-invariant Markov measure `mu` with `Phi_h(mu) = 0` for all `h <= H`,
together with a certified lower bound on `h(mu)` -- hence on `E_H`.

  PROPOSITION E (the Lipschitz constant of the Jacobian).  With `S_p = ||W_p||_inf` and
  `Nv_p = ||V_p||_1` the backward and forward passes of `r3b_jacobian.jacobian_at`, and
  `|q' - q|_inf <= beta` throughout,

      sum_b |dPhi_h/du(b) at q' - at q|  <=  sum_p [ dNv_p 2 S_{p+1} + Nv_p 2 D_{p+1} ],
      D_p = 2 beta sum_{p' > p} S_{p'},   dNv_p = ||dpi||_1 + 2 beta sum_{p' < p} Nv_{p'},

  each of the three recursions being the elementary one for a convex combination of terms of
  modulus at most one.  The same bound with `2 beta` replaced by the per-step arithmetic
  radius bounds `||A_float - DPhi(xbar)||`.

The polish that gets there is the chord iteration of R3b sec 5.1 in the exact arithmetic;
where that leaves the linearisation -- at `d = 4, H = 64`, where `||B|| = 5e8` -- a few full
Newton steps on the deep window come first.  The test is on the polished residual, so every
rung whose chord converges is bit-identical either way.

Usage:  python3 r3c_kantorovich.py checks | grid | all
"""
import json
import math
import os
import sys
import time

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from r3a_degree import Field, FAMILY                                     # noqa: E402
import r3b_jacobian as R3B                                               # noqa: E402

OUT = os.path.join(HERE, 'r3c_kantorovich.json')
FAIL = []
NCHECKS = [0]

TAUWIN = mp.mpf('1e-30')          # window depth for the certified pass
TAUFAST = mp.mpf('1e-13')         # window depth for the float Newton phase
UP = 1.0 + 2.0 ** -40             # one upward-rounding cushion per bound step
LD = np.longdouble
CLD = np.clongdouble
FXS = 160          # bits of the fixed-point pass of (6b)


def check(name, cond, extra=""):
    NCHECKS[0] += 1
    print("    [%s] %s%s" % ('ok ' if cond else 'FAIL', name, ('  ' + extra) if extra else ''))
    if not cond:
        FAIL.append(name)


def ufor(dtype):
    """Unit roundoff of the working type."""
    return float(np.finfo(dtype).eps) / 2.0


# ======================================================================================
# (1) the emission schedule and the constant table, with certified radii
# ======================================================================================
def sched_mp(F, J, M, dps=80):
    """gamma_p for p = -M..J as mpf, with a certified absolute radius for each."""
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        a, ra = F.alpha, F.alpha_r
        c, ec = F.c_m(M + 1)
        gam, rad = [], []
        for m in range(M, -1, -1):                       # p = -M .. 0
            gam.append(-c[m])
            rad.append(ec[m])
        for k in range(1, J + 1):                        # p = 1 .. J
            gam.append((a - 1) * a ** (-k))
            rad.append(ra * (a ** (-k) + (a - 1) * k * a ** (-k - 1)))
        return [mp.mpf(x) for x in gam], [mp.mpf(x) for x in rad]
    finally:
        mp.mp.dps = old


def rt(cdtype):
    """The real type matching a complex working type."""
    return np.float64 if cdtype == np.complex128 else LD


def etab(gam, grad, hs, cdtype=CLD, dps=80):
    """e(h gamma_p) rounded to `cdtype`, with one absolute radius `eta_c` for the table.

    `gamma_p` is known to `grad[p]`, so `e(h gamma_p)` to `2 pi h grad[p]`; rounding a unit
    complex costs `sqrt(2) u`.  The real and imaginary parts are written through the
    `.real` / `.imag` views from decimal strings, so no float64 intermediate appears.
    Returns (table, eta_c)."""
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        K = len(gam)
        r = rt(cdtype)
        tab = np.empty((len(hs), K), dtype=cdtype)
        for i, h in enumerate(hs):
            for j in range(K):
                th = 2 * mp.pi * h * gam[j]
                tab.real[i, j] = r(mp.nstr(mp.cos(th), 34))
                tab.imag[i, j] = r(mp.nstr(mp.sin(th), 34))
        u = ufor(r)
        rc = max(float(2 * mp.pi * max(hs) * x) for x in grad) if grad else 0.0
        return tab, (1.5 * u + rc) * UP
    finally:
        mp.mp.dps = old


# ======================================================================================
# (2) the stationary vector, with a Doeblin enclosure
# ======================================================================================
def targets(L):
    n, mask = 1 << L, (1 << L) - 1
    b = np.arange(n, dtype=np.int64)
    return ((b << 1) & mask), (((b << 1) | 1) & mask)


def stationary(q, L, iters=4000, dtype=LD):
    """pi by power iteration in the working type; normalised at the end."""
    n = 1 << L
    t0, t1 = targets(L)
    q = np.asarray(q, dtype=dtype)
    pi = np.full(n, dtype(1) / n, dtype=dtype)
    for _ in range(iters):
        nxt = np.zeros(n, dtype=dtype)
        np.add.at(nxt, t0, pi * (1 - q))
        np.add.at(nxt, t1, pi * q)
        if np.abs(nxt - pi).max() < 4 * ufor(dtype):
            pi = nxt
            break
        pi = nxt
    return pi / pi.sum()


def apply_P(pi, q, t0, t1, dtype):
    nxt = np.zeros(pi.size, dtype=dtype)
    np.add.at(nxt, t0, pi * (1 - q))
    np.add.at(nxt, t1, pi * q)
    return nxt


def doeblin_const(q, L):
    """The EXACT Doeblin constant of `P^L`, `sum_{b'} min_b P^L(b,b')`, by a min-product
    dynamic programme over the de Bruijn graph.

    A length-`L` path is determined by its start `b` and the `L` emitted symbols, which are
    the bits of its end `b'`; so `V_j[s] = min` over starts reaching `s` of the product so
    far obeys `V_j[s'] = min over the two predecessors s of V_{j-1}[s] c(s,s')`, and
    `V_L[b'] = min_b P^L(b,b')`.  Cost `L 2^L`.  This replaces the crude `(2m)^L` -- at the
    `d=2`, `L=14` Newton point it is four orders larger, which is the difference between a
    usable enclosure of `pi` and none."""
    n = 1 << L
    b = np.arange(n, dtype=np.int64)
    p0, p1 = (b >> 1), ((b >> 1) | (n >> 1))
    eps = b & 1
    q = np.asarray(q, dtype=float)
    V = np.ones(n)
    for _ in range(L):
        c0 = np.where(eps == 0, 1 - q[p0], q[p0])
        c1 = np.where(eps == 0, 1 - q[p1], q[p1])
        V = np.minimum(V[p0] * c0, V[p1] * c1)
    m = float(np.minimum(q, 1 - q).min())
    return max(float(V.sum()) * (1.0 - 1e-9), (2.0 * m) ** L)


def pi_enclose(q, L, dtype=LD, cmax=4000):
    """(pi_hat, delta) with `||pi_hat - pi||_1 <= delta`, by the L-step Doeblin bound.

    From any block `b` the chain reaches any block `b'` in exactly `L` steps along one
    deterministic path, whose probability is at least `m^L` with `m = min_b min(q_b, 1-q_b)`;
    summing over the `2^L` targets, `P^L` has Doeblin constant at least `(2m)^L`, so
    `tau(P^L) <= 1 - (2m)^L` and `tau(P^{cL}) <= tau(P^L)^c`.  Then
    `||pi_hat - pi||_1 <= ||pi_hat P^{cL} - pi_hat||_1 / (1 - tau(P^{cL}))`."""
    q = np.asarray(q, dtype=dtype)
    n = 1 << L
    t0, t1 = targets(L)
    pi = stationary(q, L, dtype=dtype)
    doeb = doeblin_const(q, L)
    if doeb <= 0.0:
        return pi, float('inf'), 0.0, 0
    tauL = 1.0 - doeb
    c = 1
    while c < cmax and tauL ** c > 0.5:
        c += 1
    tau = tauL ** c
    if tau >= 1.0 - 1e-12:
        return pi, float('inf'), tau, c
    v = pi.copy()
    for _ in range(c * L):
        v = apply_P(v, q, t0, t1, dtype)
    move = float(np.abs(v - pi).sum()) * UP
    arith = 3.0 * c * L * ufor(dtype) * UP                     # l1 rounding over cL steps
    delta = (move + arith) / (1.0 - tau) * UP
    return pi, delta, tau, c


# ======================================================================================
# (3) the forward pass, with an a-priori arithmetic radius
# ======================================================================================
def forward(tab, q, pi, L, dtype=CLD, etac=0.0, dpi=0.0):
    """Phi~_h for the memory-L chain, and a rigorous radius for the arithmetic.

    `|W| <= 1` at every stage and the step is a convex combination, so the incoming error is
    carried with factor one and each step adds `etac + 9u`.  The final contraction against
    `pi` adds `n u` plus `dpi max|W_0|` for the stationary vector's own uncertainty."""
    n = 1 << L
    t0, t1 = targets(L)
    q = np.asarray(q, dtype=rt(dtype))
    q0, q1 = (1 - q)[None, :], q[None, :]
    K = tab.shape[1]
    W = np.ones((tab.shape[0], n), dtype=dtype)
    for p in range(K - 1, -1, -1):
        W = q0 * W[:, t0] + q1 * (tab[:, p][:, None] * W[:, t1])
    u = ufor(rt(dtype))
    val = (W * np.asarray(pi, dtype=dtype)[None, :]).sum(axis=1)
    rad = (K * (etac + 9 * u) + n * u + dpi * float(np.abs(W).max())) * UP
    return val, float(rad)


# ======================================================================================
# (4) Proposition E: the Lipschitz constant of the Jacobian, and the arithmetic bound
# ======================================================================================
def lip_profiles(gam, q, hs, L, pi):
    """(S, Nv) with S[h][p] = ||W_p||_inf and Nv[h][p] = ||V_p||_1, float64, rounded up."""
    n = 1 << L
    mask = n - 1
    b = np.arange(n, dtype=np.int64)
    t0, t1 = ((b << 1) & mask), (((b << 1) | 1) & mask)
    p0, p1 = (b >> 1), ((b >> 1) | (n >> 1))
    epsb = b & 1
    q = np.asarray(q, dtype=float)
    q0, q1 = 1 - q, q
    pif = np.asarray(pi, dtype=float)
    K = len(gam)
    Ss, Ns = [], []
    for h in hs:
        e = np.exp(2j * np.pi * h * np.asarray(gam, dtype=float))
        W = np.ones(n, dtype=complex)
        S = np.empty(K + 1)
        S[K] = 1.0
        for p in range(K - 1, -1, -1):
            W = q0 * W[t0] + q1 * (e[p] * W[t1])
            S[p] = float(np.abs(W).max()) * UP
        V = pif.astype(complex)
        Nv = np.empty(K)
        for p in range(K):
            Nv[p] = float(np.abs(V).sum()) * UP
            c0 = np.where(epsb == 0, q0[p0], q1[p0] * e[p])
            c1 = np.where(epsb == 0, q0[p1], q1[p1] * e[p])
            V = V[p0] * c0 + V[p1] * c1
        Ss.append(np.minimum(S + 1e-12, 1.0))       # + the float64 error of S itself
        Ns.append(np.minimum(Nv + 1e-12, 1.0))

    return Ss, Ns


def perturb_bound(S, Nv, per_step, dpi):
    """Proposition E: bound on `sum_b |Delta g_h[b]|` when every conditional moves by at most
    `per_step / 2` and the stationary vector by `dpi` in l^1."""
    K = Nv.size
    D = np.zeros(K + 2)
    for p in range(K - 1, -1, -1):
        D[p] = D[p + 1] + per_step * S[p + 1]
    dN = np.empty(K)
    cur = dpi
    for p in range(K):
        dN[p] = cur
        cur = cur + per_step * Nv[p]
    return float(np.sum(dN * 2 * S[1:K + 1] + Nv * 2 * D[1:K + 1])) * UP


def lam_bounds(Ss, Ns, beta, dpi, u, dpi_beta):
    """(Lambda, arith) : Frobenius bounds on `||DPhi(x) - DPhi(xbar)||` over the box of
    half-width `beta`, and on `||A_float - DPhi(xbar)||`.

    The second carries one term Proposition E's three recursions do not see: the rounding of
    the accumulation `g = sum_p V_p (e W[t1] - W[t0])` itself, at most
    `(K+3) u sum_p Nv_p 2 S_{p+1}`."""
    lam, ari = [], []
    for S, Nv in zip(Ss, Ns):
        K = Nv.size
        acc = float((K + 3) * u * np.sum(Nv * 2 * S[1:K + 1])) * UP
        lam.append(perturb_bound(S, Nv, 2 * beta, dpi_beta))
        ari.append(perturb_bound(S, Nv, 10 * u, dpi) + acc)
    return (float(np.sqrt((np.array(lam) ** 2).sum())) * UP,
            float(np.sqrt((np.array(ari) ** 2).sum())) * UP)


def jacobian_at_p(gam, q, hs, L, cdtype=CLD):
    """`r3b_jacobian.jacobian_at` in a chosen working type.

    At `d >= 3` the float64 rounding of the JACOBIAN, not of the residual, is what binds
    `kappa`: it enters as `||B|| ||A_float - DPhi||`, and `||B|| = 1/s_min` is `1e6` and up.
    In longdouble the same bound is `2000` times smaller."""
    r = rt(cdtype)
    n = 1 << L
    mask = n - 1
    b = np.arange(n, dtype=np.int64)
    t0, t1 = ((b << 1) & mask), (((b << 1) | 1) & mask)
    p0, p1 = (b >> 1), ((b >> 1) | (n >> 1))
    eps = b & 1
    q = np.asarray(q, dtype=r)
    pi = stationary(q, L, dtype=r)
    q0, q1 = 1 - q, q
    K = len(gam)
    G = np.empty((len(hs), n), dtype=cdtype)
    phi = np.empty(len(hs), dtype=cdtype)
    gm = [mp.mpf(x) for x in gam] if isinstance(gam[0], mp.mpf) else \
        [mp.mpf(float(x)) for x in gam]
    old = mp.mp.dps
    mp.mp.dps = 60
    try:
        for i, h in enumerate(hs):
            e = np.empty(K, dtype=cdtype)
            for p in range(K):
                th = 2 * mp.pi * h * gm[p]
                e.real[p] = r(mp.nstr(mp.cos(th), 34))
                e.imag[p] = r(mp.nstr(mp.sin(th), 34))
            W = [None] * (K + 1)
            W[K] = np.ones(n, dtype=cdtype)
            for p in range(K - 1, -1, -1):
                W[p] = q0 * W[p + 1][t0] + q1 * (e[p] * W[p + 1][t1])
            V = pi.astype(cdtype)
            g = np.zeros(n, dtype=cdtype)
            for p in range(K):
                g += V * (e[p] * W[p + 1][t1] - W[p + 1][t0])
                c0 = np.where(eps == 0, q0[p0], q1[p0] * e[p])
                c1 = np.where(eps == 0, q0[p1], q1[p1] * e[p])
                V = V[p0] * c0 + V[p1] * c1
            G[i] = g
            phi[i] = V.sum()
    finally:
        mp.mp.dps = old
    return G, phi


# ======================================================================================
# (5) the Newton point, and the high-precision chord polish
# ======================================================================================
def newton_point(F, H, L, cap=0.45, iters=60, dqcap=0.40, tau=TAUFAST, log=None):
    """Full Newton from Bernoulli on the FAST window, float64, with a hard cap on
    `max_b |q(b) - 1/2|`.  The cap is what makes the Doeblin enclosure of `pi` usable: it
    bounds `m = min(q, 1-q)` from below, and it raises `h(mu)` at the same time."""
    J, M = F.need(H, tau)
    gam = R3B.schedule(F, J, M)
    hs = list(range(1, H + 1))
    n = 1 << L
    floor = 2 * np.pi * H * float(F.eps(J, M))
    q = np.full(n, 0.5)
    seq, lam = [], 1e-12
    for _ in range(iters):
        G, ph = R3B.jacobian_at(gam, q, hs, L)
        r = np.empty(2 * H)
        r[0::2], r[1::2] = ph.real, ph.imag
        A = np.empty((2 * H, n))
        A[0::2], A[1::2] = G.real, G.imag
        seq.append(float(np.linalg.norm(r)))
        if seq[-1] < 3 * floor:
            break
        U, S, Vt = np.linalg.svd(A, full_matrices=False)
        c = U.T @ r
        ok = False
        for _ in range(50):
            v = -(Vt.T @ ((S * c) / (S ** 2 + lam)))
            if np.abs(v).max() > dqcap or np.abs(q + v - 0.5).max() > cap:
                lam *= 4
                continue
            phn = R3B.forward(gam, q + v, hs, L)
            rn = np.empty(2 * H)
            rn[0::2], rn[1::2] = phn.real, phn.imag
            if np.linalg.norm(rn) < seq[-1]:
                q, ok = q + v, True
                lam = max(lam / 3, 1e-16)
                break
            lam *= 4
        if not ok:
            break
    return q, dict(d=F.d, H=H, L=L, cap=cap, iters=len(seq) - 1, resid=seq,
                   fastfloor=float(floor), fastfinal=seq[-1],
                   maxdq=float(np.abs(q - 0.5).max()))


def deep_setup(F, H, L, tau=TAUWIN, cdtype=CLD):
    """The deep window: schedule, constant table, float schedule for the Jacobian."""
    J, M = F.need(H, tau)
    gam_mp, grad = sched_mp(F, J, M)
    hs = list(range(1, H + 1))
    tab, etac = etab(gam_mp, grad, hs, cdtype)
    gam_f = np.array([float(x) for x in gam_mp])
    return dict(J=J, M=M, K=len(gam_mp), gam=gam_f, gam_mp=gam_mp, grad=grad, tab=tab,
                etac=etac, hs=hs, eps=float(F.eps(J, M)))


def res_vec(val):
    r = np.empty(2 * val.size)
    r[0::2], r[1::2] = np.asarray(val).real, np.asarray(val).imag
    return r


def deep_newton(D, q, L, iters=25, thresh=1e-13, dqcap=0.05, log=None):
    """Full Newton on the DEEP window, in float64, until the residual is small enough for the
    chord polish to contract.

    The chord step is `B Phi` with `||B|| = 1/s_min`, so it leaves the linearisation as soon as
    `||Phi|| / s_min` is not small; at `d = 4, H = 64` the fast window's Newton point still has
    `2e-12` on the deep window and `1/s_min = 5e8`, and the chord diverges (R3b sec 5.1).  A few
    steps with the Jacobian recomputed fix that.  A no-op, by the `thresh` test, at every rung
    whose fast-window point is already deep enough -- so those rows are untouched.

    The Levenberg damping is RELATIVE, `lam * s_max^2`.  An absolute one is useless here: at
    `d = 4, H = 64` the smallest singular value is `2e-9`, so `s_min^2 = 3e-18` sits far below
    any absolute `lam >= 1e-16` and the damping suppresses exactly the directions the step
    needs -- the residual then falls by 3% a step instead of quadratically.

    There is deliberately NO cap on `max_b |q(b) - 1/2|` here.  `newton_point` carries one, and
    at `d = 2, H = 256` its search stops ON that cap with `2.2e-2` still to go; a capped deep
    step is then rejected at every damping and the rung dies.  The cap is a device for steering
    the float search, not a hypothesis of anything: `doeblin_const` is evaluated at whatever
    `q` is reached, so the enclosure of `pi` stays sound wherever this walks."""
    hs, gam, n = D['hs'], D['gam'], 1 << L
    q = np.asarray(q, dtype=float).copy()
    ph = R3B.forward(gam, q, hs, L)
    cur = float(np.linalg.norm(res_vec(ph)))
    if cur <= thresh:
        return q, [cur]
    seq, lam = [cur], 1e-12
    for _ in range(iters):
        G, ph = R3B.jacobian_at(gam, q, hs, L)
        A = np.empty((2 * len(hs), n))
        A[0::2], A[1::2] = G.real, G.imag
        r = res_vec(ph)
        U, S, Vt = np.linalg.svd(A, full_matrices=False)
        smax2 = float(S[0]) ** 2
        c = U.T @ r
        ok = False
        for _ in range(40):
            v = -(Vt.T @ ((S * c) / (S ** 2 + lam * smax2)))
            if np.abs(v).max() > dqcap:
                lam *= 4
                continue
            rn = res_vec(R3B.forward(gam, q + v, hs, L))
            if np.linalg.norm(rn) < seq[-1]:
                q, ok = q + v, True
                seq.append(float(np.linalg.norm(rn)))
                lam = max(lam / 3, 1e-30)
                break
            lam *= 4
        if not ok or seq[-1] <= thresh:
            break
    return q, seq


def polish(D, q, Vb, B, L, steps=6, cdtype=CLD, log=None):
    """Chord Newton on the DEEP window in the working precision: `q <- q + Vb(-B Phi(q))`,
    with `B` the float64 inverse of `A Vb`.  The chord rate is `||I - B DPhi Vb||`, which the
    float Jacobian makes about `cond(A) u`, so two or three steps exhaust the precision."""
    q = np.asarray(q, dtype=rt(cdtype)).copy()
    hist = []
    best, bq = None, q.copy()
    for _ in range(steps):
        pi = stationary(q, L, dtype=rt(cdtype))
        val, rad = forward(D['tab'], q, pi, L, cdtype, D['etac'])
        r = res_vec(val).astype(np.float64)
        nrm = float(np.linalg.norm(r))
        hist.append(nrm)
        if best is None or nrm < best:
            best, bq = nrm, q.copy()
        else:
            break
        xi = -(B @ r.astype(np.float64))
        q = q + (Vb @ xi).astype(rt(cdtype))
        if np.abs(q - 0.5).max() >= 0.5:
            break
    return bq, hist


# ======================================================================================
# (6) the certificate
# ======================================================================================
def frob(X):
    return float(np.linalg.norm(np.asarray(X, dtype=float), 'fro')) * UP


def entropy(q, pi):
    q = np.clip(np.asarray(q, dtype=float), 1e-300, 1 - 1e-300)
    return float(-(np.asarray(pi, dtype=float) * (q * np.log(q) + (1 - q) * np.log(1 - q))).sum())


def certify(F, H, L, cap=0.30, tau=TAUWIN, cdtype=CLD, steps=6, q0=None, prec='ld',
            S=FXS, log=print):
    """Theorem D at the Newton point: every constant an upper bound, every conclusion a
    theorem about the TRUE Phi (the window enters through R3a Theorem A's `eps`).

    `prec` selects the arithmetic of the residual: 'ld' is numpy longdouble with the
    a-priori running bound, 'fx' the exact fixed point of (6b), which is what `d >= 3`
    needs."""
    t0 = time.time()
    if q0 is None:
        q0, nrec = newton_point(F, H, L, cap=cap, log=log)
    else:
        nrec = dict(d=F.d, H=H, L=L, cap=cap, supplied=True)
    D = deep_setup(F, H, L, tau, cdtype)
    hs, n, K, eps = D['hs'], 1 << L, D['K'], D['eps']
    u = ufor(rt(cdtype))

    G, _ = R3B.jacobian_at(D['gam'], np.asarray(q0, dtype=float), hs, L)
    A = np.empty((2 * H, n))
    A[0::2], A[1::2] = G.real, G.imag
    Vb, _ = np.linalg.qr(A.T)
    B = np.linalg.inv(A @ Vb)

    tabfx, etacfx = (fx_table(D['gam_mp'], D['grad'], hs, S) if prec == 'fx' else (None, 1.0))

    def run_polish(qs, A_, Vb_, B_):
        if prec == 'fx':
            Q_, h_ = fx_polish(tabfx, [fx_of(x, S) for x in qs], Vb_, B_, L, S, etacfx, steps)
            return Q_, fx_to_ld(Q_, S), h_
        q_, h_ = polish(D, qs, Vb_, B_, L, steps, cdtype)
        return None, q_, h_

    Q, q, hist = run_polish(q0, A, Vb, B)
    dseq = None
    if hist[-1] > (1e-25 if prec == 'fx' else 1e-14):
        # the chord left the linearisation (R3b sec 5.1): recompute the Jacobian a few times
        # on the deep window first, then polish again.  A no-op wherever the chord converges.
        # uncapped on purpose -- see `deep_newton`'s docstring: at d=2, H=256 the capped
        # float search stalls exactly on the cap, and every capped deep step is rejected.
        q0, dseq = deep_newton(D, q0, L)
        G, _ = R3B.jacobian_at(D['gam'], np.asarray(q0, dtype=float), hs, L)
        A[0::2], A[1::2] = G.real, G.imag
        Vb, _ = np.linalg.qr(A.T)
        B = np.linalg.inv(A @ Vb)
        Q, q, hist = run_polish(q0, A, Vb, B)
    scale = float(2 ** S)

    # the Jacobian, the basis and the preconditioner at the point that is certified.  The
    # pass runs in longdouble and is then represented in float64 for the linear algebra;
    # both roundings are charged to `kappa` below.
    G, _ = jacobian_at_p(D['gam_mp'], np.asarray(q, dtype=LD), hs, L, CLD)
    A[0::2], A[1::2] = np.asarray(G.real, dtype=float), np.asarray(G.imag, dtype=float)
    Vb, _ = np.linalg.qr(A.T)
    AV = A @ Vb
    B = np.linalg.inv(AV)
    smin = float(np.linalg.svd(A, compute_uv=False)[-1])

    # --- the residual, certified ------------------------------------------------------
    if prec == 'fx':
        Q = [fx_of(x, S) for x in q] if Q is None else Q
        PI, dpi, tauD, cD = fx_pi_enclose(Q, L, S)
        val, radA = fx_forward(tabfx, Q, PI, L, S, etacfx, dpi)
        pi = np.array([PI[b] / scale for b in range(n)])
    else:
        pi, dpi, tauD, cD = pi_enclose(q, L, rt(cdtype))
        val, radA = forward(D['tab'], q, pi, L, cdtype, D['etac'], dpi)
    r = res_vec(val).astype(np.float64)
    trunc = np.array([2 * np.pi * h * eps for h in hs])
    radvec = np.repeat(radA + trunc, 2)
    nres = float(np.linalg.norm(r)) * UP
    nrad = float(np.linalg.norm(radvec)) * UP
    Bn, Vn = frob(B), frob(Vb)
    An = frob(A)
    Vinf = float(np.sqrt((np.asarray(Vb, dtype=float) ** 2).sum(axis=1)).max()) * UP
    VtV = Vb.T @ Vb
    Vsp = math.sqrt(1.0 + frob(VtV - np.eye(2 * H))
                    + n * ufor(np.float64) * Vn * Vn) * UP
    eta = (float(np.linalg.norm(B @ r)) + Bn * nrad) * UP

    # --- kappa ------------------------------------------------------------------------
    errI = (frob(np.eye(2 * H) - B @ AV)
            + Bn * (n * ufor(np.float64) * An * Vn)
            + 2 * H * ufor(np.float64) * Bn * frob(AV)) * UP
    Ss, Ns = lip_profiles(D['gam'], np.asarray(q, dtype=float), hs, L,
                          np.asarray(pi, dtype=float))
    jtr = float(np.sqrt(sum((2 * np.pi * h * eps * (6 * K + 1)) ** 2 for h in hs))) * UP
    rho = 2 * eta
    beta = rho * Vinf
    mlo = float(np.minimum(q, 1 - q).min()) - beta
    dpi_beta = 2 * cD * L * beta / (1 - tauD) * UP if tauD < 1 else float('inf')
    Lam, ari = lam_bounds(Ss, Ns, beta, dpi, u, dpi_beta)
    r64 = ufor(np.float64) * An * UP                      # A written down in float64
    qrd = (Lam / beta) * (2.0 ** -64) * UP if beta > 0 else 0.0   # xbar in longdouble
    kap = (errI + Bn * Vsp * (ari + Lam + jtr + r64 + qrd)) * UP
    pos = bool(mlo > 0.0)
    ok = bool(kap <= 0.5 and pos and np.isfinite(dpi) and eta <= (1 - kap) * rho)

    ent = entropy(q, pi)
    Lq = float(np.abs(np.log((1 - np.asarray(q, dtype=float)) /
                             np.asarray(q, dtype=float))).max())
    dent = Lq * beta + (dpi + dpi_beta) * math.log(2) + 1e-12
    rec = dict(nrec, prec=prec, deep=dseq, tau=float(mp.nstr(tau, 5)), K=K, J=D['J'], M=D['M'], eps=eps,
               polish=hist, smin=smin, nres=nres, nrad=nrad, eta=eta, rho=rho, beta=beta,
               kappa=kap, errI=errI, Lam=Lam, arith=ari, jtrunc=jtr, Bnorm=Bn,
               r64=r64, qrd=qrd,
               Vinf=Vinf, Vsp=Vsp, dpi=dpi, dpi_beta=dpi_beta, doeblin_c=cD, doeblin_tau=tauD,
               maxdq=float(np.abs(np.asarray(q, dtype=float) - 0.5).max()),
               entropy=ent, dentropy=dent, entropy_lo=ent - dent,
               lip=float(Lam / beta) if beta > 0 else float('inf'),
               crit=float(4 * (Lam / beta) * Vinf * (nres + nrad) / smin ** 2)
               if beta > 0 else float('inf'),
               positive=pos, certified=ok, secs=time.time() - t0)
    if log:
        log('  d=%d H=%-4d L=%-3d cap %.2f %s | K=%d | ||Phi|| %.3e (+rad %.1e) | s_min %.3e | '
            'eta %.3e rho %.2e | kappa %.4e | %s | h(mu) >= %.6f | %.0fs'
            % (F.d, H, L, cap, prec, K, nres, nrad, smin, eta, rho, kap,
               'CERTIFIED' if ok else 'fails', rec['entropy_lo'], rec['secs']))
    return rec


# ======================================================================================
# (6b) the fixed-point pass: exact binary arithmetic at `S` bits, for d >= 3
# ======================================================================================
#
# At `d >= 3` the longdouble residual radius `K(eta_c + 9u) ~ 1e-16` is what stops the
# certificate, not the geometry: `kappa` is proportional to it.  Every quantity in the
# forward pass has modulus at most one, so the whole pass runs in FIXED POINT: a complex
# number is a pair of Python integers scaled by `2^S`, a multiply is an integer multiply and
# a shift, an add is exact, and one shift truncates by less than one unit in the last place.
# The certified point `xbar` is then a dyadic rational by construction, and the arithmetic
# radius is `6 K 2^-S` -- at `S = 160`, `K = 500` that is `2e-45` instead of `1e-16`.


def fx_of(x, S=FXS, dps=90):
    """Round an mpf / float / longdouble to the integer `round(x 2^S)`, via a decimal string
    so that no float64 intermediate can appear."""
    if isinstance(x, mp.mpf):
        v = x
    else:
        v = mp.mpf(np.format_float_positional(np.longdouble(x), precision=32, unique=False))
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        return int(mp.nint(v * mp.mpf(2) ** S))
    finally:
        mp.mp.dps = old


def fx_table(gam, grad, hs, S=FXS, dps=90):
    """e(h gamma_p) in fixed point; the table error is one ulp of rounding plus the
    schedule's own radius `2 pi h grad[p]`, both in units of `2^-S`."""
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        sc = mp.mpf(2) ** S
        tab = []
        for h in hs:
            row = []
            for g in gam:
                th = 2 * mp.pi * h * g
                row.append((int(mp.nint(mp.cos(th) * sc)), int(mp.nint(mp.sin(th) * sc))))
            tab.append(row)
        rc = max(float(2 * mp.pi * max(hs) * x) for x in grad) if grad else 0.0
        return tab, 1.0 + rc * float(2 ** S)
    finally:
        mp.mp.dps = old


def fx_step(Q, W, er, ei, t0, t1, S, one):
    """One emission of the backward pass, in fixed point."""
    out = []
    for b in range(len(Q)):
        ar, ai = W[t1[b]]
        cr = (er * ar - ei * ai) >> S
        ci = (er * ai + ei * ar) >> S
        dr, di = W[t0[b]]
        q1 = Q[b]
        q0 = one - q1
        out.append((((q0 * dr + q1 * cr) >> S), ((q0 * di + q1 * ci) >> S)))
    return out


def fx_stationary(Q, L, S=FXS, iters=6000):
    """pi in fixed point, normalised so that the entries sum to exactly `2^S`."""
    n = 1 << L
    one = 1 << S
    t0, t1 = [list(map(int, x)) for x in targets(L)]
    pi = [one // n] * n
    pi[0] += one - sum(pi)
    for _ in range(iters):
        nxt = [0] * n
        for b in range(n):
            q1 = Q[b]
            nxt[t0[b]] += (pi[b] * (one - q1)) >> S
            nxt[t1[b]] += (pi[b] * q1) >> S
        s = sum(nxt)
        if s != one:
            nxt[max(range(n), key=lambda i: nxt[i])] += one - s
        if max(abs(a - b) for a, b in zip(nxt, pi)) <= n:
            pi = nxt
            break
        pi = nxt
    return pi


def fx_pi_enclose(Q, L, S=FXS, cmax=4000):
    """(pi, delta) with `||pi - pi_true||_1 <= delta`, the same Doeblin bound as
    `pi_enclose` but with the residual measured in exact fixed point."""
    n = 1 << L
    one = 1 << S
    t0, t1 = [list(map(int, x)) for x in targets(L)]
    pi = fx_stationary(Q, L, S)
    doeb = doeblin_const(np.array([x / float(one) for x in Q]), L)
    if doeb <= 0.0:
        return pi, float('inf'), 1.0, 0
    tauL = 1.0 - doeb
    c = 1
    while c < cmax and tauL ** c > 0.5:
        c += 1
    tau = tauL ** c
    if tau >= 1.0 - 1e-12:
        return pi, float('inf'), tau, c
    v = list(pi)
    for _ in range(c * L):
        nxt = [0] * n
        for b in range(n):
            q1 = Q[b]
            nxt[t0[b]] += (v[b] * (one - q1)) >> S
            nxt[t1[b]] += (v[b] * q1) >> S
        v = nxt
    move = sum(abs(a - b) for a, b in zip(v, pi)) / float(one)
    arith = c * L * n * 2.0 ** -S
    return pi, (move + arith) / (1.0 - tau) * UP, tau, c


def fx_forward(tab, Q, PI, L, S=FXS, etac=1.0, dpi=0.0):
    """Phi~_h in fixed point, with a rigorous radius.

    Each emission adds at most `2` ulp of truncation per component and `etac` ulp from the
    constant table, against factors of modulus at most one, so after `K` emissions the
    modulus error is below `6 K (1 + etac) 2^-S`; the contraction against `pi` is accumulated
    in exact integers and shifted once."""
    n = 1 << L
    one = 1 << S
    t0, t1 = [list(map(int, x)) for x in targets(L)]
    K = len(tab[0])
    vals, mw = [], 0.0
    for row in tab:
        W = [(one, 0)] * n
        for p in range(K - 1, -1, -1):
            er, ei = row[p]
            W = fx_step(Q, W, er, ei, t0, t1, S, one)
        ar = sum(PI[b] * W[b][0] for b in range(n)) >> S
        ai = sum(PI[b] * W[b][1] for b in range(n)) >> S
        vals.append(complex(ar / float(one), ai / float(one)))
        mw = max(mw, max(max(abs(x), abs(y)) for x, y in W) / float(one))
    rad = (6.0 * K * (1.0 + etac) + 2.0) * 2.0 ** -S + dpi * min(1.0, 1.4143 * mw)
    return np.array(vals), float(rad) * UP


def fx_to_ld(Q, S=FXS):
    """The fixed-point point as an EXACT longdouble array, to within `2^-64`.

    Two 52-bit pieces, each exact in float64, recombined in longdouble: nothing goes through
    a float64 approximation of the whole number.  The Jacobian is evaluated there rather than
    at `Q/2^S` itself, and Theorem D is charged `(Lambda/beta) 2^-64` for the difference."""
    hi = np.array([int(x >> (S - 52)) for x in Q], dtype=np.float64)
    lo = np.array([int((x >> (S - 104)) - (int(x >> (S - 52)) << 52)) for x in Q],
                  dtype=np.float64)
    return hi.astype(LD) * LD(2.0) ** -52 + lo.astype(LD) * LD(2.0) ** -104


def fx_polish(tab, Q, Vb, B, L, S=FXS, etac=1.0, steps=6, log=None):
    """The chord iteration in fixed point: the step is float64 (it only has to point the
    right way), the point and the residual are exact binary."""
    hist = []
    best, bQ = None, list(Q)
    for _ in range(steps):
        PI = fx_stationary(Q, L, S)
        val, rad = fx_forward(tab, Q, PI, L, S, etac)
        r = res_vec(val)
        nrm = float(np.linalg.norm(r))
        hist.append(nrm)
        if best is None or nrm < best:
            best, bQ = nrm, list(Q)
        else:
            break
        xi = -(B @ r)
        dq = Vb @ xi
        Q = [Q[b] + fx_of(dq[b], S) for b in range(len(Q))]
        if min(min(x, (1 << S) - x) for x in Q) <= 0:
            break
    return bQ, hist


# ======================================================================================
# self-checks
# ======================================================================================
def selfchecks(log=print):
    log('=== self-checks ===')
    F2 = Field([1, -2, -1], '1+sqrt2')
    F3 = Field(FAMILY[1])
    F4 = Field(FAMILY[2])
    rng = np.random.default_rng(20260828)

    # (1) the longdouble forward pass reproduces R3b's, hence r1a_enclose's
    L, H = 6, 4
    D = deep_setup(F2, H, L, mp.mpf('1e-13'))
    q = 0.5 + 0.05 * rng.normal(size=1 << L)
    pi = stationary(q, L)
    val, rad = forward(D['tab'], q, pi, L, CLD, D['etac'])
    ref = R3B.forward(D['gam'], q, D['hs'], L)
    err = float(np.abs(np.array([complex(x) for x in val]) - ref).max())
    check('longdouble forward pass matches r3b_jacobian.forward', err < 1e-12,
          'max diff %.2e' % err)

    # (2) the fixed-point pass agrees with the longdouble one to the longdouble radius
    tabfx, etacfx = fx_table(D['gam_mp'], D['grad'], D['hs'], FXS)
    Q = [fx_of(x, FXS) for x in q]
    qd = np.array([x / float(2 ** FXS) for x in Q])
    PI = fx_stationary(Q, L, FXS)
    vfx, rfx = fx_forward(tabfx, Q, PI, L, FXS, etacfx)
    pid = np.array([x / float(2 ** FXS) for x in PI])
    vld, rld = forward(D['tab'], qd, pid, L, CLD, D['etac'])
    err = float(np.abs(np.array([complex(x) for x in vld]) - vfx).max())
    check('fixed point and longdouble agree inside the longdouble radius',
          err <= rld + rfx + 1e-17, 'diff %.2e vs radius %.2e' % (err, rld))
    check('the fixed-point radius is the smaller by ten orders', rfx < 1e-10 * rld,
          '%.2e vs %.2e' % (rfx, rld))

    # (3) fx_of is a rounding: |x - Q/2^S| <= 2^-S
    xs = [0.5, 0.3141592653589793, 0.999, 1e-9]
    ok = all(abs(x - fx_of(x) / float(2 ** FXS)) <= 2.0 ** -FXS * 2 for x in xs)
    check('fx_of rounds to the fixed-point grid', ok)

    # (4) pi_enclose: the bound covers the drift of a much longer power iteration
    qq = 0.5 + 0.1 * rng.normal(size=1 << 8)
    pih, dpi, tauD, cD = pi_enclose(qq, 8)
    t0, t1 = targets(8)
    v = pih.copy()
    for _ in range(20000):
        v = apply_P(v, np.asarray(qq, dtype=LD), t0, t1, LD)
    drift = float(np.abs(v - pih).sum())
    check('the Doeblin enclosure of pi covers a 20000-step drift',
          drift <= dpi and np.isfinite(dpi), 'drift %.2e <= delta %.2e (c=%d)' % (drift, dpi, cD))
    check('and pi_hat is stationary to the same order',
          float(np.abs(apply_P(pih, np.asarray(qq, dtype=LD), t0, t1, LD) - pih).sum()) < 1e-15)

    # (4b) the Doeblin dynamic programme is exact
    for L in (3, 4):
        n, mask = 1 << L, (1 << L) - 1
        qq = np.clip(0.5 + 0.2 * rng.normal(size=n), 0.05, 0.95)
        P = np.zeros((n, n))
        for b in range(n):
            P[b, (b << 1) & mask] += 1 - qq[b]
            P[b, ((b << 1) | 1) & mask] += qq[b]
        brute = float(np.linalg.matrix_power(P, L).min(axis=0).sum())
        got = doeblin_const(qq, L)
        crude = (2 * float(np.minimum(qq, 1 - qq).min())) ** L
        # `doeblin_const` shaves 1ppb off the DP so that it is sound against the float
        # rounding of the products; so the test is that it is a LOWER bound on the true
        # constant, tight to that shave, and beats the crude `(2m)^L`.
        check('L=%d: the Doeblin dynamic programme is the exact constant' % L,
              brute * (1 - 1e-8) <= got <= brute * (1 + 1e-12) and got >= crude,
              'DP %.12f vs brute %.12f (shave %.1e), crude %.2e'
              % (got, brute, 1 - got / brute, crude))

    # (5) Proposition E dominates the measured variation of the Jacobian
    for F, H, L in ((F2, 4, 6), (F3, 4, 6), (F4, 4, 6)):
        J, M = F.need(H, TAUFAST)
        gam = R3B.schedule(F, J, M)
        hs = list(range(1, H + 1))
        n = 1 << L
        q = np.full(n, 0.5) + 0.02 * rng.normal(size=n)
        pi = np.asarray(stationary(q, L), dtype=float)
        Ss, Ns = lip_profiles(gam, q, hs, L, pi)
        beta = 1e-6
        Lam, _ = lam_bounds(Ss, Ns, beta, 0.0, ufor(np.float64), 2 * 40 * L * beta)
        G0, _ = R3B.jacobian_at(gam, q, hs, L)
        A0 = np.empty((2 * H, n))
        A0[0::2], A0[1::2] = G0.real, G0.imag
        worst = 0.0
        for _ in range(3):
            w = rng.choice([-1.0, 1.0], size=n)
            G1, _ = R3B.jacobian_at(gam, q + beta * w, hs, L)
            A1 = np.empty_like(A0)
            A1[0::2], A1[1::2] = G1.real, G1.imag
            worst = max(worst, float(np.linalg.norm(A1 - A0, 'fro')))
        check('d=%d: Proposition E dominates the measured Jacobian variation' % F.d,
              Lam >= worst, 'bound %.3e vs measured %.3e (x%.1e)'
              % (Lam, worst, Lam / max(worst, 1e-300)))

    # (6) Theorem D on a map whose zero is known: Phi(x) = (x1^2 - 2, x2 - x1^3) in R^3
    def Psi(x):
        return np.array([x[0] ** 2 - 2.0, x[1] - x[0] ** 3])

    def DPsi(x):
        return np.array([[2 * x[0], 0.0, 0.0], [-3 * x[0] ** 2, 1.0, 0.0]])
    xb = np.array([1.41421, 2.82842, 0.3])
    A = DPsi(xb)
    Vb, _ = np.linalg.qr(A.T)
    B = np.linalg.inv(A @ Vb)
    eta = float(np.linalg.norm(B @ Psi(xb)))
    rho = 2 * eta
    beta = rho * float(np.sqrt((Vb ** 2).sum(axis=1)).max())
    lam = 2 * (2 + 3 * 2 * (abs(xb[0]) + beta))                   # Lipschitz of DPsi
    kap = float(np.linalg.norm(np.eye(2) - B @ (A @ Vb))) + \
        float(np.linalg.norm(B)) * lam * beta
    x = xb.copy()
    for _ in range(60):
        x = x - Vb @ (B @ Psi(x))
    check('Theorem D: the predicted ball contains the fixed point',
          kap < 1 and float(np.linalg.norm(Vb.T @ (x - xb))) <= eta / (1 - kap),
          'kappa %.3e, ||xi*|| %.3e <= %.3e' % (kap, float(np.linalg.norm(Vb.T @ (x - xb))),
                                                eta / (1 - kap)))
    check('and the limit is an exact zero', float(np.abs(Psi(x)).max()) < 1e-14,
          '|Psi| %.2e' % float(np.abs(Psi(x)).max()))

    # (7) row-scaling invariance of eta and kappa (the point of Theorem D)
    S = np.diag([1e-7, 1e5])
    A2 = S @ A
    B2 = np.linalg.inv(A2 @ Vb)
    eta2 = float(np.linalg.norm(B2 @ (S @ Psi(xb))))
    check('eta is invariant under row scaling of Phi', abs(eta2 - eta) <= 1e-9 * eta,
          'rel %.2e' % (abs(eta2 - eta) / eta))

    # (8) the certificate at a rung that is cheap, and its measure really is flat
    rec = certify(F2, 8, 8, cap=0.30, prec='fx', log=None)
    check('d=2, H=8, L=8 certifies', rec['certified'],
          'kappa %.3e, h(mu) >= %.6f' % (rec['kappa'], rec['entropy_lo']))
    check('and the certified entropy clears the Ledrappier-Young floor',
          rec['entropy_lo'] > 0.440687, 'margin %.6f' % (rec['entropy_lo'] - 0.440687))

    # (9) the fixed-point engine against r1a_enclose's mpmath INTERVAL forward pass, on a
    #     circulation whose weights are exact rationals -- two arithmetics sharing no code
    keep = mp.mp.dps
    import r1a_enclose as RE
    mp.mp.dps = keep
    Lc, Jc, Mc, hsc = 5, 20, 20, [1, 3, 7]
    circ = RE.circ_bernoulli(Lc, "2/5")
    box = RE.phi_iv(circ, hsc, Jc, Mc)
    mp.mp.dps = keep
    Dc = deep_setup(F2, max(hsc), Lc, mp.mpf('1e-13'), CLD)
    gm, gr = sched_mp(F2, Jc, Mc)
    tb, ec = fx_table(gm, gr, hsc, FXS)
    Qc = [fx_of(mp.mpf(2) / 5, FXS)] * (1 << Lc)
    PIc = fx_stationary(Qc, Lc, FXS)
    vfx, rc = fx_forward(tb, Qc, PIc, Lc, FXS, ec)
    off = max(abs(complex(v) - RE.box_mid(b)) - RE.box_radius(b) for v, b in zip(vfx, box))
    check("the fixed-point Phi lies in r1a_enclose's mpmath interval box",
          off <= rc, 'h = %s, worst overshoot %.2e against radius %.2e' % (hsc, off, rc))
    log('# %d ok, %d FAILED' % (NCHECKS[0] - len(FAIL), len(FAIL)))
    return not FAIL


# ======================================================================================
# (7) runners
# ======================================================================================
GRID = [
    # (d, H, L, cap, prec)   -- L is R3b's L*(H) raised where the cap or the memory needs it,
    # `prec` the arithmetic of the residual: 'fx' where it is affordable, 'ld' at L = 14.
    (2, 8, 8, 0.30, 'fx'), (2, 16, 8, 0.30, 'fx'), (2, 32, 10, 0.30, 'fx'),
    (2, 64, 12, 0.30, 'fx'), (2, 128, 14, 0.30, 'ld'), (2, 256, 14, 0.30, 'ld'),
    (3, 8, 8, 0.25, 'fx'), (3, 16, 8, 0.25, 'fx'), (3, 32, 8, 0.25, 'fx'),
    (3, 64, 10, 0.25, 'fx'), (3, 128, 12, 0.25, 'fx'),
    (4, 8, 8, 0.25, 'fx'), (4, 16, 8, 0.25, 'fx'), (4, 32, 10, 0.25, 'fx'),
    (4, 64, 12, 0.25, 'fx'),
]


def run_grid(log=print, cases=None, out=None):
    """The certified frontier: one row of Theorem D per rung."""
    rows = []
    for d, H, L, cap, prec in (cases or GRID):
        try:
            rows.append(certify(Field(FAMILY[d - 2]), H, L, cap=cap, prec=prec, log=log))
        except Exception as exc:                                       # noqa: BLE001
            log('  d=%d H=%d L=%d raised %r' % (d, H, L, exc))
        if out:
            json.dump(rows, open(out, 'w'), indent=1)
    return rows


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'all'
    out = {}
    if os.path.exists(OUT):
        try:
            out = json.load(open(OUT))
        except Exception:
            out = {}
    if cmd in ('checks', 'all'):
        out['checks'] = bool(selfchecks())
    if cmd in ('grid', 'all'):
        print('=== the certified frontier ===')
        out['grid'] = run_grid(out=os.path.join(HERE, 'r3c_grid.json'))
    json.dump(out, open(OUT, 'w'), indent=1)
    print('-> %s' % OUT)
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.exit(main())
