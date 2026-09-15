#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R3b of `plan-BB61-counterexample.html`: `DPhi` at Bernoulli, its structure, and the
small divisor that decides the lane.

sec 7.3 seeks `mu` in the memory-`L` Markov family with `Phi_h(mu) = 0` for `h <= H` by
Newton from `Bern_{1/2}`, and gates the lane on whether `residual / s_{H,L}` stays bounded
in `H`, `s_{H,L}` the smallest singular value of `DPhi`.  R3a
(`note-1061-R3a.html`) showed the residual is *rank two* at `d >= 4` -- it is
`|Phi_1|` in two coordinates and below `5.6e-6` in the other `2H-2` -- so that ratio is an
upper bound loose by the condition number, and replaced the gate by

  G-3a  is  ||DPhi^+ r||  bounded in H, for the certified residual r?
  G-3b  is there a direction moving Phi_1 at first order while moving Phi_h, 2<=h<=H,
        by o(|Phi_1|)?

Both are answered by one number, computed here.

THE DERIVATIVE, IN CLOSED FORM.  Parametrise the memory-`L` family by its conditionals
`q(b) = 1/2 + t u(b)`, `b` an `L`-block.  Bernoulli is `t = 0`, interior, so positivity is
free.  The perturbed measure is the equilibrium state of a potential perturbed by the local
`psi_k(omega) = 2 u(b_k)(2 omega_k - 1)`, `b_k = (omega_{k-L},...,omega_{k-1})`, and
`E psi = 0` under `Bern_{1/2}`, so linear response gives
`d/dt int f dmu_t = sum_k E[f psi_k]`.  With `f = e(hF)` and `F = sum_p gamma_p omega_p`
everything factorises, and

    d Phi_h / dt  =  < g_h , u >_{L^2(pi)},

    g_h(b)  =  sum_k ( e(h gamma_k) - 1 ) P_k  e( h sum_{j=1..L} gamma_{k-L+j-1} b_j ),
    P_k     =  prod_{p not in [k-L, k]} phi(h gamma_p),      phi(x) = (1 + e(x))/2.

`P_k` is a product of moduli `<= 1` computed as prefix times suffix, never a quotient, so no
`phi` near zero can spoil it.  The `b`-dependence of the `k`-th term is a *character* on the
block, `prod_{j : b_j = 1} e(h gamma_{k-L+j-1})`, of Kronecker rank one -- which is the exact
form of the sparsity sec 7.3 expects from M7 Thm 8: where the reduced weights
`<h gamma_p>` are exponentially small (R3a Theorem B: everywhere outside two bands), the
character is trivial *and* `e(h gamma_k) - 1` vanishes, so the term contributes neither
structure nor size.

At `L = 0` the formula is `sum_k (e(h gamma_k) - 1) prod_{i != k} phi(h gamma_i)`, which is
`d/dp` of the Erdos product -- the check that fixes every constant.

THE SMALL DIVISOR.  Since `r` is essentially supported on `(Re Phi_1, Im Phi_1)`, the Newton
step `DPhi^+ r` has norm `~ |Phi_1| / lambda_1(H)` with

    lambda_1(H)  :=  dist( g_1 , span{ Re g_h, Im g_h : 2 <= h <= H } )   in L^2(pi),

the part of the first mode's sensitivity that the other `2H-2` constraints leave free.  That
is G-3b's object, it is what `s_{H,L}` is a (loose) proxy for, and it is one QR per `(H,L,d)`.

Usage:  python3 r3b_jacobian.py checks | spec | g3 | sparse | table | all
"""
import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from r3a_degree import Field, FAMILY, bern_cert                          # noqa: E402

OUT = os.path.join(HERE, 'r3b_jacobian.json')
FAIL = []
NCHECKS = [0]


def check(name, cond, extra=""):
    NCHECKS[0] += 1
    print("    [%s] %s%s" % ('ok ' if cond else 'FAIL', name, ('  ' + extra) if extra else ''))
    if not cond:
        FAIL.append(name)


# ======================================================================================
# the emission schedule, in position order  -M .. J   (r1a_enclose._steps, generalised)
# ======================================================================================
def schedule(F, J, M):
    """gamma_p for p = -M..J in increasing p: past first, then future.

    `F = (a-1) sum_{k>=1} w_k a^-k - sum_{m>=0} c_m w_-m`, so gamma_{-m} = -c_m and
    gamma_k = (a-1) a^-k.  Same signs as `r1a_enclose._steps`, opposite listing order."""
    a = float(F.alpha)
    c, _ = F.c_m(M + 1)
    past = [-float(c[m]) for m in range(M, -1, -1)]          # p = -M .. 0
    fut = [(a - 1.0) * a ** (-k) for k in range(1, J + 1)]    # p = 1 .. J
    return np.array(past + fut)


def forward(gam, q, hs, L):
    """Phi~_h for the memory-L chain with conditionals q, by r1a_enclose's forward pass.

    Positions are consumed from the last (largest p) to the first, which is the backward
    recursion in time; `pi` is the stationary distribution of the chain, solved exactly."""
    n = 1 << L
    mask = n - 1
    b = np.arange(n, dtype=np.int64)
    t0, t1 = ((b << 1) & mask), (((b << 1) | 1) & mask)
    pi = stationary(q, L)
    hs = np.asarray(hs, dtype=float)
    W = np.ones((hs.size, n), dtype=complex)
    q0, q1 = (1 - q)[None, :], q[None, :]
    for p in range(len(gam) - 1, -1, -1):
        e1 = np.exp(2j * np.pi * hs * gam[p])[:, None]
        W = q0 * W[:, t0] + q1 * (e1 * W[:, t1])
    return W @ pi


def stationary(q, L, iters=20000, tol=1e-15):
    """Stationary distribution of the order-L de Bruijn chain with P(1|b) = q[b]."""
    n = 1 << L
    mask = n - 1
    b = np.arange(n, dtype=np.int64)
    t0, t1 = ((b << 1) & mask), (((b << 1) | 1) & mask)
    pi = np.full(n, 1.0 / n)
    for _ in range(iters):
        nxt = np.zeros(n)
        np.add.at(nxt, t0, pi * (1 - q))
        np.add.at(nxt, t1, pi * q)
        if np.abs(nxt - pi).max() < tol:
            pi = nxt
            break
        pi = nxt
    return pi / pi.sum()


# ======================================================================================
# the Jacobian at Bernoulli
# ======================================================================================
def character(z):
    """All 2^L values of prod_{j : b_j = 1} z_j, indexed by b = sum_j b_j 2^{L-j}."""
    v = np.ones(1, dtype=complex)
    for zj in z:
        w = np.empty(2 * v.size, dtype=complex)
        w[0::2] = v
        w[1::2] = v * zj
        v = w
    return v


def g_row(gam, h, L):
    """g_h over all 2^L blocks (the L^2(pi) representer of dPhi_h/dt at Bernoulli)."""
    K = len(gam)
    ph = (1.0 + np.exp(2j * np.pi * h * gam)) / 2.0            # phi(h gamma_p)
    pre = np.ones(K + 1, dtype=complex)                        # pre[m] = prod_{p<m} phi
    for p in range(K):
        pre[p + 1] = pre[p] * ph[p]
    suf = np.ones(K + 2, dtype=complex)                        # suf[m] = prod_{p>=m} phi
    for p in range(K - 1, -1, -1):
        suf[p] = suf[p + 1] * ph[p]
    g = np.zeros(1 << L, dtype=complex)
    for k in range(K):
        lead = np.exp(2j * np.pi * h * gam[k]) - 1.0
        if lead == 0:
            continue
        P = pre[max(k - L, 0)] * suf[k + 1]
        z = [np.exp(2j * np.pi * h * gam[k - L + j - 1]) if 0 <= k - L + j - 1 < K else 1.0
             for j in range(1, L + 1)]
        g += (lead * P) * character(z)
    return g


def jacobian(F, H, L, J=None, M=None, hs=None):
    """The real 2H x 2^L matrix of dPhi_h/du in the L^2(pi)-orthonormal coordinates,
    together with the Bernoulli residual r = (Re Phi_h, Im Phi_h) it has to cancel."""
    if J is None or M is None:
        Jn, Mn = F.need(H, mp_tau())
        J = Jn if J is None else J
        M = Mn if M is None else M
    gam = schedule(F, J, M)
    hs = list(range(1, H + 1)) if hs is None else list(hs)
    n = 1 << L
    A = np.empty((2 * len(hs), n))
    r = np.empty(2 * len(hs))
    s = n ** -0.5
    for i, h in enumerate(hs):
        g = g_row(gam, h, L)
        A[2 * i] = s * g.real
        A[2 * i + 1] = s * g.imag
        ph = np.prod((1.0 + np.exp(2j * np.pi * h * gam)) / 2.0)
        r[2 * i], r[2 * i + 1] = ph.real, ph.imag
    return A, r, (J, M, gam)


def mp_tau():
    import mpmath as mp
    return mp.mpf('1e-13')


# ======================================================================================
# the two gates
# ======================================================================================
def gates(F, H, L, A=None, r=None):
    """s_{H,L}, ||DPhi^+ r||, lambda_1(H), and the looseness of sec 7.3's own statistic."""
    if A is None:
        A, r, _ = jacobian(F, H, L)
    sv = np.linalg.svd(A, compute_uv=False)
    smin, smax = float(sv[-1]), float(sv[0])
    v, *_ = np.linalg.lstsq(A, -r, rcond=None)
    step = float(np.linalg.norm(v))
    stepinf = float(np.abs(v).max() * (1 << L) ** 0.5)      # max |dq(b)| ; must stay < 1/2
    # lambda_1 = the part of g_1 that the constraints h >= 2 leave free
    B = A[2:]
    g1 = A[:2]
    if B.size:
        Q, _ = np.linalg.qr(B.T)                       # orthonormal basis of row space
        free = g1.T - Q @ (Q.T @ g1.T)
        lam1 = float(np.linalg.svd(free, compute_uv=False)[-1])
    else:
        lam1 = float(np.linalg.svd(g1, compute_uv=False)[-1])
    rn = float(np.linalg.norm(r))
    r1 = float(np.linalg.norm(r[:2]))
    return dict(H=H, L=L, d=F.d, smin=smin, smax=smax, cond=smax / max(smin, 1e-300),
                rank=int((sv > sv[0] * 1e-13).sum()), nres=rn, nres1=r1,
                step=step, stepinf=stepinf, naive=rn / max(smin, 1e-300),
                loose=(rn / max(smin, 1e-300)) / max(step, 1e-300),
                lam1=lam1, step1=r1 / max(lam1, 1e-300))


# ======================================================================================
def selfchecks(log=print):
    log('=== self-checks ===')
    F2 = Field([1, -2, -1], '1+sqrt2')
    F3 = Field(FAMILY[1])
    F4 = Field(FAMILY[2])

    # (1) the forward pass reproduces r1a_enclose at 1+sqrt2
    import mpmath as mp
    keep = mp.mp.dps
    import r1a_enclose as R
    mp.mp.dps = keep
    L, J, M = 6, 20, 20
    cB = R.circ_bernoulli(L, "1/2")
    vals, _ = R.phi_fl(cB, [1, 3, 7], J, M)
    gam = schedule(F2, J, M)
    mine = forward(gam, np.full(1 << L, 0.5), [1, 3, 7], L)
    check('forward pass matches r1a_enclose.phi_fl at 1+sqrt2, Bernoulli',
          np.abs(mine - vals).max() < 1e-12, 'max diff %.2e' % np.abs(mine - vals).max())
    rng = np.random.default_rng(20260828)
    w = rng.integers(0, 2, 9)
    cW = R.circ_from_word(L, [int(x) for x in w])
    cM = R.circ_mix([("4/5", cW), ("1/5", cB)])
    vals, _ = R.phi_fl(cM, [1, 3, 7], J, M)
    mine = forward(gam, np.array([float(x) for x in cM.q]), [1, 3, 7], L)
    check('forward pass matches r1a_enclose.phi_fl on a mixed circulation',
          np.abs(mine - vals).max() < 1e-10, 'max diff %.2e' % np.abs(mine - vals).max())

    # (2) the L=0 formula is the derivative of the Erdos product
    gam = schedule(F2, 30, 30)
    g0 = g_row(gam, 5, 0)[0]
    ph = (1.0 + np.exp(2j * np.pi * 5 * gam)) / 2.0
    exact = sum((np.exp(2j * np.pi * 5 * gam[k]) - 1.0) * np.prod(np.delete(ph, k))
                for k in range(len(gam)))
    check('L=0: g_h is d/dp of the Erdos product', abs(g0 - exact) < 1e-12 * abs(exact),
          'rel %.2e' % (abs(g0 - exact) / abs(exact)))

    # (3) THE CHECK: finite differences against the exact chain, at three degrees
    for F, L, J, M, hs in ((F2, 5, 18, 18, (1, 3, 7)), (F3, 5, 20, 40, (1, 2, 5)),
                           (F4, 4, 20, 60, (1, 2, 3))):
        gam = schedule(F, J, M)
        A = np.array([g_row(gam, h, L) for h in hs])
        rng = np.random.default_rng(4242 + F.d)
        u = rng.normal(size=1 << L)
        u -= u.mean() * 0                                  # no constraint on u
        pred = (A @ u) / (1 << L)                          # <g_h, u>_{L^2(pi)}
        t = 1e-5
        fp = forward(gam, np.full(1 << L, 0.5) + t * u, hs, L)
        fm = forward(gam, np.full(1 << L, 0.5) - t * u, hs, L)
        fd = (fp - fm) / (2 * t)
        rel = np.abs(fd - pred).max() / np.abs(pred).max()
        check('d=%d, L=%d: closed-form dPhi matches central differences' % (F.d, L),
              rel < 2e-8, 'max rel %.2e' % rel)

    # (4) a pure Bernoulli direction: u constant reproduces d/dp of the product
    gam = schedule(F3, 20, 40)
    L = 5
    g = g_row(gam, 2, L)
    ph = (1.0 + np.exp(2j * np.pi * 2 * gam)) / 2.0
    dP = sum((np.exp(2j * np.pi * 2 * gam[k]) - 1.0) * np.prod(np.delete(ph, k))
             for k in range(len(gam)))
    check('u = const recovers the Bernoulli(p) derivative at d=3',
          abs(g.mean() - dP) < 1e-10 * abs(dP), 'rel %.2e' % (abs(g.mean() - dP) / abs(dP)))

    # (5) the residual assembled by `jacobian` is R3a's certified one
    for F in (F2, F3, F4):
        A, r, _ = jacobian(F, 4, 6)
        lo, hi, _, _ = bern_cert(F, 1)
        got = math.hypot(r[0], r[1])
        check('d=%d: row 1 of the residual is the certified |Phi_1|' % F.d,
              float(lo) * (1 - 1e-9) <= got <= float(hi) * (1 + 1e-9),
              '%.10e vs [%.10e, %.10e]' % (got, float(lo), float(hi)))

    # (6) the sparsity claim: the b-dependent part lives where the weights do
    gam = schedule(F2, 40, 40)
    L = 8
    h = 1393                                                # a rung of 1,3,7,17,41,...
    red = np.abs(gam * h - np.round(gam * h))
    band = red > 1e-3
    pos = np.arange(-40, 41)
    act = sorted(pos[band].tolist())
    check('M7 sec 5: at h = 1393 the profile is supported on [-16,-2] u [2,16]',
          act == [x for x in range(-16, -1)] + [x for x in range(2, 17)],
          '%d positions, %d..%d and %d..%d' % (len(act), act[0], act[14], act[15], act[-1]))
    # and the k-mass follows: 90% of it sits on a bounded number of positions
    ph = (1.0 + np.exp(2j * np.pi * h * gam)) / 2.0
    pre = np.concatenate([[1], np.cumprod(ph)])
    suf = np.concatenate([np.cumprod(ph[::-1])[::-1], [1], [1]])
    lead = np.abs(np.exp(2j * np.pi * h * gam) - 1.0)
    wgt = np.array([lead[k] * abs(pre[max(k - L, 0)] * suf[k + 1]) for k in range(len(gam))])
    srt = np.sort(wgt)[::-1]
    n90 = int(np.searchsorted(np.cumsum(srt), 0.9 * wgt.sum()) + 1)
    check('and 90% of the k-mass of g_h sits on at most a third of the positions',
          n90 <= len(gam) // 3, '%d of %d' % (n90, len(gam)))

    # (7) lambda_1 <= smallest singular value of the whole g_1 pair, and >= 0
    G = gates(Field(FAMILY[0]), 8, 8)
    check('lambda_1 <= ||g_1|| and the step it predicts is <= the naive one',
          0 <= G['lam1'] <= np.linalg.norm(jacobian(Field(FAMILY[0]), 8, 8)[0][:2])
          and G['step'] <= G['naive'] * (1 + 1e-9),
          'lam1 %.3e, step %.3e, naive %.3e' % (G['lam1'], G['step'], G['naive']))
    log('# %d ok, %d FAILED' % (NCHECKS[0] - len(FAIL), len(FAIL)))
    return not FAIL


def run_newton(F, H, L, iters=5, log=print):
    """The simplified (chord) Newton iteration Newton-Kantorovich actually uses:
    `u <- u - DPhi(Bern)^+ Phi(mu_u)`, with `Phi` evaluated by the exact forward pass on
    the same window the Jacobian differentiates.  Float, not certified -- this is R3b's
    evidence that the linear step is real, not R3c's theorem.  The truncation floor is
    `2 pi H eps(J,M) <= 1e-13`, below which the residual is the window's, not F's."""
    A, r0, (J, M, gam) = jacobian(F, H, L)
    hs = list(range(1, H + 1))
    n = 1 << L
    u = np.zeros(n)
    seq, sup = [], []
    for it in range(iters + 1):
        q = 0.5 + (n ** 0.5) * u
        if q.min() <= 0 or q.max() >= 1:
            log('    positivity lost at iteration %d' % it)
            break
        ph = forward(gam, q, hs, L)
        r = np.empty(2 * H)
        r[0::2], r[1::2] = ph.real, ph.imag
        seq.append(float(np.linalg.norm(r)))
        sup.append(float(np.abs(ph).max()))
        if it == iters:
            break
        dv, *_ = np.linalg.lstsq(A, -r, rcond=None)
        u = u + dv
    return dict(d=F.d, H=H, L=L, resid=seq, supPhi=sup,
                stepinf=float(np.abs(u).max() * n ** 0.5),
                stepL2=float(np.linalg.norm(u)),
                floor=float(2 * np.pi * H * float(F.eps(J, M))))


def reach(F, H, L, cap=0.25, theta=1e-8, iters=30, log=None):
    """Truncated, damped chord Newton: how far down can the residual be driven from
    Bernoulli inside the memory-L family, with a bounded step?

    The pseudo-inverse is truncated at `theta * s_max` (float64 loses at most eight digits
    there, so nothing below it is signal), and a step is halved until it does not increase
    `||Phi||`.  Both are reported, because a run that needs the truncation is a run whose
    remaining residual lies in `DPhi`'s near-null space -- which is the honest form of
    sec 7.3's own gate."""
    A, r0, (J, M, gam) = jacobian(F, H, L)
    U, S, Vt = np.linalg.svd(A, full_matrices=False)
    keep = S > theta * S[0]
    hs = list(range(1, H + 1))
    n = 1 << L
    floor = 2 * np.pi * H * float(F.eps(J, M))

    def resid(u):
        q = 0.5 + (n ** 0.5) * u
        if q.min() <= 1e-12 or q.max() >= 1 - 1e-12:
            return None, None
        ph = forward(gam, q, hs, L)
        r = np.empty(2 * H)
        r[0::2], r[1::2] = ph.real, ph.imag
        return r, ph

    u = np.zeros(n)
    r, ph = resid(u)
    seq = [float(np.linalg.norm(r))]
    it = 0
    for it in range(1, iters + 1):
        c = (U.T @ r)[keep] / S[keep]
        v = -(Vt[keep].T @ c)
        if np.linalg.norm(v) > cap:
            v *= cap / np.linalg.norm(v)
        ok = False
        for _ in range(10):
            rn, phn = resid(u + v)
            if rn is not None and np.linalg.norm(rn) < seq[-1]:
                u, r, ph, ok = u + v, rn, phn, True
                seq.append(float(np.linalg.norm(r)))
                break
            v = v / 2
        if not ok or seq[-1] < 3 * floor:
            break
    lim = ('iterations' if it >= iters else
           ('step' if seq[-1] >= 30 * floor else 'floor'))
    return dict(d=F.d, H=H, L=L, iters=it, resid=seq, floor=float(floor), limit=lim,
                final=seq[-1], sup=float(np.abs(ph).max()),
                stepinf=float(np.abs(u).max() * n ** 0.5),
                stepL2=float(np.linalg.norm(u)),
                trunc=int((~keep).sum()), smin=float(S[-1]), smax=float(S[0]),
                reached=bool(seq[-1] < 30 * floor))


def jacobian_at(gam, q, hs, L):
    """The EXACT Jacobian at any memory-L chain, by forward-backward linear response.

    At a general `q` the process is not i.i.d. and there is no product formula, but the
    equilibrium-state derivative is still `d/dt int f dmu_t = sum_k E_mu[f psi_k]` with
    `psi_k = u(b_k) [ omega_k/q(b_k) - (1-omega_k)/(1-q(b_k)) ]`, which already contains the
    change of the stationary distribution -- no `dpi/dq` is needed.  Conditioning at
    position `k` on the preceding block splits the expectation into the two emissions, and

        dPhi_h/du(b) = sum_p V_p[b] ( e(h gamma_p) W_{p+1}[t1[b]] - W_{p+1}[t0[b]] ),

    `W` the backward pass of `forward` and `V` the forward pass of phase-weighted block
    measure, `V_{-M} = pi`.  `sum_b V_{J+1}[b] = Phi_h` is the check that ties the two.
    Returns (G, phi) with `dPhi_h = sum_b G[h, b] u(b)` in the raw `u` coordinate."""
    n = 1 << L
    mask = n - 1
    b = np.arange(n, dtype=np.int64)
    t0, t1 = ((b << 1) & mask), (((b << 1) | 1) & mask)
    p0, p1 = (b >> 1), ((b >> 1) | (n >> 1))          # the two predecessors of block b
    eps = b & 1                                        # the symbol b ends with
    pi = stationary(q, L)
    q0, q1 = 1 - q, q
    K = len(gam)
    G = np.empty((len(hs), n), dtype=complex)
    phi = np.empty(len(hs), dtype=complex)
    for i, h in enumerate(hs):
        e = np.exp(2j * np.pi * h * gam)
        W = [None] * (K + 1)
        W[K] = np.ones(n, dtype=complex)
        for p in range(K - 1, -1, -1):
            W[p] = q0 * W[p + 1][t0] + q1 * (e[p] * W[p + 1][t1])
        V = pi.astype(complex)
        g = np.zeros(n, dtype=complex)
        for p in range(K):
            g += V * (e[p] * W[p + 1][t1] - W[p + 1][t0])
            c0 = np.where(eps == 0, q0[p0], q1[p0] * e[p])
            c1 = np.where(eps == 0, q0[p1], q1[p1] * e[p])
            V = V[p0] * c0 + V[p1] * c1
        G[i] = g
        phi[i] = V.sum()
    return G, phi


def newton_full(F, H, L, iters=40, dqcap=0.40, theta=1e-10, log=None):
    """Full Newton with the Jacobian recomputed at every iterate, trust region on max|dq|.

    This is the control for `reach`'s and `lm`'s stall at d = 4: if the residual reaches the
    window floor here and not there, the obstruction was the chord approximation."""
    J, M = F.need(H, mp_tau())
    gam = schedule(F, J, M)
    hs = list(range(1, H + 1))
    n = 1 << L
    floor = 2 * np.pi * H * float(F.eps(J, M))
    q = np.full(n, 0.5)
    seq, lam = [], 1e-12
    for it in range(iters):
        G, ph = jacobian_at(gam, q, hs, L)
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
        for _ in range(40):
            v = -(Vt.T @ ((S * c) / (S ** 2 + lam)))
            if np.abs(v).max() > dqcap or (q + v).min() <= 1e-12 or (q + v).max() >= 1 - 1e-12:
                lam *= 4
                continue
            phn = forward(gam, q + v, hs, L)
            rn = np.empty(2 * H)
            rn[0::2], rn[1::2] = phn.real, phn.imag
            if np.linalg.norm(rn) < seq[-1]:
                q, ok = q + v, True
                lam = max(lam / 3, 1e-16)
                break
            lam *= 4
        if not ok:
            break
    return dict(d=F.d, H=H, L=L, iters=len(seq) - 1, resid=seq, floor=float(floor),
                final=seq[-1], sup=float(np.abs(ph).max()),
                stepinf=float(np.abs(q - 0.5).max()),
                reached=bool(seq[-1] < 30 * floor))


def lm(F, H, L, iters=60, dqcap=0.40, log=None):
    """Levenberg-Marquardt on the chord Jacobian: `v = -(A^T A + lam I)^{-1} A^T r`, with
    `lam` raised until the step obeys the trust region `max_b |dq(b)| <= dqcap` and lowers
    ||Phi||.  The plain truncated step of `reach` fails at d = 4 for a reason that is not
    geometry: after three steps the residual has rotated onto singular directions of size
    ~1e-6, the least-norm correction is 0.1 in L^2(pi) (max|dq| = 0.36) and overshoots.
    LM follows the curved path instead and recovers two to three orders."""
    A, r0, (J, M, gam) = jacobian(F, H, L)
    U, S, Vt = np.linalg.svd(A, full_matrices=False)
    hs = list(range(1, H + 1))
    n = 1 << L
    floor = 2 * np.pi * H * float(F.eps(J, M))

    def res(u):
        q = 0.5 + (n ** 0.5) * u
        if q.min() <= 1e-12 or q.max() >= 1 - 1e-12:
            return None
        ph = forward(gam, q, hs, L)
        r = np.empty(2 * H)
        r[0::2], r[1::2] = ph.real, ph.imag
        return r

    u = np.zeros(n)
    r = res(u)
    seq = [float(np.linalg.norm(r))]
    lam = 1e-12
    for _ in range(iters):
        c = U.T @ r
        ok = False
        for _ in range(40):
            v = -(Vt.T @ ((S * c) / (S ** 2 + lam)))
            if np.abs(v).max() * n ** 0.5 > dqcap:
                lam *= 4
                continue
            rn = res(u + v)
            if rn is not None and np.linalg.norm(rn) < seq[-1]:
                u, r = u + v, rn
                seq.append(float(np.linalg.norm(r)))
                lam = max(lam / 3, 1e-16)
                ok = True
                break
            lam *= 4
        if not ok or seq[-1] < 3 * floor:
            break
    q = 0.5 + (n ** 0.5) * u
    ph = forward(gam, q, hs, L)
    return dict(d=F.d, H=H, L=L, iters=len(seq) - 1, resid=seq, floor=float(floor),
                final=seq[-1], sup=float(np.abs(ph).max()),
                stepinf=float(np.abs(u).max() * n ** 0.5),
                stepL2=float(np.linalg.norm(u)),
                reached=bool(seq[-1] < 30 * floor))


def run_lm(log=print, cases=((2, 128, 14), (3, 128, 14), (4, 32, 12), (4, 64, 12),
                             (4, 64, 14), (4, 128, 12), (4, 128, 14))):
    rows = []
    for d, H, L in cases:
        t0 = time.time()
        rec = lm(Field(FAMILY[d - 2]), H, L)
        rec['secs'] = time.time() - t0
        rows.append(rec)
        log('d=%d H=%-4d L=%-3d LM: %2d its | ||Phi|| %.3e -> %.3e (floor %.1e) | '
            'sup|Phi_h| %.2e | max|dq| %.3e | %s | %.0fs'
            % (d, H, L, rec['iters'], rec['resid'][0], rec['final'], rec['floor'],
               rec['sup'], rec['stepinf'], 'REACHED' if rec['reached'] else 'stalls',
               rec['secs']))
    return rows


def run_full(log=print, ds=(2, 3, 4), Hs=(8, 16, 32, 64, 128), Ls=(8, 10, 12, 14)):
    """L*(H, d) with the EXACT Jacobian recomputed at every iterate.

    `reach` (chord) and `lm` both stall at d = 4; this is the control that shows the stall
    was the chord approximation and not the geometry."""
    rows = []
    for d in ds:
        F = Field(FAMILY[d - 2])
        for H in Hs:
            best = None
            for L in Ls:
                if 2 * H > (1 << L):
                    continue
                t0 = time.time()
                rec = newton_full(F, H, L)
                rec['secs'] = time.time() - t0
                rows.append(rec)
                log('d=%d H=%-4d L=%-3d | %2d its | ||Phi|| %.3e -> %.3e (floor %.1e) | '
                    'sup|Phi_h| %.2e | max|dq| %.3e | %s | %.0fs'
                    % (d, H, L, rec['iters'], rec['resid'][0], rec['final'], rec['floor'],
                       rec['sup'], rec['stepinf'],
                       'REACHED' if rec['reached'] else 'stalls', rec['secs']))
                if rec['reached']:
                    best = L
                    break
            log('  -> d=%d H=%-4d  L* = %s' % (d, H, best if best else 'none of %s' % (Ls,)))
    return rows


def run_reach(log=print, ds=(2, 3, 4), Hs=(8, 16, 32, 64, 128), Ls=(8, 10, 12, 14, 16)):
    """L*(H, d): the smallest memory at which the residual reaches the window floor."""
    rows = []
    for d in ds:
        F = Field(FAMILY[d - 2])
        for H in Hs:
            best = None
            for L in Ls:
                if 2 * H > (1 << L):
                    continue
                t0 = time.time()
                rec = reach(F, H, L)
                rec['secs'] = time.time() - t0
                rows.append(rec)
                log('d=%d H=%-4d L=%-3d | %2d its | ||Phi|| %.3e -> %.3e (floor %.1e) | '
                    'sup|Phi_h| %.2e | max|dq| %.3e | trunc %-4d s_min %.2e | %-10s | %s | %.0fs'
                    % (d, H, L, rec['iters'], rec['resid'][0], rec['final'], rec['floor'],
                       rec['sup'], rec['stepinf'], rec['trunc'], rec['smin'], rec['limit'],
                       'REACHED' if rec['reached'] else 'stalls', rec['secs']))
                if rec['reached']:
                    best = L
                    break
            log('  -> d=%d H=%-4d  L* = %s' % (d, H, best if best else 'none of %s' % (Ls,)))
    return rows


def run_spec(log=print, Hs=(4, 8, 16, 32, 64, 128), Ls=(10, 12, 14), ds=(2, 3, 4)):
    rows = []
    for d in ds:
        F = Field(FAMILY[d - 2])
        for L in Ls:
            for H in Hs:
                if 2 * H > (1 << L):
                    continue
                t0 = time.time()
                G = gates(F, H, L)
                G['secs'] = time.time() - t0
                rows.append(G)
                log('d=%d L=%-3d H=%-4d | rank %-4d s_min %.4e s_max %.4e cond %.3e | '
                    '||r|| %.4e | step %.4e (sup %.3e) naive %.4e loose %.3e | '
                    'lambda_1 %.4e step1 %.4e | %.0fs'
                    % (d, L, H, G['rank'], G['smin'], G['smax'], G['cond'], G['nres'],
                       G['step'], G['stepinf'], G['naive'], G['loose'], G['lam1'],
                       G['step1'], G['secs']))
    return rows


def run_sparse(log=print):
    """The row structure against R3a Theorem B, at a ladder rung and at h = 1."""
    rows = []
    for d in (2, 3, 4):
        F = Field(FAMILY[d - 2])
        J, M = F.need(4096, mp_tau())
        gam = schedule(F, J, M)
        L = 8
        seeds = {2: (1, 3), 3: (3, 2, 4), 4: (4, 2, 4, 8)}[d]
        a = [-c for c in F.coeffs[1:]]
        hh = list(seeds)
        while len(hh) < 14:
            hh.append(sum(a[i] * hh[-1 - i] for i in range(F.d)))
        for h in [1, 2] + [x for x in hh if 8 <= x <= 4096][:3]:
            red = np.abs(gam * h - np.round(gam * h))
            g = g_row(gam, h, L)
            osc = g - g.mean()
            # the k-terms, by size, and where they sit
            ph = (1.0 + np.exp(2j * np.pi * h * gam)) / 2.0
            pre = np.concatenate([[1], np.cumprod(ph)])
            suf = np.concatenate([np.cumprod(ph[::-1])[::-1], [1], [1]])
            lead = np.abs(np.exp(2j * np.pi * h * gam) - 1.0)
            wgt = np.array([lead[k] * abs(pre[max(k - L, 0)] * suf[k + 1])
                            for k in range(len(gam))])
            tot = wgt.sum()
            srt = np.sort(wgt)[::-1]
            n90 = int(np.searchsorted(np.cumsum(srt), 0.9 * tot) + 1) if tot > 0 else 0
            rows.append(dict(d=d, h=int(h), K=len(gam), L=L,
                             active=int((red > 1e-3).sum()), n90=n90,
                             frac90=n90 / len(gam), osc=float(np.abs(osc).max()),
                             mean=float(abs(g.mean())),
                             ratio=float(np.abs(osc).max() / max(abs(g.mean()), 1e-300))))
            r = rows[-1]
            log('d=%d h=%-6d K=%-5d | reduced weights > 1e-3 at %-4d positions | 90%% of the '
                'k-mass in %-4d (%.1f%%) | |osc|/|mean| %.3e'
                % (r['d'], r['h'], r['K'], r['active'], r['n90'], 100 * r['frac90'],
                   r['ratio']))
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
    if cmd in ('sparse', 'all'):
        print('=== row structure ===')
        out['sparse'] = run_sparse()
    if cmd in ('spec', 'g3', 'all'):
        print('=== the spectrum and the two gates ===')
        out['spec'] = run_spec(Hs=(4, 8, 16, 32, 64, 128, 256), Ls=(10, 12, 14, 16))
    if cmd in ('reach', 'all'):
        print('=== how far down, and at what memory ===')
        out['reach'] = run_reach()
    if cmd in ('full', 'all'):
        print('=== L*(H, d) with the exact Jacobian ===')
        out['full'] = run_full()
    if cmd in ('lm', 'all'):
        print('=== Levenberg-Marquardt, where the plain chord step fails ===')
        out['lm'] = run_lm()
    if cmd in ('newton', 'all'):
        print('=== the chord Newton iteration ===')
        rows = []
        for d, H, L in ((2, 32, 12), (3, 32, 12), (4, 32, 12), (4, 64, 12), (4, 64, 14),
                        (3, 64, 14), (4, 128, 14)):
            t0 = time.time()
            rec = run_newton(Field(FAMILY[d - 2]), H, L)
            rec['secs'] = time.time() - t0
            rows.append(rec)
            print('d=%d H=%-4d L=%-3d | ||Phi|| %s | sup|Phi_h| %.2e -> %.2e | '
                  'max|dq| %.2e | window floor %.1e | %.0fs'
                  % (d, H, L, ' -> '.join('%.3e' % x for x in rec['resid']),
                     rec['supPhi'][0], rec['supPhi'][-1], rec['stepinf'], rec['floor'],
                     rec['secs']))
        out['newton'] = rows
    json.dump(out, open(OUT, 'w'), indent=1)
    print('-> %s' % OUT)
    return 1 if FAIL else 0


if __name__ == '__main__':
    sys.exit(main())
