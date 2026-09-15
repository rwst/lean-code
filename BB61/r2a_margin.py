#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2a of `plan-BB61-counterexample.html`: the conditioned margin, and the loop.

sec 6.3 defines the **conditioned margin** `m(H)` of the pool at degree `H` after the
Farkas loop has been run to convergence, and reads three behaviours off it: hits `0` at a
finite `H_0` (then `K_{H_0}` is empty and 10.61 is proved at `alpha`); decays polynomially
(witnesses continue, the pool is merely thinning); decays super-polynomially but stays
positive (ambiguous, and the honest published outcome).  Gate G-2 is which row fires.

Three pieces here, and the first is a sharpening of R1b's theorem that the loop needs.

---------------------------------------------------------------------------------------
THEOREM 1'  (weighted interior certificate).  Notation of R1b: `nu_1,...,nu_m` shift
invariant, `Phi(nu) in R^{2H}`, `V` the computed values with `|Phi(nu_j) - V_j|_2 <= e2`,
`W = [V ; 1^T] in R^{d x m}`, `d = 2H+1`, `rank W = d`.  Let

        g_j  >=  |e_j^T W^+|_2      (rows of the pseudoinverse),

and let `lam in R^m` satisfy `1^T lam = 1` and `lam_j >= R g_j` for every `j`.  Put
`r = V lam`.  If

        delta := R - |r|_2 - e2  >  0                                             (C')

then some `lam''` in the simplex has `sum_j lam''_j Phi(nu_j) = 0`, so `K_H != empty`;
and `|lam'' - lam|_2 <= (|r|_2 + e2)/sigma_min(W)`, so R1b's entropy bound (H) is
unchanged.

PROOF.  Only step (i) of R1b's Theorem 1 changes.  For `|y|_2 <= R` put
`mu_y = W^+(y,0)`; then `W mu_y = (y,0)`, so `V mu_y = y` and `1^T mu_y = 0` (the last
row of `W` is `1^T`).  Coordinatewise `|(mu_y)_j| = |e_j^T W^+ (y,0)| <= g_j |y|_2 <= lam_j`,
so `lam + mu_y >= 0` is again a probability vector and `V(lam + mu_y) = r + y`: the ball
`B(r,R)` lies in `conv{V_j}` and `y |-> lam + W^+(y,0)` is an affine selection of weights.
Steps (ii) Brouwer and (iii) entropy are verbatim, with `|mu_y|_2 <= |y|_2/sigma_min(W)`. []

R1b's Theorem 1 is the special case `g_j = 1/sigma_min(W)`, valid because
`|e_j^T W^+|_2 <= |W^+|_2 = 1/sigma_min(W)`; then `R = t sigma_min(W)` with
`t = min_j lam_j`.  That uniform choice is what makes R1b's margin fall off with the POOL
SIZE and not only with the geometry: `t <= 1/m` for weights that sum to one, so
`t sigma_min(W) <= sigma_min(W)/m` however round the hull is.  The row norms cure exactly
that -- `sum_j g_j^2 = |W^+|_F^2`, so a typical `g_j` is smaller than `|W^+|_2` by a factor
`sqrt(m)` -- and on the R1b pools they buy a factor 5.3 to 7.2, growing with `H`.  It also
makes `m(H)` an observable of the hull rather than of the bookkeeping, which is what
sec 6.3 wants to read a decay exponent off.
---------------------------------------------------------------------------------------

The second piece is an UPPER bound for the same geometric quantity.  `delta` is a certified
lower bound for the depth `rho(H) = dist(0, boundary conv{V_j}) = min_{|u|=1} max_j <u,V_j>`
of `0` in the pool's hull, and a lower bound alone cannot tell a thinning hull from a
slackening certificate.  `depth_upper` maximises `|u|` over the polar body
`P^o = {u : <u,V_j> <= 1 for all j}` -- a convex maximisation whose optimum is a vertex of
`P^o`, i.e. a facet of `P` -- by linearising the norm, which makes each step an LP.  Any
feasible `u` it produces gives `rho <= max_j <u, V_j>/|u|`, so the run is an upper bound
whether or not it found the global optimum.

The third piece is the loop.  The direction `u` that attains the upper bound is where the
hull is thinnest; the members added are the Gibbs measures at `a* +- t u`, which is WP9's
Farkas step with the infeasibility direction replaced by the thinness direction (they
coincide when the pool is infeasible, and `separate_lp` is used then).  Adding members can
only grow the hull, and `m(H)` is taken to be the best `delta` over the rounds, which is
sound because each round certifies the same statement from a sub-pool of the final one.

Two things the loop turned out to need, and neither was in sec 6.2.

  * THE TILT SCALE IS THE LEVER.  Steered at M7's `t in [0.01,0.04,0.15,0.5]` the loop runs
    BACKWARDS -- the hull grows and the certificate falls, because `delta <= 1/sum_j g_j`
    and `sum_j g_j` grows like `sqrt(m)` when the new members duplicate directions the pool
    already spans.  The certified margin peaks at `t in [0.1,0.5,2.5,12]` (`TSWIDE` in
    `r2a_pool`), worth 1.44x M7's at `H = 8` and 1.44x again at `H = 32`, and with that
    change the loop does what sec 6.2 says: 1.68x at `H = 4`, 1.12x at `H = 64`.
  * THE STEP IS MONOTONE IN THE WRONG COORDINATES.  Pool members are equilibrium states of
    the WINDOW observable `F~_L`, so the pressure is convex in `a` with gradient
    `Phi~(mu_a)` and the tilt is monotone in `<u, Phi~>` FOR EVERY `u` -- which is what lets
    WP9 promise that `a* - tc` reaches the far side of a plane.  The certificate is written
    in the enclosed `Phi`, and the two differ by `2 pi h eps_L`.  Where that matters the
    Farkas step can fail to reach its own plane at any magnitude; `tilt_response` tabulates
    both coordinates along a ray and `farkas` runs the loop until the direction repeats.

Usage:  python3 r2a_margin.py --checks           # self-checks only
        python3 r2a_margin.py                    # self-checks, then the ladder
"""
import json
import math
import os
import sys
import time

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')

BB = '/home/ralf/math/lean-code/BB61'
INF = float('inf')
U = 2.0 ** -53
LOG2 = math.log(2.0)
ENT_SLACK = 1e-11
LPOPT = dict(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10)
_ok = _bad = 0


def check(name, cond, detail=""):
    global _ok, _bad
    if cond:
        _ok += 1
        print(f"  ok   {name}   {detail}")
    else:
        _bad += 1
        print(f"  FAIL {name}   {detail}")


def dn(x):
    return math.nextafter(x, -INF)


def up(x):
    return math.nextafter(x, INF)


def gamma(k):
    """The standard `gamma_k = k u / (1 - k u)` of a length-`k` dot product."""
    ku = k * U
    return up(ku / (1.0 - ku))


def norm_up(x):
    """Upper bound in binary64 for `|x|_2`, `x` a float64 vector.

    `fl(sum x_i^2)` has relative error at most `gamma_{n+1}` (n squarings, n-1 additions),
    and `sqrt` adds one rounding."""
    x = np.asarray(x, dtype=float).ravel()
    s = float(np.dot(x, x))
    return up(math.sqrt(up(s * (1.0 + gamma(len(x) + 1)))) * (1.0 + 2 * U))


def norms_up(X):
    """Column-wise `norm_up` of a float64 matrix, vectorised."""
    X = np.asarray(X, dtype=float)
    s = np.einsum('ij,ij->j', X, X)
    return np.nextafter(np.sqrt(s * (1.0 + gamma(X.shape[0] + 1))) * (1.0 + 2 * U), INF)


# ======================================================================================
# verified positive definiteness, and sigma_min(W) from it
# ======================================================================================
def pd_verified(A):
    """True => the symmetric float64 matrix `A` is positive definite.

    Rump's criterion (Rum99/Rum06): if the floating-point Cholesky factorisation of
    `A - c I` with `c = gamma_{d+1} max_i A_ii` runs to completion then `A > 0`.  Unlike
    R1b's interval Cholesky this runs in LAPACK, so `d = 1025` costs 0.1 s instead of
    hours -- which is what makes the ladder above `H = 64` affordable at all."""
    d = len(A)
    c = up(gamma(d + 1) * max(float(np.max(np.diag(A))), 0.0))
    try:
        np.linalg.cholesky(A - c * np.eye(d))
        return True
    except np.linalg.LinAlgError:
        return False


def sigma_min_lower(Wf, steps=40):
    """Rigorous lower bound for `sigma_min(W)`; also returns `lam_min(W W^T)` bounded below.

    Three roundings are accounted, all in the safe direction:
      * `Ghat = fl(W W^T)`: `|Ghat - W W^T|_ij <= gamma_m sqrt(G_ii G_jj)` (Cauchy-Schwarz
        on the standard dot-product bound), so `|Ghat - W W^T|_2 <= |.|_F <= gamma_m tr G`;
      * `A = fl(Ghat - s I)`: only the diagonal moves, by `<= u |A_ii|`;
      * `pd_verified(A)` proves `lam_min(A) > 0`.
    Together `lam_min(W W^T) > s - u max_i|A_ii| - gamma_m tr(Ghat)(1+2 gamma_m)`."""
    d, m = Wf.shape
    G = Wf @ Wf.T
    G = 0.5 * (G + G.T)
    gam_m = gamma(m)
    trG = up(float(np.sum(np.diag(G))) * (1.0 + 2 * gam_m))
    dG = up(gam_m * trG)
    lam0 = float(np.linalg.eigvalsh(G)[0])
    if not (lam0 > 0):
        return 0.0, 0.0, lam0, dG
    lo, hi = 0.0, lam0 * (1.0 + 1e-9)
    I = np.eye(d)
    best = None
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        A = G - mid * I
        if pd_verified(A):
            lo, best = mid, A
        else:
            hi = mid
        if hi - lo < 1e-12 * max(hi, 1.0):
            break
    if best is None:
        return 0.0, 0.0, lam0, dG
    eta = up(U * float(np.max(np.abs(np.diag(best)))))
    lam_lo = dn(dn(dn(lo - eta) - dG))
    if not (lam_lo > 0):
        return 0.0, 0.0, lam0, dG
    return dn(math.sqrt(lam_lo)), lam_lo, lam0, dG


def rowpinv_upper(Wf, lam_lo, dG):
    """Upper bounds `g_j >= |e_j^T W^+|_2` for every column `j`, rigorously.

    `e_j^T W^+ = (G^{-1} W_{.j})^T` with `G = W W^T`, so with `Z ~ G^{-1} W` computed in
    LAPACK and `S = W - G Z` the exact residual,
        `g_j <= |Z_{.j}| + |S_{.j}| / lam_min(G)`.
    `S` is bounded from the computed `Shat = fl(W - Ghat Z)` by the matmul rounding
    `gamma_{d+1}(|W| + |Ghat||Z|)` and by `|Ghat - G|_2 |Z_{.j}| <= dG |Z_{.j}|`."""
    d, m = Wf.shape
    G = Wf @ Wf.T
    G = 0.5 * (G + G.T)
    Z = np.linalg.solve(G, Wf)
    Sh = Wf - G @ Z
    nZ = norms_up(Z)
    nS = norms_up(Sh)
    gd = gamma(d + 1)
    gF = up(float(np.linalg.norm(G, 'fro')) * (1.0 + 2 * U))
    nW = norms_up(Wf)
    # |E_{.j}| <= gamma_{d+1} ( |W_{.j}| + |Ghat| |Z_{.j}| ),  |Ghat| |Z| <= |Ghat|_F |Z|
    bnd = np.nextafter(nS + gd * (nW + gF * nZ) + dG * nZ, INF)
    g = np.nextafter(nZ + bnd / lam_lo, INF)
    return g, Z


# ======================================================================================
# the exact rational side, in integers (fast enough for m in the thousands)
# ======================================================================================
def _scale(Vf):
    """Common power of two making every entry of `Vf` an integer."""
    e = 0
    for x in np.asarray(Vf, dtype=float).ravel():
        n, dd = float(x).as_integer_ratio()
        e = max(e, dd.bit_length() - 1)
    return e


def rationalise(lam, D):
    a = [max(1, int(round(float(x) * D))) for x in lam]
    d = D - sum(a)
    order = sorted(range(len(a)), key=lambda j: -a[j])
    i = 0
    while d != 0:
        j = order[i % len(order)]
        step = 1 if d > 0 else -1
        if a[j] + step >= 1:
            a[j] += step
            d -= step
        i += 1
    assert sum(a) == D and min(a) >= 1
    return a


def sqrt_upper_int(num, den, k=60):
    """Upper bound in binary64 for `sqrt(num/den)`, `num, den` non-negative integers.

    `sqrt(num/den) = sqrt(num den 4^k)/(den 2^k)`, and `isqrt` truncates, so adding one
    before dividing gives an upper bound whose slack is `1/(den 2^k)` -- negligible for
    every `den` rather than only for the astronomically large ones this is called with."""
    if num == 0:
        return 0.0
    r = math.isqrt(num * den << (2 * k)) + 1
    return up(r / (den << k))


def exact_residual(Vf, a, D, e=None):
    """`|V lam|_2` rounded up, in exact integer arithmetic, `lam_j = a_j / D`.

    float64 entries are dyadic, so `2^e V` is an integer matrix for a common `e` and
    `2^e D r_i` is an exact integer sum."""
    Vf = np.asarray(Vf, dtype=float)
    d, m = Vf.shape
    if e is None:
        e = _scale(Vf)
    sc = float(2 ** e) if e < 1000 else None
    N = [[int(round(float(x) * (2 ** e))) if sc is None else int(x * sc) for x in row]
         for row in Vf]
    tot = 0
    for i in range(d):
        row = N[i]
        tot += sum(a[j] * row[j] for j in range(m)) ** 2
    den = (1 << e) * D
    return sqrt_upper_int(tot, den * den), e


# ======================================================================================
# the linear programmes -- they only PROPOSE; the certificate never trusts them
# ======================================================================================
def weighted_maximin_lp(Vm, g):
    """max R subject to `V lam = 0`, `1^T lam = 1`, `lam_j >= R g_j` -- Theorem 1's LP."""
    d, m = Vm.shape
    A_eq = np.vstack([np.hstack([Vm, np.zeros((d, 1))]), np.append(np.ones(m), 0.0)])
    b_eq = np.append(np.zeros(d), 1.0)
    A_ub = np.hstack([-np.eye(m), np.asarray(g, dtype=float)[:, None]])
    r = linprog(np.append(np.zeros(m), -1.0), A_ub=A_ub, b_ub=np.zeros(m),
                A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * m + [(None, None)],
                method='highs', options=LPOPT)
    return (np.asarray(r.x[:m]), float(r.x[-1])) if r.success else (None, None)


def refine(Vm, lam, rounds=2):
    d, m = Vm.shape
    W = np.vstack([Vm, np.ones((1, m))])
    Wp = np.linalg.pinv(W)
    lam = np.array(lam, dtype=float)
    for _ in range(rounds):
        lam = lam - Wp @ np.append(Vm @ lam, lam.sum() - 1.0)
    return lam


def separate_lp(Vm):
    """max d subject to `<u,V_j> >= d` for all `j`, `|u|_inf <= 1` -- the Farkas direction."""
    d, m = Vm.shape
    r = linprog(np.append(np.zeros(d), -1.0),
                A_ub=np.hstack([-Vm.T, np.ones((m, 1))]), b_ub=np.zeros(m),
                bounds=[(-1, 1)] * d + [(None, None)], method='highs', options=LPOPT)
    return (np.asarray(r.x[:d]), float(r.x[-1])) if r.success else (None, None)


def depth_upper(Vm, starts=8, iters=30, seed=0, u0=None, polish=True):
    """Upper bound for `rho = min_{|u|=1} max_j <u,V_j>`, and the direction attaining it.

    Softmax descent for the search (two matvecs a step), then Frank-Wolfe vertex hopping
    on the polar body for the polish.  Every iterate gives a valid upper bound, so an
    early stop costs sharpness and never soundness."""
    d, m = Vm.shape
    rng = np.random.default_rng(seed)
    cands = []
    if u0 is not None and np.linalg.norm(u0) > 0:
        cands.append(np.asarray(u0, dtype=float))
    cands += [Vm[:, j] for j in rng.choice(m, min(3, m), replace=False)]
    cands += [rng.standard_normal(d) for _ in range(max(0, starts - len(cands)))]
    best, bu = INF, None
    for c in cands:
        u = np.asarray(c, dtype=float)
        u = u / max(np.linalg.norm(u), 1e-300)
        for beta in (20.0, 100.0, 500.0, 2500.0):
            for _ in range(iters):
                z = Vm.T @ u
                w = np.exp(beta * (z - z.max()))
                gr = Vm @ (w / w.sum())
                gr -= np.dot(gr, u) * u                # tangent to the sphere
                ng = np.linalg.norm(gr)
                if ng < 1e-14:
                    break
                step = 0.5 * float(np.max(z)) / max(ng, 1e-300)
                un = u - step * gr / ng * max(np.linalg.norm(u), 1.0)
                un /= max(np.linalg.norm(un), 1e-300)
                if np.max(Vm.T @ un) >= np.max(z):
                    break
                u = un
        val = float(np.max(Vm.T @ u))
        if val < best:
            best, bu = val, u
    if polish and bu is not None:
        c = bu.copy()
        for _ in range(iters):
            r = linprog(-c, A_ub=Vm.T, b_ub=np.ones(m), bounds=(None, None),
                        method='highs', options=LPOPT)
            if not r.success or np.linalg.norm(r.x) < 1e-14:
                break
            cn = r.x / np.linalg.norm(r.x)
            done = float(np.dot(cn, c)) > 1 - 1e-12
            c = cn
            val = float(np.max(Vm.T @ c))
            if val < best:
                best, bu = val, c.copy()
            if done:
                break
    return best, bu


# ======================================================================================
# the certificate
# ======================================================================================
def margin(Vm, eps, H, ent=None, D=10 ** 14, lam=None, cache=None, refine_rounds=2):
    """Theorem 1' at one pool: propose `lam`, then certify `(C')` with every error signed.

    `cache` carries `(g, sigma, lam_lo, dG, e)` -- the parts that depend on the pool and
    not on `lam` -- across the rounds of the loop."""
    d, m = Vm.shape
    assert d == 2 * H
    Wf = np.vstack([Vm, np.ones((1, m))])
    if cache is None:
        sig, lam_lo, lam0, dG = sigma_min_lower(Wf)
        if sig <= 0:
            return dict(H=H, m=m, eps=eps, sigma=0.0, delta=-INF, feasible=False)
        g, _ = rowpinv_upper(Wf, lam_lo, dG)
        cache = dict(g=g, sigma=sig, lam_lo=lam_lo, lam0=lam0, dG=dG, e=_scale(Vm))
    g, sig = cache['g'], cache['sigma']
    if lam is None:
        lam, R0 = weighted_maximin_lp(Vm, g)
        if lam is None:
            return dict(H=H, m=m, eps=eps, sigma=sig, delta=-INF, feasible=False,
                        cache=cache)
        lam = refine(Vm, lam, refine_rounds)
    a = rationalise(np.maximum(lam, 0.0), D)
    R = dn(min(float(a[j]) / D / g[j] for j in range(m)))
    rn, _ = exact_residual(Vm, a, D, cache['e'])
    e2 = up(eps * up(math.sqrt(H)))
    delta = dn(dn(R - rn) - e2)
    out = dict(H=H, m=m, eps=eps, e2=e2, R=R, sigma=sig, r2=rn, delta=delta, D=D,
               feasible=True, cache=cache, lam=a,
               ratio=(delta / e2 if e2 > 0 else INF))
    if ent is not None:
        h_lam = math.fsum(float(a[j]) / D * (float(ent[j]) - ENT_SLACK) for j in range(m))
        drift = up(up(rn + e2) / sig) * up(math.sqrt(m)) * LOG2 if sig > 0 else INF
        out.update(h_mix=h_lam, h_drift=drift, h_lower=dn(h_lam - drift))
    return out


# ======================================================================================
# the loop
# ======================================================================================
def vmat(phi, H):
    phi = np.asarray(phi)
    return np.concatenate([phi[:, :H].real, phi[:, :H].imag], axis=1).T.copy()


def thin_directions(Vm, k=4, **kw):
    """The `k` thinnest facet normals found, best first -- one steering direction each."""
    outs = []
    for s in range(k):
        val, u = depth_upper(Vm, seed=s, starts=3, **kw)
        if u is not None and np.isfinite(val):
            outs.append((val, u))
    outs.sort(key=lambda vu: vu[0])
    return outs


def stiff_directions(Vm, k=2):
    """The worst-conditioned directions of `W`: its bottom left singular vectors.

    A member with a large component along one of these raises `sigma_min(W)`, which is the
    ceiling of Theorem 1' (`R <= 1/|W^+|_F <= sigma_min(W)`).  Steering only at the thin
    FACETS improves the hull and not the conditioning, so the loop uses both."""
    m = Vm.shape[1]
    W = np.vstack([Vm, np.ones((1, m))])
    Uu, sv, _ = np.linalg.svd(W, full_matrices=False)
    return [(float(sv[-1 - i]), Uu[:-1, -1 - i]) for i in range(min(k, len(sv) - 1))]


def loop(pool, Vm, ent, eps, rounds=10, tol=0.02, ndir=4, log=print):
    """Farkas / margin-increasing loop at one `H`, run to its own convergence.

    Each round: certify (Theorem 1'), find the thinnest directions of the hull, add the
    Gibbs measures tilted along `+- t u` for each.  Adding members can only grow the hull,
    so the depth is monotone along the loop; the loop stops when a round buys less than
    `tol` in relative terms, twice running."""
    from r2a_pool import TSFINE, TSWIDE, steer
    H = pool.H
    hist, u_prev, stall = [], None, 0
    best = dict(delta=-INF)
    for k in range(rounds + 1):
        res = margin(Vm, eps, H, ent=ent)
        repeat = False
        # every round certifies the SAME statement from a sub-pool of the final one, and
        # `0 in conv S` implies `0 in conv S'` for any larger `S'`, so keeping the best
        # round is sound and makes `m(H)` monotone under the loop by construction
        if res['feasible'] and res['delta'] > best['delta']:
            best = dict(res, round=k)
        if res['feasible']:
            dirs = thin_directions(Vm, k=ndir, u0=u_prev)
            rho = dirs[0][0] if dirs else INF
            u_prev = dirs[0][1] if dirs else None
            dirs = dirs + stiff_directions(Vm, k=2)
        else:
            u, dsep = separate_lp(Vm)
            dirs = [(-abs(dsep), u)] if u is not None else []
            rho = -abs(dsep) if u is not None else INF
            if (u is not None and u_prev is not None
                    and np.allclose(u, u_prev, rtol=1e-9, atol=1e-12)):
                log("    the Farkas direction repeats: the tilt cannot reach its plane")
                repeat = True
            u_prev = u
        rec = dict(round=k, m=res['m'], delta=res['delta'], R=res.get('R'),
                   r2=res.get('r2'), e2=res.get('e2'), sigma=res.get('sigma'),
                   rho_upper=rho, feasible=res['feasible'],
                   h_lower=res.get('h_lower'))
        hist.append(rec)
        log(f"    round {k:<2} m={res['m']:<5} delta {res['delta']:.4e}  "
            f"rho_upper {rho:.4e}  sigma {res.get('sigma', 0):.3e}  "
            f"|r| {res.get('r2', 0):.2e}", )
        if k == rounds or not dirs or repeat:
            break
        if k > 0:
            prev = hist[-2]['rho_upper']
            g_rho = (rho - prev) / abs(prev) if np.isfinite(prev) and prev != 0 else INF
            pd = max(h['delta'] for h in hist[:-1])
            g_del = (res['delta'] - pd) / abs(pd) if pd not in (0, -INF) else INF
            stall = stall + 1 if (res['feasible']
                                  and max(g_rho, g_del) < tol) else 0
            if stall >= 3:
                log(f"    converged: three rounds under {tol:.0%} on both "
                    f"the depth and the certificate")
                break
        ts = TSWIDE if res['feasible'] else TSFINE
        xs = [x for _, u in dirs[:ndir + 2] for x in steer(pool, u, ts)]
        got = pool.members(xs)
        if got is None:
            break
        phi, rad, ent_new, _, _, _ = got
        Vm = np.hstack([Vm, vmat(phi, H)])
        ent = np.concatenate([ent, ent_new])
        eps = max(eps, rad)
    return Vm, ent, eps, hist, best


# ======================================================================================
# the ladder
# ======================================================================================
def load_rung(spec):
    """A pool rung, from an R1b json row or an R2a npz.  Returns everything the loop needs."""
    import r2a_pool as PL
    path, H = spec
    if path.endswith('.json'):
        d = json.load(open(path))
        row = d['rows'][str(H)]
        phi = np.array(row['phi_re']) + 1j * np.array(row['phi_im'])
        ent = np.array(row['ent'])
        eps, L = float(row['radius']), int(d['Lpool'])
        c = d.get('coeffs', [1, -2, -1])            # x^2 - A x - B
        A, B = -int(c[1]), -int(c[2])
        name = d.get('name', '1+sqrt2')
        xstar = np.array(row['xstar']) if 'xstar' in row else None
        upper = float(row['upper'])
    else:
        z = np.load(path)
        phi = z['phi_re'] + 1j * z['phi_im']
        ent = z['ent']
        eps, L = float(z['radius']), int(z['Lpool'])
        A, B = (int(v) for v in z['coef'])
        name = os.path.basename(path).split('_')[2]
        xstar = z['xstar']
        upper = float(z['upper'])
    pool = PL.Pool(A, B, name, H, xstar=xstar, L=L)
    if xstar is None:                        # the pre-xstar R1b rows: recompute the centre
        pool.optimise()
    return pool, vmat(phi, H), ent, eps, upper


def ladder(specs, rounds=8, tol=0.02, ndir=4, out=None, log=print):
    """`m(H)` along a ladder of rungs, each with the loop run to its own convergence."""
    rec = []
    for spec in specs:
        path, H = spec
        pool, Vm, ent, eps, upper = load_rung(spec)
        log(f"\n# H={H}  L={pool.L}  pool {Vm.shape[1]}  eps {eps:.3e}  "
            f"H*eps_window {H * pool.eps_win:.3f}  optimiser {upper:.6f}")
        before = margin(Vm, eps, H, ent=ent)
        rho0, _ = depth_upper(Vm)
        t0 = time.time()
        Vm, ent, eps, hist, best = loop(pool, Vm, ent, eps, rounds=rounds, tol=tol,
                                        ndir=ndir, log=log)
        after = best if best['delta'] > -INF else margin(Vm, eps, H, ent=ent)
        rho1, _ = depth_upper(Vm)
        r = dict(H=H, L=pool.L, path=os.path.basename(path), eps_window=pool.eps_win,
                 Heps=H * pool.eps_win, upper=upper, h_min=pool.h_min,
                 m0=int(before['m']), m1=int(after['m']),
                 delta0=before['delta'], delta1=after['delta'],
                 rho0=rho0, rho1=rho1, sigma=after.get('sigma'),
                 r2=after.get('r2'), e2=after.get('e2'),
                 h_lower=after.get('h_lower'), best_round=after.get('round'),
                 rounds=len(hist) - 1,
                 secs=time.time() - t0, hist=hist)
        if not after.get('feasible', False) and hist:
            r['rho1'] = hist[-1]['rho_upper']      # separated: report the Farkas gap
        rec.append(r)
        log(f"  H={H}: m {r['m0']} -> {r['m1']}   delta {r['delta0']:.4e} -> "
            f"{r['delta1']:.4e} ({r['delta1'] / r['delta0']:.2f}x)   "
            f"rho_upper {rho0:.4e} -> {rho1:.4e}   {r['secs']:.0f}s")
        if out:
            json.dump(rec, open(out, 'w'), indent=1)
    return rec


def report(rec, log=print):
    log("\n" + "=" * 100)
    log(f"  {'H':>5} {'L':>3} {'m':>6} {'H eps':>7} {'delta (certified)':>19} "
        f"{'rho (upper)':>13} {'gamma_d':>8} {'gamma_r':>8} {'E_H >=':>11}")
    prev = None
    for r in sorted(rec, key=lambda z: (z['L'], z['H'])):
        gd = gr = float('nan')
        if prev is not None and prev['L'] == r['L'] and r['H'] > prev['H']:
            lr = math.log(r['H'] / prev['H'])
            gd = -math.log(r['delta1'] / prev['delta1']) / lr
            gr = -math.log(r['rho1'] / prev['rho1']) / lr
        log(f"  {r['H']:5d} {r['L']:3d} {r['m1']:6d} {r['Heps']:7.3f} "
            f"{r['delta1']:19.6e} {r['rho1']:13.6e} {gd:8.3f} {gr:8.3f} "
            f"{(r['h_lower'] if r['h_lower'] is not None else float('nan')):11.6f}")
        prev = r
    log("=" * 100)


LADDER12 = [(f'{BB}/r1b_pool64.json', H) for H in (4, 8, 16, 32, 64)]


def ladder_specs():
    sp = list(LADDER12)
    for H in (14, 32, 64, 128, 192):
        f = f'{BB}/r2a_pool_1+sqrt2_L14_{H}.npz'
        if os.path.exists(f):
            sp.append((f, H))
    return sp



def tilt_response(pool, Vm, u, ss=(-14, -9, -6, -4, -3, -2, -1.5, -1, -0.5, -0.2, 0,
                                  0.2, 0.5, 1, 1.5, 2, 3, 4, 6, 9, 14), log=print):
    """Where WP9's Farkas step is monotone, and where the certificate lives.

    The pool members are equilibrium states of the WINDOW observable `F~`, so the pressure
    is convex in `a` with gradient `Phi~(mu_a)` and the tilt `a* + s u` is monotone in
    `<u, Phi~>` -- guaranteed, by convexity, for every `u`.  The certificate is written in
    the ENCLOSED `Phi`, and `|Phi - Phi~| <= 2 pi h eps_L` is exactly the truncation scale
    of sec 7.  This tabulates both along one ray, which is how the stall of the Farkas
    loop at `(3+sqrt5)/2, H = 64` is diagnosed: `<u,Phi~>` crosses the separating plane
    comfortably, `<u,Phi>` never does, and every `s` at which `Phi~` is safely across has
    no member at all because the tilted chain has degenerated."""
    H = pool.H
    hs = list(range(1, H + 1))
    un = np.asarray(u, dtype=float) / max(np.linalg.norm(u), 1e-300)
    x0 = np.asarray(pool.xstar, dtype=float)
    out = []
    for s in ss:
        x = x0 + s * un
        a = x[:H] + 1j * x[H:]
        q = pool.bc.from_window(pool.win, a)
        row = dict(s=float(s), window=None, enclosed=None)
        if np.isfinite(q).all():
            pi, conv = pool.stationary(q)
            if pi is not None and np.isfinite(pi).all():
                pw = np.asarray(pool.bc.phis(q, hs, pi))
                row['window'] = float(np.dot(
                    un, np.concatenate([pw[:H].real, pw[:H].imag])))
        got = pool.member(x)
        if got is not None:
            row['enclosed'] = float(np.dot(
                un, np.concatenate([got[0][:H].real, got[0][:H].imag])))
        out.append(row)
        log(f"    s={s:+7.2f}   <u,Phi~> "
            + ("     --      " if row['window'] is None else f"{row['window']:+.6e}")
            + "   <u,Phi> "
            + ("member rejected" if row['enclosed'] is None
               else f"{row['enclosed']:+.6e}"))
    return out


def farkas(spec, rounds=8, out=None, log=print):
    """The one row R1b left open: run the Farkas loop where it was actually asked to work."""
    from r1b_certify import refute
    from r2a_pool import TSFINE, steer
    path, H = spec
    pool, Vm, ent, eps, upper = load_rung(spec)
    log(f"# Farkas loop at {pool.name}, H={H}, L={pool.L}, pool {Vm.shape[1]}, "
        f"H*eps_window {H * pool.eps_win:.3f}")
    rec = dict(alpha=float(pool.al.alpha), name=pool.name, H=H, L=pool.L,
               eps_window=pool.eps_win, rounds=[])
    u_prev = None
    for k in range(rounds + 1):
        u, gap = separate_lp(Vm)
        if u is None:
            log(f"  round {k}: no separating direction -- the pool is FEASIBLE")
            rec['rounds'].append(dict(round=k, m=int(Vm.shape[1]), gap=None))
            break
        r = refute(Vm, eps, H, u)
        log(f"  round {k}: m={Vm.shape[1]:<5} Farkas gap {gap:.6e}   certified "
            f"{r['gap']:.6e} = {r['gap'] / r['e2']:.2e} x the enclosure")
        rec['rounds'].append(dict(round=k, m=int(Vm.shape[1]), gap=float(gap),
                                  certified=float(r['gap']), e2=float(r['e2'])))
        if u_prev is not None and np.allclose(u, u_prev, rtol=1e-9, atol=1e-12):
            log("  the Farkas direction repeats: the tilt cannot reach its plane.")
            log("  response along that direction, in both coordinate systems:")
            rec['ray'] = tilt_response(pool, Vm, u, log=log)
            break
        u_prev = u
        if k == rounds:
            break
        got = pool.members(steer(pool, u, TSFINE))
        if got is None:
            break
        Vm = np.hstack([Vm, vmat(got[0], H)])
        ent = np.concatenate([ent, got[2]])
        eps = max(eps, got[1])
    if out:
        json.dump(rec, open(out, 'w'), indent=1)
        log(f"# wrote {out}")
    return rec


# ======================================================================================
# self-checks
# ======================================================================================
def selfchecks():
    import r1b_certify as C
    rng = np.random.default_rng(7)
    print("-- rounding-direction primitives")
    from mpmath import mp
    mp.dps = 60
    worst = 0.0
    for _ in range(200):
        n = int(rng.integers(2, 40))
        x = rng.standard_normal(n) * 10.0 ** rng.integers(-4, 4)
        exact = mp.sqrt(mp.fsum([mp.mpf(float(v)) ** 2 for v in x]))
        u = norm_up(x)
        if u < exact:
            worst = -1.0
            break
        worst = max(worst, float(u / exact) - 1.0)
    check("norm_up is an upper bound", worst >= 0.0,
          f"200 random vectors, worst overshoot {worst:.2e}")
    X = rng.standard_normal((12, 30))
    nu = norms_up(X)
    check("norms_up bounds every column norm",
          bool(np.all(nu >= np.linalg.norm(X, axis=0))) and
          bool(np.all(nu <= np.linalg.norm(X, axis=0) * (1 + 1e-12))),
          f"30 columns, worst overshoot "
          f"{float(np.max(nu / np.linalg.norm(X, axis=0)) - 1):.2e}")

    print("-- verified positive definiteness")
    A = rng.standard_normal((30, 30))
    A = A @ A.T + 3 * np.eye(30)
    check("pd_verified: PD matrix accepted", pd_verified(A))
    B = A - (float(np.linalg.eigvalsh(A)[0]) + 1e-9) * np.eye(30)
    check("pd_verified: indefinite matrix rejected", not pd_verified(B))
    check("pd_verified: singular matrix rejected", not pd_verified(np.ones((6, 6))))

    print("-- sigma_min: two independent verified methods must agree")
    for H in (4, 8, 16, 32, 64):
        if not os.path.exists(f'{BB}/r1b_pool64.json'):
            break
        _, row, Vm, _ = C.load_pool(f'{BB}/r1b_pool64.json', H)
        Wf = np.vstack([Vm, np.ones((1, Vm.shape[1]))])
        s_new, lam_lo, lam0, dG = sigma_min_lower(Wf)
        s_old, _, _ = C.sigma_min_lower(Wf)
        s_true = float(np.linalg.svd(Wf, compute_uv=False)[-1])
        check(f"sigma_min H={H}",
              s_new <= s_true * (1 + 1e-12) and s_new >= s_old
              and s_new >= s_true * (1 - 1e-6),
              f"Rump/LAPACK {s_new:.9f} >= R1b interval Cholesky {s_old:.9f}, "
              f"and within {1 - s_new / s_true:.1e} of svd {s_true:.9f}")

    print("-- Theorem 1' dominates Theorem 1")
    _, row, Vm, ent = C.load_pool(f'{BB}/r1b_pool64.json', 32)
    m = Vm.shape[1]
    Wf = np.vstack([Vm, np.ones((1, m))])
    sig, lam_lo, lam0, dG = sigma_min_lower(Wf)
    g, Z = rowpinv_upper(Wf, lam_lo, dG)
    g_true = np.linalg.norm(np.linalg.pinv(Wf), axis=1)
    check("g_j bounds the true row norms", bool(np.all(g >= g_true)),
          f"max shortfall {float(np.max(g_true - g)):.2e}, "
          f"worst overshoot {float(np.max(g / g_true) - 1):.2e}")
    check("g_j <= 1/sigma_min, so (C') implies (C)", bool(np.all(g <= 1.0 / sig)),
          f"max g {float(g.max()):.4f} vs 1/sigma = {1 / sig:.4f}")

    print("-- the exact residual, in integers vs Fractions")
    lam, R0 = weighted_maximin_lp(Vm, g)
    lam = refine(Vm, lam)
    D = 10 ** 14
    a = rationalise(np.maximum(lam, 0.0), D)
    r_int, e = exact_residual(Vm, a, D)
    r_frac, _ = C.exact_residual(Vm, a, D)
    check("integer and Fraction residuals agree", abs(r_int - r_frac) <= 4 * U * r_frac,
          f"{r_int:.6e} vs {r_frac:.6e}   (2^{e} scaling)")
    Vt = np.array([[0.5, -0.25], [1.0, 1.0]])      # lam = (1/4, 3/4): r = (-1/16, 1)
    rt, _ = exact_residual(Vt, [1, 3], 4)
    true = math.sqrt(257) / 16
    check("exact residual on a hand case", true <= rt <= true * (1 + 1e-15),
          f"{rt:.17f} vs sqrt(257)/16 = {true:.17f}")

    print("-- the certificate on synthetic data with a known answer")
    d2 = 8
    Vx = np.hstack([np.eye(d2), -np.eye(d2)]) * 0.75      # cross-polytope, inradius s/sqrt d
    res = margin(Vx, 0.0, d2 // 2)
    rho_true = 0.75 / math.sqrt(d2)
    rho_up, _ = depth_upper(Vx)
    check("cross-polytope: certificate below the true inradius",
          res['feasible'] and 0 < res['delta'] <= rho_true * (1 + 1e-9),
          f"delta {res['delta']:.6f}   true inradius {rho_true:.6f}")
    check("cross-polytope: depth_upper finds the inradius",
          abs(rho_up - rho_true) < 1e-6, f"{rho_up:.9f} vs {rho_true:.9f}")
    Vy = np.abs(rng.standard_normal((6, 40))) + 0.1        # all in the positive orthant
    res_y = margin(Vy, 0.0, 3)
    check("half-space pool is refused", (not res_y['feasible']) or res_y['delta'] <= 0,
          f"feasible={res_y['feasible']}  delta={res_y['delta']:.2e}")

    print("-- the bracket, and monotonicity in the pool")
    for H in (8, 32, 64):
        _, row, Vm, ent = C.load_pool(f'{BB}/r1b_pool64.json', H)
        res = margin(Vm, row['radius'], H, ent=ent)
        rho_up, _ = depth_upper(Vm)
        check(f"delta <= rho_upper at H={H}", res['delta'] < rho_up,
              f"{res['delta']:.4e} <= {rho_up:.4e}   (factor {rho_up / res['delta']:.1f})")
    _, row, Vm, ent = C.load_pool(f'{BB}/r1b_pool64.json', 16)
    half = Vm[:, ::2]
    r_half, _ = depth_upper(half)
    r_full, _ = depth_upper(Vm)
    check("depth_upper is monotone under adding members", r_full >= r_half - 1e-12,
          f"half pool {r_half:.4e} -> full pool {r_full:.4e}")

    print("-- Theorem 1 (R1b) is reproduced when g is taken uniform")
    if os.path.exists(f'{BB}/r1b_certify.json'):
        ref = json.load(open(f'{BB}/r1b_certify.json'))
        for H in (8, 32, 64):
            key = f"1+sqrt2:{H}"
            if key not in ref:
                continue
            _, row, Vm, ent = C.load_pool(f'{BB}/r1b_pool64.json', H)
            m = Vm.shape[1]
            sig, lam_lo, lam0, dG = sigma_min_lower(np.vstack([Vm, np.ones((1, m))]))
            lam, t = C.maximin_lp(Vm)
            lam = C.refine(Vm, lam)
            out = C.certify(Vm, row['radius'], H, lam, 10 ** 14, ent=ent,
                            sig_data=(sig, dG, lam0))
            r = ref[key]['maximin']
            check(f"R1b delta reproduced at H={H}",
                  abs(out['delta'] / r['delta'] - 1) < 5e-3,
                  f"recomputed {out['delta']:.6e}  recorded {r['delta']:.6e}")
    print(f"\n  {_ok} checks passed, {_bad} failed")
    return 0 if _bad == 0 else 1


def main():
    if '--checks' in sys.argv:
        return selfchecks()
    if '--farkas' in sys.argv:
        i = sys.argv.index('--farkas')
        a = sys.argv[i + 1]
        farkas((a.rsplit(':', 1)[0], int(a.rsplit(':', 1)[1])),
               out=f'{BB}/r2a_farkas.json')
        return 0
    if '--ladder' in sys.argv:
        i = sys.argv.index('--ladder')
        arg = sys.argv[i + 1:]
        specs = ladder_specs() if not arg else [
            (a.rsplit(':', 1)[0], int(a.rsplit(':', 1)[1])) for a in arg]
        rec = ladder(specs, out=f'{BB}/r2a_margin.json')
        report(rec)
        return 0
    rc = selfchecks()
    rec = ladder(ladder_specs(), out=f'{BB}/r2a_margin.json')
    report(rec)
    return rc


if __name__ == '__main__':
    sys.exit(main())
