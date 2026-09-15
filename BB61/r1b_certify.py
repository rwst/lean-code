#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R1b: the interior-of-hull certificate -- a PROOF that `K_H(alpha)` is non-empty.

`K_H = {mu in M(sigma) : Phi_h(mu) = 0, 1 <= h <= H}` where `Phi_h(mu) = int e(h F) dmu`.
`K_H` is a slice of the invariant measures by `2H` exact linear equations, so it has empty
interior and a numerical near-solution is no evidence at all that it is non-empty (the
sec-4 QA finding of `plan-BB61-counterexample.html`).  R1a supplied the missing ingredient:
a pool of measures given EXACTLY (rational circulations on the order-L de Bruijn graph)
together with a rigorous enclosure radius for each `Phi_h`.  This file turns that into a
theorem, by the following lemma -- the whole of R1b in six lines.

---------------------------------------------------------------------------------------
THEOREM (interior certificate).  Let `nu_1,...,nu_m` be shift-invariant probability
measures, `H >= 1`, and identify `Phi(nu) = (Re Phi_1,...,Re Phi_H, Im Phi_1,...,Im Phi_H)
in R^{2H}`.  Let `V in R^{2H x m}` have columns `V_j` with

        |Phi(nu_j) - V_j|_2 <= e2      for every j,                                  (E)

let `W = [V ; 1^T] in R^{(2H+1) x m}` and let `sigma > 0` satisfy `sigma <= sigma_min(W)`.
Let `lam in R^m` with `lam_j >= t > 0`, `1^T lam = 1`, and put `r = V lam`.  If

        delta := t*sigma - |r|_2 - e2  >  0                                          (C)

then there is `lam'' in the simplex with `sum_j lam''_j Phi(nu_j) = 0`; hence
`mu = sum_j lam''_j nu_j` lies in `K_H`, so `K_H != empty`.  Moreover
`|lam'' - lam|_2 <= (|r|_2 + e2)/sigma`, so

        h(mu) >= sum_j lam_j h(nu_j) - (|r|_2 + e2)/sigma * sqrt(m) * log 2 .        (H)

PROOF.  (i) *The ball.*  `sigma_min(W) >= sigma > 0` makes `W` surjective onto `R^{2H+1}`
with `|W^+| <= 1/sigma`.  Given `y in R^{2H}` with `|y|_2 <= t*sigma`, put
`mu_y = W^+ (y, 0)`, so `V mu_y = y`, `1^T mu_y = 0`, `|mu_y|_2 <= t`.  Then
`lam + mu_y` is again a probability vector (each coordinate `>= t - |mu_y|_2 >= 0`) and
`V(lam + mu_y) = r + y`.  So `B(r, t*sigma)` is contained in `conv{V_j}`, and the map
`y |-> lam + W^+(y,0)` is an affine, hence continuous, selection of weights.

(ii) *Brouwer.*  Write `Phi(nu_j) = V_j + e_j`, `|e_j|_2 <= e2` by (E).  For
`w in B := B(0, e2) subset R^{2H}` set `y(w) = -w - r`; then
`|y(w)|_2 <= e2 + |r|_2 < t*sigma` by (C), so `L(w) := lam + W^+(y(w), 0)` is a
probability vector, affine in `w`, with `V L(w) = -w`.  Define
`Psi(w) = sum_j L(w)_j e_j`; it is continuous and `|Psi(w)|_2 <= max_j |e_j|_2 <= e2`,
so `Psi : B -> B`.  Brouwer gives `w*` with `Psi(w*) = w*`, and then
`sum_j L(w*)_j Phi(nu_j) = V L(w*) + Psi(w*) = -w* + w* = 0`.  Take `lam'' = L(w*)`.

(iii) *Entropy.*  `|lam'' - lam|_2 = |W^+(y(w*),0)|_2 <= (e2 + |r|_2)/sigma`, and
`h` is concave on `M(sigma)` while `0 <= h(nu_j) <= log 2`, so
`h(mu) >= sum_j lam''_j h(nu_j) >= sum_j lam_j h(nu_j) - |lam''-lam|_2 |h|_2`.  []
---------------------------------------------------------------------------------------

Every quantity in (C) is computed here with a proof of its own direction of error:

  * `e2 = eps * sqrt(H)` from R1a's per-mode radius `eps` (truncation, M4 Prop. 3 in
    Fourier form, plus an a-priori float64 rounding bound);
  * `lam` is an EXACT rational vector `a_j / D`, so `t = min_j a_j / D` and
    `1^T lam = 1` hold exactly, and `r = V lam` is computed in exact rational arithmetic
    (float64 entries are dyadic rationals) with `|r|_2` rounded up by integer sqrt;
  * `sigma` comes from an interval Cholesky, in directed-rounding float intervals, of
    `[G] - sigma^2 I` where `[G]` encloses `W W^T` via the standard `gamma_m` dot-product
    bound: success proves `lam_min(W W^T) > sigma^2`.

Usage:  python3 r1b_certify.py                 # self-checks, then certify every pool file
        python3 r1b_certify.py --checks        # self-checks only
"""
import json
import math
import os
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')

BB = '/home/ralf/math/lean-code/BB61'
INF = float('inf')
U = 2.0 ** -53                      # unit roundoff of binary64
LOG2 = math.log(2.0)
ENT_SLACK = 1e-11                   # a-priori bound on `Circulation.entropy()` in float64

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


# ======================================================================================
# directed-rounding intervals on binary64 -- enough for a Cholesky, and fast
# ======================================================================================
def dn(x):
    return math.nextafter(x, -INF)


def up(x):
    return math.nextafter(x, INF)


class Iv:
    """[a,b] with outward rounding by one ulp after every operation.

    `fl(z)` is the nearest binary64 to `z`, so `|fl(z) - z| <= ulp(fl(z))/2` and therefore
    `z` lies in `[nextafter(fl(z),-inf), nextafter(fl(z),+inf)]`.  Widening each computed
    endpoint by one ulp is thus sound for +, -, * and sqrt on finite operands."""

    __slots__ = ('a', 'b')

    def __init__(self, a, b=None):
        self.a = a
        self.b = a if b is None else b

    def __add__(self, o):
        return Iv(dn(self.a + o.a), up(self.b + o.b))

    def __sub__(self, o):
        return Iv(dn(self.a - o.b), up(self.b - o.a))

    def __mul__(self, o):
        p = (self.a * o.a, self.a * o.b, self.b * o.a, self.b * o.b)
        return Iv(dn(min(p)), up(max(p)))

    def __truediv__(self, o):
        assert o.a > 0.0, "interval division through zero"
        p = (self.a / o.a, self.a / o.b, self.b / o.a, self.b / o.b)
        return Iv(dn(min(p)), up(max(p)))

    def sqrt(self):
        assert self.a >= 0.0
        return Iv(dn(math.sqrt(self.a)), up(math.sqrt(self.b)))

    def __repr__(self):
        return f"[{self.a!r}, {self.b!r}]"


def cholesky_pd(Gm, rad, shift, scale=None):
    """True => `A - shift*I > 0` for every symmetric `A` the data admits.

    The recursion is run on `S = D^-1 (A - shift I) D^-1` with `D = diag(scale)` positive;
    congruence by a positive diagonal preserves positive definiteness exactly, so the
    conclusion is about `A - shift I` itself, and `scale` need not be accurate for
    soundness -- only positive.  `rad` is the entrywise radius **in the scaled matrix**.

    Two reasons the scaling is not cosmetic here.  (i) The naive interval Cholesky is very
    sensitive to a spread-out diagonal, and the appended row of ones makes `G_dd = m` while
    the high-mode rows have `G_ii` orders of magnitude smaller (a near-flat measure has
    tiny high Fourier coefficients).  (ii) With `scale_i = sqrt(G_ii)`, Cauchy-Schwarz turns
    the dot-product bound `gamma_m sum_k |W_ik W_jk| <= gamma_m sqrt(G_ii G_jj)` into a
    *uniform* radius `gamma_m` in the scaled matrix -- three orders tighter, at `d = 129`,
    than the flat `gamma_m m max|W|^2`."""
    d = len(Gm)
    if scale is None:
        scale = [1.0] * d
    R = Iv(-rad, rad)
    A = [[None] * d for _ in range(d)]
    for i in range(d):
        for j in range(d):
            g = Gm[i][j] - shift if i == j else Gm[i][j]
            q = Iv(dn(g), up(g)) / Iv(dn(scale[i] * scale[j]), up(scale[i] * scale[j]))
            A[i][j] = q + R
    L = [[Iv(0.0) for _ in range(d)] for _ in range(d)]
    for i in range(d):
        s = A[i][i]
        for k in range(i):
            s = s - L[i][k] * L[i][k]
        if not (s.a > 0.0):
            return False
        L[i][i] = s.sqrt()
        for j in range(i + 1, d):
            s = A[i][j]
            for k in range(i):
                s = s - L[i][k] * L[j][k]
            L[j][i] = s / L[i][i]
    return True


def sigma_min_lower(Wf, steps=10):
    """Rigorous lower bound for `sigma_min(W)`, `W` the (2H+1) x m float matrix.

    `G = W W^T` is formed in float64; the standard bound
    `|fl(sum_j a_j b_j) - sum_j a_j b_j| <= gamma_m sum_j |a_j b_j|`, valid for any
    summation order and with or without FMA, gives an entrywise enclosure radius.  A
    bisection then finds the largest verified `shift` with `[G] - shift*I > 0`."""
    d, m = Wf.shape
    G = (Wf @ Wf.T).astype(float)
    G = 0.5 * (G + G.T)
    gam = m * U / (1.0 - m * U)
    # Cauchy-Schwarz: |fl(G_ij) - (W W^T)_ij| <= gamma_m sum_k |W_ik W_jk|
    #                                        <= gamma_m sqrt(G_ii G_jj) (1 + O(gamma_m)),
    # so after scaling by sqrt(diag G) the entrywise radius is the constant below.
    rad = up(gam * (1.0 + 4.0 * m * U))
    lam = float(np.linalg.eigvalsh(G)[0])
    if lam <= 0.0:
        return 0.0, rad, lam
    Gm = [[float(G[i][j]) for j in range(d)] for i in range(d)]
    sc = [math.sqrt(max(float(G[i][i]), 1e-300)) for i in range(d)]
    lo, hi = 0.0, lam
    if not cholesky_pd(Gm, rad, 0.0, sc):
        return 0.0, rad, lam
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        if cholesky_pd(Gm, rad, mid, sc):
            lo = mid
        else:
            hi = mid
    return dn(math.sqrt(lo)), rad, lam


# ======================================================================================
# exact rational side: the weights, and the residual
# ======================================================================================
def rationalise(lam, D):
    """`lam` (float, approximately in the simplex) -> integers `a_j >= 1` with `sum = D`."""
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


def sqrt_upper(q):
    """Upper bound in binary64 for `sqrt(q)`, `q` a non-negative Fraction."""
    n, dd = q.numerator, q.denominator
    if n == 0:
        return 0.0
    r = math.isqrt(n * dd) + 1
    return up(r / dd)


def exact_residual(Vf, a, D):
    """`r = V lam` exactly (float64 entries are dyadic rationals); returns `|r|_2` up."""
    d, m = Vf.shape
    tot = Fr(0)
    rows = []
    for i in range(d):
        s = Fr(0)
        row = Vf[i]
        for j in range(m):
            s += a[j] * Fr(float(row[j]))
        s /= D
        rows.append(s)
        tot += s * s
    return sqrt_upper(tot), rows


# ======================================================================================
# the linear programmes (float; only used to PROPOSE `lam` -- the proof never trusts them)
# ======================================================================================
def maximin_lp(Vm):
    d, m = Vm.shape
    A_eq = np.vstack([np.hstack([Vm, np.zeros((d, 1))]), np.append(np.ones(m), 0.0)])
    b_eq = np.append(np.zeros(d), 1.0)
    A_ub = np.hstack([-np.eye(m), np.ones((m, 1))])
    r = linprog(np.append(np.zeros(m), -1.0), A_ub=A_ub, b_ub=np.zeros(m),
                A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * m + [(None, None)],
                method='highs', options=LPOPT)
    return (np.asarray(r.x[:m]), float(r.x[-1])) if r.success else (None, None)


def refine(Vm, lam, rounds=2):
    """Push `lam` onto `{V lam = 0, 1^T lam = 1}` along the lemma's own map.

    `lam <- lam + W^+(-(r, s))` is exactly the correction of step (i) of the theorem, so it
    moves each coordinate by at most `(|r|_2 + |s|)/sigma_min(W)` and costs that much of
    the floor `t`.  Two rounds put the float residual at rounding level; the certificate
    then re-derives `|r|_2` in exact rational arithmetic anyway, and never trusts this."""
    d, m = Vm.shape
    W = np.vstack([Vm, np.ones((1, m))])
    Wp = np.linalg.pinv(W)
    lam = np.array(lam, dtype=float)
    for _ in range(rounds):
        res = np.append(Vm @ lam, lam.sum() - 1.0)
        lam = lam - Wp @ res
    return lam


def separate_lp(Vm):
    """max d subject to <u, V_j> >= d for all j, |u|_inf <= 1 -- the Farkas direction."""
    d, m = Vm.shape
    A_ub = np.hstack([-Vm.T, np.ones((m, 1))])
    r = linprog(np.append(np.zeros(d), -1.0), A_ub=A_ub, b_ub=np.zeros(m),
                bounds=[(-1, 1)] * d + [(None, None)], method='highs', options=LPOPT)
    return (np.asarray(r.x[:d]), float(r.x[-1])) if r.success else (None, None)


def refute(Vm, eps, H, u, D=10 ** 14):
    """Certify `0 not in conv{Phi(nu_j)}` -- a proved "pool too small", not a solver verdict.

    With `u` rational and `<u, V_j> >= d` for every `j`,
    `<u, Phi(nu_j)> >= d - |u|_2 e2`, so a positive value separates `0` from the hull.
    This proves nothing about `K_H` itself (that is a statement about all of `M(sigma)`,
    sec 6.3's "catch"); what it does give is the exact direction the pool is missing, which
    is what the Farkas / pool-augmentation loop of R2a consumes."""
    d, m = Vm.shape
    b = [int(round(float(x) * D)) for x in u]
    if not any(b):
        return None
    lo = None
    for j in range(m):
        acc = Fr(0)
        for i in range(d):
            if b[i]:
                acc += b[i] * Fr(float(Vm[i, j]))
        acc /= D
        lo = acc if lo is None else min(lo, acc)
    n2 = sqrt_upper(Fr(sum(x * x for x in b), D * D))
    e2 = up(eps * up(math.sqrt(H)))
    gap = dn(float(lo) - up(n2 * e2))
    return dict(d=float(lo), u_norm=n2, e2=e2, gap=gap, D=D)


def entropy_lp(Vm, ent, t0):
    """max sum lam_j h(nu_j) subject to `V lam = 0`, `1^T lam = 1`, `lam_j >= t0`."""
    d, m = Vm.shape
    A_eq = np.vstack([Vm, np.ones((1, m))])
    b_eq = np.append(np.zeros(d), 1.0)
    r = linprog(-np.asarray(ent), A_eq=A_eq, b_eq=b_eq, bounds=(t0, None),
                method='highs', options=LPOPT)
    return np.asarray(r.x) if r.success else None


# ======================================================================================
# the certificate
# ======================================================================================
def certify(Vm, eps, H, lam, D, ent=None, sig_data=None):
    """Evaluate condition (C) for the proposed weights `lam`.  Returns the four numbers.

    `sig_data` caches `sigma_min_lower(W)`, which depends on the pool and not on `lam`."""
    d, m = Vm.shape
    assert d == 2 * H
    a = rationalise(lam, D)
    t = dn(min(a) / D)
    if sig_data is None:
        sig_data = sigma_min_lower(np.vstack([Vm, np.ones((1, m))]))
    sig, gram_rad, lam_min = sig_data
    rn, _ = exact_residual(Vm, a, D)
    e2 = up(eps * up(math.sqrt(H)))
    delta = dn(dn(dn(t * sig) - rn) - e2)
    out = dict(H=H, m=m, eps=eps, e2=e2, t=t, sigma=sig, r2=rn, delta=delta,
               gram_rad=gram_rad, lam_min_float=lam_min, D=D,
               ratio=(delta / e2 if e2 > 0 else float('inf')))
    if ent is not None:
        h_lam = math.fsum(float(a[j]) / D * (float(ent[j]) - ENT_SLACK) for j in range(m))
        drift = (up(up(rn + e2) / sig) * up(math.sqrt(m)) * LOG2
                 if sig > 0 else float('inf'))
        out['h_mix'] = h_lam
        out['h_drift'] = drift
        out['h_lower'] = dn(h_lam - drift)
    return out


def load_pool(path, H):
    d = json.load(open(path))
    row = d['rows'][str(H)]
    phi = np.array(row['phi_re']) + 1j * np.array(row['phi_im'])
    Vm = np.concatenate([phi[:, :H].real, phi[:, :H].imag], axis=1).T.copy()
    return d, row, Vm, np.array(row['ent'])


# ======================================================================================
# self-checks
# ======================================================================================
def selfchecks():
    from mpmath import iv, mp
    import r1a_enclose as R
    rng = np.random.default_rng(20260826)
    print("# R1b self-checks")

    # 1. the interval class
    worst = 0.0
    for _ in range(20000):
        x, y = rng.normal(size=2) * rng.choice([1e-8, 1.0, 1e6])
        X, Y = Iv(x), Iv(y)
        for Z, exact in ((X + Y, Fr(x) + Fr(y)), (X - Y, Fr(x) - Fr(y)),
                         (X * Y, Fr(x) * Fr(y))):
            assert Fr(Z.a) <= exact <= Fr(Z.b), (x, y)
            worst = max(worst, Z.b - Z.a)
    z = Iv(2.0).sqrt()
    check("Iv encloses exact +,-,* (20000 triples)", Fr(z.a) ** 2 <= 2 <= Fr(z.b) ** 2,
          f"sqrt(2) in [{z.a:.17g}, {z.b:.17g}]")

    # 2. interval Cholesky against numpy, both directions
    agree = 0
    for _ in range(60):
        d = rng.integers(2, 9)
        B = rng.normal(size=(d, d))
        A = B @ B.T + rng.choice([-1.0, 0.0, 1.0]) * 0.05 * np.eye(d)
        A = 0.5 * (A + A.T)
        lm = float(np.linalg.eigvalsh(A)[0])
        pd = cholesky_pd([[float(A[i][j]) for j in range(d)] for i in range(d)], 0.0, 0.0)
        if abs(lm) > 1e-8:
            agree += (pd == (lm > 0))
        else:
            agree += 1
    check("interval Cholesky <-> eigvalsh agree", agree == 60, f"{agree}/60")

    # 3. Cholesky is CONSERVATIVE, never optimistic: a PD-certified matrix has lam_min>0
    bad = 0
    for _ in range(40):
        d = int(rng.integers(3, 12))
        B = rng.normal(size=(d, d))
        A = 0.5 * (B @ B.T + (B @ B.T).T)
        s = float(np.linalg.eigvalsh(A)[0])
        Gm = [[float(A[i][j]) for j in range(d)] for i in range(d)]
        for sh in (0.5 * s, 1.5 * s):
            if cholesky_pd(Gm, 1e-13, sh) and not (s - sh > -1e-9):
                bad += 1
    check("Cholesky never certifies a non-PD shift", bad == 0, f"{bad} false positives")

    # 4. the ball lemma, constructively
    d, m = 6, 25
    V = rng.normal(size=(d, m))
    lam = rng.random(m) + 0.5
    lam /= lam.sum()
    t = float(lam.min())
    W = np.vstack([V, np.ones((1, m))])
    sig = float(np.linalg.svd(W, compute_uv=False)[-1])
    r = V @ lam
    worst_neg, worst_err = 0.0, 0.0
    for _ in range(300):
        y = rng.normal(size=d)
        y *= (t * sig * 0.999) / np.linalg.norm(y)
        mu = np.linalg.pinv(W) @ np.append(y, 0.0)
        lp = lam + mu
        worst_neg = min(worst_neg, float(lp.min()))
        worst_err = max(worst_err, float(np.max(np.abs(V @ lp - (r + y)))),
                        abs(float(lp.sum()) - 1.0))
    check("ball lemma: lam + W^+(y,0) stays in the simplex", worst_neg >= -1e-12,
          f"min coord {worst_neg:.2e}, |V lam' - (r+y)| {worst_err:.2e}")

    # 5. and it is tight: just outside t*sigma the construction can leave the simplex
    esc = 0
    for _ in range(300):
        y = rng.normal(size=d)
        y *= (t * sig * 8.0) / np.linalg.norm(y)
        mu = np.linalg.pinv(W) @ np.append(y, 0.0)
        esc += (lam + mu).min() < 0
    check("radius t*sigma is not vacuous", esc > 0, f"{esc}/300 escape at 8 t*sigma")

    # 6. exact residual against the float product
    a = rationalise(lam, 10 ** 12)
    rn, rows = exact_residual(V, a, 10 ** 12)
    fl = float(np.linalg.norm(V @ (np.array(a, dtype=float) / 10 ** 12)))
    check("exact residual matches float", abs(rn - fl) <= 1e-9 * max(fl, 1e-12),
          f"exact {rn:.6e} vs float {fl:.6e}")

    # 7. sqrt_upper really rounds up
    bad = 0
    for _ in range(2000):
        q = Fr(int(rng.integers(1, 10 ** 12)), int(rng.integers(1, 10 ** 12)))
        s = sqrt_upper(q)
        bad += not (Fr(s) * Fr(s) >= q)
    check("sqrt_upper is an upper bound", bad == 0, f"{bad}/2000 failures")

    # 8. Gram a-priori bound against high precision
    m2 = 400
    Wf = rng.normal(size=(9, m2))
    G = Wf @ Wf.T
    mp.dps = 40
    err = 0.0
    for i in range(9):
        for j in range(9):
            s = mp.mpf(0)
            for k in range(m2):
                s += mp.mpf(float(Wf[i, k])) * mp.mpf(float(Wf[j, k]))
            err = max(err, abs(float(s) - float(G[i, j])))
    gam = m2 * U / (1 - m2 * U)
    bnd = gam * m2 * float(np.max(np.abs(Wf))) ** 2
    check("Gram float error inside the gamma_m bound", err <= bnd,
          f"observed {err:.2e} <= bound {bnd:.2e}")

    # 9. sigma_min_lower is a lower bound and not silly
    Wf = rng.normal(size=(7, 90))
    sig, _, _ = sigma_min_lower(Wf)
    true = float(np.linalg.svd(Wf, compute_uv=False)[-1])
    check("sigma_min_lower brackets sigma_min", sig <= true and sig >= 0.9 * true,
          f"{sig:.6f} <= {true:.6f}, ratio {sig / true:.4f}")

    # 10. entropy of a circulation, float64 against interval logs
    iv.dps = 30
    c = R.circ_bernoulli(6, Fr(3, 7))
    hf = c.entropy()
    hb = iv.mpf(0)
    for b in range(c.n):
        q = iv.mpf(c.q[b].numerator) / iv.mpf(c.q[b].denominator)
        p = iv.mpf(c.pi[b].numerator) / iv.mpf(c.pi[b].denominator)
        if 0 < c.q[b] < 1:
            hb -= p * (q * iv.log(q) + (1 - q) * iv.log(1 - q))
    exact = float(-(Fr(3, 7) * math.log(3 / 7) + Fr(4, 7) * math.log(4 / 7)))
    check("Circulation.entropy in float64 vs interval logs", abs(hf - float(hb.a)) < 1e-14,
          f"float {hf:.15f}  interval [{float(hb.a):.15f}, {float(hb.b):.15f}]  "
          f"Bernoulli(3/7) {exact:.15f}  slack used {ENT_SLACK:.0e}")

    # 11. a pool that does NOT surround 0 must be rejected
    Vbad = np.abs(rng.normal(size=(4, 30))) + 0.2
    lamb, tb = maximin_lp(Vbad)
    check("negative control: one-sided pool is infeasible", lamb is None or tb <= 0,
          "maximin LP infeasible" if lamb is None else f"t = {tb:.2e}")

    # 12. shrinking t shrinks delta proportionally (the certificate is not accidental)
    d, m = 4, 40
    V = rng.normal(size=(d, m))
    lam0, t0 = maximin_lp(V)
    if lam0 is not None and t0 > 0:
        c1 = certify(V, 1e-13, d // 2, lam0, 10 ** 12)
        lam1 = entropy_lp(V, rng.random(m), t0 / 10)
        c2 = certify(V, 1e-13, d // 2, lam1, 10 ** 12)
        check("delta scales with t", c2['delta'] < c1['delta'] and c2['delta'] > 0,
              f"t {c1['t']:.3e} -> {c2['t']:.3e}, delta {c1['delta']:.3e} -> "
              f"{c2['delta']:.3e}")

    # 13. R1a's enclosure claim, re-verified on a circulation built here
    c = R.circ_from_word(8, [1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1])
    hs = [1, 5, 13]
    val, rad = R.phi_fl(c, hs, 60, 60)
    box = R.phi_iv(c, hs, 60, 60)
    okall = all(abs(complex(float(box[i].real.mid), float(box[i].imag.mid)) - val[i])
                <= rad[i] for i in range(len(hs)))
    check("phi_fl radius covers the interval enclosure", okall,
          f"radius {max(rad):.3e}, worst gap "
          f"{max(abs(complex(float(box[i].real.mid), float(box[i].imag.mid)) - val[i]) for i in range(len(hs))):.3e}")
    # 12b. the refutation side: a one-sided pool must be certifiably separated from 0
    Vb = np.abs(rng.normal(size=(6, 40))) + 0.3
    ub, db = separate_lp(Vb)
    sepb = refute(Vb, 1e-13, 3, ub) if ub is not None else None
    check("refutation: one-sided pool is certifiably separated from 0",
          sepb is not None and sepb['gap'] > 0,
          f"d = {sepb['d']:.4f}, gap = {sepb['gap']:.4f}" if sepb else "no direction")

    # 12c. and a pool that DOES surround 0 must not be separable
    Vg = rng.normal(size=(6, 40))
    ug, dg = separate_lp(Vg)
    sepg = refute(Vg, 1e-13, 3, ug) if ug is not None else None
    check("refutation: a surrounding pool is not separable", sepg is None or
          sepg['gap'] <= 0, f"gap = {sepg['gap']:.3e}" if sepg else "no direction")

    # 13b. the same, on a REPAIRED order-12 circulation with 4096 distinct branch
    # probabilities -- the shape the pool actually has, and the one ENT_SLACK must cover.
    # Reference is mpmath at 30 digits (check 10 does the interval-log version, where a
    # closed form is available to compare against as well).
    L = 12
    n, mask = 1 << L, (1 << L) - 1
    q = 0.02 + 0.96 * rng.random(n)
    t0, t1 = ((np.arange(n) << 1) & mask), (((np.arange(n) << 1) | 1) & mask)
    pi = np.ones(n) / n                      # power iteration for the true stationary pi
    for _ in range(4000):
        nxt = np.zeros(n)
        np.add.at(nxt, t0, pi * (1 - q))
        np.add.at(nxt, t1, pi * q)
        pi = nxt / nxt.sum()
    wv = np.empty(1 << (L + 1))
    wv[0::2], wv[1::2] = pi * (1 - q), pi * q
    c = R.circ_from_weights(12, wv, 10 ** 10)
    hf = c.entropy()
    mp.dps = 30
    hb = mp.mpf(0)
    for b in range(c.n):
        if 0 < c.q[b] < 1:
            qq = mp.mpf(c.q[b].numerator) / mp.mpf(c.q[b].denominator)
            pp = mp.mpf(c.pi[b].numerator) / mp.mpf(c.pi[b].denominator)
            hb -= pp * (qq * mp.log(qq) + (1 - qq) * mp.log(1 - qq))
    check("entropy slack covers an order-12 repaired circulation",
          abs(hf - float(hb)) < ENT_SLACK,
          f"float {hf:.15f}, mpmath30 {float(hb):.15f}, gap {abs(hf - float(hb)):.2e} "
          f"< slack {ENT_SLACK:.0e}")

    # 14. rank control: fewer columns than 2H+1 can never certify, whatever the weights
    V = rng.normal(size=(8, 8))            # m = 8 < 2H+1 = 9
    lam = np.full(8, 1 / 8)
    c = certify(V, 1e-13, 4, lam, 10 ** 12)
    check("rank control: m < 2H+1 gives sigma = 0 and no certificate",
          c['sigma'] == 0.0 and c['delta'] <= 0,
          f"sigma {c['sigma']:.1e}, delta {c['delta']:.1e}")

    # 15. the ladder at a general quadratic unit, against m7_price's own coefficients
    from m0_engine import Alpha
    from m7_price import BlockChain
    worst, det = 0.0, []
    for A, B, nm in ((2, 1, '1+sqrt2'), (3, -1, 'golden2'), (3, 1, 'root13')):
        al = Alpha([1, -A, -B], nm)
        R.set_alpha(A, B, nm)
        L, hs = 8, [1, 2, 3, 6]
        bc = BlockChain(al, L, hmax=6)
        g = np.random.default_rng(7)
        w0 = 0.0
        for _ in range(3):
            q = 0.15 + 0.7 * g.random(1 << L)
            pi = bc.stationary(q)
            w = np.empty(1 << (L + 1))
            w[0::2], w[1::2] = pi * (1 - q), pi * q
            c = R.circ_from_weights(L, w, 10 ** 12)
            V, _ = R.phi_fl(c, hs, 60, 60)
            w0 = max(w0, float(np.max(np.abs(V - np.asarray(bc.phis(q, hs, pi))))))
        det.append(f"{nm} {w0:.1e}")
        worst = max(worst, w0)
    R.set_alpha(2, 1, '1+sqrt2')
    check("generalised ladder vs BlockChain.phis at 3 units", worst < 1e-9, "; ".join(det))
    print(f"# self-checks: {_ok} ok, {_bad} failed\n")


# ======================================================================================
def run(paths, Hs=None):
    print("# R1b   interior-of-hull certificates")
    print("#   condition (C):  delta = t*sigma - |r|_2 - eps*sqrt(H) > 0\n")
    rec = {}
    for path in paths:
        d = json.load(open(path))
        nm = d.get('name', '1+sqrt2')
        print(f"### alpha = {nm}   ({d['alpha']:.9f}),  h_min = {d['h_min']:.6f},  "
              f"pool from {os.path.basename(path)}")
        for Hs_ in sorted(d['rows'], key=int):
            H = int(Hs_)
            if Hs and H not in Hs:
                continue
            _, row, Vm, ent = load_pool(path, H)
            hmin = float(d['h_min'])
            m = Vm.shape[1]
            eps = float(row['radius'])
            lam, tmax = maximin_lp(Vm)
            if lam is None or tmax is None or tmax <= 0:
                print(f"H={H:<3} pool {m:4d}   eps {eps:.3e}   maximin LP infeasible")
                u, dd = separate_lp(Vm)
                sep = refute(Vm, eps, H, u) if u is not None else None
                if sep and sep['gap'] > 0:
                    print(f"      REFUTED: 0 is NOT in conv, certified.  separation "
                          f"d = {sep['d']:.6e}, |u|_2 = {sep['u_norm']:.3f}, "
                          f"e2 = {sep['e2']:.2e}, gap = {sep['gap']:.6e} "
                          f"= {sep['gap'] / sep['e2']:.1e} x e2")
                    print(f"      => the pool really is too small at H={H}; `u` is the "
                          f"Farkas direction R2a's augmentation loop consumes")
                else:
                    print("      and no separating direction certified either "
                          "(0 is on the boundary within the enclosure)")
                rec[f"{nm}:{H}"] = dict(m=m, eps=eps, source=os.path.basename(path),
                                        alpha=nm, certified=False, separation=sep,
                                        m7_upper=row.get('m7_upper'),
                                        m7_lower=row.get('m7_lower'),
                                        upper_here=float(row['upper']))
                print()
                continue
            sig_data = sigma_min_lower(np.vstack([Vm, np.ones((1, m))]))
            best = None
            curve = []
            for c in (1.0, 0.5, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8):
                t0 = tmax * c
                lm = entropy_lp(Vm, ent, t0) if c < 1.0 else lam
                if lm is None:
                    continue
                lm = refine(Vm, lm)
                cert = certify(Vm, eps, H, lm, 10 ** 14, ent, sig_data)
                curve.append((c, cert))
                if cert['delta'] > 0 and (best is None or
                                          cert['h_lower'] > best[1]['h_lower']):
                    best = (c, cert)
            c0 = curve[0][1]
            print(f"H={H:<3} pool {m:4d}   eps {eps:.3e}   e2 {c0['e2']:.3e}")
            print(f"      maximin weights: t {c0['t']:.6e}   sigma_min(W) >= "
                  f"{c0['sigma']:.6e}   |r|_2 <= {c0['r2']:.3e}")
            print(f"      DELTA = {c0['delta']:.6e}   =  {c0['ratio']:.2e} x e2      "
                  f"=> K_{H} != empty" if c0['delta'] > 0 else
                  f"      DELTA = {c0['delta']:.6e}   NOT CERTIFIED")
            print(f"      (Gram enclosure radius {c0['gram_rad']:.1e}, "
                  f"lam_min(G) float {c0['lam_min_float']:.6e}, D = 1e14)")
            print("      entropy trade-off   t/t_max :  t          delta        "
                  "h(mu) >=")
            for c, cert in curve:
                flag = "" if cert['delta'] > 0 else "   (not certified)"
                print(f"        {c:<8.0e}          {cert['t']:.3e}  "
                      f"{cert['delta']:+.3e}  {cert['h_lower']:.9f}{flag}")
            m7u, m7l = row.get('m7_upper'), row.get('m7_lower')
            if best:
                hL = best[1]['h_lower']
                # the crossing test must use the full-precision optimiser value
                # recomputed in this run, not M7's table entry rounded to 6 decimals
                up_here = float(row['upper'])
                print(f"      CERTIFIED: E_{H}({nm}) >= {hL:.9f}"
                      f"   [this run's optimiser upper {up_here:.9f}"
                      + (f", M7 sec 4: {m7u:.6f}/{m7l:.6f}" if m7l else
                         (f", M7 sec 4: {m7u:.6f}/-- (pool too small)" if m7u else ""))
                      + ("  <- LOWER EXCEEDS UPPER by %.1e" % (hL - up_here)
                         if hL > up_here else "") + "]")
                print(f"      => H_flat({nm}) > {H}"
                      f"   and, since {hL:.6f} > h_min = {hmin:.6f},"
                      f"  H_ent({nm}) > {H}")
            rec[f"{nm}:{H}"] = dict(m=m, eps=eps, source=os.path.basename(path),
                               alpha=nm,
                               maximin=c0, curve=[(c, k) for c, k in curve],
                               best_c=(best[0] if best else None),
                               upper_here=float(row['upper']),
                               m7_upper=m7u, m7_lower=m7l)
            print()
    with open(f'{BB}/r1b_certify.json', 'w') as f:
        json.dump(rec, f, indent=1)
    print(f"# wrote {BB}/r1b_certify.json")
    return rec


def main():
    if '--checks' in sys.argv or '--all' in sys.argv or len(sys.argv) == 1:
        selfchecks()
    if '--checks' in sys.argv:
        return 0 if _bad == 0 else 1
    # the three ladders of the recorded run; `r1a_pool.json` is deliberately not here --
    # its 1+sqrt2 rows are a subset of `r1b_pool64.json`'s and would collide key for key
    paths = [p for p in (f'{BB}/r1b_pool64.json', f'{BB}/r1b_pool_golden2.json',
                         f'{BB}/r1b_pool_root13.json') if os.path.exists(p)]
    if len(sys.argv) > 1:
        paths = [q if '/' in q else f'{BB}/{q}' for q in sys.argv[1:] if not q.startswith('-')] or paths
    run(paths)
    return 0 if _bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
