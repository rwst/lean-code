#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4: certifying a trigonometric potential by interval arithmetic, not by a
Lipschitz slack.

M3 bounded the window truncation by a single additive constant,
`delta = 2 pi (sum_h h |a_h|) * eps`, i.e. by the *global* Lipschitz constant of g
times eps.  That is the crudest possible enclosure and it is what stops the criterion
from firing at higher H: delta grows like H^2 |a| while the gain in P is slow.

The correct object -- and the one that also covers the discontinuous partition
potentials of `m4_step.py`, which have no Lipschitz constant at all -- is the *word-wise*
enclosure.  For every window word u the true value of F lies in [F~_u - eps, F~_u + eps],
so the edge weight need only dominate

    sup_{|s| <= eps} g(F~_u + s)  <=  g(F~_u) + eps |g'(F~_u)| + eps^2 M2 / 2 ,
    M2 := max |g''| = (2 pi)^2 sum_h h^2 |a_h| ,

which is a *pointwise* penalty carried by |g'(F~_u)| where the Gibbs measure actually
sits, instead of a uniform one carried by max |g'|.  The resulting log spectral radius
is already a rigorous upper bound for the pressure: there is no delta term to add.

Certification and search are separated, as M3's second pass taught: the search
minimises the cheap surrogate P~ + 2 pi (sum h |a_h|) eps_target (which has an exact
gradient and keeps the multipliers small -- the property that makes any certificate
survive a deeper window), and the winner is then *certified* with the sharp enclosure
above, at whatever window is affordable.
"""
import numpy as np
from scipy.optimize import minimize


def _trig(F, modes, a):
    """g(F) and g'(F) for g = Re sum_h a_h e(hF), evaluated word-wise."""
    ph = 2 * np.pi * F
    g = np.zeros_like(F)
    gp = np.zeros_like(F)
    for i, h in enumerate(modes):
        c, s = np.cos(h * ph), np.sin(h * ph)
        g += a[i].real * c - a[i].imag * s
        gp += 2 * np.pi * h * (-a[i].real * s - a[i].imag * c)
    return g, gp


def enclose(W, a, eps=None):
    """Word-wise upper enclosure of the potential over the window's uncertainty."""
    eps = W.err if eps is None else eps
    modes = W.modes
    g, gp = _trig(W.F, modes, a)
    M2 = (2 * np.pi) ** 2 * float(np.sum(modes ** 2 * np.abs(a)))
    return g + eps * np.abs(gp) + 0.5 * eps ** 2 * M2


def spec_ub(W, lw, iters=600, tol=1e-14):
    """Collatz-Wielandt upper bound for the operator with log-weights `lw`."""
    m = lw.max()
    w = np.exp(lw - m)
    w0, w1 = w[W.word[0]], w[W.word[1]]
    t0, t1 = W.tgt
    r = np.ones(1 << W.L)
    for it in range(iters):
        rn = w0 * r[t0] + w1 * r[t1]
        top = rn.max()
        if not np.isfinite(top) or top <= 0:
            return float('inf')
        rn /= top
        done = it > 8 and np.max(np.abs(rn - r)) < tol
        r = rn
        if done:
            break
    if r.min() <= 0:
        return float('inf')
    return float(np.log(((w0 * r[t0] + w1 * r[t1]) / r).max()) + m)


def certify(W, a, eps=None):
    """Rigorous upper bound on Lambda(g o F) at this window.  No delta to add."""
    return spec_ub(W, enclose(W, a, eps))


def search(W, eps_target, x0=None, maxiter=400, cap=8.0, eta=1e-6,
           iters=250, tol=1e-11):
    """Minimise the surrogate P~(a) + 2 pi (sum_h h |a_h|) eps_target.

    Optimising the *certifiable* quantity rather than the pressure is what keeps the
    multipliers small enough for the certificate to survive the deeper window; the
    surrogate is used only for the search, never for the claim.
    """
    K = len(W.modes)
    hh = W.modes.astype(float)

    def f(x):
        a = x[:K] + 1j * x[K:]
        P, gr = W.pressure(a, iters=iters, tol=tol)
        if not np.isfinite(P):
            return 1e6, np.zeros(2 * K)
        mag = np.sqrt(x[:K] ** 2 + x[K:] ** 2 + eta ** 2)
        pen = 2 * np.pi * eps_target * float(np.sum(hh * mag))
        dpen = 2 * np.pi * eps_target * hh / mag
        return P + pen, np.concatenate([gr[0].real + dpen * x[:K],
                                        -gr[0].imag + dpen * x[K:]])

    x0 = np.zeros(2 * K) if x0 is None else np.asarray(x0, dtype=float)
    r = minimize(f, x0, jac=True, method='L-BFGS-B', bounds=[(-cap, cap)] * (2 * K),
                 options=dict(maxiter=maxiter, ftol=1e-15, gtol=1e-12))
    a = r.x[:K] + 1j * r.x[K:]
    P, _ = W.pressure(a, want_grad=False)
    return float(P), r.x, float(2 * np.pi * np.sum(W.modes * np.abs(a)) * eps_target)


def best_window(al, L):
    """The split `N + M = L` that minimises the truncation error.

    M3 always used `N = M`.  That is never optimal: the future costs `alpha^-M` and the
    past costs `C_alpha rho^(N+1)/(1-rho)`, and those two decay at different rates, so the
    balanced split has `M log alpha` about `(N+1) log(1/rho)`.  At the frontier alpha
    `X^3-4X^2-3X-1` the square window `N = M = 12` (2^25 words) has `eps = 2.2e-4` while
    the balanced `N = 13, M = 7` (2^21 words, sixteen times cheaper) has `eps = 1.2e-4`.
    """
    a = float(al.alpha)
    rho = float(al.rho)
    Ca = float(sum(abs(complex(z) - 1) for z in al.conj))
    cand = [(a ** -M + Ca * rho ** (L - M + 1) / (1 - rho), L - M, M)
            for M in range(1, L)]
    e, N, M = min(cand)
    return N, M, e


def pad(x, Hp, Hn):
    """Zero-pad a multiplier vector from Hp modes to Hn (the warm-start ladder)."""
    if x is None:
        return None
    z = np.zeros(Hn - Hp)
    return np.concatenate([x[:Hp], z, x[Hp:], z])
