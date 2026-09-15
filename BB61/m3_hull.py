#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 -- periodic-orbit Fourier vectors and the convex-hull test.

For a binary word w of period p the bi-infinite periodic point omega has, at time n,
  t_n = (alpha-1) sum_{k=1}^p w[(n+k) mod p] alpha^{-k} / (1 - alpha^{-p}),
  S_n = Re sum_{j>=2} (alpha_j-1) sum_{m=0}^{p-1} w[(n-m) mod p] alpha_j^m/(1-alpha_j^p),
and Phi_h(w) = (1/p) sum_n e(h (t_n - S_n)) is the h-th Fourier coefficient of F_* mu_w.

A trigonometric certificate of degree H exists at alpha iff 0 is NOT in the convex hull
of {(Phi_1,..,Phi_H)(mu) : mu invariant} (note-1061-M3.html Theorem 4).  Periodic
measures are invariant, so *finding* 0 inside the hull of finitely many orbits is a
rigorous no-go: no certificate of degree <= H exists.
"""
import numpy as np
from scipy.optimize import linprog


def _mats(al, p):
    a = float(al.alpha)
    idx = np.arange(p)
    A = np.array([a ** (-k) for k in range(1, p + 1)])
    Mt = ((a - 1.0) / (1.0 - a ** (-p))) * A[(idx[None, :] - idx[:, None] - 1) % p]
    Ms = np.zeros((p, p))
    for z in al.conj:
        zz = complex(z)
        B = np.array([(zz - 1.0) * zz ** m for m in range(p)]) / (1.0 - zz ** p)
        Ms = Ms + np.real(B[(idx[:, None] - idx[None, :]) % p])
    return Mt, Ms


def phi_words(al, W, p, modes):
    """W: (N,p) 0/1 array of words of period p.  Returns (N,len(modes)) complex."""
    Mt, Ms = _mats(al, p)
    Wf = np.asarray(W, dtype=np.float64)
    F = Wf @ Mt.T - Wf @ Ms.T
    hs = np.asarray(modes, dtype=float)
    out = np.empty((Wf.shape[0], len(hs)), dtype=complex)
    step = max(1, 2_000_000 // max(1, p * len(hs)))
    for lo in range(0, Wf.shape[0], step):
        E = np.exp(2j * np.pi * (F[lo:lo + step, :, None] * hs[None, None, :]))
        out[lo:lo + step] = E.mean(axis=1)
    return out


def phi_all(al, p, modes, chunk=1 << 16):
    """All 2^p words of period p."""
    n = np.arange(1 << p, dtype=np.int64)
    outs = []
    for lo in range(0, 1 << p, chunk):
        m = n[lo:lo + chunk]
        outs.append(phi_words(al, ((m[:, None] >> np.arange(p)[None, :]) & 1), p, modes))
    return np.concatenate(outs, axis=0)


def pool(al, modes, periods=(10, 12, 14, 16), per_period=None, seed=0):
    rng = np.random.default_rng(seed)
    Zs = []
    for p in periods:
        if per_period is None or (1 << p) <= per_period:
            Zs.append(phi_all(al, p, modes))
        else:
            m = rng.integers(0, 1 << p, per_period, dtype=np.int64)
            Zs.append(phi_words(al, ((m[:, None] >> np.arange(p)[None, :]) & 1), p, modes))
    return np.concatenate(Zs, axis=0)


def separate(Z, tol=1e-9, maxit=4000):
    """Cutting plane.  Returns (inside, margin, u, active set).
    inside=True  <=>  no separating direction  <=>  no certificate on these modes."""
    P = np.concatenate([Z.real, Z.imag], axis=1).astype(np.float64)
    N, D = P.shape
    act = [int(np.argmin(P[:, 0])), int(np.argmax(P[:, 0])), 0]
    u = np.zeros(D)
    c = 0.0
    for it in range(maxit):
        A = np.array(sorted(set(act)))
        M = P[A]
        cobj = np.zeros(D + 1)
        cobj[-1] = -1.0
        r = linprog(cobj, A_ub=np.hstack([-M, np.ones((len(A), 1))]), b_ub=np.zeros(len(A)),
                    bounds=[(-1, 1)] * D + [(None, None)], method='highs')
        if not r.success:
            raise RuntimeError('LP failed: ' + r.message)
        u, c = r.x[:D], r.x[-1]
        if c <= tol:
            return True, float(c), u, sorted(set(act))
        v = P @ u
        j = int(np.argmin(v))
        if v[j] >= c - tol:
            return False, float(v.min()), u, sorted(set(act))
        act.append(j)
    return None, float(c), u, sorted(set(act))


def witness(Z, target=None, tol=1e-9):
    """Convex weights lam >= 0, sum 1, with sum_i lam_i Z_i = target (default 0)."""
    P = np.concatenate([Z.real, Z.imag], axis=1).T
    k = P.shape[1]
    b = np.zeros(P.shape[0]) if target is None else np.asarray(target, dtype=float)
    Aeq = np.vstack([P, np.ones((1, k))])
    beq = np.concatenate([b, [1.0]])
    r = linprog(np.zeros(k), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * k, method='highs')
    return (r.x if r.success else None)


def interior_radius(Z, eps):
    """True iff the l^infty ball of radius eps around 0 is inside the hull
    (checked on the 2D coordinate directions, which suffices by convexity)."""
    D = 2 * Z.shape[1]
    for j in range(D):
        for s in (+1, -1):
            t = np.zeros(D)
            t[j] = s * eps
            if witness(Z, t) is None:
                return False
    return True
