#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4 of plans/plan-1061.html -- the partition-potential machine.

M3's Theorem 12 certifies 10.61 at alpha from a *trigonometric* potential
psi_a = Re sum_{h<=H} a_h e(hF) with P(psi_a) < h_min(alpha).  Its proof, however,
never uses continuity of the potential: if F_*mu = Leb then int g(F) dmu = int g dLeb
for every bounded Borel g, and the easy half of the variational principle
(Misiurewicz's Jensen argument over the cylinder partition) also holds for bounded
measurable potentials.  So the certificate class is *all* bounded g of Leb-mean zero,
and the natural finite subclass is not a Fourier truncation but a **partition**:

    g = sum_j (log v_j) 1_{I_j},   I_j = [j/B, (j+1)/B),   prod_j v_j = 1,

for which the window truncation is handled by interval arithmetic rather than by a
Lipschitz constant (a step function has none).  Concretely, if the window value is
F~ and |F - F~| <= eps, the edge weight is the *maximum* of v over the one or two
cells that [F~-eps, F~+eps] meets: an exact upper bound with no delta term at all.

Writing E(B) = max{ h(mu) : (F_*mu)(I_j) = 1/B for all j }, the criterion fires at B
iff E(B) < h_min(alpha), exactly parallel to M3's E(H).  Two facts make this the right
basis (note-1061-M4.html sec 3):

  * with x_j = log v_j, log lambda(x + c) = log lambda(x) + c, so the constrained
    problem is the *unconstrained* minimisation of G(x) = log lambda(x) - mean(x),
    and grad G = (Gibbs occupation of cell j) - 1/B: the optimiser is looking for the
    maximal-entropy measure whose F-pushforward equidistributes over the partition;
  * the first-order gain at x = 0 is |F_*(Bernoulli) - Leb| measured in the dual of
    the potential class -- total variation for a partition, l^2 of Fourier coefficients
    for a trigonometric truncation.  F_*mu is *far* from Leb in total variation and
    *close* in Fourier (that is M0's plateau, i.e. non-Rajchman).  The Fourier price
    of M3 sec 9.2 is therefore an artefact of the basis.

The B = "one cell inside a gap of X(alpha)" case reproduces the X8 gap certificate, so
this machine also contains M4's original LP/raster lane.
"""
import numpy as np
from scipy.optimize import minimize
from m3_entropy import Window, h_min


class Cells:
    """A window (from m3_entropy) refined by the B equal cells of the circle.

    Precomputes, for every word of the window alphabet, the one or two cell indices
    that the interval [F~ - eps, F~ + eps] can meet.  `lo`/`hi` are those indices;
    the edge weight of a word is max(v[lo], v[hi]), which is a rigorous upper bound
    for sup over the cylinder of the true v(F).
    """

    def __init__(self, W, B):
        self.W, self.B = W, B
        f = np.mod(W.F, 1.0)
        e = W.err
        if 2 * e * B >= 1.0:
            raise ValueError('window too shallow for B=%d: 2*eps*B = %.3f >= 1'
                             % (B, 2 * e * B))
        self.lo = np.mod(np.floor((f - e) * B).astype(np.int64), B)
        self.hi = np.mod(np.floor((f + e) * B).astype(np.int64), B)
        self.split = float(np.mean(self.lo != self.hi))   # fraction of ambiguous words

    # ---- weights ---------------------------------------------------------
    def logw(self, x):
        """log of the edge weight of every word: max(x[lo], x[hi])."""
        return np.maximum(x[self.lo], x[self.hi])

    def argcell(self, x):
        """which cell attains the max (the one the gradient charges)."""
        return np.where(x[self.lo] >= x[self.hi], self.lo, self.hi)

    # ---- spectrum --------------------------------------------------------
    def logspec(self, x, iters=600, tol=1e-14, want_grad=True):
        """(log lambda, occupation) for the partition potential with log v = x."""
        W = self.W
        lw = self.logw(x)
        m = lw.max()
        w = np.exp(lw - m)
        w0, w1 = w[W.word[0]], w[W.word[1]]
        t0, t1 = W.tgt
        r = np.ones(1 << W.L)
        lam = 1.0
        for it in range(iters):
            rn = w0 * r[t0] + w1 * r[t1]
            lam = rn.sum() / r.sum()
            rn /= np.linalg.norm(rn)
            done = it > 8 and np.max(np.abs(rn - r)) < tol
            r = rn
            if done:
                break
        P = float(np.log(lam) + m)
        if not want_grad:
            return P, None
        q, s = W.qidx, W.sidx
        ws0 = np.where(s == 0, w0[2 * q], w1[2 * q])
        ws1 = np.where(s == 0, w0[2 * q + 1], w1[2 * q + 1])
        l = np.ones(1 << W.L)
        for it in range(iters):
            ln = ws0 * l[2 * q] + ws1 * l[2 * q + 1]
            ln /= np.linalg.norm(ln)
            done = it > 8 and np.max(np.abs(ln - l)) < tol
            l = ln
            if done:
                break
        mu = np.concatenate([l * w0 * r[t0], l * w1 * r[t1]])
        mu /= mu.sum()
        cell = self.argcell(x)
        occ = np.bincount(np.concatenate([cell[W.word[0]], cell[W.word[1]]]),
                          weights=mu, minlength=self.B)
        return P, occ

    def logspec_ub(self, x, iters=600, tol=1e-14):
        """Collatz-Wielandt upper bound: lambda <= max_u (A r)_u / r_u for any r > 0."""
        W = self.W
        lw = self.logw(x)
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


def E(cells, x0=None, maxiter=400, cap=40.0, ub=True):
    """E(B) = min over mean-zero partition potentials of the pressure bound.

    Minimises G(x) = log lambda(x) - mean(x), which is invariant under x -> x + c and
    whose minimum is the constrained one.  Returns (G, x, |grad|, log-lambda-upper).
    """
    B = cells.B

    def f(x):
        P, occ = cells.logspec(x)
        if not np.isfinite(P):
            return 1e6, np.zeros(B)
        return P - x.mean(), occ - 1.0 / B

    x0 = np.zeros(B) if x0 is None else np.asarray(x0, dtype=float)
    r = minimize(f, x0, jac=True, method='L-BFGS-B', bounds=[(-cap, cap)] * B,
                 options=dict(maxiter=maxiter, ftol=1e-14, gtol=1e-11))
    x = r.x - r.x.mean()
    G, occ = cells.logspec(x)
    out = cells.logspec_ub(x) if ub else G
    return float(G), x, float(np.abs(occ - 1.0 / B).max()), float(out)
