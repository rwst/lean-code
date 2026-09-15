#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7 of plans/plan-1061.html -- the exact price of a Fourier certificate.

M3 Thm 12 certifies 10.61 at a Pisot unit alpha from a trigonometric potential with
P(psi_a) < h_min(alpha), and M3/M4 search for one by minimising the pressure.  The
quantity that search computes is

    E_H(alpha) := inf_{a in C^H} P(psi_a)
                = max { h(mu) : mu shift-invariant, Phi_h(mu) = 0 for 1 <= h <= H }

(note-1061-M7.html Theorem 1, by Sion's minimax theorem: the two sides are the pressure
and the constrained-entropy face of the same saddle).  Every run of the optimiser is
therefore an *upper* bound for E_H, and a failure to certify proves nothing.

This module supplies the missing side.  Any finite family of invariant measures
nu_1..nu_m gives, by linear programming,

    E_H  >=  max { sum_j lam_j h(nu_j) : lam in simplex, sum_j lam_j Phi_h(nu_j) = 0 },

because the entropy is affine on the invariant simplex and the mixture is invariant.
A lower bound above h_min(alpha) is a *theorem* that no certificate of degree <= H
exists at that alpha.

The family used is memory-L Markov measures, for which Phi_h is exact (M5 Thm 13: the
past and the future are conditionally independent given the L-block at the origin, so
Phi_h is a pair of infinite products of sparse block matrices), and the natural seeds
are the Gibbs measures of the window transfer operator -- the very measures the M3/M4
optimiser walks through.
"""
import numpy as np
from scipy.optimize import linprog
from m0_engine import Alpha


class BlockChain:
    """A memory-L Markov measure on {0,1}^Z, with exact Fourier coefficients of F_*mu.

    Block b = (omega_{-L+1},...,omega_0), bit i of b being omega_{-i} (bit 0 = newest);
    q[b] = P(omega_1 = 1 | b).  Same convention as m5_memory.Memory, but the transfer
    matrices are applied as sparse gather-scatter, so L = 16 (65536 states) is routine.
    """

    def __init__(self, al, L, hmax=64, tol=1e-15):
        a, rho = float(al.alpha), float(al.rho)
        Ca = float(sum(abs(complex(z) - 1.0) for z in al.conj)) or 1.0
        self.al, self.L, self.n = al, L, 1 << L
        self.mask = self.n - 1
        self.J = int(np.log(max(hmax, 1) * (a - 1) / tol) / np.log(a)) + 3
        self.M = int(np.log(max(hmax, 1) * Ca / (tol * (1 - rho))) / np.log(1 / rho)) + 3 + L
        self.x = np.array([(a - 1) * a ** (-j) for j in range(1, self.J + 1)])
        self.c = np.array(al.c_m(self.M + 1))
        u = np.arange(self.n, dtype=np.int64)
        self.fwd = np.stack([((u << 1) & self.mask), ((u << 1) | 1) & self.mask], axis=1)
        self.bwd = np.stack([(u >> 1), (u >> 1) | (1 << (L - 1))], axis=1)
        self.emit_f = (u & 1).astype(float)                 # bit added by a forward step
        self.emit_b = ((u >> (L - 1)) & 1).astype(float)    # bit added by a backward step
        self.head = np.zeros(self.n)            # sum_{i<L} c_i * omega_{-i}
        for i in range(L):
            self.head += self.c[i] * ((u >> i) & 1)

    # -- the chain ---------------------------------------------------------------
    def stationary(self, q, iters=2000, tol=1e-15):
        """L-block distribution of the chain.

        For small state spaces the stationary vector is obtained by one dense linear
        solve (exact, and about a hundred times faster than iterating); for large ones
        by power iteration on gathers -- the preimages of b under the forward map are
        bwd[b,0], bwd[b,1] and the transition into b emits the bit b & 1, so a step is
        a pure gather.
        """
        b0, b1 = self.bwd[:, 0], self.bwd[:, 1]
        s = (np.arange(self.n) & 1)
        c0 = np.where(s == 1, q[b0], 1.0 - q[b0])
        c1 = np.where(s == 1, q[b1], 1.0 - q[b1])
        if self.n <= 4096:
            A = np.zeros((self.n, self.n))
            A[np.arange(self.n), b0] += c0
            A[np.arange(self.n), b1] += c1          # A[b, b'] = P(b' -> b)
            A -= np.eye(self.n)
            A[-1, :] = 1.0
            rhs = np.zeros(self.n)
            rhs[-1] = 1.0
            try:
                pi = np.linalg.solve(A, rhs)
                if np.all(np.isfinite(pi)) and pi.min() > -1e-12:
                    return np.maximum(pi, 0.0) / max(pi.sum(), 1e-300)
            except np.linalg.LinAlgError:
                pass
        pi = np.full(self.n, 1.0 / self.n)
        for _ in range(iters):
            nx = pi[b0] * c0 + pi[b1] * c1
            nx /= nx.sum()
            if np.max(np.abs(nx - pi)) < tol:
                pi = nx
                break
            pi = nx
        return pi

    def entropy(self, q, pi=None):
        pi = self.stationary(q) if pi is None else pi
        p = np.clip(q, 1e-300, 1 - 1e-300)
        return float(-np.sum(pi * (p * np.log(p) + (1 - p) * np.log(1 - p))))

    # -- Fourier coefficients ----------------------------------------------------
    def phis(self, q, hs, pi=None):
        """Phi_h(mu_q) for h in hs, exact up to the geometric tails of the two ladders."""
        pi = self.stationary(q) if pi is None else pi
        hs = np.asarray(hs, dtype=float)[:, None]
        f0, f1 = self.fwd[:, 0], self.fwd[:, 1]
        b0, b1 = self.bwd[:, 0], self.bwd[:, 1]
        q0, q1 = 1.0 - q, q
        # backward transition weights: Ts[b, bwd[b,r]] = pi[b''] P(b''->b) / pi[b]
        s = (np.arange(self.n) & 1)
        w0 = np.where(s == 1, q[b0], 1.0 - q[b0]) * pi[b0]
        w1 = np.where(s == 1, q[b1], 1.0 - q[b1]) * pi[b1]
        piinv = np.where(pi > 0, 1.0 / np.maximum(pi, 1e-300), 0.0)
        w0, w1 = w0 * piinv, w1 * piinv
        V = np.ones((len(hs), self.n), dtype=complex)
        for j in range(self.J, 0, -1):
            Z = V * np.exp(2j * np.pi * hs * self.x[j - 1] * self.emit_f[None, :])
            V = q0[None, :] * Z[:, f0] + q1[None, :] * Z[:, f1]
        U = np.ones((len(hs), self.n), dtype=complex)
        for m in range(self.M, self.L - 1, -1):
            Z = U * np.exp(-2j * np.pi * hs * self.c[m] * self.emit_b[None, :])
            U = w0[None, :] * Z[:, b0] + w1[None, :] * Z[:, b1]
        sh = np.exp(-2j * np.pi * hs * self.head[None, :])
        return (pi[None, :] * sh * U * V).sum(axis=1)

    # -- seeds -------------------------------------------------------------------
    def from_window(self, W, a, iters=600, tol=1e-14):
        """Conditional probabilities of the Gibbs measure of W's transfer operator.

        W's state is the word (omega_{-N},...,omega_{M-1}) with bit i = omega_{i-N}; the
        block convention here is the bit reversal of that.  Requires W.L == self.L.
        """
        lw = W.weights(a)
        mx = lw.max()
        w = np.exp(lw - mx)
        w0, w1 = w[W.word[0]], w[W.word[1]]
        t0, t1 = W.tgt
        r = np.ones(1 << W.L)
        for _ in range(iters):
            rn = w0 * r[t0] + w1 * r[t1]
            rn /= np.linalg.norm(rn)
            if np.max(np.abs(rn - r)) < tol:
                r = rn
                break
            r = rn
        num = w1 * r[t1]
        qw = num / (w0 * r[t0] + num)
        return qw[self._rev(W.L)]

    def _rev(self, L):
        u = np.arange(1 << L, dtype=np.int64)
        v = np.zeros_like(u)
        for i in range(L):
            v |= ((u >> i) & 1) << (L - 1 - i)
        return v


def lp_lower(ent, phi, H, tol=1e-12):
    """max sum lam_j h_j over mixtures with all Phi_h, h <= H, vanishing.

    `ent` is (m,), `phi` is (m, Hmax) complex with column h-1 holding Phi_h.
    Returns (value, lam) or (None, None) if 0 is not in the hull of the pool.
    """
    A = np.vstack([np.ones((1, len(ent))),
                   phi[:, :H].real.T, phi[:, :H].imag.T])
    b = np.zeros(A.shape[0])
    b[0] = 1.0
    r = linprog(-np.asarray(ent), A_eq=A, b_eq=b, bounds=(0, None), method='highs')
    if not r.success:
        return None, None
    lam = r.x
    res = float(np.max(np.abs(A @ lam - b)))
    if res > 1e-9:
        return None, None
    return float(np.dot(ent, lam)), lam


# ---------------------------------------------------------------------------
# WP9 of plan_BB61_improve_m3_entropy.html -- the steered pool.
#
# Four rows of note-1061-M7.html sec 4 read "pool too small": `lp_lower` returned
# infeasible because 0 was not in the convex hull of the pool's Phi-vectors.  That is a
# statement about the pool, and it is the only thing between a failed search and a no-go
# theorem.  The fix is not a bigger pool but a steered one.
#
# Two steering rules, one for each regime, and both read off the same LP:
#
#   infeasible.  0 not in conv{Phi_j} means, by Farkas, that some c separates: 
#   <c, g_j> >= gamma > 0 for every pool member.  That c is a multiplier direction, and
#   the Gibbs measure of the window operator at `x* - t c` is tilted towards the side of
#   the hyperplane the pool is missing.  `farkas_direction` produces it.
#
#   feasible.  The LP dual (y_0, y) prices the missing column exactly: the constraint it
#   enforces is `h(nu_j) + <y, g(nu_j)> <= value` for every j, so the column to add is
#   the maximiser of `h(mu) + int psi_{a(y)} dmu` over invariant mu -- which is the
#   definition of `P(psi_{a(y)})`, and whose maximiser is again the Gibbs measure of the
#   window operator, now at `a(y)`.
#
# The second rule closes the bracket.  For any invariant mu that is flat to degree H,
# `h(mu) = h(mu) + <y, g(mu)> <= P(psi_{a(y)})`, so `E_H <= P(psi_{a(y)})` whatever y is;
# and `E_H >= value` because the LP is a restriction.  When the two meet, E_H is
# determined -- and the upper side is produced by the LP itself, not by a second search.
# This is the same saddle as M7 Thm 1, walked from the other side: WP6 descends to E_H
# in the multipliers, WP9 climbs to it in the measures.
# ---------------------------------------------------------------------------

def real_pairing(phi, H):
    """Real coordinates `g(mu)` of the Fourier data, with `<x, g(mu)> = int psi_a dmu`.

    `psi_a = Re sum_h a_h e(hF)` gives `int psi_a dmu = sum_h (x_r[h] Re Phi_h -
    x_i[h] Im Phi_h)`, so the pairing vector is `(Re Phi, -Im Phi)` -- the same
    convention as `m3_entropy.minimize_pressure`'s gradient, which is what makes the LP
    dual directly usable as a multiplier.
    """
    p = np.asarray(phi)[:, :H]
    return np.concatenate([p.real, -p.imag], axis=1)


def lp_bound(ent, phi, H, tol=1e-9, penalty=1e6):
    """`lp_lower` with its dual and its residual: (value, lam, y, resid, atoms).

    The flatness constraints are carried with an l^1-penalised slack rather than as a
    hard equality.  That is not cosmetic: exactly where WP9 is needed the pool's hull
    has 0 on its *boundary*, and a hard equality then makes the solver report
    infeasibility while the separating direction has already collapsed to zero -- the
    loop stalls with nothing to steer by.  With the slack the LP always solves, `resid`
    says how far from flat the best mixture is, and feasibility is the honest test
    `resid <= tol`.  A `value` reported with `resid > tol` is NOT a bound on `E_H`: the
    mixture it comes from is not flat, and callers must gate on `resid`.

    `y` is the pricing direction in `m3_entropy.minimize_pressure`'s real coordinates:
    the column the LP wants next is the Gibbs measure at `a(y) = y[:H] + i y[H:]`, and
    `P(psi_{a(y)})` is an upper bound for `E_H` whatever `y` is.
    """
    G = real_pairing(phi, H)
    m, n = G.shape
    A = np.zeros((1 + n, m + 2 * n))
    A[0, :m] = 1.0
    A[1:, :m] = G.T
    A[1:, m:m + n] = -np.eye(n)                      # slack s+ ...
    A[1:, m + n:] = np.eye(n)                        # ... and s-
    b = np.zeros(1 + n)
    b[0] = 1.0
    c = np.concatenate([-np.asarray(ent), np.full(2 * n, penalty)])
    r = linprog(c, A_eq=A, b_eq=b, bounds=(0, None), method='highs')
    if not r.success:
        return None, None, None, None, 0
    lam = r.x[:m]
    resid = float(np.sum(r.x[m:]))
    u = np.asarray(r.eqlin.marginals)
    return (float(np.dot(ent, lam)), lam, u[1:].copy(), resid,
            int(np.sum(lam > 1e-12)))


def farkas_direction(phi, H, cap=1.0, tol=1e-12):
    """A separating multiplier direction when 0 is outside the pool's hull.

    Solves `max gamma s.t. <c, g_j> >= gamma for all j, |c|_inf <= cap`.  A positive
    optimum is a Farkas certificate that the LP of `lp_bound` is infeasible *for this
    pool*, and `c` says in which direction the pool is one-sided.  Returns
    `(c, gamma)`, or `(None, 0.0)` when 0 is already in the hull (or the LP fails).
    """
    G = real_pairing(phi, H)
    m, n = G.shape
    A_ub = np.hstack([-G, np.ones((m, 1))])             # -<c,g_j> + gamma <= 0
    obj = np.zeros(n + 1)
    obj[n] = -1.0
    r = linprog(obj, A_ub=A_ub, b_ub=np.zeros(m),
                bounds=[(-cap, cap)] * n + [(None, None)], method='highs')
    if not r.success:
        return None, 0.0
    gamma = float(-r.fun)
    return (r.x[:n].copy(), gamma) if gamma > tol else (None, gamma)


def gibbs_columns(W, bc, H, xs):
    """(entropies, Phi-vectors) of the window Gibbs measures at the multipliers `xs`.

    Each column is a genuine memory-L Markov measure with `Phi_h` computed exactly by
    the two ladders of `phis`, so the LP bound built from them is rigorous (M7 Thm 5);
    columns whose weights underflowed are dropped rather than reported.
    """
    hs = list(range(1, H + 1))
    ent, phi = [], []
    for x in xs:
        x = np.asarray(x, dtype=float)
        a = x[:H] + 1j * x[H:]
        with np.errstate(divide='ignore', invalid='ignore'):
            q = bc.from_window(W, a)                     # a deep tilt drives q to 0/1,
            pi = bc.stationary(q)                        # and `entropy` then logs a zero
            e = bc.entropy(q, pi)                        # `pi` is shared: `stationary`
            p = np.asarray(bc.phis(q, hs, pi))           # is deterministic, so passing
                                                         # it changes nothing but the
                                                         # cost -- one dense 2^L solve
                                                         # per column instead of two
        if np.isfinite(e) and np.isfinite(p).all():
            ent.append(float(e))
            phi.append(p)
    return np.array(ent), (np.array(phi) if phi else np.zeros((0, H), complex))


def cutting_plane_lower(W, bc, H, xstar=None, ent=None, phi=None, rounds=24,
                        steps=(0.05, 0.25, 1.0, 4.0), tol=1e-6, cap=60.0,
                        feas_tol=1e-9, max_scale=64.0, verbose=False):
    """WP9: bracket `E_H` from below by a steered pool, and from above by its own dual.

    Requires `W.L == bc.L` and `bc.hmax >= H`; `W` must already carry modes `1..H`.
    Starts from `xstar` alone (the M3/M4 optimum, if one is at hand) and lets the LP
    choose every further column, alternating the two rules above: the Farkas separator
    while the pool's hull misses 0, the dual pricing direction once it does not.

    Returns a dict.  `lb` is the rigorous lower bound (None while the pool is not flat
    to `feas_tol`); `ub_raw` is the dual's pressure on the truncated operator and `ub`
    that plus the window's slack, so `ub` is the rigorous upper bound.  `closed` means
    the rigorous bracket `ub - lb` is within `tol` -- `E_H` determined; `converged`
    means only `ub_raw - lb` is, i.e. the column generation has exhausted itself and
    anything further has to come from a deeper window.  The pool is returned too, so a
    caller can resume with more rounds.
    """
    from m3_entropy import delta_bound
    xstar = np.zeros(2 * H) if xstar is None else np.asarray(xstar, dtype=float)
    if ent is None or phi is None or len(ent) == 0:
        ent, phi = gibbs_columns(W, bc, H, [xstar])
    lb, ub, ubr, lam, atoms = None, np.inf, np.inf, None, 0
    scale, gprev, rnd, stalled = 1.0, np.inf, 0, False
    for rnd in range(1, rounds + 1):
        val, lam, y, resid, atoms = lp_bound(ent, phi, H)
        if val is None:
            stalled = True
            break
        a = np.clip(y, -cap, cap)
        av = a[:H] + 1j * a[H:]
        if resid <= feas_tol:                            # the pool is flat: price it
            lb = val if lb is None else max(lb, val)
            Pw, _ = W.pressure(av, want_grad=False)
            ubr = min(ubr, float(Pw))
            ub = min(ub, float(Pw) + delta_bound(W, av))
            if verbose:
                print('   round %-2d lb = %.9f  ub = %.9f (raw %.9f)  gap %.2e  '
                      'atoms %d/%d' % (rnd, lb, ub, ubr, ubr - lb, atoms, len(ent)))
            if ub - lb <= tol or ubr - lb <= tol:
                break
            new = [a]
        else:                                            # 0 outside the hull: separate
            c, gamma = farkas_direction(phi, H)
            if gamma >= 0.1 * gprev:                     # the separator is not moving:
                scale = min(scale * 2.0, max_scale)      # push further out, but only
            gprev = gamma if gamma > 0 else gprev        # so far -- see below
            d = c if c is not None else y                # fall back on the penalised
            new = [np.clip(xstar - scale * t * d, -cap, cap) for t in steps]
            if verbose:
                print('   round %-2d not flat (resid %.2e, gamma %.2e), +%d steered '
                      'columns at scale %g -> pool %d'
                      % (rnd, resid, gamma, len(new), scale, len(ent) + len(new)))
        e2, p2 = gibbs_columns(W, bc, H, new)
        if len(e2) == 0:
            # Every tilt underflowed the window weights.  That is a step-size failure,
            # not an exhausted generator: back off and try again rather than reporting
            # a stall, which would read as "no lower bound exists".
            if resid > feas_tol and scale > 1e-2:
                scale *= 0.25
                gprev = np.inf
                if verbose:
                    print('   round %-2d all tilts underflowed: scale -> %g'
                          % (rnd, scale))
                continue
            stalled = True
            break
        if resid <= feas_tol:                            # nothing violated: this
            gain = float(e2[0] + np.dot(y, real_pairing(p2, H)[0]))
            if gain <= lb + 1e-12:                       # generator is exhausted
                break
        ent = np.concatenate([ent, e2])
        phi = np.concatenate([phi, p2])
    fin = lb is not None
    return dict(lb=lb, ub=(float(ub) if np.isfinite(ub) else None),
                ub_raw=(float(ubr) if np.isfinite(ubr) else None),
                gap=(float(ub - lb) if (fin and np.isfinite(ub)) else None),
                gap_raw=(float(ubr - lb) if (fin and np.isfinite(ubr)) else None),
                atoms=atoms, pool=int(len(ent)), rounds=rnd, feasible=fin,
                stalled=bool(stalled),
                closed=bool(fin and np.isfinite(ub) and ub - lb <= tol),
                converged=bool(fin and np.isfinite(ubr) and ubr - lb <= tol),
                lam=(None if lam is None else np.asarray(lam).tolist()),
                ent=ent, phi=phi)
