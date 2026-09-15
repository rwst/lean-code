#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 of plans/plan-1061.html -- the entropy certificate machine.

Theorem 6 of note-1061-M3.html: for a Pisot *unit* alpha put

    h_min(alpha) = ( 1/log alpha + 1/log(1/rho) )^{-1} .

If some real trigonometric potential  psi_a = Re sum_h a_h e(h F)  has topological
pressure  P(psi_a) < h_min(alpha),  then 10.61 holds at alpha.  At a = 0 this is
P = log 2 and the criterion is exactly Route A.

The pressure is the log spectral radius of the transfer operator of the full 2-shift
with the window potential; the state is a word of length L = N+M over positions
-N..M-1 and an edge appends omega_M.  Truncating F at those depths costs at most
`Window.err`, so P(psi_a) <= P_computed + delta with

    delta = 2 pi (sum_h h |a_h|) * eps ,

which is what makes any single multiplier vector a *rigorous* upper bound on the
constrained entropy.  See note-1061-M3.html sec 7.

Implementation (WP1-WP7 of plan_BB61_improve_m3_entropy.html)
------------------------------------------------------------
The mathematics is unchanged; the cost model is not.  WP1-WP5 remove the
`O(H * 2^L)` inner loops that priced out `H > 64`; WP6-WP7 turn the single solve
into the `E_H` curve the notes actually disagree about:

WP1  The index arrays `word`, `tgt`, `qidx`, `sidx` are slices in disguise.
     `word[0]`/`word[1]` are the two halves of a length-`2^(L+1)` array, and the
     operator step  r'_{2v+j} = w0_{2v+j} r_v + w1_{2v+j} r_{v+2^(L-1)}  is one
     fused expression on `(2^(L-1), 2)` reshapes.  Same arithmetic, same order,
     bitwise-identical output, no gathers and no index arrays.  They survive as
     lazy properties only because `m4_step.py`, `m4_fourier.py` and `m7_price.py`
     still read them.

WP2  The two power iterations are warm-started from the previous call (consecutive
     operators along an L-BFGS trajectory are close), and the stopping rule is the
     Collatz-Wielandt bracket  min_u (Ar)_u/r_u <= lambda <= max_u (Ar)_u/r_u
     rather than an iterate difference: it bounds the quantity the certificate
     actually needs.  Soundness is untouched -- `pressure_ub` returns a valid upper
     bound for *any* strictly positive `r`, whatever the iteration did.

WP3  `psi_a` depends on the state only through `F` and, the modes being integers,
     is 1-periodic in it.  So it is one fixed trigonometric polynomial sampled at
     `2^(L+1)` points of the circle: evaluate it once on a grid of `G` points by
     inverse FFT and gather.  `H` leaves the per-state cost entirely.

WP4  `Phi_h = sum_u mu_u e(h F_u)` is the Fourier transform of a weighted histogram
     of `F`; one forward FFT returns all `H` coefficients at once.  Mass is split
     linearly between the two neighbouring bins, so the coefficient error is
     `O((pi h/G)^2)` rather than `O(pi h/G)`.  This path is gradient-only and is
     kept textually separate from the certificate path.

WP5  The grid of WP3 perturbs the potential by at most `Lip(psi_a)/2G`, and pressure
     is 1-Lipschitz in the sup norm of the potential, so the enclosure absorbs it as

         eps  =  err  +  1/(2G)      (`Window.eps`, and 0 when no grid is used),

     which is the single accounting change.  `delta_bound` reads `Window.eps`, never
     `Window.err`.  M4 Prop. 3 is an enclosure, not a slack: every approximation has
     to be inside it, including this one.

WP6  `a -> P(psi_a)` is convex with exact gradient `Phi_h(mu_a)`, so every local
     minimum is global: no multi-start, and the stopping criterion belongs in the
     objective.  `minimize_pressure` accumulates the cutting planes it evaluates and
     minimises that lower model over the box by LP, which brackets the solve from
     below (`W.last_solve['lb_box']`, `['gap']`).  The `cap` box is audited on every
     run, since a value reported from an active box bounds `inf_box P`, not `E_H`.
     `E_curve` runs the whole H-ladder, each rung warm-started from the last.

WP7  The window is fixed by the multiplier norm `S1 = sum_h h|a_h|` and by nothing
     else -- not by the mode count, and not by the `log h/h_min` resolution rule,
     which is the weaker requirement at every `H <= 10^3`.  `window_eps`,
     `best_split` and `choose_window` do that arithmetic; `E_curve` closes the loop
     by re-windowing each rung from the `S1` the previous rung measured, which is
     M3's operational lesson (a): the window is chosen after the multiplier.
"""
import math
import warnings

import numpy as np
from scipy.optimize import linprog, minimize


def _pow2_at_least(x):
    """Smallest power of two >= x (x >= 1)."""
    return 1 << max(0, int(math.ceil(math.log2(max(float(x), 1.0)) - 1e-12)))


class Window:
    """Transfer operator of the full 2-shift with the potential psi_a(F)."""

    #: below this many modes the direct trigonometric evaluation wins outright
    fft_min_modes = 4
    #: grid sizes are clamped to this (one irfft of this length per call)
    grid_max = 1 << 24
    #: WP2 stopping rule; 'vector' restores the pre-WP2 iterate-difference test,
    #: which is what the G-1 bitwise gate compares against
    stop = 'bracket'

    def __init__(self, al, N, M, warm=True):
        self.N, self.M, self.L = N, M, N + M
        a = float(al.alpha)
        wt = np.zeros(N + M + 1)                        # bit i <-> position i-N
        for j in range(1, M + 1):
            wt[N + j] = (a - 1.0) * a ** (-j)           # future part t
        cm = [float(sum((complex(z) - 1.0) * complex(z) ** m for z in al.conj).real)
              for m in range(N + 1)]
        for m in range(N + 1):
            wt[N - m] -= cm[m]                          # past part -S
        self.wt = wt
        nb = N + M + 1
        F = np.zeros(1)                                 # F[idx] = sum of wt[i] over
        for i in range(nb):                             # the set bits of idx, built by
            F = np.concatenate([F, F + wt[i]])          # doubling: 2^nb doubles, and no
        self.F = F                                      # (2^nb x nb) scratch matrix
        self.err = window_eps(al, N, M)                 # WP7
        self.modes = np.array([1], dtype=np.int64)
        self._word = self._tgt = None                   # WP1: legacy, built on demand
        self._qidx = self._sidx = None                  # gradient-only, built on demand
        self._G = None                                  # WP3: grid, built on demand
        self._G_fixed = False
        self._idx = self._res = None
        self.warm = bool(warm)                          # WP2
        self._r = self._l = self._mu = None

    # ---- legacy index arrays (WP1) ---------------------------------------
    # Nothing in this file uses them any more; m4_step.Cells, m4_fourier.spec_ub
    # and m7_price.Ladder.from_window still do, so they stay reachable -- but they
    # are no longer built for every window that is merely constructed.

    @property
    def word(self):
        if self._word is None:
            u = np.arange(1 << self.L, dtype=np.int64)
            self._word = [u, u | (1 << self.L)]
        return self._word

    @property
    def tgt(self):
        if self._tgt is None:
            u = np.arange(1 << self.L, dtype=np.int64)
            self._tgt = [(u >> 1), (u >> 1) | (1 << (self.L - 1))]
        return self._tgt

    @property
    def qidx(self):
        if self._qidx is None:
            self._qidx = np.arange(1 << self.L, dtype=np.int64) & ((1 << (self.L - 1)) - 1)
        return self._qidx

    @property
    def sidx(self):
        if self._sidx is None:
            self._sidx = np.arange(1 << self.L, dtype=np.int64) >> (self.L - 1)
        return self._sidx

    def set_modes(self, modes):
        self.modes = np.asarray(modes, dtype=np.int64)
        if self._G_fixed:
            if self.modes.size and 2 * int(self.modes.max()) >= self._G:
                raise ValueError('grid %d cannot resolve mode %d'
                                 % (self._G, self.modes.max()))
        elif self._G is not None and self._G != self._grid_size():
            self._G = self._idx = self._res = None      # grid no longer resolves H
        return self

    # ---- the circle grid (WP3/WP4/WP5) -----------------------------------

    def _grid_size(self):
        """A power of two fine enough on two independent counts.

        WP5, the potential: `1/(2G)` an order below the truncation error, so that the
        grid term the enclosure has to charge stays a rounding correction to `err`.

        WP4, the gradient: `(pi h_max/G)^2/2 <= 1e-7`, i.e. `G >= 8192 h_max`.  This is
        the binding one, and it is what fixes the crossover in `grid`: the FFT path is
        never taken at a window so shallow that the grid it would need costs more than
        the mode loop it replaces.  A rule tied to `err` alone would take the FFT path
        at `L = 12` on a grid too coarse to report `Phi_h` -- which is what the machine
        is steered by.
        """
        hmax = int(self.modes.max()) if self.modes.size else 1
        need = max(5.0 / max(self.err, 1e-15), 8192.0 * hmax, 4096.0)
        G = _pow2_at_least(min(need, float(self.grid_max)))
        return max(G, _pow2_at_least(4 * hmax))

    def set_grid(self, G):
        """Override the grid size (a power of two, > 2*max(modes))."""
        G = int(G)
        if G & (G - 1):
            raise ValueError('grid size must be a power of two: %d' % G)
        if self.modes.size and 2 * int(self.modes.max()) >= G:
            raise ValueError('grid %d cannot resolve mode %d' % (G, self.modes.max()))
        self._G, self._G_fixed = G, True
        self._idx = self._res = None
        return self

    @property
    def G(self):
        if self._G is None:
            self._G = self._grid_size()
        return self._G

    @property
    def grid(self):
        """`G` when the FFT path is the cheaper one for the current modes, else None.

        A deterministic function of `(L, modes, G)` alone -- never of what some earlier
        call happened to do -- so that `eps` and `delta_bound` are well defined.
        """
        H = int(self.modes.size)
        if H < self.fft_min_modes:
            return None
        G, nf = self.G, self.F.size
        direct = 2.0 * H * nf                           # 2H transcendental passes
        viafft = nf + 2.0 * G * math.log2(G)            # one irfft + one gather
        return G if direct > viafft else None

    @property
    def eps(self):
        """WP5: the truncation error the enclosure must charge, grid included."""
        G = self.grid
        return self.err + (0.0 if G is None else 0.5 / G)

    def _build_grid(self):
        """Nearest-bin index and signed residual of `G * frac(F)`, in [-1/2, 1/2].

        Built in blocks: the naive expression holds three length-`2^(L+1)` temporaries
        at once, which at `L = 24` is 0.8 GB of peak just to produce a 0.4 GB result.
        """
        G, n = self.G, self.F.size
        idx = np.empty(n, dtype=np.int64)
        res = np.empty(n, dtype=np.float32)
        for s in range(0, n, 1 << 22):
            e = min(s + (1 << 22), n)
            x = np.mod(self.F[s:e], 1.0)
            x *= G
            k = np.rint(x)
            res[s:e] = (x - k).astype(np.float32)
            idx[s:e] = np.mod(k, G).astype(np.int64)
        self._idx, self._res = idx, res

    @property
    def idx(self):
        if self._idx is None:
            self._build_grid()
        return self._idx

    @property
    def res(self):
        if self._res is None:
            self._build_grid()
        return self._res

    # ---- the potential ---------------------------------------------------

    def weights(self, a):
        """psi_a evaluated word-wise: Re sum_h a_h e(h F)."""
        a = np.asarray(a, dtype=complex)
        G = self.grid
        if G is None:
            ph = 2 * np.pi * self.F
            s = np.zeros_like(self.F)
            for i, h in enumerate(self.modes):
                s += a[i].real * np.cos(h * ph) - a[i].imag * np.sin(h * ph)
            return s
        # WP3.  irfft(A, n=G)[k] = (1/G)(A_0 + 2 sum_{m>=1} Re A_m e(mk/G)), so
        # A_h = a_h/2 with A_0 = 0 reproduces psi_a exactly at the grid points.
        A = np.zeros(G // 2 + 1, dtype=complex)
        A[self.modes] = a / 2.0
        A[0] = A[0].real * 2.0                          # irfft does not double the DC bin
        v = np.fft.irfft(A, n=G)
        v *= G
        return v[self.idx]

    def _phis(self, mu):
        """Phi_h(mu_a) = sum_u mu_u e(h F_u), for every mode at once."""
        G = self.grid
        if G is None:
            return np.array([np.sum(mu * np.exp(2j * np.pi * float(h) * self.F))
                             for h in self.modes])
        # WP4.  Deposit each mass linearly into the two bins straddling it -- the
        # `idx + sign(res)` bin is `idx` shifted by one, so a roll does the moving --
        # and read off all H coefficients with one real FFT.  Gradient only.
        idx, res = self.idx, self.res
        hi = np.bincount(idx, weights=mu * np.maximum(res, 0.0), minlength=G)
        lo = np.bincount(idx, weights=mu * np.maximum(-res, 0.0), minlength=G)
        hist = np.bincount(idx, weights=mu, minlength=G)
        hist += np.roll(hi, 1) - hi
        hist += np.roll(lo, -1) - lo
        return np.conj(np.fft.rfft(hist))[self.modes]

    def phis_exact(self, mu):
        """The same, by direct summation: O(H * 2^(L+1)), for reporting."""
        return np.array([np.sum(mu * np.exp(2j * np.pi * float(h) * self.F))
                         for h in self.modes])

    # ---- the spectrum ----------------------------------------------------

    def reset_iterates(self):
        """Forget the warm starts (WP2).  Makes `pressure` a pure function again."""
        self._r = self._l = self._mu = None
        return self

    def _start(self, cached, n):
        if self.warm and cached is not None and cached.shape == (n,):
            if np.all(np.isfinite(cached)) and cached.min() > 0:
                return cached.copy()
        return np.ones(n)

    def pressure(self, a, iters=500, tol=1e-13, want_grad=True):
        """log spectral radius, and (Gibbs Phi_h, Gibbs entropy)."""
        lw = self.weights(a)
        m = lw.max()
        w = np.exp(lw - m)
        n = 1 << self.L
        h2 = n >> 1
        W0 = w[:n].reshape(h2, 2)                       # WP1: views, not gathers
        W1 = w[n:].reshape(h2, 2)
        brtol = max(float(tol), 1e-13)
        vec = self.stop == 'vector'
        r = self._start(self._r, n)
        lam, best, stall = 1.0, np.inf, 0
        for it in range(iters):
            rn = (W0 * r[:h2, None] + W1 * r[h2:, None]).ravel()
            lam = rn.sum() / r.sum()
            gap = np.nan if vec else _bracket(rn, r)
            rn /= np.linalg.norm(rn)
            done = it > 8 and (np.max(np.abs(rn - r)) < tol if gap != gap else gap <= brtol)
            r = rn
            best, stall = _stall(gap, best, stall)
            if done or stall > 20:
                break
        self._r = r
        P = float(np.log(lam) + m)
        if not want_grad:
            return P, None
        l = self._start(self._l, n)
        best, stall = np.inf, 0
        for it in range(iters):
            l0, l1 = l[0::2], l[1::2]                   # WP1: strided views
            ln = np.concatenate([W0[:, 0] * l0 + W0[:, 1] * l1,
                                 W1[:, 0] * l0 + W1[:, 1] * l1])
            gap = np.nan if vec else _bracket(ln, l)
            ln /= np.linalg.norm(ln)
            done = it > 8 and (np.max(np.abs(ln - l)) < tol if gap != gap else gap <= brtol)
            l = ln
            best, stall = _stall(gap, best, stall)
            if done or stall > 20:
                break
        self._l = l
        lr = l.reshape(h2, 2)
        mu = np.concatenate([((lr * W0) * r[:h2, None]).ravel(),
                             ((lr * W1) * r[h2:, None]).ravel()])
        mu /= mu.sum()
        self._mu = mu
        return P, (self._phis(mu), P - float(np.sum(mu * lw)))

    def pressure_ub(self, a, iters=400, tol=1e-14):
        """Collatz-Wielandt upper bound on the pressure.  For ANY strictly positive
        vector r one has  lambda <= max_u (A r)_u / r_u,  so the value returned is a
        rigorous upper bound for the log spectral radius of the truncated operator
        whatever the power iteration did or failed to do -- warm starts included.
        Together with `delta_bound` this makes a certificate independent of the
        eigensolver:  P_true(psi_a) <= pressure_ub(a) + delta_bound(W, a).
        Returns +inf when the weights underflow (bound unavailable, never unsound)."""
        lw = self.weights(a)
        m = lw.max()
        w = np.exp(lw - m)
        n = 1 << self.L
        h2 = n >> 1
        W0 = w[:n].reshape(h2, 2)
        W1 = w[n:].reshape(h2, 2)
        brtol = max(float(tol), 1e-14)
        vec = self.stop == 'vector'
        r = self._start(self._r, n)
        best, stall = np.inf, 0
        for it in range(iters):
            rn = (W0 * r[:h2, None] + W1 * r[h2:, None]).ravel()
            top = rn.max()
            if not np.isfinite(top) or top <= 0:
                return float('inf')
            gap = np.nan if vec else _bracket(rn, r)
            rn /= top
            done = it > 8 and (np.max(np.abs(rn - r)) < tol if gap != gap else gap <= brtol)
            r = rn
            best, stall = _stall(gap, best, stall)
            if done or stall > 20:
                break
        if r.min() <= 0:
            return float('inf')
        self._r = r
        ratio = (W0 * r[:h2, None] + W1 * r[h2:, None]).ravel() / r
        return float(np.log(ratio.max()) + m)


def _stall(gap, best, stall):
    """Track how long the Collatz-Wielandt bracket has failed to improve.  Under a
    power iteration the bracket is monotone, so a stall means the floating-point floor
    has been reached and further iterations buy nothing."""
    if gap != gap:
        return best, 0
    if gap < best - 1e-16:
        return gap, 0
    return best, stall + 1


def _bracket(rn, r):
    """log(max_u rn_u/r_u) - log(min_u rn_u/r_u), or nan if the ratio is unusable.

    WP2's stopping rule.  Both the Rayleigh value `rn.sum()/r.sum()` and the true
    spectral radius lie in [min ratio, max ratio], so this width bounds the error in
    the reported pressure -- which is the quantity the certificate needs, unlike an
    iterate difference.
    """
    with np.errstate(divide='ignore', invalid='ignore'):
        q = rn / r
        lo, hi = q.min(), q.max()
    if not (lo > 0 and np.isfinite(hi)):
        return float('nan')
    return float(math.log(hi) - math.log(lo))


def delta_bound(W, a):
    """Rigorous truncation slack: P_true(psi_a) <= P_computed + delta.

    WP5: charges `W.eps = W.err + 1/(2G)`, so the resolution of the WP3 grid is inside
    the enclosure rather than beside it.  When no grid is in use `W.eps == W.err` and
    this is the original bound to the last bit.
    """
    return float(2 * np.pi * np.sum(W.modes * np.abs(a)) * W.eps)


def h_min(al):
    """Ledrappier-Young entropy floor for a counterexample (alpha a unit)."""
    la, lr = math.log(float(al.alpha)), math.log(1 / float(al.rho))
    return la * lr / (la + lr)


def minimize_pressure(W, x0=None, maxiter=500, cap=60.0, exact_phis=False,
                      gap_target=None, rounds=4, bundle=True, bundle_max=600,
                      strict_box=False):
    """min over multipliers of P(psi_a): the constrained entropy E(modes).

    WP6.  Two structural facts are used, and one is deliberately not.

    Convex.  `P(phi) = sup_mu {h(mu) + int phi dmu}` is a supremum of affine functionals
    of the potential, hence convex, and `a -> psi_a` is R-linear; so `a -> P(psi_a)` is
    convex on `C^H = R^(2H)` with exact gradient `dP/da_h = Phi_h(mu_a)` (M7 Cor. 3).
    Every local minimum is global, so **no multi-start is needed and none should be
    added at large H** -- what is needed is a stopping criterion in the objective, not
    in the iterate.  That is `gap_target`: the cutting planes `P_j + <g_j, x - x_j>`
    collected along the way are a lower model of `P`, and minimising that model over the
    box is an LP whose value brackets the solve from below (`W.last_solve['lb_box']`).
    With `gap_target` set, L-BFGS is restarted from `x*` until the bracket closes to it.

    Boxed.  `cap` silently turns `inf_a` into `inf_{|a|_inf <= cap}`, and a bound
    reported from an active box is not `E_H`.  It is still a valid certificate if it
    fires -- `inf_box P >= E_H` -- but it may not be compared against an LP lower bound,
    and the bundle bracket then bounds `inf_box P`, not `E_H`.  So the box is audited on
    every run: `W.last_solve['box_active']` records the verdict, an active box warns,
    and `strict_box=True` makes it an error.
    """
    K = len(W.modes)
    if K == 0:
        P0 = W.pressure(np.zeros(0, dtype=complex), want_grad=False)[0]
        W.last_solve = dict(P=P0, delta=0.0, cert=P0, S1=0.0, amax=0.0, xmax=0.0,
                            cap=cap, box_active=False, nfev=0, lb_box=P0, gap=0.0,
                            resid=0.0, rounds=0)
        return P0, np.zeros(0), 0.0, 0.0

    planes = []

    def f(x):
        a = x[:K] + 1j * x[K:]
        P, g = W.pressure(a)
        if not np.isfinite(P):
            return 1e6, np.zeros(2 * K)
        grad = np.concatenate([g[0].real, -g[0].imag])
        if bundle:
            planes.append((float(P), x.copy(), grad))
            if len(planes) > 2 * bundle_max:            # keep the most recent, plus
                best = min(planes, key=lambda t: t[0])  # the incumbent
                planes[:] = [best] + planes[-bundle_max:]
        return P, grad

    x = np.zeros(2 * K) if x0 is None else np.asarray(x0, dtype=float).copy()
    bounds = [(-cap, cap)] * (2 * K)
    opts = dict(maxiter=maxiter, ftol=1e-15, gtol=1e-12)
    P, gap, lb, nrounds = np.inf, float('inf'), None, 0
    for nrounds in range(1, max(1, rounds) + 1):
        r = minimize(f, x, jac=True, method='L-BFGS-B', bounds=bounds, options=opts)
        x, P = r.x, float(r.fun)
        lb = _bundle_lb(planes, cap) if bundle else None
        gap = float('inf') if lb is None else max(0.0, P - lb)
        if gap_target is None or gap <= gap_target:
            break

    a = x[:K] + 1j * x[K:]
    P, (phis, ent) = W.pressure(a)
    if exact_phis and W.grid is not None:
        phis = W.phis_exact(W._mu)              # the Gibbs measure `pressure` just built
    P, d = float(P), delta_bound(W, a)
    amax, xmax = float(np.abs(a).max()), float(np.abs(x).max())
    active = xmax >= cap * (1 - 1e-9)
    W.last_solve = dict(
        P=P, delta=d, cert=P + d, S1=float(np.sum(W.modes * np.abs(a))),
        amax=amax, xmax=xmax, cap=cap, box_active=bool(active),
        nfev=len(planes), lb_box=lb, gap=gap, rounds=nrounds,
        resid=float(np.abs(phis).max()))
    if active:
        msg = ('multiplier box active at cap=%g (max|a_h| = %.4g, max|x_j| = %.4g): '
               'the value %.9f bounds inf over the box, not E_H' % (cap, amax, xmax, P))
        if strict_box:
            raise RuntimeError(msg)
        warnings.warn(msg, RuntimeWarning, stacklevel=2)
    return P, x, float(np.abs(phis).max()), d


def _bundle_lb(planes, cap):
    """min over the box of the cutting-plane model max_j {P_j + <g_j, x - x_j>}.

    A lower bound for `inf_{|x|_inf <= cap} P`, by convexity, and hence for `E_H` too
    whenever the box turns out to be inactive at the optimum.  Returns None if the LP
    fails (an unusable bracket is never reported as a bound).

    It is a *numerical* bracket, not a certificate: convexity holds for the exact `P`,
    while the planes carry the pressure's own evaluation error, so the model can exceed
    `P(x*)` by that much and the reported gap is clamped at zero.  In practice the floor
    is around `1e-11`, the accuracy of the WP2 bracket.  The rigorous statement remains
    `pressure_ub + delta_bound`, which touches none of this.
    """
    good = [(P, x, g) for P, x, g in planes if np.isfinite(P) and P < 1e5]
    if not good:
        return None
    n = len(good[0][1])
    A = np.empty((len(good), n + 1))
    b = np.empty(len(good))
    for j, (P, x, g) in enumerate(good):
        A[j, :n], A[j, n] = g, -1.0                 # <g_j, x> - t <= <g_j, x_j> - P_j
        b[j] = float(np.dot(g, x)) - P
    c = np.zeros(n + 1)
    c[n] = 1.0
    bnds = [(-cap, cap)] * n + [(None, None)]
    r = linprog(c, A_ub=A, b_ub=b, bounds=bnds, method='highs')
    return float(r.fun) if r.success else None


def pad(x, Hp, Hn):
    """Zero-pad a multiplier vector from Hp modes to Hn: the WP6 warm-start ladder.

    (The same four lines as `m4_fourier.pad`; kept here so that M3's own continuation
    driver does not depend on an M4 module.)
    """
    if x is None:
        return None
    z = np.zeros(Hn - Hp)
    return np.concatenate([x[:Hp], z, x[Hp:], z])


def E_curve(al, Hs, L=None, slack=0.05, target=None, cap=60.0, maxiter=500,
            Lmin=10, Lmax=26, adapt=True, growth=2.5, gap_target=None,
            unbounded_gap=1e-2, stop_when_unbounded=True, verbose=True):
    """WP6 + WP7: the whole `E_H` curve, continuing in H and re-windowing as it goes.

    Solve at `Hs[0]`, pad the optimal multiplier with zeros, warm-start at `Hs[1]`, and
    so on: with WP2's warm-started eigenvectors each doubling is a short refinement
    rather than a fresh solve.  It is the curve, not the single value, that M3 sec 9.2
    and M4 sec 8 disagree about.

    WP7 rides on the same loop.  The window is set by the multiplier norm
    `S1 = sum_h h|a_h|`, and `S1` is not known until the solve is done -- M3's
    operational lesson (a).  So each stage reports its own `S1`, and the next stage's
    window is chosen from it by `choose_window`, with a budget of `slack` times the
    current distance to the floor (or the fixed `target`, if given).  This is why the
    rule of thumb `L ~ log h / h_min` is not used: it is the multiplier norm that binds,
    and it grows with H.

    Returns one record per H.  `cert = P + delta` is the rigorous upper bound for the
    true pressure and `fires = cert < h_min` says whether 10.61 is proved at this alpha
    by this multiplier.

    By M7 Thm 1 the quantity being computed is `E_H = max {h(mu) : mu sigma-invariant,
    Phi_h(mu) = 0 for h <= H}`, so it is non-increasing in H, and it is `-inf` exactly
    when no invariant measure kills the first `H` modes (M3 sec 9.1).  In that case the
    solve is unbounded below, `S1` runs away, the bundle bracket never closes, and the
    numbers are simply wherever `cap` stopped it: `unbounded` flags this.  The
    certificate is still sound -- `delta` grows with `S1` and `P + delta` falls anyway --
    but the value must not be read as `E_H`, and the run should stop at that H.
    """
    hm = h_min(al)
    S1 = 1.0
    if L is None:
        L = choose_window(al, S1, target or 1e-3, Lmin, Lmax)['L']
    win = best_split(al, L)
    W = Window(al, win[0], win[1])
    out, xp, Hp = [], None, 0
    if verbose:
        print('%-16s alpha=%.6f  h_min=%.6f' % (getattr(al, 'name', '?'),
                                                float(al.alpha), hm), flush=True)
        print('  %-5s %-3s %-9s  %-11s %-10s %-11s %-8s %-8s %-9s %s'
              % ('H', 'L', 'eps', 'E_ub', 'delta', 'cert', 'margin', 'S1', 'gap', ''),
              flush=True)
    for H in Hs:
        W.set_modes(list(range(1, H + 1)))
        P, x, resid, d = minimize_pressure(W, x0=pad(xp, Hp, H), cap=cap,
                                           maxiter=maxiter, gap_target=gap_target)
        ls = W.last_solve
        rec = dict(H=H, L=W.L, N=W.N, M=W.M, eps=W.eps, err=W.err, grid=W.grid,
                   E_ub=P, delta=d, cert=P + d, h_min=hm, margin=hm - (P + d),
                   S1=ls['S1'], amax=ls['amax'], box_active=ls['box_active'],
                   lb_box=ls['lb_box'], gap=ls['gap'], resid=resid,
                   fires=bool(P + d < hm),
                   unbounded=bool(ls['box_active'] or ls['gap'] > unbounded_gap),
                   x=list(x))
        out.append(rec)
        if verbose:
            print('  %-5d %-3d %-9.2e  %-11.7f %-10.2e %-11.7f %-+8.5f %-8.3f %-9.1e %s'
                  % (H, W.L, W.eps, P, d, P + d, hm - (P + d), ls['S1'], ls['gap'],
                     ('UNBOUNDED (no invariant measure kills h <= %d)' % H)
                     if rec['unbounded'] else ('CERT' if rec['fires'] else '.')),
                  flush=True)
        xp, Hp = x, H
        if rec['unbounded'] and stop_when_unbounded:
            if verbose:
                print('    stopping: E_H = -inf from here on', flush=True)
            break
        if adapt and H != Hs[-1]:
            budget = target if target is not None else \
                max(1e-6, slack * abs(P + d - hm))
            # S1 grows with H, so aim at the *next* rung's norm and never shrink the
            # window: a ladder that re-deepens what it just shed pays for the word
            # table twice and learns nothing.
            nxt = choose_window(al, growth * ls['S1'], budget, max(Lmin, W.L), Lmax)
            if (nxt['N'], nxt['M']) != (W.N, W.M):
                del W
                W = Window(al, nxt['N'], nxt['M'])
                if verbose:
                    print('    re-window for the next rung: (%d,%d) L=%d eps=%.2e '
                          '(budget %.2e at S1=%.3f)%s'
                          % (nxt['N'], nxt['M'], nxt['L'], nxt['eps'], budget,
                             ls['S1'], '  [Lmax reached]' if nxt['short'] else ''),
                          flush=True)
    return out


# ---- WP7: the window ------------------------------------------------------

def window_eps(al, N, M):
    """The truncation error of the window `(-N .. M-1)`: `alpha^-M` for the future part
    and `C_alpha rho^(N+1)/(1-rho)` for the past part (M3 sec 7)."""
    a, rho = float(al.alpha), float(al.rho)
    Ca = float(sum(abs(complex(z) - 1.0) for z in al.conj))
    return a ** (-M) + Ca * rho ** (N + 1) / (1 - rho)


def best_split(al, L):
    """The split `N + M = L` minimising `window_eps`; returns `(N, M, eps)`.

    At the quadratic units `rho = 1/alpha` and the balanced split is within one step of
    optimal (M4 Thm 5), which is why M3 never saw this; at the cubics it is worth an
    order of magnitude.  Agrees with `m4_fourier.best_window`.
    """
    cand = [(window_eps(al, L - M, M), L - M, M) for M in range(1, L)]
    e, N, M = min(cand)
    return N, M, e


def choose_window(al, S1, target, Lmin=10, Lmax=26):
    """WP7: the shallowest window whose enclosure costs at most `target`.

    `delta = 2 pi S1 eps` with `S1 = sum_h h |a_h|`, so the window is fixed by the
    multiplier norm and by nothing else -- not by the mode count, and not by the
    `log h / h_min` resolution heuristic, which is the weaker requirement at every
    `H <= 10^3`.  The factor `1.1` covers the WP5 grid term, which `_grid_size` keeps
    at or below a tenth of `eps`.

    Returns `dict(L, N, M, eps, delta, short)`; `short` flags that `Lmax` was reached
    before the budget was met, so the caller knows the bound is the best available and
    not the one asked for.
    """
    for L in range(Lmin, Lmax + 1):
        N, M, e = best_split(al, L)
        d = 2 * np.pi * S1 * e * 1.1
        if d <= target:
            return dict(L=L, N=N, M=M, eps=e, delta=d, short=False)
    N, M, e = best_split(al, Lmax)
    return dict(L=Lmax, N=N, M=M, eps=e, delta=2 * np.pi * S1 * e * 1.1, short=True)


def bern_phi(al, H, J=600):
    """|Phi_h| for the Bernoulli(1/2) measure, h = 1..H: the two Erdos products
    |prod_j cos(pi h (alpha-1) alpha^{-j})| * |prod_m cos(pi h c_m)|."""
    a = float(al.alpha)
    h = np.arange(1, H + 1, dtype=float)
    out = np.ones(H)
    for j in range(1, J + 1):
        w = (a - 1.0) * a ** (-j)
        if w * H < 1e-14:
            break
        out *= np.abs(np.cos(np.pi * h * w))
    for m in range(J):
        c = float(sum((complex(z) - 1) * complex(z) ** m for z in al.conj).real)
        if abs(c) * H < 1e-14:
            break
        out *= np.abs(np.cos(np.pi * h * c))
    return out
