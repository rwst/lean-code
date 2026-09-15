#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2a: the pool, built member by member and cheap enough to grow inside a loop.

R1b built its pools with `r1a_pool.py`, which is a *batch* runner: it computes the whole
M7 pool at one `H` and writes it out.  R2a's Farkas / margin-increasing loop needs the
opposite shape -- a builder that can be handed a single multiplier vector `x` and return
that member's enclosed `Phi` -- and it needs the ladder to reach `H = 512`, where the batch
runner would take a day.  Two changes buy the factor that makes that possible:

  * `stationary()` in `m7_price.BlockChain` is a dense `2^L x 2^L` solve, 0.88 s at
    `L = 12` and by far the largest cost per member.  Pool members are small perturbations
    of one another, so a power iteration warm-started at the previous member's `pi`
    converges in tens of steps: 0.0015 s, a factor of 500, and it agrees with the dense
    solve to 1.4e-11 relative.  **This costs no rigour at all**: `pi` only decides *which*
    invariant measure the member is, and `circ_from_weights` then turns whatever weights it
    is given into an exact rational circulation, whose `Phi` is what gets enclosed.  A less
    accurate `pi` is a slightly different -- and equally valid -- member of the pool.
  * `r1a_enclose._const_table` re-evaluates `H * (J+M+1)` cosines at 60 digits for every
    member; it depends only on `(hs, J, M)`, so it is memoised here.

What is NOT changed is the pool itself: the members are exactly M7 sec 4's, the Gibbs
measures of the window transfer operator at `a*` and `a* +- t e_h`, `a* +- i t e_h`.  The
loop adds to that pool; it does not replace it (sec 8 of `plan-BB61-counterexample.html`).

Usage:  python3 r2a_pool.py --check                       # reproduce r1b_pool64's H=64
        python3 r2a_pool.py --build 2 1 1+sqrt2 128 256   # extend the ladder, npz per H
"""
import functools
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
import r1a_enclose as R
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure
from m4_fourier import best_window, pad
from m7_price import BlockChain
from r1a_pool import JDEP, LPOOL, MDEP, TDEN, TS, pool_vectors

BB = '/home/ralf/math/lean-code/BB61'

_orig_const_table = R._const_table


@functools.lru_cache(maxsize=8)
def _const_table_cached(hs, J, M):
    return _orig_const_table(list(hs), J, M)


R._const_table = lambda hs, J, M: _const_table_cached(tuple(hs), J, M)


class Pool:
    """The M7 pool at one `(alpha, H)`, with members produced on demand.

    `member(x)` returns `(Phi enclosed, radius, entropy)` for the Gibbs measure at the
    multiplier vector `x in R^{2H}` (real parts first, then imaginary), converted to an
    exact circulation on the way.  `None` if the chain degenerates."""

    def __init__(self, A, B, name, H, xstar=None, verbose=False, L=LPOOL, T=TDEN):
        self.al = Alpha([1, -A, -B], name)
        self.H, self.name, self.A, self.B = H, name, A, B
        self.L, self.T = L, T
        self.h_min = h_min(self.al)
        N, M, e = best_window(self.al, L)
        self.win = Window(self.al, N, M)
        self.win.set_modes(list(range(1, H + 1)))
        self.transfer = (N, M, float(e))
        self.eps_win = float(e)
        self.bc = BlockChain(self.al, L, hmax=H)
        self.hs = list(range(1, H + 1))
        self._pi = None                      # warm start, carried between members
        self.verbose = verbose
        self.xstar, self.P = xstar, None
        self.n_member = self.n_reject = 0

    # -- the centre of the pool ------------------------------------------------------
    def optimise(self, x0=None, **kw):
        t0 = time.time()
        P, xs, flat, delta = minimize_pressure(self.win, x0=x0, **kw)
        self.xstar, self.P = xs, float(P)
        if self.verbose:
            print(f"    minimize_pressure H={self.H}: P={P:.9f}  {time.time() - t0:.0f}s",
                  flush=True)
        return P, xs

    # -- one member ------------------------------------------------------------------
    def stationary(self, q, pi0=None, iters=4000, tol=1e-14):
        """Power iteration on the block chain; returns `(pi, converged)`.

        A warm start is what makes this 500x cheaper than the dense solve, but a warm
        start also PROPAGATES a failure: one degenerate member would otherwise poison
        every member after it, and `circ_from_weights` would then be handed something
        that is not a near-circulation.  So convergence is reported, and `member` retries
        from cold before giving up on a member."""
        bc = self.bc
        b0, b1 = bc.bwd[:, 0], bc.bwd[:, 1]
        s = np.arange(bc.n) & 1
        c0 = np.where(s == 1, q[b0], 1.0 - q[b0])
        c1 = np.where(s == 1, q[b1], 1.0 - q[b1])
        pi = np.full(bc.n, 1.0 / bc.n) if pi0 is None else np.maximum(pi0, 0.0)
        t = pi.sum()
        pi = pi / t if t > 0 else np.full(bc.n, 1.0 / bc.n)
        for _ in range(iters):
            nx = pi[b0] * c0 + pi[b1] * c1
            t = nx.sum()
            if not (t > 0) or not np.isfinite(t):
                return None, False
            nx /= t
            if np.max(np.abs(nx - pi)) < tol:
                return nx, True
            pi = nx
        return pi, False

    def member(self, x):
        H = self.H
        a = np.asarray(x)[:H] + 1j * np.asarray(x)[H:]
        q = self.bc.from_window(self.win, a)
        if not np.isfinite(q).all():
            return None
        for pi0 in (self._pi, None):              # warm, then cold; never propagate a failure
            pi, conv = self.stationary(q, pi0)
            if pi is not None and conv and np.isfinite(pi).all():
                break
        else:
            self.n_reject += 1
            return None
        w = np.empty(1 << (self.L + 1))
        w[0::2] = pi * (1 - q)
        w[1::2] = pi * q
        if not np.isfinite(w).all() or w.sum() <= 0:
            self.n_reject += 1
            return None
        try:
            c = R.circ_from_weights(self.L, w, self.T)
        except AssertionError:                    # not a near-circulation: not a member
            self.n_reject += 1
            return None
        V, rad = R.phi_fl(c, self.hs, JDEP, MDEP)
        h_c = c.entropy()
        if not (np.isfinite(h_c) and np.isfinite(V).all()):
            self.n_reject += 1
            return None
        self._pi = pi
        self.n_member += 1
        return V, max(rad), float(h_c), float(c.repair_cost)

    def members(self, xs, label=""):
        """Enclose a list of multiplier vectors; returns (Phi, radius, entropy, x kept)."""
        phi, ent, rads, rep, keep = [], [], [], [], []
        t0 = time.time()
        for i, x in enumerate(xs):
            out = self.member(x)
            if out is None:
                continue
            V, rad, h_c, rc = out
            phi.append(V); rads.append(rad); ent.append(h_c); rep.append(rc)
            keep.append(np.asarray(x, dtype=float))
            if self.verbose and (i + 1) % 256 == 0:
                print(f"    {label}{i + 1}/{len(xs)}  {time.time() - t0:.0f}s", flush=True)
        if not phi:
            return None
        return (np.array(phi), float(max(rads)), np.array(ent), np.array(keep),
                float(max(rep)), time.time() - t0)


def base_pool(pool):
    """M7 sec 4's pool at `pool.H`: `a*`, then `a* +- t e_h` and `a* +- i t e_h`."""
    return pool_vectors(pool.H, np.asarray(pool.xstar, dtype=float))


# The tilt magnitudes the loop uses.  M7's pool takes `t in TS = [0.01,0.04,0.15,0.5]`;
# R2a finds that the tilt SCALE, not the member count and not the steering direction, is
# what the certificate responds to.  Rebuilding the identical construction over a grid of
# scales, the certified margin peaks at `[0.1,0.5,2.5,12]` -- 1.44x M7's at BOTH `H = 8`
# and `H = 32`, with 30% fewer members, the rest lost because the tilted chain degenerates.
# Beyond `t ~ 12` the losses outrun the gain.  So the loop steers at these magnitudes.
TSWIDE = [0.1, 0.5, 2.5, 12.0]

# When the pool is INFEASIBLE the loop is not tuning a margin, it is trying to reach the
# far side of a separating plane, and then the magnitude has to be searched rather than
# sampled: at `(3+sqrt5)/2, H = 64` the Farkas ray crosses between `t = 0.5` (where
# `<u,Phi> = -4.6e-2`) and `t = 8` (where the tilted chain degenerates and there is no
# member at all), and a four-point grid can step straight over the window.
TSFINE = [0.05, 0.1, 0.2, 0.35, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 9.0, 14.0]


def steer(pool, u, ts=TSWIDE):
    """The members the loop adds: Gibbs measures tilted along `+-t u`.

    WP9 of `plan_BB61_improve_m3_entropy.html` adds the Gibbs measure at `a* - t c` for a
    Farkas direction `c`; here `u` is the direction in which the hull is thinnest and both
    signs are taken, which costs one member and removes any dependence on the sign
    convention relating a tilt of the potential to the resulting move in `Phi`."""
    x0 = np.asarray(pool.xstar, dtype=float)
    u = np.asarray(u, dtype=float)
    nu = np.linalg.norm(u)
    if not (nu > 0):
        return []
    u = u / nu
    return [x0 + s * t * u for t in ts for s in (1.0, -1.0)]


def build(A, B, name, Hs, out=None, x0=None, verbose=True, L=LPOOL, T=TDEN):
    """Build (or extend) the M7 pool ladder, one `H` at a time, warm-started throughout.

    Each rung is written as its own `.npz` before the next is started: at `H = 512` the
    pool is 8193 members and a rung is hours, so a ladder that cannot be resumed is a
    ladder that will be lost."""
    xp, Hp = x0, (0 if x0 is None else len(x0) // 2)
    for H in Hs:
        f = out or f'{BB}/r2a_pool_{name}_L{L}_{H}.npz'
        if os.path.exists(f):
            z = np.load(f)
            xp, Hp = z['xstar'], H
            print(f"# H={H}: {f} exists ({int(z['m'])} members), skipped", flush=True)
            continue
        t0 = time.time()
        p = Pool(A, B, name, H, verbose=verbose, L=L, T=T)
        p.optimise(x0=pad(xp, Hp, H))
        xp, Hp = p.xstar, H
        out_ = p.members(base_pool(p), label=f"H={H} ")
        phi, rad, ent, xs, rep, dt = out_
        np.savez_compressed(
            f, phi_re=phi.real, phi_im=phi.imag, ent=ent, xs=xs, xstar=p.xstar,
            H=H, m=len(ent), radius=rad, repair=rep, upper=p.P, h_min=p.h_min,
            alpha=float(p.al.alpha), coef=np.array([A, B]), transfer=np.array(p.transfer),
            Lpool=L, T=T, window=np.array([JDEP, MDEP]))
        print(f"# H={H:<4} pool {len(ent):5d}  upper(optimiser) {p.P:.6f}  "
              f"radius {rad:.3e}  repair {rep:.1e}  "
              f"{time.time() - t0:.0f}s  -> {os.path.basename(f)}", flush=True)


def _check():
    """The fast builder must reproduce `r1b_pool64.json`'s H=64 row."""
    import json
    d = json.load(open(f'{BB}/r1b_pool64.json'))
    row = d['rows']['64']
    ref = np.array(row['phi_re']) + 1j * np.array(row['phi_im'])
    p = Pool(2, 1, '1+sqrt2', 64, xstar=np.array(row['xstar']))
    xs = base_pool(p)[:64]
    out = p.members(xs)
    phi = out[0]
    err = np.max(np.abs(phi - ref[:len(phi)]))
    print(f"  members {len(phi)}/{len(xs)}   max |Phi_fast - Phi_r1b| = {err:.3e}   "
          f"radius {out[1]:.3e}   {out[5]:.1f}s  ({out[5] / len(phi):.3f}s/member)")
    ok = err < 1e-11 and len(phi) == len(xs)
    print("  ok   fast builder reproduces the R1b pool" if ok else "  FAIL")
    return 0 if ok else 1


def main():
    if '--check' in sys.argv:
        return _check()
    if '--build' in sys.argv:
        i = sys.argv.index('--build')
        A, B, name = int(sys.argv[i + 1]), int(sys.argv[i + 2]), sys.argv[i + 3]
        rest = sys.argv[i + 4:]
        stop = min([rest.index(f) for f in ('--L', '--x0') if f in rest] or [len(rest)])
        Hs = [int(x) for x in rest[:stop] if x.isdigit()]
        L = int(sys.argv[sys.argv.index('--L') + 1]) if '--L' in sys.argv else LPOOL
        x0 = None
        if '--x0' in sys.argv:                       # warm start from an existing rung
            z = np.load(sys.argv[sys.argv.index('--x0') + 1])
            x0 = z['xstar']
        print(f"# R2a pool ladder  alpha^2 = {A} alpha + {B}  ({name})  L={L}  H = {Hs}",
              flush=True)
        build(A, B, name, Hs, L=L, x0=x0)
        return 0
    print(__doc__)
    return 0


if __name__ == '__main__':
    sys.exit(main())
