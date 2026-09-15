#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R1a runner: the M7 pool at `1+sqrt2`, re-parametrised and enclosed.

M7 sec 4's pool is the Gibbs measures of the window transfer operator at `a*` and
`a* +- t e_h`, `a* +- i t e_h` -- memory-12 Markov chains given by conditional
probabilities `q`, whose stationary vector is a numerical solve.  `r1a_enclose` shows that
a rigorous `Phi` wants the measure given as a **circulation** instead, so this runner
converts the pool and encloses it:

    Gibbs q  ->  w[b,x] = pi~[b] q~[b,x]  ->  circ_from_weights (exact, deterministic)
             ->  Phi_h enclosed to 1.5e-13, entropy recomputed from the circulation.

Two things are then checked, and together they are R1a's gate:

  * the converted pool reproduces M7 sec 4's LP lower bound for `E_H(1+sqrt2)` to well
    inside the `1e-5` at which M7's two brackets cross -- so the re-parametrisation costs
    nothing that matters;
  * the enclosure radius is nine orders of magnitude below that crossing, so the LP's
    Theorem 5 correction term `eps ||a||_1` is not the binding error either.

Writes `r1a_pool.json` (enclosed Phi as midpoint + radius, entropies, provenance).
Usage: python3 r1a_pool.py [H ...]      default H = 8 16
"""
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
from m7_price import BlockChain, lp_lower
from scipy.optimize import linprog


def hull_distance(phi, H):
    """min over mixtures of ||sum_j lam_j Phi(nu_j)||_inf -- zero iff 0 is in the hull.

    The observable R2 turns into the conditioned margin m(H); here it is what says whether
    a pool is feasible at all, and how far from the boundary it sits when it is."""
    v = np.concatenate([np.asarray(phi)[:, :H].real, np.asarray(phi)[:, :H].imag], axis=1)
    m = v.shape[0]
    A = np.hstack([np.vstack([v.T, -v.T]), -np.ones((4 * H, 1))])
    r = linprog(np.append(np.zeros(m), 1.0), A_ub=A, b_ub=np.zeros(4 * H),
                A_eq=np.append(np.ones(m), 0.0).reshape(1, -1), b_eq=[1.0],
                bounds=[(0, None)] * m + [(None, None)], method='highs')
    return float(r.x[-1]) if r.success else float('nan')

LPOOL = 12
TS = [0.01, 0.04, 0.15, 0.5]
TDEN = 10 ** 10                     # circulation denominator: repair cost ~ L 2^L / T
JDEP = MDEP = 60                    # window of the enclosure (NOT the transfer window)
HS = [int(x) for x in sys.argv[1:] if x.isdigit()] or [8, 16]
OUT = ('/home/ralf/math/lean-code/BB61/'
       + (sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv
          else 'r1a_pool.json'))

# M7 sec 4, the 1+sqrt2 rows: (upper from the optimiser, lower from the LP)
M7ROW = {1: (0.693098, 0.693098), 2: (0.693098, 0.693098), 4: (0.691068, 0.691073),
         8: (0.690096, 0.690102), 16: (0.689063, 0.689054), 32: (0.687346, 0.687024),
         64: (0.683271, 0.677497)}


def pool_vectors(H, xstar):
    out = [xstar.copy()]
    for h in range(1, H + 1):
        for t in TS:
            for sgn in (1, -1):
                for im in (0, 1):
                    x = xstar.copy()
                    x[(h - 1) + im * H] += sgn * t
                    out.append(x)
    return out


def hull_report(phi, ent, H, eps):
    """What R1a's enclosed data already says about R1b's certificate.

    Three readings of the same pool, and they are not the same question:
      (a) the entropy-maximising LP of M7 Thm 5 -- its basic solution is a Caratheodory
          simplex of `2H+1` atoms, and R1b's four numbers are read off it;
      (b) the MAXIMIN-weight LP `max t s.t. sum lam_j Phi_j = 0, lam_j >= t` -- the right
          objective for a *certificate*, which asks only that 0 be surrounded;
      (c) the hull distance `min_lam ||sum lam_j Phi_j||_inf`, zero iff 0 is in the hull.
    (a) drives the weights to the boundary of the weight simplex because entropy is a
    linear objective; (b) does not, and it reports a depth two orders of magnitude larger.
    """
    m = len(ent)
    V = np.concatenate([np.asarray(phi)[:, :H].real, np.asarray(phi)[:, :H].imag], axis=1)
    out = dict(H=H, m=m, eps=eps)
    A = np.vstack([np.ones((1, m)), V.T])
    b = np.zeros(2 * H + 1)
    b[0] = 1.0
    r = linprog(-np.asarray(ent), A_eq=A, b_eq=b, bounds=(0, None), method='highs')
    if r.success:
        lam = r.x
        at = np.where(lam > 1e-13)[0]
        out['entropy_lp'] = dict(value=float(np.dot(ent, lam)), atoms=int(len(at)),
                                 residual=float(np.max(np.abs(A @ lam - b))))
        if len(at) == 2 * H + 1:
            D = (V[at][1:] - V[at][0]).T
            sv = float(np.linalg.svd(D, compute_uv=False)[-1])
            wm = float(lam[at].min())
            out['simplex'] = dict(w_min=wm, s=sv, margin=wm * sv, ratio=wm * sv / eps)
    A_eq = np.vstack([np.hstack([V.T, np.zeros((2 * H, 1))]), np.append(np.ones(m), 0.0)])
    b_eq = np.append(np.zeros(2 * H), 1.0)
    A_ub = np.hstack([-np.eye(m), np.ones((m, 1))])
    r = linprog(np.append(np.zeros(m), -1.0), A_ub=A_ub, b_ub=np.zeros(m),
                A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * m + [(None, None)],
                method='highs')
    if r.success:
        lam, t = r.x[:m], float(r.x[-1])
        sv = float(np.linalg.svd(V.T, compute_uv=False)[-1])
        out['maximin'] = dict(t=t, residual=float(np.max(np.abs(V.T @ lam))),
                              entropy=float(np.dot(ent, lam)), sigma_min=sv,
                              ratio=t * sv / eps)
    out['hull_distance'] = hull_distance(phi, H)
    return out


def report():
    d = json.load(open(OUT))
    print(f"# R1a hull report   alpha={d['alpha']:.9f}  h_min={d['h_min']:.6f}  "
          f"L={d['Lpool']}  T={d['T']:.0e}")
    for Hs, row in sorted(d['rows'].items(), key=lambda kv: int(kv[0])):
        H = int(Hs)
        phi = np.array(row['phi_re']) + 1j * np.array(row['phi_im'])
        o = hull_report(phi, np.array(row['ent']), H, row['radius'])
        print(f"\nH={H}  pool {o['m']}  enclosure radius {o['eps']:.2e}  "
              f"hull distance {o['hull_distance']:.1e}")
        e = o.get('entropy_lp')
        if e:
            print(f"   entropy LP (M7 Thm 5): value {e['value']:.6f}  atoms {e['atoms']} "
                  f"(2H+1 = {2 * H + 1})  residual {e['residual']:.1e}")
        sx = o.get('simplex')
        if sx:
            print(f"   R1b four numbers on that simplex: w_min {sx['w_min']:.3e}  "
                  f"s {sx['s']:.3e}  margin w_min*s {sx['margin']:.3e}  "
                  f"= {sx['ratio']:.1e} x the enclosure radius")
        mm = o.get('maximin')
        if mm:
            print(f"   maximin-weight LP: every pool member carries lam >= {mm['t']:.3e}, "
                  f"residual {mm['residual']:.1e}, sigma_min(V) {mm['sigma_min']:.3e}, "
                  f"t*sigma = {mm['t'] * mm['sigma_min']:.3e} = {mm['ratio']:.1e} x eps")


def main():
    if '--report' in sys.argv:
        return report()
    al = Alpha([1, -2, -1], '1+sqrt2')
    hm = h_min(al)
    N, M, e = best_window(al, LPOOL)
    W = Window(al, N, M)
    bc = BlockChain(al, LPOOL, hmax=max(HS))
    print(f"# R1a pool   alpha={float(al.alpha):.9f}  h_min={hm:.6f}  "
          f"transfer window ({N},{M}) eps={e:.2e}  L={LPOOL}  T=1e{len(str(TDEN)) - 1}  "
          f"enclosure window ({JDEP},{MDEP})", flush=True)
    rec = dict(alpha=float(al.alpha), h_min=hm, Lpool=LPOOL, T=TDEN,
               enclosure_window=[JDEP, MDEP], transfer_window=[N, M, float(e)], rows={})
    xp, Hp = None, 0
    if '--resume' in sys.argv and os.path.exists(OUT):   # a long ladder must be resumable
        rec = json.load(open(OUT))
        done = sorted(H for H in map(int, rec['rows'])
                      if 'xstar' in rec['rows'][str(H)])
        have = sorted(map(int, rec['rows']))
        if done:
            Hp = done[-1]
            xp = np.array(rec['rows'][str(Hp)]['xstar'])
        print(f"# resumed from {OUT}: rows {have}, warm start at "
              f"{('H=%d' % Hp) if done else 'none (pre-xstar file)'}", flush=True)
    for H in HS:
        if ('--resume' in sys.argv and str(H) in rec['rows']
                and 'xstar' in rec['rows'][str(H)]):
            continue        # already computed, and with a warm start to hand on
        W.set_modes(list(range(1, H + 1)))
        t0 = time.time()
        P, xstar, flat, delta = minimize_pressure(W, x0=pad(xp, Hp, H))
        xp, Hp = xstar, H
        hs = list(range(1, H + 1))
        ent, phi, rads, rep, raw = [], [], [], [], []
        for i, x in enumerate(pool_vectors(H, xstar)):
            a = x[:H] + 1j * x[H:]
            q = bc.from_window(W, a)
            pi = bc.stationary(q)
            if not (np.isfinite(q).all() and np.isfinite(pi).all()):
                continue
            w = np.empty(1 << (LPOOL + 1))
            w[0::2] = pi * (1 - q)
            w[1::2] = pi * q
            if not np.isfinite(w).all() or w.sum() <= 0:
                continue
            c = R.circ_from_weights(LPOOL, w, TDEN)
            V, rad = R.phi_fl(c, hs, JDEP, MDEP)
            h_c = c.entropy()
            p7 = np.asarray(bc.phis(q, hs, pi))
            if not (np.isfinite(h_c) and np.isfinite(V).all() and np.isfinite(p7).all()):
                continue
            raw.append(p7)
            ent.append(h_c)
            phi.append(V)
            rads.append(max(rad))
            rep.append(c.repair_cost)
        ent, phi, raw = np.array(ent), np.array(phi), np.array(raw)
        d_circ, d_m7 = hull_distance(phi, H), hull_distance(raw, H)
        val_m7, _ = lp_lower(ent, raw, H)
        val, lam = lp_lower(ent, phi, H)
        if lam is None:
            resid, atoms = float('nan'), 0
        else:
            A = np.vstack([np.ones((1, len(ent))), phi[:, :H].real.T, phi[:, :H].imag.T])
            b = np.zeros(A.shape[0]); b[0] = 1.0
            resid = float(np.max(np.abs(A @ lam - b)))
            atoms = int((lam > 1e-12).sum())
        m7u, m7l = M7ROW.get(H, (None, None))
        line = (f"H={H:<4} pool {len(ent):4d}  upper(optimiser) {P:.6f}  "
                f"lower(circulations) {('%.6f' % val) if val is not None else '   --   '}  "
                f"atoms {atoms:3d}  LP residual {resid:.2e}  "
                f"radius {max(rads):.2e}  repair {max(rep):.1e}  {time.time() - t0:.0f}s")
        print(line, flush=True)
        print(f"       same pool, M7's own Phi (float, numerical pi): lower "
              f"{('%.6f' % val_m7) if val_m7 is not None else '   --   '}   "
              f"hull distance: circulations {d_circ:.3e}, M7 {d_m7:.3e}", flush=True)
        if m7l is not None:
            print(f"       M7 sec 4 row: upper {m7u:.6f} lower {m7l:.6f}   "
                  f"|delta upper| {abs(P - m7u):.2e}" +
                  (f"  |delta lower| {abs(val - m7l):.2e}" if val is not None else
                   "  lower: pool infeasible after conversion"), flush=True)
        rec['rows'][str(H)] = dict(
            n_pool=int(len(ent)), upper=float(P), lower=(None if val is None else float(val)),
            atoms=int(atoms), lp_residual=float(resid), radius=float(max(rads)),
            repair=float(max(rep)), m7_upper=m7u, m7_lower=m7l,
            lower_m7phi=(None if val_m7 is None else float(val_m7)),
            hull_distance_circ=d_circ, hull_distance_m7=d_m7,
            ent=[float(x) for x in ent],
            xstar=[float(v) for v in xstar],
            phi_re=[[float(z.real) for z in row] for row in phi],
            phi_im=[[float(z.imag) for z in row] for row in phi])
        with open(OUT, 'w') as f:      # dump after every H: a long ladder must be resumable
            json.dump(rec, f)
    with open(OUT, 'w') as f:
        json.dump(rec, f)
    print(f"# wrote {OUT}", flush=True)


if __name__ == '__main__':
    main()
