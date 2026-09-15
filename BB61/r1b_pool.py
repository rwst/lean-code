#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R1b pool builder at an arbitrary quadratic Pisot unit.

`r1a_pool.py` is the same machine wired to `1+sqrt2`.  R1b needs it at the other two units
of M7 sec 4's table, for one reason: four rows there read "pool too small", i.e. `0` was not
found in the convex hull of the pool's `Phi`-vectors, and R1a's QA item (b) says that
verdict is partly an artefact of the objective -- M7's LP maximises entropy, a linear
objective whose optimum sits at a vertex, so it reports infeasibility where a maximin
reading finds `0` comfortably inside.  This runner rebuilds those rows with

    Gibbs q  ->  w[b,x] = pi~[b] q~[b,x]  ->  circ_from_weights (exact circulation)
             ->  Phi_h enclosed by `r1a_enclose.phi_fl` (general alpha since R1b)

and reports BOTH readings, so the four rows can be re-decided.  `r1b_certify.py` then turns
whichever of them are feasible into a proof.

Usage:  python3 r1b_pool.py <A> <B> <name> <H> [H ...]      # alpha^2 = A alpha + B
        e.g.  python3 r1b_pool.py 3 -1 golden2 1 2 4 8 16   # (3+sqrt5)/2
              python3 r1b_pool.py 3  1 root13  2 4 8 16     # (3+sqrt13)/2
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
from r1a_pool import LPOOL, TDEN, JDEP, MDEP, TS, hull_distance, pool_vectors
from scipy.optimize import linprog

BB = '/home/ralf/math/lean-code/BB61'

# M7 sec 4, all three units: alpha name -> H -> (upper from the optimiser, LP lower or None)
M7 = {'1+sqrt2': {1: (0.693098, 0.693098), 2: (0.693098, 0.693098),
                  4: (0.691068, 0.691073), 8: (0.690096, 0.690102),
                  16: (0.689063, 0.689054), 32: (0.687346, 0.687024),
                  64: (0.683271, 0.677497)},
      'golden2': {1: (0.689241, None), 2: (0.689004, 0.689004), 4: (0.672111, 0.671937),
                  8: (0.649254, 0.648870), 16: (0.640665, 0.639979),
                  32: (0.596576, 0.576992), 64: (0.544161, None)},
      'root13': {1: (0.689855, 0.689855), 2: (0.687838, None), 4: (0.681631, 0.681613),
                 8: (0.679809, None), 16: (0.672736, 0.672729), 32: (0.668581, 0.668510),
                 64: (0.654501, 0.653915)}}


def maximin(Vm):
    """max t s.t. sum lam_j Phi_j = 0, sum lam_j = 1, lam_j >= t -- the certificate reading."""
    d, m = Vm.shape
    A_eq = np.vstack([np.hstack([Vm, np.zeros((d, 1))]), np.append(np.ones(m), 0.0)])
    A_ub = np.hstack([-np.eye(m), np.ones((m, 1))])
    r = linprog(np.append(np.zeros(m), -1.0), A_ub=A_ub, b_ub=np.zeros(m), A_eq=A_eq,
                b_eq=np.append(np.zeros(d), 1.0), bounds=[(0, None)] * m + [(None, None)],
                method='highs')
    return float(r.x[-1]) if r.success else None


def main():
    A, B, name = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    HS = [int(x) for x in sys.argv[4:] if x.isdigit()]
    al = Alpha([1, -A, -B], name)
    R.set_alpha(A, B, name)
    hm = h_min(al)
    N, M, e = best_window(al, LPOOL)
    W = Window(al, N, M)
    bc = BlockChain(al, LPOOL, hmax=max(HS))
    out = f'{BB}/r1b_pool_{name}.json'
    print(f"# R1b pool   {name}: alpha={float(al.alpha):.9f}  abar={float(R.ABAR.mid):.9f}"
          f"  h_min={hm:.6f}   transfer window ({N},{M}) eps={e:.2e}   L={LPOOL}"
          f"   enclosure window ({JDEP},{MDEP})", flush=True)
    rec = dict(alpha=float(al.alpha), name=name, coeffs=[1, -A, -B], h_min=hm,
               Lpool=LPOOL, T=TDEN, enclosure_window=[JDEP, MDEP],
               transfer_window=[N, M, float(e)], rows={})
    xp, Hp = None, 0
    if '--resume' in sys.argv and os.path.exists(out):
        rec = json.load(open(out))
        done = sorted(H for H in map(int, rec['rows'])
                      if 'xstar' in rec['rows'][str(H)])
        have = sorted(map(int, rec['rows']))
        if done:
            Hp = done[-1]
            xp = np.array(rec['rows'][str(Hp)]['xstar'])
        print(f"# resumed from {out}: rows {have}, warm start at "
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
        ent, phi, rads, rep = [], [], [], []
        for x in pool_vectors(H, xstar):
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
            if not (np.isfinite(h_c) and np.isfinite(V).all()):
                continue
            ent.append(h_c)
            phi.append(V)
            rads.append(max(rad))
            rep.append(c.repair_cost)
        ent, phi = np.array(ent), np.array(phi)
        Vm = np.concatenate([phi[:, :H].real, phi[:, :H].imag], axis=1).T.copy()
        val, lam = lp_lower(ent, phi, H)
        tmm = maximin(Vm)
        m7u, m7l = M7.get(name, {}).get(H, (None, None))
        verdict = ("entropy LP infeasible" if val is None else f"lower {val:.6f}")
        print(f"H={H:<4} pool {len(ent):4d}  upper(optimiser) {P:.6f}  {verdict}"
              f"   maximin t = {('%.3e' % tmm) if tmm is not None else 'INFEASIBLE'}"
              f"   hull dist {hull_distance(phi, H):.1e}   radius {max(rads):.2e}"
              f"   {time.time() - t0:.0f}s", flush=True)
        if m7u is not None:
            print(f"       M7 sec 4 row: upper {m7u:.6f}  lower "
                  + (f"{m7l:.6f}" if m7l else "-- (pool too small)")
                  + ("   <<< M7 said POOL TOO SMALL; maximin says 0 is inside"
                     if m7l is None and tmm and tmm > 0 else ""), flush=True)
        rec['rows'][str(H)] = dict(
            n_pool=int(len(ent)), upper=float(P),
            lower=(None if val is None else float(val)),
            maximin_t=tmm, radius=float(max(rads)), repair=float(max(rep)),
            m7_upper=m7u, m7_lower=m7l, ent=[float(x) for x in ent],
            xstar=[float(v) for v in xstar],
            phi_re=[[float(z.real) for z in row] for row in phi],
            phi_im=[[float(z.imag) for z in row] for row in phi])
        with open(out, 'w') as f:
            json.dump(rec, f)
    print(f"# wrote {out}", flush=True)


if __name__ == '__main__':
    main()
