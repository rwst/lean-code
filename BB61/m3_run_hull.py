#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 runner: how far the Fourier-only (Route D / Route B) certificate is from firing.

For each alpha it finds, for growing H, an invariant measure -- an explicit convex
combination of periodic orbits of period <= 18 -- with Phi_h = 0 for all h <= H.
Such a measure is a rigorous obstruction: no trigonometric certificate of degree <= H
exists at that alpha.  Writes m3_hull.json.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_hull import pool, separate, witness, interior_radius

CASES = [([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'),
         ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3')]
HS = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
out = []
for coeffs, name in CASES:
    al = Alpha(coeffs, name)
    rec = dict(name=name, coeffs=coeffs, alpha=float(al.alpha), rho=float(al.rho), H={})
    for H in HS:
        t0 = time.time()
        modes = list(range(1, H + 1))
        Z = pool(al, modes, periods=(10, 12, 14, 16, 18), per_period=max(1200, 8 * H), seed=5)
        lam = witness(Z)
        if lam is None:
            ins, c, u, act = separate(Z)
            rec['H'][str(H)] = dict(inside=False, margin=c, secs=round(time.time() - t0, 1))
            print('%-13s H=%-4d OUT margin=%.5f  %.0fs' % (name, H, c, time.time() - t0), flush=True)
            break
        res = float(np.abs((lam[:, None] * Z).sum(axis=0)).max())
        inter = interior_radius(Z[:, :min(H, 12)], 1e-3) if H <= 24 else None
        rec['H'][str(H)] = dict(inside=True, atoms=int((lam > 1e-12).sum()), resid=res,
                                pool=int(Z.shape[0]), interior_1e3=inter,
                                secs=round(time.time() - t0, 1))
        print('%-13s H=%-4d IN  atoms=%-4d resid=%.1e pool=%d interior=%s  %.0fs'
              % (name, H, (lam > 1e-12).sum(), res, Z.shape[0], inter, time.time() - t0), flush=True)
    out.append(rec)
json.dump(out, open('m3_hull.json', 'w'), indent=1)
print('wrote m3_hull.json')
