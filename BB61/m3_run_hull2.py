#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3: deeper hull search at (3+sqrt5)/2 -- larger orbit pool, longer periods."""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_hull import pool, witness, separate
al = Alpha([1, -3, 1], '(3+sqrt5)/2')
out = {}
for H in (128, 160, 192, 256):
    t0 = time.time()
    Z = pool(al, list(range(1, H + 1)), periods=(10, 12, 14, 16, 18, 20, 22), per_period=60 * H, seed=11)
    lam = witness(Z)
    if lam is None:
        ins, c, u, act = separate(Z)
        out[H] = dict(inside=False, margin=c, pool=int(Z.shape[0]))
        print('H=%-4d OUT margin=%.5f pool=%d  %.0fs' % (H, c, Z.shape[0], time.time() - t0), flush=True)
    else:
        res = float(np.abs((lam[:, None] * Z).sum(axis=0)).max())
        out[H] = dict(inside=True, atoms=int((lam > 1e-12).sum()), resid=res, pool=int(Z.shape[0]))
        print('H=%-4d IN atoms=%d resid=%.1e pool=%d  %.0fs'
              % (H, (lam > 1e-12).sum(), res, Z.shape[0], time.time() - t0), flush=True)
json.dump(out, open('m3_hull2.json', 'w'), indent=1)
print('wrote m3_hull2.json')
