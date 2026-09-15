#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 runner: the entropy-certificate coverage sweep, and the degree comparison
against the Fourier-only (Route D) certificate.  Writes m3_cert.json.

For every Pisot alpha of m0_gapsweep.json (the 42 candidates with rho<1/2, alpha<6.5,
degree 2-3) it records
  h_min, the budget log2 - h_min, the Bernoulli partial sums sum_{h<=H}|Phi_h|^2,
  E(H) = min_a P(psi_a) for H = 1..Hmax with the rigorous slack delta,
  the first H at which E(H)+delta < h_min (the entropy certificate fires),
  and the first H at which 0 leaves the convex hull of the periodic-orbit
  Fourier vectors (the Fourier certificate can fire).
"""
import sys, json, math, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, bern_phi, minimize_pressure, delta_bound
from m3_hull import pool, separate

NWIN = int(sys.argv[1]) if len(sys.argv) > 1 else 8
HLIST = [1, 2, 3, 4, 6, 8]
rows = json.load(open('m0_gapsweep.json'))
out = []
for r in rows:
    al = Alpha(r['coeffs'], r['poly'])
    a, rho = float(al.alpha), float(al.rho)
    hm = h_min(al)
    bud = math.log(2) - hm
    p = bern_phi(al, 4096)
    S = np.cumsum(p ** 2)
    rec = dict(poly=r['poly'], coeffs=r['coeffs'], d=r['d'], unit=bool(r['unit']),
               alpha=a, rho=rho, h_min=hm, budget=bud, gap=r['gap'],
               routeA=r['routeA'], S1=S[0], S4=S[3], S64=S[63], S4096=S[4095],
               E={}, fire_entropy=None, fire_fourier=None)
    if bud > 0:
        W = Window(al, NWIN, NWIN)
        rec['trunc'] = W.err
        x0 = None
        for H in HLIST:
            W.set_modes(list(range(1, H + 1)))
            t0 = time.time()
            P, x, res, dlt = minimize_pressure(W, x0=(np.concatenate([x0[:H-1], [0.], x0[H-1:], [0.]])
                                                      if x0 is not None and len(x0) == 2*(H-1) else None))
            x0 = x
            rec['E'][str(H)] = dict(P=P, delta=dlt, resid=res, secs=round(time.time()-t0, 1))
            if rec['fire_entropy'] is None and P + dlt < hm:
                rec['fire_entropy'] = H
                break
        del W
        Z = pool(al, list(range(1, 9)), periods=(10, 12, 14))
        for H in range(1, 9):
            ins, c, u, act = separate(Z[:, :H])
            if ins is False:
                rec['fire_fourier'] = H
                break
    out.append(rec)
    print('%-14s alpha=%.3f bud=%+.4f  entropy@H=%s  fourier@H=%s  E=%s' %
          (r['poly'], a, bud, rec['fire_entropy'], rec['fire_fourier'],
           {k: round(v['P'], 4) for k, v in rec['E'].items()}), flush=True)
json.dump(out, open('m3_cert.json', 'w'), indent=1)
print('wrote m3_cert.json')
