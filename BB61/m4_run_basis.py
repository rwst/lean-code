#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4: is the Fourier basis the wrong basis?

M3 sec 9.2 priced every *Fourier* route at exp(budget / c_alpha), the constant c_alpha
coming from S(H) = sum_{h<=H} |Phi_h(Bernoulli)|^2, which grows only logarithmically
because the bias of F_*mu sits on lacunary trace ladders.  The natural hope is that this
is an artefact of the basis: F_*mu is *far* from Lebesgue in total variation (M0's
X(alpha) is a Cantor-like set) while being *close* in Fourier -- that is exactly the
non-Rajchman phenomenon -- so a partition potential, whose dual norm is total variation,
should be enormously cheaper.

This script tests that hope at matched free-parameter count: a Fourier truncation at H
has 2H real parameters, a partition into B cells has B - 1 (the constraint is prod v = 1).
So E_fourier(H) is compared with E_partition(2H+1).

Writes m4_basis.json.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure, bern_phi
from m4_step import Cells, E

HS = [1, 2, 4, 8, 16]
NAMES = ['X^2-2X-1', 'X^2-3X+1', 'X^2-3X-1', 'X^2-4X+1', 'X^3-4X^2-3X-1']
NWIN = 8

rows = {r['poly']: r for r in json.load(open('m0_gapsweep.json'))}
out = []
for name in NAMES:
    r = rows[name]
    al = Alpha(r['coeffs'], name)
    hm = h_min(al)
    W = Window(al, NWIN, NWIN)
    rec = dict(poly=name, alpha=float(al.alpha), rho=float(al.rho), h_min=hm,
               err=W.err, gap=r['gap'], fourier={}, partition={})
    print('%-14s alpha=%.5f h_min=%.6f eps=%.2e  gap=%s'
          % (name, float(al.alpha), hm, W.err, round(r['gap'], 5)), flush=True)
    xp = None
    for H in HS:
        W.set_modes(list(range(1, H + 1)))
        x0 = None
        if xp is not None and len(xp) == H:                 # H doubles each step
            x0 = np.concatenate([xp[:H // 2], np.zeros(H // 2),
                                 xp[H // 2:], np.zeros(H // 2)])
        t0 = time.time()
        P, x, res, d = minimize_pressure(W, x0=x0, cap=8.0)
        xp = x
        rec['fourier'][str(H)] = dict(P=P, params=2 * H, secs=round(time.time() - t0, 1))
        print('   fourier H=%-3d params=%-3d E=%.6f  gain=%.6f  %.0fs'
              % (H, 2 * H, P, np.log(2) - P, time.time() - t0), flush=True)
    for H in HS:
        B = 2 * H + 1
        if 2 * W.err * B >= 1:
            print('   partition B=%-3d skipped (window too shallow)' % B, flush=True)
            continue
        c = Cells(W, B)
        t0 = time.time()
        for cap in (3.0, 6.0, 12.0):
            G, x, g, ub = E(c, cap=cap)
            if np.isfinite(ub):
                break
        rec['partition'][str(B)] = dict(E=G, ub=ub, params=B - 1, split=c.split,
                                        secs=round(time.time() - t0, 1))
        print('   partit  B=%-3d params=%-3d E=%.6f  ub=%.6f  gain=%.6f  split=%.3f  %.0fs'
              % (B, B - 1, G, ub, np.log(2) - ub, c.split, time.time() - t0), flush=True)
    # the two dual norms, measured at the maximal-entropy measure
    p = bern_phi(al, 4096)
    rec['S'] = {str(H): float(np.sum(p[:H] ** 2)) for H in HS}
    out.append(rec)
    del W
    json.dump(out, open('m4_basis.json', 'w'), indent=1)

print('\nwrote m4_basis.json', flush=True)
print('%-14s %-6s %-10s %-10s %s' % ('alpha', 'params', 'fourier', 'partition', 'winner'))
for rec in out:
    for H in HS:
        B = 2 * H + 1
        f = rec['fourier'].get(str(H))
        q = rec['partition'].get(str(B))
        if f and q:
            print('%-14s %-6d %-10.6f %-10.6f %s'
                  % (rec['poly'], 2 * H, f['P'], q['ub'],
                     'fourier' if f['P'] < q['ub'] else 'partition'))
