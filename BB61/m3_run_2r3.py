#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3: the entropy certificate at alpha = 2+sqrt3, verified at three window depths."""
import sys, json, math
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure, delta_bound, bern_phi

al = Alpha([1, -4, 1], '2+sqrt3')
hm = h_min(al)
print('alpha=%.9f rho=%.9f  h_min=%.9f  log2=%.9f  Bernoulli |Phi_1|=%.6f'
      % (float(al.alpha), float(al.rho), hm, math.log(2), bern_phi(al, 1)[0]))
rec = dict(alpha=float(al.alpha), h_min=hm, log2=math.log(2), runs=[])
x0 = None
for n in (8, 9, 10, 11):
    W = Window(al, n, n).set_modes([1])
    P, x, res, dlt = minimize_pressure(W, x0=x0)
    x0 = x
    a = x[0] + 1j * x[1]
    print('n=%-3d  a_1 = %+.6f %+.6fi   P = %.9f   delta = %.2e   P+delta = %.9f  %s  margin %.6f'
          % (n, a.real, a.imag, P, dlt, P + dlt, 'PROVED' if P + dlt < hm else 'no', hm - P - dlt))
    rec['runs'].append(dict(n=n, a_re=float(a.real), a_im=float(a.imag), P=P, delta=dlt,
                            margin=hm - P - dlt, err=W.err, resid=res))
    del W
# a clean rational multiplier, verified at the deepest window
W = Window(al, 11, 11).set_modes([1])
for aa in (-2.25 + 0j, -2.3 + 0j, -2.0 + 0j, -2.5 + 0j):
    P, _ = W.pressure(np.array([aa]), want_grad=False)
    d = delta_bound(W, np.array([aa]))
    print('   rational a_1 = %-8s P = %.9f  delta = %.2e  P+delta = %.9f  %s'
          % (aa.real, P, d, P + d, 'PROVED' if P + d < hm else 'no'))
    rec.setdefault('rational', []).append(dict(a=float(aa.real), P=P, delta=d, ok=bool(P + d < hm)))
json.dump(rec, open('m3_2r3.json', 'w'), indent=1)
print('wrote m3_2r3.json')
