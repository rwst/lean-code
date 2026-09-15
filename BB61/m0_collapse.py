#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 10 -- the collapse of the Bernoulli bias constant as rho -> 1.

c_B(alpha) = max_{h<=2e4} |hat F_*mu_{1/2}(h)| over 150 Pisot alpha stratified by rho.
Median 1.5e-1 at rho < 0.5 and 2.1e-18 at rho > 0.95: there is no uniform-in-alpha constant.
"""
from m0_engine import *
from m0_scan import Phi_vec
import numpy as np, json, math, sys

rows = json.load(open('coverage.json'))
rows = [r for r in rows if r['rho'] < 0.97 and r['a'] < 6.0]
rng = np.random.default_rng(0)
# stratify by rho so the whole range is represented
rows.sort(key=lambda r: r['rho'])
sel = [rows[i] for i in np.linspace(0, len(rows) - 1, 150).astype(int)]
out = []
H = 20000
for k, r in enumerate(sel):
    al = Alpha(r['coeffs'])
    P = np.prod(Phi_vec(al, H, tol=1e-12), axis=0)
    i = int(np.argmax(P))
    out.append(dict(coeffs=r['coeffs'], poly=al.polystr(), alpha=al.a, rho=al.r, d=al.d,
                    unit=bool(al.unit), cB=float(P[i]), argmax=i + 1,
                    pred=float(2 ** (-math.log(max(P[i], 1e-300) and 1, 2)))))
    print('%3d %-22s a=%7.4f rho=%.4f d=%d  c_B=%.3e at h=%d' %
          (k, al.polystr(), al.a, al.r, al.d, P[i], i + 1), flush=True)
json.dump(out, open('collapse.json', 'w'))
