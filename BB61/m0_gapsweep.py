#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 6.2 -- the gap certificate run over every Pisot alpha with rho < 1/2, alpha < 6.5.

22 of 42 carry a certified gap; 16 of those are not covered by Route A.  The smallest is
alpha = 2 + sqrt 3.  Reads m0_coverage.json, writes m0_gapsweep.json.
"""
from m0_engine import *
from m0_gaps import support_gaps
import json, numpy as np

rows = json.load(open('coverage.json'))
sel = [r for r in rows if r['rho'] < 0.5 and r['a'] < 6.5]
sel.sort(key=lambda r: (r['d'], r['a']))
print('candidates with rho<1/2 and alpha<6.5 :', len(sel))
out = []
for r in sel:
    al = Alpha(r['coeffs'])
    try:
        g, MK, pos = support_gaps(al, G=1 << 21, maxpts=1 << 21)
    except Exception as e:
        g, MK, pos = None, -1, None
    out.append(dict(coeffs=r['coeffs'], poly=al.polystr(), alpha=al.a, rho=al.r, d=al.d,
                    unit=bool(al.unit), gap=g, pos=pos, routeA=r['A'], D=r['D'], g1=r['g']))
    print('%-24s a=%8.5f rho=%.4f d=%d  gap=%-9s routeA=%.4f  %s' %
          (al.polystr(), al.a, al.r, al.d, ('%.5f' % g) if g is not None else 'n/a', r['A'],
           'ROUTE-A' if r['A'] < 1 else ''), flush=True)
    json.dump(out, open('gapsweep.json', 'w'))
