#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 8 -- the histogram figures of note-1061-M0.html.

Emits the SVG path fragments embedded in the note: full support at 1+sqrt2, two visible
gaps at 2+sqrt3 matching the sec 6 certificate.
"""
from m0_engine import *
import numpy as np

def svg_hist(al, N=3000000, B=360, W=560, H=120, seed=3):
    rng = np.random.default_rng(seed)
    eps = rng.integers(0, 2, N + 400)
    x = orbit(al, eps, L=400)
    c, _ = np.histogram(x, bins=B, range=(0, 1))
    f = c / c.sum() * B
    top = max(2.0, float(f.max()) * 1.05)
    bw = W / B
    d = []
    for i, v in enumerate(f):
        h = min(v, top) / top * H
        if h > 0: d.append('M%.2f %.2f v%.2f' % (i * bw + bw / 2, H, -h))
    zero_runs = []
    run = 0
    for i, v in enumerate(np.concatenate([c, c[:1]])):
        if v == 0: run += 1
        else:
            if run: zero_runs.append((i - run, run))
            run = 0
    return ' '.join(d), top, sorted(zero_runs, key=lambda z: -z[1])[:3], B, W, H, bw

for coeffs, name in [([1,-2,-1],'1+sqrt2'), ([1,-4,1],'2+sqrt3')]:
    al = Alpha(coeffs, name)
    d, top, zr, B, W, H, bw = svg_hist(al)
    print('### %s  alpha=%.5f  ymax=%.3f  biggest empty runs (bin,len): %s' % (name, al.a, top, zr))
    open('hist_%s.svgfrag' % name.replace('+', '').replace('√', 's'), 'w').write(
        '<path d="%s"/>' % d)
    print('   path length', len(d))
