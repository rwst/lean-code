#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 6.1 -- independent check of the gap certificates.

Same sets, different method: an explicit sorted union of fattened intervals, no raster and
no FFT.  Agrees with m0_gaps.py on every case tested.
"""
from m0_engine import *
from m0_gaps import C_points, K_points
import numpy as np

def gap_intervals(al, M, MK):
    Cv, Cerr = C_points(al, M)
    Kv, Kerr = K_points(al, MK)
    e = Cerr + Kerr
    v = (Cv[:, None] - Kv[None, :]).ravel() % 1.0
    v = np.sort(v)
    lo = v - e; hi = v + e
    run = np.maximum.accumulate(hi)
    starts = np.concatenate([[True], lo[1:] > run[:-1]])
    idx = np.flatnonzero(starts)
    seg_lo = lo[idx]
    seg_hi = np.concatenate([run[idx[1:] - 1], [run[-1]]])
    gaps = seg_lo[1:] - seg_hi[:-1]
    wrap = (seg_lo[0] + 1.0) - seg_hi[-1]
    allg = list(zip(gaps, seg_hi[:-1])) + [(wrap, seg_hi[-1])]
    allg.sort(key=lambda z: -z[0])
    return allg, len(v), e

for coeffs, name, M, MK in [([1,-4,1], '2+sqrt3', 11, 9), ([1,-4,1], '2+sqrt3 (finer)', 13, 11),
                            ([1,-2,-1], '1+sqrt2', 12, 12), ([1,-3,-1], '(3+sqrt13)/2', 12, 11),
                            ([1,-3], 'alpha=3 (sanity)', 12, 1),
                            ([1,-5,-2], 'X^2-5X-2', 13, 11)]:
    al = Alpha(coeffs, name)
    g, n, e = gap_intervals(al, M, MK)
    print('%-18s alpha=%.6f  %8d intervals, half-width %.2e   largest gaps: %s'
          % (name, al.a, n, e, ', '.join('%.6f@%.4f' % (a, b) for a, b in g[:3] if a > 4 * e) or 'NONE'))
