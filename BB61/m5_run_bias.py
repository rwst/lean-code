#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5: the bias table.  For each of the 42 candidates of m0_gapsweep.json, the
Bernoulli(1/2) Weyl limit |G_{1/2}(h)| for h <= HMAX, its maximum, the resulting
discrepancy floor, the p-window on which M3's entropy floor does NOT already kill the
Bernoulli measures, and the Theorem-C non-vanishing audit.  Writes m5_bias.json.
"""
import json, time
import mpmath as mp
from m0_engine import Alpha
import m5_bernoulli as B

mp.mp.dps = 50
HMAX = 64
PS = ['0.5', '0.4', '0.3', '0.2', '0.1']

rows = json.load(open('m0_gapsweep.json'))
out = []
t0 = time.time()
for r in rows:
    al = Alpha(r['coeffs'], r['poly'])
    half = mp.mpf('0.5')
    prof = [float(B.modulus(al, h, half)) for h in range(1, HMAX + 1)]
    hb = int(max(range(HMAX), key=lambda i: prof[i])) + 1
    w = B.weyl(al, hb, half)
    w1 = B.weyl(al, 1, half)
    # non-vanishing audit: smallest factor over all h <= HMAX, and the finite
    # half-integer candidate list of Theorem C for the future ladder
    worst = (mp.mpf(2), None, None)
    for h in range(1, HMAX + 1):
        J, M = B.depths(al, h, half)
        ww = B.weyl(al, h, half, J=J, M=M)
        if ww['minfac'] < worst[0]:
            worst = (ww['minfac'], h, ww['where'])
    cand = B.future_halfinteger_candidates(al, 1)
    ew = B.entropy_window(al) if r['unit'] else None
    rec = dict(poly=r['poly'], coeffs=r['coeffs'], d=r['d'], unit=r['unit'],
               alpha=float(al.alpha), rho=float(al.rho), norm=int(r['coeffs'][-1]),
               profile=prof, h_best=hb,
               G_best=float(w['abs']), G_best_lo=float(w['lo']),
               G_1=float(w1['abs']), G_1_lo=float(w1['lo']),
               disc_floor=float(B.discrepancy_floor(al, hb, half)),
               minfac=float(worst[0]), minfac_h=worst[1],
               minfac_where=[worst[2][0], worst[2][1]] if worst[2] else None,
               halfint_candidates=[[j, float(v)] for j, v in cand],
               h_min=float(B.h_min(al)) if r['unit'] else None,
               p_window=[float(ew[0]), float(ew[1])] if ew else None,
               subsumed_by_M3=(ew is None) if r['unit'] else None)
    for ps in PS[1:]:
        rec['G_1_p' + ps] = float(B.modulus(al, 1, mp.mpf(ps)))
    out.append(rec)
    print('%-16s a=%.5f N=%+d  |G(1)|=%.6e  best h=%-3d |G|=%.6e  minfac=%.4f  '
          'window=%s' % (r['poly'], al.alpha, rec['norm'], rec['G_1'], hb,
                         rec['G_best'], rec['minfac'],
                         'none (M3 subsumes)' if rec['subsumed_by_M3'] else
                         ('%.3f..%.3f' % tuple(rec['p_window'])) if rec['p_window'] else '-'),
          flush=True)

json.dump(out, open('m5_bias.json', 'w'), indent=1)
print('\n%d rows, %.0fs -> m5_bias.json' % (len(out), time.time() - t0))
