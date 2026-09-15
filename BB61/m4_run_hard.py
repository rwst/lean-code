#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4 task (ii): the two hard quadratic units the M4 row names by hand.

`m4_run_frontier.py` walks the 17 undecided units in order of M3's shortfall and was
stopped after six (see note-1061-M4.html sec 7.2): the cubics past that point are further
from the floor at H <= 8 than anything that fired, so continuing adds rows to a table and
nothing to the argument.  What it had not yet reached, and what the M4 row asks for by
name, are `(3+sqrt5)/2` and `1+sqrt2` -- two of the four quadratic units of M3 sec 8.2.
This runner does exactly those, with the same ladder and the same certification, and
appends the records to m4_frontier.json.

Only the best mode count is certified, but at all three depths, because the point of the
exercise is to separate the two possible obstructions: if Lambda barely moves as eps falls
by two orders of magnitude, the shortfall is the pressure and not the truncation.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min
from m4_fourier import search, certify, pad, best_window

LADDER = [4, 8, 16, 24, 32, 48, 64]
LSEARCH = 16
LDEEP = [20, 22, 24]
TARGETS = ['X^2-3X+1', 'X^2-2X-1']

gapd = {r['poly']: r for r in json.load(open('m0_gapsweep.json'))}
out = json.load(open('m4_frontier.json'))
have = {r['poly'] for r in out}

for name in TARGETS:
    if name in have:
        print('%s already recorded, skipping' % name, flush=True)
        continue
    r = gapd[name]
    al = Alpha(r['coeffs'], name)
    hm = h_min(al)
    a_, rho = float(al.alpha), float(al.rho)
    Ns, Ms, es = best_window(al, LSEARCH)
    wins = [best_window(al, L) for L in LDEEP]
    rec = dict(poly=name, coeffs=r['coeffs'], d=r['d'], alpha=a_, rho=rho, h_min=hm,
               budget=float(np.log(2)) - hm, routeA=r['routeA'],
               search_window=[Ns, Ms, es],
               deep_windows=[[L] + list(w) for L, w in zip(LDEEP, wins)],
               ladder={}, cert={}, fire_H=None, fire_L=None)
    print('%-14s alpha=%.5f rho=%.4f h_min=%.6f  search (%d,%d) eps=%.1e  deep %s'
          % (name, a_, rho, hm, Ns, Ms, es,
             ' '.join('(%d,%d):%.1e' % (w[0], w[1], w[2]) for w in wins)), flush=True)
    W = Window(al, Ns, Ms)
    xp, Hp, best = None, 0, {}
    for H in LADDER:
        W.set_modes(list(range(1, H + 1)))
        t0 = time.time()
        P, x, pen = search(W, wins[0][2], x0=pad(xp, Hp, H))
        xp, Hp = x, H
        best[H] = x.copy()
        s = float(np.sum(W.modes * np.abs(x[:H] + 1j * x[H:])))
        rec['ladder'][str(H)] = dict(P=P, sum_h_a=s, surrogate=P + pen,
                                     secs=round(time.time() - t0, 1))
        print('   H=%-3d P~=%.6f  sum h|a|=%7.1f  surrogate=%.6f  (floor %.6f)  %.0fs'
              % (H, P, s, P + pen, hm, time.time() - t0), flush=True)
    del W
    Hbest = min(best, key=lambda H: rec['ladder'][str(H)]['surrogate'])
    for L, (N, M, e) in zip(LDEEP, wins):
        W = Window(al, N, M).set_modes(list(range(1, Hbest + 1)))
        x = best[Hbest]
        t0 = time.time()
        c = certify(W, x[:Hbest] + 1j * x[Hbest:])
        ok = bool(c < hm)
        rec['cert']['%d/%d' % (L, Hbest)] = dict(Lambda_ub=c, ok=ok, N=N, M=M, eps=e,
                                                 secs=round(time.time() - t0, 1))
        print('   CERT L=%-3d (%d,%d) H=%-3d eps=%.1e Lambda_ub=%.6f  %s  %.0fs'
              % (L, N, M, Hbest, e, c, 'FIRES' if ok else '-', time.time() - t0), flush=True)
        del W
        if ok:
            rec.update(fire_H=Hbest, fire_L=L, a_re=list(x[:Hbest]), a_im=list(x[Hbest:]))
            break
    out.append(rec)
    json.dump(out, open('m4_frontier.json', 'w'), indent=1)

print('\nm4_frontier.json now holds %d records; %d certified'
      % (len(out), sum(1 for r in out if r['fire_L'])), flush=True)
