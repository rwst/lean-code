#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7 runner: finish the frontier sweep M4 stopped.

M4 examined 7 of the 17 undecided Pisot *units* of `m0_gapsweep.json` and certified 2
of them (note-1061-M4.html sec 7.2: "This is a stopping decision, not a theorem" --
the remaining ten were left as a bounded piece of compute).  This runs those ten,
with M4's own machine and M4's own parameters, so the rows are directly comparable:

  * search the multiplier vector at the *balanced* shallow window L = 16, minimising
    the certifiable surrogate P~ + 2 pi (sum_h h|a_h|) eps_target (m4_fourier.search);
  * warm-start up the mode ladder 4, 8, 16, 24, 32, 48, 64;
  * certify the three best vectors with the word-wise interval enclosure at the
    balanced deep windows L = 20, 22, 24 (m4_fourier.certify), which carries no delta.

A row FIRES when the certified Lambda is below h_min(alpha): by M3 Thm 12 that proves
Problem 10.61 at that alpha.  Writes m7_frontier.json.
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
HOPELESS = 0.20

rows = json.load(open('m0_gapsweep.json'))
done = {r['poly'] for r in json.load(open('m4_frontier.json'))}
live = [r for r in rows if not r['gap'] and r['routeA'] >= 1.0 and r['unit']]
todo = [r for r in live if r['poly'] not in done]
m3 = {r['poly']: r for r in json.load(open('m3_cert.json'))}


def head(r):
    e = (m3.get(r['poly']) or {}).get('E') or {}
    return min([v['P'] for v in e.values()], default=1.0) - m3[r['poly']]['h_min']


print('live units %d; M4 examined %d; M7 runs %d'
      % (len(live), len(live) - len(todo), len(todo)), flush=True)

out = []
for r in sorted(todo, key=head):
    al = Alpha(r['coeffs'], r['poly'])
    hm = h_min(al)
    a_, rho = float(al.alpha), float(al.rho)
    Ns, Ms, es = best_window(al, LSEARCH)
    wins = [best_window(al, L) for L in LDEEP]
    rec = dict(poly=r['poly'], coeffs=r['coeffs'], d=r['d'], alpha=a_, rho=rho,
               h_min=hm, budget=float(np.log(2)) - hm, routeA=r['routeA'],
               m3_shortfall=head(r), search_window=[Ns, Ms, es],
               deep_windows=[[L] + list(w) for L, w in zip(LDEEP, wins)],
               ladder={}, cert={}, fire_H=None, fire_L=None)
    print('%-14s alpha=%.5f rho=%.4f h_min=%.6f  search (%d,%d) eps=%.1e  deep %s'
          % (r['poly'], a_, rho, hm, Ns, Ms, es,
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
        if H >= 32 and P - hm > HOPELESS:
            print('   -> stop: %.3f above the floor at H=%d' % (P - hm, H), flush=True)
            break
    del W
    order = sorted(best, key=lambda H: rec['ladder'][str(H)]['surrogate'])
    for L, (N, M, e) in zip(LDEEP, wins):
        if rec['fire_L']:
            break
        W = Window(al, N, M)
        for H in order[:3]:
            W.set_modes(list(range(1, H + 1)))
            x = best[H]
            t0 = time.time()
            c = certify(W, x[:H] + 1j * x[H:])
            ok = bool(c < hm)
            rec['cert']['%d/%d' % (L, H)] = dict(Lambda_ub=c, ok=ok, N=N, M=M, eps=e,
                                                 secs=round(time.time() - t0, 1))
            print('   CERT L=%-3d (%d,%d) H=%-3d Lambda_ub=%.6f  %s  %.0fs'
                  % (L, N, M, H, c, 'FIRES' if ok else '-', time.time() - t0), flush=True)
            if ok:
                rec.update(fire_H=H, fire_L=L, a_re=list(x[:H]), a_im=list(x[H:]))
                break
        del W
    out.append(rec)
    json.dump(out, open('m7_frontier.json', 'w'), indent=1)

n_fire = sum(1 for r in out if r['fire_L'])
print('\nwrote m7_frontier.json;  %d/%d newly certified' % (n_fire, len(out)), flush=True)
for r in out:
    if r['fire_L']:
        print('   %-14s alpha=%.4f  H=%d at L=%d' % (r['poly'], r['alpha'], r['fire_H'], r['fire_L']))
