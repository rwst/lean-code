#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M4 runner: the frontier sweep.

M0's X8 raster decided 22 of the 42 Pisot alpha of `m0_gapsweep.json` by a confinement
gap, Route A decides 6 (all of them among those 22), and M3's entropy criterion at
H <= 8 decided 10 (again all among the 22).  So exactly **20 alpha are undecided**, and
those -- not the 42 -- are M4's target: three are non-units, where Theorem 11's entropy
floor does not apply (M-bar is only an endomorphism), leaving **17 live alpha**.

For each, climb a warm-started mode ladder at the *shallow* window N = M = 8, minimising
the certifiable surrogate (m4_fourier.search), then certify the winner at N = M = 10 and
12 with the word-wise interval enclosure (m4_fourier.certify), which carries no delta.
Search shallow, certify deep: an optimisation over 2H variables at a 2^25-state operator
is unaffordable, a single evaluation of a fixed multiplier vector is not.

Writes m4_frontier.json.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min
from m4_fourier import search, certify, pad, best_window

LADDER = [4, 8, 16, 24, 32, 48, 64]
LSEARCH = 16               # window length for the search: 2^16 states
LDEEP = [20, 22, 24]       # window lengths for the certification
HOPELESS = 0.20            # stop climbing when even H=32 is this far from the floor

rows = json.load(open('m0_gapsweep.json'))
targets = [r for r in rows if not r['gap'] and r['routeA'] >= 1.0]
live = [r for r in targets if r['unit']]
# most promising first, so the decisive alpha are reached early: M3's best E minus the floor
m3 = {r['poly']: r for r in json.load(open('m3_cert.json'))}
def head(r):
    e = (m3.get(r['poly']) or {}).get('E') or {}
    return min([v['P'] for v in e.values()], default=1.0) - m3[r['poly']]['h_min']
print('undecided: %d   of which units (in scope for Thm 11): %d'
      % (len(targets), len(live)), flush=True)

out = []
for r in sorted(live, key=head):
    al = Alpha(r['coeffs'], r['poly'])
    hm = h_min(al)
    a_, rho = float(al.alpha), float(al.rho)
    Ns, Ms, es = best_window(al, LSEARCH)
    wins = [best_window(al, L) for L in LDEEP]
    rec = dict(poly=r['poly'], coeffs=r['coeffs'], d=r['d'], alpha=a_, rho=rho,
               h_min=hm, budget=float(np.log(2)) - hm, routeA=r['routeA'],
               search_window=[Ns, Ms, es],
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
    # certify the shallow winners at the deeper windows
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
    json.dump(out, open('m4_frontier.json', 'w'), indent=1)

n_fire = sum(1 for r in out if r['fire_L'])
print('\nwrote m4_frontier.json;  %d/%d of the undecided units certified' % (n_fire, len(out)),
      flush=True)
for r in out:
    if r['fire_L']:
        print('   %-14s alpha=%.4f  H=%d at L=%d' % (r['poly'], r['alpha'], r['fire_H'], r['fire_L']))
