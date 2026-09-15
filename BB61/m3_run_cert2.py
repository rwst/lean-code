#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 runner, second pass: decide every alpha whose pressure already dips below
h_min(alpha) but whose truncation slack delta swamped the margin at N=M=8.

The multiplier vector a is a *certificate*, not something that has to be recomputed
at every window: once P(psi_a) < h_min for one admissible a, 10.61 holds at alpha
(note-1061-M3.html Theorem 12).  So this pass

  (A) recovers a* at N=M=8 exactly as m3_run_cert.py found it (cold L-BFGS at the
      best H), then
  (B) *evaluates* that same a* at N=M=10 and 12, where delta = 2 pi sum h|a_h| err
      is smaller by rho^2 and rho^4,

which is cheap: one transfer-operator solve per window instead of a full optimisation
in 2H variables over a 2^25-state operator.  Both the shallow and the deep numbers
use the Collatz-Wielandt bound `Window.pressure_ub`, so the certificate no longer
depends on the power iteration having converged.

Section (C) re-audits the rows that already fired in the first pass with the same
rigorous bound, and repairs any whose multipliers had run out of numerical range.
Reads m3_cert.json, writes m3_cert2.json.
"""
import sys, json, math, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure, delta_bound

WINDOWS = (10, 12)
HLIST = [1, 2, 3, 4, 6, 8]                 # the mode ladder m3_run_cert.py climbed


def pad(x, Hp, Hn):
    """Zero-pad a multiplier vector from Hp modes to Hn, for the warm start."""
    if x is None:
        return None
    z = np.zeros(Hn - Hp)
    return np.concatenate([x[:Hp], z, x[Hp:], z])
rows = json.load(open('m3_cert.json'))
out = dict(pending=[], audit=[], windows=list(WINDOWS))


def deep(al, a, H, hm, tag):
    """Evaluate the fixed certificate a at the deeper windows."""
    runs = []
    for n in WINDOWS:
        t0 = time.time()
        W = Window(al, n, n).set_modes(list(range(1, H + 1)))
        Pub = W.pressure_ub(a)
        dlt = delta_bound(W, a)
        ok = bool(Pub + dlt < hm)
        runs.append(dict(n=n, P_ub=Pub, delta=dlt, total=Pub + dlt, ok=ok,
                         err=W.err, secs=round(time.time() - t0, 1)))
        print('   %-14s n=%-3d P_ub=%.6f delta=%.2e  P_ub+delta=%.6f  h_min=%.6f  %s  %.0fs'
              % (tag, n, Pub, dlt, Pub + dlt, hm, 'PROVED' if ok else 'no',
                 time.time() - t0), flush=True)
        del W
        if ok and hm - (Pub + dlt) > 0.03:   # thin margins get confirmed one window deeper
            break
    return runs


# ---- (A)+(B) the five that delta blocked -----------------------------------
for r in rows:
    if not r['E'] or r['fire_entropy'] is not None:
        continue
    best = min(r['E'].items(), key=lambda kv: kv[1]['P'])
    if best[1]['P'] >= r['h_min']:
        continue
    H, hm = int(best[0]), r['h_min']
    al = Alpha(r['coeffs'], r['poly'])
    print('%-14s alpha=%.5f h_min=%.6f  H=%d  (pass 1: P=%.6f delta=%.4f)'
          % (r['poly'], r['alpha'], hm, H, best[1]['P'], best[1]['delta']), flush=True)
    t0 = time.time()
    W = Window(al, 8, 8).set_modes(list(range(1, H + 1)))
    P8, x, res, d8 = minimize_pressure(W)              # cold start: reproduces pass 1
    a = x[:H] + 1j * x[H:]
    P8ub = W.pressure_ub(a)
    print('   %-14s n=8   P=%.6f (pass 1 %.6f, drift %.1e)  P_ub=%.6f  |grad|=%.2e  %.0fs'
          % (r['poly'], P8, best[1]['P'], abs(P8 - best[1]['P']), P8ub, res,
             time.time() - t0), flush=True)
    del W
    rec = dict(poly=r['poly'], alpha=r['alpha'], unit=r['unit'], h_min=hm, gap=r['gap'],
               H=H, P8=P8, P8_pass1=best[1]['P'], P8_ub=P8ub, delta8=d8, resid8=res,
               a_re=list(x[:H]), a_im=list(x[H:]), runs=deep(al, a, H, hm, r['poly']))
    rec['fire_n'] = next((q['n'] for q in rec['runs'] if q['ok']), None)
    out['pending'].append(rec)
    json.dump(out, open('m3_cert2.json', 'w'), indent=1)

# ---- (C) re-audit of the rows that fired in pass 1 -------------------------
print('\n--- audit of pass-1 certificates (Collatz-Wielandt) ---', flush=True)
for r in rows:
    if r['fire_entropy'] is None:
        continue
    H, hm = r['fire_entropy'], r['h_min']
    al = Alpha(r['coeffs'], r['poly'])
    W = Window(al, 8, 8).set_modes(list(range(1, H + 1)))
    P8, x, res, d8 = minimize_pressure(W)
    a = x[:H] + 1j * x[H:]
    Pub = W.pressure_ub(a)
    sound = bool(Pub + d8 < hm)
    print('%-14s H=%-2d P=%.6f  P_ub=%.6f  delta=%.4f  P_ub+delta=%.6f  h_min=%.6f  %s'
          % (r['poly'], H, P8, Pub, d8, Pub + d8, hm,
             'sound' if sound else 'SPURIOUS (power iteration did not certify)'), flush=True)
    rec = dict(poly=r['poly'], alpha=r['alpha'], H=H, h_min=hm, P8=P8, P8_ub=Pub,
               delta8=d8, resid8=res, sound=sound, gap=r['gap'],
               a_re=list(x[:H]), a_im=list(x[H:]))
    if not sound:
        # Diagnosis: the cap=60 multiplier box let pass 1 walk into the regime where
        # exp(psi - max psi) underflows, so its reported P was an artefact of a power
        # iteration on a numerically singular operator.  Re-optimise warm-started from
        # H-1 modes inside a tight box, where the Collatz-Wielandt bound exists.
        rec['repair'] = []
        for cap in (4.0, 8.0, 20.0):
            xp, Hp = None, 0
            for Hq in [q for q in HLIST if q <= H]:      # pass 1's ladder, zero-padded
                W.set_modes(list(range(1, Hq + 1)))
                P, x, res, d8 = minimize_pressure(W, x0=pad(xp, Hp, Hq), cap=cap)
                xp, Hp = x, Hq
            a = x[:H] + 1j * x[H:]
            Pub = W.pressure_ub(a)
            sound = bool(Pub + d8 < hm)
            rec['repair'].append(dict(cap=cap, P=P, P_ub=Pub, delta=d8, ok=sound, resid=res))
            print('   repair cap=%-5.1f P=%.6f  P_ub=%.6f  delta=%.4f  P_ub+delta=%.6f  %s'
                  % (cap, P, Pub, d8, Pub + d8, 'PROVED' if sound else 'no'), flush=True)
            if sound:
                break
        rec.update(sound=sound, repaired=sound, P8=P, P8_ub=Pub, delta8=d8, resid8=res,
                   a_re=list(x[:H]), a_im=list(x[H:]))
        if not sound:
            rec['runs'] = deep(al, a, H, hm, r['poly'])
            rec['fire_n'] = next((q['n'] for q in rec['runs'] if q['ok']), None)
    del W
    out['audit'].append(rec)
    json.dump(out, open('m3_cert2.json', 'w'), indent=1)

n_ok = sum(1 for r in out['pending'] if r['fire_n'])
print('\nwrote m3_cert2.json;  %d/%d pending certified;  %d/%d pass-1 certificates sound'
      % (n_ok, len(out['pending']),
         sum(1 for r in out['audit'] if r['sound']), len(out['audit'])), flush=True)
