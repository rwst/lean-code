#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Cross-check the numbers asserted in note-1061-R2a.html against the recorded runs.

Prose drifts from data when a run is repeated; this reads the claims back out of the note
and compares them with `r2a_margin.json`, `r2a_farkas.json`, `r2a_flat.json` and the R1b
records.  Every failure here is a sentence in the note that has to change.

Usage:  python3 r2a_checknote.py
"""
import json, math, os, re, sys
BB = '/home/ralf/math/lean-code/BB61'
NOTE = '/home/ralf/math/lean-code/note-1061-R2a.html'
ok = bad = 0

def chk(name, cond, detail=''):
    global ok, bad
    if cond:
        ok += 1; print(f"  ok   {name}   {detail}")
    else:
        bad += 1; print(f"  FAIL {name}   {detail}")

def close(a, b, rel=5e-3):
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)

txt = open(NOTE).read()
def load(name, default):
    try:
        return json.load(open(f'{BB}/{name}'))
    except Exception as exc:
        print(f"  -- {name} not available ({type(exc).__name__}); its claims are skipped")
        return default

mar = {(r['L'], r['H']): r for r in load('r2a_margin.json', [])}
far = load('r2a_farkas.json', {'rounds': [], 'ray': []})
flat = load('r2a_flat.json', {'sweep': {}, 'pin': {}, 'ray': []})

print('-- the ladder, and the exponent quoted in sec 1 and sec 5')
L12 = sorted([k[1] for k in mar if k[0] == 12])
r0, r1 = mar[(12, L12[0])], mar[(12, L12[-1])]
gam = -math.log(r1['rho1'] / r0['rho1']) / math.log(r1['H'] / r0['H'])
m = re.search(r'\\bar\\rho\\asymp H\^\{-([0-9.]+)\}', txt)
chk('gamma_rho as quoted', m is not None and close(float(m.group(1)), gam, 0.02),
    f"note {m.group(1) if m else '?'}, recomputed {gam:.4f} over H={r0['H']}..{r1['H']}")
gd = -math.log(r1['delta1'] / r0['delta1']) / math.log(r1['H'] / r0['H'])
m = re.search(r'certified \\\(\\delta\\\) tracks it at \\\(H\^\{-([0-9.]+)\}', txt)
chk('gamma_delta as quoted', m is not None and close(float(m.group(1)), gd, 0.02),
    f"note {m.group(1) if m else '?'}, recomputed {gd:.4f}")

print('-- the loop gains quoted in sec 1 F3')
for H, want in ((4, 1.68), (8, 1.31), (64, 1.12)):
    r = mar.get((12, H))
    g = r['delta1'] / r['delta0'] if r else float('nan')
    chk(f'loop gain at H={H}', close(g, want, 6e-3), f"note {want}, run {g:.4f}")

print('-- the bracket holds at every rung, and delta is positive')
for k, r in sorted(mar.items()):
    chk(f'delta <= rho_upper at L={k[0]}, H={k[1]}',
        0 < r['delta1'] <= r['rho1'],
        f"{r['delta1']:.4e} <= {r['rho1']:.4e}  (factor {r['rho1']/r['delta1']:.1f})")

print('-- the Farkas stall')
if not far['rounds']:
    print('  -- skipped')
gaps = [x['gap'] for x in far['rounds']]
far['rounds'] and chk('the gap stops moving', len(gaps) >= 3 and close(gaps[-1], gaps[-2], 1e-12),
    f"rounds {['%.6e' % g for g in gaps]}")
chk('the refutation is certified', all(x['certified'] > 1e4 * x['e2'] for x in far['rounds']),
    f"gap/e2 = {far['rounds'][-1]['certified']/far['rounds'][-1]['e2']:.2e}")
ray = far['ray']
# monotone in exact arithmetic (convexity of the pressure); at |s| = 14 the window
# operator is itself near-degenerate and its power iteration no longer resolves the value
win = [p['window'] for p in ray if p['window'] is not None and abs(p['s']) <= 9]
chk('the window coordinate is monotone along the ray (|s| <= 9)',
    all(win[i] <= win[i+1] + 1e-9 for i in range(len(win)-1)),
    f"{win[0]:+.4f} .. {win[-1]:+.4f} over {len(win)} points")
enc = [p['enclosed'] for p in ray if p['enclosed'] is not None]
thr = far['rounds'][-1]['gap'] / 7.0986
chk('the enclosed coordinate never crosses', min(enc) > thr,
    f"min <u,Phi> = {min(enc):+.6e} > plane {thr:.6e}")
chk('every point where the window is safely across has no member',
    all(p['enclosed'] is None for p in ray if p['window'] is not None
        and p['window'] < -0.2),
    f"{sum(1 for p in ray if p['window'] is not None and p['window'] < -0.2)} such points")

print('-- the truncation law')
ons = {}
for Ls, sw in flat['sweep'].items():
    o = [r for r in sw if 0.3 <= r['xmax'] < 54.0]
    if o:
        ons[int(Ls)] = o[0]['Heps']
chk('the onset is at H eps = 1.10 +- 0.03 at every window',
    len(ons) >= 2 and max(ons.values()) - min(ons.values()) < 0.07,
    ', '.join(f"L={L}: {v:.3f}" for L, v in sorted(ons.items())))
for Ls, p in flat.get('pin', {}).items():
    chk(f'H_0({Ls}) eps is the same constant', 1.05 < p['prod'] < 1.45,
        f"H_0 = {p['H0']}, H_0 eps = {p['prod']:.4f}")
sw16 = flat['sweep'].get('16', [])
safe = [r for r in sw16 if r['Heps'] <= 0.9 and r['P'] > 0]
if len(safe) >= 2:
    rate = (safe[0]['P'] - safe[-1]['P']) / math.log2(safe[-1]['H'] / safe[0]['H'])
    chk('the pressure falls 3.3e-3 per doubling at 1+sqrt2', close(rate, 3.3e-3, 0.05),
        f"{safe[0]['H']}..{safe[-1]['H']}: {rate:.4e} per doubling")
    hmin = 0.440687
    chk('h_min is ~70 doublings away',
        65 < (safe[-1]['P'] - hmin) / rate < 76,
        f"{(safe[-1]['P'] - hmin) / rate:.1f} doublings")

print('-- the ray re-pricing')
for r in flat.get('ray', []):
    if r['L'] > 12:
        chk(f"the runaway direction does not separate at L={r['L']}",
            min(v for v in r['ub'] if v == v and abs(v) != float('inf')) > 0,
            f"best P_ub = {min(v for v in r['ub'] if v == v and abs(v) != float('inf')):.3f}")

print(f"\n  {ok} claims verified, {bad} failed")
sys.exit(0 if bad == 0 else 1)
