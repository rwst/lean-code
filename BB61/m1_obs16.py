#!/usr/bin/env python3
"""M1 Observation 16, checked at adaptive precision.

The note's (i) -- "along a ladder the future factor and the past factor of the
Bernoulli(1/2) Weyl limit converge to the same value L" -- is two different phenomena:

  * at a quadratic unit of norm +1 the two factors are EQUAL at every rung k (the past
    ladder is the future ladder shifted by one, M5 Thm 7), so no limit is involved;
  * at a quadratic unit of norm -1 a limit is genuinely involved and |future - past|
    decays by exactly rho^2 per rung -- the rate proved in BB61/Plateau.lean
    (`abs_future_band`, `abs_past_band`).

At non-units the past factor collapses to 0 while the future factor settles.

Double precision is useless here: h_k ~ alpha^k, so evaluating h_k (alpha-1) alpha^{-j}
needs about k*log10(alpha) guard digits (the note's F10 trap).  Everything below is
mpmath at precision set from k, with exact integer ladders.

Writes m1_obs16.json.
"""
import json
import math
from mpmath import mp, mpf, sqrt, cos, pi, log

FUT = 'future'
PAST = 'past'


def factors(a, b, kmax, tol=mpf('1e-40')):
    """(alpha, rho, [(k, future, past)]) for the trace ladder h_k = Tr(alpha^k)."""
    disc = a * a + 4 * b
    al0 = (a + math.sqrt(disc)) / 2.0
    mp.dps = int(60 + 2 * kmax * math.log10(al0))
    al = (mpf(a) + sqrt(mpf(disc))) / 2
    be = (mpf(a) - sqrt(mpf(disc))) / 2
    rho = abs(be)
    h = [2, a]                                   # exact integers
    for _ in range(2, kmax + 1):
        h.append(a * h[-1] + b * h[-2])
    rows = []
    for k in range(6, kmax + 1, 4):
        H = h[k]
        J = int(float(log(mpf(abs(H)) * abs(al - 1) / tol) / log(al))) + 5
        f = mpf(1)
        for j in range(1, J + 1):
            f *= abs(cos(pi * H * (al - 1) / al**j))
        M = int(float(log(mpf(abs(H)) * abs(be - 1) / tol) / log(1 / rho))) + 5
        p = mpf(1)
        for m in range(0, M + 1):
            p *= abs(cos(pi * H * (be - 1) * be**m))
        rows.append((k, f, p))
    return al, rho, rows


CASES = [
    # (a, b, label);  X^2 - aX - b,  norm N(alpha) = alpha*beta = -b
    (2,  1, '1+sqrt2'),
    (3,  1, '(3+sqrt13)/2'),
    (5,  1, '(5+sqrt29)/2'),
    (1,  1, 'golden'),
    (4, -1, '2+sqrt3'),
    (6, -1, '3+2sqrt2'),
    (7, -1, 'X^2-7X+1'),
    (5, -2, 'NON-UNIT X^2-5X+2'),
    (4, -2, 'NON-UNIT X^2-4X+2'),
]

KMAX = 30
out = []
print('%-22s %5s %8s %16s %16s %11s %9s'
      % ('alpha', 'norm', 'k', 'future', 'past', '|f-p|', 'ratio/rho^2'))
for a, b, label in CASES:
    al, rho, rows = factors(a, b, KMAX)
    norm = -b
    unit = abs(b) == 1
    prev = None
    rec = dict(label=label, a=a, b=b, norm=norm, unit=unit,
               alpha=float(al), rho=float(rho), rows=[])
    for k, f, p in rows:
        d = abs(f - p)
        # |f-p| should fall by rho^(2*4) = rho^8 over the four-step grid
        r = float(d / prev / rho**8) if (prev is not None and prev > 0 and d > 0) else float('nan')
        prev = d
        print('%-22s %5d %8d %16.12f %16.12f %11.2e %9.3f'
              % (label if k == rows[0][0] else '', norm if k == rows[0][0] else 0,
                 k, float(f), float(p), float(d), r))
        rec['rows'].append(dict(k=k, future=float(f), past=float(p),
                                diff=float(d), ratio_over_rho8=r))
    out.append(rec)
    print()

# --- the two verdicts, as assertions -------------------------------------------------
verdict = {}
for rec in out:
    tail = rec['rows'][-1]
    if rec['unit'] and rec['norm'] == 1:
        # equal to working precision at EVERY k -- no limit involved
        ok = all(r['diff'] < 1e-60 for r in rec['rows'])
        verdict[rec['label']] = dict(kind='norm+1: equal at every k', ok=bool(ok),
                                     worst=max(r['diff'] for r in rec['rows']))
    elif rec['unit']:
        # geometric with ratio rho^2 per rung: the four-step ratio is rho^8
        rs = [r['ratio_over_rho8'] for r in rec['rows'][2:] if r['ratio_over_rho8'] == r['ratio_over_rho8']]
        ok = all(abs(r - 1.0) < 0.05 for r in rs)
        verdict[rec['label']] = dict(kind='norm-1: |f-p| ~ rho^{2k}', ok=bool(ok),
                                     ratios=rs)
    else:
        ok = tail['past'] < 1e-8 < tail['future']
        verdict[rec['label']] = dict(kind='non-unit: past collapses', ok=bool(ok),
                                     future=tail['future'], past=tail['past'])

for name, v in verdict.items():
    print('%-22s %-32s %s' % (name, v['kind'], 'OK' if v['ok'] else 'FAIL'))

json.dump(dict(cases=out, verdict=verdict), open('m1_obs16.json', 'w'), indent=1)
print('\n[results written to m1_obs16.json]')
