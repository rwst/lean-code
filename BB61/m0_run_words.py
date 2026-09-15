#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 7-8 -- Weyl sums, star discrepancy and histogram statistics for every word.

The X14 falsification watch: the minimum of max_h |Weyl| over all (word, alpha) pairs is
0.0089 against a noise floor of 0.0016, so nothing looks uniformly distributed.
"""
from m0_engine import *
from m0_fourier import Phi_parts
import numpy as np, json, math
from m0_words import CATALOG

def star_discrepancy(x):
    x = np.sort(x); N = len(x)
    i = np.arange(1, N + 1)
    return float(max(np.max(i / N - x), np.max(x - (i - 1) / N)))

def hist_stats(x, B=1000):
    c, _ = np.histogram(x, bins=B, range=(0, 1))
    f = c / len(x)
    empty = 0; run = 0
    for v in np.concatenate([c, c]):
        run = run + 1 if v == 0 else 0
        empty = max(empty, run)
    return dict(Linf=float(np.max(np.abs(f - 1.0 / B)) * B), max_empty_run_frac=empty / B,
                zero_bins=int(np.sum(c == 0)) / B)

def weyl_all(x, hs):
    e = np.exp(2j * np.pi * np.outer(hs, x))
    return np.abs(e.mean(axis=1))

CASES = [([1,-2,-1],'1+sqrt2'), ([1,-4,1],'2+sqrt3'), ([1,-3,1],'(3+sqrt5)/2'),
         ([1,-3,2,-1],'X^3-3X^2+2X-1'), ([1,-3,0,-1],'X^3-3X^2-1'), ([1,-2,-1,-1],'X^3-2X^2-X-1')]
N = 400000; L = 400
res = {}
for coeffs, name in CASES:
    al = Alpha(coeffs, name)
    # candidate modes: best 12 from the closed-form scan up to 5000, plus 1..30
    from m0_scan import Phi_vec
    P1, P2 = Phi_vec(al, 20000); P = P1 * P2
    top = list(np.argsort(-P)[:10] + 1)
    hs = sorted(set([int(t) for t in top] + list(range(1, 21))))
    res[name] = dict(alpha=al.a, rho=al.r, d=al.d, unit=bool(al.unit),
                     bern_top=[[int(t), float(P[t-1])] for t in top], words={})
    print('=' * 108)
    print('%-16s alpha=%.6f rho=%.5f  Bernoulli(1/2) best modes: %s' %
          (name, al.a, al.r, ', '.join('%d:%.4f' % (t, P[t-1]) for t in top[:6])))
    print('  %-20s %9s %9s %9s %9s   %s' % ('word', 'maxWeyl', 'argmax', 'D*_N', 'gapfrac', 'Weyl at top-4 modes'))
    for wname, f in CATALOG.items():
        eps = np.asarray(f(N + L), dtype=np.int8)
        x = orbit(al, eps, L=L)
        W = weyl_all(x, np.array(hs))
        i = int(np.argmax(W))
        hstat = hist_stats(x)
        d = star_discrepancy(x)
        res[name]['words'][wname] = dict(maxWeyl=float(W[i]), argmax=int(hs[i]), Dstar=d,
                                         hist=hstat, weyl={int(h): float(w) for h, w in zip(hs, W)})
        print('  %-20s %9.5f %9d %9.5f %9.4f   %s' % (wname, W[i], hs[i], d, hstat['max_empty_run_frac'],
              ' '.join('%.4f' % W[hs.index(int(t))] for t in top[:4])))
json.dump(res, open('words.json', 'w'))
