#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5: the direct check of Theorem A + Theorem B.

Theorem A says the empirical measures of ({xi alpha^n}) converge to F_* mu_p whenever
the digit word is generic for the Bernoulli(p) measure; Theorem B evaluates the Fourier
coefficients of F_* mu_p in closed form.  Together they predict

    (1/N) sum_{n<N} e(h {xi alpha^n})  ->  G_p(h)      (complex, phase included).

This script draws Bernoulli(p) words, runs the M0 orbit engine on them, and compares.
The expected error is the CLT size 1/sqrt(N), so the test is: |empirical - G| * sqrt(N)
stays O(1) while |empirical| stays far from 0.  Writes m5_direct.json.
"""
import json, sys, time
import numpy as np
import mpmath as mp
from m0_engine import Alpha, orbit
import m5_bernoulli as B

mp.mp.dps = 40
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
SEEDS = [1, 2, 3]
CASES = [('X^2-2X-1', [1, -2, -1], [1, 3]),
         ('X^2-4X+1', [1, -4, 1], [1, 14]),
         ('X^3-4X^2-3X-1', [1, -4, -3, -1], [1, 2]),
         ('X^2-5X-2', [1, -5, -2], [1, 27])]
PS = [0.5, 0.3]

out = []
for name, co, hs in CASES:
    al = Alpha(co, name)
    L = 200
    for p in PS:
        for seed in SEEDS:
            rng = np.random.default_rng(seed)
            eps = (rng.random(N + L) < p).astype(np.int64)
            t0 = time.time()
            x = orbit(al, eps, L=L)
            for h in hs:
                emp = complex(np.mean(np.exp(2j * np.pi * h * x)))
                G = complex(B.weyl(al, h, mp.mpf(p))['value'])
                err = abs(emp - G)
                rec = dict(poly=name, p=p, seed=seed, h=h, N=len(x),
                           emp_re=emp.real, emp_im=emp.imag,
                           G_re=G.real, G_im=G.imag, err=err,
                           err_scaled=err * np.sqrt(len(x)), absG=abs(G))
                out.append(rec)
                print('%-14s p=%.1f seed=%d h=%-3d  emp=%+.6f%+.6fi  G=%+.6f%+.6fi  '
                      'err=%.2e  err*sqrtN=%.2f' %
                      (name, p, seed, h, emp.real, emp.imag, G.real, G.imag,
                       err, rec['err_scaled']), flush=True)
            print('     (%.0fs for the orbit)' % (time.time() - t0), flush=True)

json.dump(out, open('m5_direct.json', 'w'), indent=1)
bad = [r for r in out if r['err_scaled'] > 8.0]
print('\n%d comparisons, max err*sqrtN = %.2f, %d above 8' %
      (len(out), max(r['err_scaled'] for r in out), len(bad)))
