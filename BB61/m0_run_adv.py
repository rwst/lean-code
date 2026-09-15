#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 9 -- how small can max_h |hat F_*nu(h)| be pushed over Markov nu?

A down payment on A4-S11 / M4.  Result: p = 1/2 is the Bernoulli optimum, but order-2
Markov measures beat Bernoulli, so the master-target constant c(alpha) is strictly below
the X5 plateau constant.
"""
from m0_engine import *
from m0_markov import Fhat, adversary
from m0_scan import Phi_vec
import numpy as np, json

CASES = [([1,-2,-1],'1+sqrt2'), ([1,-3,1],'(3+sqrt5)/2'), ([1,-3,-1],'(3+sqrt13)/2'),
         ([1,-3,2,-1],'X^3-3X^2+2X-1'), ([1,-2,-1,-1],'X^3-2X^2-X-1'), ([1,-3,0,-1],'X^3-3X^2-1')]
out = {}
for coeffs, name in CASES:
    al = Alpha(coeffs, name)
    P = np.prod(Phi_vec(al, 20000), axis=0)
    top = [int(i + 1) for i in np.argsort(-P)[:8]]
    hs = sorted(set(top[:6] + list(range(1, 7))))
    bern = max(float(P[h - 1]) for h in hs)
    print('=' * 96)
    print('%-16s alpha=%.5f rho=%.4f   H = %s' % (name, al.a, al.r, hs))
    print('   Bernoulli(1/2)                      max_H |F| = %.6f' % bern)
    # Bernoulli p-sweep
    ps = np.linspace(0.02, 0.98, 97)
    vals = [max(abs(Fhat(al, h, np.array([p, p]), 1)) for h in hs) for p in ps]
    i = int(np.argmin(vals))
    print('   best Bernoulli(p): p=%.3f            max_H |F| = %.6f' % (ps[i], vals[i]))
    rec = dict(alpha=al.a, rho=al.r, H=hs, bern_half=bern, bern_best=[float(ps[i]), float(vals[i])], markov={})
    for r in (1, 2, 3):
        v, p = adversary(al, hs, r, ntries=4, seed=r)
        # re-check the minimiser over a wide mode range
        wide = sorted(set(list(range(1, 200)) + top + [int(t) for t in np.argsort(-P)[:30] + 1]))
        wv = max(abs(Fhat(al, h, p, r)) for h in wide)
        print('   best order-%d Markov                 max_H |F| = %.6f   (over h<=400+ladder: %.6f)'
              % (r, v, wv))
        rec['markov'][r] = dict(minH=float(v), wide=float(wv), p=[float(z) for z in p])
    out[name] = rec
    json.dump(out, open('adv.json', 'w'))
