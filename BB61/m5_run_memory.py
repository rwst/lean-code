#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 sec 8: Psi_k(alpha) = the smallest max_{1<=h<=H} |G_P(h)| found over memory-k
Markov measures P on {0,1}^Z.

Multi-start Nelder-Mead in logit coordinates (unconstrained), then one polish restart.
Psi_k is non-increasing in k -- memory k embeds in memory k+1 -- and memory-k measures
are weak-* dense in the invariant measures as k -> infinity, so the ladder is a finite
but genuine probe of the master target (note-1061-M1.html Cor. 9): 10.61 fails at alpha
only if inf_k Psi_k = 0 for every H.  Every value printed is an upper bound for the true
minimum (it is a value actually attained) and a lower bound for sup over ALL h.
Also records the entropy of the optimiser, to be compared with M3's floor h_min(alpha).
"""
import json, sys, time
import numpy as np
from scipy.optimize import minimize
from m0_engine import Alpha
from m5_memory import Memory

H = int(sys.argv[1]) if len(sys.argv) > 1 else 12
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
HS = list(range(1, H + 1))
TARGETS = [('X^2-2X-1', [1, -2, -1]), ('X^2-3X+1', [1, -3, 1]),
           ('X^2-4X+1', [1, -4, 1]), ('X^3-4X^2-3X-1', [1, -4, -3, -1]),
           ('X^3-6X^2+3X-1', [1, -6, 3, -1])]
sig = lambda z: 1.0 / (1.0 + np.exp(-np.clip(z, -30, 30)))


def block_entropy(mm, q):
    """h(mu) for the memory-k chain with parameters q."""
    T, pi, _ = mm.chains(np.asarray(q, dtype=float))
    h = 0.0
    for b in range(mm.n):
        for p in (1 - q[b], q[b]):
            if p > 1e-15: h -= pi[b] * p * np.log(p)
    return float(h)


out = []
for name, co in TARGETS:
    al = Alpha(co, name)
    rec = dict(poly=name, alpha=float(al.alpha), H=H, ladder={})
    for k in range(1, KMAX + 1):
        mm = Memory(al, k, hmax=H)
        f = lambda z: mm.Psi(sig(np.asarray(z)), HS)
        rng = np.random.default_rng(100 + k)
        nstart = 10 if k <= 3 else 14
        mfev = 8000 if k <= 3 else 40000
        best = (1e9, None)
        t0 = time.time()
        starts = [np.zeros(1 << k)] + [rng.normal(0, 1.5, 1 << k) for _ in range(nstart - 1)]
        for z0 in starts:
            r = minimize(f, z0, method='Nelder-Mead',
                         options=dict(xatol=1e-8, fatol=1e-14, maxfev=mfev))
            r = minimize(f, r.x, method='Nelder-Mead',
                         options=dict(xatol=1e-9, fatol=1e-15, maxfev=mfev))
            if r.fun < best[0]: best = (float(r.fun), sig(r.x))
        q = best[1]
        rec['ladder'][str(k)] = dict(Psi=best[0], q=q.tolist(), entropy=block_entropy(mm, q),
                                     profile=mm.profile(q, HS), secs=round(time.time() - t0, 1))
        print('%-15s k=%d  Psi_k = %.6f   h(mu)=%.4f   (%.0fs)'
              % (name, k, best[0], rec['ladder'][str(k)]['entropy'], time.time() - t0), flush=True)
    out.append(rec)
    json.dump(out, open('m5_memory.json', 'w'), indent=1)

print('\n%-15s %s' % ('poly', '  '.join('  k=%d' % k for k in range(1, KMAX + 1))))
for r in out:
    print('%-15s %s' % (r['poly'], '  '.join('%.4f' % r['ladder'][str(k)]['Psi']
                                             for k in range(1, KMAX + 1))))
print('-> m5_memory.json')
