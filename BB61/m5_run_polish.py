#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 sec 8: enforce the monotonicity of the memory ladder.

Psi_k is non-increasing in k by embedding -- a memory-(k-1) chain is the memory-k chain
that ignores its oldest bit -- so a rise in the recorded ladder is optimiser noise, not
mathematics.  This pass restarts each cell from the *lifted* optimum of the previous
memory (in my bit convention the oldest bit is the high one, so q'[b] = q[b mod 2^{k-1}])
and keeps the better of the two.  Updates m5_memory.json in place.
"""
import json, time
import numpy as np
from scipy.optimize import minimize
from m0_engine import Alpha
from m5_memory import Memory

POLY = {'X^2-2X-1': [1, -2, -1], 'X^2-3X+1': [1, -3, 1], 'X^2-4X+1': [1, -4, 1],
        'X^3-4X^2-3X-1': [1, -4, -3, -1], 'X^3-6X^2+3X-1': [1, -6, 3, -1]}
sig = lambda z: 1.0 / (1.0 + np.exp(-np.clip(z, -30, 30)))


def block_entropy(mm, q):
    T, pi, _ = mm.chains(np.asarray(q, dtype=float))
    h = 0.0
    for b in range(mm.n):
        for p in (1 - q[b], q[b]):
            if p > 1e-15: h -= pi[b] * p * np.log(p)
    return float(h)


rows = json.load(open('m5_memory.json'))
for r in rows:
    al = Alpha(POLY[r['poly']], r['poly'])
    H = r['H']; HS = list(range(1, H + 1))
    ks = sorted(int(x) for x in r['ladder'])
    for k in ks[1:]:
        prev = np.array(r['ladder'][str(k - 1)]['q'])
        lift = np.array([prev[b % (1 << (k - 1))] for b in range(1 << k)])
        mm = Memory(al, k, hmax=H)
        f = lambda z: mm.Psi(sig(np.asarray(z)), HS)
        z0 = np.log(np.clip(lift, 1e-6, 1 - 1e-6) / (1 - np.clip(lift, 1e-6, 1 - 1e-6)))
        t0 = time.time()
        rr = minimize(f, z0, method='Nelder-Mead',
                      options=dict(xatol=1e-8, fatol=1e-14, maxfev=20000))
        rr = minimize(f, rr.x, method='Nelder-Mead',
                      options=dict(xatol=1e-9, fatol=1e-15, maxfev=20000))
        old = r['ladder'][str(k)]['Psi']
        if rr.fun < old:
            q = sig(rr.x)
            r['ladder'][str(k)].update(Psi=float(rr.fun), q=q.tolist(),
                                       entropy=block_entropy(mm, q),
                                       profile=mm.profile(q, HS), polished=True)
            print('%-15s k=%d  %.6f -> %.6f  (%.0fs)' % (r['poly'], k, old, rr.fun,
                                                         time.time() - t0), flush=True)
        else:
            r['ladder'][str(k)]['polished'] = False
            print('%-15s k=%d  %.6f kept  (%.0fs)' % (r['poly'], k, old,
                                                      time.time() - t0), flush=True)
json.dump(rows, open('m5_memory.json', 'w'), indent=1)
print('\n%-15s %s' % ('poly', '  '.join('  k=%d' % k for k in ks)))
for r in rows:
    print('%-15s %s' % (r['poly'], '  '.join('%.4f' % r['ladder'][str(k)]['Psi'] for k in ks)))
