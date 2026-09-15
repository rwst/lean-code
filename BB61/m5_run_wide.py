#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 sec 8, the two honesty checks on the memory ladder.

Psi_k was minimised against the modes h <= 12 and with no constraint on the measure.
Both need auditing.

  (A) Degrees of freedom.  A memory-k chain has 2^k free parameters against 12 constraints,
      so from k = 4 on a decline in Psi_k may be the optimiser exploiting the truncation.
      Test: evaluate the RECORDED optimisers on h <= HWIDE, and re-minimise there.
  (B) Entropy.  M3 Thm 11 already excludes every invariant measure with h(mu) < h_min(alpha),
      so a chain that buys a small Fourier bias by spending entropy has bought nothing.
      Test: re-minimise with the penalty  10*max(0, h_min - h(mu)),  i.e. subject to the
      only constraint 10.61 actually leaves.

Writes m5_wide.json.
"""
import json, sys, time
import numpy as np
from scipy.optimize import minimize
from m0_engine import Alpha
from m5_memory import Memory
import m5_bernoulli as B

HWIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 32
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
POLY = {'X^2-2X-1': [1, -2, -1], 'X^2-3X+1': [1, -3, 1], 'X^2-4X+1': [1, -4, 1],
        'X^3-4X^2-3X-1': [1, -4, -3, -1], 'X^3-6X^2+3X-1': [1, -6, 3, -1]}
HS = list(range(1, HWIDE + 1))


def block_entropy(mm, q):
    """h(mu) for the memory-k chain with parameters q (same as m5_run_memory)."""
    T, pi, _ = mm.chains(np.asarray(q, dtype=float))
    h = 0.0
    for b in range(mm.n):
        for p in (1 - q[b], q[b]):
            if p > 1e-15: h -= pi[b] * p * np.log(p)
    return float(h)
sig = lambda z: 1.0 / (1.0 + np.exp(-np.clip(z, -30, 30)))

rows = [r for r in json.load(open('m5_memory.json')) if r['poly'] in POLY]
out = []
for r in rows:
    al = Alpha(POLY[r['poly']], r['poly'])
    hm = float(B.h_min(al))
    rec = dict(poly=r['poly'], alpha=r['alpha'], H=HWIDE, h_min=hm, ladder={})
    for k in sorted(int(x) for x in r['ladder']):
        if k > KMAX: continue
        mm = Memory(al, k, hmax=HWIDE)
        q = np.array(r['ladder'][str(k)]['q'])
        prof = mm.profile(q, HS)
        wide_at_old, argmax = float(max(prof)), int(np.argmax(prof)) + 1
        z0s = [np.zeros(1 << k), np.log(q / (1 - q))] + \
              [np.random.default_rng(200 + k + i).normal(0, 1.5, 1 << k) for i in range(2)]
        def run(pen):
            best = (1e9, None)
            for z0 in z0s:
                f = (lambda z: mm.Psi(sig(np.asarray(z)), HS)) if not pen else \
                    (lambda z: mm.Psi(sig(np.asarray(z)), HS)
                     + 10.0 * max(0.0, hm - block_entropy(mm, sig(np.asarray(z)))))
                rr = minimize(f, z0, method='Nelder-Mead',
                              options=dict(xatol=1e-7, fatol=1e-13, maxfev=10000))
                if rr.fun < best[0]: best = (float(rr.fun), sig(rr.x))
            return best
        t0 = time.time()
        u, qu = run(False)
        c, qc = run(True)
        rec['ladder'][str(k)] = dict(
            Psi12=r['ladder'][str(k)]['Psi'], entropy12=r['ladder'][str(k)].get('entropy'),
            wide_at_old_opt=wide_at_old, argmax=argmax,
            Psi_wide=u, entropy_wide=block_entropy(mm, qu),
            Psi_wide_ent=mm.Psi(qc, HS), entropy_wide_ent=block_entropy(mm, qc),
            q_wide=qu.tolist(), q_ent=qc.tolist(), secs=round(time.time() - t0, 1))
        d = rec['ladder'][str(k)]
        print('%-13s k=%d  Psi_12=%.5f (h=%.3f) | at h<=%d: %.5f (argmax %d) | '
              're-min %.5f (h=%.3f) | with h>=h_min=%.3f: %.5f (h=%.3f)  %.0fs'
              % (r['poly'], k, d['Psi12'], d['entropy12'] or 0, HWIDE, wide_at_old, argmax,
                 d['Psi_wide'], d['entropy_wide'], hm, d['Psi_wide_ent'],
                 d['entropy_wide_ent'], time.time() - t0), flush=True)
    out.append(rec)
    json.dump(out, open('m5_wide.json', 'w'), indent=1)
print('-> m5_wide.json')
