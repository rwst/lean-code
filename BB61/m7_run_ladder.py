#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7 runner: the first case beyond independence, via the ladder limits.

M5 sec 14 asks whether inf_P sup_h |Phi_h(mu_P)| > 0 over the memory-k Markov chains.
The ladder limits of m7_ladder answer it with no h-scan at all: at a quadratic Pisot
unit the mode-h_k test function splits into two bands of fixed shape at lag 2k, so for
every mixing mu the ladder coefficients converge, and

    Psi_k^lad(alpha) := min over memory-k chains of max over ladders |L_lam|
                     <=  inf_P sup_h |Phi_h(mu_P)| .

Each row is therefore a *lower* bound for the quantity M5 asks about.  The number of
ladders is also varied, because the bound can only improve with more of them.

Writes m7_ladder.json.
"""
import sys, json, time, itertools
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m7_ladder import rungs_from_seed, lam_of_seed, bernoulli_band
from m7_price import BlockChain

KMAX = 4
NLAD = 24
NSUB = [4, 12, 24]
HCAP = 4_000_000
NSTART = 10
TARGETS = [([1, -2, -1], '1+sqrt2'), ([1, -3, 1], '(3+sqrt5)/2'),
           ([1, -3, -1], '(3+sqrt13)/2'), ([1, -4, 1], '2+sqrt3')]


def ladders(al, bc, kmax=40, rng=6):
    q = np.full(1 << bc.L, 0.5)
    out, seen = [], set()
    seeds = [s for s in itertools.product(range(-rng, rng + 1), repeat=al.d) if any(s)]
    for s in seeds:
        h = [x for x in rungs_from_seed(al, s, kmax) if 0 < x <= HCAP]
        if len(h) < 5:
            continue
        v = np.abs(bc.phis(q, h[-2:]))
        if v.max() < 1e-5 or abs(v[0] - v[1]) > 1e-7:
            continue
        key = round(float(v[-1]), 9)
        if key in seen:
            continue
        seen.add(key)
        lam = lam_of_seed(al, s)
        out.append(dict(seed=list(s), h=int(h[-1]), plateau=float(v[-1]),
                        band=bernoulli_band(al, lam)))
    out.sort(key=lambda r: -r['plateau'])
    return out[:NLAD]


def run(al, name, coeffs):
    bc0 = BlockChain(al, 1, hmax=HCAP)
    lads = ladders(al, bc0)
    hs = [r['h'] for r in lads]
    rec = dict(poly=name, coeffs=coeffs, alpha=float(al.alpha), ladders=lads, rows={})
    print('%-14s alpha=%.5f  %d ladders; plateaux %s'
          % (name, float(al.alpha), len(lads),
             ' '.join('%.4f' % r['plateau'] for r in lads[:8])), flush=True)
    prev = None
    for k in range(1, KMAX + 1):
        bc = BlockChain(al, k, hmax=HCAP)
        n = 1 << k
        rng = np.random.default_rng(1000 + k)
        starts = [np.full(n, 0.5)]
        if prev is not None:                      # lift the previous optimum
            starts.append(np.concatenate([prev, prev]))
            starts.append(np.repeat(prev, 2))
        starts += [rng.uniform(0.02, 0.98, n) for _ in range(NSTART)]
        row = {}
        for N in NSUB:
            if N > len(hs):
                continue
            hh = hs[:N]
            f = lambda x: float(np.max(np.abs(bc.phis(np.clip(x, 1e-7, 1 - 1e-7), hh))))
            t0, best, bq = time.time(), 1e9, None
            for x0 in starts:
                r = minimize(f, x0, method='Nelder-Mead',
                             options=dict(maxiter=600 * n, xatol=1e-8, fatol=1e-13))
                if r.fun < best:
                    best, bq = float(r.fun), np.clip(r.x, 1e-7, 1 - 1e-7)
            row[str(N)] = dict(min_max_L=best, q=[float(v) for v in bq],
                               secs=round(time.time() - t0, 1))
            if N == NSUB[-1] or N == len(hs):
                prev = bq
        row['bern'] = float(np.max(np.abs(bc.phis(np.full(n, 0.5), hs))))
        rec['rows'][str(k)] = row
        print('   memory %d (%2d params):  %s   (Bernoulli %.6f)'
              % (k, n, '  '.join('N=%d:%.6f' % (N, row[str(N)]['min_max_L'])
                                 for N in NSUB if str(N) in row), row['bern']), flush=True)
        del bc
    return rec


out = []
for coeffs, name in TARGETS:
    out.append(run(Alpha(coeffs, name), name, coeffs))
    json.dump(out, open('m7_ladder.json', 'w'), indent=1)
print('\nwrote m7_ladder.json', flush=True)
