#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M7 runner: bracket E_H(alpha) from both sides.

Upper bound: the M3/M4 optimiser, min over multipliers of the truncated pressure --
which is what every earlier run reported.  Lower bound: an explicit mixture of
memory-L Markov measures with all Fourier coefficients up to H vanishing exactly
(m7_price.lp_lower).  A lower bound above h_min(alpha) proves that *no* trigonometric
certificate of degree <= H exists at that alpha -- which is what turns M4's silence
into a theorem.

Writes m7_price.json.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
from m0_engine import Alpha
from m3_entropy import Window, h_min, minimize_pressure
from m4_fourier import best_window, pad
from m7_price import BlockChain, lp_lower

LPOOL = 12
HS = [1, 2, 4, 8, 16, 32, 64]
TS = [0.01, 0.04, 0.15, 0.5]

TARGETS = [
    ([1, -2, -1], '1+sqrt2'),            # hard, no gap, no Route A, Thm T excludes X8
    ([1, -3, 1], '(3+sqrt5)/2'),         # ditto
    ([1, -3, -1], '(3+sqrt13)/2'),       # hard
    ([1, -4, 1], '2+sqrt3'),             # decided: one cosine (M3 sec 8.1)
    ([1, -4, -3, -1], 'X^3-4X^2-3X-1'),  # decided by M4 at H=64
    ([1, -4, -4, -1], 'X^3-4X^2-4X-1'),  # decided by M4 at H=64
    ([1, -6, 3, -1], 'X^3-6X^2+3X-1'),   # examined by M4, resisted
]
ONLY = set(sys.argv[1:])
if ONLY:
    TARGETS = [t for t in TARGETS if t[1] in ONLY]
OUTFILE = 'm7_price2.json' if ONLY else 'm7_price.json'


def pool_vectors(H, xstar):
    out = [xstar.copy()]
    for h in range(1, H + 1):
        for t in TS:
            for sgn in (1, -1):
                for im in (0, 1):
                    x = xstar.copy()
                    x[(h - 1) + im * H] += sgn * t
                    out.append(x)
    return out


out = []
for coeffs, name in TARGETS:
    al = Alpha(coeffs, name)
    hm = h_min(al)
    N, M, e = best_window(al, LPOOL)
    W = Window(al, N, M)
    bc = BlockChain(al, LPOOL, hmax=max(HS))
    rec = dict(poly=name, coeffs=coeffs, alpha=float(al.alpha), rho=float(al.rho),
               h_min=hm, window=[N, M, e], Lpool=LPOOL, rows={})
    print('%-16s alpha=%.5f  h_min=%.6f  pool window (%d,%d) eps=%.1e'
          % (name, float(al.alpha), hm, N, M, e), flush=True)
    xp, Hp = None, 0
    for H in HS:
        W.set_modes(list(range(1, H + 1)))
        t0 = time.time()
        P, xstar, flat, delta = minimize_pressure(W, x0=pad(xp, Hp, H))
        xp, Hp = xstar, H
        hs = list(range(1, H + 1))
        ent, phi = [], []
        for x in pool_vectors(H, xstar):
            a = x[:H] + 1j * x[H:]
            q = bc.from_window(W, a)
            ent.append(bc.entropy(q))
            phi.append(bc.phis(q, hs))
        ent, phi = np.array(ent), np.array(phi)
        ok = np.isfinite(ent) & np.isfinite(phi).all(axis=1)   # a gap sends the
        ent, phi = ent[ok], phi[ok]                            # multipliers to the
        if len(ent) == 0:                                      # box boundary and the
            ent, phi = np.zeros(1), np.zeros((1, H), complex)  # weights underflow
        lb, lam = lp_lower(ent, phi, H)
        nat = int(np.sum(lam > 1e-12)) if lam is not None else 0
        rec['rows'][str(H)] = dict(E_ub=P, flat=flat, E_lb=lb, atoms=nat,
                                   pool=len(ent), ent_max=float(ent.max()),
                                   no_cert=bool(lb is not None and lb > hm),
                                   secs=round(time.time() - t0, 1))
        print('   H=%-3d  E_ub=%.6f (|Phi|<=%.1e)   E_lb=%s  atoms=%-4d  %s  %.0fs'
              % (H, P, flat, ('%.6f' % lb) if lb is not None else 'infeasible', nat,
                 'NO CERTIFICATE of degree <= %d' % H if (lb is not None and lb > hm)
                 else ('' if lb is None else 'inconclusive (lb below the floor)'),
                 time.time() - t0), flush=True)
    del W
    out.append(rec)
    json.dump(out, open(OUTFILE, 'w'), indent=1)
print('\nwrote ' + OUTFILE, flush=True)
