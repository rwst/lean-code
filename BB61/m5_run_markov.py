#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M5 sec 8: how close can a Markov measure come to killing every Fourier mode?

Psi(P) = max_{1<=h<=H} |G_P(h)|.  A Markov counterexample to 10.61 needs Psi = 0 with
H = infinity.  Grid over the 2-parameter family, then Nelder-Mead from the best grid
point.  Writes m5_markov.json.
"""
import json, time
import numpy as np
from scipy.optimize import minimize
from m0_engine import Alpha
from m5_markov import MarkovG, mat

H = 12
HS = list(range(1, H + 1))
GRID = 25
TARGETS = [('X^2-2X-1', [1, -2, -1]), ('X^2-3X+1', [1, -3, 1]),
           ('X^2-4X+1', [1, -4, 1]), ('X^3-4X^2-3X-1', [1, -4, -3, -1]),
           ('X^3-4X^2-4X-1', [1, -4, -4, -1]), ('X^3-6X^2+3X-1', [1, -6, 3, -1])]

out = []
for name, co in TARGETS:
    al = Alpha(co, name)
    mg = MarkovG(al, hmax=H)
    t0 = time.time()
    g = np.linspace(0.02, 0.98, GRID)
    best = (1e9, None)
    Z = np.empty((GRID, GRID))
    for i, u in enumerate(g):
        for j, v in enumerate(g):
            s = mg.Psi(mat(u, v), HS)
            Z[i, j] = s
            if s < best[0]: best = (s, (u, v))
    def f(z):
        u, v = np.clip(z, 1e-4, 1 - 1e-4)
        return mg.Psi(mat(u, v), HS)
    r = minimize(f, np.array(best[1]), method='Nelder-Mead',
                 options=dict(xatol=1e-6, fatol=1e-12, maxiter=800))
    u, v = np.clip(r.x, 1e-4, 1 - 1e-4)
    # the Bernoulli slice for comparison, and the argmax mode at the optimum
    bern = min(mg.Psi(mat(p, 1 - p), HS) for p in np.linspace(0.02, 0.98, 200))
    hstar = max(HS, key=lambda h: abs(mg.G(mat(u, v), h)))
    rec = dict(poly=name, alpha=float(al.alpha), H=H, grid=GRID,
               grid_min=float(best[0]), grid_arg=[float(best[1][0]), float(best[1][1])],
               opt=float(r.fun), opt_arg=[float(u), float(v)],
               bernoulli_min=float(bern), h_star=hstar,
               profile_at_opt=[abs(mg.G(mat(u, v), h)) for h in HS])
    out.append(rec)
    print('%-15s alpha=%.5f  min_P max_{h<=%d}|G| = %.6f at (p01,p10)=(%.4f,%.4f); '
          'Bernoulli slice min %.6f; argmax h=%d   %.0fs'
          % (name, al.alpha, H, r.fun, u, v, bern, hstar, time.time() - t0), flush=True)

json.dump(out, open('m5_markov.json', 'w'), indent=1)
print('\n-> m5_markov.json')
