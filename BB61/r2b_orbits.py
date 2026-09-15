#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""R2b by-product: periodic orbits as a pool, and R1b's certificate on top of them.

R2b's generators are periodic orbits, whose `Phi_h` is a `q`-term average of explicitly
summable series -- no window, no transfer operator, no stationary solve, and a radius of
`3e-13` for free (`r2b_ergodic.orbit_phi_true`).  That makes them a POOL in exactly R1b's
sense, and Theorem 1' of `note-1061-R2a.html` (`r2a_margin.margin`) certifies

    0 in int conv{Phi(nu_j)}   ==>   K_H != empty   ==>   nu_H = 0 ,

which is the statement R2b's own criterion is blocked by.  Two things are worth running:

  * `1+sqrt2`, as a cross-check against R1b's M7-pool certificates at `H <= 64`;
  * `(3+sqrt5)/2` at `H = 64`, where R1b recorded its one REFUTATION -- the M7 pool there
    was proved too small.  A pool that is not the M7 pool is exactly what that needs.

Usage:  python3 r2b_orbits.py            # the recorded run
        python3 r2b_orbits.py --one A B name H q
"""
import json
import math
import sys
import time
import warnings

import numpy as np

sys.path.insert(0, '/home/ralf/math/lean-code/BB61')
import r2b_ergodic as Z
import r2a_margin as MG
from m0_engine import Alpha

warnings.filterwarnings('ignore')
BB = '/home/ralf/math/lean-code/BB61'


def pool(al, H, qmax=14, bern=True):
    """Every periodic orbit of period `<= qmax` (and Bernoulli), as `Phi` rows."""
    V = [Z.orbit_phi_true(al, wd, H) for wd in Z.necklaces(qmax)]
    if bern:
        V.append(Z.bern_phi_true(al, H))
    return np.asarray(V), Z.orbit_phi_radius(al, H)


def certify(al, H, qmax=14, log=print):
    t0 = time.time()
    phi, eps = pool(al, H, qmax)
    Vm = MG.vmat(phi, H)
    r = MG.margin(Vm, eps, H)
    nu, _ = Z.hull_nu(list(phi), H, r=0.0, iters=6000)
    out = dict(name=al.name, H=H, qmax=qmax, m=int(phi.shape[0]), eps=float(eps),
               delta=float(r['delta']), sigma=float(r.get('sigma', 0.0)),
               feasible=bool(r['delta'] > 0), nu=float(nu), secs=time.time() - t0)
    log(f"  {al.name:>12} H={H:<4d} q<={qmax:<3d} m={out['m']:<5d} eps {eps:.2e}  "
        f"sigma {out['sigma']:.3e}  delta {out['delta']:12.5e}  "
        f"nu_up {nu:.3e}  {'K_H != empty CERTIFIED' if out['feasible'] else 'not certified'}"
        f"  ({out['secs']:.0f}s)")
    return out


def run(log=print):
    out = []
    log("=" * 96)
    log("R2b by-product: the periodic-orbit pool, certified with R2a Theorem 1'")
    log("=" * 96)
    log("\n# 1+sqrt2 -- the cross-check against R1b's M7-pool certificates")
    al = Alpha([1, -2, -1], '1+sqrt2')
    for H in (8, 16, 32, 64):
        for q in (10, 12, 14):
            out.append(certify(al, H, q, log=log))
    log("\n# (3+sqrt5)/2 -- R1b's one refutation: its H=64 M7 pool was proved too small")
    al5 = Alpha([1, -3, 1], '(3+sqrt5)/2')
    for H in (8, 16, 32, 64):
        for q in (10, 12, 14):
            out.append(certify(al5, H, q, log=log))
    log("\n# (3+sqrt13)/2 -- the third unit of M7 sec 4")
    al13 = Alpha([1, -3, -1], '(3+sqrt13)/2')
    for H in (32, 64):
        for q in (12, 14):
            out.append(certify(al13, H, q, log=log))
    with open(f'{BB}/r2b_orbits.json', 'w') as f:
        json.dump(out, f, indent=1)
    log(f"\n# wrote {BB}/r2b_orbits.json")
    return 0


def main():
    if '--one' in sys.argv:
        i = sys.argv.index('--one')
        A, B, name, H, q = (int(sys.argv[i + 1]), int(sys.argv[i + 2]), sys.argv[i + 3],
                            int(sys.argv[i + 4]), int(sys.argv[i + 5]))
        certify(Alpha([1, -A, -B], name), H, q)
        return 0
    return run()


if __name__ == '__main__':
    sys.exit(main())
