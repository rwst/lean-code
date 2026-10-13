#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# atlas_sound.py -- R-6 cross-check of the atlas graph (gencert.LeanModel.succMask = the Lean
# Params.succList): iterate x_n = floor(xi (p/q)^n + nu) for random rational xi in exact
# Fractions, straight from the definition, and check that every pair of consecutive avoiding
# times is an edge (vertex (x_n mod M, floor(D y_n)) -> next vertex, labelled by the true carry).
# A soundness failure here would mean the over-approximation drops a real transition.
#
# Usage: atlas_sound.py p q nu P D [--n 4000] [--steps 80]

import argparse
import math
import random
from fractions import Fraction

import gencert as g


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("p", type=int)
    ap.add_argument("q", type=int)
    ap.add_argument("nu")
    ap.add_argument("P")
    ap.add_argument("D", type=int)
    ap.add_argument("--n", type=int, default=4000)
    ap.add_argument("--steps", type=int, default=80)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    nu = Fraction(a.nu)
    P = [int(t) for t in a.P.split(",")]
    m = g.LeanModel(a.p, a.q, nu.numerator, nu.denominator, P, a.D)
    rnd = random.Random(a.seed)
    beta = Fraction(a.p, a.q)
    pairs = bad = 0
    longest = 0
    for _ in range(a.n):
        xi = Fraction(rnd.randint(-10 ** 6, 10 ** 6), rnd.randint(1, 10 ** 6))
        if xi == 0:
            continue
        z = xi
        prev = None
        run = 0
        for n in range(a.steps):
            w = z + nu
            x = math.floor(w)
            y = w - x
            av = all(x % l != 0 for l in P)
            run = run + 1 if av else 0
            longest = max(longest, run)
            v = (x % m.M) * m.D + math.floor(m.D * y)
            if prev is not None and av and prev[2]:
                pv, px = prev[0], prev[1]
                s = a.q * x - a.p * px
                t = s - m.sLo
                ok = 0 <= t < m.nA and (m.succMask(pv, s) >> v) & 1
                pairs += 1
                if not ok:
                    bad += 1
            prev = (v, x, av)
            z *= beta
    print(f"{a.p}/{a.q} nu={nu} P={P} D={a.D}: {pairs} avoiding transitions checked, "
          f"{bad} violations, longest avoiding run {longest}")


if __name__ == "__main__":
    main()
