#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# atlas2.py -- plan-dubC2 M2 (X2/X4/O-3): the (p/q, nu) divisor-set atlas, judged by EXACTLY
# the criterion DubC2/GenCert.lean checks (gencert.LeanModel.certificate()).
#
# For each (p/q, nu): the minimal-size divisor sets P (primes <= --pmax, |P| <= --maxP) that
# certify at some cell count D on the ladder D = p*b*2^j (j = 0..), vertex count <= --maxV.
# All minimal sets of the minimal size are reported.  One JSON line per (p/q, nu).
#
# Usage: atlas2.py --bases 3/2,5/2 --nus 0,1/2,-1 [--pmax 13] [--maxP 4] [--maxV 20000]

import argparse
import itertools
import json
import time
from fractions import Fraction
from math import gcd

import gencert as g


def certifies(p, q, a, b, P, maxV, jmax=6):
    for j in range(jmax + 1):
        D = p * b * 2 ** j
        m = g.LeanModel(p, q, a, b, list(P), D)
        if m.nV > maxV:
            return None
        c = g.fast_verdict(p, q, a, b, list(P), D, det_limit=1500)
        if c is not None and c["ok"]:
            return dict(D=D, core=c["core"], det=c["det"], nV=m.nV)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", required=True)
    ap.add_argument("--nus", default="0,1/2")
    ap.add_argument("--pmax", type=int, default=13)
    ap.add_argument("--maxP", type=int, default=4)
    ap.add_argument("--maxV", type=int, default=20000)
    ap.add_argument("--budget", type=float, default=900)
    args = ap.parse_args()
    primes = [l for l in range(2, args.pmax + 1) if all(l % d for d in range(2, l))]
    for base in args.bases.split(","):
        f = Fraction(base)
        p, q = f.numerator, f.denominator
        for nu in args.nus.split(","):
            v = Fraction(nu)
            t0 = time.time()
            found, cut = [], False
            for size in range(1, args.maxP + 1):
                for P in itertools.combinations(primes, size):
                    if any(q % l != 0 and gcd(l, q) != 1 for l in P):
                        continue
                    if any(l != 1 and p % l == 0 and q % l == 0 for l in P):
                        continue
                    if time.time() - t0 > args.budget:
                        cut = True
                        break
                    r = certifies(p, q, v.numerator, v.denominator, P, args.maxV)
                    if r:
                        found.append(dict(P=list(P), **r))
                if found or cut:
                    break
            print(json.dumps(dict(p=p, q=q, nu=str(v), minimal=found, truncated=cut,
                                  secs=round(time.time() - t0, 1))), flush=True)


if __name__ == "__main__":
    main()
