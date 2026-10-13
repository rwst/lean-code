#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xschema.py -- plan-dubC2-transform X-S (gate G-1): run the GenCert criterion
# (gencert.fast_verdict, same verdict as DubC2/GenCert.lean) for FIXED divisor sets P along a
# column of bases at fixed shift nu, and record the certificate shape (D, core, det, nV).
# One JSON line per (p/q, nu, P).  A null verdict is a fact about the ladder
# D = p*b*2^j (j <= --jmax, vertices <= --maxV), never about the object (plan L24).
#
# Usage: xschema.py --nu -1 --sets 2.3,2.3.5 --pmax 25 [--qmin 2] [--ratio 4]

import argparse
import json
import time
from fractions import Fraction
from math import gcd

import gencert as g


def verdict(p, q, a, b, P, maxV, jmax):
    for j in range(jmax + 1):
        D = p * b * 2 ** j
        m = g.LeanModel(p, q, a, b, list(P), D)
        if m.nV > maxV:
            return None, D
        c = g.fast_verdict(p, q, a, b, list(P), D, det_limit=1500)
        if c is not None and c["ok"]:
            return dict(D=D, core=c["core"], det=c["det"], nV=m.nV), D
    return None, D


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nu", required=True)
    ap.add_argument("--sets", required=True)
    ap.add_argument("--pmax", type=int, default=25)
    ap.add_argument("--qmin", type=int, default=2)
    ap.add_argument("--ratio", type=float, default=4.0)
    ap.add_argument("--maxV", type=int, default=20000)
    ap.add_argument("--jmax", type=int, default=6)
    args = ap.parse_args()
    v = Fraction(args.nu)
    sets = [[int(x) for x in s.split(".")] for s in args.sets.split(",")]
    for p in range(3, args.pmax + 1):
        for q in range(args.qmin, p):
            if gcd(p, q) != 1 or p / q > args.ratio:
                continue
            for P in sets:
                if any(q % l != 0 and gcd(l, q) != 1 for l in P) or any(p % l == 0 and q % l == 0 for l in P):
                    continue
                if any(q % l == 0 and p % l == 0 for l in P):
                    continue
                t0 = time.time()
                r, Dlast = verdict(p, q, v.numerator, v.denominator, P, args.maxV, args.jmax)
                print(json.dumps(dict(p=p, q=q, nu=str(v), P=P, cert=r, Dlast=Dlast,
                                      secs=round(time.time() - t0, 2))), flush=True)


if __name__ == "__main__":
    main()
