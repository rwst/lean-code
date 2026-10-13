#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xresfree.py -- plan-dubC2-transform X-S/X-nu on RESIDUE-FREE cells: divisor sets P made of
# primes dividing p*q.  Avoiding P then forces exactly gcd(s_n, prod P) = 1 on the carries
# (l | q: q x' = p x + s gives s = -p x != 0 mod l;  l | p: q x' = s mod l), and nothing else:
# the residue part of the certificate graph carries no information, and the model is the
# one-dimensional open system  y' = (p y - s - w)/q,  w = (p-q) nu,  letters s coprime to prod P.
#
# For each nu on a rational grid over one period prod P of the shift circle, report
#   cert  = least D (ladder 2p*2^j, j <= --jmax) at which gencert.fast_verdict certifies, or None;
#   words = number of admissible carry words of length --n (exact cylinder intervals), and the
#           ratio of the last two counts (a growth-rate estimate: > 1 + eps means positive entropy,
#           hence an aperiodic avoiding pseudo-orbit, hence NO certificate at any D).
# One JSON line per nu.
#
# Usage: xresfree.py p q P(dot-separated) denom [--n 28] [--jmax 7]

import argparse
import json
import math
from fractions import Fraction as F
from math import gcd

import gencert as g


def letters(p, q, nu, m):
    w = (p - q) * nu
    return [s for s in range(math.floor(-q - w) + 1, math.ceil(p - w)) if gcd(s, m) == 1]


def word_counts(p, q, nu, m, n, cap=60000):
    w = (p - q) * nu
    L = letters(p, q, nu, m)
    cur = [(F(0), F(1))]
    counts = []
    for _ in range(n):
        nxt = []
        for a, b in cur:
            for s in L:
                lo = max(a, (s + w) / p)
                hi = min(b, (s + w + q) / p)
                if lo < hi:
                    nxt.append(((p * lo - s - w) / q, (p * hi - s - w) / q))
        cur = nxt
        counts.append(len(cur))
        if len(cur) > cap:
            break
    return L, counts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("p", type=int)
    ap.add_argument("q", type=int)
    ap.add_argument("P")
    ap.add_argument("denom", type=int)
    ap.add_argument("--n", type=int, default=28)
    ap.add_argument("--jmax", type=int, default=7)
    ap.add_argument("--lo", default=None)
    ap.add_argument("--hi", default=None)
    a = ap.parse_args()
    P = [int(x) for x in a.P.split(".")]
    m = math.prod(P)
    assert all((a.p % l == 0) != (a.q % l == 0) for l in P), "P must be residue-free"
    lo = F(a.lo) if a.lo else F(0)
    hi = F(a.hi) if a.hi else F(m)
    k0, k1 = math.ceil(lo * a.denom), math.floor(hi * a.denom)
    for k in range(k0, k1 + 1):
        nu = F(k, a.denom)
        cert = None
        for j in range(a.jmax + 1):
            D = 2 * a.p * 2 ** j
            if D * math.prod(l for l in P if a.q % l) > 40000:
                break
            c = g.fast_verdict(a.p, a.q, nu.numerator, nu.denominator, P, D, det_limit=3000)
            if c is not None and c["ok"]:
                cert = D
                break
        L, cnt = word_counts(a.p, a.q, nu, m, a.n if cert is None else 12)
        ratio = cnt[-1] / cnt[-2] if len(cnt) > 1 and cnt[-2] else None
        print(json.dumps(dict(p=a.p, q=a.q, P=P, nu=str(nu), letters=L, cert=cert,
                              words=cnt[-1], wlen=len(cnt),
                              ratio=round(ratio, 5) if ratio else None)), flush=True)


if __name__ == "__main__":
    main()
