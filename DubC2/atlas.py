#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# atlas.py -- plan-dubC2 M2, experiments X2/X4/O-3: the (p/q, nu) divisor-set atlas.
#
# For every base p/q and shift nu in the scan, find the MINIMAL divisor sets P (by size,
# then lexicographically) that the gencert criterion certifies:
#
#     peel the gencert graph G(P, D) to its bi-infinite core, determinize from the whole
#     core, and require that every det-SCC has at most one internal letter.
#
# This is exactly the check DubC2/GenCert.lean performs, so every row of the output with
# verdict CERT is one `decide` away from a Lean theorem.  Output: one JSON line per
# (p, q, nu) to stdout.
#
# Usage: atlas.py [--bases 3/2,5/2,...] [--nus 0,1/2,...] [--primes 2,3,5,7,11,13]
#                 [--maxP 4] [--Ds 1,2,3]

import argparse
import itertools
import json
import sys
import time
from fractions import Fraction
from math import gcd

import gencert as g


def bicore(m):
    V = m.vertices()
    succ = {v: set() for v in V}
    pred = {v: set() for v in V}
    for v in V:
        for s in m.alph:
            for w in m.succ_v(v, s):
                succ[v].add(w)
                pred[w].add(v)
    alive = set(V)
    # worklist peel
    outd = {v: len(succ[v]) for v in V}
    ind = {v: len(pred[v]) for v in V}
    work = [v for v in V if outd[v] == 0 or ind[v] == 0]
    while work:
        v = work.pop()
        if v not in alive:
            continue
        alive.discard(v)
        for w in succ[v]:
            if w in alive:
                ind[w] -= 1
                if ind[w] == 0:
                    work.append(w)
        for u in pred[v]:
            if u in alive:
                outd[u] -= 1
                if outd[u] == 0:
                    work.append(u)
    return frozenset(alive)


def verdict(m, det_limit=5000):
    C = bicore(m)
    if not C:
        return dict(v="EMPTY", core=0, det=0, total=0)
    r = g.determinize(m, C, det_limit)
    if r is None:
        return dict(v="BIG", core=len(C))
    sets, trans = r
    n = len(sets)
    adj = [[j for j in trans[i].values() if j is not None] for i in range(n)]
    comp, nc = g.tarjan(n, adj)
    ok = all(len([s for s, j in trans[i].items() if j is not None and comp[j] == comp[i]]) <= 1
             for i in range(n))
    return dict(v="CERT" if ok else "FAIL", core=len(C), det=n,
                total=sum(len(S) for S in sets))


def scan(p, q, nu, primes, maxP, Dmults, budget):
    a, b = nu.numerator, nu.denominator
    t0 = time.time()
    found = []
    tried = 0
    for size in range(1, maxP + 1):
        for P in itertools.combinations(primes, size):
            # every l must divide q or be coprime to q, and l | q => l coprime to p (automatic)
            if any(q % l != 0 and gcd(l, q) != 1 for l in P):
                continue
            if any(set(F) <= set(P) for F, _ in found):
                continue  # not minimal
            best = None
            for dm in Dmults:
                D = p * b * dm
                m = g.Model(p, q, a, b, P, D)
                if len(m.vertices()) > 40000:
                    break
                vd = verdict(m)
                tried += 1
                if vd["v"] in ("CERT", "EMPTY"):
                    best = dict(D=D, **vd)
                    break
            if best:
                found.append((P, best))
            if time.time() - t0 > budget:
                return found, tried, True
        if found:
            break  # minimal size reached
    return found, tried, False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", default=None)
    ap.add_argument("--nus", default="0,1/2")
    ap.add_argument("--primes", default="2,3,5,7,11,13")
    ap.add_argument("--maxP", type=int, default=4)
    ap.add_argument("--Ds", default="1,2,4,8")
    ap.add_argument("--budget", type=float, default=600)
    args = ap.parse_args()
    primes = [int(t) for t in args.primes.split(",")]
    Dm = [int(t) for t in args.Ds.split(",")]
    if args.bases:
        bases = [Fraction(t) for t in args.bases.split(",")]
    else:
        bases = sorted({Fraction(p, q) for q in range(2, 8) for p in range(q + 1, 3 * q + 1)
                        if gcd(p, q) == 1})
    nus = [Fraction(t) for t in args.nus.split(",")]
    for base in bases:
        p, q = base.numerator, base.denominator
        for nu in nus:
            t0 = time.time()
            found, tried, cut = scan(p, q, nu, primes, args.maxP, Dm, args.budget)
            print(json.dumps(dict(p=p, q=q, nu=str(nu),
                                  minimal=[dict(P=list(P), **r) for P, r in found],
                                  tried=tried, truncated=cut,
                                  secs=round(time.time() - t0, 1))), flush=True)


if __name__ == "__main__":
    main()
