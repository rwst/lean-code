#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# xg3.py -- plan-dubC2-transform, gate G-3 (the only sanctioned rerun of the scan).
#
# Input: data/transform/g3/scan*.jsonl, written by
#   atlas2.py --bases <24 bases> --nus 0,1/2,-1 --pmax 17 --maxP 5 --maxV 20000 --budget 1800
# i.e. the 21 scanned bases plus 14/9, 15/8, 17/9, primes <= 17 (was 13), |P| <= 5 (was 4).
# Tests the conjectures fed to G-3 by X-DB (note sec. 7) on the new data and records every death:
#   C-1  at non-integer nu every minimal certified P contains 2
#   C-2  |P_min(1/2)| <= |P_min(0)| where both rows certify
#   N-3  no certificate at p >= 8 (and none at p - q >= 3, q >= 3)
#   N-4  at integer nu, Thm 42 kills {2} and {3} on every row  (obstruction_scan.witness, no scan
#        needed; run on the 24 bases and on every coprime p/q with q < p <= 30, p/q <= 4)
# Output: data/transform/g3/g3_verdicts.json, and a printed summary.

import glob
import json
import os
import sys
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from obstruction_scan import witness  # noqa: E402

G3 = os.path.join(HERE, "data", "transform", "g3")


def load(paths):
    out = {}
    for f in paths:
        for l in open(f):
            if l.strip():
                r = json.loads(l)
                out[(r["p"], r["q"], r["nu"])] = r
    return out


def main():
    new = load(sorted(glob.glob(os.path.join(G3, "scan*.jsonl"))))
    old = load([os.path.join(HERE, "atlas_out", "atlas2.jsonl")])
    deaths, notes = [], []

    # the rerun must reproduce every old hit at size <= old size (primes <= 13 are a subset)
    for k, r in old.items():
        if k in new and r["minimal"]:
            ns = min((len(m["P"]) for m in new[k]["minimal"]), default=None)
            os_ = len(r["minimal"][0]["P"])
            if ns is None or ns > os_:
                notes.append(f"REGRESSION {k}: old size {os_}, new {ns}")

    c1 = [(k, m["P"]) for k, r in new.items() if Fraction(k[2]).denominator > 1
          for m in r["minimal"]]
    c1_dead = [x for x in c1 if 2 not in x[1]]
    if c1_dead:
        deaths.append(dict(conj="C-1", witnesses=c1_dead))

    c2 = []
    for (p, q, nu), r in new.items():
        if nu != "1/2" or (p, q, "0") not in new:
            continue
        a, b = r["minimal"], new[(p, q, "0")]["minimal"]
        if a and b:
            c2.append(((p, q), len(a[0]["P"]), len(b[0]["P"])))
    c2_dead = [x for x in c2 if x[1] > x[2]]
    if c2_dead:
        deaths.append(dict(conj="C-2", witnesses=c2_dead))

    n3 = [(k, r["minimal"]) for k, r in new.items() if r["minimal"] and
          (k[0] >= 8 or (k[0] - k[1] >= 3 and k[1] >= 3))]
    if n3:
        deaths.append(dict(conj="N-3", witnesses=n3))

    n4_rows, n4_dead = 0, []
    for p in range(3, 31):
        for q in range(2, p):
            if gcd(p, q) != 1 or p > 4 * q:
                continue
            for nu in (0, -1, 1, 2, -2):
                n4_rows += 1
                for l in (2, 3, 5):
                    w = witness(p, q, Fraction(nu), [l])
                    if w is None:
                        n4_dead.append((p, q, nu, l))
    n4 = dict(rows=n4_rows,
              unkilled={l: [x[:3] for x in n4_dead if x[3] == l] for l in (2, 3, 5)})
    if n4["unkilled"][2] or n4["unkilled"][3]:
        deaths.append(dict(conj="N-4", witnesses=n4["unkilled"][2] + n4["unkilled"][3]))

    # coverage: which candidate sets the ladder could test at all (nV = M*D <= maxV at j = 0)
    import itertools
    PR = [2, 3, 5, 7, 11, 13, 17]
    cov = {}
    for (p, q, nu), r in new.items():
        b = Fraction(nu).denominator
        t = {"old(<=13,<=4)": [0, 0], "with 17": [0, 0], "size 5": [0, 0]}
        for k in range(1, 6):
            for P in itertools.combinations(PR, k):
                if any(q % l and gcd(l, q) != 1 for l in P):
                    continue
                M = 1
                for l in P:
                    if q % l:
                        M *= l
                ok = M * p * b <= 20000
                key = "size 5" if k == 5 else ("with 17" if 17 in P else "old(<=13,<=4)")
                t[key][0] += 1
                t[key][1] += ok
        cov[f"{p}/{q}@{nu}"] = t
    tot = {k: [sum(v[k][0] for v in cov.values()), sum(v[k][1] for v in cov.values())]
           for k in ("old(<=13,<=4)", "with 17", "size 5")}

    res = dict(coverage_total_candidates_vs_testable=tot, rows_scanned=len(new), rows_hit=sum(bool(r["minimal"]) for r in new.values()),
               truncated=[k for k, r in new.items() if r.get("truncated")],
               new_hits=[(k, r["minimal"]) for k, r in new.items()
                         if r["minimal"] and not (old.get(k) or {}).get("minimal")],
               smaller=[(k, [m["P"] for m in r["minimal"]]) for k, r in new.items()
                        if r["minimal"] and (old.get(k) or {}).get("minimal")
                        and len(r["minimal"][0]["P"]) < len(old[k]["minimal"][0]["P"])],
               c1_support=len({k for k, _ in c1}), c2_support=c2, n4=n4,
               deaths=deaths, notes=notes)
    json.dump(res, open(os.path.join(G3, "g3_verdicts.json"), "w"), indent=1, default=str)
    print(json.dumps(res, indent=1, default=str)[:6000])


if __name__ == "__main__":
    main()
