#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# g3.py -- plan-dubC2 milestone M1: the G-3 calibration gate.
#
# Runs the reference engine (joint.py) and the independent engine (joint.c) on
# every known answer in the literature, over a ladder in the cell depth k and
# the q-adic depth K, and diffs every reported number.  M1's exit condition is
# that all of this passes; the plan's wording is "G-3 passes bit-for-bit".
#
#   (a) the branch table and the two-letter interval computation   [done at G-4]
#   (b) [DN05] Thm 4(ii)   5/3, nu=1/2, P = {2,3}
#   (c) [DN05] Thm 4(iii)  7/5, nu=1/2, P = {2,3,5,11}
#   (d) [DN05] Thm 1 / [FS67]  floor 3/2, nu=0, P = {2,5,7,11}
#
# and, since the same engine must be run on the open case to mean anything,
#   (t) the target        3/2, nu=1/2, P = {2,5,7,11}
#
# Usage:  ./g3.py [--quick] [--target-only]

import json
import subprocess
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
PY = [sys.executable, os.path.join(HERE, "joint.py")]
C = [os.path.join(HERE, "joint")]

# fields both implementations report
SHARED = ["nodes_total", "edges_total", "core_nodes", "core_edges", "sccs",
          "cyclic_sccs", "largest_cyclic", "branch_nodes", "branch_sccs",
          "all_simple", "verdict", "det_states", "det_verdict"]
FLOAT = ["lam", "det_lam"]

CASES = [
    ("G-3(b) [DN05] Thm 4(ii)  5/3 nearest, P={2,3}",
     dict(pq=(5, 3), nu="1/2", P="2,3"), [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4)]),
    ("G-3(c) [DN05] Thm 4(iii) 7/5 nearest, P={2,3,5,11}",
     dict(pq=(7, 5), nu="1/2", P="2,3,5,11"), [(2, 2), (2, 3), (2, 4), (3, 3)]),
    ("G-3(d) [DN05] Thm 1 / [FS67]  3/2 floor, P={2,5,7,11}",
     dict(pq=(3, 2), nu="0", P="2,5,7,11"), [(2, 4), (2, 6), (2, 8), (2, 10), (3, 8), (4, 8)]),
    ("TARGET  3/2 nearest (nu=1/2), P={2,5}   -- the M1 candidate certificate",
     dict(pq=(3, 2), nu="1/2", P="2,5"),
     [(2, 3), (2, 4), (2, 6), (2, 8), (2, 10), (2, 12), (3, 8), (4, 8), (5, 6)]),
    ("        3/2 nearest (nu=1/2), P={2,5,7,11}  -- the [FS67]-shaped set",
     dict(pq=(3, 2), nu="1/2", P="2,5,7,11"), [(2, 3), (2, 4), (2, 6), (2, 8), (2, 10), (3, 8), (4, 8)]),
    ("CONTROL 3/2 nearest (nu=1/2), P={2,7}   -- must FAIL at every rung",
     dict(pq=(3, 2), nu="1/2", P="2,7"), [(2, 4), (2, 6), (2, 8), (3, 6)]),
]


def run(cmd, case, K, k):
    a = cmd + ["--pq", str(case["pq"][0]), str(case["pq"][1]), "--nu", case["nu"],
               "--P", case["P"], "--K", str(K), "--k", str(k), "--det", "--summary"]
    out = subprocess.run(a, capture_output=True, text=True, timeout=7200)
    if out.returncode:
        raise RuntimeError(" ".join(a) + "\n" + out.stderr[-2000:])
    return json.loads(out.stdout.strip().splitlines()[-1])


def main():
    quick = "--quick" in sys.argv
    only_t = "--target-only" in sys.argv
    bad = 0
    for title, case, rungs in CASES:
        if only_t and not title.startswith("TARGET"):
            continue
        print("=" * 100)
        print(title)
        print(f"{'K':>2} {'k':>2} {'D':>8} {'nodes':>10} {'core':>7} {'cyc':>5} "
              f"{'lam':>10} {'state verdict':<12} {'detN':>6} {'det lam':>8} "
              f"{'det verdict':<16} agree")
        for K, k in (rungs[:2] if quick else rungs):
            rp = run(PY, case, K, k)
            rc = run(C, case, K, k)
            ok = all(str(rp.get(f)).lower() == str(rc.get(f)).lower() for f in SHARED)
            for f in FLOAT:
                x, y = float(rp.get(f, 0)), float(rc.get(f, 0))
                ok &= abs(x - y) <= 1e-9 * max(1.0, abs(x))
            if not ok:
                bad += 1
                diff = {f: (rp.get(f), rc.get(f)) for f in SHARED + FLOAT
                        if str(rp.get(f)).lower() != str(rc.get(f)).lower()}
            print(f"{K:>2} {k:>2} {rp['D']:>8} {rp['nodes_total']:>10} "
                  f"{rp['core_nodes']:>7} {rp['cyclic_sccs']:>5} {rp['lam']:>10.6f} "
                  f"{rp['verdict']:<12} {rp['det_states']:>6} "
                  f"{rp.get('det_lam', 0):>8.5f} {rp['det_verdict']:<16} "
                  f"{'OK' if ok else 'MISMATCH ' + json.dumps(diff)}")
    print("=" * 100)
    print("G-3 two-implementation agreement:", "PASS" if bad == 0 else f"{bad} MISMATCHES")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
