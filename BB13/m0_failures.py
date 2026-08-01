#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0(i) of plans/plan-1013.html — Bugeaud Problem 10.13.

Recompute the exact failure set of

    ‖(3/2)^n‖ < (3/4)^n                                                (10.13)

and the associated margin statistics up to n = N (default 10^6).

Method (the Delmer--Deshouillers "(3/2)-side is free" observation, Math. Comp.
54 (1990), 885--893): carry the exact big integer P = 3^n by one multiplication
per step and read the residue off its low bits,

    r_n := 3^n mod 2^n            (odd, so 1 <= r_n <= 2^n - 1),
    D_n := min(r_n, 2^n - r_n)    = 2^n * ‖(3/2)^n‖,

so that (10.13) is the *exact integer* predicate

    D_n * 2^n < 3^n .

The comparison is decided by bit lengths (bitlen(D_n) + n  vs  bitlen(3^n)) and
falls back to a full big-int comparison only on the measure-zero tie, so the
inner loop is one multiply, one mask and O(1) integer arithmetic.

Two-sidedness (plan §2.2 caveat).  Delmer--Deshouillers' (**) is one-sided: it
only tracks runs of 1s.  Problem 10.13 needs both sides, so every record here
carries `side`:

    side = 0  :  r_n small        -> 3^n has a run of ZEROS  in the middle band,
    side = 1  :  2^n - r_n small  -> 3^n has a run of ONES   in the middle band.

Only side 1 is a failure of the Waring condition {(3/2)^n} <= 1 - (3/4)^n behind
g(n) = 2^n + floor((3/2)^n) - 2 ([Bug12] (3.23)/(3.24)), which is what the
verification record (Stemmler / Kubina--Wunderlich / Cumberbatch) certifies.
Problem 10.13 is two-sided, so its failure set is strictly larger; the script
reports both.

Band run length and margin.  With bl := bitlen(D_n),

    ell_n := n - bl        (# of equal bits of 3^n at positions bl .. n-1),
    margin_n := log2(D_n) - (log2 3 - 1) * n .

Failure at n  <=>  margin_n < 0  <=>  ell_n exceeds (2 - log2 3) n ~ 0.41504 n
(up to the O(1) boundary bit that the exact predicate settles).  `ell_n` is the
*band* run length, not the DD/Kubina--Wunderlich quantity l(3^n) (the maximal
run anywhere in the expansion); that one belongs to M0(ii).

Heuristic to check against: ell_n is geometric, P[ell >= L] ~ 2^-L, whence
sum_n 2^(-0.415 n) < oo and the failure set is conjecturally exactly {1,2,3,4}.

Usage:
    python3 m0_failures.py                    # N = 10^6, JSON next to this file
    python3 m0_failures.py -N 100000 --selftest
    python3 m0_failures.py -N 10000 --dump per_n.csv
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

LOG2_3 = math.log2(3.0)
ALPHA = LOG2_3 - 1.0          # 0.5849625007...; log2 of the (3/2)^n threshold
BAND = 2.0 - LOG2_3           # 0.4150374992...; run length needed to fail


def log2_int(x: int) -> float:
    """log2 of a positive int of arbitrary size (float never overflows)."""
    bl = x.bit_length()
    if bl <= 53:
        return math.log2(x)
    return (bl - 53) + math.log2(x >> (bl - 53))


def scan(n_max: int, *, dump=None, report_every: int = 100_000, quiet: bool = False):
    """Single pass n = 1 .. n_max.  Returns the statistics dict."""
    failures = []          # every n with ‖(3/2)^n‖ < (3/4)^n
    records = []           # running maxima of the band run length ell_n
    closest = []           # K smallest normalised margins margin_n / n
    hist = {}              # ell -> count
    side_counts = [0, 0]
    ties = 0               # times the bit-length test was inconclusive
    best_ell = 0
    keep = 32              # size of the `closest` table

    P = 1                  # P = 3^n, carried exactly
    t0 = time.time()

    for n in range(1, n_max + 1):
        P *= 3
        pow2 = 1 << n
        r = P & (pow2 - 1)              # 3^n mod 2^n, odd
        hi = pow2 - r
        if r <= hi:
            D, side = r, 0
        else:
            D, side = hi, 1

        bl = D.bit_length()             # D >= 1 always (r is odd)
        ell = n - bl

        # exact predicate  D * 2^n < 3^n , decided on bit lengths
        lhs_bl = bl + n
        rhs_bl = P.bit_length()
        if lhs_bl < rhs_bl:
            fail = True
        elif lhs_bl > rhs_bl:
            fail = False
        else:
            ties += 1
            fail = (D << n) < P

        margin = log2_int(D) - ALPHA * n

        side_counts[side] += 1
        hist[ell] = hist.get(ell, 0) + 1

        if fail:
            failures.append({"n": n, "side": side, "ell": ell,
                             "margin": margin, "D": str(D)})
        if ell > best_ell:
            best_ell = ell
            records.append({"n": n, "side": side, "ell": ell,
                            "margin": margin, "needed": BAND * n})

        norm = margin / n
        if len(closest) < keep or norm < closest[-1]["norm"]:
            closest.append({"n": n, "side": side, "ell": ell,
                            "margin": margin, "norm": norm})
            closest.sort(key=lambda e: e["norm"])
            del closest[keep:]

        if dump is not None:
            dump.write(f"{n},{side},{ell},{margin:.6f},{int(fail)}\n")

        if not quiet and report_every and n % report_every == 0:
            print(f"  n = {n:>9}  {time.time() - t0:7.1f}s"
                  f"  max ell = {best_ell}  failures = {len(failures)}",
                  file=sys.stderr)

    elapsed = time.time() - t0

    # Heuristic expected number of failures beyond the verified initial segment.
    tail = sum(2.0 ** (-BAND * n) for n in range(5, min(n_max, 4000) + 1))

    return {
        "n_max": n_max,
        "elapsed_sec": elapsed,
        "failure_set": [f["n"] for f in failures],
        "failure_set_zeros_side": [f["n"] for f in failures if f["side"] == 0],
        "failure_set_ones_side": [f["n"] for f in failures if f["side"] == 1],
        "failures": failures,
        "records": records,
        "closest": closest,
        "ell_histogram": {str(k): v for k, v in sorted(hist.items())},
        "side_counts": {"zeros_run": side_counts[0], "ones_run": side_counts[1]},
        "bitlen_ties": ties,
        "band_constant": BAND,
        "heuristic_expected_failures_n_ge_5": tail,
    }


def selftest(n_max: int = 200) -> None:
    """Independent O(n^2) check with exact rationals, n = 1 .. n_max."""
    ref = []
    for n in range(1, n_max + 1):
        x = Fraction(3 ** n, 2 ** n)
        frac = x - x.numerator // x.denominator
        norm = min(frac, 1 - frac)                 # ‖(3/2)^n‖
        if norm < Fraction(3, 4) ** n:
            ref.append(n)
    got = scan(n_max, report_every=0, quiet=True)["failure_set"]
    assert got == ref, f"self-test mismatch: {got} != {ref}"
    print(f"self-test OK to n = {n_max}: failures {ref}")


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-N", "--n-max", type=int, default=10 ** 6)
    ap.add_argument("-o", "--out", default=None,
                    help="JSON output path (default BB13/m0_failures_<N>.json)")
    ap.add_argument("--dump", default=None,
                    help="also write per-n CSV: n,side,ell,margin,fail")
    ap.add_argument("--report-every", type=int, default=100_000)
    ap.add_argument("--selftest", action="store_true",
                    help="cross-check against exact rationals to n = 200 first")
    args = ap.parse_args()

    if args.selftest:
        selftest()

    out = args.out or os.path.join(here, f"m0_failures_{args.n_max}.json")
    dump = open(args.dump, "w") if args.dump else None
    if dump:
        dump.write("n,side,ell,margin,fail\n")
    try:
        stats = scan(args.n_max, dump=dump, report_every=args.report_every)
    finally:
        if dump:
            dump.close()

    with open(out, "w") as fh:
        json.dump(stats, fh, indent=1)

    print(f"\nscanned n = 1 .. {stats['n_max']} in {stats['elapsed_sec']:.1f}s")
    print(f"failure set (10.13, two-sided)  ‖(3/2)^n‖ < (3/4)^n :  "
          f"{stats['failure_set']}")
    print(f"  of which runs of ZEROS: {stats['failure_set_zeros_side']}")
    print(f"  of which runs of ONES : {stats['failure_set_ones_side']}"
          f"   <- the one-sided Waring/(**) event")
    print(f"side counts: run-of-zeros {stats['side_counts']['zeros_run']}, "
          f"run-of-ones {stats['side_counts']['ones_run']} "
          f"(bit-length ties resolved exactly: {stats['bitlen_ties']})")
    print(f"heuristic sum_{{n>=5}} 2^(-{BAND:.5f} n) = "
          f"{stats['heuristic_expected_failures_n_ge_5']:.3e}")

    print("\nrecord band runs (max ell so far)   [side 0 = zeros, 1 = ones]")
    print(f"  {'n':>9}  {'side':>4}  {'ell':>4}  {'needed':>12}  {'margin':>12}")
    for r in stats["records"]:
        print(f"  {r['n']:>9}  {r['side']:>4}  {r['ell']:>4}"
              f"  {r['needed']:>12.1f}  {r['margin']:>12.2f}")

    print("\nsmallest normalised margins  (margin/n; failure iff margin < 0)")
    print(f"  {'n':>9}  {'side':>4}  {'ell':>4}  {'margin':>12}  {'margin/n':>10}")
    for c in stats["closest"][:12]:
        print(f"  {c['n']:>9}  {c['side']:>4}  {c['ell']:>4}"
              f"  {c['margin']:>12.2f}  {c['norm']:>10.5f}")

    print(f"\nwrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
