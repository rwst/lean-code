#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0(ii) of plans/plan-1013.html — Bugeaud Problem 10.13.

Middle-band run-length statistics of the binary expansion of 3^m: the digit-run
engine of plan §2.2, computed exactly and cross-checked against M0(i).

Quantities, per m (bit positions counted from the LSB; L_m := bitlen(3^m)):

    l1(m), l0(m)   maximal run of 1s / of 0s anywhere in 3^m,
    l(m)           = max(l0, l1) — Habsieger's two-sided maximal equal-bit run
                     (Lemma 2); DD 1990 and (**) use the one-sided l1 only,
    band(m)        maximal equal-bit run *inside the middle band*, i.e. the bit
                     positions [ceil(log2(3/2) m), m) of 3^m,
    s2(m)          binary digit sum (plan-A4+ / TH/StewartDigits territory),
    runs(m)        number of maximal blocks = popcount(x ^ (x>>1))  (A4+ "B1
                     transitions"; p-breaks are the block boundaries).

The band has length  W_m = m - ceil(log2(3/2) m) ~ 0.41504 m,  and

    n is a 10.13 failure  <=>  the band is CONSTANT  <=>  band(m) = W_m ,

up to the rounding of the band bottom b0 (the criterion is a proxy; the exact
M0(i) predicate D*2^m < 3^m is computed alongside it and every disagreement is
reported -- there are none up to 10^5).  band(m)/W_m is then the "how close to
failing" ratio.

Three run quantities are routinely conflated and the report separates them:
l1 (anywhere in the expansion) > band(m) (anywhere in the band) > the ANCHORED
run ending at position m, which is M0(i)'s ell_n and the only one that controls
the failure event.  It is also the one Kubina--Wunderlich's record table tracks:
l1 reaches 29 already at m ~ 2*10^4, whereas the anchored run reaches only 17 by
10^5 and 21 by 8.4*10^5 -- consistent with KW's record of 29 at k = 9.26*10^7.

DD 1990 Prop. 1 (propagation, §6): if 3^m has no run of h consecutive 1s then
(**) holds for  m log3/log4 + (h+1)/2 <= k <= m.  One checkpoint therefore
certifies a window of relative width ~1 - log3/log4 = 0.2075, which is the
source of Habsieger's "4 checkpoints per dyadic block".  `--cover` builds the
greedy checkpoint cover from the computed h-values, in both the one-sided (DD,
proved) and two-sided (Habsieger form, *assumed* here — flag for M1/M2) variants.

`--check-quant` tests DD's implicit quantitative form  xi_k >= 2^(-h-1) 3^(k-m)
under both readings of xi (nearest-integer distance, and the one-sided 1-frac),
and reports which reading survives.

Cost is O(N^2) bit operations — unlike M0(i) this does NOT reach 10^6 in an
afternoon.  Default N = 10^5 (~20 s); use --stride to sample a longer range.

Usage:
    python3 m0_runs.py                          # N = 10^5, full report
    python3 m0_runs.py -N 300000 --stride 3
    python3 m0_runs.py -N 20000 --check-quant --selftest
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time

LOG2_3 = math.log2(3.0)
BAND = 2.0 - LOG2_3           # 0.41504...: band width / m, and the failure threshold
LOG3_LOG4 = math.log(3.0) / math.log(4.0)   # 0.79248...: DD Prop. 1 window base


def max_run_ones(x: int) -> int:
    """Length of the longest run of 1 bits in x >= 0."""
    n = 0
    while x:
        x &= x >> 1
        n += 1
    return n


def max_run_zeros(x: int, width: int) -> int:
    """Longest run of 0 bits inside the low `width` bits of x."""
    return max_run_ones(~x & ((1 << width) - 1))


def popcount(x: int) -> int:
    return x.bit_count() if hasattr(x, "bit_count") else bin(x).count("1")


def scan(n_max: int, *, stride: int = 1, report_every: int = 10_000,
         quiet: bool = False):
    """One pass m = 1 .. n_max, carrying 3^m exactly."""
    rec1 = []      # records of l1 (the KW table), l0, l, band
    rec0 = []
    rec2 = []
    recb = []
    best1 = best0 = best2 = bestb = 0
    best_ratio = (0.0, 0)
    hist1, hist0, histb = {}, {}, {}
    h_table = {}   # m -> (l1, l) at sampled m, for the checkpoint cover
    band_rows = []  # (m, band, W, ratio) for the closest 32 to failure
    band_disagree = []   # band criterion vs the exact M0(i) predicate
    rec_anchor = {0: [], 1: []}   # records of the anchored run, per side
    best_anchor = {0: 0, 1: 0}
    s2_min = None
    failures = []

    P = 1
    t0 = time.time()
    for m in range(1, n_max + 1):
        P *= 3
        if m % stride:
            continue

        L = P.bit_length()                      # ~ 1.585 m
        b0 = math.ceil((LOG2_3 - 1.0) * m)      # bottom of the middle band
        W = m - b0                              # band width ~ 0.41504 m
        band_word = (P >> b0) & ((1 << W) - 1)

        l1 = max_run_ones(P)
        l0 = max_run_zeros(P, L)                # top bit is 1, so runs are internal
        l = max(l0, l1)
        b = max(max_run_ones(band_word), max_run_zeros(band_word, W))
        s2 = popcount(P)
        nruns = popcount(P ^ (P >> 1))

        h_table[m] = (l1, l)
        hist1[l1] = hist1.get(l1, 0) + 1
        hist0[l0] = hist0.get(l0, 0) + 1
        histb[b] = histb.get(b, 0) + 1
        if s2_min is None or s2 < s2_min[1]:
            s2_min = (m, s2)

        # exact M0(i) predicate  D * 2^m < 3^m , to audit the band criterion
        r = P & ((1 << m) - 1)
        D = min(r, (1 << m) - r)
        lhs_bl, rhs_bl = D.bit_length() + m, L
        fail = lhs_bl < rhs_bl if lhs_bl != rhs_bl else (D << m) < P
        if fail:
            failures.append({"m": m, "band": b, "W": W,
                             "side": 1 if band_word else 0, "runs": nruns})
        if (b >= W) != fail:                    # rounding of the band bottom
            band_disagree.append({"m": m, "band": b, "W": W, "exact_fail": fail})

        # anchored run: the equal-bit run ending AT position m (M0(i)'s ell_n).
        # This — not l1 or band — is the quantity KW's record table tracks.
        ell = m - D.bit_length()
        side = 1 if r > D else 0
        if ell > best_anchor[side]:
            best_anchor[side] = ell
            rec_anchor[side].append({"m": m, "ell": ell, "side": side,
                                     "needed": BAND * m})

        ratio = b / W if W else 0.0
        if ratio > best_ratio[0]:
            best_ratio = (ratio, m)
        band_rows.append((ratio, m, b, W, s2, nruns))

        if l1 > best1:
            best1 = l1
            rec1.append({"m": m, "l1": l1, "L": L, "needed": BAND * m})
        if l0 > best0:
            best0 = l0
            rec0.append({"m": m, "l0": l0, "L": L, "needed": BAND * m})
        if l > best2:
            best2 = l
            rec2.append({"m": m, "l": l, "L": L, "needed": BAND * m})
        if b > bestb:
            bestb = b
            recb.append({"m": m, "band": b, "W": W, "ratio": b / W})

        if not quiet and report_every and m % report_every == 0:
            print(f"  m = {m:>8}  {time.time() - t0:7.1f}s  max l1 = {best1}"
                  f"  max l = {best2}  max band = {bestb}", file=sys.stderr)

    band_rows.sort(reverse=True)
    elapsed = time.time() - t0
    return {
        "n_max": n_max, "stride": stride, "elapsed_sec": elapsed,
        "records_l1_ones": rec1, "records_l0_zeros": rec0,
        "records_l_two_sided": rec2, "records_band": recb,
        "records_anchored_zeros": rec_anchor[0],
        "records_anchored_ones": rec_anchor[1],
        "hist_l1": {str(k): v for k, v in sorted(hist1.items())},
        "hist_l0": {str(k): v for k, v in sorted(hist0.items())},
        "hist_band": {str(k): v for k, v in sorted(histb.items())},
        "closest_to_failure": [
            {"m": r[1], "band": r[2], "W": r[3], "ratio": r[0],
             "s2": r[4], "runs": r[5]} for r in band_rows[:32]],
        "failures": failures,
        "band_criterion_disagreements": band_disagree,
        "s2_min": {"m": s2_min[0], "s2": s2_min[1]} if s2_min else None,
        "_h_table": h_table,
    }


def greedy_cover(h_table, n_max: int, *, two_sided: bool, start: int = 200):
    """DD Prop. 1 checkpoint cover of [start, n_max].

    `h` in Prop. 1 is a length 3^m has NO run of, so h = maxrun + 1: the
    checkpoint at m certifies all k in [m*log3/log4 + (h+1)/2, m].  Since
    lo >= log3/log4 * m, only m <= (frontier+1)/(log3/log4) can reach down to
    the frontier, which bounds the search exactly.  Everything below `start` is
    the directly verified base range (M0(i) settles it to 10^6).
    """
    idx = 1 if two_sided else 0
    checkpoints = []
    covered = start - 1
    while covered < n_max:
        best_m = None
        hi_search = min(n_max, int((covered + 1) / LOG3_LOG4) + 2)
        for m in range(covered + 1, hi_search + 1):
            if m not in h_table:
                continue
            h = h_table[m][idx] + 1
            if LOG3_LOG4 * m + (h + 1) / 2.0 <= covered + 1:
                best_m = m               # ascending: keep the largest that fits
        if best_m is None:
            return checkpoints, covered, False
        h = h_table[best_m][idx] + 1
        checkpoints.append({"m": best_m, "h": h,
                            "window_lo": LOG3_LOG4 * best_m + (h + 1) / 2.0,
                            "window_hi": best_m})
        covered = best_m
    return checkpoints, covered, True


def check_quantitative(n_max: int, h_table, *, samples: int = 400):
    """Test DD's implicit form  xi_k >= 2^(-h-1) 3^(k-m)  for both readings of xi.

    reading A: xi_k = ‖(3/2)^k‖            (two-sided, Problem 10.13's quantity)
    reading B: xi_k = 1 - {(3/2)^k}        (one-sided, the (**)/Waring quantity)
    """
    ms = [m for m in sorted(h_table) if m >= 20][-samples:]
    bad = {"A": [], "B": []}
    tested = 0
    for m in ms:
        h1 = h_table[m][0] + 1      # DD's h = 'no run of h ones' = maxrun + 1
        P3m = 3 ** m
        lo = math.ceil(LOG3_LOG4 * m + (h1 + 1) / 2.0)
        step = max(1, (m - lo) // 8)
        for k in range(max(lo, 1), m + 1, step):
            P3k = 3 ** k
            den = 1 << k
            r = P3k & (den - 1)
            hi = den - r
            # xi = num/den >= 2^-(h1+1) 3^(k-m)  <=>  num * 2^(h1+1) * 3^m >= den * 3^k
            for name, num in (("A", min(r, hi)), ("B", hi)):
                if num * (1 << (h1 + 1)) * P3m < den * P3k:
                    bad[name].append({"m": m, "k": k, "h": h1})
            tested += 1
    return {"tested_pairs": tested,
            "violations_A_nearest_integer": bad["A"][:10],
            "violations_B_one_sided": bad["B"][:10],
            "count_A": len(bad["A"]), "count_B": len(bad["B"])}


def selftest() -> None:
    assert max_run_ones(0b1011101111) == 4
    assert max_run_ones(0) == 0
    assert max_run_zeros(0b10001001, 8) == 3
    assert popcount(0b1011101111) == 8
    # 3^7 = 2187 = 0b100010001011 : band for m=7 is bits [5,7) = 0b00
    P = 3 ** 7
    b0 = math.ceil((LOG2_3 - 1.0) * 7)
    W = 7 - b0
    band = (P >> b0) & ((1 << W) - 1)
    assert band == 0 and W == 2, (band, W, b0)   # constant band = the n=7 failure
    print("self-test OK (run primitives; n=7 band is constant, matching M0(i))")


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-N", "--n-max", type=int, default=100_000)
    ap.add_argument("--stride", type=int, default=1)
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--report-every", type=int, default=10_000)
    ap.add_argument("--cover-start", type=int, default=200,
                    help="frontier below which the range is verified directly")
    ap.add_argument("--cover", action="store_true",
                    help="build the DD Prop. 1 greedy checkpoint cover")
    ap.add_argument("--check-quant", action="store_true",
                    help="test DD's implicit bound xi_k >= 2^(-h-1) 3^(k-m)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        selftest()

    stats = scan(args.n_max, stride=args.stride, report_every=args.report_every)
    h_table = stats.pop("_h_table")

    if args.cover:
        for two in (False, True):
            cps, covered, ok = greedy_cover(h_table, args.n_max, two_sided=two,
                                            start=args.cover_start)
            key = "cover_two_sided" if two else "cover_one_sided"
            stats[key] = {"checkpoints": len(cps), "covered_to": covered,
                          "complete": ok,
                          "per_dyadic_block": len(cps) / math.log2(max(args.n_max, 2)),
                          "list": cps[:40]}
    if args.check_quant:
        stats["quantitative_check"] = check_quantitative(args.n_max, h_table)

    out = args.out or os.path.join(here, f"m0_runs_{args.n_max}.json")
    with open(out, "w") as fh:
        json.dump(stats, fh, indent=1)

    print(f"\nscanned m = 1 .. {stats['n_max']} (stride {stats['stride']}) "
          f"in {stats['elapsed_sec']:.1f}s")
    print(f"exact 10.13 failures in range: {[f['m'] for f in stats['failures']]}"
          f"   (band-criterion disagreements, from rounding the band bottom: "
          f"{len(stats['band_criterion_disagreements'])})")

    print("\nrecord maximal runs in 3^m  [l1 = ones (DD/(**)), "
          "l0 = zeros, l = two-sided (Habsieger)]")
    print(f"  {'m':>8}  {'l1':>4}      {'m':>8}  {'l0':>4}      {'m':>8}  {'l':>4}")
    for a, b, c in zip(stats["records_l1_ones"][-8:],
                       stats["records_l0_zeros"][-8:],
                       stats["records_l_two_sided"][-8:]):
        print(f"  {a['m']:>8}  {a['l1']:>4}      {b['m']:>8}  {b['l0']:>4}"
              f"      {c['m']:>8}  {c['l']:>4}")
    last = stats["records_l_two_sided"][-1]
    print(f"  two-sided record l = {last['l']} at m = {last['m']}, "
          f"vs {BAND * last['m']:.0f} needed to fail "
          f"(log2 of expansion length = {math.log2(LOG2_3 * last['m']):.1f})")

    # Three DIFFERENT run quantities, routinely conflated in the literature.
    ra1 = stats["records_anchored_ones"][-1] if stats["records_anchored_ones"] else None
    ra0 = stats["records_anchored_zeros"][-1] if stats["records_anchored_zeros"] else None
    rb = stats["records_band"][-1] if stats["records_band"] else None
    print("\ncalibration — three distinct quantities (do not conflate):")
    r1 = stats["records_l1_ones"][-1]
    print(f"  whole expansion, max run of 1s   l1 = {r1['l1']:>3} "
          f"(record at m = {r1['m']})")
    if rb:
        print(f"  inside the middle band           b  = {rb['band']:>3} "
              f"(record at m = {rb['m']})")
    if ra1:
        print(f"  ANCHORED at position m, ones     e1 = {ra1['ell']:>3} "
              f"(record at m = {ra1['m']})   <- KW's record table")
    if ra0:
        print(f"  ANCHORED at position m, zeros    e0 = {ra0['ell']:>3} "
              f"(record at m = {ra0['m']})")
    print("  Only the anchored run controls the failure event; it runs ~8 bits\n"
          "  behind l1 at these sizes, so margins quoted from l1 are not KW's.")

    print("\nclosest the middle band came to being constant (ratio = band/W)")
    print(f"  {'m':>8}  {'band':>5}  {'W':>7}  {'ratio':>7}  {'s2':>7}  {'runs':>7}")
    for r in stats["closest_to_failure"][:10]:
        print(f"  {r['m']:>8}  {r['band']:>5}  {r['W']:>7}  {r['ratio']:>7.4f}"
              f"  {r['s2']:>7}  {r['runs']:>7}")

    if args.cover:
        for key, label in (("cover_one_sided", "one-sided (DD Prop. 1, proved)"),
                           ("cover_two_sided", "two-sided (Habsieger form, ASSUMED)")):
            c = stats[key]
            print(f"\nDD checkpoint cover, {label}: {c['checkpoints']} checkpoints "
                  f"for [{args.cover_start}, {c['covered_to']}] "
                  f"({c['per_dyadic_block']:.2f} per dyadic block; DD/Habsieger "
                  f"report 4), complete = {c['complete']}")
    if args.check_quant:
        q = stats["quantitative_check"]
        print(f"\nDD quantitative form on {q['tested_pairs']} (m,k) pairs: "
              f"violations — reading A (‖·‖) {q['count_A']}, "
              f"reading B (1-frac) {q['count_B']}")

    print(f"\nwrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
