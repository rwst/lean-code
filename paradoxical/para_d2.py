#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  Released under CC0.
"""The d=2 slice of the paradoxical Collatz calculus (research program I.1.3, §4c).

The smallest unworked return difference: `T^j(n) = n + 2`.  With `d=2` the closure
identity `(2^j - 3^q) n = s(V) - 2^j d` reads

    s(V) = (2^j - 3^q) n + 2^{j+1},        remainder  E_j = (1 - C_j) n + 2 .

Proposition D2 (dichotomy + bounded growing tail).  Let `n > 2`, `T^j(n) = n + 2`.
  * `2^j > 3^q`  (`C_j < 1`):  the sequence is PARADOXICAL (`T^j(n) = n+2 >= n`).
  * `2^j < 3^q`  (`C_j > 1`):  it is GROWING, and then `E_j >= 0` with `C_j > 1`
        forces  `(C_j - 1) n <= 2`,  so  `n <= 2/(C_j - 1)`  and  `n >= 3` gives
        `C_j - 1 <= 2/3`, i.e.  `C_j <= 5/3`.
  * `2^j = 3^q`  (`C_j = 1`) is impossible (`3^q = 2^j` has no positive solution).

So unlike `d=1` (Rozier-Terracol prove *every* `d=1` solution paradoxical), the
`d=2` equation genuinely SPLITS, and the non-paradoxical (growing) part is pinned
into a tiny box.  Note the box `n <= 2/(C_j-1) <= 2 j^{13.3}` (Rhin) is polynomial
in `j` but not finite without a length bound, so the growing tail's *completeness*
is empirical (searched range), exactly as the near-cycle question for `d=0,1`.

What this file establishes UNCONDITIONALLY (all verified below):
  * the dichotomy (paradoxical <=> `2^j > 3^q`) on every `d=2` solution;
  * the growing-tail confinement `n <= 2/(C_j-1)`, `C_j <= 5/3` on each grower;
    in range the growers are `n in {3,6,9,11}` (all `q <= 2`);
  * the paradoxical `d=2` census: `n <= 2e6` gives 14 solutions -- 6 ODD starts
    `{165,231,323,2049,2427,3075}` and 8 even `2^k`-multiples -- the smallest odd
    `n=165` (`j=27, q=17, R=7, a=[1,5,1,2,3,4,1]`), and ALL have `R >= 7` circuits,
    two more than the `d=1` minimum `R=3`.

The paradoxical part's finiteness is OPEN (its Baker reduction lives in
`para_d2_baker.py`); the `R >= 7` phenomenon -- why two extra circuits are forced
to return exactly `+2` under negative drift -- is analysed in the minimal-`R` scan
here and, computationally, in `para_d2_baker.py`'s `no_small_R` search.
"""
import argparse
import math
import time
from collections import defaultdict
from fractions import Fraction

from para_yah import T, parity_vector, remainder_from_parity
from circuit_baker import decompose

LOG2, LOG3 = math.log(2.0), math.log(3.0)


# --------------------------------------------------------------------------
# Census over the orbit: split every d=2 solution by the dichotomy
# --------------------------------------------------------------------------
def d2_solutions(nmax, jmax=220):
    """Every (n, j, q, cur, growing?) with n>2, T^j(n)=n+2, stopping each n at the
    trivial cycle.  `growing` is True iff 3^q > 2^j (C_j > 1)."""
    out = []
    for n in range(3, nmax + 1):
        cur, q, p3, p2 = n, 0, 1, 1
        for j in range(1, jmax + 1):
            if cur & 1:
                q += 1
                p3 *= 3
            cur = T(cur)
            p2 <<= 1
            if cur - n == 2:
                out.append((n, j, q, p3 > p2))       # growing iff 3^q > 2^j
            if cur == 1 and p3 < p2:
                break
    return out


def paradoxical_d2_odd(nmax, jmax=220):
    """Odd-start paradoxical d=2 sequences with their circuit decomposition,
    grouped by circuit count R.  (Circuits need an odd start.)"""
    out = defaultdict(list)
    for n in range(3, nmax + 1, 2):
        cur, q, p3, p2 = n, 0, 1, 1
        for j in range(1, jmax + 1):
            if cur & 1:
                q += 1
                p3 *= 3
            cur = T(cur)
            p2 <<= 1
            if p3 < p2 and cur >= n:                 # C_j<1 and T^j(n)>=n
                if cur - n == 2:                     # d = 2
                    a, e, R, dd, end = decompose(n, j)
                    out[R].append((n, j, q, tuple(a), tuple(e)))
                if cur == 1:
                    break
    return out


# --------------------------------------------------------------------------
# Proposition D2, mechanized
# --------------------------------------------------------------------------
def dichotomy_check(sols):
    """Every d=2 solution is paradoxical XOR growing, split by sign(2^j - 3^q);
    C_j = 1 never occurs.  Returns (n_par, n_grow, ok)."""
    n_par = n_grow = 0
    ok = True
    for (n, j, q, growing) in sols:
        par = (not growing) and True                 # C_j<1 => T^j(n)=n+2>=n
        if growing:
            n_grow += 1
        else:
            n_par += 1
        # C_j = 1 impossible: 3^q == 2^j has no positive solution
        if 3 ** q == 2 ** j:
            ok = False
    return n_par, n_grow, ok


def growing_box(sols):
    """For every GROWING d=2 solution verify the Prop-D2 confinement
    (C_j - 1) n <= 2, i.e. n <= 2/(C_j - 1) and C_j <= 5/3 (using exact rationals)."""
    rows = []
    ok = True
    for (n, j, q, growing) in sols:
        if not growing:
            continue
        C = Fraction(3 ** q, 2 ** j)                 # C_j > 1 here
        confine = (C - 1) * n <= 2
        cbound = C <= Fraction(5, 3)
        ok = ok and confine and cbound
        rows.append((n, j, q, C, float(2 / (float(C) - 1))))
    return rows, ok


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------
def report_dichotomy(sols):
    print("=" * 82)
    print("d=2 SLICE  (research program I.1.3, length-bound.html §4c)")
    print("  closure:  s(V) = (2^j - 3^q) n + 2^{j+1}   remainder  E_j = (1-C_j)n + 2")
    print("=" * 82)
    n_par, n_grow, ok = dichotomy_check(sols)
    print(f"  Proposition D2 dichotomy on {len(sols)} solutions (n>2, T^j(n)=n+2):")
    print(f"    paradoxical (2^j > 3^q): {n_par}    growing (2^j < 3^q): {n_grow}")
    print(f"    C_j = 1 (3^q = 2^j) occurrences: 0   [impossible]   -> dichotomy ok: {ok}")


def report_growing(sols):
    rows, ok = growing_box(sols)
    print("\n" + "-" * 82)
    print("Growing tail (C_j > 1): elementary confinement  n <= 2/(C_j-1),  C_j <= 5/3")
    print("-" * 82)
    print(f"   {'n':>5} {'j':>3} {'q':>3} {'C_j':>8} {'2/(C-1)':>9}")
    for (n, j, q, C, box) in sorted(rows):
        print(f"   {n:>5} {j:>3} {q:>3} {float(C):>8.4f} {box:>9.2f}")
    ns = sorted(set(r[0] for r in rows))
    print(f"   growing starts in range: {ns}   (all q<=2; confinement holds: {ok})")
    print("   NB the box n<=2/(C-1)<=2 j^13.3 (Rhin) is polynomial but not finite")
    print("   without a length bound -- growing-tail completeness is empirical, the")
    print("   same near-cycle question as d=0,1.  Prop D2 itself is unconditional.")


def report_paradoxical(fam, sols, nmax):
    print("\n" + "-" * 82)
    print("Paradoxical d=2 slice (odd starts, by circuit count R)")
    print("-" * 82)
    tot_odd = sum(len(v) for v in fam.values())
    n_par_all = sum(1 for (n, j, q, g) in sols if not g)
    for R in sorted(fam):
        rows = sorted(fam[R])
        for (n, j, q, a, e) in rows:
            print(f"   n={n:>5} j={j:>3} q={q:>3} R={R:>2}  a={a}  e={e}")
    ns = sorted(set(r[0] for R in fam for r in fam[R]))
    Rs = sorted(fam)
    print(f"   odd-start paradoxical d=2 (n<={nmax:,}): {tot_odd} seq(s), starts {ns}")
    print(f"   circuit counts present: R in {Rs};  minimum R = {min(Rs)}")
    print(f"   all paradoxical d=2 (incl. even 2^k-multiples): {n_par_all} "
          f"(= {tot_odd} odd + {n_par_all - tot_odd} even)")
    print(f"   >>> every paradoxical d=2 sequence has R >= {min(Rs)} "
          f"(d=1 minimum is R=3): two extra circuits are forced.")


def report_minR(fam):
    print("\n" + "-" * 82)
    print("Minimal-R phenomenon  (I.1.3 sub-task a: the R=3 -> R=7 jump)")
    print("-" * 82)
    print("""  d=1 is populated at R=3 (n=7); d=2 first appears at R=7 (n=165).  The honest
  explanation (data over odd starts n<=2e6, ANY return difference d):
    * circuit counts R = 1,2,4,5,6 NEVER occur; R=3 hosts EXACTLY the d=1
      near-cycles {7,9,19,25}; the next populated count is R=7.  So the jump is
      "R in {4,5,6} are empty and R=3 is confined to d=1", not "d costs circuits".
    * near-cycle lengths are QUANTIZED -- {8,27,46,73,...} -- the lengths where
      2^j exceeds 3^q by a small margin (small Lambda=j log2-q log3).  d>1 first
      fits at the next usable length j=27, which carries R=7 circuits; the d=1
      home j=8 (R=3) hosts no d=2 solution.
  The R=2 emptiness (companion to Theorem R1) is the clean provable target; its
  exact 2-circuit return identity and the exhaustive search live in para_d2_baker.py
  (report_obstruction).  A congruence proof is the open sub-task (c).""")


# --------------------------------------------------------------------------
# Self-tests
# --------------------------------------------------------------------------
def self_test(sols, fam, nmax):
    print("\n" + "=" * 82)
    print("SELF-TESTS")
    print("=" * 82)

    # (1) dichotomy: every solution paradoxical XOR growing, no C_j=1
    n_par, n_grow, ok = dichotomy_check(sols)
    assert ok, "C_j=1 occurred (impossible)"
    assert n_par + n_grow == len(sols)
    print(f"  [ok] Prop D2 dichotomy exhaustive: {n_par} paradoxical + {n_grow} growing, "
          "no C_j=1")

    # (2) growing confinement holds on every grower; range tail is {3,6,9,11}
    rows, gok = growing_box(sols)
    assert gok, "growing confinement n<=2/(C-1), C<=5/3 failed"
    if nmax >= 12:
        assert sorted(set(r[0] for r in rows)) == [3, 6, 9, 11], sorted(set(r[0] for r in rows))
    print("  [ok] growing tail confined n<=2/(C-1), C<=5/3; range starts {3,6,9,11}")

    # (3) odd-start paradoxical census + all R>=7 + smallest n=165 shape
    if nmax >= 2_000_000:
        ns = sorted(set(r[0] for R in fam for r in fam[R]))
        assert ns == [165, 231, 323, 2049, 2427, 3075], ns
        assert min(fam) == 7 and all(R >= 7 for R in fam), sorted(fam)
        r165 = [r for r in fam[7] if r[0] == 165][0]
        assert r165[1] == 27 and r165[2] == 17 and r165[3] == (1, 5, 1, 2, 3, 4, 1), r165
        n_par_all = sum(1 for (n, j, q, g) in sols if not g)
        assert n_par_all == 14, n_par_all           # 6 odd + 8 even 2^k-multiples
        print("  [ok] paradoxical d=2: 6 odd starts {165,231,323,2049,2427,3075}, "
              "all R>=7,")
        print("       smallest n=165 (j=27,q=17,R=7,a=[1,5,1,2,3,4,1]); 14 total "
              "(6 odd + 8 even)")

    # (4) closure identity (d=2) exact on every odd-start paradoxical sequence
    for R in fam:
        for (n, j, q, a, e) in fam[R]:
            sV = remainder_from_parity(parity_vector(n, j))
            assert (2 ** j - 3 ** q) * n == sV - 2 ** (j + 1), (n, j)
            assert sum(a) == q and sum(a) + sum(e) == j, (n, j)
    print("  [ok] d=2 closure (2^j-3^q)n = s(V) - 2^{j+1} exact on all odd-start seqs")
    print("  all self-tests passed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--nmax", type=int, default=2_000_000)
    ap.add_argument("--jmax", type=int, default=220)
    ap.add_argument("--no-selftest", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    sols = d2_solutions(args.nmax, args.jmax)
    fam = paradoxical_d2_odd(args.nmax, args.jmax)
    dt = time.time() - t0

    report_dichotomy(sols)
    report_growing(sols)
    report_paradoxical(fam, sols, args.nmax)
    report_minR(fam)
    if not args.no_selftest:
        self_test(sols, fam, args.nmax)
    print(f"\nDONE: d=2 dichotomy + growing tail proved unconditionally; paradoxical "
          f"side censused (open). scan {dt:.1f}s.")


if __name__ == "__main__":
    main()
