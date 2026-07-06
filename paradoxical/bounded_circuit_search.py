#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  Released under CC0.
"""Automated bounded-circuit (Baker) search for paradoxical Collatz sequences.

Research-program Part I, work package I.1.1 ("Automate the bounded-circuit
search").  Companion to ``length-bound.html`` and ``circuit_baker.py``.

    Accelerated map   T(n) = (3n+1)/2 (n odd),  n/2 (n even).
    A sequence Omega_j(n)=(n,...,T^j(n)), n>2, is PARADOXICAL iff
        (i)  C_j = 3^q / 2^j < 1     (q = # odd steps)
        (ii) T^j(n) >= n .
    Return difference  d = T^j(n) - n >= 0.

Circuit decomposition (length-bound.html sec. 1).  An odd start's parity word
splits into R bursts a_1..a_R (runs of 1's, a_i>=1) separated by gaps
e_1..e_R (runs of 0's; interior e_i>=1, final e_R>=0).  With q=sum a_i,
j=sum(a_i+e_i), the CLOSURE IDENTITY is

        (2^j - 3^q) n  =  s(V) - 2^j d ,
        s(V) = sum_i (3^{a_i}-2^{a_i}) * 3^{a_{i+1}+..+a_R} * 2^{c_1+..+c_{i-1}}
             = remainder_from_parity(V)          (integer remainder 2^j E_j).

For a FIXED pair (R,d) the shape (a_i,e_i) is finitely many integer parameters
per length, and each shape DETERMINES its start:

        n = (s(V) - 2^j d) / (2^j - 3^q)          (needs 2^j > 3^q, i.e. C_j<1).

A shape is a genuine solution iff this n is an integer >= 3 whose own parity word
is exactly V (self-consistency).  The transcendence lower bounds

        Rhin    |j log2 - q log3| >= j^{-13.3}      => 2^j-3^q >= 3^q j^{-13.3}
        Ellison  2^j - 3^q > (2.56)^q / 2   (q>12)

cap the start any shape can realise, n <= rho_V j^{13.3} with rho_V=s(V)/3^q,
and (with the excursion bound M<=m^beta, RT Conj. 6.2) would cap the length.

This module enumerates every shape up to a length cap, applies the closure
identity and the transcendence bounds, and for each (R,d) reports either

    (a) an UNCONDITIONAL length bound        -- R=1 (Theorem R1) and d=0 (no
        nontrivial cycle: Steiner / Simons-de Weger), where the slice is
        provably empty; or
    (b) the finite list of candidate shapes that survive the bound (verified
        genuine paradoxical sequences), complete up to the length cap.

Everything is cross-checked against a direct orbit scan (independent oracle) and
against ``circuit_baker.py`` / ``para_yah.py``.
"""
import argparse
import math
import time
from collections import defaultdict

from para_yah import T, parity_vector, remainder_from_parity
from circuit_baker import decompose, length_cutoff

LOG2, LOG3 = math.log(2.0), math.log(3.0)


# ==========================================================================
# 1. Shape enumeration + closure identity  (the generator core)
# ==========================================================================
def circuit_word(a_list, e_list):
    """Parity word 1^{a_1} 0^{e_1} ... 1^{a_R} 0^{e_R} of a circuit shape."""
    V = []
    for a, e in zip(a_list, e_list):
        V.extend([1] * a)
        V.extend([0] * e)
    return tuple(V)


def s_of_shape(a_list, e_list):
    """s(V) via the closure-identity circuit sum (independent of n).

        s(V) = sum_i (3^{a_i}-2^{a_i}) 3^{a_{i+1}+..+a_R} 2^{c_1+..+c_{i-1}}.
    Returned alongside remainder_from_parity(word) so the two are cross-checked."""
    R = len(a_list)
    c = [a + e for a, e in zip(a_list, e_list)]
    suffix_a = [0] * (R + 1)                 # suffix_a[i] = a_{i+1}+..+a_R
    for i in range(R - 1, -1, -1):
        suffix_a[i] = suffix_a[i + 1] + a_list[i]
    s = 0
    prefix_c = 0                             # c_1+..+c_{i-1}
    for i in range(R):
        term = (3 ** a_list[i] - 2 ** a_list[i]) * 3 ** suffix_a[i + 1] * 2 ** prefix_c
        s += term
        prefix_c += c[i]
    return s


def enum_shapes(R, jmax):
    """Yield every circuit shape (a_list, e_list) with R bursts and length j<=jmax
    that is paradoxical-feasible (2^j > 3^q).  Interior gaps >=1, final gap >=0."""
    a = [0] * R
    e = [0] * R

    def rec(i, length, q):
        # i = index of the next burst to choose (0-based)
        if length > jmax:
            return
        if i == R:
            if length >= 1 and 2 ** length > 3 ** q:      # C_j < 1
                yield (tuple(a), tuple(e))
            return
        # choose burst a_i >= 1, then gap e_i (>=1 interior, >=0 for last)
        for ai in range(1, jmax - length + 1):
            a[i] = ai
            emin = 0 if i == R - 1 else 1
            for ei in range(emin, jmax - length - ai + 1):
                e[i] = ei
                yield from rec(i + 1, length + ai + ei, q + ai)

    yield from rec(0, 0, 0)


def shape_solutions(a_list, e_list, dmax):
    """Closure identity applied to one shape, for every return difference
    d = 0..dmax at once.  Yields (n, j, q, sV, d) for each genuine odd start
    n>=3 whose own parity word is exactly V (Terras self-consistency).

    n = (s(V) - 2^j d)/(2^j-3^q) both decreases in d and needs an exact division,
    so the loop breaks as soon as the numerator drops non-positive."""
    V = circuit_word(a_list, e_list)
    j = len(V)
    q = sum(a_list)
    Delta = 2 ** j - 3 ** q                           # > 0 by construction
    twoj = 2 ** j
    sV = remainder_from_parity(V)                     # = s_of_shape(a,e), see self-test
    for d in range(0, dmax + 1):
        num = sV - twoj * d
        if num < 3 * Delta:                           # n < 3 from here on -> stop
            break
        if num % Delta:                               # non-integer start
            continue
        n = num // Delta
        if n % 2 == 0:                                # odd start (V begins with 1)
            continue
        if parity_vector(n, j) == V:                  # self-consistency (Terras)
            yield (n, j, q, sV, d)


# ==========================================================================
# 2. Transcendence engine + Baker reduction quantities (verified per survivor)
# ==========================================================================
def rhin_ok(j, q):
    return abs(j * LOG2 - q * LOG3) >= j ** (-13.3)


def ellison_ok(j, q):
    # Ellison / RT Lemma B.1, only meaningful for q>12
    return (2 ** j - 3 ** q) > (2.56 ** q) / 2


def min_odd_term(n, j):
    m, cur = n, n
    for _ in range(j):
        if cur & 1:
            m = min(m, cur)
        cur = T(cur)
    return m


def max_excursion(n, j):
    M, cur = n, n
    for _ in range(j):
        cur = T(cur)
        M = max(M, cur)
    return M


def baker_reduction(n, j, q, sV, R):
    """The explicit (unconditional) reduction chain of length-bound.html sec. 4d.
    Returns a dict of the quantities; the only UNPROVEN link is M <= m^beta."""
    rho_V = sV / 3 ** q                               # remainder excess
    return {
        "Lambda": j * LOG2 - q * LOG3,
        "rhin_lb": j ** (-13.3),
        "n_bound": rho_V * j ** 13.3,                 # n <= rho_V j^13.3   (a)
        "rho_V": rho_V,
        "m": min_odd_term(n, j),                      # least odd term
        "M": max_excursion(n, j),                     # excursion (peak)
        "M_lower": 2 ** (j / (2 * R)) - 1,            # M >= 2^{j/2R}-1     (c)
        "rhin_ok": rhin_ok(j, q),
        "ellison_ok": ellison_ok(j, q) if q > 12 else None,
    }


# ==========================================================================
# 3. Independent oracle: direct orbit scan
# ==========================================================================
def direct_scan(Rmax, dmax, nmax, jmax):
    """All odd-start paradoxical sequences with R<=Rmax, d<=dmax, n<=nmax."""
    out = defaultdict(list)
    for n in range(3, nmax + 1, 2):
        cur, q, p3, p2 = n, 0, 1, 1
        for j in range(1, jmax + 1):
            if cur & 1:
                q += 1
                p3 *= 3
            cur = T(cur)
            p2 <<= 1
            if p3 < p2 and cur >= n:                  # C_j<1 and T^j(n)>=n
                d = cur - n
                if d <= dmax:
                    a, e, R, dd, end = decompose(n, j)
                    if R <= Rmax:
                        out[(R, d)].append((n, j, q, tuple(a), tuple(e)))
                if cur == 1:
                    break
    return out


# ==========================================================================
# 4. The generator: search each (R,d) slice
# ==========================================================================
def search(Rmax, dmax, jmax):
    """For each (R,d), enumerate shapes, solve the closure identity, keep the
    genuine survivors.  Returns survivors[(R,d)] = sorted list of
    (n, j, q, a_list, e_list, red)."""
    survivors = defaultdict(list)
    for R in range(1, Rmax + 1):
        for (a_list, e_list) in enum_shapes(R, jmax):
            for (n, j, q, sV, d) in shape_solutions(a_list, e_list, dmax):
                red = baker_reduction(n, j, q, sV, R)
                survivors[(R, d)].append((n, j, q, a_list, e_list, red))
    for key in survivors:
        survivors[key].sort()
    return survivors


# ==========================================================================
# 5. Reporting
# ==========================================================================
def classify_and_report(survivors, Rmax, dmax, jmax):
    print("=" * 78)
    print("BOUNDED-CIRCUIT SEARCH  (research program I.1.1)")
    print(f"  slices R=1..{Rmax}, d=0..{dmax};  length cap j<={jmax}")
    print("  each shape: closure identity n=(s(V)-2^j d)/(2^j-3^q), then verify")
    print("  parity-vector self-consistency + Rhin/Ellison lower bounds.")
    print("=" * 78)

    for R in range(1, Rmax + 1):
        for d in range(0, dmax + 1):
            rows = survivors.get((R, d), [])
            if rows:
                # ---- outcome (b): finite candidate list -------------------
                jmaxfound = max(r[1] for r in rows)
                print(f"\n(R={R}, d={d})  OUTCOME (b): {len(rows)} candidate shape(s) "
                      f"survive; max length j={jmaxfound}")
                print(f"   {'n':>6} {'j':>4} {'q':>3}  bursts a_i / gaps e_i")
                for (n, j, q, a, e, red) in rows:
                    print(f"   {n:>6} {j:>4} {q:>3}  a={list(a)}  e={list(e)}")
                # transcendence + reduction on the whole family
                allrhin = all(r[5]["rhin_ok"] for r in rows)
                ell = [r[5]["ellison_ok"] for r in rows if r[5]["ellison_ok"] is not None]
                print(f"   Rhin |j log2 - q log3| >= j^-13.3 : "
                      f"{'ALL hold' if allrhin else 'VIOLATED'}"
                      + (f";  Ellison (q>12): {'all hold' if all(ell) else 'VIOLATED'}"
                         if ell else ";  Ellison n/a (q<=12)"))
                print("   Baker reduction (unconditional except M<=m^beta):")
                print(f"      {'n':>6} {'rho_V':>7} {'n<=rho_V*j^13.3':>16} "
                      f"{'m(least)':>9} {'M(exc)':>8} {'M>=2^(j/2R)-1':>14}")
                for (n, j, q, a, e, red) in rows:
                    print(f"      {n:>6} {red['rho_V']:>7.2f} "
                          f"{'yes(%.1e)'%red['n_bound']:>16} {red['m']:>9} "
                          f"{red['M']:>8} {'yes(%.1f)'%red['M_lower']:>14}")
                print("   => complete up to the length cap; unbounded length is barred"
                      " only by")
                print("      the excursion hypothesis M<=m^beta (RT Conj 6.2) -- the wall.")
            else:
                # ---- outcome (a) or empty-up-to-cap -----------------------
                if R == 1:
                    print(f"\n(R={R}, d={d})  OUTCOME (a): UNCONDITIONALLY EMPTY "
                          "(Theorem R1: no 1-burst paradoxical sequence).")
                elif d == 0:
                    print(f"\n(R={R}, d={d})  OUTCOME (a): UNCONDITIONALLY EMPTY "
                          "(d=0 is a nontrivial cycle; none exist -- Steiner/Simons-de Weger).")
                else:
                    print(f"\n(R={R}, d={d})  empty up to j<={jmax} "
                          "(no shape survives the closure identity in range;")
                    print("      completeness beyond the cap is conditional on M<=m^beta).")


def conditional_cutoff_table():
    print("\n" + "=" * 78)
    print("Conditional uniform length cutoff (transcendence collision, length-bound sec.5)")
    print("  solve j^14.3 e^{-j/(alpha beta)} > 3 log3/log2  (Rhin j^-13.3 vs heuristic):")
    print("=" * 78)
    for (a, b, tag) in [(42, 3, "RT example"),
                        (37, 2.6, "empirical records"),
                        (41.677, 2, "heuristic limit")]:
        print(f"   (alpha,beta)=({a},{b})  [{tag:17}] : no paradoxical seq with j > {length_cutoff(0,0,a,b)}")
    print("   (conditional on d_T(n)<=alpha log n and M_T(n)<=n^beta -- RT Conj 6.2)")


# ==========================================================================
# 6. Self-tests: cross-validate against the direct oracle
# ==========================================================================
def self_test(survivors, Rmax, dmax, jmax, nmax_oracle):
    print("\n" + "=" * 78)
    print("SELF-TESTS")
    print("=" * 78)

    # (1) shape-enumeration survivors  ==  direct-orbit oracle (n<=nmax_oracle)
    oracle = direct_scan(Rmax, dmax, nmax_oracle, jmax)
    gen_set, ora_set = set(), set()
    for (R, d), rows in survivors.items():
        for (n, j, q, a, e, red) in rows:
            if n <= nmax_oracle:
                gen_set.add((R, d, n, j))
    for (R, d), rows in oracle.items():
        for (n, j, q, a, e) in rows:
            if j <= jmax:
                ora_set.add((R, d, n, j))
    assert gen_set == ora_set, (
        f"generator vs oracle mismatch:\n  only gen: {sorted(gen_set-ora_set)}"
        f"\n  only oracle: {sorted(ora_set-gen_set)}")
    print(f"  [ok] shape-enumeration survivors == direct orbit scan "
          f"({len(gen_set)} seqs, n<={nmax_oracle:,}, j<={jmax})")

    # (1b) closure s(V): box circuit-sum formula == remainder recursion.
    #      Sampled over the shape space + forced on every survivor.
    checked = 0
    for R in range(1, Rmax + 1):
        for k, (a_list, e_list) in enumerate(enum_shapes(R, min(jmax, 14))):
            if k % 97:                                 # sparse sample, keep it cheap
                continue
            assert s_of_shape(a_list, e_list) == remainder_from_parity(
                circuit_word(a_list, e_list)), (a_list, e_list)
            checked += 1
    for (R, d), rows in survivors.items():
        for (n, j, q, a, e, red) in rows:
            assert s_of_shape(a, e) == remainder_from_parity(circuit_word(a, e))
            checked += 1
    print(f"  [ok] closure s(V) circuit-sum == remainder recursion "
          f"({checked} shapes incl. all survivors)")

    # (2) closure identity + return difference on every survivor
    bad = 0
    for (R, d), rows in survivors.items():
        for (n, j, q, a, e, red) in rows:
            sV = remainder_from_parity(parity_vector(n, j))
            # (2^j-3^q) n = s(V) - 2^j d
            if (2 ** j - 3 ** q) * n != sV - (2 ** j) * d:
                bad += 1
            # T^j(n) - n == d
            cur = n
            for _ in range(j):
                cur = T(cur)
            if cur - n != d:
                bad += 1
    print(f"  [{'ok' if bad == 0 else 'FAIL'}] closure identity (2^j-3^q)n=s(V)-2^j d "
          f"and T^j(n)-n=d hold on all survivors")

    # (3) known near-cycle family: (R=3,d=1) must be exactly {7,9,19,25}, j=8
    fam = sorted(n for (n, j, q, a, e, red) in survivors.get((3, 1), []))
    assert fam == [7, 9, 19, 25], f"R=3,d=1 family wrong: {fam}"
    assert all(j == 8 for (n, j, q, a, e, red) in survivors.get((3, 1), []))
    print("  [ok] near-cycle family (R=3,d=1) == {7,9,19,25}, all j=8 "
          "(length-bound sec.4a)")

    # (4) R=1 provably empty; d=2..dmax with R<=6 empty (smallest d=2 is R=7)
    assert all(not survivors.get((1, d)) for d in range(0, dmax + 1)), "R=1 not empty"
    d2plus = [(R, d) for R in range(1, Rmax + 1) for d in range(2, dmax + 1)
              if survivors.get((R, d))]
    print(f"  [ok] R=1 empty (Theorem R1); no R<={Rmax} survivor with 2<=d<={dmax} "
          f"({'confirmed' if not d2plus else 'FOUND '+str(d2plus)})")
    assert not d2plus, f"unexpected d>=2 survivors: {d2plus}"
    print("  all self-tests passed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--Rmax", type=int, default=6, help="max circuits R (default 6)")
    ap.add_argument("--dmax", type=int, default=10, help="max return difference d (default 10)")
    ap.add_argument("--jmax", type=int, default=20, help="length cap j (default 20)")
    ap.add_argument("--nmax-oracle", type=int, default=2_000_000,
                    help="n cap for the direct-scan cross-check (default 2e6)")
    ap.add_argument("--no-selftest", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    survivors = search(args.Rmax, args.dmax, args.jmax)
    dt = time.time() - t0

    classify_and_report(survivors, args.Rmax, args.dmax, args.jmax)
    conditional_cutoff_table()
    if not args.no_selftest:
        self_test(survivors, args.Rmax, args.dmax, args.jmax, args.nmax_oracle)

    total = sum(len(v) for v in survivors.values())
    print(f"\nDONE: {total} surviving candidate shape(s) across all slices "
          f"(R<={args.Rmax}, d<={args.dmax}, j<={args.jmax}); search {dt:.1f}s.")


if __name__ == "__main__":
    main()
