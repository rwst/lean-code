#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""B4 of plans/report3-BB13.html -- 2-adic interpolation rigidity, measured.

Strategy B4 has two halves.  The cheap one (rated 90%) is the set of rigidity
facts that survive correction CB1 of the report: ord(3 mod 2^m) = 2^{m-2}, the
tower-separation lemma, the (5,37) counterexample to A3's uniqueness claim, and
a log* bound on how often one value of k can recur.  The expensive one (rated
8%) asks for a Padé-based 2-adic measure at the "self-referential" points k_a.

This script measures both.  Notation:

    m_a = round((3/2)^a) = (2*3^a + 2^a) >> (a+1)        exact
    k_a = 3^a - m_a 2^a       (|k_a| <= 2^{a-1} always;  v_2(3^a - k_a) = a + v_2(m_a))
    a is *self-referential for k*  iff  v_2(3^a - k) >= a + 2
    the *corridor* at a is  |k| < (3/2)^a  (the exception window of Problem 10.13)

Blocks
  [A] tower separation, and the (5,37) counterexample -- is it minimal?
  [B] the corridor census: is any exception self-referential?
  [C] recurrence of the value k_a among the exceptions
  [D] corridor saturation: how deep can a height-only measure see?
  [E] the v_2(m_a) statistics behind "4 | m_a" (density 1/4, never on E)
  [F] the log* bound is attained: an explicit 4-term self-referential chain
  [G] CB2 re-check: Yu's p-adic Baker output against the trivial bound

Usage:  python3 BB13/b4_twoadic.py [NMAX] [AMAX]   (defaults 20000, 400)

The Lean side of the same work is BB13/TwoAdicRigidity.lean; its module
docstring quotes the numbers produced here.
"""
import json
import os
import sys
import time
from math import log, log2

HERE = os.path.dirname(os.path.abspath(__file__))
LOG32 = log2(1.5)  # 0.5849625007211562


def mnum(a):
    """round((3/2)^a), exactly."""
    return (2 * 3 ** a + 2 ** a) >> (a + 1)


def kres(a):
    """k_a = 3^a - m_a 2^a."""
    return 3 ** a - mnum(a) * 2 ** a


def v2(n):
    """2-adic valuation of a nonzero integer."""
    if n == 0:
        return None
    n = abs(n)
    return (n & -n).bit_length() - 1


def centered(x, mod):
    """The representative of x mod `mod` in (-mod/2, mod/2]."""
    r = x % mod
    return r - mod if r > mod // 2 else r


def selfref(k, a):
    """v_2(3^a - k) >= a + 2 ?"""
    d = 3 ** a - k
    return d == 0 or v2(d) >= a + 2


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    amax = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    t0 = time.time()

    # ---------------------------------------------------------------- [A]
    print("=" * 78)
    print("[A] tower separation and CB1's counterexample")
    print("=" * 78)
    K = pow(3, 37, 2 ** 39)
    print(f"  k = 3^37 mod 2^39 = {K}")
    print(f"  v_2(3^5  - k) = {v2(3 ** 5 - K):2d}   (needs >= 7)   ->  {selfref(K, 5)}")
    print(f"  v_2(3^37 - k) = {'inf' if 3 ** 37 == K else v2(3 ** 37 - K)}"
          f"  (needs >= 39)  ->  {selfref(K, 37)}")
    print(f"  gap: 37 - 5 = {37 - 5} = 2^5 exactly -> the pair is EXTREMAL for a' >= a + 2^a")
    print(f"  corridor at a=5: |k| < (3/2)^5 = {1.5 ** 5:.2f}, but |k| = {K:.3g}"
          f"  -> {K / 1.5 ** 5:.3g} times too large")
    # is (5,37) the smallest counterexample with a >= 5?  a' - a must be a
    # multiple of 2^a, so the least a' for a given a is a + 2^a.
    print("  least admissible a' per a (a' = a + 2^a):")
    print("   ", ", ".join(f"{a}->{a + 2 ** a}" for a in range(1, 9)))
    print("  so with a >= 5 the smallest pair is (5, 37); the previous ones are")
    print("  (1,3), (2,6), (3,11), (4,20) -- all with a < 5, outside A3's claim.")
    # verify the constructed witnesses for a range of a
    bad = []
    for a in range(1, 13):
        ap = a + 2 ** a
        k = pow(3, ap, 2 ** (ap + 2))
        if not (selfref(k, a) and selfref(k, ap)):
            bad.append(a)
    print(f"  constructed witnesses k = 3^{{a'}} mod 2^{{a'+2}} valid for a = 1..12:"
          f" {'ALL OK' if not bad else 'FAILED at ' + str(bad)}")
    # and the converse direction: a' - a not a multiple of 2^a => no common k
    viol = 0
    for a in range(1, 8):
        for ap in range(a + 1, a + 3 * 2 ** a):
            common = ((3 ** ap - 3 ** a) % 2 ** (a + 2) == 0)
            if common != ((ap - a) % 2 ** a == 0):
                viol += 1
    print(f"  tower separation is an IFF (checked a<=7, a'<a+3*2^a): violations = {viol}")

    # ---------------------------------------------------------------- [B]
    print()
    print("=" * 78)
    print("[B] the corridor census: is any exception self-referential?")
    print("=" * 78)
    census = os.path.join(HERE, "m0_failures_1000000.json")
    if os.path.exists(census):
        with open(census) as fh:
            d = json.load(fh)
        E, NCEN = d["failure_set"], d["n_max"]
    else:
        E, NCEN = [1, 2, 3, 4, 7], 0
    print(f"  E ∩ [1,{NCEN}] = {E}   (BB13/m0_failures.py)")
    print("     a    m_a     k_a   v_2(m_a)   4|m_a   |k_a|<(3/2)^a   v_2(3^a-k_a)  a+2")
    for a in E:
        m, k = mnum(a), kres(a)
        print(f"  {a:4d} {m:6d} {k:6d}   {v2(m) if m else 0:6d}     "
              f"{str(m % 4 == 0):>5}   "
              f"{str(abs(k) < 1.5 ** a):>10}      {v2(3 ** a - k):8d}  {a + 2:4d}")
    print("  => v_2(m_a) <= 1 on all of E: NO exception below 10^6 is self-referential.")
    print("     A3's hypothesis 'v_2(3^a - k_a) >= a+2 inside the corridor' is VACUOUS")
    print("     in the verified range; a corridor recurrence would need a > 10^6 and")
    print("     then a' - a >= 2^{a-2} > 2^{10^6}.")

    # ---------------------------------------------------------------- [C]
    print()
    print("=" * 78)
    print("[C] does the value k_a recur among the exceptions?")
    print("=" * 78)
    vals = {}
    for a in E:
        vals.setdefault(kres(a), []).append(a)
    for k, aa in sorted(vals.items()):
        tag = "  <-- RECURS" if len(aa) > 1 else ""
        print(f"  k = {k:4d}  at a = {aa}{tag}")
    print("  line partition of E (BB13/Census.lean): {1}, {2,3}, {4}, {7}")
    print("  => k_2 = k_4 = 1 with 2 and 4 on DIFFERENT lines: the value does recur,")
    print("     so A3's downstream 'no value of k_a recurs' is false as stated.")
    print("     (Within a line k_b = 3^{b-a} k_a, so recurrence is only ever across lines.)")

    # ---------------------------------------------------------------- [D]
    print()
    print("=" * 78)
    print("[D] corridor saturation: the depth a height-only measure already sees")
    print("=" * 78)
    print("  maxdepth(a) = max { M : some |k| < (3/2)^a has 2^M | 3^a - k }")
    print("  floor(a*log2(3/2)) is the trivial lower bound (corridor_saturation);")
    print("  Problem 2 asks for the depth to stay <= a + O(1).")
    print("      a  floor(.585a)  maxdepth  diff   a+v_2(m_a)   exception?")
    rows = []
    for a in list(range(4, 41)) + [50, 60, 70, 80, 100, 128, 160, 200]:
        if a > amax:
            break
        p3, corr = 3 ** a, 1.5 ** a
        M = 0
        while True:
            c = centered(p3, 2 ** (M + 1))
            if abs(c) < corr:
                M += 1
            else:
                break
        base = int(a * LOG32)
        rows.append((a, base, M, M - base, a + v2(mnum(a)), a in E))
    for (a, base, M, diff, av, isE) in rows[:20]:
        print(f"  {a:5d}  {base:9d}  {M:9d}  {diff:4d}   {av:9d}      {isE}")
    print(f"  ... ({len(rows)} values computed up to a = {rows[-1][0]})")
    diffs = [r[3] for r in rows]
    print(f"  maxdepth - floor(.585a): min {min(diffs)}, max {max(diffs)},"
          f" mean {sum(diffs) / len(diffs):.2f}")
    over = [r for r in rows if r[2] >= r[0]]
    print(f"  maxdepth >= a happens exactly at a = {[r[0] for r in over]}"
          f"  (= the exceptions in range: {[r[0] for r in rows if r[5]]})")
    print("  => the free reach is 0.585a + a small excess (<= 8 here, heuristically")
    print("     O(log a) as a max of geometrics); everything Problem 2 asks for lives")
    print("     in the window [0.585a, a], and there the only input is that m_a is an")
    print("     integer -- which is the statement itself (measure_iff_problem_two).")

    # ---------------------------------------------------------------- [E]
    print()
    print("=" * 78)
    print(f"[E] the v_2(m_a) statistics behind '4 | m_a'  (a <= {nmax})")
    print("=" * 78)
    hist = {}
    p3, p2 = 1, 1
    mx, mxa = 0, 0
    for a in range(1, nmax + 1):
        p3 *= 3
        p2 *= 2
        m = (2 * p3 + p2) >> (a + 1)
        w = v2(m)
        hist[w] = hist.get(w, 0) + 1
        if w > mx:
            mx, mxa = w, a
    tot = sum(hist.values())
    print("     j   #{v_2(m_a)=j}     freq      2^{-(j+1)}")
    for j in sorted(hist)[:12]:
        print(f"  {j:4d}   {hist[j]:9d}   {hist[j] / tot:.5f}    {2.0 ** (-(j + 1)):.5f}")
    ge2 = sum(c for j, c in hist.items() if j >= 2)
    print(f"  #{{4 | m_a}} = {ge2} of {tot} = {ge2 / tot:.5f}  (heuristic 1/4)")
    print(f"  max v_2(m_a) = {mx} at a = {mxa}   (log2({nmax}) = {log2(nmax):.1f})")
    print("  so 'self-referential' is a density-1/4 condition on all of N -- and yet")
    print("  it never meets the 5 exceptions.  The two conditions are independent")
    print("  events of probability 1/4 and ~0, and the census sees the product.")

    # ---------------------------------------------------------------- [F]
    print()
    print("=" * 78)
    print("[F] the log* bound is ATTAINED: an explicit self-referential chain")
    print("=" * 78)
    chain = [1]
    while len(chain) < 4:
        chain.append(chain[-1] + 2 ** chain[-1])
    print(f"  chain a_1..a_4 = {chain}  (each a_{{i+1}} = a_i + 2^{{a_i}}, extremal)")
    top = chain[-1]
    k = pow(3, top, 2 ** (top + 2))
    ok = all(selfref(k, a) for a in chain)
    print(f"  k = 3^{top} mod 2^{top + 2}  ({len(str(k))} decimal digits)")
    print(f"  self-referential at every a in the chain: {ok}")
    print(f"  v_2(3^a - k) - (a+2) for a in chain: "
          f"{[v2(3 ** a - k) - (a + 2) for a in chain[:-1]]} (+inf at the top)")
    print("  => the tower-separation bound is sharp, so the log* count of")
    print("     selfRef_card_le cannot be improved to anything slower-growing.")

    # ---------------------------------------------------------------- [G]
    print()
    print("=" * 78)
    print("[G] CB2 re-check: Yu's p-adic Baker bound vs the trivial bound")
    print("=" * 78)
    print("  the linear form is  Lambda = a*log_2(3) - log_2(k)  with  |k| ~ 2^{0.585a};")
    print("  a p-adic Baker bound has shape v_2(Lambda) <= C * log(A_1) log(A_2) log(B)")
    print("  with log A_2 ~ log|k| ~ 0.585 a log 2 and log B ~ log a:")
    print("       a     0.585a (trivial)     ~ a log a (Yu shape)     ratio")
    for a in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        triv, yu = LOG32 * a, a * log(a)
        print(f"  {a:8d}   {triv:16.1f}   {yu:22.1f}   {yu / triv:8.1f}")
    print("  => Yu's output exceeds the trivial 0.585a by a factor ~ log a: vacuous,")
    print("     exactly as CB2 states.  Nothing in B4 changes this; what changes is")
    print("     that measure_iff_problem_two shows *no* height-only bound can help.")

    print()
    print(f"total {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
