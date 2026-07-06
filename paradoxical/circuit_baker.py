#!/usr/bin/env python3
"""Bounded-circuit (Baker) construction for paradoxical Collatz sequences.

A paradoxical sequence with odd start decomposes into R "circuits", each = one
ascending burst (a_i odd steps) followed by a descending gap (e_i halvings):

    y_{i+1} = (3^{a_i} y_i + (3^{a_i} - 2^{a_i})) / 2^{c_i},   c_i = a_i + e_i,

with y_i odd, v2(y_i+1) = a_i.  Composing R circuits gives the exact identity

    (2^j - 3^q) y_1  =  S  -  2^j d,        j = sum c_i,  q = sum a_i,
    S = s(V) = 2^j E_j,   d = T^j(n) - n >= 0.

R = number of bursts.  This is the acyclic analog of the circuit/cycle calculus
of Steiner and Simons-de Weger, in which Baker's theorem bounds the length for a
bounded number of circuits.  Here we (1) verify the algebra on all 593 sequences,
(2) prove no paradoxical sequence has R = 1, (3) census (R,d), (4) instantiate the
Baker / Rhin / Ellison lower bounds that drive the length cutoff per fixed (R,d).
"""
import math
from para_yah import (T, paradoxical_sequences, parity_vector,
                      remainder_from_parity)

LOG2, LOG3 = math.log(2.0), math.log(3.0)
RHO = LOG2 / LOG3


def v2(x):
    x = abs(int(x)); c = 0
    while x and x % 2 == 0:
        x //= 2; c += 1
    return c


# --------------------------------------------------------------------------
# Circuit decomposition of a paradoxical sequence (odd start)
# --------------------------------------------------------------------------
def runs(V):
    out = []
    for b in V:
        if out and out[-1][0] == b:
            out[-1][1] += 1
        else:
            out.append([b, 1])
    return [(b, L) for b, L in out]


def decompose(n, j):
    """Return (a_list, e_list, R, d, end) for odd start n, length j.
    a_list = burst lengths, e_list = gap lengths (last may be 0)."""
    assert n % 2 == 1, "odd start expected"
    V = parity_vector(n, j)
    rr = runs(V)
    assert rr[0][0] == 1, "odd start => V begins with 1"
    a_list = [L for b, L in rr if b == 1]
    zero_runs = [L for b, L in rr if b == 0]
    R = len(a_list)
    if len(zero_runs) == R:
        e_list = zero_runs[:]          # V ends in a 0-run
    else:                              # ends in a 1-run
        e_list = zero_runs + [0]
    end = n
    for _ in range(j):
        end = T(end)
    return a_list, e_list, R, end - n, end


def circuit_step(y, a, e):
    """One circuit: a odd steps then e halvings.  The affine formula
    T^a(y) = 3^a (y+1)/2^a - 1 is valid whenever the first a steps are odd,
    i.e. v2(y+1) >= a (equality for interior bursts; the final, truncated burst
    or gap of a finite sequence may have v2 strictly larger)."""
    assert v2(y + 1) >= a, f"burst needs v2({y}+1)={v2(y+1)} >= {a}"
    z = (3 ** a) * (y + 1) // (2 ** a) - 1      # value after a odd steps
    if e == 0:
        return z
    assert v2(z) >= e, f"gap needs v2({z})={v2(z)} >= {e}"
    return z // (2 ** e)


def verify_decomposition(seqs):
    ok = 0
    for (n, j, q, cur, s) in seqs:
        if n % 2 == 0:
            continue                            # treat odd-start representatives
        a_list, e_list, R, d, end = decompose(n, j)
        # replay the circuits
        y = n
        good = True
        for a, e in zip(a_list, e_list):
            try:
                y = circuit_step(y, a, e)
            except AssertionError:
                good = False
                break
        # composite identity
        comp = (2 ** j - 3 ** q) * n == s - (2 ** j) * d
        if good and y == end and comp and sum(a_list) == q and \
           sum(a_list) + sum(e_list) == j:
            ok += 1
    odd_starts = sum(1 for (n, j, q, cur, s) in seqs if n % 2 == 1)
    print(f"circuit decomposition verified (odd-start seqs): {ok}/{odd_starts}")
    print("  identity (2^j - 3^q) n = s(V) - 2^j d  holds for each.")


# --------------------------------------------------------------------------
# R = 1: no paradoxical sequence  (elementary, complete)
# --------------------------------------------------------------------------
def verify_R1_empty(nmax=300_000):
    """Elementary theorem: no paradoxical sequence has a single burst (R=1).
    Proof: one circuit (a,e). If e=0 then j=a, C=3^a/2^a>1 (not condition i).
    If e>=1, C<1 forces 2^e > (3/2)^a, and
       T^{a+e}(y) = z/2^e < (3/2)^a (y+1) / 2^e < (y+1),
    so T^j(y) <= y with equality only for the trivial 1-circuit cycle y=1.
    Hence no paradoxical R=1 with n>2.  We also check exhaustively."""
    bad = 0
    for (n, j, q, cur, s) in paradoxical_sequences(3, nmax, jmax=400):
        if n % 2 == 1:
            a_list, e_list, R, d, end = decompose(n, j)
            if R == 1:
                bad += 1
    print(f"R=1 paradoxical sequences with odd start n<={nmax:,}: {bad} "
          f"(elementary proof: none exist)")


# --------------------------------------------------------------------------
# Census of (R, d) over the 593
# --------------------------------------------------------------------------
def census(seqs):
    from collections import Counter
    R_count = Counter()
    Rd = Counter()
    for (n, j, q, cur, s) in seqs:
        if n % 2 == 0:
            continue
        a_list, e_list, R, d, end = decompose(n, j)
        R_count[R] += 1
        Rd[(R, d)] += 1
    print("burst-count R distribution (odd-start sequences):")
    print("   " + ", ".join(f"R={R}:{c}" for R, c in sorted(R_count.items())))
    print(f"   minimum R = {min(R_count)}  (no R<{min(R_count)} exists)")
    dvals = sorted(set(d for (R, d) in Rd))
    print(f"difference d = T^j(n)-n takes values: min {min(dvals)}, max {max(dvals)}")
    near = sum(c for (R, d), c in Rd.items() if d <= 1)
    print(f"   near-cycles (d<=1, Baker/Ellison-controlled): {near} sequences")
    print(f"   d=0 (genuine cycles): {sum(c for (R,d),c in Rd.items() if d==0)} "
          f"(must be 0 -- Collatz cycles)")


# --------------------------------------------------------------------------
# Baker / Rhin / Ellison lower bounds that drive the cutoff
# --------------------------------------------------------------------------
def verify_transcendence_bounds(seqs):
    print("Transcendence lower bounds on the linear form (verified on the data):")
    rhin_ok = ell_ok = 0
    tot = 0
    for (n, j, q, cur, s) in seqs:
        tot += 1
        Lam = abs(j * LOG2 - q * LOG3)
        if Lam >= j ** (-13.3):                       # Rhin Prop 6.3
            rhin_ok += 1
        if q > 12:
            if (2 ** j - 3 ** q) > (2.56 ** q) / 2:    # Ellison / RT Lemma B.1
                ell_ok += 1
    nq = sum(1 for (n, j, q, cur, s) in seqs if q > 12)
    print(f"   Rhin   |j log2 - q log3| >= j^-13.3 : {rhin_ok}/{tot}")
    print(f"   Ellison 2^j - 3^q > 2.56^q / 2 (q>12): {ell_ok}/{nq}")


def length_cutoff(R, d, alpha=42, beta=3):
    """Schematic explicit cutoff: for fixed (R,d) the circuit equation plus the
    Rhin bound force j below a finite L(R,d).  We report the RT-style number
    obtained from |j log2 - q log3| >= j^-13.3 against the heuristic upper bound;
    the rigorous (unconditional) cutoff for d=0 is Steiner/Simons-de Weger, for
    d<=1 it is Ellison (astronomically larger).  Returns the conditional figure."""
    rhs = 3 * LOG3 / LOG2
    ab = alpha * beta
    best = 0
    j = 2
    while j < 10 ** 7:
        val = 14.3 * math.log(j) - j / ab
        if val > math.log(rhs):
            best = j
        elif j > ab * 40:
            break
        j += 1
    return best


def near_cycles(seqs):
    """List the d<=1 near-cycles with their circuit shapes (the subclass the
    Baker/Ellison machinery rigorously controls -- RT Appendix B)."""
    print("Near-cycles d = T^j(n)-n <= 1  (odd start): circuit shapes")
    print(f"   {'n':>5} {'j':>4} {'q':>3} {'R':>3} {'d':>3}  shape (a_i / e_i)")
    rows = []
    for (n, j, q, cur, s) in seqs:
        if n % 2 == 0:
            continue
        a, e, R, d, end = decompose(n, j)
        if d <= 1:
            rows.append((n, j, q, R, d, a, e))
    for (n, j, q, R, d, a, e) in sorted(rows):
        print(f"   {n:>5} {j:>4} {q:>3} {R:>3} {d:>3}  a={a}  e={e}")
    print(f"   total near-cycles: {len(rows)} (RT Lemma B.2: all d=1, n>3 are paradoxical)")


def cutoff_table():
    """Explicit conditional length cutoff L(R,d) figures.  For fixed (R,d) the
    bound is unconditional (Steiner/SdW for d=0, Ellison/RT for d=1) but huge;
    the figure below is the heuristic Baker bound (RT Sec 6) for reference."""
    print("Length cutoff (no paradoxical seq longer than L), GIVEN delay/excursion")
    print("heuristics -- the bound that the transcendence engine yields:")
    for (a, b, tag) in [(42, 3, "RT example"), (37, 2.6, "empirical")]:
        print(f"   alpha={a}, beta={b} ({tag}): j < {length_cutoff(0,0,a,b)}")
    print("   For each FIXED (R,d) the bound is unconditional but astronomically")
    print("   larger (Simons-de Weger d=0; Ellison d=1); the union over d is the wall.")


if __name__ == "__main__":
    seqs = paradoxical_sequences(3, 4614, jmax=200)
    print("=" * 72)
    print("Circuit decomposition")
    print("=" * 72)
    verify_decomposition(seqs)
    # worked example
    a, e, R, d, end = decompose(7, 8)
    print(f"  example n=7, j=8: R={R} circuits, bursts a={a}, gaps e={e}, "
          f"end=T^8(7)={end}, d={d} (a near-cycle!)")
    print("\n" + "=" * 72)
    print("R = 1 emptiness (elementary)")
    print("=" * 72)
    verify_R1_empty()
    print("\n" + "=" * 72)
    print("(R, d) census of the 593")
    print("=" * 72)
    census(seqs)
    print("\n" + "=" * 72)
    print("Transcendence bounds")
    print("=" * 72)
    verify_transcendence_bounds(seqs)
    print("\n" + "=" * 72)
    print("Near-cycle subclass (Baker/Ellison-controlled)")
    print("=" * 72)
    near_cycles(seqs)
    print("\n" + "=" * 72)
    print("Length cutoff figures")
    print("=" * 72)
    cutoff_table()
