#!/usr/bin/env python3
"""Paradoxical Collatz sequences (Rozier-Terracol, arXiv:2502.00948v5) through
the lens of the YAH SRS / tropical-shadow machinery (this repo).

Foundational layer: reproduce the paper's data and verify the exact identities
that the YAH bridge rests on.

  T(n) = (3n+1)/2 (n odd), n/2 (n even).
  T^j(n) = C_j(n) n + E_j(n),  C_j = 3^q/2^j,  q = #odd among n..T^{j-1}(n).
  Integer remainder s_j(n) := 2^j E_j(n) in Z>=0 ; T^j(n) = (3^q n + s_j)/2^j.
  Paradoxical (n>2):  (i) C_j < 1  (3^q < 2^j)   (ii) T^j(n) >= n.
  Equivalently s_j >= (2^j - 3^q) n  with 2^j - 3^q >= 1.
"""
import math
from fractions import Fraction

LOG2, LOG3 = math.log(2.0), math.log(3.0)
THRESH = LOG2 / LOG3  # critical ones-ratio ~0.6309


def T(n):
    return (3 * n + 1) >> 1 if n & 1 else n >> 1


def orbit_data(n, jmax):
    """Yield (j, q, pow3, pow2, val, s) along the orbit, with val=T^j(n),
    s = integer remainder 2^j E_j = 2^j val - 3^q n."""
    cur, q, p3, p2 = n, 0, 1, 1
    for j in range(1, jmax + 1):
        if cur & 1:
            q += 1
            p3 *= 3
        cur = T(cur)
        p2 <<= 1
        s = p2 * cur - p3 * n          # = 2^j T^j(n) - 3^q n  (integer remainder)
        yield j, q, p3, p2, cur, s


def paradoxical_sequences(start, end, jmax=200):
    """All paradoxical (n,j,q) with start<=n<=end, length<=jmax."""
    out = []
    for n in range(max(start, 3), end + 1):
        for j, q, p3, p2, cur, s in orbit_data(n, jmax):
            if p3 < p2 and cur >= n:        # (i) C<1  (ii) T^j(n)>=n
                out.append((n, j, q, cur, s))
                if cur == 1:
                    break
    return out


def parity_vector(n, j):
    v, cur = [], n
    for _ in range(j):
        v.append(cur & 1)
        cur = T(cur)
    return tuple(v)


# --------------------------------------------------------------------------
# 1. Reproduce the paper's Table 1 and Theorem 1.3 counts
# --------------------------------------------------------------------------
def reproduce_table():
    seqs = paradoxical_sequences(3, 4614, jmax=200)
    from collections import defaultdict
    byjq = defaultdict(list)
    for (n, j, q, cur, s) in seqs:
        byjq[(j, q)].append((n, cur, s))
    print(f"Total paradoxical sequences with n<=4614: {len(seqs)}  (paper: 593)")
    starts = sorted(set(n for (n, j, q, cur, s) in seqs))
    print(f"Distinct start integers: {len(starts)}  (paper: 550)")
    print(f"\n{'(j, q)':>10} {'C=3^q/2^j':>11} {'N':>5} {'n-range':>14} {'E-range':>16}")
    for (j, q) in sorted(byjq):
        rows = byjq[(j, q)]
        C = 3 ** q / 2 ** j
        ns = [r[0] for r in rows]
        Es = [r[2] / 2 ** j for r in rows]   # E = s/2^j
        print(f"{str((j,q)):>10} {C:>11.4f} {len(rows):>5} "
              f"{min(ns):>6}-{max(ns):<7} {min(Es):>7.2f}-{max(Es):<7.2f}")
    # backbone: which fixed value appears in all sequences?
    def contains(n, j, v):
        cur = n
        for _ in range(j + 1):
            if cur == v:
                return True
            cur = T(cur)
        return False
    for v in (11, 103):
        cnt = sum(1 for (n, j, q, cur, s) in seqs if contains(n, j, v))
        print(f"sequences containing {v:3}: {cnt}")
    j8 = [(n, j) for (n, j, q, cur, s) in seqs if j == 8]
    print(f"j=8 sequences start at: {sorted(set(n for n,j in j8))} (paper: 7,9,18,19,25)")
    return seqs


# --------------------------------------------------------------------------
# 2. Verify exact identities: remainder integrality + per-V finiteness bound
# --------------------------------------------------------------------------
def verify_identities(seqs):
    bad = 0
    bound_ok = 0
    for (n, j, q, cur, s) in seqs:
        # integrality and definition of s
        assert s >= 0 and (2 ** j * cur == 3 ** q * n + s)
        # paradoxical <=> s >= (2^j - 3^q) n
        gap = 2 ** j - 3 ** q
        assert gap >= 1 and s >= gap * n
        # remainder depends only on parity vector (residue mod 2^j):
        V = parity_vector(n, j)
        s_check = remainder_from_parity(V)
        if s_check != s:
            bad += 1
        # per-parity-vector start bound  n <= s(V)/(2^j-3^q)
        if n <= s_check / gap + 1e-9:
            bound_ok += 1
    print(f"\nremainder = function of parity vector only: {len(seqs)-bad}/{len(seqs)} exact")
    print(f"per-parity-vector bound  n <= s(V)/(2^j-3^q): {bound_ok}/{len(seqs)} hold")


def remainder_from_parity(V):
    """Integer remainder s = 2^j E_j computed from the parity word ALONE
    (no n).  s_0=0; even bit: s->2s ... actually track via the affine maps.
    T^j(n) = (3^q n + s)/2^j.  Step rules on (3^q, s, 2^j):
        bit 0 (even): denom doubles only            -> s unchanged, p2 doubles
        bit 1 (odd):  (3x+1)/2                       -> s -> 3 s + p2(old), p2 doubles, p3 triples
    """
    p2, p3, s = 1, 1, 0
    for b in V:
        if b == 1:
            s = 3 * s + p2
            p3 *= 3
        p2 <<= 1
    return s


# --------------------------------------------------------------------------
# 3. Remainder as a 2-dim matrix interpretation; partial order decreases it
# --------------------------------------------------------------------------
def remainder_matrix_interp(V):
    """E_j as the output of a 2-dim affine (natural matrix-interpretation) reading
    of the parity word, in the rational form (C,E):
        bit 0:  (C,E) -> (C/2, E/2)
        bit 1:  (C,E) -> (3C/2, (3E+1)/2)
    Returns (C,E) = (C_j, E_j)."""
    C, E = Fraction(1), Fraction(0)
    for b in V:
        if b:
            C, E = 3 * C / 2, (3 * E + 1) / 2
        else:
            C, E = C / 2, E / 2
    return C, E


def check_order_decreases_E():
    """Lemma 2.3 mechanized: swapping a '01' to '10' (shift a 1 left) strictly
    DECREASES the remainder E (with equal length & ones-count).  This makes the
    partial order <= a termination order and E a strictly monotone interpretation
    -- exactly a YAH matrix-interpretation / dependency-pair style argument."""
    import itertools
    viol = 0
    tested = 0
    for L in range(2, 11):
        for W in itertools.product((0, 1), repeat=L):
            for i in range(L - 1):
                if W[i] == 0 and W[i + 1] == 1:
                    W2 = list(W); W2[i], W2[i + 1] = 1, 0   # 01 -> 10
                    _, E = remainder_matrix_interp(W)
                    _, E2 = remainder_matrix_interp(tuple(W2))
                    tested += 1
                    if not (E2 < E):           # shifting 1 left lowers E
                        viol += 1
    print(f"\nLemma 2.3 (swap 01->10 strictly lowers remainder E): "
          f"{tested-viol}/{tested} hold  ({viol} violations)")
    # extremes (Theorem 2.4): V=0^(j-q)1^q maximises E, V=1^q 0^(j-q) minimises
    j, q = 8, 5
    Vmax = (0,)*(j-q) + (1,)*q
    Vmin = (1,)*q + (0,)*(j-q)
    _, Emax = remainder_matrix_interp(Vmax)
    _, Emin = remainder_matrix_interp(Vmin)
    print(f"  Thm 2.4 extremes j={j},q={q}: E(0^(j-q)1^q)={float(Emax):.4f} (max), "
          f"E(1^q 0^(j-q))={float(Emin):.4f} (min)")


if __name__ == "__main__":
    print("=" * 70)
    print("PARADOXICAL SEQUENCES x YAH -- foundational verification")
    print("=" * 70)
    seqs = reproduce_table()
    verify_identities(seqs)
    check_order_decreases_E()
