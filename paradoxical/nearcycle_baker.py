#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  Released under CC0.
"""Bounded-circuit Baker reduction for the d=1 near-cycle slice (research I.1.2).

Companion to `bounded_circuit_search.py` and `length-bound.html` §4d (which works
the analogous d=2, R=7 case).  Here we close the d=1 near-cycles for every fixed
number of circuits R<=10:

  * Rozier-Terracol prove  d=1 => paradoxical  (RT App. B, Lemma B.2); finiteness
    of the d=1 solutions is open.
  * For a FIXED R we run the linear-form engine to a conditional finiteness
    theorem and isolate the single missing hypothesis.

Closure identity (d=1):  (2^j - 3^q) n = s(V) - 2^j,   so
    n = (s(V) - 2^j) / (2^j - 3^q),           s(V) = remainder_from_parity(V).

The reduction chain (each link UNCONDITIONAL except the last):
  (a) Rhin (Prop 6.3): |j log2 - q log3| >= j^{-13.3}, so 2^j - 3^q >= 3^q j^{-13.3},
      whence the start is bounded polynomially:  n <= rho_V j^{13.3},  rho_V=s(V)/3^q.
  (b) RT Cor 4.4 + Rhin: least odd term  m <= H(j) = 1/(2^{j/floor(rho j)} - 3) = O(j^{14.3}).
  (c) Pigeonhole: with R circuits max(a_i,e_i) >= j/(2R), so the excursion
      M >= 2^{j/(2R)} - 1  (a STRUCTURAL lower bound, exponential in j).
  (d) Excursion hypothesis  M <= m^beta  (RT Conj 6.2):  then
        2^{j/(2R)} - 1 <= M <= m^beta <= H(j)^beta = O(j^{14.3 beta})
      collides exponential vs polynomial => j <= J0(R,beta) (bounded).

Conditional finiteness theorem (d=1, fixed R): granting (d), there are only
finitely many paradoxical Omega_j(n) with T^j(n)=n+1 and R circuits -- the length
j is bounded by J0(R,beta), and for each length only finitely many starts
(per-length finiteness, RT.finite_paradoxical_of_length: n <= 2^j 3^j).  The
excursion bound M <= m^beta is the SOLE unproved input.

Unlike d=2 (smallest R=7) the d=1 slice is populated already at small R: the
census over odd starts n<=5e6 is R in {3,8,10} at the convergent lengths
j in {8,27,46}.  All verified below.
"""
import argparse
import math
import time
from collections import defaultdict

from para_yah import T, parity_vector, remainder_from_parity
from circuit_baker import decompose

LOG2, LOG3 = math.log(2.0), math.log(3.0)
RHO = LOG2 / LOG3          # ~0.6309297535


# --------------------------------------------------------------------------
# Slice census: d=1 paradoxical odd starts by circuit count R
# --------------------------------------------------------------------------
def find_d1_by_R(Rmax, nmax, jmax=220):
    """All odd-start d=1 paradoxical sequences grouped by R (<=Rmax)."""
    out = defaultdict(list)
    for n in range(3, nmax + 1, 2):
        cur, q, p3, p2 = n, 0, 1, 1
        for j in range(1, jmax + 1):
            if cur & 1:
                q += 1
                p3 *= 3
            cur = T(cur)
            p2 <<= 1
            if p3 < p2 and cur >= n:              # C_j<1 and T^j(n)>=n
                if cur - n == 1:                  # d = 1
                    a, e, R, dd, end = decompose(n, j)
                    if R <= Rmax:
                        out[R].append((n, j, q, tuple(a), tuple(e)))
                if cur == 1:
                    break
    return out


# --------------------------------------------------------------------------
# Reduction quantities
# --------------------------------------------------------------------------
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


def H(j):
    """RT Cor 4.4 least-odd-term bound  m <= H(j) = 1/(2^{j/floor(rho j)} - 3)."""
    q = math.floor(RHO * j)
    if q == 0:
        return float("inf")
    den = 2.0 ** (j / q) - 3.0
    return 1.0 / den if den > 0 else float("inf")


def reduction_row(n, j, q, R):
    """The full unconditional reduction chain for one d=1 sequence; also the
    observed excursion exponent beta_obs = log M / log m (the least beta for which
    the hypothesis M<=m^beta holds on this sequence)."""
    sV = remainder_from_parity(parity_vector(n, j))
    Delta = 2 ** j - 3 ** q
    Lam = j * LOG2 - q * LOG3
    rho_V = sV / 3 ** q
    m = min_odd_term(n, j)
    M = max_excursion(n, j)
    beta_obs = math.log(M) / math.log(m) if m > 1 else float("inf")
    return {
        "sV": sV, "Delta": Delta, "Lambda": Lam, "rho_V": rho_V,
        "closure_ok": (sV - 2 ** j) % Delta == 0 and (sV - 2 ** j) // Delta == n,
        "rhin_ok": Lam >= j ** (-13.3),
        "delta_rhin_ok": Delta >= 3 ** q * j ** (-13.3),
        "n_bound": rho_V * j ** 13.3, "n_le_bound": n <= rho_V * j ** 13.3,
        "m": m, "H": H(j), "m_le_H": m <= H(j) + 1e-9,
        "M": M, "M_lower": 2 ** (j / (2 * R)) - 1,
        "M_ge_lower": M >= 2 ** (j / (2 * R)) - 1,
        "beta_obs": beta_obs,
    }


# --------------------------------------------------------------------------
# Conditional cutoff J0(R, beta): the (d) collision, analytically
# --------------------------------------------------------------------------
def cutoff_d1(R, beta, jcap=500_000):
    """Largest j for which the collision (d) can still hold:
        (log2/(2R)) j <= 14.3 beta log j      (2^{j/2R} <= H(j)^beta, H=O(j^14.3)).
    Above J0(R,beta) the exponential excursion lower bound exceeds m^beta, so no
    paradoxical d=1 sequence with R circuits can exist."""
    c = LOG2 / (2 * R)
    best, j = 0, 2
    while j < jcap:
        if c * j <= 14.3 * beta * math.log(j):
            best = j
        elif j > 200 and c * j > 14.3 * beta * math.log(j) + 60:
            break                                    # safely past the crossover
        j += 1
    return best


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------
def report_slice(fam, Rmax):
    print("=" * 82)
    print("d=1 NEAR-CYCLE SLICE  (research program I.1.2)")
    print(f"  census of odd-start d=1 paradoxical sequences with R<={Rmax}:")
    print("=" * 82)
    tot = 0
    for R in sorted(fam):
        rows = fam[R]
        tot += len(rows)
        ns = sorted(set(r[0] for r in rows))
        js = sorted(set(r[1] for r in rows))
        print(f"  R={R:>2}: {len(rows)} seq(s)  n={ns}  j={js}")
    print(f"  total: {tot} sequences; circuit counts present: {sorted(fam)}")
    print("  (RT App. B: every d=1 sequence is paradoxical; finiteness is open.)")


def report_reduction(fam):
    print("\n" + "=" * 82)
    print("Baker reduction per sequence (every link unconditional except M<=m^beta)")
    print("=" * 82)
    print(f"   {'n':>6} {'j':>3} {'q':>3} {'R':>2} {'Lambda':>8} {'rho_V':>6} "
          f"{'n<=rV j^13.3':>13} {'m':>5} {'H(j)':>9} {'M':>7} {'2^(j/2R)':>9} {'beta_obs':>8}")
    allok = True
    for R in sorted(fam):
        for (n, j, q, a, e) in sorted(fam[R]):
            r = reduction_row(n, j, q, R)
            ok = (r["closure_ok"] and r["rhin_ok"] and r["delta_rhin_ok"]
                  and r["n_le_bound"] and r["m_le_H"] and r["M_ge_lower"])
            allok = allok and ok
            print(f"   {n:>6} {j:>3} {q:>3} {R:>2} {r['Lambda']:>8.5f} {r['rho_V']:>6.2f} "
                  f"{'yes' if r['n_le_bound'] else 'NO':>13} {r['m']:>5} {r['H']:>9.1f} "
                  f"{r['M']:>7} {r['M_lower']:>9.2f} {r['beta_obs']:>8.3f}")
    print(f"\n   all reduction links verified: {allok}")
    print("   (closure n=(s(V)-2^j)/(2^j-3^q); Rhin Lambda>=j^-13.3 and "
          "2^j-3^q>=3^q j^-13.3;")
    print("    m<=H(j); pigeonhole M>=2^(j/2R)-1.  beta_obs=logM/logm is the least")
    print("    beta for which M<=m^beta holds on that sequence.)")
    betas = [reduction_row(n, j, q, R)["beta_obs"]
             for R in fam for (n, j, q, a, e) in fam[R]]
    print(f"   observed excursion exponents beta_obs in "
          f"[{min(betas):.2f}, {max(betas):.2f}] over the whole slice.")


def report_cutoffs(Rmax):
    print("\n" + "=" * 82)
    print("Conditional length cutoff J0(R,beta) -- the (d) collision 2^(j/2R) <= H(j)^beta")
    print("  above J0 no paradoxical d=1 sequence with R circuits exists (given M<=m^beta):")
    print("=" * 82)
    betas = [2.0, 3.0, 4.0]
    print(f"   {'R':>3} | " + " ".join(f"beta={b:<4.1f} -> J0" for b in betas))
    for R in range(1, Rmax + 1):
        cells = " ".join(f"{cutoff_d1(R, b):>13}" for b in betas)
        print(f"   {R:>3} | {cells}")
    print("   The cutoff GROWS with R (base 2^{1/2R} -> 1) and with beta, but is")
    print("   FINITE for every fixed (R,beta): exponential excursion beats any")
    print("   polynomial m^beta.  Contrast the uniform (all-R) RT cutoff 17396,")
    print("   which needs the delay heuristic too; here R is fixed so the structural")
    print("   pigeonhole M>=2^(j/2R) alone closes the collision.")


def report_theorem():
    print("\n" + "=" * 82)
    print("CONDITIONAL FINITENESS THEOREM (d=1, fixed R)  and the missing hypothesis")
    print("=" * 82)
    print("""  Theorem.  Fix R.  Suppose the excursion bound  M <= m^beta  holds on the
  d=1, R-circuit slice (m = least odd term, M = excursion, some fixed beta).
  Then there are only FINITELY many paradoxical sequences with T^j(n)=n+1 and R
  circuits.  Explicitly the length is bounded, j <= J0(R,beta), and for each
  admissible j only finitely many starts occur
  (per-length finiteness: n <= 2^j 3^j, RT.finite_paradoxical_of_length).

  Proof (reduction above): closure identity + Rhin bound the start polynomially
  and the least odd term by H(j)=O(j^14.3); the pigeonhole gives the excursion a
  2^{j/(2R)} lower bound; M<=m^beta collides the two and caps j.  Every step is
  unconditional EXCEPT M<=m^beta.

  MISSING HYPOTHESIS (the exact Collatz wall for this slice):
      M <= m^beta          (the excursion part of RT Conjecture 6.2),
  equivalently a polynomial bound on the excursion in terms of the least odd
  term.  Observed beta_obs stays small on the whole computed slice (see above),
  so the hypothesis is empirically comfortable -- but it is unproved, and a
  bound uniform over ALL R (not just each fixed R) is the full Collatz/CST wall.""")


# --------------------------------------------------------------------------
# Self-tests
# --------------------------------------------------------------------------
def self_test(fam, Rmax, nmax):
    print("\n" + "=" * 82)
    print("SELF-TESTS")
    print("=" * 82)
    # (1) known slice contents for the computed range
    got = {R: sorted(set(r[0] for r in rows)) for R, rows in fam.items()}
    if nmax >= 5_000_000:
        assert got.get(3) == [7, 9, 19, 25], got.get(3)
        assert got.get(8) == [333], got.get(8)
        assert got.get(10) == [667, 889], got.get(10)
        assert set(fam) == {3, 8, 10}, sorted(fam)
        print("  [ok] slice census == {R=3:{7,9,19,25}, R=8:{333}, R=10:{667,889}} "
              f"(n<={nmax:,})")
    # (2) every reduction link holds on every sequence
    bad = []
    for R in fam:
        for (n, j, q, a, e) in fam[R]:
            r = reduction_row(n, j, q, R)
            if not (r["closure_ok"] and r["rhin_ok"] and r["delta_rhin_ok"]
                    and r["n_le_bound"] and r["m_le_H"] and r["M_ge_lower"]):
                bad.append((n, j))
    assert not bad, f"reduction failed on {bad}"
    print("  [ok] closure + Rhin + m<=H(j) + pigeonhole verified on all sequences")
    # (3) closure identity two ways: n from closure == actual n
    for R in fam:
        for (n, j, q, a, e) in fam[R]:
            sV = remainder_from_parity(parity_vector(n, j))
            assert (2 ** j - 3 ** q) * n == sV - 2 ** j, (n, j)
    print("  [ok] closure identity (2^j-3^q)n = s(V) - 2^j exact on all sequences")
    # (4) cutoff monotone in R and beta, and finite
    for b in (2.0, 3.0):
        cs = [cutoff_d1(R, b) for R in range(1, Rmax + 1)]
        assert all(cs[i] <= cs[i + 1] for i in range(len(cs) - 1)), cs
        assert all(0 < c < 10 ** 7 for c in cs), cs
    assert cutoff_d1(3, 3.0) > cutoff_d1(3, 2.0)
    print("  [ok] J0(R,beta) finite, non-decreasing in R and in beta")
    print("  all self-tests passed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--Rmax", type=int, default=10)
    ap.add_argument("--nmax", type=int, default=5_000_000)
    ap.add_argument("--jmax", type=int, default=220)
    ap.add_argument("--no-selftest", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    fam = find_d1_by_R(args.Rmax, args.nmax, args.jmax)
    dt = time.time() - t0

    report_slice(fam, args.Rmax)
    report_reduction(fam)
    report_cutoffs(args.Rmax)
    report_theorem()
    if not args.no_selftest:
        self_test(fam, args.Rmax, args.nmax)
    print(f"\nDONE: d=1 slice R<={args.Rmax} closed conditionally on M<=m^beta; "
          f"census scan {dt:.1f}s.")


if __name__ == "__main__":
    main()
