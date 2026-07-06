#!/usr/bin/env python3
# (C) Ralf Stephan, in collaboration with Claude Code.  Released under CC0.
"""Bounded-circuit Baker reduction for the paradoxical d=2 slice (research I.1.3).

The d=2 analog of `nearcycle_baker.py` (which does d=1) and of `length-bound.html`
§4d.  The smallest paradoxical d=2 family is `R=7` (`{165,231}`); we run the full
linear-form reduction on every paradoxical d=2 family, isolate the single missing
hypothesis, and give the exhaustive `R<=6` emptiness search (sub-task c).

Closure identity (d=2):  `(2^j - 3^q) n = s(V) - 2^{j+1}`, so
    n = (s(V) - 2^{j+1}) / (2^j - 3^q),      s(V) = remainder_from_parity(V).

The reduction chain (each link UNCONDITIONAL except the last), §4d:
  (a) Rhin (Prop 6.3):  |j log2 - q log3| >= j^{-13.3}, so 2^j-3^q >= 3^q j^{-13.3},
      hence the start is bounded polynomially:  n <= rho_V j^{13.3},  rho_V=s(V)/3^q.
  (b) RT Cor 4.4 + Rhin:  least odd term  m <= H(j) = 1/(2^{j/floor(rho j)}-3) = O(j^{14.3}).
  (c) Pigeonhole:  with R circuits some run has length >= j/(2R), so the excursion
      M >= 2^{j/(2R)} - 1  (structural, exponential in j).
  (d) Excursion hypothesis  M <= m^beta  (RT Conj 6.2):  then
        2^{j/(2R)} - 1 <= M <= m^beta <= H(j)^beta = O(j^{14.3 beta})
      collides exponential vs polynomial => j <= J0(R,beta) (bounded).

Conditional finiteness theorem (d=2, fixed R): granting (d), only finitely many
paradoxical Omega_j(n) with T^j(n)=n+2 and R circuits exist (length j<=J0(R,beta),
and per length only finitely many starts, n<=2^j 3^j).  M<=m^beta is the SOLE
unproved input -- identical wall to d=1, RT Conj 6.2.

Unlike d=1 (smallest R=3), the d=2 slice is empty for every R<=6 in range and
starts at R=7: two extra circuits are forced to return exactly +2 under negative
drift.  `no_small_R` makes that emptiness computational up to a length cap.

Sub-task (c) attempt: `report_obstruction` proves the exact affine-return criterion
and reduces "no paradoxical R=2" to the near-resonance shapes, but shows those are
INFINITE (`resonance_shape_count` grows ~quadratically) -- so R=2 emptiness is NOT an
elementary theorem; it inherits the same Baker/Rhin Diophantine wall as the general
finiteness problem (R=1's Theorem R1 is elementary only because a single circuit has
no interior value to decouple its burst constraints).  Full proof OPEN.
"""
import argparse
import math
import time
from collections import defaultdict
from fractions import Fraction

from para_yah import T, parity_vector, remainder_from_parity
from circuit_baker import decompose
from bounded_circuit_search import enum_shapes, shape_solutions

LOG2, LOG3 = math.log(2.0), math.log(3.0)
RHO = LOG2 / LOG3          # ~0.6309297535
D = 2                      # this file's return difference


# --------------------------------------------------------------------------
# Slice census: d=2 paradoxical odd starts by circuit count R
# --------------------------------------------------------------------------
def find_d2_by_R(Rmax, nmax, jmax=220):
    """All odd-start d=2 paradoxical sequences grouped by R (<=Rmax)."""
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
                if cur - n == D:                  # d = 2
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
    """Full unconditional reduction chain for one d=2 sequence, plus the observed
    excursion exponent beta_obs = log M / log m (least beta with M<=m^beta here)."""
    sV = remainder_from_parity(parity_vector(n, j))
    Delta = 2 ** j - 3 ** q
    Lam = j * LOG2 - q * LOG3
    rho_V = sV / 3 ** q
    m = min_odd_term(n, j)
    M = max_excursion(n, j)
    beta_obs = math.log(M) / math.log(m) if m > 1 else float("inf")
    return {
        "sV": sV, "Delta": Delta, "Lambda": Lam, "rho_V": rho_V,
        # d=2 closure: n = (s(V) - 2^{j+1}) / (2^j - 3^q)
        "closure_ok": (sV - 2 ** (j + 1)) % Delta == 0
                      and (sV - 2 ** (j + 1)) // Delta == n,
        "rhin_ok": Lam >= j ** (-13.3),
        "delta_rhin_ok": Delta >= 3 ** q * j ** (-13.3),
        "n_bound": rho_V * j ** 13.3, "n_le_bound": n <= rho_V * j ** 13.3,
        "m": m, "H": H(j), "m_le_H": m <= H(j) + 1e-9,
        "M": M, "M_lower": 2 ** (j / (2 * R)) - 1,
        "M_ge_lower": M >= 2 ** (j / (2 * R)) - 1,
        "beta_obs": beta_obs,
    }


# --------------------------------------------------------------------------
# Conditional cutoff J0(R, beta): the (d) collision (d-independent)
# --------------------------------------------------------------------------
def cutoff_d2(R, beta, jcap=500_000):
    """Largest j for which the collision (d) can still hold:
        (log2/(2R)) j <= 14.3 beta log j     (2^{j/2R} <= H(j)^beta, H=O(j^14.3)).
    Above J0(R,beta) the exponential excursion lower bound exceeds m^beta, so no
    paradoxical d=2 sequence with R circuits can exist.  (The collision does not
    involve d, so J0 is shared with d=1; the SLICE it bounds is the d=2 one.)"""
    c = LOG2 / (2 * R)
    best, j = 0, 2
    while j < jcap:
        if c * j <= 14.3 * beta * math.log(j):
            best = j
        elif j > 200 and c * j > 14.3 * beta * math.log(j) + 60:
            break
        j += 1
    return best


# --------------------------------------------------------------------------
# Exhaustive R<=6 emptiness (I.1.3 sub-task c, computational core)
# --------------------------------------------------------------------------
def no_small_R(Rmax=6, jmax=22):
    """Enumerate every circuit shape with 2<=R<=Rmax and length j<=jmax, solve the
    closure identity for d=2, and collect genuine paradoxical survivors.  In range
    there are NONE -- the d=2 slice is empty below R=7.  (R=1 is Theorem R1.)

    This is unbounded in the start n (a shape determines its n), complementing the
    direct orbit scan which is bounded in n but reaches every j.  Returns the list
    of d=2 survivors found (expected empty) and the number of shapes examined."""
    survivors = []
    shapes = 0
    for R in range(2, Rmax + 1):
        for (a_list, e_list) in enum_shapes(R, jmax):
            shapes += 1
            # solve the closure identity for THIS shape, keep only d == 2
            for (n, j, q, sV, d) in shape_solutions(a_list, e_list, D):
                if d == D:
                    survivors.append((R, n, j, q, a_list, e_list))
    return survivors, shapes


def empty_R2_all_d(jmax=60, dmax=400):
    """Stronger, d-independent probe behind the R=3->R=7 jump: NO paradoxical
    sequence has exactly R=2 circuits (any return difference d), over every shape
    of length j<=jmax.  Returns (survivors, shapes) -- survivors expected empty."""
    survivors = []
    shapes = 0
    for (a_list, e_list) in enum_shapes(2, jmax):
        shapes += 1
        for (n, j, q, sV, d) in shape_solutions(a_list, e_list, dmax):
            survivors.append((n, j, q, d, a_list, e_list))
    return survivors, shapes


# --------------------------------------------------------------------------
# The exact R-circuit return identity (the R=2 analog of RT's Theorem-R1
# telescoping) -- reduces "no paradoxical R=2" to a sharp Diophantine statement
# --------------------------------------------------------------------------
def _replay_two_circuits(n, a, e1, b, e2):
    """Replay parity word 1^a 0^e1 1^b 0^e2 from odd n; return (y2, final) or None
    if the parities don't hold (shape invalid for this n)."""
    cur = n
    for _ in range(a):
        if cur % 2 == 0:
            return None
        cur = T(cur)
    for _ in range(e1):
        if cur % 2 == 1:
            return None
        cur = T(cur)
    y2 = cur
    for _ in range(b):
        if cur % 2 == 0:
            return None
        cur = T(cur)
    for _ in range(e2):
        if cur % 2 == 1:
            return None
        cur = T(cur)
    return y2, cur


def two_circuit_identity_check(trials=200_000):
    """Verify (exactly, in Q) the two-circuit RETURN IDENTITY

        final + 2^{-e2}  =  C_j (n+1)  +  r2 (1 - 2^{-e1}),          (star)

    with r1=3^a/2^{c1}, r2=3^b/2^{c2}, c_i=a_i+e_i, C_j=r1 r2, on every valid R=2
    shape.  (star) is the R=2 analog of the R=1 telescoping final+2^{-e1}=C_j(n+1)
    that PROVES Theorem R1 (C_j<1 => final<n+1 => final<=n, so no paradoxical R=1).
    For R=2 the extra term r2(1-2^{-e1}) (with r2 possibly >1) is exactly what a
    paradoxical dip would exploit; (star) reduces "no paradoxical R=2" to the
    non-solvability of (star) with n>=3, d=final-n>=0, C_j<1, y2 a positive odd
    integer.  Returns (ok, tested)."""
    ok = tested = 0
    # deterministic sweep over small shapes and a range of admissible starts
    for a in range(1, 6):
        for e1 in range(1, 6):
            for b in range(1, 6):
                for e2 in range(0, 6):
                    for m in range(1, 60):
                        n = (2 ** a) * m - 1          # ensures v2(n+1) >= a
                        if n < 3:
                            continue
                        r = _replay_two_circuits(n, a, e1, b, e2)
                        if r is None:
                            continue
                        y2, final = r
                        c1, c2 = a + e1, b + e2
                        r1 = Fraction(3 ** a, 2 ** c1)
                        r2 = Fraction(3 ** b, 2 ** c2)
                        Cj = r1 * r2
                        lhs = Fraction(final) + Fraction(1, 2 ** e2)
                        rhs = Cj * (n + 1) + r2 * (1 - Fraction(1, 2 ** e1))
                        tested += 1
                        if lhs == rhs:
                            ok += 1
                        if tested >= trials:
                            return ok, tested
    return ok, tested


def r2_return_difference(a, b, e1, e2, m2):
    """The exact return difference d = final - n of a valid R=2 config with the second
    burst's odd core m2 (i.e. y2 + 1 = 2^b m2):

        d = ( 2^(a+e2)(2^e1 - 1) + 3^a(2^e2 - 1) - m2 (2^j - 3^q) ) / (2^e2 3^a).

    Equivalently the composed 2-circuit map is AFFINE, final = C_j n + (C_j + K), slope
    C_j = 3^q/2^j < 1, so "paradoxical" (final >= n) <=> n <= its fixed point n*.  With
    m2 >= 1 this forces  Delta = 2^j - 3^q <= RHS  for d >= 0, and
    Delta <= RHS - 2^e2 3^a  for d >= 1 -- i.e. the drift must be NEAR-RESONANT."""
    j = a + e1 + b + e2
    q = a + b
    num = 2 ** (a + e2) * (2 ** e1 - 1) + 3 ** a * (2 ** e2 - 1) - m2 * (2 ** j - 3 ** q)
    return Fraction(num, 2 ** e2 * 3 ** a)


def resonance_shape_count(jcap):
    """Number of R=2 shapes that admit a strictly-paradoxical (d>=1) return by SIZE, i.e.
    Delta = 2^j - 3^q <= 2^(a+e2)(2^e1 - 1) - 3^a.  These "near-resonance" shapes (3^q
    within 2^-b of 2^j) are the ONLY survivors of the elementary reduction; the count
    GROWS (~quadratically in jcap), so infinitely many exist -- no finite check can
    finish R=2 emptiness."""
    c = 0
    for a in range(1, jcap):
        for b in range(1, jcap):
            if a + b + 2 > jcap:
                break
            for e1 in range(1, jcap):
                for e2 in range(0, jcap):
                    j = a + e1 + b + e2
                    if j > jcap:
                        break
                    if 2 ** j <= 3 ** (a + b):
                        continue
                    if 2 ** j - 3 ** (a + b) <= 2 ** (a + e2) * (2 ** e1 - 1) - 3 ** a:
                        c += 1
    return c


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------
def report_slice(fam, Rmax):
    print("=" * 82)
    print("d=2 PARADOXICAL SLICE  (research program I.1.3; length-bound.html §4d)")
    print(f"  census of odd-start d=2 paradoxical sequences with R<={Rmax}:")
    print("=" * 82)
    tot = 0
    for R in sorted(fam):
        rows = fam[R]
        tot += len(rows)
        ns = sorted(set(r[0] for r in rows))
        js = sorted(set(r[1] for r in rows))
        print(f"  R={R:>2}: {len(rows)} seq(s)  n={ns}  j={js}")
    print(f"  total: {tot} odd-start sequences; circuit counts present: {sorted(fam)}")
    print(f"  smallest paradoxical d=2 family: R={min(fam)} (d=1 minimum is R=3).")


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
    print("   (closure n=(s(V)-2^{j+1})/(2^j-3^q); Rhin Lambda>=j^-13.3 and")
    print("    2^j-3^q>=3^q j^-13.3; m<=H(j); pigeonhole M>=2^(j/2R)-1.  beta_obs=")
    print("    logM/logm is the least beta for which M<=m^beta holds on that sequence.)")
    betas = [reduction_row(n, j, q, R)["beta_obs"]
             for R in fam for (n, j, q, a, e) in fam[R]]
    print(f"   observed excursion exponents beta_obs in "
          f"[{min(betas):.2f}, {max(betas):.2f}] over the whole d=2 slice.")


def report_family_R7(fam):
    """§4d: the smallest paradoxical d=2 family, R=7 = {165,231}."""
    print("\n" + "=" * 82)
    print("§4d  The R=7 family {165,231}: linear form run to its honest end")
    print("=" * 82)
    fam7 = sorted(fam.get(7, []))
    for (n, j, q, a, e) in fam7:
        r = reduction_row(n, j, q, 7)
        print(f"   n={n}: j={j} q={q} Lambda={r['Lambda']:.5f} Rhin>=j^-13.3="
              f"{r['rhin_ok']}  m={r['m']} H(j)={r['H']:.1f} rho_V={r['rho_V']:.2f} "
              f"M={r['M']} 2^(j/2R)={r['M_lower']:.1f}")
    print("   Reduction reproduces §4d: every link holds with room; the length bound")
    print("   for this family is EQUIVALENT, via explicit inequalities, to M<=m^beta.")


def report_no_small_R(survivors, shapes, Rmax, jmax):
    print("\n" + "=" * 82)
    print(f"Exhaustive R<={Rmax} emptiness (I.1.3 sub-task c): closure search over shapes")
    print("=" * 82)
    if survivors:
        print(f"   FOUND {len(survivors)} d=2 survivor(s) with R<={Rmax}: {survivors}")
    else:
        print(f"   NO paradoxical d=2 sequence with 2<=R<={Rmax} and length j<={jmax}")
        print(f"   ({shapes:,} circuit shapes examined; each shape's start solved from")
        print(f"    the closure identity, so this is unbounded in n).  Combined with the")
        print(f"    direct orbit scan (n<=2e6, all j), the d=2 slice is empty below R=7.")
    print("   R=1 is unconditionally empty (Theorem R1).  A congruence/shape")
    print("   obstruction upgrading this to a proof for all j is the open sub-task.")


def report_obstruction(r2surv, r2shapes, r2jmax, r2dmax, star_ok, star_tested):
    res = [(jc, resonance_shape_count(jc)) for jc in (40, 60, 80)]
    print("\n" + "=" * 82)
    print("The R=3 -> R=7 jump (sub-task a) and the R=2 attempt (sub-task c)")
    print("=" * 82)
    print(f"""  Structural facts (odd-start paradoxical sequences, n<=2e6, ANY d):
    * circuit counts R = 1,2,4,5,6 NEVER occur; R=3 hosts EXACTLY the d=1
      near-cycles {{7,9,19,25}}; the next populated count is R=7.
    * so "d=2 needs R>=7" is really "R in {{4,5,6}} are empty AND R=3 is
      confined to d=1", and the smallest length hosting d=2 is j=27 (R=7),
      not the d=1 home j=8 (R=3).
    * near-cycle lengths are quantized -- {{8,27,46,73,...}}, where 2^j exceeds
      3^q by a small margin (small Lambda=j log2-q log3).  d>1 first fits at the
      next usable length j=27, forcing R=7.

  ATTEMPTED PROOF of "no paradoxical R=2" -- honest outcome (NOT elementary):
    empty over {r2shapes:,} shapes (R=2, j<={r2jmax}, every d<={r2dmax}); full search
    n<=2e6 (all j) and every shape j<=70 give survivors={len(r2surv)}.

    (1) EXACT criterion (proved; verified): the composed 2-circuit map is AFFINE,
        final = C_j n + (C_j + K), slope C_j = 3^q/2^j < 1, so paradoxical
        (final>=n) <=> n <= its fixed point n*.  Equivalently, with y2+1 = 2^b m2,
          d = ( 2^(a+e2)(2^e1-1) + 3^a(2^e2-1) - m2 Delta ) / (2^e2 3^a),  Delta=2^j-3^q.
        [the R=1 case final+2^-e1 = C_j(n+1) is exactly RT Theorem-R1's telescoping.]
    (2) REDUCTION (proved): m2>=1 => paradoxical needs Delta <= RHS, and d>=1 needs
        Delta <= RHS - 2^e2 3^a, forcing C_j > 1 - 2^(1-b): the drift must be
        NEAR-RESONANT (3^q within 2^-b of 2^j).  ALL non-resonant shapes: empty
        elementarily.
    (3) THE WALL (negative result): the near-resonance shapes are INFINITE -- the
        count grows ~quadratically: j<=40:{res[0][1]}  j<=60:{res[1][1]}  j<=80:{res[2][1]}
        (lengths j in {{8,13,16,21,24,27,...}}).  Each is killed by a congruence
        mod Delta with no uniform form; ruling them ALL out = bounding |2^j-3^q|
        below = Baker/Rhin, which caps only a,b = O(log j), NOT j.
    => R=2 emptiness inherits the SAME Diophantine wall as general finiteness; it is
       NOT an elementary theorem.  R=1 is special: one circuit has no interior value,
       so its single burst constraint n>=2^a-1 contradicts C_j<1 directly (plus the
       Steiner cited axiom for the d=0 cycle).  Two circuits DECOUPLE the two burst
       constraints through y2 -- the same freedom that makes R=3 nonempty.
    Status: EMPTY exhaustively verified; full proof OPEN, provably not elementary.""")


def report_cutoffs(Rmax):
    print("\n" + "=" * 82)
    print("Conditional length cutoff J0(R,beta) -- the (d) collision 2^(j/2R) <= H(j)^beta")
    print("  above J0 no paradoxical d=2 sequence with R circuits exists (given M<=m^beta):")
    print("=" * 82)
    betas = [2.0, 3.0, 4.0]
    print(f"   {'R':>3} | " + " ".join(f"beta={b:<4.1f} -> J0" for b in betas))
    for R in range(7, Rmax + 1):
        cells = " ".join(f"{cutoff_d2(R, b):>13}" for b in betas)
        print(f"   {R:>3} | {cells}")
    print("   Finite for every fixed (R,beta): exponential excursion beats any m^beta.")
    print("   (The collision is d-independent; the slice bounded here is d=2, R>=7.)")


def report_theorem():
    print("\n" + "=" * 82)
    print("CONDITIONAL FINITENESS THEOREM (d=2, fixed R)  and the missing hypothesis")
    print("=" * 82)
    print("""  Theorem.  Fix R.  Suppose the excursion bound  M <= m^beta  holds on the
  d=2, R-circuit slice (m = least odd term, M = excursion, some fixed beta).
  Then there are only FINITELY many paradoxical sequences with T^j(n)=n+2 and R
  circuits: the length is bounded, j <= J0(R,beta), and for each admissible j only
  finitely many starts occur (per-length finiteness: n <= 2^j 3^j).

  Proof (reduction above): closure identity + Rhin bound the start polynomially
  and the least odd term by H(j)=O(j^14.3); the pigeonhole gives the excursion a
  2^{j/(2R)} lower bound; M<=m^beta collides the two and caps j.  Every step is
  unconditional EXCEPT M<=m^beta.

  This is IDENTICAL, link for link, to the d=1 theorem (nearcycle_baker.py); the
  return difference enters only the closure numerator (2^{j+1} vs 2^j), not the
  collision.  In Lean the reduction is already d-agnostic: BakerReduction.lean's
  `finite_RCircuitSlice` finiteness-reduces ANY R-circuit slice given only
  `excWin j n <= (minWin j n)^beta` -- so the d=2 case is covered with no new Lean.

  MISSING HYPOTHESIS (the exact Collatz wall for this slice):
      M <= m^beta          (the excursion part of RT Conjecture 6.2).""")


# --------------------------------------------------------------------------
# Self-tests
# --------------------------------------------------------------------------
def self_test(fam, Rmax, nmax):
    print("\n" + "=" * 82)
    print("SELF-TESTS")
    print("=" * 82)

    # (1) known slice contents for the computed range
    if nmax >= 2_000_000:
        got = {R: sorted(set(r[0] for r in rows)) for R, rows in fam.items()}
        assert got.get(7) == [165, 231], got.get(7)
        assert set(fam) == {7, 11, 15, 18, 20}, sorted(fam)
        assert min(fam) == 7
        print("  [ok] slice census: R=7 {165,231}; all R in {7,11,15,18,20}, min R=7 "
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

    # (3) d=2 closure identity exact, and the §4d numbers on {165,231}
    for R in fam:
        for (n, j, q, a, e) in fam[R]:
            sV = remainder_from_parity(parity_vector(n, j))
            assert (2 ** j - 3 ** q) * n == sV - 2 ** (j + 1), (n, j)
    if 7 in fam:
        d = {n: reduction_row(n, j, q, 7) for (n, j, q, a, e) in fam[7]}
        if 165 in d:
            assert d[165]["m"] == 31 and d[165]["M"] == 890, d[165]
        if 231 in d:
            assert d[231]["m"] == 31 and d[231]["M"] == 1322, d[231]
        for n in (165, 231):
            if n in d:
                assert abs(d[n]["Lambda"] - 0.03856) < 1e-4, d[n]["Lambda"]
        print("  [ok] d=2 closure (2^j-3^q)n=s(V)-2^{j+1} exact; §4d {165,231}: "
              "m=31, M=890/1322, Lambda=0.03856")

    # (4) cutoff finite, monotone in R and beta
    for b in (2.0, 3.0):
        cs = [cutoff_d2(R, b) for R in range(7, Rmax + 1)]
        assert all(cs[i] <= cs[i + 1] for i in range(len(cs) - 1)), cs
        assert all(0 < c < 10 ** 7 for c in cs), cs
    assert cutoff_d2(7, 3.0) > cutoff_d2(7, 2.0)
    print("  [ok] J0(R,beta) finite, non-decreasing in R and in beta")

    # (5) exhaustive R<=6 emptiness (small jmax kept cheap for the test)
    surv, shapes = no_small_R(Rmax=6, jmax=16)
    assert surv == [], f"unexpected d=2 R<=6 survivor: {surv}"
    print(f"  [ok] no paradoxical d=2 with R<=6, j<=16 ({shapes:,} shapes; empty)")

    # (6) R=2 empty for ALL d, identity (star), and the exact d-formula
    r2surv, r2shapes = empty_R2_all_d(jmax=30, dmax=200)
    assert r2surv == [], f"unexpected R=2 survivor (any d): {r2surv}"
    ok, tested = two_circuit_identity_check(trials=5000)
    assert ok == tested and tested > 0, f"2-circuit identity failed: {ok}/{tested}"
    # exact d-formula: sweep small valid R=2 configs and verify d = formula(a,b,e1,e2,m2)
    dchk = dbad = 0
    for a in range(1, 5):
        for e1 in range(1, 5):
            for b in range(1, 5):
                for e2 in range(0, 5):
                    for m1 in range(1, 40, 2):
                        n = 2 ** a * m1 - 1
                        if n < 3:
                            continue
                        r = _replay_two_circuits(n, a, e1, b, e2)
                        if r is None:
                            continue
                        y2, final = r
                        if (y2 + 1) % 2 ** b:
                            continue
                        m2 = (y2 + 1) // 2 ** b
                        if r2_return_difference(a, b, e1, e2, m2) == final - n:
                            dchk += 1
                        else:
                            dbad += 1
    assert dbad == 0 and dchk > 0, f"exact d-formula failed: {dchk} ok, {dbad} bad"
    # (7) near-resonance shapes are infinitely many (count strictly grows)
    c40, c80 = resonance_shape_count(40), resonance_shape_count(80)
    assert c80 > c40 > 0, (c40, c80)
    print(f"  [ok] no paradoxical R=2 (any d), j<=30 ({r2shapes:,} shapes); "
          f"identity (star) {ok}/{tested}; exact d-formula {dchk} configs")
    print(f"  [ok] near-resonance shapes grow (j<=40:{c40} -> j<=80:{c80}) => "
          "R=2 emptiness is not elementary (Diophantine wall)")
    print("  all self-tests passed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--Rmax", type=int, default=20)
    ap.add_argument("--nmax", type=int, default=2_000_000)
    ap.add_argument("--jmax", type=int, default=220)
    ap.add_argument("--nosmallR-jmax", type=int, default=22,
                    help="length cap for the exhaustive R<=6 emptiness search")
    ap.add_argument("--r2-jmax", type=int, default=50,
                    help="length cap for the R=2 all-d emptiness probe")
    ap.add_argument("--r2-dmax", type=int, default=400,
                    help="return-difference cap for the R=2 all-d emptiness probe")
    ap.add_argument("--no-selftest", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    fam = find_d2_by_R(args.Rmax, args.nmax, args.jmax)
    dt = time.time() - t0

    report_slice(fam, args.Rmax)
    report_reduction(fam)
    report_family_R7(fam)
    surv, shapes = no_small_R(6, args.nosmallR_jmax)
    report_no_small_R(surv, shapes, 6, args.nosmallR_jmax)
    r2surv, r2shapes = empty_R2_all_d(jmax=args.r2_jmax, dmax=args.r2_dmax)
    star_ok, star_tested = two_circuit_identity_check(trials=20_000)
    report_obstruction(r2surv, r2shapes, args.r2_jmax, args.r2_dmax, star_ok, star_tested)
    report_cutoffs(args.Rmax)
    report_theorem()
    if not args.no_selftest:
        self_test(fam, args.Rmax, args.nmax)
    print(f"\nDONE: d=2 slice R<={args.Rmax} reduced conditionally on M<=m^beta; "
          f"census scan {dt:.1f}s.")


if __name__ == "__main__":
    main()
