/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Cycles

/-!
# Infinite right-truncatable primes — [DubOst06] Conjecture 1 at `b = 7`

`DubC/Cycles.lean` settles [DubOst06] **Conjecture 2** at `b = 7`: for every real `ξ > 0` the
sequence `⌊ξ·7ⁿ⌋` has infinitely many composite terms.  Their §3 derives **Conjecture 1** — no
infinite right-truncatable prime in base `b` — from Conjecture 2, for arbitrary `b`.  This file
does not follow that route, and does not need it.

## Why not §3

The §3 implication builds `ξ = lim pₙ/bⁿ` from a prime chain and identifies `⌊ξbⁿ⌋` with `pₙ`.
That identification fails on exactly one family: if the digit word ends in `(b−1)^∞` then
`ξ·bⁿ = pₙ + 1` exactly, and the floor is off by one.  Dubickas closes that branch with a
separate Fermat argument.

Going direct there is no branch to close.  The certificate `CoreClosed`/`CoreDet` forces the
digit word of *any* admissible chain to be eventually periodic, and an all-`(b−1)` word is
eventually periodic like any other, so the Euler-return engine of
`DubC.infinite_composites_of_periodic_digits` ([Dub09] Theorem 4) disposes of it with everything
else.  No real number, no series, no Fermat lemma.

## What had to be generalized

Every step of `DubC/Certificate.lean` and `DubC/CoreCertificate.lean` is *stated* for
`DubC.floorPow ξ a n` but *uses* only three facts about that sequence, collected here as
`DubC.IsDigitRec` together with unboundedness:

* `xₙ₊₁ = a·xₙ + dₙ` (`DubC.floorPow_succ`),
* `0 ≤ dₙ < a` (`DubC.floorDigit_nonneg`, `DubC.floorDigit_lt`),
* `‖xₙ‖ → ∞` (`DubC.tendsto_natAbs_floorPow`).

A prime chain supplies all three, the last one for free from `pₙ₊₁ ≥ b·pₙ`.  So the plumbing is
re-proved here for an abstract `x`, and `DubC.isDigitRec_floorPow` records that the old case is
an instance.  Nothing in `DubC/Certificate.lean` or `DubC/CoreCertificate.lean` is edited — the
two `native_decide` modules downstream of them must not be rebuilt without reason.

## Results

* `DubC.no_infiniteTruncatablePrime_seven` — **there is no infinite right-truncatable prime in
  base 7**, on the same trusted base as `DubC.Cycles.infinite_composites_seven`: no new
  `native_decide`, no cited-literature axiom.
* `DubC.no_infiniteTruncatablePrime_three`, `_four`, `_five`, `_six` — the same statement for
  `b ≤ 6`, from the hand certificates of `DubC/Verdict.lean`.  That is [MPP+24] Lemma A.1, whose
  authors prove it by alphabet collapse plus Fermat without knowing it is [DubOst06]
  Conjecture 1.

Two remarks on the statement `DubC.InfiniteTruncatablePrime`.  The appended digit is **not**
required to be prime — primality is a condition on the truncations, and the largest base-10
right-truncatable prime `73939133` has digits `9` and `1`.  And `p 0` is not required to be a
single digit, so the chain may start at *any* prime; since the theorem is a negation, dropping
that restriction strengthens it, and it is the form [MPP+24] Lemma A.1 uses.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.  Conjecture 1 and the §3 equivalence.
* **[MPP+24]** S. J. Miller et al., *Walking to infinity along some number theory sequences*,
  Integers **24** (2024).  Lemma A.1: `b = 3, 4, 5, 6`.
-/

namespace DubC

open Filter

/-! ### Base-`a` digit recurrences

The three properties of `⌊ξaⁿ⌋` that the certificate machinery actually consumes. -/

/-- A **base-`a` digit recurrence**: `xₙ₊₁ = a·xₙ + dₙ` with digits `0 ≤ dₙ < a`.  The floor
sequence of a real number is one instance (`DubC.isDigitRec_floorPow`); a right-truncatable
prime chain is another (`DubC.exists_digitRec_of_truncatable`). -/
structure IsDigitRec (a : ℕ) (x dg : ℕ → ℤ) : Prop where
  /-- The recurrence itself. -/
  step : ∀ n, x (n + 1) = (a : ℤ) * x n + dg n
  /-- Digits are nonnegative. -/
  nonneg : ∀ n, 0 ≤ dg n
  /-- Digits are less than the base. -/
  lt : ∀ n, dg n < (a : ℤ)

/-- The floor sequence of a real number is a base-`a` digit recurrence — so the results below
subsume the `⌊ξaⁿ⌋` forms of `DubC/Certificate.lean`. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem isDigitRec_floorPow {a : ℕ} (ha : 0 < a) (ξ : ℝ) :
    IsDigitRec a (floorPow ξ a) (floorDigit ξ a) :=
  ⟨floorPow_succ ξ a, floorDigit_nonneg ξ a, floorDigit_lt ξ ha⟩

/-! ### The plumbing, without `ξ`

Verbatim analogues of `DubC.step_floorPow`, `DubC.digits_periodic_of_residues_periodic` and the
tail of `DubC.digits_eventually_periodic_of_coreCert`, with the floor sequence replaced by an
abstract digit recurrence. -/

/-- **The residue path is admissible.**  If the residues of `xₙ` modulo `M` are units from `N`
on, the shifted residue sequence is an infinite path of the base-`a` coprimality subshift. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem step_of_digitRec {a M : ℕ} [NeZero M] {x dg : ℕ → ℤ} (h : IsDigitRec a x dg) {N : ℕ}
    (hunit : ∀ n, N ≤ n → Cop M ((x n : ZMod M))) (j : ℕ) :
    Step a M ((x (N + j) : ZMod M)) ((x (N + (j + 1)) : ZMod M)) := by
  refine ⟨hunit _ (by omega), hunit _ (by omega), (dg (N + j)).toNat, ?_, ?_⟩
  · have h1 := h.nonneg (N + j)
    have h2 := h.lt (N + j)
    omega
  · have hcast : (((dg (N + j)).toNat : ℕ) : ZMod M) = ((dg (N + j) : ZMod M)) := by
      rw [← Int.cast_natCast (R := ZMod M), Int.toNat_of_nonneg (h.nonneg _)]
    rw [hcast]
    have hidx : N + (j + 1) = (N + j) + 1 := by omega
    rw [hidx, h.step (N + j)]
    push_cast
    ring

/-- **Digits are determined by residues.**  If the residues of `xₙ` modulo `M` are `L`-periodic
from `n₁` on and `a ≤ M`, then so is the digit word: two digits congruent mod `M` and both in
`[0, a) ⊆ [0, M)` are equal. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem digits_periodic_of_res_periodic {a M : ℕ} (haM : a ≤ M) [NeZero M]
    {x dg : ℕ → ℤ} (h : IsDigitRec a x dg) {n₁ L : ℕ}
    (hres : ∀ q, n₁ ≤ q → ((x (q + L) : ZMod M)) = ((x q : ZMod M))) :
    ∀ m, n₁ ≤ m → dg (m + L) = dg m := by
  have key : ∀ q : ℕ, ((dg q : ZMod M))
      = ((x (q + 1) : ZMod M)) - (a : ZMod M) * ((x q : ZMod M)) := by
    intro q
    have hq : ((x (q + 1) : ZMod M))
        = (a : ZMod M) * ((x q : ZMod M)) + ((dg q : ZMod M)) := by
      rw [h.step q]; push_cast; ring
    rw [hq]; ring
  intro m hm
  have hd : ((dg (m + L) : ZMod M)) = ((dg m : ZMod M)) := by
    rw [key (m + L), key m]
    have e1 : m + L + 1 = (m + 1) + L := by omega
    rw [e1, hres (m + 1) (by omega), hres m (by omega)]
  have hdvd : ((M : ℤ)) ∣ (dg (m + L) - dg m) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    rw [hd, sub_self]
  have hb1 := h.nonneg (m + L)
  have hb2 := h.lt (m + L)
  have hb3 := h.nonneg m
  have hb4 := h.lt m
  have haM' : (a : ℤ) ≤ (M : ℤ) := by exact_mod_cast haM
  have habs : |dg (m + L) - dg m| < (M : ℤ) := by
    rw [abs_lt]; omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- The shared tail of the two certificate forms: an eventually periodic residue path gives an
eventually periodic digit word, after transporting the period back to absolute indices. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem digits_periodic_of_path {a M : ℕ} (haM : a ≤ M) [NeZero M]
    {x dg : ℕ → ℤ} (h : IsDigitRec a x dg) {N j₀ L : ℕ} (hL : 0 < L)
    (hjper : ∀ j, j₀ ≤ j → ((x (N + (j + L)) : ZMod M)) = ((x (N + j) : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → dg (m + L) = dg m := by
  refine ⟨N + j₀, L, hL, digits_periodic_of_res_periodic haM h ?_⟩
  intro q hq
  have h1 := hjper (q - N) (by omega)
  have e1 : N + (q - N + L) = q + L := by omega
  have e2 : N + (q - N) = q := by omega
  rw [e1, e2] at h1
  exact h1

/-- The rank certificate makes the digit word of any base-`a` digit recurrence eventually
periodic, once its residues are units.  (Abstract form of
`DubC.digits_eventually_periodic_of_certOK`.) -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem digits_eventually_periodic_of_certOK' {a M : ℕ} (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank) {x dg : ℕ → ℤ} (h : IsDigitRec a x dg)
    {N : ℕ} (hunit : ∀ n, N ≤ n → Cop M ((x n : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → dg (m + L) = dg m := by
  obtain ⟨j₀, L, hL, hjper⟩ := eventually_periodic_of_rank rank (rank_le_of_certOK hcert)
    (unique_of_certOK hcert) (fun j => ((x (N + j) : ZMod M))) (step_of_digitRec h hunit)
  exact digits_periodic_of_path haM h hL hjper

/-- The compressed-core certificate makes the digit word of any base-`a` digit recurrence
eventually periodic, once its residues are units.  (Abstract form of
`DubC.digits_eventually_periodic_of_coreCert`.) -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem digits_eventually_periodic_of_coreCert' {a M : ℕ} (haM : a ≤ M) [NeZero M]
    (K : ZMod M → Prop) (hclosed : CoreClosed a M K) (hdet : CoreDet a M K)
    {x dg : ℕ → ℤ} (h : IsDigitRec a x dg)
    {N : ℕ} (hunit : ∀ n, N ≤ n → Cop M ((x n : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → dg (m + L) = dg m := by
  obtain ⟨j₀, L, hL, hjper⟩ := eventually_periodic_of_core K hclosed (det_of_coreDet hdet)
    (fun j => ((x (N + j) : ZMod M))) (step_of_digitRec h hunit)
  exact digits_periodic_of_path haM h hL hjper

/-! ### No digit recurrence is all-prime

The counterpart of `DubC.infinite_composites_floorPow_of_digits`, and simpler than it: there the
terms had to be *shown* eventually prime by contradiction, here primality is the hypothesis. -/

/-- **A prime digit recurrence is impossible, given periodic digits.**  If every term of a
base-`a` digit recurrence with unbounded terms is prime and some mechanism forces the digit word
to be eventually periodic once the residues are units, the situation is contradictory: the terms
are eventually primes exceeding `M`, hence units, so the mechanism fires and [Dub09] Theorem 4
produces a composite term. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_truncatable"]
theorem not_forall_prime_of_digits {a M : ℕ} (ha : 2 ≤ a) [NeZero M] {x dg : ℕ → ℤ}
    (h : IsDigitRec a x dg) (hgrow : Tendsto (fun n => (x n).natAbs) atTop atTop)
    (hprime : ∀ n, (x n).natAbs.Prime)
    (H : ∀ N : ℕ, (∀ n, N ≤ n → Cop M ((x n : ZMod M))) →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → dg (m + L) = dg m) : False := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hgrow (M + 1)
  have hunit : ∀ n, N ≤ n → Cop M ((x n : ZMod M)) := by
    intro n hn
    have hbig : M + 1 ≤ (x n).natAbs := hN n hn
    refine (cop_iff_isUnit _).mpr ?_
    refine isUnit_intCast_of_coprime ((Nat.Prime.coprime_iff_not_dvd (hprime n)).mpr fun hd => ?_)
    have := Nat.le_of_dvd hMpos hd
    omega
  obtain ⟨n₀, L, hL, hper⟩ := H N hunit
  obtain ⟨n, hn⟩ :=
    (infinite_composites_of_periodic_digits (a := (a : ℤ)) (by omega) h.step hL hper hgrow).nonempty
  exact hn.2 (hprime n)

/-- No base-`a` digit recurrence with unbounded terms is all-prime, if a rank certificate
`CertOK a M rank` exists for some `M ≥ a`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_truncatable"]
theorem not_forall_prime_of_certOK {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank) {x dg : ℕ → ℤ} (h : IsDigitRec a x dg)
    (hgrow : Tendsto (fun n => (x n).natAbs) atTop atTop)
    (hprime : ∀ n, (x n).natAbs.Prime) : False :=
  not_forall_prime_of_digits ha h hgrow hprime fun _ hunit =>
    digits_eventually_periodic_of_certOK' haM rank hcert h hunit

/-- No base-`a` digit recurrence with unbounded terms is all-prime, if a compressed core
`K` catches every cycle of the subshift modulo `M ≥ a` and is deterministic. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_truncatable"]
theorem not_forall_prime_of_coreCert {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (K : ZMod M → Prop) (hclosed : CoreClosed a M K) (hdet : CoreDet a M K)
    {x dg : ℕ → ℤ} (h : IsDigitRec a x dg)
    (hgrow : Tendsto (fun n => (x n).natAbs) atTop atTop)
    (hprime : ∀ n, (x n).natAbs.Prime) : False :=
  not_forall_prime_of_digits ha h hgrow hprime fun _ hunit =>
    digits_eventually_periodic_of_coreCert' haM K hclosed hdet h hunit

/-! ### Infinite right-truncatable primes -/

/-- **An infinite right-truncatable prime in base `b`** — the object of [DubOst06]
Conjecture 1: an infinite sequence of primes, each obtained from its predecessor by appending
one base-`b` digit on the right.  Equivalently, an infinite base-`b` digit string all of whose
truncations are prime.

Two deliberate omissions, both of which *strengthen* the theorems below, since those negate this
predicate.  The appended digit `d` is not required to be prime: primality is a condition on the
truncations `p n`, and the largest base-10 right-truncatable prime `73939133` has digits `9` and
`1`.  (At `b = 7` requiring it would be worse than redundant — coprimality to `2` forces the
alphabet into `{2, 4, 6}`, so `d` prime would leave only `d = 2`.)  And `p 0` is not required to
be a single digit, so the chain may start at any prime — the "walking from any starting prime"
form of [MPP+24] Lemma A.1. -/
def InfiniteTruncatablePrime (b : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ n, (p n).Prime) ∧ ∀ n, ∃ d < b, p (n + 1) = b * p n + d

/-- A right-truncatable prime chain **is** a base-`b` digit recurrence, and its terms are
unbounded — the growth is free, from `pₙ₊₁ ≥ b·pₙ ≥ pₙ + 2`. -/
@[category API, AMS 11 37, ref "DubOst06", group "dubc_truncatable"]
theorem exists_digitRec_of_truncatable {b : ℕ} (hb : 2 ≤ b) {p : ℕ → ℕ}
    (hp : InfiniteTruncatablePrime b p) :
    ∃ dg : ℕ → ℤ, IsDigitRec b (fun n => (p n : ℤ)) dg
      ∧ Tendsto (fun n => ((p n : ℤ)).natAbs) atTop atTop := by
  obtain ⟨hprime, hstep⟩ := hp
  choose d hd hrec using hstep
  refine ⟨fun n => (d n : ℤ), ⟨fun n => ?_, fun n => Int.natCast_nonneg _, fun n => ?_⟩, ?_⟩
  · exact_mod_cast hrec n
  · exact_mod_cast hd n
  · -- `p` is unbounded because it grows by at least `2` per step
    have key : ∀ n, p n + 1 ≤ p (n + 1) := by
      intro n
      have h2 := (hprime n).two_le
      have hmul : 2 * p n ≤ b * p n := Nat.mul_le_mul_right _ hb
      have := hrec n
      omega
    have hle : ∀ n, n ≤ p n := by
      intro n
      induction n with
      | zero => omega
      | succ n ih => have := key n; omega
    have hnatAbs : ∀ n, ((p n : ℤ)).natAbs = p n := fun n => Int.natAbs_natCast _
    simp only [hnatAbs]
    exact Filter.tendsto_atTop_atTop.mpr fun B => ⟨B, fun n hn => le_trans hn (hle n)⟩

/-- **A rank certificate kills the base.**  If `CertOK b M rank` holds for a single `M ≥ b`,
there is no infinite right-truncatable prime in base `b`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_of_certOK {b M : ℕ} (hb : 2 ≤ b) (hbM : b ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK b M rank) (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime b p := by
  intro hp
  obtain ⟨dg, hdig, hgrow⟩ := exists_digitRec_of_truncatable hb hp
  exact not_forall_prime_of_certOK hb hbM rank hcert hdig hgrow fun n => by simpa using hp.1 n

/-- **A compressed core kills the base.**  If some `K` catches every cycle of the base-`b`
coprimality subshift modulo `M ≥ b` and is deterministic, there is no infinite right-truncatable
prime in base `b`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_of_coreCert {b M : ℕ} (hb : 2 ≤ b) (hbM : b ≤ M) [NeZero M]
    (K : ZMod M → Prop) (hclosed : CoreClosed b M K) (hdet : CoreDet b M K) (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime b p := by
  intro hp
  obtain ⟨dg, hdig, hgrow⟩ := exists_digitRec_of_truncatable hb hp
  exact not_forall_prime_of_coreCert hb hbM K hclosed hdet hdig hgrow fun n => by
    simpa using hp.1 n

/-! ### The target -/

/-- **[DubOst06] Conjecture 1 at `b = 7`: there is no infinite right-truncatable prime in
base 7.**  No infinite sequence of primes `p₀, p₁, …` satisfies `pₙ₊₁ = 7·pₙ + dₙ` with digits
`dₙ < 7` — for any starting prime `p₀`.

This is the companion of `DubC.Cycles.infinite_composites_seven` and rests on exactly the same
two facts, `DubC.Cycles.coreClosed_seven` and `DubC.Y31.coreDet_seven`: no new `native_decide`,
no cited-literature axiom, and in particular **not** the §3 equivalence of [DubOst06], whose
`(b−1)^∞` branch never arises on this route.  It is the next case after [MPP+24] Lemma A.1's
`b ≤ 6`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_seven (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime 7 p :=
  no_infiniteTruncatablePrime_of_coreCert (by norm_num) (by norm_num [primorial31])
    Y31.Kset Cycles.coreClosed_seven Y31.coreDet_seven p

/-! ### The bases below, for comparison

[MPP+24] Lemma A.1 in the certificate language.  Their proof collapses the alphabet to a
constant digit by hand and kills the constant word by Fermat; here the same four bases fall out
of the `decide`-checked rank certificates of `DubC/Verdict.lean`, with the Fermat step replaced
by the period-`1` case of the [Dub09] Theorem 4 return. -/

/-- **Base 3**: no infinite right-truncatable prime ([MPP+24] Lemma A.1). -/
@[category research solved, AMS 11 37, ref "MPP+24" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_three (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime 3 p :=
  no_infiniteTruncatablePrime_of_certOK (by norm_num) (by norm_num) _ certOK_three p

/-- **Base 4**: no infinite right-truncatable prime ([MPP+24] Lemma A.1). -/
@[category research solved, AMS 11 37, ref "MPP+24" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_four (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime 4 p :=
  no_infiniteTruncatablePrime_of_certOK (by norm_num) (by norm_num) _ certOK_four p

/-- **Base 5**: no infinite right-truncatable prime ([MPP+24] Lemma A.1; the modulus is the one
[DN05] uses for `a = 5`). -/
@[category research solved, AMS 11 37, ref "MPP+24" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_five (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime 5 p :=
  no_infiniteTruncatablePrime_of_certOK (by norm_num) (by norm_num) _ certOK_five p

/-- **Base 6**: no infinite right-truncatable prime ([MPP+24] Lemma A.1). -/
@[category research solved, AMS 11 37, ref "MPP+24" "DubOst06", group "dubc_truncatable"]
theorem no_infiniteTruncatablePrime_six (p : ℕ → ℕ) :
    ¬ InfiniteTruncatablePrime 6 p :=
  no_infiniteTruncatablePrime_of_certOK (by norm_num) (by norm_num) _ certOK_six p

end DubC
