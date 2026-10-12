/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Fin
import Evertse1984.Corollaries
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Evertse's S-unit sum lower bound (Compositio 1984), ℚ-specialization

The finiteness theorem behind Evertse's work on sums of `S`-units ([Eve84], Theorem 1
and its `ℚ`-form Corollary 1; read in full 2026-07-08), a Thue–Siegel–Roth–Schmidt
(Subspace) consequence: **a sum of `S`-units cannot be much smaller than its largest
term, outside finitely many exceptional proportional classes.**

> Let `S` be a finite set of primes enclosing `S_∞`, `n ≥ 1`, and `ε > 0`.  Then, among
> the **primitive** integer points `x = (x₀ : x₁ : … : xₙ) ∈ ℙⁿ(ℚ)` all of whose
> coordinates are `S`-units and which are **non-degenerate** (no proper subsum
> `x_{i₀}+…+x_{iₛ}` vanishes), only finitely many satisfy
>
>   `|x₀ + x₁ + … + xₙ| < H(x)^{1-ε}`.
>
> ([Eve84], Theorem 1 gives the projective-point / proportional-class count; Corollary 1
> is the explicit `ℚ`-normalization with `gcd = 1`.)

`H(x)` is the absolute (projective) Weil height.  Because `x` is a **primitive integer
point**, `H(x) = max_i |x_i|` — this is the identity ([Eve84], eq. (5)):
`‖x‖ = H(X)` iff `gcd(x₀, …, xₙ) = 1`.  So the height in the statement is the plain
archimedean maximum, and no product-formula machinery is needed.

## Statement conventions (the ℚ-specialization — all uses in this corpus)

Each direction *weakens*, or is *equivalent to*, the source (safe):

* **`S = {∞, 2, 3}`.**  The `S`-units among the rational integers are exactly `±2^a·3^b`
  (`a, b ≥ 0`); this is the predicate `Evertse.IsSUnit`.
* **Proportional classes = primitive integer points.**  Over `ℚ`, every proportional
  class of `S`-unit tuples has a unique-up-to-sign representative that is a *primitive
  integer* point (clear denominators, divide out the common `2^{min aᵢ}·3^{min bᵢ}`);
  primitivity is `gcd(x₀, …, xₙ) = 1`.  This is Evertse's own normalization
  ([Eve84], Corollary 1, eq. (11)), and it is **essential** for the truth of the bound:
  without it the map `x ↦ 2^{-N}·x` shows every direction to be exceptional (the values
  `2^a·3^b` are dense near `1`, so freely scaled `ℤ[1/6]`-unit tuples have arbitrarily
  small sums relative to their max).  Fixing `gcd = 1` — equivalently, passing to
  proportional classes — kills exactly that scaling freedom.
* **Height = archimedean max.**  By `gcd = 1` and [Eve84] eq. (5), `H(x) = max_i |x_i|`,
  recorded as `Finset.univ.sup (|x ·|)` in `ℕ` and cast to `ℝ`; the threshold
  `H(x)^{1-ε}` lives in `ℝ` via `rpow` with `ε : ℝ` free.  Since every coordinate is an
  `S`-unit, `max_i |x_i| ≥ 1` (`IsSUnit.one_le_natAbs`).
* **Non-degeneracy** is transcribed verbatim: `∑_{i ∈ I} x_i ≠ 0` for every proper,
  nonempty `I ⊂ univ` ([Eve84], eq. (8)/(10)).
* **One inequality covers both regimes.**  The exceptional condition
  `|∑ x_i| < H(x)^{1-ε}` includes the exact `S`-unit *equation* `∑ x_i = 0` (Theorem 1
  proper: also finitely many non-degenerate primitive solutions) *and* the approximate
  ("sum is small") case, uniformly.

The finiteness is **ineffective** (Subspace-based): [Eve84] bounds the *number* of
exceptional classes but provides no bound on their size.  Do not expect computable
exceptional bounds downstream.

Role in the program ([M4A3] §8 row 2): a shared `S`-unit engine — bounded-`u` extremal
subfamilies, reusable across the A5/A6 window analyses and BCZ-style `gcd(2ⁿ−1, 3ⁿ−1)`
arguments.  Consumers with `S`-units such as `(3/2)^c = 2^{-c}·3^c` clear denominators to
land on the primitive integer representative.

## Contents

* `Evertse.IsSUnit` — the predicate "`x = ±2^a·3^b`" (an `S`-unit of `ℤ` for
  `S = {∞, 2, 3}`).
* `Evertse.isSUnit_two_pow_three_pow`, `IsSUnit.ne_zero`, `IsSUnit.one_le_natAbs` — the
  basic facts a consumer needs (existence witness; nonvanishing; `max ≥ 1`).
* `Evertse.primes23`, `Evertse.IsSUnit.abs_mul_prod_padicNorm` — `|x| |x|₂ |x|₃ = 1`.
* `Evertse.sUnit_sum_lower` — **Theorem 1 / Corollary 1** of [Eve84], ℚ-specialized; proved
  from the Subspace-Theorems library's Corollary 1 (formerly a cited `axiom`).

## References

* [Eve84] Evertse, Jan-Hendrik. "On sums of `S`-units and linear recurrences."
  *Compositio Mathematica* **53**.2 (1984), 225–244.  (Theorem 1, p. 227; Corollary 1,
  p. 227, the `ℚ`-normalization with `gcd = 1`; Theorem 2 is the underlying analytic
  Subspace inequality.)
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §7 (engine audit), §8 row 2
  (transcription brief), §9 (file listing).
-/

namespace Evertse

open Finset

/-- An `S`-unit of `ℤ` for `S = {∞, 2, 3}`: a rational integer `x = ±2^a·3^b`
(`a, b ≥ 0`).  These are exactly the integers among the `S`-units of `ℚ` (units of
`ℤ[1/6]`) that are algebraic integers. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
def IsSUnit (x : ℤ) : Prop := ∃ a b : ℕ, x = 2 ^ a * 3 ^ b ∨ x = -(2 ^ a * 3 ^ b)

/-- The canonical positive witnesses: `2^a·3^b` is an `S`-unit. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma isSUnit_two_pow_three_pow (a b : ℕ) : IsSUnit ((2 : ℤ) ^ a * 3 ^ b) :=
  ⟨a, b, Or.inl rfl⟩

/-- An `S`-unit is nonzero. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma IsSUnit.ne_zero {x : ℤ} (h : IsSUnit x) : x ≠ 0 := by
  obtain ⟨a, b, h | h⟩ := h <;> subst h
  · positivity
  · rw [neg_ne_zero]; positivity

/-- An `S`-unit has absolute value at least `1`; hence the maximum coordinate of an
`S`-unit tuple is `≥ 1` (so the height base of `sUnit_sum_lower` is `≥ 1`). -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma IsSUnit.one_le_natAbs {x : ℤ} (h : IsSUnit x) : 1 ≤ x.natAbs :=
  Int.natAbs_pos.mpr h.ne_zero

/-- `|q ^ n|_p = |q|_p ^ n`. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma padicNorm_pow (p : ℕ) [Fact p.Prime] (q : ℚ) : ∀ n : ℕ, padicNorm p (q ^ n) = padicNorm p q ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, padicNorm.mul, padicNorm_pow p q n, pow_succ]

/-- The finite places `{2, 3}` of `S`, as a `Finset Nat.Primes`. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
def primes23 : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}

/-- **An `S`-unit has `S`-height one**: `|x| · |x|₂ · |x|₃ = 1` for `x = ±2^a 3^b`. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma IsSUnit.abs_mul_prod_padicNorm {x : ℤ} (h : IsSUnit x) :
    |((x : ℤ) : ℝ)| * ∏ p ∈ primes23, (padicNorm (p : ℕ) (x : ℚ) : ℝ) = 1 := by
  have hne : (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ ⟨3, Nat.prime_three⟩ := fun h ↦
    absurd (congrArg Subtype.val h) (by norm_num)
  have h2 : ∀ a b : ℕ, padicNorm 2 ((2 : ℚ) ^ a * 3 ^ b) = (2 ^ a)⁻¹ := fun a b ↦ by
    rw [padicNorm.mul, padicNorm_pow, padicNorm_pow, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime,
      padicNorm.padicNorm_of_prime_of_ne (by norm_num)]
    simp
  have h3 : ∀ a b : ℕ, padicNorm 3 ((2 : ℚ) ^ a * 3 ^ b) = (3 ^ b)⁻¹ := fun a b ↦ by
    rw [padicNorm.mul, padicNorm_pow, padicNorm_pow, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime,
      padicNorm.padicNorm_of_prime_of_ne (by norm_num)]
    simp
  have hpair : ∀ g : Nat.Primes → ℝ, ∏ p ∈ primes23, g p = g ⟨2, Nat.prime_two⟩ * g ⟨3, Nat.prime_three⟩ :=
    fun g ↦ by unfold primes23; exact Finset.prod_pair hne
  rw [hpair]
  change |((x : ℤ) : ℝ)| * ((padicNorm 2 (x : ℚ) : ℝ) * (padicNorm 3 (x : ℚ) : ℝ)) = 1
  obtain ⟨a, b, rfl | rfl⟩ := h
  · push_cast
    rw [h2, h3, abs_of_pos (by positivity)]
    push_cast
    field_simp
  · push_cast
    rw [padicNorm.neg, padicNorm.neg, h2, h3, abs_neg, abs_of_pos (by positivity)]
    push_cast
    field_simp

/-- **Evertse's `S`-unit sum lower bound** ([Eve84], Theorem 1 / Corollary 1),
ℚ-specialized to `S = {∞, 2, 3}` and the primitive-integer (proportional-class)
normalization (see the module doc for the specialization directions):

for every `n ≥ 1` and `ε > 0`, only finitely many tuples `x : Fin n → ℤ` satisfy

  * every coordinate is an `S`-unit `±2^a·3^b`  (`IsSUnit`),
  * `gcd(x₀, …, x_{n-1}) = 1`  (primitivity = the proportional-class representative),
  * non-degeneracy: `∑_{i ∈ I} x_i ≠ 0` for every proper, nonempty `I ⊂ univ`, and
  * `|∑ x_i| < (max_i |x_i|)^{1-ε}`   (the sum is smaller than the height to the `1-ε`).

Equivalently: **all but finitely many** primitive non-degenerate `S`-unit tuples obey
`|∑ x_i| ≥ (max_i |x_i|)^{1-ε}`.  The finiteness is **ineffective**.

Formerly a cited `axiom`; now a theorem, from [Eve84] Corollary 1 as proved in the
Subspace-Theorems library (`Rat.finite_setOf_sum_eq_zero_of_gcd_eq_one`, with `d = max(1 − ε, 0)`,
`c = 1`, `S₀ = {2, 3}`).  A tuple with `∑ x_i = 0` is a solution of Corollary 1 itself.  Otherwise
the tuple extended by `−∑ x_i` (indexed by `Option (Fin n)`) sums to zero, has no vanishing proper
subsum, is primitive, and its `S`-part product is `|∑ x_i| < max^{1-ε}`, the `S`-unit coordinates
contributing `1` each (`IsSUnit.abs_mul_prod_padicNorm`). -/
@[category research solved, AMS 11, ref "Eve84", group "three_halves_m4"]
theorem sUnit_sum_lower (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    { x : Fin n → ℤ |
        (∀ i, IsSUnit (x i)) ∧
        Finset.univ.gcd (fun i => x i) = 1 ∧
        (∀ I : Finset (Fin n), I.Nonempty → I ⊂ Finset.univ → ∑ i ∈ I, x i ≠ 0) ∧
        ((|∑ i, x i| : ℤ) : ℝ) < ((Finset.univ.sup fun i => (x i).natAbs : ℕ) : ℝ) ^ (1 - ε) }.Finite := by
  classical
  set d : ℝ := max (1 - ε) 0 with hd
  have hd0 : 0 ≤ d := le_max_right _ _
  have hd1 : d < 1 := max_lt (by linarith) one_pos
  have hA := Rat.finite_setOf_sum_eq_zero_of_gcd_eq_one (Fin n) primes23 (c := 1) hd0 hd1
  have hB := Rat.finite_setOf_sum_eq_zero_of_gcd_eq_one (Option (Fin n)) primes23 (c := 1) hd0 hd1
  set f : (Fin n → ℤ) → (Option (Fin n) → ℤ) := fun x o ↦ o.elim (-∑ i, x i) x with hfdef
  have hf : Function.Injective f := fun x y h ↦ funext fun i ↦ congrFun h (some i)
  refine (hA.union (hB.preimage hf.injOn)).subset ?_
  rintro x ⟨hunit, hgcd, hnv, hlt⟩
  set M : ℕ := univ.sup fun i => (x i).natAbs with hM
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_mem_eq_sup univ (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => (x i).natAbs
  have hi₀' : M = (x i₀).natAbs := hi₀
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hi₀']; exact_mod_cast (hunit i₀).one_le_natAbs
  have hMd : (M : ℝ) ^ (1 - ε) ≤ (M : ℝ) ^ d :=
    Real.rpow_le_rpow_of_exponent_le hM1 (le_max_left _ _)
  have hMi₀ : ((M : ℕ) : ℝ) = ((|x i₀| : ℤ) : ℝ) := by
    rw [hi₀', ← Int.cast_natCast, Int.natCast_natAbs]
  have hprod1 : ∀ i, |((x i : ℤ) : ℝ)| * ∏ p ∈ primes23, (padicNorm (p : ℕ) (x i) : ℝ) = 1 :=
    fun i ↦ (hunit i).abs_mul_prod_padicNorm
  by_cases hs : ∑ i, x i = 0
  · left
    refine ⟨hs, fun I hI hIu ↦ hnv I hI (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hIu⟩), hgcd, ?_⟩
    have hsup : ((|x i₀| : ℤ) : ℝ) ≤ ((⨆ k, |x k| : ℤ) : ℝ) := by
      exact_mod_cast le_ciSup (Set.finite_range fun k ↦ |x k|).bddAbove i₀
    rw [Finset.prod_congr rfl fun i _ ↦ hprod1 i, prod_const_one, one_mul]
    exact Real.one_le_rpow (hM1.trans (hMi₀ ▸ hsup)) hd0
  · right
    rw [Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨?_, fun I hI hIu ↦ ?_, ?_, ?_⟩
    · rw [Fintype.sum_option]; simp [hfdef]
    · set J := eraseNone I with hJ
      by_cases hnone : none ∈ I
      · have hI' : I = insertNone J := by rw [hJ, insertNone_eraseNone, insert_eq_of_mem hnone]
        rw [hI', sum_insertNone]
        simp only [hfdef, Option.elim_none, Option.elim_some]
        by_cases hJe : J = ∅
        · rw [hJe, sum_empty, add_zero, neg_ne_zero]; exact hs
        · have hJu : J ≠ univ := by
            rintro hJu; apply hIu; rw [hI', hJu]; ext o; cases o <;> simp
          have hc := sum_compl_add_sum J x
          have hJc := hnv Jᶜ (nonempty_iff_ne_empty.mpr (by rwa [Ne, compl_eq_empty_iff]))
            (Finset.ssubset_univ_iff.mpr ((compl_ne_univ_iff_nonempty J).mpr
              (nonempty_iff_ne_empty.mpr hJe)))
          intro h0; apply hJc; linarith
      · have hI' : I = J.map Function.Embedding.some := by
          rw [hJ, map_some_eraseNone, erase_eq_of_notMem hnone]
        rw [hI', sum_map]
        simp only [hfdef, Function.Embedding.some_apply, Option.elim_some]
        have hJn : J.Nonempty := by
          rw [hI'] at hI; exact map_nonempty.mp hI
        by_cases hJu : J = univ
        · rw [hJu]; exact hs
        · exact hnv J hJn (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hJu⟩)
    · have hdvd : univ.gcd (f x) ∣ univ.gcd (fun i => x i) :=
        Finset.dvd_gcd fun i _ ↦ Finset.gcd_dvd (f := f x) (mem_univ (some i))
      rw [hgcd] at hdvd
      rw [← Finset.normalize_gcd]
      exact normalize_eq_one.mpr (isUnit_of_dvd_one hdvd)
    · rw [Fintype.prod_option]
      simp only [hfdef, Option.elim_some, Option.elim_none]
      rw [Finset.prod_congr rfl fun i _ ↦ hprod1 i, prod_const_one, mul_one, one_mul]
      have hpad : ∏ p ∈ primes23, (padicNorm (p : ℕ) ((-∑ i, x i : ℤ) : ℚ) : ℝ) ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ ↦ by exact_mod_cast padicNorm.nonneg _)
          fun p _ ↦ by exact_mod_cast padicNorm.of_int _
      have hsup : ((|x i₀| : ℤ) : ℝ) ≤ ((⨆ o, |f x o| : ℤ) : ℝ) := by
        exact_mod_cast le_ciSup (Set.finite_range fun o ↦ |f x o|).bddAbove (some i₀)
      calc |(((-∑ i, x i : ℤ)) : ℝ)| * ∏ p ∈ primes23, (padicNorm (p : ℕ) ((-∑ i, x i : ℤ) : ℚ) : ℝ)
          ≤ |(((-∑ i, x i : ℤ)) : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left hpad (abs_nonneg _)
        _ = ((|∑ i, x i| : ℤ) : ℝ) := by push_cast; rw [mul_one, abs_neg]
        _ ≤ (M : ℝ) ^ (1 - ε) := hlt.le
        _ ≤ (M : ℝ) ^ d := hMd
        _ ≤ ((⨆ o, |f x o| : ℤ) : ℝ) ^ d :=
            Real.rpow_le_rpow (by positivity) (hMi₀ ▸ hsup) hd0

end Evertse
