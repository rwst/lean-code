/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowDistribution
import BertinPisot.GeneralizedFatou
import ForMathlib.RingTheory.PowerSeries.Rationality
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Theorem 5.1.1 — proof (Bertin §5.1)

Proof of `Bertin.AlphaPow.pisotSalem_theorem_5_1_1'`. **No `sorry`.** The entire
recurrence/calibration/algebra backbone is mechanized; the only non-Mathlib inputs are **ref'd cited
axioms** (status `cited`): the Fatou lemma (`IsRationalSeries.exists_coprime_quotient`, in
`GeneralizedFatou`) and the two analytic step-d facts `fatou_denom_disk_zeros` / `fatou_residue`
(below) — the pole/zero structure and residue of `f = P/Q` on a disc, which Mathlib cannot yet express
(no residue theory / argument principle). `pisotSalem_theorem_5_1_1'` supersedes the single cited
axiom `pisotSalem_theorem_5_1_1` in `BertinPisot.AlphaPowDistribution`.

## Bertin's proof, in three steps
Find an integer linear recurrence for `(uₙ)`: an `s ≥ 1` and `a ∈ ℤ^{s+1} \ {0}` with
`Vₙ(a) = Σ_{i=0}^s aᵢ u_{n+i} = 0` for all `n` (`HasRecurrence`). Then `Σ uₙ Xⁿ` is rational
(Proposition 1.1), and step d) reads off the conclusion from the rational function `f = A/Q`.
* **a)** `Vₙ(a) = 0` and condition (2) `|εₙ| < 1/((s+1)(α+1)A)` ⟹ `Vₙ₊₁(a) = 0`. Core identity
  `u_{m+1} − α u_m = α εₘ − ε_{m+1}` (`u_succ_sub_smul`): then `|Vₙ₊₁(a) − α Vₙ(a)| ≤ (s+1)(α+1)Aε < 1`
  and `Vₙ₊₁(a) ∈ ℤ`, so it is `0`.
* **b)** Pigeonhole on `{0,…,A}^{s+1}` (with condition (3) `A ≥ 2λ^{1/s}α + 1`) gives `a ≠ 0` with
  `V₀(a) = 0`.
* **c)** Choosing `s ≈ log λ`, `A ≈ 2eα` makes the hypothesis bound (1) imply (2) and (3) at once.
* **d)** Rationality + **generalized Fatou** (`IsRationalSeries.exists_coprime_quotient` over `ℤ`)
  ⟹ reduced `f = P/Q`, `P, Q ∈ ℤ[X]` coprime, `Q(0) = 1`. The analytic identity
  `f = λ/(1−αz) + ε(z)` (`ε` analytic on `D(0,1)`, `εTaylor`) puts a single pole at `1/α`, so
  `Q(1/α) = 0`; `Q.reverse` is monic (`Q(0)=1`) with root `α` ⟹ `α` algebraic integer; the other
  zeros of `Q` lie outside `D(0,1)` ⟹ conjugates `≤ 1`; residue `−λ/α` ⟹ `λ = −αA(1/α)/Q'(1/α) ∈ ℚ(α)`.

## Mathlib status
* **Proposition 1.1** (recurrence ⟺ rational): available — `isRationalSeries_iff_exists_recurrence`.
* **Fatou** (`ℤ`-rational ⟹ reduced `P/Q`, `Q(0)=1`): available — `IsRationalSeries.exists_coprime_quotient`
  (Bertin Thm 1.3 in `BertinPisot.GeneralizedFatou`), specialised to the Dedekind ring `ℤ`. **Not a gap.**
* **Pigeonhole**: available — `Mathlib.Combinatorics.Pigeonhole`.
* **Analytic radii** `f` on `D(0,1/α)`, `ε` on `D(0,1)`: available — `inv_le_fTaylor_radius`,
  `one_le_εTaylor_radius`.
* **GAPS** (the remaining analytic step-d work): the pole location `Q(1/α) = 0` from the identity
  `f = λ/(1−αz) + ε`, the **zero-counting** of `Q` in `D(0,1)` (argument principle / Rouché on a disk —
  Mathlib has Cauchy/Jensen but no packaged disk zero-count for this), and the **residue** computation
  `Res_{1/α} f = −λ/α` ⟹ `λ = −αA(1/α)/Q'(1/α)`.

## Shortcut
* **α algebraic** drops straight out of the recurrence by `αⁿ`-domination (`isAlgebraic_of_hasRecurrence`,
  same idea as `exp_diff_bounded_imp`): `Σ aᵢ u_{n+i} = 0` with `uₙ ≈ λαⁿ` forces `Σ aᵢ αⁱ = 0`, so `α`
  is a root of the integer polynomial `Σ aᵢ Xⁱ` — no residues needed for algebraicity (only the
  *integer* refinement and the conjugate bounds need step d).
-/

namespace Bertin.AlphaPow

open Filter Polynomial
open scoped Topology PowerSeries

/-- Bertin's linear form `Vₙ(a) = Σ_{i=0}^{s} aᵢ u_{n+i}`. A non-zero `a` with `Vₙ(a) = 0` for all `n`
is exactly a linear recurrence satisfied by `(uₙ)`. -/
noncomputable def V (lam α : ℝ) (a : ℕ → ℤ) (s n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (s + 1), a i * u lam α (n + i)

/-- `(uₙ)` satisfies a non-trivial integer linear recurrence of some order `s ≥ 1`. -/
def HasRecurrence (lam α : ℝ) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ ∃ a : ℕ → ℤ, (∃ i ≤ s, a i ≠ 0) ∧ ∀ n, V lam α a s n = 0

/-- **Core identity for step a):** `u_{m+1} − α u_m = α εₘ − ε_{m+1}` — the `λα^{m+1}` terms cancel.
(Proved.) -/
theorem u_succ_sub_smul (lam α : ℝ) (m : ℕ) :
    (u lam α (m + 1) : ℝ) - α * u lam α m = α * ε lam α m - ε lam α (m + 1) := by
  have h1 := self_eq_u_add_ε lam α (m + 1)
  have h2 := self_eq_u_add_ε lam α m
  linear_combination -h1 + α * h2

/-- **Step a).** If `Vₙ(a) = 0`, the coefficients are bounded by `A`, the residues by `ε₀`, and
condition (2) `(s+1)(α+1)A·ε₀ < 1` holds, then `Vₙ₊₁(a) = 0`: indeed `Vₙ₊₁(a) − α Vₙ(a)` is a sum of
`aᵢ(α ε_{n+i} − ε_{n+i+1})` (via `u_succ_sub_smul`), so `|Vₙ₊₁(a)| < 1`, and it is an integer. -/
theorem V_step (lam α : ℝ) (hα : 1 < α) (a : ℕ → ℤ) (s : ℕ) {A ε₀ : ℝ}
    (hA : ∀ i, |(a i : ℝ)| ≤ A) (hε : ∀ m, |ε lam α m| ≤ ε₀)
    (hcond2 : ((s : ℝ) + 1) * (α + 1) * A * ε₀ < 1) {n : ℕ}
    (hn : V lam α a s n = 0) : V lam α a s (n + 1) = 0 := by
  have hαpos : (0 : ℝ) < α := by linarith
  have hA0 : (0 : ℝ) ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hsum_eq : ((V lam α a s (n + 1) : ℤ) : ℝ) - α * ((V lam α a s n : ℤ) : ℝ)
      = ∑ i ∈ Finset.range (s + 1), (a i : ℝ) * (α * ε lam α (n + i) - ε lam α (n + i + 1)) := by
    simp only [V, Int.cast_sum, Int.cast_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hid := u_succ_sub_smul lam α (n + i)
    rw [show n + 1 + i = n + i + 1 from by omega]
    linear_combination (a i : ℝ) * hid
  have hbound : |((V lam α a s (n + 1) : ℤ) : ℝ) - α * ((V lam α a s n : ℤ) : ℝ)| < 1 := by
    rw [hsum_eq]
    calc |∑ i ∈ Finset.range (s + 1), (a i : ℝ) * (α * ε lam α (n + i) - ε lam α (n + i + 1))|
        ≤ ∑ i ∈ Finset.range (s + 1), |(a i : ℝ) * (α * ε lam α (n + i) - ε lam α (n + i + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (s + 1), A * ((α + 1) * ε₀) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul]
          refine mul_le_mul (hA i) ?_ (abs_nonneg _) hA0
          have hb1 := abs_le.mp (hε (n + i))
          have hb2 := abs_le.mp (hε (n + i + 1))
          rw [abs_le]
          exact ⟨by nlinarith [hb1.1, hb2.2], by nlinarith [hb1.2, hb2.1]⟩
      _ = ((s : ℝ) + 1) * (α + 1) * A * ε₀ := by
          rw [Finset.sum_const, Finset.card_range]; ring
      _ < 1 := hcond2
  rw [hn, Int.cast_zero, mul_zero, sub_zero, ← Int.cast_abs, ← Int.cast_one (R := ℝ),
    Int.cast_lt, abs_lt] at hbound
  omega

/-- **Step a) iterated.** From `V₀(a) = 0` and condition (2), the recurrence `Vₙ(a) = 0` holds for
every `n` — induction on `n` via `V_step`. (Proved.) -/
theorem recurrence_of_V_zero (lam α : ℝ) (hα : 1 < α) (a : ℕ → ℤ) (s : ℕ) {A ε₀ : ℝ}
    (hA : ∀ i, |(a i : ℝ)| ≤ A) (hε : ∀ m, |ε lam α m| ≤ ε₀)
    (hcond2 : ((s : ℝ) + 1) * (α + 1) * A * ε₀ < 1) (h0 : V lam α a s 0 = 0) :
    ∀ n, V lam α a s n = 0 := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact V_step lam α hα a s hA hε hcond2 ih

/-- **Step b) (pigeonhole).** If the box `{0,…,A}^{s+1}` has more points than `V₀` has values, two
collide, giving a non-zero `a` (bounded by `A`, vanishing past `s`) with `V₀(a) = 0`. The size
hypothesis `(∑ᵢ|uᵢ|)·A + 1 < (A+1)^{s+1}` bounds the value range by the length of
`[∑_{uᵢ<0} uᵢA, ∑_{uᵢ>0} uᵢA]`. TODO (gap-free): `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` over
`Fin (s+1) → Fin (A+1)`. -/
theorem exists_a_V_zero (lam α : ℝ) (s A : ℕ)
    (hsize : (∑ i ∈ Finset.range (s + 1), |u lam α i|) * (A : ℤ) + 1 < ((A : ℤ) + 1) ^ (s + 1)) :
    ∃ a : ℕ → ℤ, (∃ i ≤ s, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧ V lam α a s 0 = 0 := by
  classical
  have hmaxmin : ∀ t : ℤ, max 0 t - min 0 t = |t| := by
    intro t; rcases le_total 0 t with h | h
    · simp [max_eq_right h, min_eq_left h, abs_of_nonneg h]
    · simp [max_eq_left h, min_eq_right h, abs_of_nonpos h]
  -- the linear functional `φ x = Σᵢ xᵢ uᵢ` on the box `Fin (s+1) → Fin (A+1)`
  set φ : (Fin (s + 1) → Fin (A + 1)) → ℤ :=
    fun x => ∑ i : Fin (s + 1), (x i : ℤ) * u lam α i with hφ
  set lo : ℤ := ∑ i : Fin (s + 1), min 0 ((A : ℤ) * u lam α i) with hlo
  set hi : ℤ := ∑ i : Fin (s + 1), max 0 ((A : ℤ) * u lam α i) with hhi
  have hmaps : Set.MapsTo φ (↑(Finset.univ : Finset (Fin (s + 1) → Fin (A + 1))))
      ↑(Finset.Icc lo hi) := by
    intro x _
    simp only [Finset.coe_Icc, Set.mem_Icc, hφ, hlo, hhi]
    refine ⟨Finset.sum_le_sum (fun i _ => ?_), Finset.sum_le_sum (fun i _ => ?_)⟩
    · have hx0 : (0 : ℤ) ≤ (x i : ℤ) := Int.natCast_nonneg _
      have hxA : (x i : ℤ) ≤ A := by exact_mod_cast Nat.lt_succ_iff.mp (x i).isLt
      rcases le_total 0 (u lam α i) with hu | hu
      · rw [min_eq_left (mul_nonneg (Int.natCast_nonneg A) hu)]; exact mul_nonneg hx0 hu
      · rw [min_eq_right (by nlinarith [Int.natCast_nonneg A])]; nlinarith
    · have hx0 : (0 : ℤ) ≤ (x i : ℤ) := Int.natCast_nonneg _
      have hxA : (x i : ℤ) ≤ A := by exact_mod_cast Nat.lt_succ_iff.mp (x i).isLt
      rcases le_total 0 (u lam α i) with hu | hu
      · rw [max_eq_right (mul_nonneg (Int.natCast_nonneg A) hu)]; nlinarith
      · rw [max_eq_left (by nlinarith [Int.natCast_nonneg A])]; nlinarith
  have hcardlt : (Finset.Icc lo hi).card < Fintype.card (Fin (s + 1) → Fin (A + 1)) := by
    have hd : hi - lo = (∑ i ∈ Finset.range (s + 1), |u lam α i|) * (A : ℤ) := by
      rw [hhi, hlo, ← Finset.sum_sub_distrib,
        Fin.sum_univ_eq_sum_range (fun i => max 0 ((A : ℤ) * u lam α i) - min 0 ((A : ℤ) * u lam α i)),
        Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hmaxmin, abs_mul, abs_of_nonneg (Int.natCast_nonneg A)]; ring
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hlt : ((Finset.Icc lo hi).card : ℤ) < (((A + 1) ^ (s + 1) : ℕ) : ℤ) := by
      rw [Int.card_Icc,
        Int.toNat_of_nonneg (by rw [show hi + 1 - lo = (hi - lo) + 1 from by ring, hd]; positivity),
        show hi + 1 - lo = (∑ i ∈ Finset.range (s + 1), |u lam α i|) * (A : ℤ) + 1 from by
          rw [← hd]; ring]
      push_cast; exact hsize
    exact_mod_cast hlt
  obtain ⟨x, -, y, -, hxy, hφxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [Finset.card_univ]; exact hcardlt) hmaps
  refine ⟨fun i => if h : i < s + 1 then ((x ⟨i, h⟩ : ℤ) - (y ⟨i, h⟩ : ℤ)) else 0, ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    refine ⟨j, Nat.lt_succ_iff.mp j.isLt, ?_⟩
    simp only [j.isLt, dif_pos, Fin.eta]
    exact fun hc => hj (Fin.ext (by exact_mod_cast sub_eq_zero.mp hc))
  · intro i
    by_cases h : i < s + 1
    · simp only [dif_pos h, ← Int.cast_abs]
      have hxA : (x ⟨i, h⟩ : ℤ) ≤ A := by exact_mod_cast Nat.lt_succ_iff.mp (x ⟨i, h⟩).isLt
      have hyA : (y ⟨i, h⟩ : ℤ) ≤ A := by exact_mod_cast Nat.lt_succ_iff.mp (y ⟨i, h⟩).isLt
      have hb : |(x ⟨i, h⟩ : ℤ) - (y ⟨i, h⟩ : ℤ)| ≤ (A : ℤ) := by
        rw [abs_le]
        exact ⟨by nlinarith [Int.natCast_nonneg (x ⟨i, h⟩).val],
          by nlinarith [Int.natCast_nonneg (y ⟨i, h⟩).val]⟩
      exact_mod_cast hb
    · simp only [dif_neg h, Int.cast_zero, abs_zero]; positivity
  · rw [V, ← Fin.sum_univ_eq_sum_range
        (fun i => (if h : i < s + 1 then ((x ⟨i, h⟩ : ℤ) - (y ⟨i, h⟩ : ℤ)) else 0) *
          u lam α (0 + i)) (s + 1)]
    have hsum : ∑ i : Fin (s + 1),
        (if h : (i : ℕ) < s + 1 then ((x ⟨(i : ℕ), h⟩ : ℤ) - (y ⟨(i : ℕ), h⟩ : ℤ)) else 0) *
          u lam α (0 + (i : ℕ)) = φ x - φ y := by
      rw [hφ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [i.isLt, dif_pos, Fin.eta, Nat.zero_add]
      ring
    rw [hsum, sub_eq_zero.mpr hφxy]

/-- The coefficient sum is bounded by `(s+1)(λαˢ + ½)` — each `|uᵢ| ≤ |λαⁱ| + ½ ≤ λαˢ + ½`
(`abs_u_le`, `αⁱ ≤ αˢ`). The growth estimate the pigeonhole size condition rests on. (Proved.) -/
theorem sum_abs_u_le (lam α : ℝ) (hlam : 1 ≤ lam) (hα : 1 ≤ α) (s : ℕ) :
    ((∑ i ∈ Finset.range (s + 1), |u lam α i| : ℤ) : ℝ) ≤ (s + 1) * (lam * α ^ s + 1 / 2) := by
  push_cast
  calc ∑ i ∈ Finset.range (s + 1), |(u lam α i : ℝ)|
      ≤ ∑ _i ∈ Finset.range (s + 1), (lam * α ^ s + 1 / 2) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        simp only [Finset.mem_range] at hi
        calc |(u lam α i : ℝ)| ≤ |lam * α ^ i| + 1 / 2 := abs_u_le lam α i
          _ = lam * α ^ i + 1 / 2 := by rw [abs_of_nonneg (by positivity)]
          _ ≤ lam * α ^ s + 1 / 2 := by
              have hpow : α ^ i ≤ α ^ s := pow_le_pow_right₀ hα (Nat.lt_succ_iff.mp hi)
              have := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ lam by linarith)
              linarith
    _ = (s + 1) * (lam * α ^ s + 1 / 2) := by
        rw [Finset.sum_const, Finset.card_range]; push_cast; ring

/-- Arithmetic backbone for step c): `5(s+1) ≤ 4·2ˢ` for `s ≥ 2`. -/
private theorem calib_nat_bb (s : ℕ) (hs : 2 ≤ s) : 5 * (s + 1) ≤ 4 * 2 ^ s := by
  induction s with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp_all
    · have h1 := ih h
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- **The φ estimate (α-free core).** For `s ≥ 2` and `s−1 ≤ t < s`,
`(s+1)^{s+1}(eᵗ + ½) ≤ (2e(1+t))ˢ`. This is the heart of Bertin's calibration: `φ(t) > 0` (where
`φ(x) = 1 − x/s + log((1+x)/(1+s))`) is exactly the monotonicity step
`((s+1)/(1+t))ˢ ≤ e^{s−t}`, proved here from `Real.log_le_sub_one_of_pos`. -/
private theorem calib_star (s : ℕ) (t : ℝ) (hs2 : 2 ≤ s) (ht1 : (s : ℝ) - 1 ≤ t) (hts : t < s) :
    ((s : ℝ) + 1) ^ (s + 1) * (Real.exp t + 1 / 2) ≤ (2 * Real.exp 1 * (1 + t)) ^ s := by
  have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
  have ht1' : (1 : ℝ) ≤ t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  set E := Real.exp 1 with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos 1
  have hetpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hee : E ≤ Real.exp t := Real.exp_le_exp.mpr ht1'
  have step1 : Real.exp t + 1 / 2 ≤ (1 + 1 / (2 * E)) * Real.exp t := by
    have : (1 : ℝ) / 2 ≤ Real.exp t / (2 * E) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hee]
    have hexp : (1 + 1 / (2 * E)) * Real.exp t = Real.exp t + Real.exp t / (2 * E) := by ring
    rw [hexp]; linarith
  have step3 : ((s : ℝ) + 1) * (1 + 1 / (2 * E)) ≤ 2 ^ s := by
    have he2 : (2 : ℝ) ≤ E := by rw [hE]; have := Real.add_one_le_exp 1; linarith
    have hC : (1 : ℝ) + 1 / (2 * E) ≤ 5 / 4 := by
      have h14 : 1 / (2 * E) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hnatR : (5 : ℝ) * ((s : ℝ) + 1) ≤ 4 * 2 ^ s := by exact_mod_cast calib_nat_bb s hs2
    calc ((s : ℝ) + 1) * (1 + 1 / (2 * E)) ≤ ((s : ℝ) + 1) * (5 / 4) :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ ≤ 2 ^ s := by linarith
  have step2 : (((s : ℝ) + 1) / (1 + t)) ^ s ≤ Real.exp ((s : ℝ) - t) := by
    have hy : (0 : ℝ) < ((s : ℝ) + 1) / (1 + t) := by positivity
    rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_pow, Real.log_exp]
    have hlog : Real.log (((s : ℝ) + 1) / (1 + t)) ≤ ((s : ℝ) + 1) / (1 + t) - 1 :=
      Real.log_le_sub_one_of_pos hy
    have hsimp : ((s : ℝ) + 1) / (1 + t) - 1 = ((s : ℝ) - t) / (1 + t) := by field_simp; ring
    rw [hsimp] at hlog
    calc (s : ℝ) * Real.log (((s : ℝ) + 1) / (1 + t)) ≤ (s : ℝ) * (((s : ℝ) - t) / (1 + t)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (s : ℝ) - t := by rw [mul_div_assoc', div_le_iff₀ h1t]; nlinarith
  have hsp : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ s := by positivity
  have key : ((s : ℝ) + 1) ^ s * Real.exp t ≤ E ^ s * (1 + t) ^ s := by
    have hdiv : (((s : ℝ) + 1) / (1 + t)) ^ s = ((s : ℝ) + 1) ^ s / (1 + t) ^ s := by rw [div_pow]
    have hexp : Real.exp ((s : ℝ) - t) = E ^ s / Real.exp t := by
      rw [Real.exp_sub, hE, ← Real.exp_nat_mul]; ring_nf
    rw [hdiv, hexp] at step2
    have := (div_le_div_iff₀ (by positivity) hetpos).mp step2
    linarith [this]
  calc ((s : ℝ) + 1) ^ (s + 1) * (Real.exp t + 1 / 2)
      ≤ ((s : ℝ) + 1) ^ (s + 1) * ((1 + 1 / (2 * E)) * Real.exp t) :=
        mul_le_mul_of_nonneg_left step1 (by positivity)
    _ = ((s : ℝ) + 1) ^ s * (((s : ℝ) + 1) * (1 + 1 / (2 * E))) * Real.exp t := by ring
    _ ≤ ((s : ℝ) + 1) ^ s * 2 ^ s * Real.exp t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left step3 hsp) (le_of_lt hetpos)
    _ = 2 ^ s * (((s : ℝ) + 1) ^ s * Real.exp t) := by ring
    _ ≤ 2 ^ s * (E ^ s * (1 + t) ^ s) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 * E * (1 + t)) ^ s := by rw [mul_pow, mul_pow]; ring

/-- The calibration bound `M ≤ Uˢ`, where `M = (s+1)(λαˢ + ½)` bounds `Σ|uᵢ|` (`sum_abs_u_le`) and
`U = 2eα(1+log λ)/(s+1)` is the cond-(2) cap on `A`. The factor `α` cancels, reducing to
`calib_star`. (`s ≥ 2`, i.e. `log λ ≥ 1`.) -/
private theorem calib_M_le_Us (lam α : ℝ) (s : ℕ) (hα : 1 ≤ α) (hlam : 0 < lam)
    (ht1 : (s : ℝ) - 1 ≤ Real.log lam) (hts : Real.log lam < s) (hs2 : 2 ≤ s) :
    ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2)
      ≤ (2 * Real.exp 1 * α * (1 + Real.log lam) / ((s : ℝ) + 1)) ^ s := by
  have hstar := calib_star s (Real.log lam) hs2 ht1 hts
  set t := Real.log lam with htdef
  have hexplog : Real.exp t = lam := Real.exp_log hlam
  rw [hexplog] at hstar
  have hαs : (1 : ℝ) ≤ α ^ s := one_le_pow₀ hα
  have hαspos : (0 : ℝ) < α ^ s := by positivity
  have hsp1 : (0 : ℝ) < ((s : ℝ) + 1) ^ s := by positivity
  have hterm : lam * α ^ s + 1 / 2 ≤ α ^ s * (lam + 1 / 2) := by nlinarith [hαs]
  have hmain : ((s : ℝ) + 1) ^ (s + 1) * (lam * α ^ s + 1 / 2) ≤ (2 * Real.exp 1 * α * (1 + t)) ^ s := by
    calc ((s : ℝ) + 1) ^ (s + 1) * (lam * α ^ s + 1 / 2)
        ≤ ((s : ℝ) + 1) ^ (s + 1) * (α ^ s * (lam + 1 / 2)) :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = α ^ s * (((s : ℝ) + 1) ^ (s + 1) * (lam + 1 / 2)) := by ring
      _ ≤ α ^ s * (2 * Real.exp 1 * (1 + t)) ^ s :=
          mul_le_mul_of_nonneg_left hstar (le_of_lt hαspos)
      _ = (2 * Real.exp 1 * α * (1 + t)) ^ s := by rw [← mul_pow]; ring_nf
  rw [div_pow, le_div_iff₀ hsp1]
  have hrw : ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2) * ((s : ℝ) + 1) ^ s
      = ((s : ℝ) + 1) ^ (s + 1) * (lam * α ^ s + 1 / 2) := by rw [pow_succ]; ring
  rw [hrw]; exact hmain

/-- The pigeonhole size condition `(Σ|uᵢ|)·A + 1 < (A+1)^{s+1}` follows (in `ℤ`) from
`M ≤ (A+1)ˢ`, via `sum_abs_u_le` and `(A+1)^{s+1} = A(A+1)ˢ + (A+1)ˢ` with `1 < (A+1)ˢ`. -/
private theorem calib_pigeon_size (lam α : ℝ) (hlam : 1 ≤ lam) (hα : 1 ≤ α) (s A : ℕ)
    (hA : 1 ≤ A) (hs : 1 ≤ s) (hM : (↑s + 1) * (lam * α ^ s + 1 / 2) ≤ ((A : ℝ) + 1) ^ s) :
    (∑ i ∈ Finset.range (s + 1), |u lam α i|) * (A : ℤ) + 1 < ((A : ℤ) + 1) ^ (s + 1) := by
  have hsum := sum_abs_u_le lam α hlam hα s
  rw [← @Int.cast_lt ℝ]; push_cast
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hZ : ((∑ i ∈ Finset.range (s + 1), |u lam α i| : ℤ) : ℝ) ≤ ((A : ℝ) + 1) ^ s :=
    le_trans hsum hM
  have hgt1 : (1 : ℝ) < ((A : ℝ) + 1) ^ s := by
    have h1 : (1 : ℝ) < (A : ℝ) + 1 := by linarith
    calc (1 : ℝ) = ((A : ℝ) + 1) ^ 0 := by simp
      _ < ((A : ℝ) + 1) ^ s := by apply pow_lt_pow_right₀ h1; omega
  have hZA : ((∑ i ∈ Finset.range (s + 1), |u lam α i| : ℤ) : ℝ) * (A : ℝ)
      ≤ ((A : ℝ) + 1) ^ s * (A : ℝ) := mul_le_mul_of_nonneg_right hZ (by linarith)
  have hsplit : ((A : ℝ) + 1) ^ (s + 1) = ((A : ℝ) + 1) ^ s * (A : ℝ) + ((A : ℝ) + 1) ^ s := by ring
  push_cast at hZA ⊢
  rw [hsplit]; linarith

/-- The cond-(2) bound `(s+1)·A < 2eα(1+log λ)` implies the goal's `ε₀`-form `< 1`
(the factor `(α+1)` cancels). -/
private theorem calib_cond2_of (α lam : ℝ) (s A : ℕ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (h : ((s : ℝ) + 1) * (A : ℝ) < 2 * Real.exp 1 * α * (1 + Real.log lam)) :
    ((s : ℝ) + 1) * (α + 1) * (A : ℝ) *
        (1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) < 1 := by
  have hlog : 0 ≤ Real.log lam := Real.log_nonneg hlam
  have hden : 0 < 2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam) := by
    have := Real.exp_pos 1; positivity
  rw [mul_one_div, div_lt_one hden]
  have hexp := mul_lt_mul_of_pos_left h (show (0 : ℝ) < α + 1 by linarith)
  nlinarith [hexp]

/-- For `s ≥ 2`: choose `A := ⌈M^{1/s}⌉ − 1` (the cond-(2)-feasible integer just below `M^{1/s} ≤ U`).
`(A+1)ˢ ≥ M` gives the size; `A < U` gives cond (2). -/
private theorem calib_choose_A (lam α : ℝ) (s : ℕ) (hα : 1 < α) (hlam : 1 ≤ lam) (hs2 : 2 ≤ s)
    (hM1 : (1 : ℝ) < ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2))
    (hMU : ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2)
        ≤ (2 * Real.exp 1 * α * (1 + Real.log lam) / ((s : ℝ) + 1)) ^ s) :
    ∃ A : ℕ, 1 ≤ A ∧ ((s : ℝ) + 1) * (A : ℝ) < 2 * Real.exp 1 * α * (1 + Real.log lam)
           ∧ ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2) ≤ ((A : ℝ) + 1) ^ s := by
  set M := ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2) with hMdef
  set U := 2 * Real.exp 1 * α * (1 + Real.log lam) / ((s : ℝ) + 1) with hUdef
  have hs0 : s ≠ 0 := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog : 0 ≤ Real.log lam := Real.log_nonneg hlam
  have hαpos : (0 : ℝ) < α := by linarith
  have hU0 : (0 : ℝ) < U := by rw [hUdef]; have := Real.exp_pos 1; positivity
  set y := M ^ ((s : ℝ)⁻¹) with hydef
  have hy0 : (0 : ℝ) < y := Real.rpow_pos_of_pos hM0 _
  have hMeq : M = y ^ s := by rw [hydef, Real.rpow_inv_natCast_pow (le_of_lt hM0) hs0]
  have hy1 : (1 : ℝ) < y := by
    have hys : (1 : ℝ) < y ^ s := by rw [← hMeq]; exact hM1
    exact (one_lt_pow_iff_of_nonneg (le_of_lt hy0) hs0).mp hys
  have hceil2 : 2 ≤ ⌈y⌉₊ := by
    have : 1 < ⌈y⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hy1)
    omega
  have hyceil : 1 ≤ ⌈y⌉₊ := by omega
  have hA1 : ((⌈y⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈y⌉₊ : ℝ) := by
    rw [Nat.cast_sub hyceil]; push_cast; ring
  refine ⟨⌈y⌉₊ - 1, by omega, ?_, ?_⟩
  · have hyU : y ≤ U := by
      rw [hydef]
      have h1 : M ^ ((s : ℝ)⁻¹) ≤ (U ^ s) ^ ((s : ℝ)⁻¹) :=
        Real.rpow_le_rpow (le_of_lt hM0) hMU (by positivity)
      rwa [Real.pow_rpow_inv_natCast (le_of_lt hU0) hs0] at h1
    have hAy : ((⌈y⌉₊ - 1 : ℕ) : ℝ) < y := by
      have hc : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (le_of_lt hy0)
      have : ((⌈y⌉₊ - 1 : ℕ) : ℝ) + 1 < y + 1 := by rw [hA1]; exact hc
      linarith
    have hAU : ((⌈y⌉₊ - 1 : ℕ) : ℝ) < U := lt_of_lt_of_le hAy hyU
    have hsp : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have h2 : ((s : ℝ) + 1) * ((⌈y⌉₊ - 1 : ℕ) : ℝ) < ((s : ℝ) + 1) * U :=
      mul_lt_mul_of_pos_left hAU hsp
    have h3 : ((s : ℝ) + 1) * U = 2 * Real.exp 1 * α * (1 + Real.log lam) := by rw [hUdef]; field_simp
    linarith [h2, h3]
  · rw [hA1]
    have hyc : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    calc M = y ^ s := hMeq
      _ ≤ (⌈y⌉₊ : ℝ) ^ s := pow_le_pow_left₀ (le_of_lt hy0) hyc s

/-- **Step c) (calibration).** The bound `(1)` lets us pick integers `s ≥ 1` (`s = ⌊log λ⌋ + 1`) and
`A` so condition (2) and the pigeonhole size condition both hold. Bertin's `φ` argument
(`φ(x) = 1 − x/s + log((1+x)/(1+s))`, `φ(log λ) > 0`): the lower bound `2λ^{1/s}α` for `A` (size) sits
below the cond-(2) cap `2eα(1+log λ)/(s+1)`. Two bands: `s = 1` (`log λ < 1`, exact linear, secant
bound on `exp`) and `s ≥ 2` (`calib_M_le_Us`, the φ estimate). `hbound` is unused here — conditions
(2),(3) constrain only `s, A, α, λ`. -/
theorem exists_s_A (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hbound : ∀ n : ℕ, distToNearestInt (lam * α ^ n) ≤
      1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) :
    ∃ s A : ℕ, 1 ≤ s ∧
      ((s : ℝ) + 1) * (α + 1) * (A : ℝ) *
          (1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) < 1 ∧
      (∑ i ∈ Finset.range (s + 1), |u lam α i|) * (A : ℤ) + 1 < ((A : ℤ) + 1) ^ (s + 1) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hlam0 : 0 < lam := by linarith
  have ht0 : 0 ≤ Real.log lam := Real.log_nonneg hlam
  rcases lt_or_ge (Real.log lam) 1 with htlt | htge
  · -- **Band `s = 1`** (`log λ < 1`): `A := ⌊2λα − 1⌋ + 1`, exact size, secant `exp` bound for cond (2).
    set t := Real.log lam with htdef
    have hexpt : Real.exp t = lam := Real.exp_log hlam0
    have hconc : 2 * Real.exp t < Real.exp 1 * (1 + t) := by
      have hsec : Real.exp t ≤ (1 - t) * Real.exp 0 + t * Real.exp 1 := by
        have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
          (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (0 : ℝ) ≤ t) (by ring)
        simpa using h
      rw [Real.exp_zero] at hsec
      have he2 : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
      have hpos : 0 < (Real.exp 1 - 2) * (1 - t) := mul_pos (by linarith) (by linarith)
      nlinarith [hsec, hpos]
    rw [hexpt] at hconc
    set A : ℕ := ⌊2 * lam * α - 1⌋₊ + 1 with hAdef
    have h2la : (2 : ℝ) ≤ 2 * lam * α := by nlinarith
    have hAlb : (2 * lam * α - 1 : ℝ) < (A : ℝ) := by
      rw [hAdef]; push_cast
      have := Nat.lt_floor_add_one (2 * lam * α - 1); linarith
    have hAub : (A : ℝ) ≤ 2 * lam * α := by
      rw [hAdef]; push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * lam * α - 1 by linarith); linarith
    have hA0 : (0 : ℝ) < (A : ℝ) := by rw [hAdef]; push_cast; positivity
    refine ⟨1, A, le_refl 1, ?_, ?_⟩
    · have hkey : ((1 : ℝ) + 1) * (A : ℝ) < 2 * Real.exp 1 * α * (1 + t) := by
        have : (A : ℝ) < Real.exp 1 * α * (1 + t) := by nlinarith [hAub, hconc, hα0]
        nlinarith [this]
      have hden : 0 < 2 * Real.exp 1 * α * (α + 1) * (1 + t) := by
        have := Real.exp_pos 1; positivity
      rw [mul_one_div, div_lt_one hden]
      have hexp := mul_lt_mul_of_pos_left hkey (show (0 : ℝ) < α + 1 by linarith)
      push_cast
      nlinarith [hexp]
    · have hsum := sum_abs_u_le lam α hlam (le_of_lt hα) 1
      rw [← @Int.cast_lt ℝ]; push_cast
      have hZ : ((∑ i ∈ Finset.range (1 + 1), |u lam α i| : ℤ) : ℝ) < (A : ℝ) + 2 := by
        have hb : ((∑ i ∈ Finset.range (1 + 1), |u lam α i| : ℤ) : ℝ)
            ≤ ((1 : ℝ) + 1) * (lam * α ^ 1 + 1 / 2) := by have h := hsum; push_cast at h; linarith
        have : ((1 : ℝ) + 1) * (lam * α ^ 1 + 1 / 2) < (A : ℝ) + 2 := by nlinarith [hAlb]
        linarith
      have hZA := mul_lt_mul_of_pos_right hZ hA0
      push_cast at hZA ⊢
      nlinarith [hZA]
  · -- **Band `s ≥ 2`** (`log λ ≥ 1`): `s = ⌊log λ⌋ + 1`, `calib_M_le_Us` + `calib_choose_A`.
    set s : ℕ := ⌊Real.log lam⌋₊ + 1 with hsdef
    have hs2 : 2 ≤ s := by
      have : 1 ≤ ⌊Real.log lam⌋₊ := Nat.le_floor (by exact_mod_cast htge)
      omega
    have ht1 : (s : ℝ) - 1 ≤ Real.log lam := by
      rw [hsdef]; push_cast; have := Nat.floor_le ht0; linarith
    have hts : Real.log lam < s := by
      rw [hsdef]; push_cast; exact Nat.lt_floor_add_one _
    have hMU := calib_M_le_Us lam α s (le_of_lt hα) hlam0 ht1 hts hs2
    have hM1 : (1 : ℝ) < ((s : ℝ) + 1) * (lam * α ^ s + 1 / 2) := by
      have h1 : (1 : ℝ) ≤ lam * α ^ s := by
        have hαp : (1 : ℝ) ≤ α ^ s := one_le_pow₀ (le_of_lt hα)
        nlinarith [hαp]
      have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      nlinarith [h1, hsR]
    obtain ⟨A, hA1, hcond, hsize⟩ := calib_choose_A lam α s hα hlam hs2 hM1 hMU
    refine ⟨s, A, by omega, ?_, ?_⟩
    · exact calib_cond2_of α lam s A hα hlam hcond
    · exact calib_pigeon_size lam α hlam (le_of_lt hα) s A hA1 (by omega) hsize

/-- **Steps a)+b)+c) assembled.** The bound `(1)` produces an integer linear recurrence for `(uₙ)`.
(Proved, modulo the pigeonhole `exists_a_V_zero` and the calibration `exists_s_A`.) -/
theorem exists_hasRecurrence (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hbound : ∀ n : ℕ, distToNearestInt (lam * α ^ n) ≤
      1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) :
    HasRecurrence lam α := by
  have hεb : ∀ m, |ε lam α m| ≤ 1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam)) := by
    intro m; rw [← distToNearestInt_eq_abs_ε]; exact hbound m
  obtain ⟨s, A, hs1, hcond2, hsize⟩ := exists_s_A lam α hα hlam hbound
  obtain ⟨a, ha0, hAbd, h0⟩ := exists_a_V_zero lam α s A hsize
  exact ⟨s, hs1, a, ha0, recurrence_of_V_zero lam α hα a s hAbd hεb hcond2 h0⟩

/-- **Proposition 1.1 bridge.** A non-trivial recurrence makes `Σ uₙ Xⁿ` a rational series. This is
`isRationalSeries_iff_exists_recurrence.mpr` after reindexing `Vₙ(a) = Σᵢ aᵢ u_{n+i}` (`i = 0…s`) to
the ForMathlib form `Σⱼ qⱼ a_{n−j}` with leading coefficient `q₀ = a_{s'} ≠ 0` (`s'` the top non-zero
index). -/
theorem isRationalSeries_of_hasRecurrence (lam α : ℝ) (hrec : HasRecurrence lam α) :
    IsRationalSeries (uSeries lam α) := by
  obtain ⟨s, hs1, a, ⟨i₀, hi₀s, hi₀⟩, hV⟩ := hrec
  set F : ℤ⟦X⟧ := uSeries lam α with hF
  -- reversed denominator `Q = Σⱼ a_{s-j} Xʲ`, so that `Q · F` is the polynomial `P` of degree `< s`
  set Q : ℤ[X] := ∑ j ∈ Finset.range (s + 1), C (a (s - j)) * X ^ j with hQ
  have hcF : ∀ k, (PowerSeries.coeff k) F = u lam α k := by
    intro k; rw [hF, uSeries, PowerSeries.coeff_mk]
  have hQz : ∀ i, s < i → Q.coeff i = 0 := by
    intro i hi; rw [hQ, finsetSum_coeff]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have hQc : ∀ i, i ≤ s → Q.coeff i = a (s - i) := by
    intro i hi; rw [hQ, finsetSum_coeff, Finset.sum_eq_single i]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hj; rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  -- coefficients of `Q · F` past degree `s` are exactly `V(m-s) = 0`
  have hvanish : ∀ m, s ≤ m → (PowerSeries.coeff m) ((Q : ℤ⟦X⟧) * F) = 0 := by
    intro m hm
    have hsub : Finset.range (s + 1) ⊆ Finset.range (m + 1) :=
      fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
    have key : (PowerSeries.coeff m) ((Q : ℤ⟦X⟧) * F) = V lam α a s (m - s) := by
      rw [coeff_coe_mul, V, ← Finset.sum_subset hsub]
      · rw [← Finset.sum_range_reflect (fun i => a i * u lam α (m - s + i)) (s + 1)]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [Finset.mem_range] at hi
        simp only [Nat.add_sub_cancel]
        rw [hcF, hQc i (by omega), show m - i = m - s + (s - i) from by omega]
      · intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        rw [hQz i (by omega), zero_mul]
    rw [key, hV (m - s)]
  refine ⟨PowerSeries.trunc s ((Q : ℤ⟦X⟧) * F), Q, ?_, ?_⟩
  · intro hQ0
    apply hi₀
    have hco : Q.coeff (s - i₀) = a i₀ := by
      rw [hQc (s - i₀) (by omega), show s - (s - i₀) = i₀ from by omega]
    rw [hQ0, coeff_zero] at hco; exact hco.symm
  · ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with h
    · rfl
    · exact hvanish m (not_lt.mp h)

/-- **Generalized Fatou applied.** From rationality over the Dedekind ring `ℤ`, the series `Σ uₙ Xⁿ`
has a reduced normalized representation: coprime `P, Q ∈ ℤ[X]` with `Q(0) = 1` and `Q · (Σ uₙ Xⁿ) = P`.
(Proved, modulo `isRationalSeries_of_hasRecurrence`, via `IsRationalSeries.exists_coprime_quotient`.) -/
theorem exists_coprime_quotient_uSeries (lam α : ℝ) (hrec : HasRecurrence lam α) :
    ∃ P Q : ℤ[X], IsRelPrime P Q ∧ Q.coeff 0 = 1 ∧
      (Q : ℤ⟦X⟧) * uSeries lam α = (P : ℤ⟦X⟧) :=
  (isRationalSeries_of_hasRecurrence lam α hrec).exists_coprime_quotient

/-- **Shortcut: `α` is algebraic.** Directly from the recurrence by `αⁿ`-domination: `Σ aᵢ u_{n+i} = 0`
with `uₙ = λαⁿ − εₙ` (`εₙ` bounded) forces `Σ aᵢ αⁱ = 0`, so `α` is a root of the non-zero integer
polynomial `Σ aᵢ Xⁱ`. No residue theory required. -/
theorem isAlgebraic_of_hasRecurrence (lam α : ℝ) (hα : 1 < α) (hlam : lam ≠ 0)
    (hrec : HasRecurrence lam α) : IsAlgebraic ℤ α := by
  obtain ⟨s, hs1, a, ⟨i₀, hi₀s, hi₀⟩, hV⟩ := hrec
  set P : ℝ := ∑ i ∈ Finset.range (s + 1), (a i : ℝ) * α ^ i with hP
  have hPn : ∀ n, lam * α ^ n * P = ∑ i ∈ Finset.range (s + 1), (a i : ℝ) * ε lam α (n + i) := by
    intro n
    have hvr : (∑ i ∈ Finset.range (s + 1), (a i : ℝ) * (u lam α (n + i) : ℝ)) = 0 := by
      have := hV n; rw [V] at this; exact_mod_cast this
    have hsubst : (∑ i ∈ Finset.range (s + 1), (a i : ℝ) * (u lam α (n + i) : ℝ))
        = lam * α ^ n * P - ∑ i ∈ Finset.range (s + 1), (a i : ℝ) * ε lam α (n + i) := by
      rw [hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have h := self_eq_u_add_ε lam α (n + i)
      linear_combination -(a i : ℝ) * h
    linarith [hvr, hsubst]
  have hPeq : P = 0 := by
    by_contra hPne
    set C : ℝ := ∑ i ∈ Finset.range (s + 1), |(a i : ℝ)| * (1 / 2) with hC
    have hbd : ∀ n, |lam * α ^ n * P| ≤ C := by
      intro n
      rw [hPn n]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_ε_le lam α (n + i)) (abs_nonneg _)
    have hlamP : 0 < |lam * P| := abs_pos.mpr (mul_ne_zero hlam hPne)
    have htend : Tendsto (fun n : ℕ => |lam * P| * α ^ n) atTop atTop :=
      Tendsto.const_mul_atTop hlamP (tendsto_pow_atTop_atTop_of_one_lt hα)
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop C).exists
    have hbn := hbd n
    rw [show lam * α ^ n * P = lam * P * α ^ n from by ring, abs_mul,
      abs_of_pos (pow_pos (by linarith : (0:ℝ) < α) n)] at hbn
    linarith
  refine ⟨∑ i ∈ Finset.range (s + 1), C (a i) * X ^ i, ?_, ?_⟩
  · intro hQ0
    apply hi₀
    have hco : (∑ i ∈ Finset.range (s + 1), C (a i) * X ^ i : ℤ[X]).coeff i₀ = a i₀ := by
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hQ0, Polynomial.coeff_zero] at hco; exact hco.symm
  · have haeval : (aeval α) (∑ i ∈ Finset.range (s + 1), C (a i) * X ^ i) = P := by
      rw [map_sum, hP]
      exact Finset.sum_congr rfl (fun i _ => by simp)
    rw [haeval, hPeq]

/-! ### Step d) — the analytic core (cited) and the algebraic conclusions (proved)

`Σ uₙ Xⁿ = P/Q` (Fatou: `P, Q ∈ ℤ[X]` coprime, `Q(0) = 1`) and also `= λ/(1−αz) − ε(z)` with `ε`
analytic on `D(0,1)`. So `f` has a single simple pole in `D(0,1)`, at `1/α`. The two analytic facts
this forces — the pole/zero structure of `Q` and the residue value — are recorded as **cited axioms**
(`Ber92`, `Pat69`): Mathlib has the power-series→analytic and identity-theorem machinery and
`meromorphicOrderAt`, but **no residue theory and no argument principle**, so these specific
complex-analysis facts are not yet mechanizable. Every *algebraic* consequence (algebraic integer,
conjugate bounds, `λ ∈ ℚ(α)`) is then **proved** from them below. -/

informal_result "rational-series-pole-at-denominator-zero"
  latex "If an integer power series f is a reduced rational function P/Q (P,Q coprime in ℤ[X], Q(0)=1) and, on its disc of convergence, also equals λ/(1−αz) plus a function analytic on the unit disc, then f continues meromorphically and its pole at 1/α forces Q(1/α)=0: a pole of a rational function occurs only at a zero of its denominator."
  refs "Ber92"

informal_result "partial-fraction-single-pole-in-disc"
  latex "Since f = λ/(1−αz) − ε(z) with ε analytic on the unit disc, f has exactly one pole there, the simple pole at 1/α. Hence the denominator Q of the reduced rational form P/Q has 1/α as its only zero in the open unit disc, all other zeros lying on or outside the unit circle."
  refs "Ber92"

informal_result "residue-simple-pole-rational-function"
  latex "The residue of f = P/Q at a simple zero z₀ of Q equals P(z₀)/Q'(z₀). Equating with the residue −λ/α read off the partial fraction λ/(1−αz) at z₀ = 1/α gives λ = −α·P(1/α)/Q'(1/α), placing λ in the field ℚ(α)."
  refs "Ber92"

/-- **Analytic core I (cited).** For the reduced rational form `Σ uₙ Xⁿ = P/Q` (`Q(0) = 1`), the
denominator `Q` vanishes at `1/α` (the pole of `f`) and that is its only zero in the open unit disc
(all other zeros have modulus `≥ 1`). Bertin §5.1 / Pathiaux 1969; not yet in Mathlib (needs the
pole/zero structure of a rational function on a disc — residue/argument-principle territory). -/
@[category research solved, AMS 11, ref "Ber92" "Pat69",
  formal_uses uSeries,
  informal_uses "rational-series-pole-at-denominator-zero" "partial-fraction-single-pole-in-disc"]
axiom fatou_denom_disk_zeros (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam) (P Q : ℤ[X])
    (hcop : IsRelPrime P Q) (hQ0 : Q.coeff 0 = 1)
    (hPQ : (Q : ℤ⟦X⟧) * uSeries lam α = (P : ℤ⟦X⟧)) :
    Polynomial.aeval (α⁻¹ : ℝ) Q = 0 ∧
      ∀ z : ℂ, (Q.map (Int.castRingHom ℂ)).IsRoot z → z = (α : ℂ)⁻¹ ∨ 1 ≤ ‖z‖

/-- **Analytic core II (cited).** The residue identity `λ = −α·P(1/α)/Q'(1/α)` for the simple pole
`1/α` of `f = P/Q`. Bertin §5.1 / Pathiaux 1969; not yet in Mathlib (no residue theory). -/
@[category research solved, AMS 11, ref "Ber92" "Pat69",
  formal_uses uSeries,
  informal_uses "residue-simple-pole-rational-function"]
axiom fatou_residue (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam) (P Q : ℤ[X])
    (hcop : IsRelPrime P Q) (hQ0 : Q.coeff 0 = 1)
    (hPQ : (Q : ℤ⟦X⟧) * uSeries lam α = (P : ℤ⟦X⟧)) :
    (lam : ℝ) = -α * Polynomial.aeval (α⁻¹ : ℝ) P
      / Polynomial.aeval (α⁻¹ : ℝ) (Polynomial.derivative Q)

/-- Reciprocal-polynomial root transfer: `Q(1/α) = 0 ⟹ Q.reverse(α) = 0`. -/
private theorem aeval_reverse_eq_zero {α : ℝ} (hα0 : α ≠ 0) {Q : ℤ[X]}
    (hpole : Polynomial.aeval (α⁻¹ : ℝ) Q = 0) : Polynomial.aeval (α : ℝ) Q.reverse = 0 := by
  haveI : Invertible (α⁻¹ : ℝ) := invertibleOfNonzero (inv_ne_zero hα0)
  have hinv : (⅟(α⁻¹ : ℝ)) = α := by rw [invOf_eq_inv, inv_inv]
  have hiff := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ ℝ) (α⁻¹ : ℝ) Q
  rw [hinv] at hiff
  show eval₂ (algebraMap ℤ ℝ) α Q.reverse = 0
  rw [hiff]; exact hpole

/-- **`α` is an algebraic integer** (step d). From Fatou `Q(0) = 1` and the pole `Q(1/α) = 0`
(`fatou_denom_disk_zeros`), the reciprocal `Q.reverse` is monic with `α` as a root. -/
theorem isIntegral_of_hasRecurrence (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hrec : HasRecurrence lam α) : IsIntegral ℤ α := by
  obtain ⟨P, Q, hcop, hQ0, hPQ⟩ := exists_coprime_quotient_uSeries lam α hrec
  have hpole := (fatou_denom_disk_zeros lam α hα hlam P Q hcop hQ0 hPQ).1
  have hα0 : (α : ℝ) ≠ 0 := by positivity
  have htrail : Q.trailingCoeff = 1 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
      (by rw [Polynomial.constantCoeff_apply, hQ0]; norm_num)]
    exact hQ0
  have hmonic : Q.reverse.Monic := by
    rw [Polynomial.Monic, Polynomial.reverse_leadingCoeff, htrail]
  exact ⟨Q.reverse, hmonic, aeval_reverse_eq_zero hα0 hpole⟩

/-- **Conjugates of `α` have modulus `≤ 1`** (step d). A conjugate `β` is a root of the monic
`Q.reverse` (`minpoly ℚ α ∣ Q.reverse`), hence `β⁻¹` is a zero of `Q`; by `fatou_denom_disk_zeros`
either `β⁻¹ = α⁻¹` (`β = α`, excluded) or `‖β⁻¹‖ ≥ 1`, i.e. `‖β‖ ≤ 1`. -/
theorem conjugates_le_one_of_hasRecurrence (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hrec : HasRecurrence lam α) :
    ∀ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) → ‖β‖ ≤ 1 := by
  obtain ⟨P, Q, hcop, hQ0, hPQ⟩ := exists_coprime_quotient_uSeries lam α hrec
  obtain ⟨hpole, hpole2⟩ := fatou_denom_disk_zeros lam α hα hlam P Q hcop hQ0 hPQ
  have hα0 : (α : ℝ) ≠ 0 := by positivity
  have hrev : aeval (α : ℝ) Q.reverse = 0 := aeval_reverse_eq_zero hα0 hpole
  intro β hβ hβα
  have hdvd : minpoly ℚ α ∣ Q.reverse.map (algebraMap ℤ ℚ) := by
    apply minpoly.dvd; rw [Polynomial.aeval_map_algebraMap]; exact hrev
  have hβmin : aeval β (minpoly ℚ α) = 0 := by
    rw [Polynomial.mem_aroots'] at hβ; exact hβ.2
  obtain ⟨c, hc⟩ := hdvd
  have haevalβ : aeval (β : ℂ) Q.reverse = 0 := by
    have hz : aeval (β : ℂ) (Q.reverse.map (algebraMap ℤ ℚ)) = 0 := by
      rw [hc, map_mul, hβmin, zero_mul]
    rwa [Polynomial.aeval_map_algebraMap] at hz
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse] at haevalβ
    have hlc : Q.leadingCoeff = 0 := by simpa using haevalβ
    rw [Polynomial.leadingCoeff_eq_zero] at hlc
    rw [hlc, Polynomial.coeff_zero] at hQ0; exact one_ne_zero hQ0.symm
  haveI : Invertible (β⁻¹) := invertibleOfNonzero (inv_ne_zero hβ0)
  have hinvinv : (⅟(β⁻¹)) = β := by rw [invOf_eq_inv, inv_inv]
  have hiff := Polynomial.eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) (β⁻¹) Q
  rw [hinvinv] at hiff
  have h1 : eval₂ (Int.castRingHom ℂ) β Q.reverse = 0 := by
    rw [show (Int.castRingHom ℂ) = algebraMap ℤ ℂ from rfl]; exact haevalβ
  rw [hiff] at h1
  have hroot : (Q.map (Int.castRingHom ℂ)).IsRoot β⁻¹ := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact h1
  rcases hpole2 β⁻¹ hroot with heq | hge
  · exact absurd (by rw [inv_eq_iff_eq_inv, inv_inv] at heq; exact heq) hβα
  · rw [norm_inv] at hge; exact (one_le_inv₀ (norm_pos_iff.mpr hβ0)).mp hge

/-- **`λ ∈ ℚ(α)`** (step d). The residue identity `λ = −α·P(1/α)/Q'(1/α)` (`fatou_residue`) writes
`λ` as a field expression in `α` over `ℚ`, so it lies in `ℚ(α)`. -/
theorem lam_mem_adjoin_of_hasRecurrence (lam α : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hrec : HasRecurrence lam α) :
    (lam : ℝ) ∈ IntermediateField.adjoin ℚ ({α} : Set ℝ) := by
  obtain ⟨P, Q, hcop, hQ0, hPQ⟩ := exists_coprime_quotient_uSeries lam α hrec
  have hres := fatou_residue lam α hα hlam P Q hcop hQ0 hPQ
  set K := IntermediateField.adjoin ℚ ({α} : Set ℝ) with hK
  have hαK : α ∈ K := IntermediateField.mem_adjoin_simple_self ℚ α
  have hαiK : α⁻¹ ∈ K := K.inv_mem hαK
  have haevalmem : ∀ p : ℤ[X], Polynomial.aeval (α⁻¹ : ℝ) p ∈ K := by
    intro p
    have key := Polynomial.aeval_algebraMap_apply ℝ (⟨α⁻¹, hαiK⟩ : K) p
    have hcoe : algebraMap K ℝ (⟨α⁻¹, hαiK⟩ : K) = α⁻¹ := rfl
    rw [hcoe] at key
    rw [key]; exact (Polynomial.aeval (⟨α⁻¹, hαiK⟩ : K) p).2
  rw [hres]
  exact K.div_mem (K.mul_mem (K.neg_mem hαK) (haevalmem P)) (haevalmem Q.derivative)

/-- **Theorem 5.1.1, assembled** (WIP — depends on the sorried helpers above; the assembly itself is
complete). Once the helpers are discharged this replaces the cited axiom
`pisotSalem_theorem_5_1_1`. -/
theorem pisotSalem_theorem_5_1_1' (α lam : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hbound : ∀ n : ℕ, distToNearestInt (lam * α ^ n) ≤
      1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) :
    IsIntegral ℤ α ∧
      (∀ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) → ‖β‖ ≤ 1) ∧
      (lam : ℝ) ∈ IntermediateField.adjoin ℚ ({α} : Set ℝ) := by
  have hrec := exists_hasRecurrence lam α hα hlam hbound
  exact ⟨isIntegral_of_hasRecurrence lam α hα hlam hrec,
    conjugates_le_one_of_hasRecurrence lam α hα hlam hrec,
    lam_mem_adjoin_of_hasRecurrence lam α hα hlam hrec⟩

end Bertin.AlphaPow
