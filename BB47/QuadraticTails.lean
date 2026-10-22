/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Field.GeomSum
import BB47.Popcount

/-!
# [BBCP04, Thm. 7.1] in degree 2: every quadratic sparse number has `≫ √N` ones

`BB47/Popcount.lean` proves the `√N` bound for the larger root of a quadratic by completing the
square.  For the smaller root (e.g. `2 − √2`, whose ones are the zeros of `√2`) that argument
fails, and so does every positive-coefficient multiple of the minimal polynomial (Descartes).
Here we transcribe the *BBP-tail* argument of [BBCP04, §§6–7] for `D = 2`, base `b`, which works
for **every** quadratic `y = ∑_j b^{-t_j}`, and so discharge the whole `D = 2` slice of the cited
axiom `BB47.bbcp_base_b`.

## The argument (`A y² + B y + C = 0`, `A > 0`)

Write `y² = ∑_n r(n) b^{-n}` without carries (`r(n)` counts ordered pairs `t_i + t_j = n`) and
let `e(n) ∈ {0,1}` be the digit at `n`.  The **tail**

  `T(R) = −C b^R − ∑_{n ≤ R} b^{R−n} (A r(n) + B e(n))`

is an integer, satisfies `T(R+1) = b T(R) − A r(R+1) − B e(R+1)` (`tail_succ`), and equals
`b^R (A (y² − u_R) + B (y − y_R))` with `u_R`, `y_R` the truncations (`tail_eq`).  Hence:

* `T(R) ≥ 0` unless a digit `1` lies in `(R, R + c₀)` (an integer `> −1`), and `T(R) ≥ −|B|`;
* `T(R) ≤ A·#{t_j ≤ R} + O(1)`;
* positivity propagates **down** through zero digits: if `e(R) = 0`, `T(R) ≥ 0` and `r(R) ≥ 1`
  then `T(R − 1) > 0` ([BBCP04, Lem. 6.2]);
* in a gap `(t_j, t_{j+1})` of the ones, Liouville's inequality for quadratic irrationals puts a
  one `t_m` with `t_j + t_m` in the second half of the gap, so `T > 0` on half the gap;
* summing the recurrence, `(b − 1) ∑_{R<N} T(R) ≤ A k² + O(k)` with `k = #{t_j ≤ N}`
  ([BBCP04, Lem. 6.1]).

So `N/2 − O(k) ≤ #{R ≤ N : T(R) > 0} ≤ A k² + O(k)`, i.e. `k ≥ (2A)^{-1/2} √N − O(1)`.

## Main results

* `BB47.QuadraticTails.liouville_quadratic` — `|y − p/q| ≥ c/q²`.
* `BB47.QuadraticTails.ones_bound_quadratic` — `t_j ≤ K j²` for every quadratic irrational `y`.
* `BB47.QuadraticTails.bbcp_base_b_deg_two` — the conclusion of `BB47.bbcp_base_b` when the
  minimal polynomial has degree `2`.
* `BB47.QuadraticTails.sqrt_two_ones` — **Vandehey's constant**: `√2` has at least
  `√(2N) − 3/2` ones among its binary digits at positions `0, …, N`, by pairing the cross terms
  of `Y²` in base `2` (`ds_two_sq_le`) against the borrow block of `Y² = 2^{2N+1} − R`.

## References

* [BBCP04] D. Bailey, J. Borwein, R. Crandall, C. Pomerance, *On the binary expansions of
  algebraic numbers*, J. Théor. Nombres Bordeaux **16** (2004), 487–518 — §§6–7, Thm. 7.1.
-/

namespace BB47.QuadraticTails

open Finset BB47.Popcount

section Defs

variable (t : ℕ → ℕ)

/-- `r(n)`: the number of ordered pairs `(i, j)` with `t_i + t_j = n` (the carry-free coefficient
of `b^{-n}` in `y²`). -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
def rc (n : ℕ) : ℕ := ((range (n + 1) ×ˢ range (n + 1)).filter fun p => t p.1 + t p.2 = n).card

/-- `e(n)`: the base-`b` digit of `y` at position `n` (`1` if `n` is some `t_j`, else `0`). -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
def ec (n : ℕ) : ℕ := ((range (n + 1)).filter fun j => t j = n).card

variable (b : ℕ) (A : ℕ) (B C : ℤ)

/-- The integer part `I(R) = ∑_{n ≤ R} b^{R−n} (A r(n) + B e(n))`. -/
def II (R : ℕ) : ℤ := ∑ n ∈ range (R + 1), (b : ℤ) ^ (R - n) * (A * rc t n + B * ec t n)

/-- The **BBP tail** `T(R) = −C b^R − I(R)` of [BBCP04, §6]. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
def TT (R : ℕ) : ℤ := -C * (b : ℤ) ^ R - II t b A B R

/-- **The tail recurrence** `T(R+1) = b T(R) − (A r(R+1) + B e(R+1))`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem tail_succ (R : ℕ) :
    TT t b A B C (R + 1) = b * TT t b A B C R - (A * rc t (R + 1) + B * ec t (R + 1)) := by
  have hI : II t b A B (R + 1) = b * II t b A B R + (A * rc t (R + 1) + B * ec t (R + 1)) := by
    unfold II
    rw [sum_range_succ, Nat.sub_self, pow_zero, one_mul, mul_sum]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [mem_range] at hn
    rw [show R + 1 - n = (R - n) + 1 by omega, pow_succ]
    ring
  unfold TT
  rw [hI, pow_succ]
  ring

end Defs

section Kappa

variable {t : ℕ → ℕ} (ht : StrictMono t)

include ht in
private lemma exists_gt (R : ℕ) : ∃ j, R < t j := ⟨R + 1, by have := ht.le_apply (x := R + 1); omega⟩

/-- `κ(R) = #{j : t_j ≤ R}`, the number of ones up to position `R`. -/
noncomputable def kappa (R : ℕ) : ℕ := by
  classical exact Nat.find (exists_gt ht R)

include ht in
lemma lt_kappa_iff (R j : ℕ) : j < kappa ht R ↔ t j ≤ R := by
  classical
  unfold kappa
  constructor
  · intro h
    have := Nat.find_min (exists_gt ht R) h
    omega
  · intro h
    by_contra hc
    push Not at hc
    have h1 := Nat.find_spec (exists_gt ht R)
    have h2 := ht.monotone hc
    omega

include ht in
lemma t_kappa_gt (R : ℕ) : R < t (kappa ht R) := by
  have := (lt_kappa_iff ht R (kappa ht R)).not.mp (lt_irrefl _)
  omega

end Kappa

/-! ## The tail as a real number -/

section Real

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t)

/-- The truncation `y_R = ∑_{t_j ≤ R} b^{-t_j}`. -/
noncomputable def yR (R : ℕ) : ℝ := ∑ j ∈ range (kappa ht R), ((b : ℝ) ^ t j)⁻¹

/-- The pairs `(i, j)` with `t_i + t_j ≤ R`. -/
noncomputable def PR (R : ℕ) : Finset (ℕ × ℕ) :=
  (range (kappa ht R) ×ˢ range (kappa ht R)).filter fun p => t p.1 + t p.2 ≤ R

/-- The carry-free truncation `u_R = ∑_{t_i + t_j ≤ R} b^{-t_i - t_j}` of `y²`. -/
noncomputable def uR (R : ℕ) : ℝ := ∑ p ∈ PR ht R, ((b : ℝ) ^ (t p.1 + t p.2))⁻¹

include hb ht in
lemma sum_ec (R : ℕ) :
    ∑ n ∈ range (R + 1), (b : ℝ) ^ (R - n) * (ec t n : ℝ) = (b : ℝ) ^ R * yR (b := b) ht R := by
  classical
  have hb0 : (b : ℝ) ≠ 0 := by have := one_lt_b hb; positivity
  have hmaps : ∀ j ∈ range (kappa ht R), t j ∈ range (R + 1) := by
    intro j hj
    rw [mem_range] at hj ⊢
    have := (lt_kappa_iff ht R j).mp hj
    omega
  unfold yR
  rw [mul_sum, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  have hset : (range (kappa ht R)).filter (fun j => t j = n) = (range (n + 1)).filter
      (fun j => t j = n) := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨by have := ht.le_apply (x := j); omega, h⟩
    · rintro ⟨-, h⟩
      exact ⟨(lt_kappa_iff ht R j).mpr (by omega), h⟩
  have : ∑ j ∈ (range (kappa ht R)).filter (fun j => t j = n), (b : ℝ) ^ R * ((b : ℝ) ^ t j)⁻¹
      = ∑ j ∈ (range (kappa ht R)).filter (fun j => t j = n), (b : ℝ) ^ (R - n) := by
    refine sum_congr rfl fun j hj => ?_
    rw [mem_filter] at hj
    rw [hj.2, pow_sub₀ _ hb0 (by omega)]
  rw [this, sum_const, nsmul_eq_mul, hset, ec, mul_comm]

include hb ht in
lemma sum_rc (R : ℕ) :
    ∑ n ∈ range (R + 1), (b : ℝ) ^ (R - n) * (rc t n : ℝ) = (b : ℝ) ^ R * uR (b := b) ht R := by
  classical
  have hb0 : (b : ℝ) ≠ 0 := by have := one_lt_b hb; positivity
  have hmaps : ∀ p ∈ PR ht R, t p.1 + t p.2 ∈ range (R + 1) := by
    intro p hp
    unfold PR at hp
    rw [mem_filter] at hp
    rw [mem_range]
    omega
  unfold uR
  rw [mul_sum, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  have hset : (PR ht R).filter (fun p => t p.1 + t p.2 = n) =
      (range (n + 1) ×ˢ range (n + 1)).filter (fun p => t p.1 + t p.2 = n) := by
    ext ⟨i, j⟩
    simp only [PR, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      refine ⟨⟨?_, ?_⟩, h⟩
      · have := ht.le_apply (x := i); omega
      · have := ht.le_apply (x := j); omega
    · rintro ⟨-, h⟩
      exact ⟨⟨⟨(lt_kappa_iff ht R i).mpr (by omega), (lt_kappa_iff ht R j).mpr (by omega)⟩,
        by omega⟩, h⟩
  have : ∑ p ∈ (PR ht R).filter (fun p => t p.1 + t p.2 = n),
        (b : ℝ) ^ R * ((b : ℝ) ^ (t p.1 + t p.2))⁻¹
      = ∑ p ∈ (PR ht R).filter (fun p => t p.1 + t p.2 = n), (b : ℝ) ^ (R - n) := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter] at hp
    rw [hp.2, pow_sub₀ _ hb0 (by omega)]
  rw [this, sum_const, nsmul_eq_mul, hset, rc, mul_comm]

include hb ht in
/-- **The tail as a real number**: `T(R) = b^R (A (y² − u_R) + B (y − y_R))`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem tail_eq (A : ℕ) (B C : ℤ)
    (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0) (R : ℕ) :
    (TT t b A B C R : ℝ) = (b : ℝ) ^ R * (A * (sparseValue b t ^ 2 - uR (b := b) ht R)
      + B * (sparseValue b t - yR (b := b) ht R)) := by
  have hII : (II t b A B R : ℝ) = A * ((b : ℝ) ^ R * uR (b := b) ht R)
      + B * ((b : ℝ) ^ R * yR (b := b) ht R) := by
    rw [← sum_rc hb ht, ← sum_ec hb ht, mul_sum, mul_sum, ← sum_add_distrib]
    unfold II
    push_cast
    refine sum_congr rfl fun n _ => ?_
    ring
  unfold TT
  push_cast
  rw [hII]
  linear_combination (-(b : ℝ) ^ R) * hpoly

include hb ht in
/-- `y = y_R + (tail from index κ(R))`. -/
lemma y_split (R : ℕ) :
    sparseValue b t = yR (b := b) ht R + ∑' i : ℕ, ((b : ℝ) ^ t (i + kappa ht R))⁻¹ :=
  ((summable_sparse hb ht).sum_add_tsum_nat_add (kappa ht R)).symm

include hb ht in
lemma y_sub_yR_pos (R : ℕ) : 0 < sparseValue b t - yR (b := b) ht R := by
  rw [y_split hb ht R]
  have hsum : Summable fun i : ℕ => ((b : ℝ) ^ t (i + kappa ht R))⁻¹ :=
    (summable_sparse hb ht).comp_injective (add_left_injective _)
  have hb1 := one_lt_b hb
  have := hsum.tsum_pos (fun i => by positivity) 0 (by positivity)
  linarith

include hb ht in
/-- If no one lies in `(R, M)`, then `b^R (y − y_R) ≤ 2 b^{R−M}`. -/
lemma tail_le_gap (R M : ℕ) (hM : ∀ j, R < t j → M ≤ t j) :
    (b : ℝ) ^ R * (sparseValue b t - yR (b := b) ht R) ≤ 2 * (b : ℝ) ^ R * ((b : ℝ) ^ M)⁻¹ := by
  have hb1 := one_lt_b hb
  have h1 : sparseValue b t - yR (b := b) ht R ≤ 2 * ((b : ℝ) ^ t (kappa ht R))⁻¹ := by
    have := tail_le_from hb ht (kappa ht R)
    rw [y_split hb ht R]; linarith
  have h2 : ((b : ℝ) ^ t (kappa ht R))⁻¹ ≤ ((b : ℝ) ^ M)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ hb1.le (hM _ (t_kappa_gt ht R))
  have : (0 : ℝ) ≤ (b : ℝ) ^ R := by positivity
  nlinarith

include hb ht in
lemma tail_le_one (R : ℕ) :
    (b : ℝ) ^ R * (sparseValue b t - yR (b := b) ht R) ≤ 1 := by
  have hb1 := one_lt_b hb
  have h := tail_le_gap hb ht R (R + 1) (fun j hj => hj)
  have h2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have : 2 * (b : ℝ) ^ R * ((b : ℝ) ^ (R + 1))⁻¹ = 2 / b := by
    rw [pow_succ]; field_simp
  rw [this] at h
  have : (2 : ℝ) / b ≤ 1 := by rw [div_le_one (by positivity)]; exact h2
  linarith

include hb ht in
/-- A finite set of distinct powers `b^{-t_j}` with all `t_j ≥ M` sums to at most `2 b^{-M}`. -/
lemma fin_geom (S : Finset ℕ) (M : ℕ) (hS : ∀ j ∈ S, M ≤ t j) :
    ∑ j ∈ S, ((b : ℝ) ^ t j)⁻¹ ≤ 2 * ((b : ℝ) ^ M)⁻¹ := by
  classical
  have hb1 := one_lt_b hb
  have hinv : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  rw [← sum_image (f := fun m => ((b : ℝ) ^ m)⁻¹) (fun i _ j _ h => ht.injective h)]
  set L := (S.image t).sup id + 1
  have hsub : S.image t ⊆ Ico M L := by
    intro m hm
    rw [mem_Ico]
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
      exact hS j hj
    · have := le_sup (f := id) hm
      simp only [id] at this
      omega
  calc ∑ m ∈ S.image t, ((b : ℝ) ^ m)⁻¹ ≤ ∑ m ∈ Ico M L, ((b : ℝ) ^ m)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ m ∈ Ico M L, ((b : ℝ)⁻¹) ^ m := by simp [inv_pow]
    _ ≤ ((b : ℝ)⁻¹) ^ M / (1 - (b : ℝ)⁻¹) := geom_sum_Ico_le_of_lt_one hinv (inv_b_lt_one hb)
    _ ≤ 2 * ((b : ℝ) ^ M)⁻¹ := by
      rw [inv_pow, div_le_iff₀ (by linarith [inv_b_lt_one hb])]
      have h2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have : (b : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
      have : (0 : ℝ) ≤ ((b : ℝ) ^ M)⁻¹ := by positivity
      nlinarith

include ht in
lemma yR_sq (R : ℕ) : yR (b := b) ht R ^ 2 =
    ∑ p ∈ range (kappa ht R) ×ˢ range (kappa ht R), ((b : ℝ) ^ (t p.1 + t p.2))⁻¹ := by
  rw [yR, sq, sum_mul_sum, sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [pow_add, mul_inv]

include hb ht in
/-- `0 ≤ y_R² − u_R` and `b^R (y_R² − u_R) ≤ κ(R)`. -/
lemma yR_sq_sub_uR (R : ℕ) :
    0 ≤ yR (b := b) ht R ^ 2 - uR (b := b) ht R ∧
      (b : ℝ) ^ R * (yR (b := b) ht R ^ 2 - uR (b := b) ht R) ≤ kappa ht R := by
  classical
  have hb1 := one_lt_b hb
  set K := kappa ht R
  set f : ℕ × ℕ → ℝ := fun p => ((b : ℝ) ^ (t p.1 + t p.2))⁻¹
  have hsplit := sum_filter_add_sum_filter_not (range K ×ˢ range K) (fun p => t p.1 + t p.2 ≤ R) f
  have hdiff : yR (b := b) ht R ^ 2 - uR (b := b) ht R
      = ∑ p ∈ (range K ×ˢ range K).filter (fun p => ¬ t p.1 + t p.2 ≤ R), f p := by
    rw [yR_sq ht, uR, PR, ← hsplit]; ring
  rw [hdiff]
  refine ⟨sum_nonneg fun p _ => by positivity, ?_⟩
  have hinner : ∀ i ∈ range K,
      ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R), f (i, j) ≤ 2 * ((b : ℝ) ^ (R + 1))⁻¹ := by
    intro i hi
    have hti : t i ≤ R := (lt_kappa_iff ht R i).mp (mem_range.mp hi)
    have : ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R), f (i, j)
        = ((b : ℝ) ^ t i)⁻¹ * ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R),
          ((b : ℝ) ^ t j)⁻¹ := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
      simp only [f, pow_add, mul_inv]
    rw [this]
    have hg := fin_geom hb ht ((range K).filter (fun j => ¬ t i + t j ≤ R)) (R + 1 - t i)
      (by intro j hj; rw [mem_filter] at hj; omega)
    calc ((b : ℝ) ^ t i)⁻¹ * ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R), ((b : ℝ) ^ t j)⁻¹
        ≤ ((b : ℝ) ^ t i)⁻¹ * (2 * ((b : ℝ) ^ (R + 1 - t i))⁻¹) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 2 * ((b : ℝ) ^ (R + 1))⁻¹ := by
        rw [show R + 1 = t i + (R + 1 - t i) by omega, pow_add]
        simp only [show t i + (R + 1 - t i) - t i = R + 1 - t i by omega]
        rw [mul_inv]; ring
  have hfilt : ∑ p ∈ (range K ×ˢ range K).filter (fun p => ¬ t p.1 + t p.2 ≤ R), f p
      = ∑ i ∈ range K, ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R), f (i, j) := by
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_filter]
  rw [hfilt]
  have hsum : ∑ i ∈ range K, ∑ j ∈ (range K).filter (fun j => ¬ t i + t j ≤ R), f (i, j)
      ≤ K * (2 * ((b : ℝ) ^ (R + 1))⁻¹) := by
    calc _ ≤ ∑ i ∈ range K, 2 * ((b : ℝ) ^ (R + 1))⁻¹ := sum_le_sum hinner
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have h2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbR : (b : ℝ) ^ R * (K * (2 * ((b : ℝ) ^ (R + 1))⁻¹)) = K * (2 / b) := by
    rw [pow_succ]; field_simp
  have h2b : (2 : ℝ) / b ≤ 1 := by rw [div_le_one (by positivity)]; exact h2
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  calc (b : ℝ) ^ R * _ ≤ (b : ℝ) ^ R * (K * (2 * ((b : ℝ) ^ (R + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K * (2 / b) := hbR
    _ ≤ K := by nlinarith

end Real


/-! ## Bounds on the tail -/

section Bounds

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t) (A : ℕ) (B C : ℤ)
  (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0)

include hb ht in
lemma yR_nonneg (R : ℕ) : 0 ≤ yR (b := b) ht R := sum_nonneg fun _ _ => by positivity

include hb ht in
lemma uR_le (R : ℕ) : uR (b := b) ht R ≤ sparseValue b t ^ 2 := by
  have h1 := (yR_sq_sub_uR hb ht R).1
  have h2 := y_sub_yR_pos hb ht R
  have h3 := yR_nonneg hb ht R
  nlinarith

include hb ht hpoly in
/-- `T(R) ≥ −|B| b^R (y − y_R)`. -/
lemma TT_ge (R : ℕ) :
    -|(B : ℝ)| * ((b : ℝ) ^ R * (sparseValue b t - yR (b := b) ht R)) ≤ TT t b A B C R := by
  rw [tail_eq hb ht A B C hpoly R]
  have h1 := uR_le hb ht R
  have h2 := (y_sub_yR_pos hb ht R).le
  have hbR : (0 : ℝ) ≤ (b : ℝ) ^ R := by positivity
  have hX : 0 ≤ (b : ℝ) ^ R * (sparseValue b t - yR (b := b) ht R) := mul_nonneg hbR h2
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hAterm : 0 ≤ (b : ℝ) ^ R * (A * (sparseValue b t ^ 2 - uR (b := b) ht R)) :=
    mul_nonneg hbR (mul_nonneg hA (by linarith))
  have hB : -|(B : ℝ)| ≤ B := by
    have := neg_abs_le (B : ℝ); simpa using this
  nlinarith

include hb ht hpoly in
lemma TT_ge_abs (R : ℕ) : -|B| ≤ TT t b A B C R := by
  have h := TT_ge hb ht A B C hpoly R
  have h1 := tail_le_one hb ht R
  have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ R) (y_sub_yR_pos hb ht R).le
  have hB : (0 : ℝ) ≤ |(B : ℝ)| := abs_nonneg _
  have : -|(B : ℝ)| ≤ TT t b A B C R := by nlinarith
  exact_mod_cast this

include hb ht hpoly in
/-- **`T(R) ≥ 0` away from the ones.**  If `2|B| < b^{c₀}` and no one lies in `(R, R + c₀)`, then
`T(R) ≥ 0`: it is an integer `> −1`. -/
lemma TT_nonneg_of_gap (c₀ : ℕ) (hc₀ : 2 * |(B : ℝ)| < (b : ℝ) ^ c₀) (R : ℕ)
    (hgap : ∀ j, R < t j → R + c₀ ≤ t j) : 0 ≤ TT t b A B C R := by
  have h := TT_ge hb ht A B C hpoly R
  have hg := tail_le_gap hb ht R (R + c₀) hgap
  have hb1 := one_lt_b hb
  have hpow : 2 * (b : ℝ) ^ R * ((b : ℝ) ^ (R + c₀))⁻¹ = 2 * ((b : ℝ) ^ c₀)⁻¹ := by
    rw [pow_add]; field_simp
  rw [hpow] at hg
  have hB : (0 : ℝ) ≤ |(B : ℝ)| := abs_nonneg _
  have hlt : |(B : ℝ)| * (2 * ((b : ℝ) ^ c₀)⁻¹) < 1 := by
    rw [← mul_assoc, mul_comm |(B : ℝ)| 2, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hc₀
  have : (-1 : ℝ) < TT t b A B C R := by nlinarith
  have : (-1 : ℤ) < TT t b A B C R := by exact_mod_cast this
  omega

include hb ht hpoly in
/-- `T(R) ≤ A (κ(R) + 2y) + |B|`. -/
lemma TT_le (R : ℕ) :
    (TT t b A B C R : ℝ) ≤ A * (kappa ht R + 2 * sparseValue b t) + |(B : ℝ)| := by
  rw [tail_eq hb ht A B C hpoly R]
  set y := sparseValue b t
  set X := (b : ℝ) ^ R * (y - yR (b := b) ht R)
  have hX1 : X ≤ 1 := tail_le_one hb ht R
  have hX0 : 0 ≤ X := mul_nonneg (by positivity) (y_sub_yR_pos hb ht R).le
  have hq := (yR_sq_sub_uR hb ht R).2
  have hyR := yR_nonneg hb ht R
  have hyy : yR (b := b) ht R ≤ y := (y_sub_yR_pos hb ht R).le |> fun h => by linarith
  have hsplit : (b : ℝ) ^ R * (y ^ 2 - uR (b := b) ht R)
      = X * (y + yR (b := b) ht R) + (b : ℝ) ^ R * (yR (b := b) ht R ^ 2 - uR (b := b) ht R) := by
    simp only [X]; ring
  have h1 : X * (y + yR (b := b) ht R) ≤ 2 * y := by nlinarith
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hBX : (B : ℝ) * X ≤ |(B : ℝ)| := by
    have : (B : ℝ) ≤ |(B : ℝ)| := le_abs_self _
    have hB0 : (0 : ℝ) ≤ |(B : ℝ)| := abs_nonneg _
    nlinarith
  have : (b : ℝ) ^ R * (A * (y ^ 2 - uR (b := b) ht R) + B * (y - yR (b := b) ht R))
      = A * ((b : ℝ) ^ R * (y ^ 2 - uR (b := b) ht R)) + B * X := by simp only [X]; ring
  rw [this, hsplit]
  nlinarith

end Bounds

/-! ## Liouville's inequality for quadratic irrationals -/

/-- **Liouville's inequality** for a quadratic irrational `y`: `|y − p/q| ≥ c/q²`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem liouville_quadratic {y : ℝ} (A : ℕ) (hA : 0 < A) (B C : ℤ)
    (hpoly : (A : ℝ) * y ^ 2 + B * y + C = 0) (hirr : Irrational y) :
    ∃ cL : ℝ, 0 < cL ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → cL / (q : ℝ) ^ 2 ≤ |y - p / q| := by
  set H : ℝ := A * (2 * |y| + 1) + |(B : ℝ)| with hH
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hHpos : 0 < H := by positivity
  refine ⟨min 1 (1 / H), by positivity, fun p q hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  by_cases hbig : 1 ≤ |y - p / q|
  · calc min 1 (1 / H) / (q : ℝ) ^ 2 ≤ 1 / (q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (min_le_left _ _) hq2.le
      _ ≤ 1 := by rw [div_le_one hq2]; nlinarith
      _ ≤ _ := hbig
  push Not at hbig
  set x : ℝ := p / q with hx
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  -- the nonzero integer `A p² + B p q + C q²`
  set N0 : ℤ := A * p ^ 2 + B * p * q + C * q ^ 2 with hN0
  have hN0r : (N0 : ℝ) = (q : ℝ) ^ 2 * ((x - y) * (A * (x + y) + B)) := by
    have hxq : (p : ℝ) = x * q := by rw [hx]; field_simp
    simp only [hN0]; push_cast
    linear_combination (A * (p + x * q) + B * q) * hxq + (q : ℝ) ^ 2 * hpoly
  have hN0ne : N0 ≠ 0 := by
    intro h0
    have : (x - y) * (A * (x + y) + B) = 0 := by
      have h0' : (N0 : ℝ) = 0 := by exact_mod_cast h0
      rw [hN0r] at h0'
      rcases mul_eq_zero.mp h0' with h | h
      · exact absurd h (by positivity)
      · exact h
    rcases mul_eq_zero.mp this with h | h
    · exact hirr ⟨(p : ℚ) / q, by push_cast; rw [← hx]; linarith⟩
    · refine hirr ⟨-(B : ℚ) / A - (p : ℚ) / q, ?_⟩
      have hA0 : (A : ℝ) ≠ 0 := by positivity
      push_cast
      rw [← hx]
      field_simp
      linarith
  have hN1 : (1 : ℝ) ≤ |(N0 : ℝ)| := by
    have : (1 : ℤ) ≤ |N0| := Int.one_le_abs hN0ne
    exact_mod_cast this
  have hxy : |x + y| ≤ 2 * |y| + 1 := by
    have : |x| ≤ |y| + 1 := by
      have := abs_sub_abs_le_abs_sub y x
      rw [abs_sub_comm] at hbig
      have h2 := abs_sub_abs_le_abs_sub x y
      linarith
    calc |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ 2 * |y| + 1 := by linarith
  have hfac : |(A : ℝ) * (x + y) + B| ≤ H := by
    calc |(A : ℝ) * (x + y) + B| ≤ |(A : ℝ) * (x + y)| + |(B : ℝ)| := abs_add_le _ _
      _ = A * |x + y| + |(B : ℝ)| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ A * (2 * |y| + 1) + |(B : ℝ)| := by gcongr
      _ = H := by rw [hH]
  have hkey : 1 ≤ (q : ℝ) ^ 2 * (|y - x| * H) := by
    calc (1 : ℝ) ≤ |(N0 : ℝ)| := hN1
      _ = (q : ℝ) ^ 2 * (|x - y| * |(A : ℝ) * (x + y) + B|) := by
        rw [hN0r, abs_mul, abs_mul, abs_of_pos hq2]
      _ ≤ (q : ℝ) ^ 2 * (|y - x| * H) := by
        rw [abs_sub_comm x y]; gcongr
  have : 1 / H / (q : ℝ) ^ 2 ≤ |y - x| := by
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc min 1 (1 / H) / (q : ℝ) ^ 2 ≤ 1 / H / (q : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) hq2.le
    _ ≤ _ := this


/-! ## Positivity in the gaps, and the count -/

section Gaps

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t) (A : ℕ) (hA : 0 < A) (B C : ℤ)
  (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0)

include ht in
lemma t_add_le (a k : ℕ) : t a + k ≤ t (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := ht (show a + k < a + (k + 1) by omega)
    omega

include ht in
/-- No digit `1` strictly between two consecutive ones. -/
lemma ec_eq_zero {j n : ℕ} (h1 : t j < n) (h2 : n < t (j + 1)) : ec t n = 0 := by
  unfold ec
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i _ hi
  have a : j < i := ht.lt_iff_lt.mp (by omega)
  have c : i < j + 1 := ht.lt_iff_lt.mp (by omega)
  omega

include ht in
lemma rc_pos (i m : ℕ) : 1 ≤ rc t (t i + t m) := by
  unfold rc
  refine card_pos.mpr ⟨(i, m), ?_⟩
  simp only [mem_filter, mem_product, mem_range, and_true]
  have := ht.le_apply (x := i)
  have := ht.le_apply (x := m)
  omega

include hb ht hA in
/-- **Positivity propagates down through zero digits** ([BBCP04, Lem. 6.2] for `D = 2`).  If
`t_j < R' < t_{j+1}`, `T(R') ≥ 0` and `r(R') ≥ 1`, then `T(R) > 0` for `t_j ≤ R < R'`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem TT_pos_down (j R' : ℕ) (hlo : t j < R') (hhi : R' < t (j + 1))
    (h0 : 0 ≤ TT t b A B C R') (hr : 1 ≤ rc t R') :
    ∀ R, t j ≤ R → R < R' → 0 < TT t b A B C R := by
  have hb0 : (0 : ℤ) ≤ b := by positivity
  suffices H : ∀ d R, R + 1 + d = R' → t j ≤ R → 0 < TT t b A B C R by
    intro R h1 h2; exact H (R' - 1 - R) R (by omega) h1
  intro d
  induction d with
  | zero =>
    intro R hR h1
    have hs := tail_succ t b A B C R
    rw [show R + 1 = R' by omega, ec_eq_zero ht hlo hhi] at hs
    have hA1 : (1 : ℤ) ≤ A := by exact_mod_cast hA
    have hr1 : (1 : ℤ) ≤ rc t R' := by exact_mod_cast hr
    have : (1 : ℤ) ≤ A * rc t R' := by nlinarith
    have : 0 < (b : ℤ) * TT t b A B C R := by push_cast at hs; linarith
    exact pos_of_mul_pos_right this hb0
  | succ d ih =>
    intro R hR h1
    have hpos := ih (R + 1) (by omega) (by omega)
    have hs := tail_succ t b A B C R
    rw [ec_eq_zero ht (show t j < R + 1 by omega) (show R + 1 < t (j + 1) by omega)] at hs
    have : (0 : ℤ) ≤ A * rc t (R + 1) := by positivity
    have : 0 < (b : ℤ) * TT t b A B C R := by push_cast at hs; linarith
    exact pos_of_mul_pos_right this hb0

include hb ht hA hpoly in
/-- **Ones in the second half of every long gap** (Liouville).  Every prefix `[0, G]` with
`G ≥ t_0` contains a one at a position `≥ (G − c')/2`. -/
lemma gap_liouville (hirr : Irrational (sparseValue b t)) :
    ∃ c' : ℕ, ∀ G, t 0 ≤ G → ∃ m, t m ≤ G ∧ G ≤ 2 * t m + c' := by
  obtain ⟨cL, hcL, hL⟩ := liouville_quadratic A hA B C hpoly hirr
  have hb1 := one_lt_b hb
  obtain ⟨c', hc'⟩ := pow_unbounded_of_one_lt (2 / cL) hb1
  refine ⟨c', fun G hG => ?_⟩
  set K := kappa ht G
  have hK : 0 < K := (lt_kappa_iff ht G 0).mpr hG
  refine ⟨K - 1, (lt_kappa_iff ht G (K - 1)).mp (by omega), ?_⟩
  by_contra hcon
  push Not at hcon
  set m := K - 1
  set p : ℕ := ∑ j ∈ range K, b ^ (t m - t j)
  set q : ℝ := (b : ℝ) ^ t m
  have hqpos : 0 < q := by positivity
  have hyR : yR (b := b) ht G = (p : ℝ) / q := by
    rw [eq_div_iff hqpos.ne']
    unfold yR
    simp only [p, q]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun j hj => ?_
    have : t j ≤ t m := ht.monotone (by rw [mem_range] at hj; omega)
    rw [pow_sub₀ _ (by positivity) this]
    field_simp
  have h1 := hL (p : ℤ) (b ^ t m) (by positivity)
  have h3 := y_sub_yR_pos hb ht G
  have h2 := tail_le_gap hb ht G (G + 1) (fun j hj => hj)
  have hbG : (0 : ℝ) < (b : ℝ) ^ G := by positivity
  have h2' : sparseValue b t - yR (b := b) ht G ≤ 2 * ((b : ℝ) ^ (G + 1))⁻¹ := by
    have : (b : ℝ) ^ G * (sparseValue b t - yR (b := b) ht G)
        ≤ (b : ℝ) ^ G * (2 * ((b : ℝ) ^ (G + 1))⁻¹) := by linarith
    exact le_of_mul_le_mul_left this hbG
  rw [hyR] at h3 h2'
  push_cast at h1
  rw [abs_of_pos h3] at h1
  -- `cL/q² ≤ 2 b^{-(G+1)}` while `b^{G+1} ≥ q² b^{c'}`
  have hpow : q ^ 2 * (b : ℝ) ^ c' ≤ (b : ℝ) ^ (G + 1) := by
    have : q ^ 2 * (b : ℝ) ^ c' = (b : ℝ) ^ (2 * t m + c') := by
      simp only [q]; rw [pow_add, pow_mul']
    rw [this]
    exact pow_le_pow_right₀ hb1.le (by omega)
  have hchain : cL / q ^ 2 ≤ 2 * ((b : ℝ) ^ (G + 1))⁻¹ := h1.trans h2'
  have hbG1 : (0 : ℝ) < (b : ℝ) ^ (G + 1) := by positivity
  rw [div_le_iff₀ (by positivity), mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc,
    le_div_iff₀ hbG1] at hchain
  have hcb : 2 < cL * (b : ℝ) ^ c' := by
    rw [div_lt_iff₀ hcL] at hc'; linarith
  have hq2 : 0 < q ^ 2 := by positivity
  nlinarith

include hb ht hA hpoly in
/-- **Half of every gap is positive.**  For `t_j ≤ X ≤ t_{j+1}`,
`X − t_j ≤ 2·#{R ∈ [t_j, X) : T(R) > 0} + c`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem gap_count (c₀ c' : ℕ) (hc₀1 : 1 ≤ c₀) (hc₀ : 2 * |(B : ℝ)| < (b : ℝ) ^ c₀)
    (hc' : ∀ G, t 0 ≤ G → ∃ m, t m ≤ G ∧ G ≤ 2 * t m + c') (j X : ℕ) (hX1 : t j ≤ X)
    (hX2 : X ≤ t (j + 1)) :
    X - t j ≤ 2 * ((Ico (t j) X).filter fun R => 0 < TT t b A B C R).card
      + (c₀ + c' + t 0 + 1) := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = t (j + 1) - c₀ - t j := ⟨_, rfl⟩
  by_cases hG : t 0 ≤ G ∧ c' < G
  · obtain ⟨m, hm1, hm2⟩ := hc' G hG.1
    obtain ⟨R', hR'⟩ : ∃ R', R' = t j + t m := ⟨_, rfl⟩
    have hlo : t j < R' := by omega
    have hhi : R' + c₀ ≤ t (j + 1) := by omega
    have h0 : 0 ≤ TT t b A B C R' := by
      refine TT_nonneg_of_gap hb ht A B C hpoly c₀ hc₀ R' fun i hi => ?_
      have : j < i := ht.lt_iff_lt.mp (by omega)
      have : t (j + 1) ≤ t i := ht.monotone (by omega)
      omega
    have hpos := TT_pos_down hb ht A hA B C j R' hlo (by omega) h0 (by rw [hR']; exact rc_pos ht j m)
    have hsub : Ico (t j) (min R' X) ⊆ (Ico (t j) X).filter fun R => 0 < TT t b A B C R := by
      intro R hR
      rw [mem_Ico] at hR
      rw [mem_filter, mem_Ico]
      exact ⟨⟨hR.1, by omega⟩, hpos R hR.1 (by omega)⟩
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  · omega

include hb ht hA hpoly in
/-- Summing `gap_count` over the gaps up to `t_K`. -/
lemma count_lower (c₀ c' : ℕ) (hc₀1 : 1 ≤ c₀) (hc₀ : 2 * |(B : ℝ)| < (b : ℝ) ^ c₀)
    (hc' : ∀ G, t 0 ≤ G → ∃ m, t m ≤ G ∧ G ≤ 2 * t m + c') (N : ℕ) :
    ∀ K, (∀ i < K, t i ≤ N) → min (t K) (N + 1) - t 0 ≤
      2 * ((Ico (t 0) (min (t K) (N + 1))).filter fun R => 0 < TT t b A B C R).card
        + K * (c₀ + c' + t 0 + 1) := by
  classical
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hK
    have htK : t K ≤ N := hK K (by omega)
    have hIH := ih fun i hi => hK i (by omega)
    rw [show min (t K) (N + 1) = t K by omega] at hIH
    have hmono : t K ≤ t (K + 1) := (ht (show K < K + 1 by omega)).le
    have h0K : t 0 ≤ t K := ht.monotone (Nat.zero_le K)
    have hgap := gap_count hb ht A hA B C hpoly c₀ c' hc₀1 hc₀ hc' K (min (t (K + 1)) (N + 1))
      (by omega) (min_le_left _ _)
    rw [← Ico_union_Ico_eq_Ico h0K (show t K ≤ min (t (K + 1)) (N + 1) by omega), filter_union,
      card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _))]
    have : min (t (K + 1)) (N + 1) - t 0
        = (t K - t 0) + (min (t (K + 1)) (N + 1) - t K) := by omega
    rw [this]
    nlinarith

include ht in
/-- `∑_{n < t_{J+1}} r(n) ≤ (J + 1)²`: every pair counted has both entries among the first
`J + 1` ones. -/
lemma sum_rc_le (J : ℕ) : ∑ n ∈ range (t (J + 1)), rc t n ≤ (J + 1) ^ 2 := by
  classical
  set S := (range (J + 1) ×ˢ range (J + 1)).filter fun p => t p.1 + t p.2 < t (J + 1)
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => t p.1 + t p.2) S (range (t (J + 1))) := by
    intro p hp
    simp only [S, coe_filter, Set.mem_ofPred_eq] at hp
    simpa using hp.2
  have hcard := card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ n ∈ range (t (J + 1)),
      (S.filter fun p => t p.1 + t p.2 = n).card = rc t n := by
    intro n hn
    rw [mem_range] at hn
    unfold rc
    congr 1
    ext ⟨i, k⟩
    simp only [S, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      refine ⟨⟨?_, ?_⟩, h⟩
      · have := ht.le_apply (x := i); omega
      · have := ht.le_apply (x := k); omega
    · rintro ⟨-, h⟩
      refine ⟨⟨⟨ht.lt_iff_lt.mp (by omega), ht.lt_iff_lt.mp (by omega)⟩, by omega⟩, h⟩
  rw [sum_congr rfl hfib] at hcard
  rw [← hcard]
  calc S.card ≤ (range (J + 1) ×ˢ range (J + 1)).card := card_filter_le _ _
    _ = (J + 1) ^ 2 := by rw [card_product, card_range, sq]

include ht in
lemma sum_ec_le (J : ℕ) : ∑ n ∈ range (t (J + 1)), ec t n ≤ J + 1 := by
  classical
  set S := (range (J + 1)).filter fun j => t j < t (J + 1)
  have hmaps : Set.MapsTo t S (range (t (J + 1))) := by
    intro j hj
    simp only [S, coe_filter, Set.mem_ofPred_eq] at hj
    simpa using hj.2
  have hcard := card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ n ∈ range (t (J + 1)), (S.filter fun j => t j = n).card = ec t n := by
    intro n hn
    rw [mem_range] at hn
    unfold ec
    congr 1
    ext i
    simp only [S, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      exact ⟨by have := ht.le_apply (x := i); omega, h⟩
    · rintro ⟨-, h⟩
      exact ⟨⟨ht.lt_iff_lt.mp (by omega), by omega⟩, h⟩
  rw [sum_congr rfl hfib] at hcard
  rw [← hcard]
  calc S.card ≤ (range (J + 1)).card := card_filter_le _ _
    _ = J + 1 := card_range _

/-- **Summing the recurrence**: `(b − 1) ∑_{R<N} T(R) = ∑_{R<N} (A r(R+1) + B e(R+1)) − T(0) + T(N)`
([BBCP04, Lem. 6.1]). -/
lemma telescope (N : ℕ) :
    ((b : ℤ) - 1) * ∑ R ∈ range N, TT t b A B C R
      = ∑ R ∈ range N, ((A : ℤ) * rc t (R + 1) + B * ec t (R + 1))
        - TT t b A B C 0 + TT t b A B C N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, mul_add, ih, tail_succ t b A B C N]
    ring

include hb ht hpoly in
/-- `#{R < t_{J+1} : T(R) < 0} ≤ (J + 1 + c₀) c₀`: a negative tail needs a one within `c₀`. -/
lemma neg_count (c₀ : ℕ) (hc₀ : 2 * |(B : ℝ)| < (b : ℝ) ^ c₀) (J : ℕ) :
    ((range (t (J + 1))).filter fun R => TT t b A B C R < 0).card ≤ (J + 1 + c₀) * c₀ := by
  classical
  have hsub : (range (t (J + 1))).filter (fun R => TT t b A B C R < 0) ⊆
      (range (J + 1 + c₀)).biUnion fun i => Ico (t i - c₀) (t i) := by
    intro R hR
    rw [mem_filter, mem_range] at hR
    have : ¬ ∀ i, R < t i → R + c₀ ≤ t i := by
      intro h
      have := TT_nonneg_of_gap hb ht A B C hpoly c₀ hc₀ R h
      omega
    push Not at this
    obtain ⟨i, hi1, hi2⟩ := this
    rw [mem_biUnion]
    refine ⟨i, ?_, ?_⟩
    · rw [mem_range]
      by_contra hc
      push Not at hc
      have h1 := t_add_le ht (J + 1) c₀
      have h2 := ht.monotone hc
      omega
    · rw [mem_Ico]; omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i ∈ range (J + 1 + c₀), (Ico (t i - c₀) (t i)).card := card_biUnion_le
    _ ≤ ∑ i ∈ range (J + 1 + c₀), c₀ := sum_le_sum fun i _ => by rw [Nat.card_Ico]; omega
    _ = (J + 1 + c₀) * c₀ := by rw [sum_const, card_range, smul_eq_mul]

include ht in
lemma kappa_eq (J : ℕ) : kappa ht (t (J + 1) - 1) = J + 1 := by
  have h1 : J < kappa ht (t (J + 1) - 1) :=
    (lt_kappa_iff ht _ J).mpr (by have := ht (show J < J + 1 by omega); omega)
  have h2 : ¬ J + 1 < kappa ht (t (J + 1) - 1) := by
    rw [lt_kappa_iff]
    have := ht.le_apply (x := J + 1)
    omega
  omega

end Gaps

/-- The final bookkeeping, isolated: all quantities are reals and `x = J + 1 ≥ 1`. -/
private lemma final_arith {t1 t0 P TN S Neg A Bb y c c₀ x : ℝ} (hx : 1 ≤ x) (hA : 0 ≤ A)
    (hBb : 0 ≤ Bb) (hy : 0 ≤ y) (hc : 0 ≤ c) (hc0 : 0 ≤ c₀) (ht0 : 0 ≤ t0)
    (hlow : t1 - t0 ≤ 2 * P + x * c) (h1 : P - Bb * Neg ≤ S + TN)
    (h2 : S ≤ A * x ^ 2 + Bb * x + Bb + TN) (h3 : Neg ≤ (x + c₀) * c₀)
    (hT : TN ≤ A * (x + 2 * y) + Bb) :
    t1 ≤ (t0 + c + 2 * (3 * A + 4 * A * y + 4 * Bb + Bb * (1 + c₀) * c₀) + 1) * x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hx1 : 1 ≤ x ^ 2 := by nlinarith
  have e0 : Bb * Neg ≤ Bb * ((x + c₀) * c₀) := mul_le_mul_of_nonneg_left h3 hBb
  have e1 : t0 ≤ t0 * x ^ 2 := by nlinarith
  have e2 : x * c ≤ c * x ^ 2 := by nlinarith
  have e3 : A * x ≤ A * x ^ 2 := by nlinarith
  have hAy : 0 ≤ A * y := by positivity
  have e4 : A * y ≤ A * y * x ^ 2 := by nlinarith
  have e5 : Bb * x ≤ Bb * x ^ 2 := by nlinarith
  have e6 : Bb ≤ Bb * x ^ 2 := by nlinarith
  have hBc : 0 ≤ Bb * c₀ := by positivity
  have e7 : Bb * c₀ * x ≤ Bb * c₀ * x ^ 2 := by nlinarith
  have hBc2 : 0 ≤ Bb * c₀ ^ 2 := by positivity
  have e8 : Bb * c₀ ^ 2 ≤ Bb * c₀ ^ 2 * x ^ 2 := by nlinarith
  have e9 : 0 ≤ x ^ 2 := by positivity
  have : t1 ≤ t0 + x * c + 2 * (A * x ^ 2 + Bb * x + Bb + 2 * (A * (x + 2 * y) + Bb)
      + Bb * ((x + c₀) * c₀)) := by linarith
  nlinarith

/-! ## The theorem -/

section Main

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t)

include hb ht in
/-- **[BBCP04, Thm. 7.1] for `D = 2`, base `b`.**  If `y = ∑_j b^{-t_j}` is a quadratic irrational,
`A y² + B y + C = 0` with `A > 0`, then `t_j ≤ K j²` for all `j ≥ 1`: `y` has `≫ √N` ones among
its first `N` digits. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ones_bound_quadratic (A : ℕ) (hA : 0 < A) (B C : ℤ)
    (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0)
    (hirr : Irrational (sparseValue b t)) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, 1 ≤ j → (t j : ℝ) ≤ K * (j : ℝ) ^ 2 := by
  classical
  have hb1 := one_lt_b hb
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (2 * |(B : ℝ)|) hb1
  set c₀ := c₁ + 1
  have hc₀ : 2 * |(B : ℝ)| < (b : ℝ) ^ c₀ :=
    lt_of_lt_of_le hc₁ (pow_le_pow_right₀ hb1.le (by omega))
  obtain ⟨c', hc'⟩ := gap_liouville hb ht A hA B C hpoly hirr
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = c₀ + c' + t 0 + 1 := ⟨_, rfl⟩
  have hy : 0 < sparseValue b t := sparseValue_pos hb ht
  have hBb : 0 ≤ |(B : ℝ)| := abs_nonneg _
  refine ⟨t 0 + c + 2 * (3 * A + 4 * A * sparseValue b t + 4 * |(B : ℝ)|
    + |(B : ℝ)| * (1 + c₀) * c₀) + 1, by positivity, fun j hj => ?_⟩
  obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, N = t (J + 1) - 1 := ⟨_, rfl⟩
  have htN : t (J + 1) = N + 1 := by have := ht.le_apply (x := J + 1); omega
  -- lower bound on the number of positive tails
  have hlow := count_lower hb ht A hA B C hpoly c₀ c' (by omega) hc₀ hc' N (J + 1)
    (fun i hi => by
      have := ht.monotone (show i ≤ J by omega); have := ht (show J < J + 1 by omega); omega)
  rw [show min (t (J + 1)) (N + 1) = N + 1 by omega, ← hc] at hlow
  set Pos := (range (N + 1)).filter fun R => 0 < TT t b A B C R
  have hP : ((Ico (t 0) (N + 1)).filter fun R => 0 < TT t b A B C R).card ≤ Pos.card := by
    refine card_le_card fun R hR => ?_
    rw [mem_filter, mem_Ico] at hR
    rw [mem_filter, mem_range]
    exact ⟨hR.1.2, hR.2⟩
  -- upper bound: `#pos ≤ ∑ T + |B| #neg`
  set Neg := (range (N + 1)).filter fun R => TT t b A B C R < 0
  have hNeg : Neg.card ≤ (J + 1 + c₀) * c₀ := by
    have := neg_count hb ht A B C hpoly c₀ hc₀ J
    rwa [htN] at this
  have hterm : ∀ R ∈ range (N + 1), ((if 0 < TT t b A B C R then 1 else 0 : ℤ))
      - |B| * (if TT t b A B C R < 0 then 1 else 0 : ℤ) ≤ TT t b A B C R := by
    intro R _
    have := TT_ge_abs hb ht A B C hpoly R
    split_ifs <;> omega
  have hsum1 : (Pos.card : ℤ) - |B| * Neg.card ≤ ∑ R ∈ range (N + 1), TT t b A B C R := by
    have := sum_le_sum hterm
    rw [sum_sub_distrib, ← mul_sum, sum_boole, sum_boole] at this
    exact this
  -- the telescoped sum
  have htel := telescope (b := b) (t := t) A B C N
  have hrc : ∑ R ∈ range N, (rc t (R + 1) : ℤ) ≤ (J + 1) ^ 2 := by
    have h := sum_rc_le ht J
    rw [htN, sum_range_succ'] at h
    have : ∑ R ∈ range N, rc t (R + 1) ≤ (J + 1) ^ 2 := by omega
    exact_mod_cast this
  have hec : ∑ R ∈ range N, (ec t (R + 1) : ℤ) ≤ J + 1 := by
    have h := sum_ec_le ht J
    rw [htN, sum_range_succ'] at h
    have : ∑ R ∈ range N, ec t (R + 1) ≤ J + 1 := by omega
    exact_mod_cast this
  have hec0 : 0 ≤ ∑ R ∈ range N, (ec t (R + 1) : ℤ) := sum_nonneg fun _ _ => by positivity
  have hA_sum : ∑ R ∈ range N, ((A : ℤ) * rc t (R + 1) + B * ec t (R + 1))
      ≤ A * (J + 1) ^ 2 + |B| * (J + 1) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hA0 : (0 : ℤ) ≤ A := by positivity
    have h1 : (A : ℤ) * ∑ R ∈ range N, (rc t (R + 1) : ℤ) ≤ A * (J + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hrc hA0
    have h2 : B * ∑ R ∈ range N, (ec t (R + 1) : ℤ) ≤ |B| * (J + 1) := by
      calc B * ∑ R ∈ range N, (ec t (R + 1) : ℤ) ≤ |B| * ∑ R ∈ range N, (ec t (R + 1) : ℤ) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) hec0
        _ ≤ |B| * (J + 1) := mul_le_mul_of_nonneg_left hec (abs_nonneg B)
    linarith
  have hT0 := TT_ge_abs hb ht A B C hpoly 0
  have hTN := TT_ge_abs hb ht A B C hpoly N
  set S := ∑ R ∈ range N, TT t b A B C R
  have hS : S ≤ A * (J + 1) ^ 2 + |B| * (J + 1) + |B| + TT t b A B C N := by
    have hb2 : (1 : ℤ) ≤ (b : ℤ) - 1 := by
      have : (2 : ℤ) ≤ b := by exact_mod_cast hb
      linarith
    by_cases hS0 : 0 ≤ S
    · nlinarith
    · have : (0 : ℤ) ≤ A * (J + 1) ^ 2 + |B| * (J + 1) := by positivity
      linarith
  have hfull : ∑ R ∈ range (N + 1), TT t b A B C R = S + TT t b A B C N := sum_range_succ _ _
  rw [hfull] at hsum1
  -- pass to the reals and conclude
  have hTNr := TT_le hb ht A B C hpoly N
  have hk : kappa ht N = J + 1 := by rw [hN]; exact kappa_eq ht J
  rw [hk] at hTNr
  have hlowN : t (J + 1) - t 0 ≤ 2 * Pos.card + (J + 1) * c := by omega
  have h0 : t 0 ≤ t (J + 1) := ht.monotone (Nat.zero_le _)
  have hlowr : (t (J + 1) : ℝ) - t 0 ≤ 2 * (Pos.card : ℝ) + ((J : ℝ) + 1) * c := by
    have : ((t (J + 1) - t 0 : ℕ) : ℝ) ≤ ((2 * Pos.card + (J + 1) * c : ℕ) : ℝ) := by
      exact_mod_cast hlowN
    push_cast [h0] at this
    linarith
  have h1r : (Pos.card : ℝ) - |(B : ℝ)| * Neg.card ≤ (S : ℝ) + TT t b A B C N := by
    have : ((Pos.card : ℤ) : ℝ) - ((|B| : ℤ) : ℝ) * ((Neg.card : ℤ) : ℝ)
        ≤ ((S + TT t b A B C N : ℤ) : ℝ) := by exact_mod_cast hsum1
    push_cast at this
    exact this
  have h2r : (S : ℝ) ≤ A * ((J : ℝ) + 1) ^ 2 + |(B : ℝ)| * ((J : ℝ) + 1) + |(B : ℝ)|
      + TT t b A B C N := by
    have : ((S : ℤ) : ℝ) ≤ ((A * (J + 1) ^ 2 + |B| * (J + 1) + |B| + TT t b A B C N : ℤ) : ℝ) := by
      exact_mod_cast hS
    push_cast at this
    exact this
  have h3r : (Neg.card : ℝ) ≤ ((J : ℝ) + 1 + c₀) * c₀ := by exact_mod_cast hNeg
  push_cast at hTNr ⊢
  exact final_arith (by have : (0 : ℝ) ≤ J := Nat.cast_nonneg _; linarith) (Nat.cast_nonneg _)
    hBb hy.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hlowr h1r h2r h3r hTNr

include hb ht in
/-- **[BBCP04, Thm. 7.1] in degree `2`**, in exactly the form of the cited axiom
`BB47.bbcp_base_b`, proved (standard axioms only): this discharges the whole `D = 2` slice. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem bbcp_base_b_deg_two (halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : (minpoly ℚ (sparseValue b t)).natDegree = 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (t j : ℝ) ≤ C * (j : ℝ) ^ (minpoly ℚ (sparseValue b t)).natDegree := by
  rw [hdeg]
  set y := sparseValue b t with hy
  set p := minpoly ℚ y with hp
  have hmon : p.Monic := minpoly.monic halg.isIntegral
  have hc2 : p.coeff 2 = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
  set c1 := p.coeff 1
  set c0 := p.coeff 0
  have hroot : y ^ 2 + (c1 : ℝ) * y + c0 = 0 := by
    have h := minpoly.aeval ℚ y
    rw [Polynomial.aeval_eq_sum_range, ← hp, hdeg] at h
    simp [Finset.sum_range_succ, hc2, Algebra.smul_def] at h
    linear_combination h
  have hirr : Irrational y := irrational_of_one_lt_minpoly_natDegree (by rw [← hp, hdeg]; omega)
  have hd1 : (0 : ℝ) < c1.den := by positivity
  have hd0 : (0 : ℝ) < c0.den := by positivity
  have hc1 : (c1 : ℝ) = c1.num / c1.den := Rat.cast_def c1
  have hc0 : (c0 : ℝ) = c0.num / c0.den := Rat.cast_def c0
  refine ones_bound_quadratic hb ht (c1.den * c0.den) (by positivity) (c1.num * c0.den)
    (c0.num * c1.den) ?_ hirr
  have : ((c1.den * c0.den : ℕ) : ℝ) * y ^ 2 + ((c1.num * c0.den : ℤ) : ℝ) * y
      + ((c0.num * c1.den : ℤ) : ℝ)
      = ((c1.den * c0.den : ℕ) : ℝ) * (y ^ 2 + (c1 : ℝ) * y + c0) := by
    rw [hc1, hc0]; push_cast; field_simp
  rw [this, hroot, mul_zero]

end Main

/-! ## Vandehey's constant for `√2` -/

section SqrtTwo

/-- **Pairing the cross terms in base 2.**  A number with `k` binary ones has a square with at
most `k(k+1)/2` binary ones: `(∑ 2^{e})² = ∑ 2^{2e} + ∑_{e<e'} 2^{e+e'+1}`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ds_two_sq_le (S : Finset ℕ) :
    2 * ds 2 ((∑ e ∈ S, 2 ^ e) ^ 2) ≤ S.card * (S.card + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha]
    set X := ∑ e ∈ S, 2 ^ e
    have hX : ds 2 X ≤ S.card := by
      refine (ds_sum_le le_rfl _ _).trans ?_
      simp [ds_pow le_rfl]
    have hsq : (2 ^ a + X) ^ 2 = 1 * 2 ^ (2 * a) + (X * 2 ^ (a + 1) + X ^ 2) := by ring
    have h1 : ds 2 ((2 ^ a + X) ^ 2) ≤ 1 + (ds 2 X + ds 2 (X ^ 2)) := by
      rw [hsq]
      refine (ds_add_le le_rfl _ _).trans (Nat.add_le_add ?_ ((ds_add_le le_rfl _ _).trans ?_))
      · rw [ds_mul_pow le_rfl, ds_one le_rfl]
      · rw [ds_mul_pow le_rfl]
    nlinarith

/-- **The borrow block of `√2`.**  With `Y = ⌊2^N √2⌋ = ∑_{t_j ≤ N} 2^{N − t_j}`,
`Y² + R = 2^{2N+1}` with `0 < R ≤ 2^{N+2}`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem sqrt_two_borrow {t : ℕ → ℕ} (ht : StrictMono t) (hy : sparseValue 2 t = √2) (N : ℕ) :
    ∃ R : ℕ, 0 < R ∧ R ≤ 2 ^ (N + 2) ∧
      (∑ j ∈ range (kappa ht N), 2 ^ (N - t j)) ^ 2 + R = 2 ^ (2 * N + 1) := by
  have hb : 2 ≤ 2 := le_rfl
  set K := kappa ht N
  set Y : ℕ := ∑ j ∈ range K, 2 ^ (N - t j)
  have hYr : (Y : ℝ) = (2 : ℝ) ^ N * yR (b := 2) ht N := by
    simp only [Y, yR]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have : t j ≤ N := (lt_kappa_iff ht N j).mp (mem_range.mp hj)
    rw [pow_sub₀ _ (by norm_num) this]
  set ε := (2 : ℝ) ^ N * (sparseValue 2 t - yR (b := 2) ht N)
  have hε0 : 0 < ε := mul_pos (by positivity) (y_sub_yR_pos hb ht N)
  have hε1 : ε ≤ 1 := by simpa using tail_le_one hb ht N
  have hY : (2 : ℝ) ^ N * √2 = Y + ε := by rw [hYr, ← hy]; simp only [ε]; ring
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lo : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2hi : √2 < (3 : ℝ) / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  -- `Y² + R = 2^{2N+1}` with `0 < R < 2^{N+2}`
  set R : ℤ := 2 * 4 ^ N - (Y : ℤ) ^ 2 with hRdef
  have hRr : (R : ℝ) = ε * (2 * (2 : ℝ) ^ N * √2 - ε) := by
    have : (R : ℝ) = 2 * ((2 : ℝ) ^ N) ^ 2 - (Y : ℝ) ^ 2 := by
      simp only [hRdef]; push_cast; rw [show (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    rw [this, show (Y : ℝ) = (2 : ℝ) ^ N * √2 - ε by linarith]
    linear_combination (-((2 : ℝ) ^ N) ^ 2) * hs2
  have h2N : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hRpos : (0 : ℝ) < R := by
    rw [hRr]; exact mul_pos hε0 (by nlinarith)
  have hRlt : (R : ℝ) ≤ (2 : ℝ) ^ (N + 2) := by
    rw [hRr, pow_add]
    have : 2 * (2 : ℝ) ^ N * √2 - ε ≤ 2 * (2 : ℝ) ^ N * √2 := by linarith
    have : ε * (2 * (2 : ℝ) ^ N * √2 - ε) ≤ 1 * (2 * (2 : ℝ) ^ N * √2) := by
      apply mul_le_mul hε1 this (by nlinarith) (by norm_num)
    nlinarith
  have hR0 : 0 < R := by exact_mod_cast hRpos
  have hRn : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR0.le
  refine ⟨R.toNat, by omega, ?_, ?_⟩
  · have : (R.toNat : ℝ) ≤ ((2 ^ (N + 2) : ℕ) : ℝ) := by
      have : (R.toNat : ℝ) = (R : ℝ) := by exact_mod_cast hRn
      rw [this]; push_cast; exact hRlt
    exact_mod_cast this
  · have : ((Y ^ 2 + R.toNat : ℕ) : ℤ) = ((2 ^ (2 * N + 1) : ℕ) : ℤ) := by
      have h4 : (4 : ℤ) ^ N = 2 ^ (2 * N) := by rw [pow_mul]; norm_num
      push_cast
      rw [hRn, hRdef, h4]
      ring
    exact_mod_cast this

/-- **Vandehey's constant.**  Among the first `N` binary digits of `√2` (positions `0, …, N`)
there are at least `√(2N) − 3/2` ones.  This is the `√(2N)` bound of
`plans/report-sqrtnorm.html` §2.7, obtained by pairing the cross terms of `Y²`. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem sqrt_two_ones {t : ℕ → ℕ} (ht : StrictMono t) (hy : sparseValue 2 t = √2) (N : ℕ) :
    √(2 * N) - 3 / 2 ≤ kappa ht N := by
  classical
  have hb : 2 ≤ 2 := le_rfl
  set K := kappa ht N
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  -- the key inequality `K (K + 1) ≥ 2 (N − 1)`
  suffices hkey : 2 * ((N : ℝ) - 1) ≤ K * (K + 1) by
    rw [sub_le_iff_le_add, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0; push_cast; nlinarith
  obtain ⟨Rn, hR0, hRnle, hX⟩ := sqrt_two_borrow ht hy N
  set Y : ℕ := ∑ j ∈ range K, 2 ^ (N - t j)
  rw [show 2 * N + 1 = (N + 2) + (N - 1) by omega, ← one_mul (2 ^ _)] at hX
  have hlower := ds_borrow_block hb le_rfl hR0 hRnle hX
  -- upper: `Y` has `K` binary ones
  have hYS : Y = ∑ e ∈ (range K).image (fun j => N - t j), 2 ^ e := by
    rw [sum_image]
    intro i hi j hj hij
    have hi' := (lt_kappa_iff ht N i).mp (mem_coe.mp hi |> mem_range.mp)
    have hj' := (lt_kappa_iff ht N j).mp (mem_coe.mp hj |> mem_range.mp)
    exact ht.injective (by simp only at hij; omega)
  have hcard : ((range K).image (fun j => N - t j)).card = K := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    have hi' := (lt_kappa_iff ht N i).mp (mem_coe.mp hi |> mem_range.mp)
    have hj' := (lt_kappa_iff ht N j).mp (mem_coe.mp hj |> mem_range.mp)
    exact ht.injective (by simp only at hij; omega)
  have hupper := ds_two_sq_le ((range K).image (fun j => N - t j))
  rw [← hYS, hcard] at hupper
  have : 2 * (N - 1) ≤ K * (K + 1) := by omega
  have : ((2 * (N - 1) : ℕ) : ℝ) ≤ ((K * (K + 1) : ℕ) : ℝ) := by exact_mod_cast this
  push_cast [show 1 ≤ N by omega] at this
  linarith

end SqrtTwo

end BB47.QuadraticTails
