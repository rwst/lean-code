/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Minpoly.Field
import BB47.Sliver
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The `√N` ones bound for quadratic irrationals with `0/1` digits

The quadratic case of [BBCP04, Thm. 7.1], i.e. the `D = 2` slice of the cited axiom
`BB47.bbcp_base_b`, for every sparse number `y = ∑_j b^{-t_j}` that is the **larger** root of its
quadratic equation; in particular for every `y` with `y² ∈ ℚ` (`plans/report-sqrtnorm.html` §2.7,
rank #2).

## The argument

Let `A y² + B y + C = 0` with `A > 0` and `δ = 2Ay + B > 0` (`y` is the larger root).  Truncate at
`N = t_{J+1} − 1`: `b^N y = Y + ε` with `Y = ∑_{j ≤ J} b^{N − t_j}` and `0 < ε ≤ 1`.  Put
`Z = 2AY + B b^N` and `D = B² − 4AC = δ²`.  Then

  `Z² = D b^{2N} − R`,  `R = 4Aε(b^N δ − Aε)`,  `0 < R ≤ 4Aδ b^N`,

so the binary-like base-`b` expansion of `Z²` carries a block of `N − O(1)` digits `b − 1` (the
*borrow block*), and its digit sum `s_b(Z²)` is `≥ (b − 1)(N − O(1))`.  On the other side
`s_b(Z) ≤ s_b(2A)(J + 1) + δ` — the term `B b^N` only touches the top `O(1)` digits, whatever its
sign — and `s_b(Z²) ≤ s_b(Z)²`.  Hence `t_{J+1} ≪ (J + 1)²`.

This replaces [BBCP04, Thm. 5.2] (which needs `B ≥ 0`) by completing the square.  The smaller
root (e.g. `2 − √2`, whose ones are the zeros of `√2`) is genuinely different: there no multiple
of the minimal polynomial has a single sign change (Descartes), and [BBCP04, §7] is needed.

## Main results

* `BB47.Popcount.ds_mul_le`, `ds_add_le`, `ds_split` — the digit-sum calculus.
* `BB47.Popcount.ones_bound_of_larger_root` — `t_j ≤ C j²` for the larger root.
* `BB47.Popcount.bbcp_base_b_sq` — the conclusion of `BB47.bbcp_base_b` when `y² ∈ ℚ`.
* `BB47.Popcount.bbcp_base_b_larger` — the same for every `y` of degree `2` that is the larger
  root of its minimal polynomial.

## References

* [BBCP04] D. Bailey, J. Borwein, R. Crandall, C. Pomerance, *On the binary expansions of
  algebraic numbers*, J. Théor. Nombres Bordeaux **16** (2004), 487–518 — Thms. 5.2, 7.1.
-/

namespace BB47.Popcount

/-! ## Digit sums -/

/-- The base-`b` digit sum `s_b(n)`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
def ds (b n : ℕ) : ℕ := (Nat.digits b n).sum

section DigitSum

variable {b : ℕ} (hb : 2 ≤ b)

@[simp] lemma ds_zero (b : ℕ) : ds b 0 = 0 := by simp [ds]

include hb in
lemma ds_eq (n : ℕ) : ds b n = n % b + ds b (n / b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · unfold ds
    rw [Nat.digits_def' (by omega) hn, List.sum_cons]

include hb in
lemma ds_add_mul {d : ℕ} (hd : d < b) (m : ℕ) : ds b (d + b * m) = d + ds b m := by
  have h1 : (d + b * m) % b = d := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  have h2 : (d + b * m) / b = m := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hd, zero_add]
  rw [ds_eq hb, h1, h2]

include hb in
lemma ds_of_lt {d : ℕ} (hd : d < b) : ds b d = d := by
  simpa using ds_add_mul hb hd 0

include hb in
lemma ds_one : ds b 1 = 1 := ds_of_lt hb (by omega)

include hb in
lemma ds_mul_base (m : ℕ) : ds b (b * m) = ds b m := by
  simpa using ds_add_mul hb (d := 0) (by omega) m

include hb in
lemma ds_mul_pow (n e : ℕ) : ds b (n * b ^ e) = ds b n := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, show n * (b ^ e * b) = b * (n * b ^ e) by ring, ds_mul_base hb, ih]

include hb in
lemma ds_pow (e : ℕ) : ds b (b ^ e) = 1 := by
  simpa [ds_one hb] using ds_mul_pow hb 1 e

include hb in
lemma ds_le_self (n : ℕ) : ds b n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hlt : n / b < n := Nat.div_lt_self hn (by omega)
      have hdec := Nat.mod_add_div n b
      have hq : n / b ≤ b * (n / b) := Nat.le_mul_of_pos_left _ (by omega)
      rw [ds_eq hb]
      have := ih _ hlt
      omega

include hb in
/-- **Subadditivity** `s_b(m + n) ≤ s_b(m) + s_b(n)`: every carry costs `b − 1`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ds_add_le (m n : ℕ) : ds b (m + n) ≤ ds b m + ds b n := by
  induction h : m + n using Nat.strong_induction_on generalizing m n with
  | _ s ih =>
    rw [← h]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
      simp
    obtain ⟨r, q, hr, rfl⟩ : ∃ r q, r < b ∧ m = r + b * q :=
      ⟨m % b, m / b, Nat.mod_lt m (by omega), (Nat.mod_add_div m b).symm⟩
    obtain ⟨r', q', hr', rfl⟩ : ∃ r q, r < b ∧ n = r + b * q :=
      ⟨n % b, n / b, Nat.mod_lt n (by omega), (Nat.mod_add_div n b).symm⟩
    have hbq : b * q + b * q' ≥ 2 * (q + q') := by nlinarith
    have hq : q + q' < s := by omega
    rw [ds_add_mul hb hr, ds_add_mul hb hr']
    have h2 := ih _ hq q q' rfl
    by_cases hc : r + r' < b
    · have : r + b * q + (r' + b * q') = (r + r') + b * (q + q') := by ring
      rw [this, ds_add_mul hb hc]
      omega
    · have : r + b * q + (r' + b * q') = (r + r' - b) + b * (q + q' + 1) := by
        zify [show b ≤ r + r' by omega]; ring
      rw [this, ds_add_mul hb (by omega)]
      have hq1 : q + q' + 1 < s := by omega
      have h1 := ih _ hq1 (q + q') 1 rfl
      rw [ds_one hb] at h1
      omega

include hb in
lemma ds_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ds b (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ds b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ds_add_le hb _ _).trans (by omega)

include hb in
lemma ds_nsmul_le (c n : ℕ) : ds b (c * n) ≤ c * ds b n := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [add_mul, one_mul, add_mul, one_mul]
    exact (ds_add_le hb _ _).trans (by omega)

include hb in
/-- **Submultiplicativity** `s_b(mn) ≤ s_b(m) s_b(n)`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ds_mul_le (m n : ℕ) : ds b (m * n) ≤ ds b m * ds b n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    have hm := Nat.mod_add_div m b
    have hlt : m / b < m := Nat.div_lt_self hm0 (by omega)
    have hsplit : m * n = (m % b) * n + b * (m / b * n) := by
      conv_lhs => rw [← hm]
      ring
    rw [hsplit, ds_eq hb m]
    calc ds b ((m % b) * n + b * (m / b * n))
        ≤ ds b ((m % b) * n) + ds b (b * (m / b * n)) := ds_add_le hb _ _
      _ ≤ (m % b) * ds b n + ds b (m / b) * ds b n := by
        rw [ds_mul_base hb]
        exact Nat.add_le_add (ds_nsmul_le hb _ _) (ih _ hlt)
      _ = (m % b + ds b (m / b)) * ds b n := by ring

include hb in
/-- Cutting the expansion at position `e`: `s_b(n) = s_b(n mod b^e) + s_b(⌊n / b^e⌋)`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ds_split (e n : ℕ) : ds b n = ds b (n % b ^ e) + ds b (n / b ^ e) := by
  induction e generalizing n with
  | zero => simp [Nat.mod_one]
  | succ e ih =>
    have hmod : n % b ^ (e + 1) = n % b + b * (n / b % b ^ e) := by
      rw [pow_succ', Nat.mod_mul]
    have hdiv : n / b ^ (e + 1) = n / b / b ^ e := by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [hmod, hdiv, ds_add_mul hb (Nat.mod_lt _ (by omega)), ds_eq hb n, ih (n / b)]
    ring

include hb in
lemma ds_pow_sub_one (m : ℕ) : ds b (b ^ m - 1) = (b - 1) * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 1 ≤ b ^ m := Nat.one_le_pow _ _ (by omega)
    have : b ^ (m + 1) - 1 = (b - 1) + b * (b ^ m - 1) := by
      rw [pow_succ]
      have : 1 ≤ b ^ m * b := le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
      zify [h1, this, show 1 ≤ b by omega]
      ring
    rw [this, ds_add_mul hb (by omega), ih]
    ring

include hb in
/-- **The borrow block.**  If `X + R = D b^{e+m}` with `D ≥ 1` and `0 < R ≤ b^e`, then the digits
of `X` at positions `e, …, e + m − 1` are all `b − 1`, so `s_b(X) ≥ (b − 1) m`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ds_borrow_block {X R D e m : ℕ} (hD : 1 ≤ D) (hR0 : 0 < R) (hRe : R ≤ b ^ e)
    (hX : X + R = D * b ^ (e + m)) : (b - 1) * m ≤ ds b X := by
  have hbm : 1 ≤ b ^ m := Nat.one_le_pow _ _ (by omega)
  have hDm : 1 ≤ D * b ^ m := le_trans hbm (Nat.le_mul_of_pos_left _ (by omega))
  have hbe : 0 < b ^ e := by positivity
  have hXeq : X = (b ^ e - R) + (D * b ^ m - 1) * b ^ e := by
    have : D * b ^ (e + m) = D * b ^ m * b ^ e := by ring
    rw [this] at hX
    zify [hRe, hDm] at hX ⊢
    linarith
  have hdiv : X / b ^ e = D * b ^ m - 1 := by
    rw [hXeq, Nat.add_mul_div_right _ _ hbe, Nat.div_eq_of_lt (by omega), zero_add]
  have hq : D * b ^ m - 1 = (b ^ m - 1) + b ^ m * (D - 1) := by
    zify [hbm, hDm, hD]
    ring
  have hmod : (D * b ^ m - 1) % b ^ m = b ^ m - 1 := by
    rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  calc (b - 1) * m = ds b (b ^ m - 1) := (ds_pow_sub_one hb m).symm
    _ = ds b ((D * b ^ m - 1) % b ^ m) := by rw [hmod]
    _ ≤ ds b (D * b ^ m - 1) := by rw [ds_split hb m (D * b ^ m - 1)]; omega
    _ = ds b (X / b ^ e) := by rw [hdiv]
    _ ≤ ds b X := by rw [ds_split hb e X]; omega

end DigitSum

/-! ## The sparse number near its truncations -/

section Sparse

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t)

include hb in
lemma one_lt_b : (1 : ℝ) < (b : ℝ) := by
  have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

include hb in
lemma inv_b_lt_one : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_b hb)

include hb ht in
lemma summable_sparse : Summable fun j : ℕ => ((b : ℝ) ^ t j)⁻¹ := by
  have hgeo : Summable fun j : ℕ => ((b : ℝ)⁻¹) ^ j :=
    summable_geometric_of_lt_one (by positivity) (inv_b_lt_one hb)
  refine hgeo.of_nonneg_of_le (fun j => by positivity) fun j => ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (inv_b_lt_one hb).le ht.le_apply

include hb ht in
/-- The tail of the sparse series from index `K` on is at most `2 b^{-t_K}`. -/
lemma tail_le_from (K : ℕ) :
    (∑' i : ℕ, ((b : ℝ) ^ t (i + K))⁻¹) ≤ 2 * ((b : ℝ) ^ t K)⁻¹ := by
  have hb1 := one_lt_b hb
  have hsum : Summable fun i : ℕ => ((b : ℝ) ^ t (i + K))⁻¹ :=
    (summable_sparse hb ht).comp_injective (add_left_injective K)
  have hgeo : Summable fun i : ℕ => ((b : ℝ) ^ t K)⁻¹ * ((b : ℝ)⁻¹) ^ i :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) (inv_b_lt_one hb))
  have hle : ∀ i : ℕ, ((b : ℝ) ^ t (i + K))⁻¹ ≤ ((b : ℝ) ^ t K)⁻¹ * ((b : ℝ)⁻¹) ^ i := by
    intro i
    have hexp : t K + i ≤ t (i + K) := by
      have key : ∀ k, t K + k ≤ t (K + k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have := ht (show K + k < K + (k + 1) by omega)
          omega
      simpa [add_comm] using key i
    have hrhs : ((b : ℝ) ^ t K)⁻¹ * ((b : ℝ)⁻¹) ^ i = ((b : ℝ) ^ (t K + i))⁻¹ := by
      rw [pow_add, mul_inv, inv_pow]
    rw [hrhs, inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ hb1.le hexp
  refine (hsum.tsum_le_tsum hle hgeo).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_b_lt_one hb)]
  have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hfac : (1 - (b : ℝ)⁻¹)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith [inv_b_lt_one hb]) (by norm_num)]
    have : (b : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
    linarith
  have hpos : (0 : ℝ) ≤ ((b : ℝ) ^ t K)⁻¹ := by positivity
  nlinarith

include hb ht in
private lemma tail_le (J : ℕ) :
    (∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹) ≤ 2 * ((b : ℝ) ^ t (J + 1))⁻¹ :=
  tail_le_from hb ht (J + 1)

include hb ht in
/-- **Truncation.**  With `N = t_{J+1} − 1` and `Y = ∑_{j ≤ J} b^{N − t_j}` (an integer whose
base-`b` digits are `0/1`, with `J + 1` ones), `b^N y = Y + ε` with `0 < ε ≤ 1`. -/
@[category API, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem truncation (J : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (b : ℝ) ^ (t (J + 1) - 1) * sparseValue b t
        = ((∑ j ∈ Finset.range (J + 1), b ^ (t (J + 1) - 1 - t j) : ℕ) : ℝ) + ε := by
  set N := t (J + 1) - 1 with hN
  have hb1 := one_lt_b hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hsum := summable_sparse hb ht
  have hsplit := hsum.sum_add_tsum_nat_add (J + 1)
  have htN : t (J + 1) = N + 1 := by
    have := ht (show J < J + 1 by omega)
    omega
  set τ := ∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹ with hτ
  have hτpos : 0 < τ := by
    have hsum' : Summable fun i : ℕ => ((b : ℝ) ^ t (i + (J + 1)))⁻¹ :=
      hsum.comp_injective (add_left_injective (J + 1))
    exact hsum'.tsum_pos (fun i => by positivity) 0 (by positivity)
  refine ⟨(b : ℝ) ^ N * τ, by positivity, ?_, ?_⟩
  · have h := tail_le hb ht J
    rw [htN, pow_succ, mul_inv] at h
    have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hN0 : (b : ℝ) ^ N * ((b : ℝ) ^ N)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hbinv : 2 * (b : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hbpos]; exact h2
    calc (b : ℝ) ^ N * τ ≤ (b : ℝ) ^ N * (2 * (((b : ℝ) ^ N)⁻¹ * (b : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * (b : ℝ)⁻¹ * ((b : ℝ) ^ N * ((b : ℝ) ^ N)⁻¹) := by ring
      _ ≤ 1 := by rw [hN0, mul_one]; exact hbinv
  · rw [sparseValue, ← hsplit, mul_add]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hle : t j ≤ N := by
      have := ht.monotone (show j ≤ J by omega)
      have := ht (show J < J + 1 by omega)
      omega
    rw [pow_sub₀ _ (by positivity) hle]

end Sparse

/-! ## The larger root -/

section LargerRoot

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t)

include hb ht in
/-- **The main inequality.**  Let `A y² + B y + C = 0` with `A > 0` and `δ = 2Ay + B > 0`, where
`y = ∑_j b^{-t_j}`.  If `N = t_{J+1} − 1` is large (`b^N δ > 2A`, `L ≤ N` with `4Aδ ≤ b^L`), then
`(b − 1)(N − L) ≤ (s_b(2A)(J + 1) + δ)²`. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem main_ineq (A : ℕ) (hA : 0 < A) (B C : ℤ)
    (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0)
    (hδ : 0 < 2 * A * sparseValue b t + B) (J L : ℕ)
    (hL : 4 * A * (2 * A * sparseValue b t + B) ≤ (b : ℝ) ^ L) (hLN : L ≤ t (J + 1) - 1)
    (hbig : 2 * A < (b : ℝ) ^ (t (J + 1) - 1) * (2 * A * sparseValue b t + B)) :
    ((b : ℝ) - 1) * ((t (J + 1) - 1 - L : ℕ) : ℝ)
      ≤ ((ds b (2 * A) : ℝ) * (J + 1) + (2 * A * sparseValue b t + B)) ^ 2 := by
  set y := sparseValue b t with hy
  set δ := 2 * A * y + B with hδdef
  set N := t (J + 1) - 1 with hN
  obtain ⟨ε, hε0, hε1, hY⟩ := truncation hb ht J
  rw [← hN] at hY
  set Y : ℕ := ∑ j ∈ Finset.range (J + 1), b ^ (N - t j) with hYdef
  set Bn : ℝ := (b : ℝ) ^ N with hBn
  have hb1 := one_lt_b hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hBnpos : 0 < Bn := by positivity
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  -- the integers `Z = 2AY + B b^N`, `D = B² − 4AC`, `R = D b^{2N} − Z²`
  set Z : ℤ := 2 * A * Y + B * b ^ N with hZdef
  have hZr : (Z : ℝ) = Bn * δ - 2 * A * ε := by
    simp only [hZdef, hδdef, hBn]; push_cast
    linear_combination (-2 * (A : ℝ)) * hY
  set D : ℤ := B ^ 2 - 4 * A * C with hDdef
  have hDr : (D : ℝ) = δ ^ 2 := by
    simp only [hDdef, hδdef]; push_cast
    linear_combination (-4 * (A : ℝ)) * hpoly
  set R : ℤ := D * b ^ (2 * N) - Z ^ 2 with hRdef
  have hRr : (R : ℝ) = 4 * A * ε * (Bn * δ - A * ε) := by
    have : (R : ℝ) = (D : ℝ) * Bn ^ 2 - (Z : ℝ) ^ 2 := by
      simp only [hRdef, hBn]; push_cast; ring
    rw [this, hDr, hZr]; ring
  have hZpos : (0 : ℝ) < Z := by rw [hZr]; nlinarith
  have hRpos : (0 : ℝ) < R := by
    rw [hRr]
    have : 0 < Bn * δ - A * ε := by nlinarith
    positivity
  have hRle : (R : ℝ) ≤ (b : ℝ) ^ (N + L) := by
    rw [hRr, pow_add, ← hBn]
    have h1 : Bn * δ - A * ε ≤ Bn * δ := by nlinarith
    have h2 : 0 ≤ Bn * δ - A * ε := by nlinarith
    calc 4 * A * ε * (Bn * δ - A * ε) ≤ 4 * A * 1 * (Bn * δ) := by gcongr
      _ = Bn * (4 * A * δ) := by ring
      _ ≤ Bn * (b : ℝ) ^ L := by gcongr
  have hDpos : (0 : ℝ) < D := by rw [hDr]; positivity
  -- pass to natural numbers
  have hZ0 : 0 ≤ Z := by exact_mod_cast hZpos.le
  have hR0 : 0 < R := by exact_mod_cast hRpos
  have hD0 : 0 < D := by exact_mod_cast hDpos
  set Zn := Z.toNat
  set Rn := R.toNat
  set Dn := D.toNat
  have hZn : (Zn : ℤ) = Z := Int.toNat_of_nonneg hZ0
  have hRn : (Rn : ℤ) = R := Int.toNat_of_nonneg hR0.le
  have hDn : (Dn : ℤ) = D := Int.toNat_of_nonneg hD0.le
  have hX : Zn ^ 2 + Rn = Dn * b ^ ((N + L) + (N - L)) := by
    have he : (N + L) + (N - L) = 2 * N := by omega
    rw [he]
    have : ((Zn ^ 2 + Rn : ℕ) : ℤ) = ((Dn * b ^ (2 * N) : ℕ) : ℤ) := by
      push_cast; rw [hZn, hRn, hDn, hRdef]; ring
    exact_mod_cast this
  have hRnle : Rn ≤ b ^ (N + L) := by
    have : (Rn : ℝ) ≤ ((b ^ (N + L) : ℕ) : ℝ) := by
      have : (Rn : ℝ) = (R : ℝ) := by exact_mod_cast hRn
      rw [this]; push_cast; exact hRle
    exact_mod_cast this
  have hlower := ds_borrow_block hb (by omega : 1 ≤ Dn) (by omega : 0 < Rn) hRnle hX
  -- the upper bound on `s_b(Z)`
  have hYds : ds b Y ≤ J + 1 := by
    refine (ds_sum_le hb _ _).trans ?_
    simp [ds_pow hb]
  have hmod : Zn % b ^ N = (2 * A * Y) % b ^ N := by
    have : ((Zn % b ^ N : ℕ) : ℤ) = (((2 * A * Y) % b ^ N : ℕ) : ℤ) := by
      push_cast
      rw [hZn, hZdef, Int.add_mul_emod_self_right]
    exact_mod_cast this
  have hlow : ds b (Zn % b ^ N) ≤ ds b (2 * A) * (J + 1) := by
    rw [hmod]
    calc ds b ((2 * A * Y) % b ^ N) ≤ ds b (2 * A * Y) := by
          rw [ds_split hb N (2 * A * Y)]; omega
      _ ≤ ds b (2 * A) * ds b Y := ds_mul_le hb _ _
      _ ≤ ds b (2 * A) * (J + 1) := Nat.mul_le_mul_left _ hYds
  have hhigh : (ds b (Zn / b ^ N) : ℝ) ≤ δ := by
    have h1 : (ds b (Zn / b ^ N) : ℝ) ≤ ((Zn / b ^ N : ℕ) : ℝ) := by
      exact_mod_cast ds_le_self hb _
    have h2 : ((Zn / b ^ N : ℕ) : ℝ) ≤ (Zn : ℝ) / ((b ^ N : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : (Zn : ℝ) = (Z : ℝ) := by exact_mod_cast hZn
    have h4 : (Zn : ℝ) / ((b ^ N : ℕ) : ℝ) ≤ δ := by
      rw [div_le_iff₀ (by push_cast; positivity), h3, hZr]
      push_cast
      nlinarith
    linarith
  have hZds : (ds b Zn : ℝ) ≤ (ds b (2 * A) : ℝ) * (J + 1) + δ := by
    have h := ds_split hb N Zn
    have h' : (ds b Zn : ℝ) = ds b (Zn % b ^ N) + ds b (Zn / b ^ N) := by exact_mod_cast h
    have hlow' : (ds b (Zn % b ^ N) : ℝ) ≤ (ds b (2 * A) : ℝ) * (J + 1) := by
      exact_mod_cast hlow
    linarith
  have hsq : ds b (Zn ^ 2) ≤ ds b Zn ^ 2 := by
    rw [pow_two, pow_two]; exact ds_mul_le hb _ _
  have hfinal : (((b - 1) * (N - L) : ℕ) : ℝ) ≤ (ds b Zn : ℝ) ^ 2 := by
    exact_mod_cast hlower.trans hsq
  have hcast : (((b - 1) * (N - L) : ℕ) : ℝ) = ((b : ℝ) - 1) * ((N - L : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  rw [hcast] at hfinal
  have hds0 : (0 : ℝ) ≤ ds b Zn := Nat.cast_nonneg _
  calc ((b : ℝ) - 1) * ((N - L : ℕ) : ℝ) ≤ (ds b Zn : ℝ) ^ 2 := hfinal
    _ ≤ ((ds b (2 * A) : ℝ) * (J + 1) + δ) ^ 2 := by gcongr

include hb ht in
/-- **The `√N` bound for the larger root.**  If `y = ∑_j b^{-t_j}` satisfies `A y² + B y + C = 0`
with `A > 0` and `2Ay + B > 0`, then `t_j ≤ K j²` for all `j ≥ 1`, i.e. `y` has `≫ √N` digits `1`
among its first `N`. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ones_bound_of_larger_root (A : ℕ) (hA : 0 < A) (B C : ℤ)
    (hpoly : (A : ℝ) * sparseValue b t ^ 2 + B * sparseValue b t + C = 0)
    (hδ : 0 < 2 * A * sparseValue b t + B) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, 1 ≤ j → (t j : ℝ) ≤ K * (j : ℝ) ^ 2 := by
  set δ := 2 * A * sparseValue b t + B with hδdef
  have hb1 := one_lt_b hb
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (4 * A * δ) hb1
  obtain ⟨N₁, hN₁⟩ := pow_unbounded_of_one_lt (2 * A / δ) hb1
  set a : ℝ := (ds b (2 * A) : ℝ)
  set T₀ : ℝ := ∑ i ∈ Finset.range (N₁ + L + 1), (t i : ℝ)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hT₀ : 0 ≤ T₀ := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  refine ⟨1 + L + (a + δ) ^ 2 + T₀, by positivity, fun j hj => ?_⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  by_cases hsmall : j ≤ N₁ + L
  · have : (t j : ℝ) ≤ T₀ :=
      Finset.single_le_sum (f := fun i => (t i : ℝ)) (fun i _ => Nat.cast_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
    set N := t (J + 1) - 1 with hN
    have htJ : J + 1 ≤ t (J + 1) := ht.le_apply
    have hNJ : N₁ + L ≤ N := by omega
    have hLN : L ≤ N := by omega
    have hbig : 2 * A < (b : ℝ) ^ N * δ := by
      have h1 : (b : ℝ) ^ N₁ ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1.le (by omega)
      have h2 : 2 * A / δ < (b : ℝ) ^ N := lt_of_lt_of_le hN₁ h1
      rwa [div_lt_iff₀ hδ] at h2
    have key := main_ineq hb ht A hA B C hpoly hδ J L hL.le hLN hbig
    have hcast : ((N - L : ℕ) : ℝ) = (N : ℝ) - L := by rw [Nat.cast_sub hLN]
    have htN : (t (J + 1) : ℝ) = (N : ℝ) + 1 := by
      have : t (J + 1) = N + 1 := by omega
      rw [this]; push_cast; ring
    rw [hcast] at key
    have hb2 : (1 : ℝ) ≤ (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have hNL : (0 : ℝ) ≤ (N : ℝ) - L := by
      have : (L : ℝ) ≤ N := by exact_mod_cast hLN
      linarith
    have h3 : (N : ℝ) - L ≤ (a * ((J : ℝ) + 1) + δ) ^ 2 := by
      nlinarith
    push_cast at hj1 hj2 ⊢
    rw [htN]
    have h4 : (a * ((J : ℝ) + 1) + δ) ^ 2 ≤ (a + δ) ^ 2 * ((J : ℝ) + 1) ^ 2 := by
      have : a * ((J : ℝ) + 1) + δ ≤ (a + δ) * ((J : ℝ) + 1) := by nlinarith
      have h0 : 0 ≤ a * ((J : ℝ) + 1) + δ := by positivity
      calc (a * ((J : ℝ) + 1) + δ) ^ 2 ≤ ((a + δ) * ((J : ℝ) + 1)) ^ 2 := by gcongr
        _ = (a + δ) ^ 2 * ((J : ℝ) + 1) ^ 2 := by ring
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith

include hb ht in
lemma sparseValue_pos : 0 < sparseValue b t :=
  (summable_sparse hb ht).tsum_pos (fun i => by positivity) 0 (by positivity)

include hb ht in
/-- **`y² ∈ ℚ`.**  If `y = ∑_j b^{-t_j}` has rational square, then `t_j ≤ K j²` for `j ≥ 1`.  For
`b = 2` and `y = √2`-type numbers this is the `≫ √N` count of ones of [BBCP04, Thm. 5.2]. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ones_bound_of_sq_rat (hsq : ∃ r : ℚ, sparseValue b t ^ 2 = r) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, 1 ≤ j → (t j : ℝ) ≤ K * (j : ℝ) ^ 2 := by
  obtain ⟨r, hr⟩ := hsq
  have hy := sparseValue_pos hb ht
  refine ones_bound_of_larger_root hb ht r.den r.den_pos 0 (-r.num) ?_ ?_
  · rw [hr]
    have : (r : ℝ) = r.num / r.den := Rat.cast_def r
    rw [this]
    have hden : (r.den : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have : (0 : ℝ) < r.den := by positivity
    push_cast
    nlinarith

/-- Evaluation of a monic quadratic. -/
private lemma aeval_quadratic {p : Polynomial ℚ} (hmon : p.Monic) (h2 : p.natDegree = 2) (z : ℝ) :
    Polynomial.aeval z p = z ^ 2 + (p.coeff 1 : ℝ) * z + (p.coeff 0 : ℝ) := by
  have hc2 : p.coeff 2 = 1 := by rw [← h2]; exact hmon.coeff_natDegree
  rw [Polynomial.aeval_eq_sum_range, h2]
  simp [Finset.sum_range_succ, hc2, Algebra.smul_def]
  ring

include hb ht in
/-- **The larger root.**  If `y = ∑_j b^{-t_j}` is algebraic of degree `2` and is the larger of the
two (real) roots of its minimal polynomial, then `t_j ≤ K j²` for `j ≥ 1`. -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem ones_bound_of_minpoly_larger (halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : (minpoly ℚ (sparseValue b t)).natDegree = 2)
    (hlarger : ∀ z : ℝ, Polynomial.aeval z (minpoly ℚ (sparseValue b t)) = 0 →
      z ≤ sparseValue b t) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, 1 ≤ j → (t j : ℝ) ≤ K * (j : ℝ) ^ 2 := by
  set y := sparseValue b t with hy
  set p := minpoly ℚ y with hp
  have hmon : p.Monic := minpoly.monic halg.isIntegral
  set c1 := p.coeff 1
  set c0 := p.coeff 0
  have hroot : y ^ 2 + (c1 : ℝ) * y + c0 = 0 := by
    rw [← aeval_quadratic hmon hdeg y]; exact minpoly.aeval ℚ y
  have hirr : Irrational y := irrational_of_one_lt_minpoly_natDegree (by rw [← hp, hdeg]; omega)
  -- the conjugate `-c1 - y` is the other root, and it is smaller
  have hconj : -(c1 : ℝ) - y < y := by
    have hz := hlarger (-(c1 : ℝ) - y) (by rw [aeval_quadratic hmon hdeg]; linear_combination hroot)
    rcases hz.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hirr
      refine ⟨-c1 / 2, ?_⟩
      push_cast
      linarith
  have hd1 : (0 : ℝ) < c1.den := by positivity
  have hd0 : (0 : ℝ) < c0.den := by positivity
  have hc1 : (c1 : ℝ) = c1.num / c1.den := Rat.cast_def c1
  have hc0 : (c0 : ℝ) = c0.num / c0.den := Rat.cast_def c0
  refine ones_bound_of_larger_root hb ht (c1.den * c0.den) (by positivity) (c1.num * c0.den)
    (c0.num * c1.den) ?_ ?_
  · have : ((c1.den * c0.den : ℕ) : ℝ) * y ^ 2 + ((c1.num * c0.den : ℤ) : ℝ) * y
        + ((c0.num * c1.den : ℤ) : ℝ)
        = ((c1.den * c0.den : ℕ) : ℝ) * (y ^ 2 + (c1 : ℝ) * y + c0) := by
      rw [hc1, hc0]; push_cast; field_simp
    rw [this, hroot, mul_zero]
  · have : 2 * ((c1.den * c0.den : ℕ) : ℝ) * y + ((c1.num * c0.den : ℤ) : ℝ)
        = ((c1.den * c0.den : ℕ) : ℝ) * (2 * y + c1) := by
      rw [hc1]; push_cast; field_simp
    rw [this]
    have : (0 : ℝ) < ((c1.den * c0.den : ℕ) : ℝ) := by positivity
    have : 0 < 2 * y + (c1 : ℝ) := by linarith
    positivity

/-! ## Discharging the `D = 2` slice of `BB47.bbcp_base_b` -/

include hb ht in
/-- **[BBCP04, Thm. 7.1] for `y² ∈ ℚ`**, in exactly the form of the cited axiom
`BB47.bbcp_base_b`, proved (standard axioms only). -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem bbcp_base_b_sq (_halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : 1 < (minpoly ℚ (sparseValue b t)).natDegree)
    (hsq : ∃ r : ℚ, sparseValue b t ^ 2 = r) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (t j : ℝ) ≤ C * (j : ℝ) ^ (minpoly ℚ (sparseValue b t)).natDegree := by
  obtain ⟨r, hr⟩ := hsq
  have h2 : (minpoly ℚ (sparseValue b t)).natDegree = 2 := by
    have hne : (Polynomial.X ^ 2 - Polynomial.C r : Polynomial ℚ) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
    have hle := minpoly.degree_le_of_ne_zero ℚ (sparseValue b t) hne (by simp [hr])
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)] at hle
    have := Polynomial.natDegree_le_of_degree_le hle
    omega
  rw [h2]
  exact ones_bound_of_sq_rat hb ht ⟨r, hr⟩

include hb ht in
/-- **[BBCP04, Thm. 7.1] for the larger root of a quadratic**, in exactly the form of the cited
axiom `BB47.bbcp_base_b`, proved (standard axioms only). -/
@[category research solved, AMS 11, ref "BBCP04", group "bugeaud_10_47"]
theorem bbcp_base_b_larger (halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : (minpoly ℚ (sparseValue b t)).natDegree = 2)
    (hlarger : ∀ z : ℝ, Polynomial.aeval z (minpoly ℚ (sparseValue b t)) = 0 →
      z ≤ sparseValue b t) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (t j : ℝ) ≤ C * (j : ℝ) ^ (minpoly ℚ (sparseValue b t)).natDegree := by
  rw [hdeg]
  exact ones_bound_of_minpoly_larger hb ht halg hdeg hlarger

end LargerRoot

end BB47.Popcount
