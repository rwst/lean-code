/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.PrimePrefix
import CITED.NarrowPrimeAP
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Round

/-!
# Arbitrarily long prime prefixes ([Oda26] App. E.1, Theorem 68)

For every `L ≥ 3` and `T` there are `t ≥ T` and a rational `ξ > 0` with `⌊ξ((6t+3)/(6t+1))ʲ⌋`
prime for `0 ≤ j < L`, the first term exceeding `6t + 3`.

The proof combines Lemma 67 (`Oda.transplant`) with two cited inputs (`CITED/NarrowPrimeAP.lean`):
the prime number theorem (to make the primes in `(Y/2, Y]` dense enough) and Shao's narrow
progressions in dense sets of primes.  `#print axioms` shows both.

* `Oda.theta_sub_le` — `θ(Y) − θ(Y/2) ≤ #{primes in (Y/2, Y]}·log Y`.
* `Oda.long_prime_prefix` — **[Oda26] Theorem 68**.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

open Filter Topology Finset

theorem theta_sub_le {Y : ℝ} (hY : 2 ≤ Y) :
    Chebyshev.theta Y - Chebyshev.theta (Y / 2) ≤
      ((Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊).filter Nat.Prime).card * Real.log Y := by
  have hmn : ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta Y = Chebyshev.theta (Y / 2) +
      ∑ p ∈ (Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊).filter Nat.Prime, Real.log p := by
    unfold Chebyshev.theta
    rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hmn, Finset.filter_union,
      Finset.sum_union]
    refine Finset.disjoint_left.2 fun x h1 h2 => ?_
    simp only [Finset.mem_filter, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, add_sub_cancel_left]
  have h := Finset.sum_le_card_nsmul ((Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊).filter Nat.Prime)
    (fun p : ℕ => Real.log p) (Real.log Y) (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      have hpY : (p : ℝ) ≤ Y := le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))
      exact Real.log_le_log hp0 hpY)
  simpa using h

theorem eventually_theta_gap :
    ∀ᶠ Y : ℝ in atTop, Y / 3 ≤ Chebyshev.theta Y - Chebyshev.theta (Y / 2) := by
  have h1 := PNT.theta_div_tendsto
  have h2 := h1.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have e1 := h1.eventually (Ioi_mem_nhds (show (0.9 : ℝ) < 1 by norm_num))
  have e2 := h2.eventually (Iio_mem_nhds (show (1 : ℝ) < 1.1 by norm_num))
  filter_upwards [e1, e2, eventually_gt_atTop 0] with Y h1 h2 hY
  simp only [Function.comp, id] at h1 h2
  rw [lt_div_iff₀ hY] at h1
  rw [div_lt_iff₀ (by linarith)] at h2
  linarith

theorem eventually_log_pow_le {K : ℝ} (hK : 0 < K) (n : ℕ) :
    ∀ᶠ Y : ℝ in atTop, K * Real.log Y ^ n ≤ Y := by
  have := (Real.isLittleO_pow_log_id_atTop (n := n)).bound (show 0 < 1 / K by positivity)
  filter_upwards [this, eventually_gt_atTop 0] with Y h hY
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hY] at h
  have h' := le_trans (le_abs_self _) h
  calc K * Real.log Y ^ n ≤ K * (1 / K * Y) := mul_le_mul_of_nonneg_left h' hK.le
    _ = Y := by field_simp

/-- A narrow prime progression of length `L` with `P > 48L²D²` and `P > M·D` (from the cited
prime number theorem and Shao's theorem). -/
theorem exists_narrow_prime_ap (L : ℕ) (hL : 3 ≤ L) (M : ℝ) (hM : 0 ≤ M) :
    ∃ P D : ℕ, 0 < D ∧ (∀ j < L, (P + j * D).Prime) ∧ 3 < P ∧ 48 * L ^ 2 * D ^ 2 < P ∧
      M * D < P := by
  obtain ⟨C, Y₀, hShao⟩ := Shao.narrow_ap L hL (1 / 3) (by norm_num)
  set e := (L - 1) * 2 ^ (L - 2)
  obtain ⟨C', hC'1, hCC'⟩ : ∃ C' : ℝ, 1 ≤ C' ∧ C ≤ C' := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨K, hK, hK1, hK2⟩ : ∃ K : ℝ, 0 < K ∧ 2 * (48 * L ^ 2 * C' ^ 2) ≤ K ∧ 2 * (M * C') ≤ K :=
    ⟨2 * (48 * L ^ 2 * C' ^ 2 + M * C') + 1, by positivity,
      by nlinarith [mul_nonneg hM (by linarith : (0 : ℝ) ≤ C')],
      by nlinarith [show (0 : ℝ) ≤ 48 * L ^ 2 * C' ^ 2 by positivity]⟩
  obtain ⟨Y, hY1, hY2, hY3, hY4, hY5⟩ := (eventually_theta_gap.and
    ((eventually_log_pow_le hK (2 * e)).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
    ((eventually_ge_atTop Y₀).and (eventually_ge_atTop 8))))).exists
  set A := (Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊).filter Nat.Prime with hAdef
  have hA : ∀ p ∈ A, p.Prime ∧ (p : ℝ) ≤ Y := fun p hp => by
    simp only [hAdef, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by linarith))⟩
  have hlogpos : 0 < Real.log Y := by linarith
  have hcard : 1 / 3 * Y / Real.log Y ≤ A.card := by
    rw [div_le_iff₀ hlogpos]
    have := theta_sub_le (Y := Y) (by linarith)
    linarith
  obtain ⟨P, D, hD, hDle, hAP⟩ := hShao Y hY4 A hA hcard
  have hpr : ∀ j < L, (P + j * D).Prime := fun j hj => (hA _ (hAP j hj)).1
  have hP2 : Y / 2 < P := by
    have := hAP 0 (by omega)
    simp only [zero_mul, add_zero, hAdef, Finset.mem_filter, Finset.mem_Ioc] at this
    exact Nat.lt_of_floor_lt this.1.1
  obtain ⟨ℓ, hℓ1, hℓ2, hDr⟩ : ∃ ℓ : ℝ, 1 ≤ ℓ ∧ K * ℓ ^ 2 ≤ Y ∧ (D : ℝ) ≤ C' * ℓ := by
    refine ⟨Real.log Y ^ e, one_le_pow₀ hY3, by rw [← pow_mul, mul_comm e 2]; exact hY2,
      le_trans hDle (mul_le_mul_of_nonneg_right hCC' (by positivity))⟩
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  refine ⟨P, D, hD, hpr, ?_, ?_, ?_⟩
  · have : (3 : ℝ) < P := by linarith
    exact_mod_cast this
  · have h1 : (D : ℝ) ^ 2 ≤ C' ^ 2 * ℓ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hD0.le hDr 2
    have h2 : (48 : ℝ) * L ^ 2 * D ^ 2 ≤ 48 * L ^ 2 * C' ^ 2 * ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 48 * L ^ 2)
      linarith
    have h3 : (48 : ℝ) * L ^ 2 * C' ^ 2 * ℓ ^ 2 ≤ K / 2 * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have : (48 : ℝ) * ((L : ℝ) ^ 2 * (D : ℝ) ^ 2) < P := by nlinarith
    have : ((48 * L ^ 2 * D ^ 2 : ℕ) : ℝ) < P := by push_cast; linarith
    exact_mod_cast this
  · have h1 : M * D ≤ M * C' * ℓ ^ 2 := by
      have : (D : ℝ) ≤ C' * ℓ ^ 2 := le_trans hDr (mul_le_mul_of_nonneg_left hℓℓ (by linarith))
      have := mul_le_mul_of_nonneg_left this hM
      linarith
    have h2 : M * C' * ℓ ^ 2 ≤ K / 2 * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith

/-- The denominator `b = 6t + 1` nearest to `2P/D`, with `t ≥ T` when `P > (6T+7)D`. -/
theorem exists_denominator {P D T : ℕ} (hD : 0 < D) (hTD : ((6 * T + 7 : ℕ) : ℝ) * D < P) :
    ∃ t : ℕ, T ≤ t ∧ |((6 * t + 1 : ℕ) : ℝ) - 2 * P / D| ≤ 3 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set x : ℝ := (2 * P / D - 1) / 6 with hx
  have hxT : (2 * T + 2 : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ (by norm_num), le_sub_iff_add_le, le_div_iff₀ hD0]
    push_cast at hTD
    nlinarith
  have hround := abs_le.1 (abs_sub_round x)
  have hm0 : 0 ≤ round x := by
    have : (0 : ℝ) < round x := by linarith
    exact_mod_cast this.le
  refine ⟨(round x).toNat, ?_, ?_⟩
  · have htm : ((round x).toNat : ℝ) = round x := by exact_mod_cast Int.toNat_of_nonneg hm0
    have : (T : ℝ) ≤ (round x).toNat := by rw [htm]; linarith
    exact_mod_cast this
  · have htm : ((round x).toNat : ℝ) = round x := by exact_mod_cast Int.toNat_of_nonneg hm0
    have e : (((6 * (round x).toNat + 1 : ℕ)) : ℝ) - 2 * P / D = -6 * (x - round x) := by
      push_cast; rw [htm, hx]; ring
    rw [e, abs_le]
    constructor <;> linarith

/-- **[Oda26] Theorem 68 (arbitrarily long prime prefixes).**  For every `L ≥ 3` and `T` there are
`t ≥ T` and a rational `ξ > 0` such that `⌊ξ((6t+3)/(6t+1))ʲ⌋` is prime for `0 ≤ j < L` and the
first term exceeds `6t + 3`.  (Uses the cited `PNT.theta_div_tendsto` and `Shao.narrow_ap`.) -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_prime_prefix"]
theorem long_prime_prefix (L : ℕ) (hL : 3 ≤ L) (T : ℕ) :
    ∃ t, T ≤ t ∧ ∃ ξ : ℚ, 0 < ξ ∧
      (∀ j < L, ∃ p : ℕ, p.Prime ∧ Qf (6 * t + 3) (6 * t + 1) (ξ : ℝ) 0 j = p) ∧
      ((6 * t + 3 : ℕ) : ℤ) < Qf (6 * t + 3) (6 * t + 1) (ξ : ℝ) 0 0 := by
  obtain ⟨P, D, hD, hpr, h3, hP48, hTD⟩ :=
    exists_narrow_prime_ap L hL ((6 * T + 7 : ℕ) : ℝ) (by positivity)
  obtain ⟨t, hTt, hbc⟩ := exists_denominator hD hTD
  obtain ⟨-, hbP, hfl⟩ := transplant hL hD hpr h3 hP48 (b := 6 * t + 1) (by omega) hbc
  have e3 : 6 * t + 3 = 6 * t + 1 + 2 := by ring
  refine ⟨t, hTt, (P : ℚ) + 1 / 2, by positivity, fun j hj => ⟨P + j * D, hpr j hj, ?_⟩, ?_⟩
  · rw [e3]; push_cast; exact hfl j hj
  · have := hfl 0 (by omega)
    rw [e3]
    push_cast at this ⊢
    rw [this]
    simp only [zero_mul, add_zero]
    exact_mod_cast hbP

end Oda
