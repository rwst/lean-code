/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace RT

open Classical

/-- The irrational constant `log 2 / log 3`. -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
noncomputable def ξ : ℝ := Real.log 2 / Real.log 3

@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
lemma xi_pos : 0 < ξ := div_pos log2_pos log3_pos

/-- `ξ = log 2 / log 3 > 1/2` since `4 > 3`. -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
lemma half_lt_xi : (1 : ℝ) / 2 < ξ := by
  rw [ξ, lt_div_iff₀ log3_pos]
  have h4 : Real.log 3 < 2 * Real.log 2 := by
    have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; push_cast; ring
    linarith [h4']
  linarith

@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
lemma xi_lt_one : ξ < 1 := by
  rw [ξ, div_lt_one log3_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Auxiliary arithmetic core of the irrationality proof: if `log 2 * b = a * log 3` for
    positive integer `b`, this leads to a contradiction (`2^b = 3^a` cannot hold in `ℕ`). -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma irrational_xi_aux (a b : ℤ) (hb : 0 < b)
    (hcross : Real.log 2 * (b : ℝ) = (a : ℝ) * Real.log 3) : False := by
  have hapos : 0 < a := by
    by_contra ha
    push Not at ha
    have h1 : (a : ℝ) * Real.log 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha) log3_pos.le
    have h2 : 0 < Real.log 2 * (b : ℝ) := mul_pos log2_pos (by exact_mod_cast hb)
    linarith
  set b' := b.toNat with hb'_def
  set a' := a.toNat with ha'_def
  have hbb' : (b' : ℤ) = b := Int.toNat_of_nonneg hb.le
  have haa' : (a' : ℤ) = a := Int.toNat_of_nonneg hapos.le
  have hb'pos : 0 < b' := by omega
  have heqR : Real.log ((2 : ℝ) ^ b') = Real.log ((3 : ℝ) ^ a') := by
    rw [Real.log_pow, Real.log_pow]
    have e1 : (b' : ℝ) = (b : ℝ) := by exact_mod_cast hbb'
    have e2 : (a' : ℝ) = (a : ℝ) := by exact_mod_cast haa'
    rw [e1, e2]; linarith
  have heqP : (2 : ℝ) ^ b' = (3 : ℝ) ^ a' :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) heqR
  have heqN : (2 : ℕ) ^ b' = 3 ^ a' := by exact_mod_cast heqP
  have heven : (2 : ℕ) ^ b' % 2 = 0 := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hb'pos.ne'
    rw [hc, pow_succ]; omega
  have hodd : (3 : ℕ) ^ a' % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [heqN] at heven
  omega

/-- Auxiliary Lemma 1: `ξ` is irrational. -/
@[category research solved, AMS 11, ref "Roz25", group "roz_approximation"]
lemma irrational_xi : Irrational ξ := by
  rw [ξ, irrational_iff_ne_rational]
  intro a b hb heq
  have hcross : Real.log 2 * (b : ℝ) = (a : ℝ) * Real.log 3 :=
    (div_eq_div_iff log3_pos.ne' (Int.cast_ne_zero.mpr hb)).mp heq
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · exact irrational_xi_aux (-a) (-b) (by omega) (by push_cast; linarith)
  · exact irrational_xi_aux a b hpos hcross

/-! ### A density lemma via Dirichlet's approximation theorem

We show that for every `ε ∈ (0, 1)` there are infinitely many pairs of positive naturals
`(a, b)` with `1 - ε < 3^a / 2^b < 1`. Equivalently (dividing by `log 3 > 0`), writing
`δ = -log(1 - ε) / log 3 > 0`, there are infinitely many `b` with `0 < b·ξ - a < δ` for a
suitable integer `a`. -/

@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma fract_ne_zero_of_pos {k : ℕ} (hk : 0 < k) : Int.fract ((k : ℝ) * ξ) ≠ 0 := by
  intro h0
  have hirr : Irrational ((k : ℝ) * ξ) := irrational_xi.natCast_mul hk.ne'
  apply hirr
  refine ⟨(⌊(k : ℝ) * ξ⌋ : ℚ), ?_⟩
  have hfl := Int.floor_add_fract ((k : ℝ) * ξ)
  rw [h0, add_zero] at hfl
  push_cast
  linarith

/-- The distance from `x` to the nearest integer is a lower bound for `|x - j|`, for any
    integer `j`. -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma abs_sub_int_ge_dist (x : ℝ) (j : ℤ) :
    Int.fract x ⊓ (1 - Int.fract x) ≤ |x - j| := by
  have hfl : (⌊x⌋ : ℝ) = x - Int.fract x := by
    have := Int.floor_add_fract x; linarith
  by_cases hj : j ≤ ⌊x⌋
  · have hjx : (j : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hj
    have h2 : Int.fract x ≤ x - j := by linarith
    have h3 : 0 ≤ x - j := le_trans (Int.fract_nonneg x) h2
    rw [abs_of_nonneg h3]
    exact le_trans (min_le_left _ _) h2
  · push Not at hj
    have hj1 : (⌊x⌋ : ℤ) + 1 ≤ j := hj
    have hjx : ((⌊x⌋ : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hj1
    have h2 : 1 - Int.fract x ≤ j - x := by linarith
    have h3 : x - j ≤ 0 := by linarith [Int.fract_lt_one x]
    rw [abs_of_nonpos h3]
    linarith [min_le_right (Int.fract x) (1 - Int.fract x)]

/-- For any finite range `[1, N]`, every multiple `k·ξ` (`1 ≤ k ≤ N`) stays a definite
    positive distance away from the nearest integer. -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma exists_min_dist (N : ℕ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ k ∈ Finset.Icc 1 N,
      μ ≤ Int.fract ((k : ℝ) * ξ) ∧ μ ≤ 1 - Int.fract ((k : ℝ) * ξ) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · exact ⟨1, one_pos, by simp [hN0]⟩
  · set f : ℕ → ℝ := fun k => Int.fract ((k : ℝ) * ξ) ⊓ (1 - Int.fract ((k : ℝ) * ξ)) with hf_def
    have hne : (Finset.Icc 1 N).Nonempty := ⟨1, by simp; omega⟩
    refine ⟨(Finset.Icc 1 N).inf' hne f, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hkpos : 0 < k := by omega
      have hne0 := fract_ne_zero_of_pos hkpos
      have h1 : 0 < Int.fract ((k : ℝ) * ξ) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne0)
      have h2 : Int.fract ((k : ℝ) * ξ) < 1 := Int.fract_lt_one _
      simp only [hf_def]
      exact lt_min h1 (by linarith)
    · intro k hk
      have hle := Finset.inf'_le f hk
      simp only [hf_def] at hle
      exact ⟨le_trans hle (min_le_left _ _), le_trans hle (min_le_right _ _)⟩

/-- Core density step: for every bound `N` and target precision `δ > 0`, there is `b > N`
    and an integer `z` with `0 ≤ b·ξ - z < δ`. -/
@[category API, AMS 11, ref "Roz25", group "roz_approximation"]
private lemma exists_close_multiple (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (b : ℕ) (z : ℤ), N < b ∧ 0 < z ∧ (b : ℝ) * ξ - z = Int.fract ((b : ℝ) * ξ) ∧
      0 < Int.fract ((b : ℝ) * ξ) ∧ Int.fract ((b : ℝ) * ξ) < δ := by
  obtain ⟨μ, hμpos, hμ⟩ := exists_min_dist N
  set ε := min δ μ with hε_def
  have hεpos : 0 < ε := lt_min hδ hμpos
  obtain ⟨n1, hn1⟩ := exists_nat_gt (1 / ε)
  set n := n1 + 1 with hn_def
  have hnpos : 0 < n := by omega
  have hn_bound : (1 : ℝ) / (n + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : (1 : ℝ) / ε < n := by
      have : (n1 : ℝ) < n := by rw [hn_def]; push_cast; linarith
      linarith
    rw [div_lt_iff₀ hεpos] at h1
    nlinarith
  obtain ⟨j, k, hk0, hkn, hgap⟩ := Real.exists_int_int_abs_mul_sub_le ξ hnpos
  set g := (k : ℝ) * ξ - j with hg_def
  have hgne : g ≠ 0 := by
    intro h0
    have hkne : k ≠ 0 := hk0.ne'
    have heqkj : (k : ℝ) * ξ = (j : ℝ) := by linarith [h0]
    exact (irrational_xi.intCast_mul hkne) ⟨j, by push_cast; linarith [heqkj]⟩
  set k' := k.toNat with hk'_def
  have hkk' : (k' : ℤ) = k := Int.toNat_of_nonneg hk0.le
  have hk'pos : 0 < k' := by omega
  have hgle : |g| ≤ 1 / (n + 1) := hgap
  have hxeq : (k' : ℝ) * ξ = (k : ℝ) * ξ := by
    have hcast : (k' : ℝ) = (k : ℝ) := by exact_mod_cast hkk'
    rw [hcast]
  -- `n + 1 ≥ 2`, hence `1/(n+1) ≤ 1/2`.
  have hn2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ n + 1)
  have hhalf : (1 : ℝ) / (n + 1) ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hn2
    linarith
  -- Step 5: `k'` exceeds `N`.
  have hkN : N < k' := by
    by_contra hle
    push Not at hle
    have hmem : k' ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hk'pos, hle⟩
    obtain ⟨hb1, hb2⟩ := hμ k' hmem
    have hdist := abs_sub_int_ge_dist ((k' : ℝ) * ξ) j
    have hcontra0 : μ ≤ |(k' : ℝ) * ξ - (j : ℝ)| := le_trans (le_min hb1 hb2) hdist
    rw [hxeq, ← hg_def] at hcontra0
    have : μ < μ :=
      lt_of_le_of_lt hcontra0 (lt_of_le_of_lt hgle (lt_of_lt_of_le hn_bound (min_le_right δ μ)))
    exact lt_irrefl _ this
  -- `k'·ξ > 1/2`.
  have hxgt : (1 : ℝ) / 2 < (k : ℝ) * ξ := by
    have hk'ge : (1 : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk'pos
    calc (1 : ℝ) / 2 < ξ := half_lt_xi
      _ = 1 * ξ := (one_mul ξ).symm
      _ ≤ (k' : ℝ) * ξ := mul_le_mul_of_nonneg_right hk'ge xi_pos.le
      _ = (k : ℝ) * ξ := hxeq
  -- Step 6: `j` is (strictly) positive.
  have hj_pos : 0 < j := by
    have hgub : g ≤ 1 / (n + 1) := (abs_le.mp hgle).2
    have hjeq : (j : ℝ) = (k : ℝ) * ξ - g := by rw [hg_def]; ring
    have hjr : (0 : ℝ) < (j : ℝ) := by linarith
    exact_mod_cast hjr
  rcases lt_or_gt_of_ne hgne with hneg | hpos
  · -- g < 0 : set h := -g > 0, multiply by m := ⌊1/h⌋₊ to flip near 1 into near 0.
    set h := -g with hh_def
    have hhpos : 0 < h := by linarith
    have hhle : h ≤ 1 / (n + 1) := by
      have := abs_le.mp hgle; linarith [this.1]
    set m := ⌊(1 : ℝ) / h⌋₊ with hm_def
    have hm_ge : ((n : ℝ) + 1) ≤ 1 / h := by
      rw [le_div_iff₀ hhpos]
      calc ((n : ℝ) + 1) * h ≤ ((n : ℝ) + 1) * (1 / (n + 1)) :=
            mul_le_mul_of_nonneg_left hhle (by positivity)
        _ = 1 := by field_simp
    have hmpos : 0 < m := by
      have h1le : (1 : ℝ) ≤ 1 / h := le_trans (by linarith) hm_ge
      have h1m : 1 ≤ m := by
        rw [hm_def]; exact (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast h1le)
      omega
    have hmh_le : (m : ℝ) * h ≤ 1 := by
      have := Nat.floor_le (show (0:ℝ) ≤ 1 / h by positivity)
      rw [← hm_def] at this
      calc (m : ℝ) * h ≤ (1 / h) * h := by
            apply mul_le_mul_of_nonneg_right this hhpos.le
        _ = 1 := by field_simp
    have hhirr : Irrational h := by
      have hgirr : Irrational g := by
        rw [hg_def]
        exact (irrational_xi.intCast_mul hk0.ne').sub_intCast j
      rw [hh_def]; exact hgirr.neg
    have hmh_ne : (m : ℝ) * h ≠ 1 := by
      intro heq1
      have hcomm : h * (m : ℝ) = 1 := by rw [mul_comm]; exact heq1
      have this : h⁻¹ = (m : ℝ) := (eq_inv_of_mul_eq_one_right hcomm).symm
      exact (irrational_inv_iff.mpr hhirr) ⟨(m : ℚ), by push_cast; linarith [this]⟩
    have hmh_lt : (m : ℝ) * h < 1 := lt_of_le_of_ne hmh_le hmh_ne
    have hmh1_gt : (1 : ℝ) < (m + 1) * h := by
      have h2 : (1 : ℝ) / h < (m : ℝ) + 1 := by
        have hlt := Nat.lt_floor_add_one (1 / h : ℝ)
        rwa [← hm_def] at hlt
      calc (1:ℝ) = (1/h) * h := by field_simp
        _ < ((m:ℝ) + 1) * h := by exact mul_lt_mul_of_pos_right h2 hhpos
    have h1mh : 1 - (m : ℝ) * h < h := by nlinarith
    -- `m·j ≥ 2` as integers.
    have hmj_ge2 : (2 : ℤ) ≤ (m : ℤ) * j := by
      rcases lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        have hgeq : g = (k : ℝ) * ξ - 1 := by rw [hg_def, hj1]; push_cast; ring
        have hh_lt : h < 1 / 2 := by
          have hheq : h = 1 - (k : ℝ) * ξ := by rw [hh_def, hgeq]; ring
          linarith
        have hinv_gt2 : (2 : ℝ) < 1 / h := by
          rw [lt_div_iff₀ hhpos]; linarith
        have hm_ge2 : (2 : ℕ) ≤ m := by
          rw [hm_def]
          exact (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hinv_gt2.le)
        calc (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm_ge2
          _ = (m : ℤ) * 1 := (mul_one _).symm
          _ ≤ (m : ℤ) * j := by rw [hj1]
      · have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmpos
        calc (2 : ℤ) ≤ j := hj2
          _ = 1 * j := (one_mul j).symm
          _ ≤ (m : ℤ) * j := mul_le_mul_of_nonneg_right hm1 (by omega)
    have hbxi : ((k' * m : ℕ) : ℝ) * ξ = (m : ℝ) * (j : ℝ) - (m : ℝ) * h := by
      have e1 : ((k' * m : ℕ) : ℝ) = (k' : ℝ) * (m : ℝ) := by push_cast; ring
      have e2 : (k' : ℝ) * (m : ℝ) * ξ = (m : ℝ) * ((k' : ℝ) * ξ) := by ring
      have e3 : (k : ℝ) * ξ = (j : ℝ) - h := by rw [hh_def, hg_def]; ring
      rw [e1, e2, hxeq, e3]; ring
    have hfrac2 : Int.fract (((k' * m : ℕ) : ℝ) * ξ) = 1 - (m : ℝ) * h := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, ?_, (m : ℤ) * j - 1, ?_⟩
      · have : (0 : ℝ) < (m : ℝ) * h := mul_pos (by exact_mod_cast hmpos) hhpos
        linarith
      · rw [hbxi]; push_cast; ring
    refine ⟨k' * m, (m : ℤ) * j - 1, ?_, ?_, ?_, ?_, ?_⟩
    · calc N < k' := hkN
        _ = k' * 1 := (mul_one k').symm
        _ ≤ k' * m := Nat.mul_le_mul_left k' hmpos
    · omega
    · rw [hfrac2, hbxi]; push_cast; ring
    · rw [hfrac2]
      have : (0 : ℝ) < (m : ℝ) * h := mul_pos (by exact_mod_cast hmpos) hhpos
      linarith
    · rw [hfrac2]
      linarith [min_le_left δ μ, min_le_right δ μ]
  · -- g > 0 : b := k', z := j.
    have hg01 : 0 ≤ g ∧ g < 1 := by
      have hgub := (abs_le.mp hgle).2
      exact ⟨hpos.le, by linarith⟩
    have hfrac : Int.fract ((k : ℝ) * ξ) = g := by
      rw [Int.fract_eq_iff]
      exact ⟨hg01.1, hg01.2, j, by rw [hg_def]; ring⟩
    refine ⟨k', j, hkN, hj_pos, ?_, ?_, ?_⟩
    · rw [hxeq, ← hg_def, hfrac]
    · rw [hxeq, hfrac]; exact hpos
    · rw [hxeq, hfrac]
      have hgub := (abs_le.mp hgle).2
      linarith [min_le_left δ μ]

/-- **Auxiliary Lemma 2**: for every `ε ∈ (0, 1)` there are infinitely many pairs of
    positive naturals `(a, b)` with `1 - ε < 3^a / 2^b < 1`. -/
@[category research solved, AMS 11, ref "Roz25", group "roz_approximation"]
lemma exists_infinite_pairs_approx (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
      (1 - ε) < (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 ∧ (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 < 1}.Infinite := by
  set δ' := -Real.log (1 - ε) / Real.log 3 with hδ'_def
  have h1me_pos : 0 < 1 - ε := by linarith
  have hlog1me_neg : Real.log (1 - ε) < 0 := Real.log_neg h1me_pos (by linarith)
  have hδ'pos : 0 < δ' := by
    rw [hδ'_def]; exact div_pos (by linarith) log3_pos
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set S := {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧
      (1 - ε) < (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 ∧ (3 : ℝ) ^ p.1 / (2 : ℝ) ^ p.2 < 1} with hS_def
  have hfin2 : (Prod.snd '' S).Finite := hfin.image Prod.snd
  obtain ⟨M, hM⟩ := hfin2.bddAbove
  obtain ⟨b, z, hbM, hzpos, heq, hfracpos, hlt⟩ := exists_close_multiple M δ' hδ'pos
  set t := Int.fract ((b : ℝ) * ξ) with ht_def
  set a := z.toNat with ha_def
  have haz : (a : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  have haR : (a : ℝ) = (z : ℝ) := by exact_mod_cast haz
  -- Bridge `ξ`, `log 2`, `log 3`.
  have hxi3 : Real.log 2 = ξ * Real.log 3 := by rw [ξ]; field_simp
  have hcross : (b : ℝ) * Real.log 2 - (z : ℝ) * Real.log 3 = t * Real.log 3 := by
    rw [hxi3,
      show (b : ℝ) * (ξ * Real.log 3) - (z : ℝ) * Real.log 3
        = ((b : ℝ) * ξ - (z : ℝ)) * Real.log 3 from by ring, heq]
  have hlogdiv : Real.log ((3 : ℝ) ^ a / (2 : ℝ) ^ b) = (a : ℝ) * Real.log 3 - (b : ℝ) * Real.log 2 := by
    rw [Real.log_div (pow_ne_zero a (by norm_num)) (pow_ne_zero b (by norm_num)),
      Real.log_pow, Real.log_pow]
  have hlogval : Real.log ((3 : ℝ) ^ a / (2 : ℝ) ^ b) = -(t * Real.log 3) := by
    rw [hlogdiv, haR]; linarith [hcross]
  have hδ'eq : δ' * Real.log 3 = -Real.log (1 - ε) := by
    rw [hδ'_def]; field_simp
  have ht3_pos : 0 < t * Real.log 3 := mul_pos hfracpos log3_pos
  have ht3_lt : t * Real.log 3 < -Real.log (1 - ε) := by
    rw [← hδ'eq]; exact mul_lt_mul_of_pos_right hlt log3_pos
  have hlt0 : Real.log ((3 : ℝ) ^ a / (2 : ℝ) ^ b) < 0 := by rw [hlogval]; linarith
  have hgt : Real.log (1 - ε) < Real.log ((3 : ℝ) ^ a / (2 : ℝ) ^ b) := by rw [hlogval]; linarith
  have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ a / (2 : ℝ) ^ b := by positivity
  have hub : (3 : ℝ) ^ a / (2 : ℝ) ^ b < 1 := (Real.log_neg_iff hpow_pos).mp hlt0
  have hlb : (1 - ε) < (3 : ℝ) ^ a / (2 : ℝ) ^ b := (Real.log_lt_log_iff h1me_pos hpow_pos).mp hgt
  have hmem : (a, b) ∈ S := ⟨hapos, hbpos, hlb, hub⟩
  have hbmem : b ∈ Prod.snd '' S := ⟨(a, b), hmem, rfl⟩
  have hble : b ≤ M := hM hbmem
  omega

end RT
