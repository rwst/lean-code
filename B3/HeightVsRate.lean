import B3.SubspaceInstantiation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_den_rpow_gen (τ : ℝ) (hτ : 0 ≤ τ) (c N : ℕ) {D : ℝ} (hD : 0 < D)
    (hDle : D ≤ (3 : ℝ) ^ c) (ε : ℝ) (hε : 0 < ε)
    (hidx : (τ + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ D ^ (-τ - ε) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : Real.log D ≤ (c : ℝ) * Real.log 3 := by
    have h := Real.log_le_log hD hDle
    rwa [Real.log_pow] at h
  have hτε : (0 : ℝ) ≤ τ + ε := by linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hD, Real.exp_le_exp]
  nlinarith [hidx, hlogD, hlog2, mul_le_mul_of_nonneg_left hlogD hτε]

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_den_rpow (c N : ℕ) {D : ℝ} (hD : 0 < D) (hDle : D ≤ (3 : ℝ) ^ c)
    (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ D ^ (-(3 : ℝ) - ε) :=
  rate_le_den_rpow_gen 3 (by norm_num) c N hD hDle ε hε hidx

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_height_rpow (c N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((3 : ℝ) ^ c) ^ (-(3 : ℝ) - ε) :=
  rate_le_den_rpow c N (by positivity) le_rfl ε hε hidx

@[category API, AMS 11 37, ref "BL96"]
theorem subspaceDen_le_pow (c p : ℕ) : ((subspaceDen c p : ℤ) : ℝ) ≤ (3 : ℝ) ^ c := by
  unfold subspaceDen
  push_cast
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  linarith

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_subspaceDen_rpow (c p N : ℕ) (hDpos : 0 < subspaceDen c p)
    (ε : ℝ) (hε : 0 < ε)
    (hidx : (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((subspaceDen c p : ℤ) : ℝ) ^ (-(3 : ℝ) - ε) := by
  refine rate_le_den_rpow c N ?_ (subspaceDen_le_pow c p) ε hε hidx
  exact_mod_cast hDpos

@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexConditionExp (τ : ℝ) (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ m, (τ + ε) * (c m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2

@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexCondition (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  IndexConditionExp 3 c N ε

@[category API, AMS 11 37, ref "AB07" "BL96"]
def IndexConditionExpFreq (τ : ℝ) (c N : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ᶠ m in Filter.atTop, (τ + ε) * (c m : ℝ) * Real.log 3 ≤ (N m : ℝ) * Real.log 2

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem family_rate_le_height (c N : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hidx : IndexCondition c N ε) (m : ℕ) :
    (2 : ℝ) ^ (-(N m : ℝ)) ≤ ((3 : ℝ) ^ (c m)) ^ (-(3 : ℝ) - ε) :=
  rate_le_height_rpow (c m) (N m) ε hε (hidx m)

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem index_of_large_w_gen (τ : ℝ) (hτ : 0 ≤ τ) (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (τ + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (τ + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0; simp only [Nat.cast_zero, mul_zero, zero_mul]; positivity
  · have hcpos' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
    have hcs' : (c : ℝ) ≤ (s : ℝ) := by exact_mod_cast hcs
    have hwpos : (1 : ℝ) < w := by
      nlinarith [hw, hlog2, mul_pos (show (0 : ℝ) < τ + ε by linarith) hlog3]
    have hcw : (c : ℝ) * (w - 1) ≤ (N : ℝ) := by
      nlinarith [hsN, hcpos', mul_le_mul_of_nonneg_right hcs' (by linarith : (0 : ℝ) ≤ w)]
    calc (τ + ε) * (c : ℝ) * Real.log 3
        ≤ (c : ℝ) * (w - 1) * Real.log 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hw (show (0 : ℝ) ≤ (c : ℝ) by linarith)]
      _ ≤ (N : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hcw hlog2.le

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem index_of_large_w (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (3 + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (3 + ε) * (c : ℝ) * Real.log 3 ≤ (N : ℝ) * Real.log 2 :=
  index_of_large_w_gen 3 (by norm_num) c s N w ε hε hcs hsN hw

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem rate_le_height_of_large_w (c s N : ℕ) (w ε : ℝ) (hε : 0 < ε)
    (hcs : c ≤ s) (hsN : w * (s : ℝ) - 1 ≤ (N : ℝ))
    (hw : (3 + ε) * Real.log 3 ≤ (w - 1) * Real.log 2) :
    (2 : ℝ) ^ (-(N : ℝ)) ≤ ((3 : ℝ) ^ c) ^ (-(3 : ℝ) - ε) :=
  rate_le_height_rpow c N ε hε (index_of_large_w c s N w ε hε hcs hsN hw)

end B3
