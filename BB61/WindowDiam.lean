/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteACeiling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Proposition 7: the width of the window, and the vacuity of X7

Formal companion of `note-1061-M2.html` §6 (milestone M2 of `plans/plan-1061.html`),
Proposition 7 — the first of the note's two no-gos, and the one that kills a criterion.

**X7** (`plans/plan-1061.html` §7) proposed to prove Problem 10.61 with no dynamics and no
dimension theory at all: with `Δ = ∑_{j≥2} |α_j-1|/(1-|α_j|)` the `ℓ¹` size of the conjugate
shadow and `g = (α-2)/α` the first gap of `C(α)`, *if `2Δ < g` then every orbit misses a
fixed interval.*  Proposition 7 says the hypothesis is **never satisfied**, at any Pisot
`α > 2` of any degree `d ≥ 2` — and says so with an exact identity rather than an estimate.

## The three statements

* `diam_windowOf` — `diam K = ∑_{m≥0} |c_m|` **exactly**, for the subset-sum set
  `K = {∑_m c_m δ_m}` of any absolutely summable real sequence.  Both endpoints are hit by
  greedy words, so this is an equality, not the usual two-sided estimate.
* `diam_windowOf_eq_two_mul_posSum` — the note's identity
  `diam K = -(∑_m c_m) + 2 ∑_{c_m>0} c_m`, from `|x| = 2 max(x,0) - x` alone; hence
  `diam_windowOf_eq_neg_tsum_iff`: the bound `diam K ≥ |∑_m c_m|` is **attained** exactly
  when no coefficient is positive.
* `not_x7Criterion` — with `c_m = ∑_{j≥2} (α_j-1)α_j^m` the identity
  `∑_{m≥0} c_m = ∑_{j≥2} (α_j-1)/(1-α_j) = -(d-1)` (`tsum_conjCoef`) turns the first two
  into `2Δ ≥ 2 diam K ≥ 2(d-1) ≥ 2 > 1 > g`, so `X7Criterion` is empty.

## Zero margin

The point of the identity is that no sharpening of the `ℓ¹` bound can revive X7.  Everything
in the chain is attained at once: the file constructs `unitQuad a`, the root `α > 2` of
`X² - aX + 1`, for which

* `conjDelta_unitQuad`, `diam_windowSet_unitQuad` — `Δ = diam K = d - 1 = 1` **all three
  equal**, because `β = 1/α ∈ (0,1)` makes every `c_m = (β-1)βᵐ` negative
  (`cCoef_nonpos_of_beta_nonneg`);
* `tendsto_ratio_unitQuad` — the failure ratio `2Δ/g` tends to `2` along the family, so the
  constant `2` in `2Δ ≥ 2 > g` is the exact infimum, approached but never attained.

`unitQuad 4` is `2 + √3` (`unitQuad_four_alpha`), M0's first certified `α`, where the note's
sweep records the enumeration minimum `2Δ/g = 2.20` two members later at `X² - 22X + 1`.

## What is new here relative to `BB61/Confinement.lean`

M1 Lemma 3 already gave `one_le_wMax_sub_wMin`, `diam K ≥ 1` at degree two, by the triangle
inequality.  Proposition 7 replaces that inequality by the identity, adds the general-degree
statement, and adds the attainment — which is what makes the no-go final rather than
provisional.  `Metric.diam` itself appears here for the first time in the root
(`diam_windowSet`); Lemma 3 only ever compared the two endpoints.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M2.html` §6 Prop. 7 (this file), `note-1061-M1.html` Lemmas 2–3 (the
  coefficients `c_m` and the window `K`), `plans/plan-1061.html` §7 row X7 (the criterion).
* Verification script `BB61/m2_prop7_lean.py`.
-/

noncomputable section

namespace BB61

open Filter Topology

/-! ## The subset-sum set of an absolutely summable sequence

Everything in this section is about an arbitrary `c : ℕ → ℝ` with `∑ |c_m| < ∞`; the window
`K` of M1 Lemma 3 is the case `c = P.cCoef` (`windowSet_eq_windowOf`). -/

section Abstract

variable {c : ℕ → ℝ}

/-- The set of all subset sums `∑_{m≥0} c_m δ_m`, `δ ∈ {0,1}^ℕ`. -/
def windowOf (c : ℕ → ℝ) : Set ℝ := Set.range fun δ : ℕ → Bool => ∑' m : ℕ, c m * dR δ m

/-- The note's `P = ∑_{c_m>0} c_m`, the top of `windowOf c`. -/
def posSum (c : ℕ → ℝ) : ℝ := ∑' m : ℕ, max (c m) 0

/-- The note's `-Q = ∑_{c_m<0} c_m`, the bottom of `windowOf c`. -/
def negSum (c : ℕ → ℝ) : ℝ := ∑' m : ℕ, min (c m) 0

/-- The greedy word taking every positive coefficient and no other. -/
def posWord (c : ℕ → ℝ) : ℕ → Bool := fun m => decide (0 < c m)

/-- The greedy word taking every negative coefficient and no other. -/
def negWord (c : ℕ → ℝ) : ℕ → Bool := fun m => decide (c m < 0)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_mul_dR (h : Summable fun m : ℕ => |c m|) (δ : ℕ → Bool) :
    Summable fun m : ℕ => c m * dR δ m := by
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) h)
  rw [abs_mul, abs_of_nonneg (dR_nonneg δ m)]
  exact mul_le_of_le_one_right (abs_nonneg _) (dR_le_one δ m)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_max (h : Summable fun m : ℕ => |c m|) :
    Summable fun m : ℕ => max (c m) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun _ => max_le (le_abs_self _) (abs_nonneg _)) h

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_min (h : Summable fun m : ℕ => |c m|) :
    Summable fun m : ℕ => min (c m) 0 := by
  have hneg : Summable fun m : ℕ => -min (c m) 0 :=
    Summable.of_nonneg_of_le (fun _ => by simp)
      (fun m => by rcases le_total (c m) 0 with h' | h' <;>
        simp [h', abs_of_nonpos, abs_of_nonneg]) h
  simpa using hneg.neg

/-- `P + (-Q) = ∑_m c_m`: the two greedy sums recover the total. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem posSum_add_negSum (h : Summable fun m : ℕ => |c m|) :
    posSum c + negSum c = ∑' m : ℕ, c m := by
  rw [posSum, negSum, ← (summable_max h).tsum_add (summable_min h)]
  exact tsum_congr fun m => by simp [max_add_min (c m) 0]

/-- `P - (-Q) = ∑_m |c_m|`: the width of the window. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem posSum_sub_negSum (h : Summable fun m : ℕ => |c m|) :
    posSum c - negSum c = ∑' m : ℕ, |c m| := by
  rw [posSum, negSum, ← (summable_max h).tsum_sub (summable_min h)]
  exact tsum_congr fun m => by simp [max_sub_min_eq_abs (c m) 0]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wOf_le_posSum (h : Summable fun m : ℕ => |c m|) (δ : ℕ → Bool) :
    ∑' m : ℕ, c m * dR δ m ≤ posSum c := by
  refine (summable_mul_dR h δ).tsum_le_tsum (fun m => ?_) (summable_max h)
  rcases Bool.eq_false_or_eq_true (δ m) with hm | hm <;> simp [dR, hm]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem negSum_le_wOf (h : Summable fun m : ℕ => |c m|) (δ : ℕ → Bool) :
    negSum c ≤ ∑' m : ℕ, c m * dR δ m := by
  refine (summable_min h).tsum_le_tsum (fun m => ?_) (summable_mul_dR h δ)
  rcases Bool.eq_false_or_eq_true (δ m) with hm | hm <;> simp [dR, hm]

/-- `K ⊆ [-Q, P]`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem windowOf_subset_Icc (h : Summable fun m : ℕ => |c m|) :
    windowOf c ⊆ Set.Icc (negSum c) (posSum c) := by
  rintro _ ⟨δ, rfl⟩
  exact ⟨negSum_le_wOf h δ, wOf_le_posSum h δ⟩

/-- The top of the window is attained, by the greedy word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem posSum_mem_windowOf : posSum c ∈ windowOf c := by
  refine ⟨posWord c, ?_⟩
  refine tsum_congr fun m => ?_
  by_cases hm : 0 < c m
  · rw [max_eq_left hm.le]; simp [posWord, dR, hm]
  · rw [max_eq_right (not_lt.mp hm)]; simp [posWord, dR, hm]

/-- The bottom of the window is attained, by the greedy word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem negSum_mem_windowOf : negSum c ∈ windowOf c := by
  refine ⟨negWord c, ?_⟩
  refine tsum_congr fun m => ?_
  by_cases hm : c m < 0
  · rw [min_eq_left hm.le]; simp [negWord, dR, hm]
  · rw [min_eq_right (not_lt.mp hm)]; simp [negWord, dR, hm]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isBounded_windowOf (h : Summable fun m : ℕ => |c m|) :
    Bornology.IsBounded (windowOf c) :=
  Metric.isBounded_Icc _ _ |>.subset (windowOf_subset_Icc h)

/-- **The width of the window, exactly.**  Both endpoints of `[-Q, P]` are hit by greedy
words, so the diameter is the full `ℓ¹` norm of the coefficient sequence — an identity, not
the two-sided estimate M1 Lemma 3 settled for. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowOf (h : Summable fun m : ℕ => |c m|) :
    Metric.diam (windowOf c) = ∑' m : ℕ, |c m| := by
  have hle : negSum c ≤ posSum c :=
    le_trans (negSum_le_wOf h (posWord c)) (wOf_le_posSum h (posWord c))
  refine le_antisymm ?_ ?_
  · refine Metric.diam_le_of_forall_dist_le (tsum_nonneg fun m => abs_nonneg (c m))
      fun x hx y hy => ?_
    obtain ⟨hx1, hx2⟩ := windowOf_subset_Icc h hx
    obtain ⟨hy1, hy2⟩ := windowOf_subset_Icc h hy
    rw [Real.dist_eq, ← posSum_sub_negSum h]
    rw [abs_le]; constructor <;> linarith
  · have hd := Metric.dist_le_diam_of_mem (isBounded_windowOf h)
      (posSum_mem_windowOf (c := c)) (negSum_mem_windowOf (c := c))
    rwa [Real.dist_eq, abs_of_nonneg (by linarith), posSum_sub_negSum h] at hd

/-- **The note's identity**: `diam K = -(∑_m c_m) + 2 ∑_{c_m>0} c_m`.  It is nothing but
`|x| = 2 max(x,0) - x` summed, and it is what makes the no-go final: the excess of `diam K`
over `|∑ c_m|` is exactly twice the positive part. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowOf_eq_two_mul_posSum (h : Summable fun m : ℕ => |c m|) :
    Metric.diam (windowOf c) = -(∑' m : ℕ, c m) + 2 * posSum c := by
  have h1 := posSum_add_negSum h
  have h2 := posSum_sub_negSum h
  rw [diam_windowOf h, ← h2]
  linarith

/-- `diam K ≥ |∑_m c_m|`: the triangle inequality, recovered from the identity. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_tsum_le_diam_windowOf (h : Summable fun m : ℕ => |c m|) :
    |∑' m : ℕ, c m| ≤ Metric.diam (windowOf c) := by
  rw [diam_windowOf h]
  have hs : Summable c := Summable.of_abs h
  simpa [Real.norm_eq_abs] using
    norm_tsum_le_tsum_norm (f := c) (by simpa [Real.norm_eq_abs] using h)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem posSum_nonneg : 0 ≤ posSum c := tsum_nonneg fun m => le_max_right (c m) 0

/-- The positive part vanishes exactly when no coefficient is positive. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem posSum_eq_zero_iff (h : Summable fun m : ℕ => |c m|) :
    posSum c = 0 ↔ ∀ m, c m ≤ 0 := by
  constructor
  · intro h0 m
    have hle : max (c m) 0 ≤ posSum c :=
      (summable_max h).le_tsum m fun j _ => le_max_right _ _
    rw [h0] at hle
    exact le_trans (le_max_left _ _) hle
  · intro hnp
    have hz : (fun m : ℕ => max (c m) 0) = fun _ => (0 : ℝ) := funext fun m => max_eq_right (hnp m)
    rw [posSum, hz, tsum_zero]

/-- **The equality case.**  `diam K = |∑_m c_m|` exactly when no coefficient is positive —
the note's "with equality iff no `c_m` is positive".  So the bound is attained, and no
sharpening of the estimate that produced it is available. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowOf_eq_neg_tsum_iff (h : Summable fun m : ℕ => |c m|) :
    Metric.diam (windowOf c) = -(∑' m : ℕ, c m) ↔ ∀ m, c m ≤ 0 := by
  rw [diam_windowOf_eq_two_mul_posSum h, ← posSum_eq_zero_iff h]
  constructor
  · intro hd; linarith
  · intro hd; rw [hd]; ring

end Abstract

/-! ## The window coefficients of a multiset of conjugates

M1 Lemma 2 puts `c_m = ∑_{j≥2} (α_j - 1) α_j^m`, a sum over the conjugates of `α` other than
`α` itself.  Nothing below needs the multiset to come from an algebraic number: only that
every element lies strictly inside the unit disc. -/

section Conjugates

variable {s : Multiset ℂ}

/-- `c_m = ∑_{j≥2} (α_j - 1) α_j^m` of M1 Lemma 2, before taking the real part. -/
def conjCoefC (s : Multiset ℂ) (m : ℕ) : ℂ := (s.map fun z => (z - 1) * z ^ m).sum

/-- **The window coefficient `c_m`.**  For the conjugate multiset of a real algebraic number
the sum `conjCoefC` is already real — the multiset is closed under complex conjugation — so
this is exactly the note's `c_m`; taking the real part spares the file that argument and
loses nothing, since every statement below is an inequality on `|c_m|`. -/
def conjCoef (s : Multiset ℂ) (m : ℕ) : ℝ := (conjCoefC s m).re

/-- **`Δ = ∑_{j≥2} |α_j - 1|/(1 - |α_j|)`** — the `ℓ¹` size of the conjugate shadow, the
quantity X7 compares against the first gap. -/
def conjDelta (s : Multiset ℂ) : ℝ := (s.map fun z => ‖z - 1‖ / (1 - ‖z‖)).sum

/-- The termwise triangle-inequality majorant of `c_m`, whose total is `Δ`. -/
def conjNormCoef (s : Multiset ℂ) (m : ℕ) : ℝ := (s.map fun z => ‖z - 1‖ * ‖z‖ ^ m).sum

/-- **The identity behind the whole no-go**: `∑_{m≥0} c_m = ∑_{j≥2} (α_j-1)/(1-α_j) = -(d-1)`.
Each conjugate contributes exactly `-1`, whatever it is. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem hasSum_conjCoefC (h : ∀ z ∈ s, ‖z‖ < 1) :
    HasSum (conjCoefC s) (-(Multiset.card s : ℂ)) := by
  induction s using Multiset.induction_on with
  | empty =>
    have hz : conjCoefC (0 : Multiset ℂ) = fun _ : ℕ => (0 : ℂ) := by
      funext m; simp [conjCoefC]
    rw [hz, Multiset.card_zero, Nat.cast_zero, neg_zero]
    exact hasSum_zero
  | cons a t ih =>
    have ha : ‖a‖ < 1 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ z ∈ t, ‖z‖ < 1 := fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have hne : (1 : ℂ) - a ≠ 0 := fun h0 => by
      rw [show a = 1 by linear_combination -h0] at ha; simp at ha
    have hgeom : HasSum (fun m : ℕ => (a - 1) * a ^ m) (-1) := by
      have hg := (hasSum_geometric_of_norm_lt_one ha).mul_left (a - 1)
      rwa [show (a - 1) * (1 - a)⁻¹ = -1 by field_simp; ring] at hg
    have hkey := hgeom.add (ih ht)
    have hfun : (fun m : ℕ => (a - 1) * a ^ m + conjCoefC t m) = conjCoefC (a ::ₘ t) := by
      funext m; simp [conjCoefC]
    have hval : (-1 : ℂ) + -(Multiset.card t : ℂ) = -(Multiset.card (a ::ₘ t) : ℂ) := by
      rw [Multiset.card_cons]; push_cast; ring
    rwa [hfun, hval] at hkey

/-- The majorants sum to `Δ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem hasSum_conjNormCoef (h : ∀ z ∈ s, ‖z‖ < 1) :
    HasSum (conjNormCoef s) (conjDelta s) := by
  induction s using Multiset.induction_on with
  | empty =>
    have hz : conjNormCoef (0 : Multiset ℂ) = fun _ : ℕ => (0 : ℝ) := by
      funext m; simp [conjNormCoef]
    rw [hz, show conjDelta (0 : Multiset ℂ) = 0 by simp [conjDelta]]
    exact hasSum_zero
  | cons a t ih =>
    have ha : ‖a‖ < 1 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ z ∈ t, ‖z‖ < 1 := fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have hgeom : HasSum (fun m : ℕ => ‖a - 1‖ * ‖a‖ ^ m) (‖a - 1‖ / (1 - ‖a‖)) := by
      have hg := (hasSum_geometric_of_lt_one (norm_nonneg a) ha).mul_left ‖a - 1‖
      rwa [← div_eq_mul_inv] at hg
    have hkey := hgeom.add (ih ht)
    have hfun : (fun m : ℕ => ‖a - 1‖ * ‖a‖ ^ m + conjNormCoef t m) = conjNormCoef (a ::ₘ t) := by
      funext m; simp [conjNormCoef]
    have hval : ‖a - 1‖ / (1 - ‖a‖) + conjDelta t = conjDelta (a ::ₘ t) := by
      simp [conjDelta]
    rwa [hfun, hval] at hkey

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_conjCoef_le (s : Multiset ℂ) (m : ℕ) : |conjCoef s m| ≤ conjNormCoef s m := by
  refine le_trans (Complex.abs_re_le_norm _) (le_trans (norm_multiset_sum_le _) (le_of_eq ?_))
  rw [Multiset.map_map, conjNormCoef]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => by simp)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_conjCoef (h : ∀ z ∈ s, ‖z‖ < 1) :
    Summable fun m : ℕ => |conjCoef s m| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_conjCoef_le s)
    (hasSum_conjNormCoef h).summable

/-- **`∑_{m≥0} c_m = -(d-1)`** (M1 Lemma 2), on the real part. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_conjCoef (h : ∀ z ∈ s, ‖z‖ < 1) :
    ∑' m : ℕ, conjCoef s m = -(Multiset.card s : ℝ) := by
  have hre := Complex.hasSum_re (hasSum_conjCoefC h)
  simpa [conjCoef] using hre.tsum_eq

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_abs_conjCoef_le_conjDelta (h : ∀ z ∈ s, ‖z‖ < 1) :
    ∑' m : ℕ, |conjCoef s m| ≤ conjDelta s := by
  rw [← (hasSum_conjNormCoef h).tsum_eq]
  exact (summable_abs_conjCoef h).tsum_le_tsum (abs_conjCoef_le s)
    (hasSum_conjNormCoef h).summable

/-- **The width of the window at general degree**: `diam K = ∑_m |c_m| ≤ Δ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowOf_conjCoef_le (h : ∀ z ∈ s, ‖z‖ < 1) :
    Metric.diam (windowOf (conjCoef s)) ≤ conjDelta s := by
  rw [diam_windowOf (summable_abs_conjCoef h)]
  exact tsum_abs_conjCoef_le_conjDelta h

/-- **M1 Lemma 3 at general degree, with the identity**: `diam K ≥ d - 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_le_diam_windowOf_conjCoef (h : ∀ z ∈ s, ‖z‖ < 1) :
    (Multiset.card s : ℝ) ≤ Metric.diam (windowOf (conjCoef s)) := by
  have hkey := abs_tsum_le_diam_windowOf (summable_abs_conjCoef h)
  rwa [tsum_conjCoef h, abs_neg, Nat.abs_cast] at hkey

/-- **The `ℓ¹` bound, end to end**: `Δ ≥ diam K ≥ d - 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_le_conjDelta (h : ∀ z ∈ s, ‖z‖ < 1) :
    (Multiset.card s : ℝ) ≤ conjDelta s :=
  le_trans (card_le_diam_windowOf_conjCoef h) (diam_windowOf_conjCoef_le h)

end Conjugates

/-! ## Proposition 7: the criterion X7 is empty

For the record, the quantity X7 compares `Δ` against really is a gap of `C(α)`: the two
branch images of M1 Lemma 1(ii) are separated by the open interval `(1/α, (α-1)/α)`, of
length `g = (α-2)/α` (`sub_inv_eq_gap`).  That is what a criterion of the form `2Δ < g`
would exploit — and `not_x7Criterion` says the form is empty. -/

/-- **The first gap of `C(α)`.**  The open interval between the two branch images meets the
Cantor set nowhere; `sub_inv_eq_gap` says its length is exactly `gap α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_inter_gapIoo_eq_empty {α : ℝ} (hα : 1 < α) :
    cantorSet α ∩ Set.Ioo α⁻¹ ((α - 1) / α) = ∅ := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_and,
    not_lt]
  intro hx
  rw [cantorSet_eq_union hα] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · intro h1
    rw [ifsMap_false, lt_div_iff₀ hα0, inv_mul_cancel₀ hα0.ne'] at h1
    have hy1 : y ≤ 1 := (cantorSet_subset_Icc hα hy).2
    linarith
  · intro _
    have hy0 : 0 ≤ y := (cantorSet_subset_Icc hα hy).1
    rw [ifsMap_true, div_le_div_iff_of_pos_right hα0]
    linarith

/-! ### The criterion -/

/-- **The X7 criterion** (`plans/plan-1061.html` §7, row X7): the `ℓ¹` size of the conjugate
shadow is less than half the first gap `g = (α-2)/α` of `C(α)` (`BB61/Cantor.lean`).  Were it
ever satisfiable it would prove Problem 10.61 at `α` with no dynamics and no dimension
theory; `not_x7Criterion` says it never is. -/
def X7Criterion (s : Multiset ℂ) (α : ℝ) : Prop := 2 * conjDelta s < gap α

/-- The first gap of `C(α)` is smaller than `1` — for every `α > 0`, whether or not the
Cantor set is a Cantor set. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_lt_one {α : ℝ} (hα : 0 < α) : gap α < 1 := by
  rw [gap, div_lt_one hα]; linarith

/-- **M2 Proposition 7, the sharp form.**  Even with the *exact* width of the window in place
of its `ℓ¹` majorant `Δ`, the comparison fails: `2 diam K ≥ 2(d-1) ≥ 2 > 1 > g`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_lt_two_mul_diam_windowOf {α : ℝ} {s : Multiset ℂ} (hs : s ≠ 0)
    (h : ∀ z ∈ s, ‖z‖ < 1) (hα : 0 < α) :
    gap α < 2 * Metric.diam (windowOf (conjCoef s)) := by
  have hcard : (1 : ℝ) ≤ (Multiset.card s : ℝ) := by
    have : 1 ≤ Multiset.card s := Nat.one_le_iff_ne_zero.mpr fun h0 =>
      hs (Multiset.card_eq_zero.mp h0)
    exact_mod_cast this
  have hd := card_le_diam_windowOf_conjCoef h
  have hg := gap_lt_one hα
  linarith

/-- **M2 Proposition 7.**  The X7 criterion `2Δ < g` is satisfied by no `α > 0` and no
nonempty multiset of conjugates inside the unit disc — in particular by no Pisot number of
degree `d ≥ 2`.  The reason is the identity `∑_m c_m = -(d-1)`, not an estimate. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_x7Criterion {α : ℝ} {s : Multiset ℂ} (hs : s ≠ 0) (h : ∀ z ∈ s, ‖z‖ < 1)
    (hα : 0 < α) : ¬ X7Criterion s α := by
  have hd := gap_lt_two_mul_diam_windowOf hs h hα
  have hle := diam_windowOf_conjCoef_le h
  rw [X7Criterion]
  linarith

/-- **M2 Proposition 7, stated in the degree.**  If `α` is a real root of a monic integer
polynomial of degree `d ≥ 2` all of whose other roots lie strictly inside the unit disc — a
Pisot number of degree `d ≥ 2`, in particular — then X7 does not fire at `α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_x7Criterion_of_natDegree {p : Polynomial ℤ} (hp : p.Monic) {α : ℝ}
    {s : Multiset ℂ} (hroots : (p.map (Int.castRingHom ℂ)).roots = (α : ℂ) ::ₘ s)
    (hd : 2 ≤ p.natDegree) (h : ∀ z ∈ s, ‖z‖ < 1) (hα : 0 < α) : ¬ X7Criterion s α := by
  have hcard := card_add_one_eq_natDegree hp hroots
  refine not_x7Criterion (fun h0 => ?_) h hα
  rw [h0] at hcard
  simp only [Multiset.card_zero] at hcard
  omega

/-- **The margin.**  `2Δ/g ≥ 2/g > 2`: the criterion fails by a factor of at least two, and
that factor is exactly `2/g` whenever `Δ = d - 1` — which happens (`conjDelta_unitQuad`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_div_gap_le_ratio {α : ℝ} {s : Multiset ℂ} (hs : s ≠ 0) (h : ∀ z ∈ s, ‖z‖ < 1)
    (hα : 2 < α) : 2 / gap α ≤ 2 * conjDelta s / gap α := by
  have hg : 0 < gap α := (gap_pos_iff (by linarith)).mpr hα
  have hcard : (1 : ℝ) ≤ (Multiset.card s : ℝ) := by
    have : 1 ≤ Multiset.card s := Nat.one_le_iff_ne_zero.mpr fun h0 =>
      hs (Multiset.card_eq_zero.mp h0)
    exact_mod_cast this
  have hΔ := card_le_conjDelta h
  have h2 : (2 : ℝ) ≤ 2 * conjDelta s := by linarith
  gcongr

/-! ## Degree two: the window of a `QuadSetup`

The single conjugate is `β`, so `d - 1 = 1`, the majorant `Δ` is *equal* to the width
`∑_m |c_m|` (there is only one conjugate, so the triangle inequality is an identity), and the
whole chain of Proposition 7 collapses to `2 diam K = 2Δ ≥ 2 > 1 > g`. -/

namespace QuadSetup

variable (P : QuadSetup)

/-- The conjugate multiset at degree two: the single conjugate `β`. -/
def quadConj : Multiset ℂ := {(P.β : ℂ)}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_quadConj : Multiset.card P.quadConj = 1 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadConj_ne_zero : P.quadConj ≠ 0 := by
  intro h0
  have := congrArg Multiset.card h0
  simp [card_quadConj] at this

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_lt_one_of_mem_quadConj : ∀ z ∈ P.quadConj, ‖z‖ < 1 := by
  intro z hz
  rw [quadConj, Multiset.mem_singleton] at hz
  subst hz
  simpa using P.abs_beta_lt_one

/-- The general-degree coefficient specialises to M1's `c_m = (β-1)βᵐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem conjCoef_quadConj : conjCoef P.quadConj = P.cCoef := by
  funext m
  have h : conjCoefC P.quadConj m = (((P.β - 1) * P.β ^ m : ℝ) : ℂ) := by
    simp [conjCoefC, quadConj]
  rw [conjCoef, h, Complex.ofReal_re, cCoef]

/-- The general-degree `Δ` specialises to `|β-1|/(1-|β|)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem conjDelta_quadConj : conjDelta P.quadConj = |P.β - 1| / (1 - |P.β|) := by
  rw [conjDelta, quadConj, Multiset.map_singleton, Multiset.sum_singleton]
  congr 1
  · rw [show ((P.β : ℂ) - 1) = (((P.β - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  · rw [Complex.norm_real, Real.norm_eq_abs]

/-- The window of M1 Lemma 3 is the subset-sum set of its coefficients. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem windowSet_eq_windowOf : P.windowSet = windowOf P.cCoef := rfl

/-- **`diam K = ∑_m |c_m|` at degree two.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet : Metric.diam P.windowSet = ∑' m : ℕ, |P.cCoef m| := by
  rw [windowSet_eq_windowOf]
  exact diam_windowOf P.summable_abs_cCoef

/-- **At degree two the `ℓ¹` majorant is exact**: `Δ = diam K`.  With one conjugate the
triangle inequality of Proposition 7's chain has nothing to lose. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_eq_conjDelta :
    Metric.diam P.windowSet = conjDelta P.quadConj := by
  have hβ := P.abs_beta_lt_one
  have habs : ∀ m : ℕ, |P.cCoef m| = |P.β - 1| * |P.β| ^ m := by
    intro m; rw [cCoef, abs_mul, abs_pow]
  rw [diam_windowSet, conjDelta_quadConj]
  rw [tsum_congr habs, tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg _) hβ,
    div_eq_mul_inv]

/-- `P + (-Q) = -1`: M1's `∑_m c_m = -(d-1)` at `d = 2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wMax_add_wMin : P.wMax + P.wMin = -1 := by
  rw [show P.wMax = posSum P.cCoef from rfl, show P.wMin = negSum P.cCoef from rfl,
    posSum_add_negSum P.summable_abs_cCoef, P.tsum_cCoef]

/-- **The note's identity at degree two**: `diam K = (d-1) + 2P = 1 + 2P`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_eq_one_add_two_mul_wMax :
    Metric.diam P.windowSet = 1 + 2 * P.wMax := by
  rw [windowSet_eq_windowOf, diam_windowOf_eq_two_mul_posSum P.summable_abs_cCoef, P.tsum_cCoef]
  norm_num [show posSum P.cCoef = P.wMax from rfl]

/-- **M1 Lemma 3's bound, from the identity**: `diam K ≥ 1 = d - 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_diam_windowSet : 1 ≤ Metric.diam P.windowSet := by
  rw [diam_windowSet_eq_one_add_two_mul_wMax]
  have := posSum_nonneg (c := P.cCoef)
  rw [show P.wMax = posSum P.cCoef from rfl]
  linarith

/-- **The equality case at degree two**: the bound is attained exactly when no coefficient is
positive. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_eq_one_iff : Metric.diam P.windowSet = 1 ↔ ∀ m, P.cCoef m ≤ 0 := by
  rw [windowSet_eq_windowOf, ← posSum_eq_zero_iff P.summable_abs_cCoef,
    diam_windowOf_eq_two_mul_posSum P.summable_abs_cCoef, P.tsum_cCoef]
  constructor
  · intro hd; linarith
  · intro hd; rw [hd]; norm_num

/-- If the conjugate is nonnegative, every `c_m = (β-1)βᵐ` is `≤ 0`: the conjugate is inside
the unit disc, so `β - 1 < 0`, and `βᵐ ≥ 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cCoef_nonpos_of_beta_nonneg (hβ : 0 ≤ P.β) (m : ℕ) : P.cCoef m ≤ 0 := by
  have h1 : P.β < 1 := lt_of_le_of_lt (le_abs_self _) P.abs_beta_lt_one
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg hβ m)

/-- **The attainment.**  A conjugate in `[0,1)` puts every coefficient on the negative side,
so the window is exactly as wide as the identity forces and no wider: `diam K = d - 1 = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_eq_one_of_beta_nonneg (hβ : 0 ≤ P.β) : Metric.diam P.windowSet = 1 :=
  (P.diam_windowSet_eq_one_iff).mpr (P.cCoef_nonpos_of_beta_nonneg hβ)

/-- For a unit of norm `+1` — the polynomial `X² - aX + 1` — the conjugate is `1/α > 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_pos_of_b_eq_neg_one (hb : P.b = -1) : 0 < P.β := by
  have h := P.alpha_mul_beta
  rw [hb] at h
  norm_num at h
  nlinarith [P.alpha_pos, h]

/-- **The note's attainment family, at the level of the setting**: every `X² - aX + 1`
attains `diam K = d - 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_eq_one_of_b_eq_neg_one (hb : P.b = -1) : Metric.diam P.windowSet = 1 :=
  P.diam_windowSet_eq_one_of_beta_nonneg (P.beta_pos_of_b_eq_neg_one hb).le

/-- **M2 Proposition 7 at degree two.**  X7 never fires on a `QuadSetup`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_x7Criterion_quad : ¬ X7Criterion P.quadConj P.α :=
  not_x7Criterion P.quadConj_ne_zero P.norm_lt_one_of_mem_quadConj P.alpha_pos

end QuadSetup

/-! ## The attainment family `X² - aX + 1`, and the exact constant `2`

The note's "with zero margin" is the statement that every inequality of Proposition 7's chain
except the last is an equality somewhere.  This section exhibits the family where they all
are at once, and shows that the surviving inequality `1 > g` degenerates along it — so the
constant `2` in `2Δ ≥ 2 > g` is the exact infimum of the failure ratio. -/

section UnitQuad

variable {a : ℕ} (ha : 3 ≤ a)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sq_sqrt_sq_sub_four (ha : 3 ≤ a) :
    Real.sqrt ((a : ℝ) ^ 2 - 4) ^ 2 = (a : ℝ) ^ 2 - 4 := by
  have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  exact Real.sq_sqrt (by nlinarith)

/-- **The attainment family.**  The larger root of `X² - aX + 1`, `a ≥ 3`: a unit of norm
`+1`, with conjugate `β = 1/α ∈ (0,1)` and hence every window coefficient `c_m = (β-1)βᵐ`
strictly negative.  `unitQuad 4` is `2 + √3`. -/
def unitQuad (a : ℕ) (ha : 3 ≤ a) : QuadSetup where
  a := (a : ℤ)
  b := -1
  α := ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 4)) / 2
  root := by
    have hS := sq_sqrt_sq_sub_four ha
    push_cast
    linear_combination hS / 4
  one_lt := by
    have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have h0 := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 4)
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  conj_lt := by
    have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have h0 := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 4)
    have hS := sq_sqrt_sq_sub_four ha
    push_cast
    rw [abs_lt]
    constructor <;> [skip; skip] <;> nlinarith [hS, h0, h3]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem unitQuad_b : (unitQuad a ha).b = -1 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem unitQuad_alpha :
    (unitQuad a ha).α = ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 4)) / 2 := rfl

/-- Every member has `α > 2`, so `C(α)` really is a Cantor set and `g > 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_lt_unitQuad_alpha : 2 < (unitQuad a ha).α := by
  have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have h0 := Real.sqrt_nonneg ((a : ℝ) ^ 2 - 4)
  have hS := sq_sqrt_sq_sub_four ha
  rw [unitQuad_alpha, lt_div_iff₀ (by norm_num)]
  nlinarith [hS, h0, h3]

/-- The first member is `2 + √3` — M0's first certified `α`, and `BB61/Window.lean`'s. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem unitQuad_four_alpha (h : 3 ≤ 4) : (unitQuad 4 h).α = 2 + Real.sqrt 3 := by
  rw [unitQuad_alpha, show ((4 : ℕ) : ℝ) = 4 by norm_num,
    show (4 : ℝ) ^ 2 - 4 = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]
  ring

/-- **The bound of Proposition 7 is attained**: `diam K = d - 1 = 1` on the whole family. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem diam_windowSet_unitQuad : Metric.diam (unitQuad a ha).windowSet = 1 :=
  (unitQuad a ha).diam_windowSet_eq_one_of_b_eq_neg_one rfl

/-- **And so is the `ℓ¹` majorant**: `Δ = diam K = d - 1 = 1`.  Every inequality of the
note's chain `2Δ ≥ 2∑|c_m| ≥ 2 diam K ≥ 2(d-1)` is an equality here. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem conjDelta_unitQuad : conjDelta (unitQuad a ha).quadConj = 1 := by
  rw [← (unitQuad a ha).diam_windowSet_eq_conjDelta, diam_windowSet_unitQuad]

end UnitQuad

section UnitQuadSeq

/-- The family, indexed so that the dependent hypothesis is uniform. -/
def unitQuadSeq (n : ℕ) : QuadSetup := unitQuad (n + 3) (by omega)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem unitQuadSeq_alpha (n : ℕ) :
    (unitQuadSeq n).α = (((n + 3 : ℕ) : ℝ) + Real.sqrt (((n + 3 : ℕ) : ℝ) ^ 2 - 4)) / 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem conjDelta_unitQuadSeq (n : ℕ) : conjDelta (unitQuadSeq n).quadConj = 1 :=
  conjDelta_unitQuad (by omega)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_alpha_unitQuadSeq :
    Filter.Tendsto (fun n : ℕ => (unitQuadSeq n).α) Filter.atTop Filter.atTop := by
  refine tendsto_atTop_mono (f := fun n : ℕ => ((n : ℝ) + 3) / 2) (fun n => ?_) ?_
  · have hc : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [unitQuadSeq_alpha, hc]
    have h0 := Real.sqrt_nonneg (((n : ℝ) + 3) ^ 2 - 4)
    linarith
  · exact (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num)

/-- The first gap tends to its ceiling `1` as `α → ∞`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_gap_atTop : Filter.Tendsto gap Filter.atTop (nhds 1) := by
  have hev : gap =ᶠ[Filter.atTop] fun α : ℝ => 1 - 2 * α⁻¹ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with α hα
    rw [gap]; field_simp
  refine Filter.Tendsto.congr' hev.symm ?_
  have h0 : Filter.Tendsto (fun α : ℝ => 2 * α⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  simpa using tendsto_const_nhds.sub h0

/-- **Zero margin, made precise.**  Along `X² - aX + 1` the failure ratio `2Δ/g` tends to
`2`: the constant in Proposition 7's `2Δ ≥ 2 > g` is the exact infimum over all Pisot `α > 2`
of degree `≥ 2`, approached but — since `g < 1` always — never attained.  No refinement of
the `ℓ¹` bound can revive X7. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_ratio_unitQuadSeq :
    Filter.Tendsto
      (fun n : ℕ => 2 * conjDelta (unitQuadSeq n).quadConj / gap (unitQuadSeq n).α)
      Filter.atTop (nhds 2) := by
  have hc : ∀ n : ℕ, 2 * conjDelta (unitQuadSeq n).quadConj = 2 := fun n => by
    rw [conjDelta_unitQuadSeq]; norm_num
  simp only [hc]
  have hg : Filter.Tendsto (fun n : ℕ => gap (unitQuadSeq n).α) Filter.atTop (nhds 1) :=
    tendsto_gap_atTop.comp tendsto_alpha_unitQuadSeq
  have hdiv : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / gap (unitQuadSeq n).α)
      Filter.atTop (nhds (2 / 1)) := Filter.Tendsto.div tendsto_const_nhds hg one_ne_zero
  simpa using hdiv

end UnitQuadSeq

end BB61
