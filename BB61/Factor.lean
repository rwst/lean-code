/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Covering
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Lemma 6: the factor map `F : {0,1}^ℤ → 𝕋`

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Lemma 6, quadratic case.

`BB61/Splitting.lean` writes `{ξ αⁿ}` as `{t_n - S_n}`, with `t_n` a function of the digits
*after* time `n` and `S_n` a function of the digits *before* it.  Lemma 6 packages the two
halves into a single continuous map off the **two-sided** shift space, so that the whole
orbit `({ξ αⁿ})_{n ≥ 0}` becomes the image of one shift orbit:

* `Shift = ℤ → Bool` with the product topology, `shiftZ` the left shift `(σω)_k = ω_{k+1}`;
* `futures ω = (ω_1, ω_2, …)` and `pasts ω = (ω_0, ω_{-1}, ω_{-2}, …)`;
* `wVal δ = ∑_{m≥0} c_m δ_m` with `c_m = (β-1)βᵐ` — the window map `S` of the note, whose
  image is the compact set `K` of Lemma 3;
* `fRaw ω = t(ω⁺) - S(ω⁻)` and `fMap ω = fRaw ω mod 1`, valued in `AddCircle (1 : ℝ)`.

The two halves of Lemma 6:

* `abs_fRaw_sub_le_of_agree` — if `ω` and `ω'` agree on the central block `[-N, N]` then
  `|F ω - F ω'| ≤ α^{-N} + (1+|β|)|β|^{N+1}/(1-|β|)`.  The note's shift metric is
  `d(ω, ω') = 2^{-N}`, so this *is* its Hölder estimate; `holder_fRaw` states it in that
  shape, for any exponent `θ` with `2^θ ≤ α` and `2^θ|β| ≤ 1` — the largest being the note's
  `θ = min(log α, log(1/ρ))/log 2`.  `continuous_fMap` is the consequence Theorem 7 uses.
* `fMap_iterate_padZ` — with `ω̃ = padZ ε` the word `ε` padded by zeros on the non-positive
  coordinates, `F(σⁿ ω̃) = ξ αⁿ mod 1` for every `n ≥ 0`.  This is `fract_split` read on the
  circle, and it is what turns the orbit of fractional parts into a shift orbit.

`BB61/Invariant.lean` builds M1 Theorem 7 on top of it.
-/

namespace BB61

open Filter Topology

/-! ## The two-sided shift -/

/-- The two-sided full `2`-shift space `{0,1}^ℤ`, with the product topology. -/
abbrev Shift : Type := ℤ → Bool

/-- The left shift `(σ ω)_k = ω_{k+1}` on `{0,1}^ℤ`. -/
def shiftZ (ω : Shift) : Shift := fun k => ω (k + 1)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_shiftZ : Continuous shiftZ :=
  continuous_pi fun k => continuous_apply (k + 1)

/-- The `n`-th iterate of the shift reads the word `n` places later. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shiftZ_iterate (ω : Shift) (n : ℕ) (k : ℤ) : shiftZ^[n] ω k = ω (k + n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', shiftZ, ih]
      congr 1
      push_cast
      ring

/-- The future half `ω⁺ = (ω_1, ω_2, …)`, zero-indexed. -/
def futures (ω : Shift) : ℕ → Bool := fun j => ω ((j : ℤ) + 1)

/-- The past half `ω⁻ = (ω_0, ω_{-1}, ω_{-2}, …)`, zero-indexed. -/
def pasts (ω : Shift) : ℕ → Bool := fun m => ω (-(m : ℤ))

/-- `ω̃`: the one-sided word `ε` padded by zeros on the non-positive coordinates.
The note's `ω̃_k = ε_k` for `k ≥ 1` and `ω̃_k = 0` for `k ≤ 0`; digits are zero-indexed
here, so the note's `ε_k` is `ε (k-1)`. -/
def padZ (ε : ℕ → Bool) : Shift := fun k => if 1 ≤ k then ε (k - 1).toNat else false

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem futures_iterate_padZ (ε : ℕ → Bool) (n : ℕ) :
    futures (shiftZ^[n] (padZ ε)) = shift ε n := by
  funext j
  have hk : ((j : ℤ) + 1 + n) = ((n + j : ℕ) : ℤ) + 1 := by push_cast; ring
  have hpos : (0 : ℤ) ≤ (n : ℤ) + (j : ℤ) := by omega
  have hidx : ((n : ℤ) + (j : ℤ)).toNat = n + j := by omega
  simp only [futures, shiftZ_iterate, hk, padZ, shift]
  simp [hpos, hidx]

/-- The past half of the shifted padded word is the reversed, zero-padded past
`padWord ε n = (ε_{n-1}, …, ε_0, 0, 0, …)` of `BB61/Covering.lean`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pasts_iterate_padZ (ε : ℕ → Bool) (n : ℕ) :
    pasts (shiftZ^[n] (padZ ε)) = QuadSetup.padWord ε n := by
  funext m
  simp only [pasts, shiftZ_iterate, padZ, QuadSetup.padWord]
  by_cases h : m < n
  · have h1 : (1 : ℤ) ≤ -(m : ℤ) + n := by omega
    have h2 : (-(m : ℤ) + n - 1).toNat = n - 1 - m := by omega
    simp [h1, h2, h]
  · have h1 : ¬ (1 : ℤ) ≤ -(m : ℤ) + n := by omega
    simp [h1, h]

/-! ## The Cantor half: continuity and the agreement bound

Both halves of `F` are uniformly convergent series of *coordinate observables*, so both are
continuous and both obey an agreement bound.  This section does the Cantor half, which needs
no quadratic data. -/

/-- Digits agreeing at one place give equal real values there. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_congr {u v : ℕ → Bool} {k : ℕ} (h : u k = v k) : dR u k = dR v k := by
  unfold dR; rw [h]

/-- `|dR u k - dR v k| ≤ 1`: two digits differ by at most one. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_dR_sub_le_one (u v : ℕ → Bool) (k : ℕ) : |dR u k - dR v k| ≤ 1 := by
  rcases abs_cases (dR u k - dR v k) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    linarith [dR_nonneg u k, dR_le_one u k, dR_nonneg v k, dR_le_one v k]

/-- A single digit of the two-sided word, as a real observable: `Bool` is discrete, so any
function out of it is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_boolAt (j : ℤ) : Continuous fun ω : Shift => (if ω j then (1 : ℝ) else 0) :=
  (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
    (continuous_apply j)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_dR_futures (k : ℕ) : Continuous fun ω : Shift => dR (futures ω) k :=
  continuous_boolAt ((k : ℤ) + 1)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_dR_pasts (m : ℕ) : Continuous fun ω : Shift => dR (pasts ω) m :=
  continuous_boolAt (-(m : ℤ))

/-- The future half of the factor map is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_piVal_futures {α : ℝ} (hα : 1 < α) :
    Continuous fun ω : Shift => piVal α (futures ω) := by
  have hr0 : (0 : ℝ) ≤ α⁻¹ := (inv_pos_of_one_lt hα).le
  have hr1 : α⁻¹ < 1 := inv_lt_one_of_one_lt hα
  refine continuous_const.mul (continuous_tsum
    (fun k => (continuous_dR_futures k).mul continuous_const)
    (summable_geom_succ hr0 hr1) fun k ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dR_nonneg _ _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (α⁻¹) ^ (k + 1))]
  exact mul_le_of_le_one_left (by positivity) (dR_le_one _ _)

/-- **Lemma 6, future half.**  Words agreeing on their first `N` letters have Cantor values
within `α^{-N}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_piVal_sub_le_of_agree {α : ℝ} (hα : 1 < α) {u v : ℕ → Bool} {N : ℕ}
    (h : ∀ k, k < N → u k = v k) : |piVal α u - piVal α v| ≤ (α⁻¹) ^ N := by
  have hr0 : (0 : ℝ) ≤ α⁻¹ := (inv_pos_of_one_lt hα).le
  have hr1 : α⁻¹ < 1 := inv_lt_one_of_one_lt hα
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hsu := summable_dR_pow hr0 hr1 u
  have hsv := summable_dR_pow hr0 hr1 v
  have hsg : Summable fun k : ℕ => dR u k * (α⁻¹) ^ (k + 1) - dR v k * (α⁻¹) ^ (k + 1) :=
    hsu.sub hsv
  have hdiff : piVal α u - piVal α v
      = (α - 1) * ∑' k : ℕ, (dR u k * (α⁻¹) ^ (k + 1) - dR v k * (α⁻¹) ^ (k + 1)) := by
    rw [piVal, piVal, ← mul_sub, hsu.tsum_sub hsv]
  have hzero : ∀ k ∈ Finset.range N,
      dR u k * (α⁻¹) ^ (k + 1) - dR v k * (α⁻¹) ^ (k + 1) = 0 := by
    intro k hk
    rw [dR_congr (h k (Finset.mem_range.mp hk)), sub_self]
  have hshift : ∑' k : ℕ, (dR u k * (α⁻¹) ^ (k + 1) - dR v k * (α⁻¹) ^ (k + 1))
      = ∑' k : ℕ, (dR u (k + N) * (α⁻¹) ^ (k + N + 1) - dR v (k + N) * (α⁻¹) ^ (k + N + 1)) := by
    rw [← hsg.sum_add_tsum_nat_add N, Finset.sum_eq_zero hzero, zero_add]
  have hgeom : Summable fun k : ℕ => (α⁻¹) ^ (k + (N + 1)) := by
    simp only [pow_add]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hbd : ∀ k : ℕ,
      ‖dR u (k + N) * (α⁻¹) ^ (k + N + 1) - dR v (k + N) * (α⁻¹) ^ (k + N + 1)‖
        ≤ (α⁻¹) ^ (k + (N + 1)) := by
    intro k
    have hrw : dR u (k + N) * (α⁻¹) ^ (k + N + 1) - dR v (k + N) * (α⁻¹) ^ (k + N + 1)
        = (dR u (k + N) - dR v (k + N)) * (α⁻¹) ^ (k + (N + 1)) := by ring_nf
    rw [Real.norm_eq_abs, hrw, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (α⁻¹) ^ (k + (N + 1)))]
    exact mul_le_of_le_one_left (by positivity) (abs_dR_sub_le_one u v (k + N))
  have htail :
      |∑' k : ℕ, (dR u (k + N) * (α⁻¹) ^ (k + N + 1) - dR v (k + N) * (α⁻¹) ^ (k + N + 1))|
        ≤ (α⁻¹) ^ (N + 1) * (1 - α⁻¹)⁻¹ := by
    have hb := tsum_of_norm_bounded hgeom.hasSum hbd
    rw [Real.norm_eq_abs] at hb
    refine hb.trans_eq ?_
    simp only [pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
    ring
  rw [hdiff, hshift, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ α - 1)]
  calc (α - 1)
        * |∑' k : ℕ, (dR u (k + N) * (α⁻¹) ^ (k + N + 1) - dR v (k + N) * (α⁻¹) ^ (k + N + 1))|
      ≤ (α - 1) * ((α⁻¹) ^ (N + 1) * (1 - α⁻¹)⁻¹) := by gcongr
  _ = (α⁻¹) ^ N := by
        have hα1 : α - 1 ≠ 0 := by linarith
        have h1 : (1 : ℝ) - α⁻¹ = (α - 1) / α := by field_simp
        rw [pow_succ, h1]
        field_simp

/-! ## The window half, and the factor map -/

namespace QuadSetup

variable (P : QuadSetup)

/-- The window coefficient `c_m = (β-1) βᵐ` (M1 Lemma 2, degree two). -/
noncomputable def cCoef (m : ℕ) : ℝ := (P.β - 1) * P.β ^ m

/-- `|c_m| ≤ (1+|β|)|β|ᵐ`: the note's `|c_m| ≤ C_α ρᵐ` at degree two. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_cCoef_le (m : ℕ) : |P.cCoef m| ≤ (1 + |P.β|) * |P.β| ^ m := by
  have h1 : |P.β - 1| ≤ 1 + |P.β| := by
    rcases abs_cases P.β with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (P.β - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith
  rw [cCoef, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_cCoef (δ : ℕ → Bool) : Summable fun m : ℕ => P.cCoef m * dR δ m := by
  have hβ := P.abs_beta_lt_one
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg P.β) hβ).mul_left (1 + |P.β|)) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |P.cCoef m| * |dR δ m| ≤ ((1 + |P.β|) * |P.β| ^ m) * 1 := by
        refine mul_le_mul (P.abs_cCoef_le m) ?_ (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (dR_nonneg δ m)]; exact dR_le_one δ m
  _ = (1 + |P.β|) * |P.β| ^ m := mul_one _

/-- **The window map** `S(δ) = ∑_{m≥0} c_m δ_m` (M1 Lemma 6); its image is the compact
set `K` of M1 Lemma 3. -/
noncomputable def wVal (δ : ℕ → Bool) : ℝ := ∑' m : ℕ, P.cCoef m * dR δ m

/-- On a word supported in `[0, n)` the window series is the finite window sum: the
zero-padded past of `ε` at time `n` has `S(δ) = S_n` **exactly**.  This is M1 Prop. 4's
point — truncation of the past is not an approximation of a point of `K`, it *is* a point
of `K`, which is why the confinement carries no `O(ρⁿ)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wVal_padWord (ε : ℕ → Bool) (n : ℕ) : P.wVal (padWord ε n) = P.sPart ε n := by
  have hvanish : ∀ m ∉ Finset.range n, P.cCoef m * dR (padWord ε n) m = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    simp [dR_padWord, hm]
  rw [wVal, tsum_eq_sum hvanish, P.sPart_eq_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m < n := Finset.mem_range.mp hm
  simp only [dR_padWord, cCoef, mul_assoc]
  simp [hm']

/-- The past half of the factor map is continuous. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_wVal_pasts : Continuous fun ω : Shift => P.wVal (pasts ω) := by
  have hβ := P.abs_beta_lt_one
  refine continuous_tsum (fun m => continuous_const.mul (continuous_dR_pasts m))
    ((summable_geometric_of_lt_one (abs_nonneg P.β) hβ).mul_left (1 + |P.β|)) fun m ω => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |P.cCoef m| * |dR (pasts ω) m| ≤ ((1 + |P.β|) * |P.β| ^ m) * 1 := by
        refine mul_le_mul (P.abs_cCoef_le m) ?_ (abs_nonneg _) (by positivity)
        rw [abs_of_nonneg (dR_nonneg _ _)]; exact dR_le_one _ _
  _ = (1 + |P.β|) * |P.β| ^ m := mul_one _

/-- **Lemma 6, past half.**  Words agreeing on their first `N+1` letters have window values
within `(1+|β|)|β|^{N+1}/(1-|β|)` — the note's `C_α ρ^{N+1}/(1-ρ)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_wVal_sub_le_of_agree {δ δ' : ℕ → Bool} {N : ℕ} (h : ∀ m, m ≤ N → δ m = δ' m) :
    |P.wVal δ - P.wVal δ'| ≤ (1 + |P.β|) * |P.β| ^ (N + 1) / (1 - |P.β|) := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hsδ := P.summable_cCoef δ
  have hsδ' := P.summable_cCoef δ'
  have hsg : Summable fun m : ℕ => P.cCoef m * dR δ m - P.cCoef m * dR δ' m := hsδ.sub hsδ'
  have hdiff : P.wVal δ - P.wVal δ'
      = ∑' m : ℕ, (P.cCoef m * dR δ m - P.cCoef m * dR δ' m) := (hsδ.tsum_sub hsδ').symm
  have hzero : ∀ m ∈ Finset.range (N + 1), P.cCoef m * dR δ m - P.cCoef m * dR δ' m = 0 := by
    intro m hm
    rw [dR_congr (h m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))), sub_self]
  have hshift : ∑' m : ℕ, (P.cCoef m * dR δ m - P.cCoef m * dR δ' m)
      = ∑' m : ℕ, (P.cCoef (m + (N + 1)) * dR δ (m + (N + 1))
          - P.cCoef (m + (N + 1)) * dR δ' (m + (N + 1))) := by
    rw [← hsg.sum_add_tsum_nat_add (N + 1), Finset.sum_eq_zero hzero, zero_add]
  have hgeom : Summable fun m : ℕ => (1 + |P.β|) * |P.β| ^ (m + (N + 1)) := by
    simp only [pow_add]
    exact ((summable_geometric_of_lt_one hβ0 hβ).mul_right _).mul_left _
  have hbd : ∀ m : ℕ,
      ‖P.cCoef (m + (N + 1)) * dR δ (m + (N + 1))
        - P.cCoef (m + (N + 1)) * dR δ' (m + (N + 1))‖
        ≤ (1 + |P.β|) * |P.β| ^ (m + (N + 1)) := by
    intro m
    have hrw : P.cCoef (m + (N + 1)) * dR δ (m + (N + 1))
        - P.cCoef (m + (N + 1)) * dR δ' (m + (N + 1))
        = P.cCoef (m + (N + 1)) * (dR δ (m + (N + 1)) - dR δ' (m + (N + 1))) := by ring
    rw [Real.norm_eq_abs, hrw, abs_mul]
    calc |P.cCoef (m + (N + 1))| * |dR δ (m + (N + 1)) - dR δ' (m + (N + 1))|
        ≤ ((1 + |P.β|) * |P.β| ^ (m + (N + 1))) * 1 :=
          mul_le_mul (P.abs_cCoef_le _) (abs_dR_sub_le_one δ δ' _) (abs_nonneg _) (by positivity)
    _ = (1 + |P.β|) * |P.β| ^ (m + (N + 1)) := mul_one _
  rw [hdiff, hshift]
  have hb := tsum_of_norm_bounded hgeom.hasSum hbd
  rw [Real.norm_eq_abs] at hb
  refine hb.trans_eq ?_
  simp only [pow_add]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ]
  field_simp

/-! ## The factor map -/

/-- The factor map before reduction mod one: `t(ω⁺) - S(ω⁻)`. -/
noncomputable def fRaw (ω : Shift) : ℝ := piVal P.α (futures ω) - P.wVal (pasts ω)

/-- **The factor map** `F : {0,1}^ℤ → 𝕋` of M1 Lemma 6. -/
noncomputable def fMap (ω : Shift) : AddCircle (1 : ℝ) := ((P.fRaw ω : ℝ) : AddCircle (1 : ℝ))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_fRaw : Continuous P.fRaw :=
  (continuous_piVal_futures P.one_lt).sub P.continuous_wVal_pasts

/-- **`F` is continuous** — the half of M1 Lemma 6 that Theorem 7 consumes. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_fMap : Continuous P.fMap :=
  QuotientAddGroup.continuous_mk.comp P.continuous_fRaw

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_fMap : Measurable P.fMap := P.continuous_fMap.measurable

/-- **M1 Lemma 6, the modulus of continuity.**  If `ω` and `ω'` agree on the central block
`[-N, N]` then

`|F ω - F ω'| ≤ α^{-N} + (1+|β|)|β|^{N+1}/(1-|β|)`.

The note's shift metric is `d(ω, ω') = 2^{-N}`, so this is exactly its Hölder estimate;
`holder_fRaw` restates it in that shape. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fRaw_sub_le_of_agree {ω ω' : Shift} {N : ℕ}
    (h : ∀ k : ℤ, |k| ≤ (N : ℤ) → ω k = ω' k) :
    |P.fRaw ω - P.fRaw ω'|
      ≤ (P.α⁻¹) ^ N + (1 + |P.β|) * |P.β| ^ (N + 1) / (1 - |P.β|) := by
  have hfut : ∀ k, k < N → futures ω k = futures ω' k := fun k hk =>
    h ((k : ℤ) + 1) (by rw [abs_of_nonneg (by positivity)]; omega)
  have hpast : ∀ m, m ≤ N → pasts ω m = pasts ω' m := fun m hm =>
    h (-(m : ℤ)) (by rw [abs_neg, abs_of_nonneg (by positivity)]; omega)
  have hsplit : P.fRaw ω - P.fRaw ω'
      = (piVal P.α (futures ω) - piVal P.α (futures ω'))
        - (P.wVal (pasts ω) - P.wVal (pasts ω')) := by rw [fRaw, fRaw]; ring
  rw [hsplit]
  exact (abs_sub _ _).trans
    (add_le_add (abs_piVal_sub_le_of_agree P.one_lt hfut) (P.abs_wVal_sub_le_of_agree hpast))

/-- **M1 Lemma 6, Hölder form.**  Let `θ ≥ 0` satisfy `2^θ ≤ α` and `2^θ |β| ≤ 1`; the
largest such is the note's exponent `θ = min(log α, log(1/ρ))/log 2`.  Then for words
agreeing on `[-N, N]` — i.e. at shift distance `d(ω, ω') ≤ 2^{-N}` —

`|F ω - F ω'| ≤ (1 + (1+|β|)/(1-|β|)) · d(ω, ω')^θ`,

so `F` is Hölder continuous of exponent `θ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem holder_fRaw {θ : ℝ} (hα : (2 : ℝ) ^ θ ≤ P.α) (hβ : (2 : ℝ) ^ θ * |P.β| ≤ 1)
    {ω ω' : Shift} {N : ℕ} (h : ∀ k : ℤ, |k| ≤ (N : ℤ) → ω k = ω' k) :
    |P.fRaw ω - P.fRaw ω'|
      ≤ (1 + (1 + |P.β|) / (1 - |P.β|)) * (((2 : ℝ) ^ (-(N : ℝ))) ^ θ) := by
  have hβ1 := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hq0 : (0 : ℝ) < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hkey : ((2 : ℝ) ^ (-(N : ℝ))) ^ θ = (((2 : ℝ) ^ θ)⁻¹) ^ N := by
    rw [← Real.rpow_natCast (((2 : ℝ) ^ θ)⁻¹) N, ← Real.rpow_neg_one ((2 : ℝ) ^ θ),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  have h1 : (P.α⁻¹) ^ N ≤ (((2 : ℝ) ^ θ)⁻¹) ^ N :=
    pow_le_pow_left₀ (inv_nonneg.mpr P.alpha_pos.le) (inv_anti₀ hq0 hα) N
  have hble : |P.β| ≤ ((2 : ℝ) ^ θ)⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hβ (le_of_lt (inv_pos.mpr hq0))
    rw [← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul, mul_one] at hm
    exact hm
  have h2 : |P.β| ^ (N + 1) ≤ (((2 : ℝ) ^ θ)⁻¹) ^ N :=
    (pow_le_pow_of_le_one hβ0 hβ1.le (Nat.le_succ N)).trans (pow_le_pow_left₀ hβ0 hble N)
  rw [hkey]
  calc |P.fRaw ω - P.fRaw ω'|
      ≤ (P.α⁻¹) ^ N + (1 + |P.β|) * |P.β| ^ (N + 1) / (1 - |P.β|) :=
        P.abs_fRaw_sub_le_of_agree h
  _ ≤ (((2 : ℝ) ^ θ)⁻¹) ^ N + (1 + |P.β|) * (((2 : ℝ) ^ θ)⁻¹) ^ N / (1 - |P.β|) := by gcongr
  _ = (1 + (1 + |P.β|) / (1 - |P.β|)) * (((2 : ℝ) ^ θ)⁻¹) ^ N := by field_simp

/-! ## The orbit identity -/

/-- On the zero-padded word the factor map computes the splitting of `BB61/Splitting.lean`:
`F(σⁿ ω̃) = t_n - S_n`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fRaw_iterate_padZ (ε : ℕ → Bool) (n : ℕ) :
    P.fRaw (shiftZ^[n] (padZ ε)) = tPart P.α ε n - P.sPart ε n := by
  rw [fRaw, futures_iterate_padZ, pasts_iterate_padZ, P.wVal_padWord, tPart]

/-- **M1 Lemma 6, the orbit identity.**  With `ω̃ = padZ ε` the word `ε` padded by zeros on
the non-positive coordinates, `F(σⁿ ω̃) = ξ αⁿ mod 1` for every `n ≥ 0`: the orbit of
fractional parts *is* the `F`-image of a single shift orbit. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fMap_iterate_padZ (ε : ℕ → Bool) (n : ℕ) :
    P.fMap (shiftZ^[n] (padZ ε)) = ((piVal P.α ε * P.α ^ n : ℝ) : AddCircle (1 : ℝ)) := by
  rw [fMap, P.fRaw_iterate_padZ]
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp (P.fract_split ε n)
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-z, ?_⟩
  simp only [neg_smul, zsmul_eq_mul, mul_one]
  linarith [hz]

end QuadSetup

end BB61
