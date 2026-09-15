/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Splitting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The finite-candidate covering and the avoided-interval engine

M2 Theorem 2 of `note-1061-M2.html`, quadratic case, in the *finite-candidate* form:

* truncating the future at depth `M` and the (zero-padded) past at depth `M'` places
  every fractional part `{ξ αⁿ}` within `δ = α^{-M} + (1+|β|)|β|^{M'}/(1-|β|)` of a
  **finite set of candidate values** — at most `2^M · 2^{M'} · (2K+1)` many, `K` bounding
  the integer part (`exists_cand_near`);
* if `card · 2δ < 1` the candidate intervals cannot cover `(0,1)`, and since their union
  is closed its complement contains an open interval `J ⊆ (0,1)`: **one interval,
  uniform in `ξ` and `n`, that every orbit misses at every time**
  (`exists_avoided_interval`).

Compared with the note, the intervals here are centred on candidate *points* rather than
cylinder images, and the integer part contributes the factor `2K+1` instead of the mod-1
tiling identity — a constant-factor loss that only shifts the certificate depth, not the
criterion.  The numeric certificate is discharged at `α = 2 + √5` in `BB61/RouteA.lean`;
`BB61/m2_verify.py` (checks T1a, T1c) is the numerical shadow.
-/

namespace BB61

open Finset MeasureTheory

section TCand

variable {α : ℝ}

/-- Depth-`M` truncation of the Cantor series. -/
noncomputable def tCand (α : ℝ) (w : ℕ → Bool) (M : ℕ) : ℝ :=
  (α - 1) * ∑ k ∈ Finset.range M, dR w k * (α⁻¹) ^ (k + 1)

/-- The truncation error of the Cantor series: `|π(w) - tCand| ≤ α^{-M}`
(M1 Lemma 1(iv), covering form). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_piVal_sub_tCand (hα : 1 < α) (w : ℕ → Bool) (M : ℕ) :
    |piVal α w - tCand α w M| ≤ (α⁻¹) ^ M := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have hr1 := inv_lt_one_of_one_lt hα
  have hf : Summable fun k : ℕ => dR w k * (α⁻¹) ^ (k + 1) := summable_dR_pow hr0 hr1 w
  have hsplit := hf.sum_add_tsum_nat_add M
  have htail0 : 0 ≤ ∑' i : ℕ, dR w (i + M) * (α⁻¹) ^ (i + M + 1) :=
    tsum_nonneg fun i => mul_nonneg (dR_nonneg w _) (pow_nonneg hr0 _)
  have htailsummable : Summable fun i : ℕ => dR w (i + M) * (α⁻¹) ^ (i + M + 1) :=
    (summable_nat_add_iff M).mpr hf
  have hgeo : Summable fun i : ℕ => (α⁻¹ : ℝ) ^ M * (α⁻¹) ^ (i + 1) :=
    (summable_geom_succ hr0 hr1).mul_left _
  have htailub : ∑' i : ℕ, dR w (i + M) * (α⁻¹) ^ (i + M + 1)
      ≤ (α⁻¹) ^ M * (α - 1)⁻¹ := by
    calc ∑' i : ℕ, dR w (i + M) * (α⁻¹) ^ (i + M + 1)
        ≤ ∑' i : ℕ, (α⁻¹ : ℝ) ^ M * (α⁻¹) ^ (i + 1) := by
          refine htailsummable.tsum_le_tsum (fun i => ?_) hgeo
          have h2 : (α⁻¹ : ℝ) ^ (i + M + 1) = (α⁻¹) ^ M * (α⁻¹) ^ (i + 1) := by
            rw [← pow_add]; ring_nf
          calc dR w (i + M) * (α⁻¹) ^ (i + M + 1) ≤ 1 * (α⁻¹) ^ (i + M + 1) :=
                mul_le_mul_of_nonneg_right (dR_le_one w _) (pow_nonneg hr0 _)
          _ = (α⁻¹) ^ M * (α⁻¹) ^ (i + 1) := by rw [one_mul, h2]
    _ = (α⁻¹) ^ M * ∑' i : ℕ, (α⁻¹ : ℝ) ^ (i + 1) := tsum_mul_left
    _ = (α⁻¹) ^ M * (α - 1)⁻¹ := by rw [tsum_inv_pow_succ hα]
  have hdiff : piVal α w - tCand α w M
      = (α - 1) * ∑' i : ℕ, dR w (i + M) * (α⁻¹) ^ (i + M + 1) := by
    rw [piVal, tCand, ← hsplit]
    ring
  rw [hdiff, abs_of_nonneg (mul_nonneg (by linarith) htail0)]
  calc (α - 1) * ∑' i : ℕ, dR w (i + M) * (α⁻¹) ^ (i + M + 1)
      ≤ (α - 1) * ((α⁻¹) ^ M * (α - 1)⁻¹) :=
        mul_le_mul_of_nonneg_left htailub (by linarith)
  _ = (α⁻¹) ^ M := by
        have hne : α - 1 ≠ 0 := by linarith
        field_simp

end TCand

namespace QuadSetup

variable (P : QuadSetup)

/-- Depth-`M'` truncation of the window series at a digit word `w`. -/
noncomputable def sCand (w : ℕ → Bool) (M' : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M', (P.β - 1) * P.β ^ m * dR w m

/-- The reversed, zero-padded past of the word at time `n`:
`padWord ε n = (ε_{n-1}, ε_{n-2}, …, ε_0, 0, 0, …)`. -/
def padWord (ε : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  fun m => decide (m < n) && ε (n - 1 - m)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_padWord (ε : ℕ → Bool) (n m : ℕ) :
    dR (padWord ε n) m = if m < n then dR ε (n - 1 - m) else 0 := by
  by_cases h : m < n <;> simp [dR, padWord, h]

/-- The window sum over the padded word, at any depth `N ≥ n`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sPart_eq_sum_pad (ε : ℕ → Bool) {n N : ℕ} (hN : n ≤ N) :
    P.sPart ε n = ∑ m ∈ Finset.range N, (P.β - 1) * P.β ^ m * dR (padWord ε n) m := by
  rw [← Finset.sum_range_add_sum_Ico _ hN]
  have h2 : ∑ m ∈ Finset.Ico n N, (P.β - 1) * P.β ^ m * dR (padWord ε n) m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have hmn : ¬ m < n := not_lt.mpr (Finset.mem_Ico.mp hm).1
      simp [dR_padWord, hmn]
  rw [h2, add_zero, P.sPart_eq_sum]
  exact Finset.sum_congr rfl fun m hm => by
    have hmn : m < n := Finset.mem_range.mp hm
    simp [dR_padWord, hmn]

/-- The truncation error of the window:
`|S_n - sCand (padWord ε n) M'| ≤ (1+|β|)|β|^{M'}/(1-|β|)` (M1 Lemma 3, covering form). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sPart_sub_sCand (ε : ℕ → Bool) (n M' : ℕ) :
    |P.sPart ε n - P.sCand (padWord ε n) M'|
      ≤ (1 + |P.β|) * |P.β| ^ M' / (1 - |P.β|) := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  set N := max n M' with hNdef
  have hnN : n ≤ N := le_max_left _ _
  have hMN : M' ≤ N := le_max_right _ _
  rw [P.sPart_eq_sum_pad ε hnN, sCand,
    ← Finset.sum_range_add_sum_Ico (fun m => (P.β - 1) * P.β ^ m * dR (padWord ε n) m) hMN,
    add_sub_cancel_left]
  calc |∑ m ∈ Finset.Ico M' N, (P.β - 1) * P.β ^ m * dR (padWord ε n) m|
      ≤ ∑ m ∈ Finset.Ico M' N, |(P.β - 1) * P.β ^ m * dR (padWord ε n) m| :=
        Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ m ∈ Finset.Ico M' N, (1 + |P.β|) * |P.β| ^ m := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul, abs_mul, abs_pow]
        have h1 : |P.β - 1| ≤ 1 + |P.β| := by
          rcases abs_cases P.β with ⟨h, _⟩ | ⟨h, _⟩ <;>
            rcases abs_cases (P.β - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith
        have h2 : |dR (padWord ε n) m| ≤ 1 := by
          rw [abs_of_nonneg (dR_nonneg _ _)]; exact dR_le_one _ _
        calc |P.β - 1| * |P.β| ^ m * |dR (padWord ε n) m|
            ≤ (1 + |P.β|) * |P.β| ^ m * |dR (padWord ε n) m| :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (by positivity)) (abs_nonneg _)
        _ ≤ (1 + |P.β|) * |P.β| ^ m * 1 :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (1 + |P.β|) * |P.β| ^ m := mul_one _
  _ ≤ (1 + |P.β|) * (|P.β| ^ M' * (1 - |P.β|)⁻¹) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ m ∈ Finset.Ico M' N, |P.β| ^ m
            = ∑ j ∈ Finset.range (N - M'), |P.β| ^ (M' + j) :=
              Finset.sum_Ico_eq_sum_range _ _ _
        _ = |P.β| ^ M' * ∑ j ∈ Finset.range (N - M'), |P.β| ^ j := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
        _ ≤ |P.β| ^ M' * (1 - |P.β|)⁻¹ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              calc ∑ j ∈ Finset.range (N - M'), |P.β| ^ j
                  ≤ ∑' j : ℕ, |P.β| ^ j :=
                    (summable_geometric_of_lt_one hβ0 hβ).sum_le_tsum _
                      (fun j _ => by positivity)
              _ = (1 - |P.β|)⁻¹ := tsum_geometric_of_lt_one hβ0 hβ
  _ = (1 + |P.β|) * |P.β| ^ M' / (1 - |P.β|) := by ring

/-! ## The finite candidate set -/

/-- Extend a finite digit pattern by zeros. -/
def extendW (M : ℕ) (w : Fin M → Bool) : ℕ → Bool :=
  fun k => if h : k < M then w ⟨k, h⟩ else false

theorem tCand_extendW (α : ℝ) (w : ℕ → Bool) (M : ℕ) :
    tCand α (extendW M fun i : Fin M => w i) M = tCand α w M := by
  unfold tCand
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have h : k < M := Finset.mem_range.mp hk
  simp [extendW, dR, h]

theorem sCand_extendW (w : ℕ → Bool) (M' : ℕ) :
    P.sCand (extendW M' fun i : Fin M' => w i) M' = P.sCand w M' := by
  unfold sCand
  refine Finset.sum_congr rfl fun m hm => ?_
  have h : m < M' := Finset.mem_range.mp hm
  simp [extendW, dR, h]

/-- The finite set of candidate values: one for each pair of digit windows and each
integer part in `[-K, K]`.  It depends only on `(α, a, b, M, M', K)` — **not** on the
word `ε` or the time `n`: this is what makes the avoided interval uniform. -/
noncomputable def cands (M M' K : ℕ) : Finset ℝ :=
  ((Finset.univ : Finset ((Fin M → Bool) × (Fin M' → Bool))) ×ˢ
      Finset.Icc (-(K : ℤ)) (K : ℤ)).image
    fun p => tCand P.α (extendW M p.1.1) M - P.sCand (extendW M' p.1.2) M' - (p.2 : ℝ)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_cands_le (M M' K : ℕ) :
    (P.cands M M' K).card ≤ 2 ^ M * 2 ^ M' * (2 * K + 1) := by
  refine le_trans Finset.card_image_le (le_of_eq ?_)
  rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Int.card_Icc]
  have h : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rw [h]

/-- The covering radius `δ = α^{-M} + (1+|β|)|β|^{M'}/(1-|β|)`. -/
noncomputable def delta (M M' : ℕ) : ℝ :=
  (P.α⁻¹) ^ M + (1 + |P.β|) * |P.β| ^ M' / (1 - |P.β|)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem delta_nonneg (M M' : ℕ) : 0 ≤ P.delta M M' := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have h1 : (0 : ℝ) ≤ (P.α⁻¹) ^ M := pow_nonneg (inv_nonneg.mpr P.alpha_pos.le) M
  have h2 : (0 : ℝ) ≤ (1 + |P.β|) * |P.β| ^ M' / (1 - |P.β|) := by positivity
  rw [delta]; linarith

/-- **The cover lemma** (M2 Theorem 2, candidate form): every fractional part of the
orbit lies within `δ` of one of the candidates. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_cand_near (M M' K : ℕ)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ)) (ε : ℕ → Bool) (n : ℕ) :
    ∃ f ∈ P.cands M M' K,
      |Int.fract (piVal P.α ε * P.α ^ n) - f| ≤ P.delta M M' := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  set x := tPart P.α ε n - P.sPart ε n with hx
  have hfr : Int.fract x = x - (⌊x⌋ : ℝ) := by
    have h := Int.floor_add_fract x; linarith
  -- bounds on x and on its floor
  have ht0 := P.tPart_nonneg ε n
  have ht1 := P.tPart_le_one ε n
  have hS := abs_le.mp (P.abs_sPart_le ε n)
  have hxlow : -((1 + |P.β|) / (1 - |P.β|)) ≤ x := by rw [hx]; linarith [hS.2]
  have hxhigh : x ≤ 1 + (1 + |P.β|) / (1 - |P.β|) := by rw [hx]; linarith [hS.1]
  have hk1 : (⌊x⌋ : ℝ) ≤ (K : ℝ) := le_trans (Int.floor_le x) (by linarith)
  have hk2 : -(K : ℝ) ≤ (⌊x⌋ : ℝ) := by
    have h := Int.lt_floor_add_one x
    linarith
  have hkmem : ⌊x⌋ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast hk2
    · exact_mod_cast hk1
  refine ⟨tCand P.α (extendW M fun i : Fin M => shift ε n i) M
      - P.sCand (extendW M' fun i : Fin M' => padWord ε n i) M' - ((⌊x⌋ : ℤ) : ℝ),
    Finset.mem_image.mpr
      ⟨⟨⟨fun i => shift ε n (i : ℕ), fun i => padWord ε n (i : ℕ)⟩, ⌊x⌋⟩,
        Finset.mem_product.mpr ⟨Finset.mem_univ _, hkmem⟩, rfl⟩, ?_⟩
  rw [P.fract_split, ← hx, hfr, tCand_extendW, P.sCand_extendW]
  have h1 : |tPart P.α ε n - tCand P.α (shift ε n) M| ≤ (P.α⁻¹) ^ M := by
    rw [tPart]
    exact abs_piVal_sub_tCand P.one_lt _ M
  have h2 := P.abs_sPart_sub_sCand ε n M'
  have hsplit : x - (⌊x⌋ : ℝ) - (tCand P.α (shift ε n) M - P.sCand (padWord ε n) M' - (⌊x⌋ : ℝ))
      = (tPart P.α ε n - tCand P.α (shift ε n) M) - (P.sPart ε n - P.sCand (padWord ε n) M') := by
    rw [hx]; ring
  rw [hsplit]
  have htri : |(tPart P.α ε n - tCand P.α (shift ε n) M)
        - (P.sPart ε n - P.sCand (padWord ε n) M')|
      ≤ |tPart P.α ε n - tCand P.α (shift ε n) M|
        + |P.sPart ε n - P.sCand (padWord ε n) M'| := by
    have h := abs_add_le (tPart P.α ε n - tCand P.α (shift ε n) M)
      (-(P.sPart ε n - P.sCand (padWord ε n) M'))
    rw [abs_neg] at h
    calc |(tPart P.α ε n - tCand P.α (shift ε n) M)
          - (P.sPart ε n - P.sCand (padWord ε n) M')|
        = |(tPart P.α ε n - tCand P.α (shift ε n) M)
          + -(P.sPart ε n - P.sCand (padWord ε n) M')| := by rw [sub_eq_add_neg]
    _ ≤ _ := h
  calc |(tPart P.α ε n - tCand P.α (shift ε n) M)
        - (P.sPart ε n - P.sCand (padWord ε n) M')|
      ≤ |tPart P.α ε n - tCand P.α (shift ε n) M|
        + |P.sPart ε n - P.sCand (padWord ε n) M'| := htri
  _ ≤ (P.α⁻¹) ^ M + (1 + |P.β|) * |P.β| ^ M' / (1 - |P.β|) := add_le_add h1 h2
  _ = P.delta M M' := rfl

/-! ## The avoided-interval engine -/

/-- **The Route A engine** (M2 Theorem 2, degree 2): if the numeric certificate
`(2^M · 2^{M'} · (2K+1)) · 2δ < 1` holds at some depths `(M, M')` and integer-part
bound `K`, then there is **one open interval `J ⊆ (0,1)`, uniform in `ξ ∈ C(α)` and
`n`, that every orbit `({ξ αⁿ})_n` misses at every time**.  In particular no
`(ξ αⁿ)` with `ξ ∈ C(α)` is dense — a fortiori none is u.d. mod one. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_avoided_interval (M M' K : ℕ)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ))
    (hcert : ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M') < 1) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  have hδ0 := P.delta_nonneg M M'
  set U : Set ℝ :=
    ⋃ f ∈ P.cands M M' K, Set.Icc (f - P.delta M M') (f + P.delta M M') with hU
  have hUclosed : IsClosed U := by
    refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun f _ => isClosed_Icc
  have hUvol : volume U
      ≤ ENNReal.ofReal (((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M')) := by
    calc volume U
        ≤ ∑ f ∈ P.cands M M' K,
            volume (Set.Icc (f - P.delta M M') (f + P.delta M M')) :=
          measure_biUnion_finset_le _ _
    _ = ∑ _f ∈ P.cands M M' K, ENNReal.ofReal (2 * P.delta M M') := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Real.volume_Icc]
          congr 1; ring
    _ = ((P.cands M M' K).card : ENNReal) * ENNReal.ofReal (2 * P.delta M M') := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ENNReal)
          * ENNReal.ofReal (2 * P.delta M M') := by
          gcongr
          exact_mod_cast P.card_cands_le M M' K
    _ = ENNReal.ofReal (((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ)
          * (2 * P.delta M M')) := by
          rw [ENNReal.ofReal_mul
              (show (0 : ℝ) ≤ ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) by positivity),
            ENNReal.ofReal_natCast]
  have hnotsub : ¬ Set.Ioo (0 : ℝ) 1 ⊆ U := by
    intro hsub
    have h1 : (1 : ENNReal) ≤ volume U := by
      calc (1 : ENNReal) = volume (Set.Ioo (0 : ℝ) 1) := by
            rw [Real.volume_Ioo]; norm_num
      _ ≤ volume U := measure_mono hsub
    have h2 : volume U < 1 := by
      refine lt_of_le_of_lt hUvol ?_
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hcert
    exact absurd h1 (not_le.mpr h2)
  obtain ⟨x₀, hx₀Ioo, hx₀U⟩ : ∃ x₀, x₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₀ ∉ U := by
    by_contra h
    push Not at h
    exact hnotsub fun y hy => h y hy
  have hopen : IsOpen (Set.Ioo (0 : ℝ) 1 ∩ Uᶜ) := isOpen_Ioo.inter hUclosed.isOpen_compl
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hopen x₀ ⟨hx₀Ioo, hx₀U⟩
  refine ⟨x₀, r, hr0, ?_, ?_⟩
  · intro y hy
    have hmem : y ∈ Metric.ball x₀ r := by rw [Real.ball_eq_Ioo]; exact hy
    exact (hball hmem).1
  · intro ε n hy
    have hyU : Int.fract (piVal P.α ε * P.α ^ n) ∈ U := by
      obtain ⟨f, hf, hnear⟩ := P.exists_cand_near M M' K hK ε n
      have habs := abs_le.mp hnear
      refine Set.mem_biUnion hf ?_
      rw [Set.mem_Icc]
      constructor <;> linarith [habs.1, habs.2]
    have hmem : Int.fract (piVal P.α ε * P.α ^ n) ∈ Metric.ball x₀ r := by
      rw [Real.ball_eq_Ioo]; exact hy
    exact (hball hmem).2 hyU

end QuadSetup

end BB61
