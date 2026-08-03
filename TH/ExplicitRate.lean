/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.KernelReduction
import BB13.MahlerFrame
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A14(i): the explicit-rate upgrade of M4, and what the quantitative lane can supply

Angle **A14**, item (i) of `plans/plan-A1+.html` §5 (work package W10): rework the counting in
`TH.superlinear_of_kernel` so that the conclusion carries a *rate* — an explicit `f` with
`p_T(k) ≥ k · f k` — and test whether BB13's quantitative line-cover machinery can supply the
input that such a rate consumes.

`TH.complexity_superlinear` (M4) is ineffective for one reason: it consumes `Kernel`, i.e. the
*finiteness* of `kernelViolators θ`, and finiteness yields a ceiling `M` on the violators with no
handle on its size.  This file splits that step in two.

## Part 1 — the reduction, made explicit (std3)

`KernelCeiling B` asks for an **explicit ceiling**: every (K)-violating pair at scale `θ` has
`c ≤ B θ`.  Existentially quantified it is *equivalent* to `Kernel`
(`exists_kernelCeiling_iff_kernel` — finiteness bounds each violator set and choice does the rest),
so the whole content of an effective M4 is the **naming** of a `B`, and that is exactly what the
pigeonhole reduction consumes:

* `complexity_gt_of_violatorBound` — the core of `superlinear_of_kernel` with the ceiling as a
  parameter: at the Bernoulli scale of slope `C`, any `k > M` has `p_T(k) > C·k`;
* `rate B` — the explicit rate function `Nat.findGreatest (fun C => B (bScale C) < k) k`;
* `rate_mul_lt_complexity` — **`k · rate B k < p_T(k)`**, the rate form of M4;
* `tendsto_rate_atTop` — `rate B → ∞` (unconditionally in `B`: it is the *statement* `p_T(k)/k → ∞`
  that needs the ceiling, not the divergence of the rate function).

So "M4 with a rate" is precisely "M4 with an explicit kernel ceiling", and the rate is a
transparent inverse of the ceiling: `f(k) = max {C ≤ k : B(θ(C)) < k}` with
`θ(C) = 1 − (1/3)/(C+2)`.

## Part 2 — what BB13 supplies, and at what scale (`std3 + BugeaudEvertse.ridout_line_cover`)

A kernel pair is a *multiplied* Mahler failure: `(3/2)^c − (3/2)^a = δ_g · (3/2)^a` with
`δ_g = (3/2)^g − 1`, `g = c − a`, so

  `(a, c) ∈ kernelViolators θ  ⟹  BB13.IsFailureMul δ_g 3 2 θ a`

(`isFailureMul_of_mem_kernelViolators`), and `BB13.mahler_line_cover` — the general multiplied
line cover, uniform in the multiplier — puts the violators of **one fixed gap** on at most
`K(ε(3,θ))` lines once `a ≥ g + 1` clears the height threshold `3^a > 2·H(δ_g)`
(`ratHeight_gapMul_le`, `kernel_gap_lines_card_le`).  The threshold `a ≥ g+1` is not an artifact:
it is the "late occurrence" band `a ≳ c/2`, the complement of the huge-gap slice that
`TH.GapSlices` handles by other means.

The scale the reduction demands is `θ(C) → 1`, i.e. `ε → 0`, so the size of the cover matters:
`epsilon_bScale_ge` gives `ε(3, θ(C)) ≥ 1/(4(C+2))`, hence `1 + 1/ε ≤ 4C + 9` and the line count
at slope `C` is bounded by an explicit **cubic-times-log** polynomial in `C`
(`lineBound_bScale_le`).  The cover side therefore scales perfectly well with the rate one wants.

## The verdict: the lane cannot supply a ceiling (W10 no-go)

What the reduction consumes is a *ceiling*; what the quantitative literature supplies is a *count
of lines*, and — as `BB13/FailureCount.lean` already records for its own headline problem — the
passage from lines to solutions is [BE08] Rem. 7.4, open.  Two independent gaps, both named here:

1. **Per-line height** (the BB13 gap, inherited verbatim): a bound on the number of lines never
   bounds the position of a solution.
2. **Multiplier uniformity** (new, specific to the two-point kernel): `mahler_line_cover` is a
   statement about one fixed `δ`.  The kernel ranges over *all* gaps `g`, hence over infinitely
   many multipliers `δ_g`, and the line families of different `δ` are unrelated.  Even granting
   gap 1 — finitely many violators for each fixed gap — no ceiling follows:
   `gapwiseFinite_not_ceiling` exhibits a set of pairs with exactly one element per gap and
   unbounded second coordinate.

So A14(i) is **blocked, and blocked at a named interface**: an explicit rate for M4 is equivalent
to an explicit kernel ceiling (Part 1), and the BE08 lane is structurally the wrong shape to
produce one, in the same way and for the same reason that it cannot produce an unconditional
constant for Problem 10.13.  What Part 2 *does* buy is the first quantitative statement about the
M4 kernel that does not go through the qualitative Subspace theorem.

## Contents

* `TH.bScale` — the Bernoulli scale `θ(C)` of the reduction, as a function.
* `TH.KernelCeiling`, `TH.exists_kernelCeiling_iff_kernel` — the quantitative kernel (explicit
  violator ceiling), and the fact that only its *naming*, not its existence, is new.
* `TH.complexity_gt_of_violatorBound`, `TH.complexity_gt_of_kernelCeiling` — the explicit reduction.
* `TH.rate`, `TH.rate_mul_lt_complexity`, `TH.tendsto_rate_atTop` — **the rate form of M4**.
* `TH.gapMul`, `TH.isFailureMul_of_mem_kernelViolators` — the kernel-to-Mahler bridge.
* `TH.kernel_gap_lines_card_le` — the fixed-gap line cover for the kernel.
* `TH.epsilon_bScale_ge`, `TH.lineBound_bScale_le` — the cover's size at the reduction's scale.
* `TH.gapwiseFinite_not_ceiling` — the no-go: per-gap finiteness does not give a ceiling.

## References

* [A1plus] `plans/plan-A1+.html` (this repository, 2026-08): §5 A14(i), §7.3 W10.
* [M4A3] `plans/plan-M4A3.html` (this repository, 2026-07): §4 (Stage 1), §9.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Cor. 5.2 (the line count), Rem. 7.4 (the per-line problem).
-/

namespace TH

open Filter

/-! ## Part 1 — the reduction with an explicit ceiling (std3) -/

/-- The **Bernoulli scale of slope `C`**: `θ(C) = 1 − (1/3)/(C+2)`, the rational kernel scale that
`TH.exists_pow_ge` produces for `r = 2/3` and `N = C + 2`.  Made a function here because the
explicit rate has to name it. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
def bScale (C : ℕ) : ℚ := 1 - (1 / 3) / ((C : ℚ) + 2)

@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
lemma bScale_pos (C : ℕ) : 0 < bScale C := by
  have hC : (0 : ℚ) < (C : ℚ) + 2 := by positivity
  have h : (1 / 3 : ℚ) / ((C : ℚ) + 2) ≤ 1 / 3 :=
    div_le_self (by norm_num) (by linarith)
  rw [bScale]; linarith

@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
lemma bScale_lt_one (C : ℕ) : bScale C < 1 := by
  have hC : (0 : ℚ) < (C : ℚ) + 2 := by positivity
  have h : 0 < (1 / 3 : ℚ) / ((C : ℚ) + 2) := by positivity
  rw [bScale]; linarith

/-- The Bernoulli certificate at the named scale: `(2/3) ≤ θ(C)^{C+2}`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
lemma two_thirds_le_bScale_pow (C : ℕ) : (2 / 3 : ℚ) ≤ bScale C ^ (C + 2) := by
  have hN0 : (0 : ℚ) < ((C : ℚ) + 2) := by positivity
  have hdivpos : 0 < (1 / 3 : ℚ) / ((C : ℚ) + 2) := by positivity
  have hdivle : (1 / 3 : ℚ) / ((C : ℚ) + 2) ≤ 1 / 3 :=
    div_le_self (by norm_num) (by linarith)
  have hb := one_add_mul_le_pow (a := -((1 / 3 : ℚ) / ((C : ℚ) + 2))) (by linarith) (C + 2)
  have hcast : ((C + 2 : ℕ) : ℚ) = (C : ℚ) + 2 := by push_cast; ring
  rw [hcast] at hb
  calc (2 / 3 : ℚ) = 1 + ((C : ℚ) + 2) * (-((1 / 3 : ℚ) / ((C : ℚ) + 2))) := by
        field_simp
        norm_num
    _ ≤ (1 + -((1 / 3 : ℚ) / ((C : ℚ) + 2))) ^ (C + 2) := hb
    _ = bScale C ^ (C + 2) := by rw [bScale, ← sub_eq_add_neg]

/-- **The quantitative kernel**: an *explicit* ceiling `B θ` on the (K)-violating pairs at scale
`θ`.  This is the input an effective M4 consumes; `TH.Kernel` is its qualitative shadow
(`kernel_of_kernelCeiling`), and the whole content of A14(i) is whether any Diophantine lane can
produce a `B`.  [A1plus] §5 A14(i). -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
def KernelCeiling (B : ℚ → ℕ) : Prop :=
  ∀ θ : ℚ, 0 < θ → θ < 1 → ∀ p ∈ kernelViolators θ, p.2 ≤ B θ

/-- A ceiling implies the kernel (K): boundedness of the second coordinate is finiteness here. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem kernel_of_kernelCeiling {B : ℚ → ℕ} (hB : KernelCeiling B) : Kernel := by
  intro θ hθ0 hθ1
  refine Set.Finite.subset
    (Set.finite_Icc ((0 : ℕ), (0 : ℕ)) ((B θ, B θ) : ℕ × ℕ)) ?_
  intro p hp
  have hc : p.2 ≤ B θ := hB θ hθ0 hθ1 p hp
  have hac : p.1 < p.2 := hp.2.1
  exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, ⟨by omega, hc⟩⟩

/-- **Where the content sits**: *existentially* quantified, a ceiling is no more than the kernel —
finiteness bounds each violator set, and choice packages the bounds into a function.  So A14(i) is
not asking for a stronger hypothesis than (K); it is asking for a **named** `B`, and it is exactly
that naming which the effective statement `rate_mul_lt_complexity` consumes. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem exists_kernelCeiling_iff_kernel : (∃ B : ℚ → ℕ, KernelCeiling B) ↔ Kernel := by
  constructor
  · rintro ⟨B, hB⟩
    exact kernel_of_kernelCeiling hB
  · intro hK
    have h : ∀ θ : ℚ, ∃ M : ℕ, 0 < θ → θ < 1 → ∀ p ∈ kernelViolators θ, p.2 ≤ M := by
      intro θ
      by_cases hθ : 0 < θ ∧ θ < 1
      · obtain ⟨M, hM⟩ := ((hK θ hθ.1 hθ.2).image Prod.snd).bddAbove
        exact ⟨M, fun _ _ p hp => hM (Set.mem_image_of_mem _ hp)⟩
      · exact ⟨0, fun h0 h1 => absurd ⟨h0, h1⟩ hθ⟩
    choose B hB using h
    exact ⟨B, fun θ h0 h1 => hB θ h0 h1⟩

/-- **The reduction with the ceiling exposed** — the body of `TH.superlinear_of_kernel`, with the
bound `M` on the violators as a parameter instead of an existential extracted from finiteness.
Every `k > M` beats the slope `C` whose Bernoulli certificate is `hθpow`. -/
@[category research solved, AMS 11 68, ref "A1plus" "M4A3", group "weyl_a14_explicitrate"]
theorem complexity_gt_of_violatorBound {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {C M k : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ (C + 2))
    (hM : ∀ p ∈ kernelViolators θ, p.2 ≤ M) (hk : M < k) :
    C * k < complexity k := by
  by_contra hle
  have hple : complexity k ≤ C * k := Nat.not_lt.mp hle
  have hncard : complexity k = (factorSet_finite k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite k)
  have hcard : ((factorSet_finite k).toFinset).card
      < (Finset.Icc 2 (C * k + 2)).card := by
    rw [Nat.card_Icc, ← hncard]
    have harith : C * k + 2 + 1 - 2 = C * k + 1 := by
      generalize C * k = P
      omega
    rw [harith]
    exact Nat.lt_succ_of_le hple
  have hmaps : ∀ a ∈ Finset.Icc 2 (C * k + 2),
      factor a k ∈ (factorSet_finite k).toFinset := fun a _ => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hx hy
  have hmem : ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ C * k + 2 ∧ IsRepetition a c k := by
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, hx.1, h, hy.2, factor_eq_iff.mp hfeq⟩
    · have hlt : y < x := by omega
      exact ⟨y, x, hy.1, hlt, hx.2, factor_eq_iff.mp hfeq.symm⟩
  obtain ⟨a, c, ha, hac, hc, hrep⟩ := hmem
  have hck : c ≤ (C + 2) * k := by
    have h2k : 2 ≤ 2 * k := by omega
    calc c ≤ C * k + 2 := hc
      _ ≤ C * k + 2 * k := Nat.add_le_add_left h2k _
      _ = (C + 2) * k := by ring
  have hkv := mem_kernelViolators_of_repetition hθ0 hθ1 hθpow ha hac hck hrep
  have hcM : c ≤ M := hM (a, c) hkv
  have hbound := repetition_linear_bound ha hac hrep
  omega

/-- **The explicit threshold**: with a kernel ceiling `B`, the slope `C` is beaten by every
`k > B(θ(C))` — the effective form of M4, ceiling-in/threshold-out. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem complexity_gt_of_kernelCeiling {B : ℚ → ℕ} (hB : KernelCeiling B) (C k : ℕ)
    (hk : B (bScale C) < k) : C * k < complexity k :=
  complexity_gt_of_violatorBound (bScale_pos C) (bScale_lt_one C) (two_thirds_le_bScale_pow C)
    (hB _ (bScale_pos C) (bScale_lt_one C)) hk

/-- **The rate function attached to a ceiling** `B`: the largest slope `C ≤ k` whose threshold
`B(θ(C))` has already been passed at `k`.  This is the `f` of `p_T(k) ≥ k · f(k)`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
def rate (B : ℚ → ℕ) (k : ℕ) : ℕ := Nat.findGreatest (fun C => B (bScale C) < k) k

/-- **M4 with a rate**: `k · rate B k < p_T(k)` for every `k` past the ceiling of slope `0`.
The rate is explicit in `B` — no existential is extracted anywhere in the chain. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem rate_mul_lt_complexity {B : ℚ → ℕ} (hB : KernelCeiling B) {k : ℕ}
    (hk : B (bScale 0) < k) : rate B k * k < complexity k :=
  complexity_gt_of_kernelCeiling hB _ k
    (Nat.findGreatest_spec (P := fun C => B (bScale C) < k) (Nat.zero_le k) hk)

/-- The rate function diverges — for *any* `B`.  The content of A14(i) is therefore located
exactly where it should be: in `rate_mul_lt_complexity`, i.e. in the existence of the ceiling,
not in the shape of the rate. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem tendsto_rate_atTop (B : ℚ → ℕ) : Tendsto (rate B) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun C => ⟨max C (B (bScale C) + 1), fun k hk => ?_⟩
  have hCk : C ≤ k := le_trans (le_max_left _ _) hk
  have hBk : B (bScale C) < k := by
    have := le_trans (le_max_right C (B (bScale C) + 1)) hk
    omega
  exact Nat.le_findGreatest hCk hBk

/-- The qualitative statement is recovered: a ceiling gives M4 (`TH.Superlinear`). -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem superlinear_of_kernelCeiling {B : ℚ → ℕ} (hB : KernelCeiling B) : Superlinear :=
  fun C => ⟨B (bScale C) + 1, fun k hk => complexity_gt_of_kernelCeiling hB C k (by omega)⟩

/-! ## Part 2 — the supply side: the kernel as a multiplied Mahler problem

Footprint of this section: `std3 + BugeaudEvertse.ridout_line_cover` (through
`BB13.mahler_line_cover`), the quantitative lane — *not* `Subspace.evertseSchlickewei`, the
qualitative lane on which `TH.complexity_superlinear` rests. -/

/-- The **multiplier of gap `g`**: `δ_g = (3/2)^g − 1`, so that a kernel pair with gap `g` is a
failure of the multiplied sequence `δ_g (3/2)^a`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
def gapMul (g : ℕ) : ℚ := (3 / 2 : ℚ) ^ g - 1

@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
lemma orbit_sub_eq (a g : ℕ) :
    (3 / 2 : ℚ) ^ (a + g) - (3 / 2 : ℚ) ^ a = gapMul g * (3 / 2 : ℚ) ^ a := by
  rw [gapMul, pow_add]; ring

/-- **The kernel-to-Mahler bridge**: a (K)-violating pair `(a, c)` at scale `θ` is a failure of
`‖δ_g (3/2)^a‖ < θ^a` for the gap multiplier `δ_g`, `g = c − a`.  The strict inequality is free:
the violator bound is `θ^c` and `c > a`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_explicitrate"]
theorem isFailureMul_of_mem_kernelViolators {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c : ℕ}
    (h : (a, c) ∈ kernelViolators θ) :
    BB13.IsFailureMul (gapMul (c - a)) 3 2 (θ : ℝ) a := by
  obtain ⟨-, hac, hd⟩ := h
  have hca : c = a + (c - a) := by omega
  have hq : Rat.distToNearestInt (gapMul (c - a) * (3 / 2 : ℚ) ^ a) ≤ θ ^ c := by
    rw [← orbit_sub_eq, ← hca]; exact hd
  have hlt : (θ : ℚ) ^ c < θ ^ a := pow_lt_pow_right_of_lt_one₀ hθ0 hθ1 hac
  have harg : (gapMul (c - a) : ℝ) * (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a
      = ((gapMul (c - a) * (3 / 2 : ℚ) ^ a : ℚ) : ℝ) := by push_cast; ring
  rw [BB13.IsFailureMul, harg, distToNearestInt_ratCast]
  exact_mod_cast lt_of_le_of_lt hq hlt

/-- The height of the gap multiplier: `H(δ_g) ≤ 3^g`.  (Exactly: `δ_g = (3^g − 2^g)/2^g` in lowest
terms, so `H = 3^g − 2^g` for `g ≥ 2`; the crude bound is what the threshold needs.) -/
@[category research solved, AMS 11 68, ref "A1plus" "BE08", group "weyl_a14_explicitrate"]
theorem ratHeight_gapMul_le (g : ℕ) : BugeaudEvertse.ratHeight (gapMul g) ≤ 3 ^ g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · norm_num [BugeaudEvertse.ratHeight, gapMul]
  have h2ne : ((2 : ℤ) ^ g) ≠ 0 := by positivity
  have hrep : gapMul g = Rat.divInt ((3 : ℤ) ^ g - (2 : ℤ) ^ g) ((2 : ℤ) ^ g) := by
    rw [Rat.divInt_eq_div, gapMul, div_pow]
    push_cast
    field_simp
  have hden : (gapMul g).den ≤ 2 ^ g := by
    have hdvd : ((gapMul g).den : ℤ) ∣ (2 : ℤ) ^ g := by
      rw [hrep]; exact Rat.den_dvd _ _
    have hle : ((gapMul g).den : ℤ) ≤ (2 : ℤ) ^ g := Int.le_of_dvd (by positivity) hdvd
    exact_mod_cast hle
  have hnum : (gapMul g).num.natAbs ≤ 3 ^ g := by
    have hdvd : (gapMul g).num ∣ (3 : ℤ) ^ g - (2 : ℤ) ^ g := by
      rw [hrep]; exact Rat.num_dvd _ h2ne
    have hlt : (2 : ℤ) ^ g < 3 ^ g := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have hne : ((3 : ℤ) ^ g - (2 : ℤ) ^ g) ≠ 0 := by omega
    have hle : (gapMul g).num.natAbs ≤ ((3 : ℤ) ^ g - (2 : ℤ) ^ g).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)
    have hb : ((3 : ℤ) ^ g - (2 : ℤ) ^ g).natAbs ≤ 3 ^ g := by
      have h0 : (0 : ℤ) ≤ (3 : ℤ) ^ g - (2 : ℤ) ^ g := by linarith
      have h2pos : (0 : ℤ) < (2 : ℤ) ^ g := by positivity
      zify
      rw [abs_of_nonneg h0]
      linarith
    exact le_trans hle hb
  rw [BugeaudEvertse.ratHeight]
  exact max_le hnum (le_trans hden (Nat.pow_le_pow_left (by norm_num) g))

/-- **The fixed-gap line cover for the kernel** — A14(i)'s supply statement.  For each scale `θ`
and each gap `g`, the (K)-violating pairs of gap `g` whose earlier occurrence clears the height
threshold (`a ≥ g + 1`) and the rate threshold (`θ^a < 1/16`) send their frame points into a set of
at most `K(ε(3,θ))` slopes.

This is the quantitative analogue of `TH.GapSlices`' bounded-gap finiteness, on the [BE08] lane
instead of the qualitative Subspace lane.  What it does *not* give is a ceiling: see
`gapwiseFinite_not_ceiling`. -/
@[category research solved, AMS 11 68, ref "A1plus" "BE08", group "weyl_a14_explicitrate"]
theorem kernel_gap_lines_card_le {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (g : ℕ) :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound (BB13.epsilon 3 (θ : ℝ)) ∧
      ∀ a c : ℕ, (a, c) ∈ kernelViolators θ → c = a + g → g + 1 ≤ a →
        ((θ : ℝ) ^ a < 1 / 16) → BB13.linePointMul (gapMul g) 3 2 a ∈ R := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨R, hcard, hR⟩ := BB13.mahler_line_cover (gapMul g) 3 2 (θ : ℝ) (by norm_num)
    (by norm_num) (by norm_num) hθ0' hθ1'
  refine ⟨R, hcard, fun a c hmem hc hga hthr => ?_⟩
  have hgca : c - a = g := by omega
  have hfail : BB13.IsFailureMul (gapMul g) 3 2 (θ : ℝ) a := by
    have := isFailureMul_of_mem_kernelViolators hθ0 hθ1 hmem
    rwa [hgca] at this
  refine hR a hthr ?_ hfail
  -- height threshold `2·H(δ_g) < 3^a`, from `H(δ_g) ≤ 3^g` and `a ≥ g + 1`
  have hH : (BugeaudEvertse.ratHeight (gapMul g) : ℝ) ≤ (3 : ℝ) ^ g := by
    exact_mod_cast ratHeight_gapMul_le g
  have hmono : (3 : ℝ) ^ (g + 1) ≤ (3 : ℝ) ^ a := by
    apply pow_le_pow_right₀ (by norm_num) hga
  calc 2 * (BugeaudEvertse.ratHeight (gapMul g) : ℝ) ≤ 2 * (3 : ℝ) ^ g := by linarith
    _ < (3 : ℝ) ^ (g + 1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) g]
    _ ≤ (3 : ℝ) ^ a := hmono
    _ = ((3 : ℕ) : ℝ) ^ a := by norm_num

/-! ### The size of the cover at the reduction's scale

The reduction needs slope `C` at scale `θ(C) = 1 − (1/3)/(C+2)`, which tends to `1`, so the gap
exponent `ε(3, θ(C))` tends to `0` and the line count grows.  It grows only polynomially. -/

/-- `ε(3, θ(C)) ≥ 1/(4(C+2))`: the gap exponent at the Bernoulli scale decays no faster than
`1/C`.  Uses `log x ≤ x − 1` and `3·log 3 < 4`. -/
@[category research solved, AMS 11 68, ref "A1plus" "BE08", group "weyl_a14_explicitrate"]
theorem epsilon_bScale_ge (C : ℕ) :
    1 / (4 * ((C : ℝ) + 2)) ≤ BB13.epsilon 3 ((bScale C : ℚ) : ℝ) := by
  have hC2 : (0 : ℝ) < (C : ℝ) + 2 := by positivity
  have hθ : ((bScale C : ℚ) : ℝ) = 1 - (1 / 3) / ((C : ℝ) + 2) := by
    rw [bScale]; push_cast; ring
  have hθ0 : (0 : ℝ) < ((bScale C : ℚ) : ℝ) := by exact_mod_cast bScale_pos C
  have hlog3 : Real.log 3 ≤ 1.1 := by
    have h := abs_le.mp Real.log_three_near_10
    norm_num at h ⊢
    linarith [h.2]
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- `−log θ ≥ 1 − θ = (1/3)/(C+2)`
  have hkey : (1 / 3) / ((C : ℝ) + 2) ≤ -Real.log ((bScale C : ℚ) : ℝ) := by
    have h1 : Real.log ((bScale C : ℚ) : ℝ) ≤ ((bScale C : ℚ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hθ0
    have h2 : ((bScale C : ℚ) : ℝ) - 1 = -((1 / 3) / ((C : ℝ) + 2)) := by rw [hθ]; ring
    rw [h2] at h1
    linarith
  have hlogeq : Real.log (1 / ((bScale C : ℚ) : ℝ)) = -Real.log ((bScale C : ℚ) : ℝ) := by
    rw [one_div, Real.log_inv]
  have hfin : 1 / (4 * ((C : ℝ) + 2)) * Real.log 3 ≤ (1 / 3) / ((C : ℝ) + 2) := by
    have hrw : 1 / (4 * ((C : ℝ) + 2)) * Real.log 3
        = Real.log 3 / 4 * (1 / ((C : ℝ) + 2)) := by field_simp
    have hpos : (0 : ℝ) < 1 / ((C : ℝ) + 2) := by positivity
    rw [hrw]
    calc Real.log 3 / 4 * (1 / ((C : ℝ) + 2)) ≤ (1 / 3) * (1 / ((C : ℝ) + 2)) := by nlinarith
      _ = (1 / 3) / ((C : ℝ) + 2) := by ring
  have hgoal : 1 / (4 * ((C : ℝ) + 2))
      ≤ Real.log (1 / ((bScale C : ℚ) : ℝ)) / Real.log 3 := by
    rw [hlogeq, le_div_iff₀ hlog3pos]
    linarith
  have hcast : Real.log ((3 : ℕ) : ℝ) = Real.log 3 := by norm_num
  rw [BB13.epsilon, hcast]
  exact hgoal

/-- The line count is antitone in the gap exponent: a smaller `ε` costs more lines. -/
@[category API, AMS 11 68, ref "BE08", group "weyl_a14_explicitrate"]
theorem lineBound_anti {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h : ε₁ ≤ ε₂) :
    BugeaudEvertse.lineBound ε₂ ≤ BugeaudEvertse.lineBound ε₁ := by
  have h2 : 0 < ε₂ := lt_of_lt_of_le h1 h
  have hinv : ε₂⁻¹ ≤ ε₁⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_le_one_div_of_le h1 h
  have hb2 : (0 : ℝ) < 1 + ε₂⁻¹ := by positivity
  have hb : 1 + ε₂⁻¹ ≤ 1 + ε₁⁻¹ := by linarith
  have hlog6 : (1 : ℝ) ≤ Real.log 6 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hcube : (1 + ε₂⁻¹) ^ 3 ≤ (1 + ε₁⁻¹) ^ 3 := pow_le_pow_left₀ hb2.le hb 3
  have hmul : (1 + ε₂⁻¹) * Real.log 6 ≤ (1 + ε₁⁻¹) * Real.log 6 :=
    mul_le_mul_of_nonneg_right hb (by linarith)
  have hll : Real.log ((1 + ε₂⁻¹) * Real.log 6) ≤ Real.log ((1 + ε₁⁻¹) * Real.log 6) :=
    Real.log_le_log (by positivity) hmul
  have hll0 : 0 ≤ Real.log ((1 + ε₂⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ε₂⁻¹ := by positivity
    nlinarith
  have hleft : (2 : ℝ) ^ 32 * (1 + ε₂⁻¹) ^ 3 * Real.log 6
      ≤ (2 : ℝ) ^ 32 * (1 + ε₁⁻¹) ^ 3 * Real.log 6 := by
    have h32 : (0 : ℝ) ≤ (2 : ℝ) ^ 32 := by positivity
    nlinarith
  have hright : (0 : ℝ) ≤ (2 : ℝ) ^ 32 * (1 + ε₁⁻¹) ^ 3 * Real.log 6 := by
    have : (0 : ℝ) ≤ 1 + ε₁⁻¹ := by positivity
    positivity
  rw [BugeaudEvertse.lineBound, BugeaudEvertse.lineBound]
  exact Nat.ceil_le_ceil (mul_le_mul hleft hll hll0 hright)

/-- **The cover is polynomial in the slope**: at the Bernoulli scale of slope `C` the number of
lines is at most `K(1/(4(C+2)))`, i.e. `⌈2³²(4C+9)³·log 6·log((4C+9)·log 6)⌉` — cubic times a log.
So the *cover* side of the quantitative lane scales harmlessly with the rate one is chasing; the
obstruction is entirely on the per-line side. -/
@[category research solved, AMS 11 68, ref "A1plus" "BE08", group "weyl_a14_explicitrate"]
theorem lineBound_bScale_le (C : ℕ) :
    BugeaudEvertse.lineBound (BB13.epsilon 3 ((bScale C : ℚ) : ℝ))
      ≤ BugeaudEvertse.lineBound (1 / (4 * ((C : ℝ) + 2))) :=
  lineBound_anti (by positivity) (epsilon_bScale_ge C)

/-! ## The no-go: per-gap finiteness is not a ceiling -/

/-- **The A14(i) no-go** (the counterpart of A13's `TH.ladder_permits_density_zero`).  Even the
strongest conclusion the fixed-gap line cover could be upgraded to — *finitely many violators for
every fixed gap* — is compatible with violators of unbounded size, so it can never feed
`complexity_gt_of_kernelCeiling`.  Witness: one pair per gap, `{(g, 2g)}`.

Together with [BE08] Rem. 7.4 (a line count is not a solution count), this is why A14(i) does not
close on the quantitative lane: the reduction consumes a ceiling, and the lane is shaped to
produce covers. -/
@[category research solved, AMS 11 68, ref "A1plus" "BE08", group "weyl_a14_explicitrate"]
theorem gapwiseFinite_not_ceiling :
    ∃ S : Set (ℕ × ℕ), (∀ g : ℕ, {p ∈ S | p.2 - p.1 = g}.Finite) ∧
      ¬ ∃ B : ℕ, ∀ p ∈ S, p.2 ≤ B := by
  refine ⟨Set.range (fun n : ℕ => (n, 2 * n)), fun g => ?_, ?_⟩
  · refine Set.Finite.subset (Set.finite_singleton ((g, 2 * g) : ℕ × ℕ)) ?_
    rintro p ⟨⟨n, rfl⟩, hg⟩
    simp only [Set.mem_singleton_iff]
    have hn : 2 * n - n = g := by simpa using hg
    have : n = g := by omega
    subst this
    rfl
  · rintro ⟨B, hB⟩
    have := hB (B + 1, 2 * (B + 1)) ⟨B + 1, rfl⟩
    omega

end TH
