/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Matveev's explicit lower bound for a linear form in logarithms

Matveev's theorem ([Mat00]): an effective lower bound for a nonzero linear form
`Λ = ∑ bᵢ · log αᵢ` in the logarithms of algebraic numbers whose main term in `n`
is the *pure exponential* `30^{n+3}` (or `C^n`), rather than the `n^{2n}`-type factor
of Baker–Wüstholz (`CITED/BakerWustholz.lean`).  This is the corpus's second general
archimedean transcendence engine and the sharpest closed-form one for `n ≥ 3`
(≈ `15×` at `n = 3`, ≈ `325×` at `n = 4` over [BW93]); the two-logarithm specialists
([Rhi87] `CITED/RhinLogForm`, [Lau08]) remain sharper at `n = 2`.

This file transcribes the two results of `plan-formalize-logforms.html` brief **F-1**:

* **Corollary 2.3** ([Mat00], eq. (2.6)) — the general workhorse (`linearForms_logs`),
  no independence hypothesis, with the `0.16`-floored modified height and constant `C₁`.
* **Theorem 2.1** ([Mat00], eq. (2.3)) — the sharper `5`–`8×` bound
  (`linearForms_logs_indep`) valid when `log α₁, …, log αₙ` are `ℤ`-linearly
  independent, with the un-floored height, the constant `C`, and the weighted `B`.

together with the proved instance `two_three` that discharges the independence
hypothesis of Theorem 2.1 for the flagship pair `(2, 3)`.

## Statement conventions

* `α₁, …, αₙ` are nonzero elements of a number field `K`, embedded in `ℂ` via a
  ring hom `φ`, and we use `Complex.log` (principal branch) for the logs of the
  images — exactly as in `CITED/BakerWustholz.lean`.
* `D := Module.finrank ℚ K` is the field degree, appearing *undivided* below.
* `κ` is Matveev's reality indicator: `κ = 1` when `φ(K) ⊆ ℝ` (guarded here by the
  hypothesis `∀ x, (φ x).im = 0`), else `κ = 2`.  See the height/`κ` note below.
* `clampHeight φ α = max(logHeight₁ α, ‖log φ(α)‖, 0.16)` is Matveev's modified
  height `Aⱼ` of eq. (2.4) (used by Corollary 2.3), and `clampHeightIndep` is the
  un-floored `Aⱼ` of eq. (2.1) (used by Theorem 2.1).
* `Ω := ∏ᵢ Aᵢ` is the height product.

### Height API — the load-bearing contrast with Baker–Wüstholz

Matveev's `Aⱼ ≥ max{D·h(αⱼ), |log αⱼ|, 0.16}` is stated with the **unnormalized**
`D·h`, which is *exactly* Mathlib's `Height.logHeight₁ α` (the product-over-places
sum).  So `clampHeight` clamps `Height.logHeight₁ α` **with no division by `D`
anywhere** — the opposite of `BakerWustholz.modifiedHeight`, which divides by `d`
three times to recover the classical absolute height.  A stray `1/D` here would
silently *strengthen* the axiom (unsoundly): this is risk **R2** of the plan and the
single most important thing to get right in the transcription.  Likewise the `B`-factor
is `log(eB) = 1 + log B` (Cor 2.3), never bare `log B` nor BW's `max(log B, 1/d)`, and
the `0.16` Lehmer floor is load-bearing (only the independent-logs Theorem 2.1 drops it).

### `κ` and the requirement `2 ≤ n`

`C₁(n, 2) ≥ C₁(n, 1)` and `C(n, 2) ≥ C(n, 1)` hold **only for `n ≥ 2`** (at `n = 1`
the `κ = 2` constant is *smaller*, so a blanket `κ = 2` claim on a real field would be
unsound).  Both axioms therefore require `2 ≤ n` and guard `κ = 1` by the reality
predicate; the corpus never needs the degenerate single- or two-log `n = 1` case
(which is LTE-exact anyway).

## Cross-check

[BMS06] Theorem 9.4 is the widely-quoted real-case (`κ = 1`) restatement of Corollary
2.3, with constant `1.4 · 30^{n+3} · n^{4.5} · D² · (1+log D) · (1+log B)` and the same
`Aⱼ = max{D h(αⱼ), |log αⱼ|, 0.16}`, `B = max|bⱼ|`.  It rounds Matveev's `e/2 ≈ 1.359`
up to `1.4` and drops the `min` with `2^{6n+20}`, i.e. it is `linearForms_logs` at
`κ = 1` weakened — an independent confirmation of the transcription (`e/2 = C₁(n,1)`
first branch coefficient, since `C₁(n,1) = (e/2)·30^{n+3}·n^{4.5}`).  Numerically
`C₁(2, 1) ≈ 7.47×10⁸`.

## Contents

* `Matveev.C`, `Matveev.C₁`, `Matveev.C₀`, `Matveev.W₀` — the constants (2.2), (2.6).
* `Matveev.clampHeight`, `Matveev.clampHeightIndep` — the modified heights (2.4), (2.1).
* `Matveev.linearForms_logs` — **Corollary 2.3** ([Mat00]); a cited `axiom`.
* `Matveev.linearForms_logs_indep` — **Theorem 2.1** ([Mat00]); a cited `axiom`.
* `Matveev.log_two_three_indep` — `a·log 2 + b·log 3 = 0 → a = b = 0` (proved).
* `Matveev.two_three` — the `ℤ`-independence of `log 2, log 3`, in the exact shape of
  the `hindep` hypothesis of `linearForms_logs_indep` at `K = ℚ`, `φ = algebraMap ℚ ℂ`,
  `α = ![2, 3]` (proved).

## References

* [Mat00] E. M. Matveev, "An explicit lower bound for a homogeneous rational linear
  form in the logarithms of algebraic numbers. II." *Izvestiya: Mathematics* **64**:6
  (2000), 1217–1269.  (§2 Statement of results: Thm 2.1 eq. (2.3), Cor 2.3 eq. (2.6),
  constants (2.2); read in full 2026-07-09.)
* [BMS06] Y. Bugeaud, M. Mignotte, S. Siksek, "Classical and modular approaches to
  exponential Diophantine equations I." *Ann. of Math.* **163** (2006), 969–1018,
  Theorem 9.4 (cross-check).
* `plan-formalize-logforms.html` §4 brief F-1 (this repository).
-/

open Complex

namespace Matveev

/-- Matveev's constant of eq. (2.2):
`C(n, κ) = (16 / (n! · κ)) · eⁿ · (2n+1+2κ) · (n+2) · (4(n+1))^{n+1} · (en/2)^κ`. -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def C (n κ : ℕ) : ℝ :=
  16 / ((n.factorial : ℝ) * κ) * Real.exp 1 ^ n * (2 * n + 1 + 2 * κ) * (n + 2)
    * (4 * (n + 1) : ℝ) ^ (n + 1) * (Real.exp 1 * n / 2) ^ κ

/-- Matveev's constant of Corollary 2.3, eq. (2.6):
`C₁(n, κ) = min{ (1/κ)·(en/2)^κ · 30^{n+3} · n^{3.5},  2^{6n+20} }`. -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def C₁ (n κ : ℕ) : ℝ :=
  min ((1 / (κ : ℝ)) * (Real.exp 1 * n / 2) ^ κ * 30 ^ (n + 3) * (n : ℝ) ^ ((7 : ℝ) / 2))
      (2 ^ (6 * n + 20))

/-- Matveev's constant `C₀ = log(e^{4.4n+7} · n^{5.5} · D² · log(eD))` (used by Theorem 2.1). -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def C₀ (n : ℕ) (D : ℝ) : ℝ :=
  Real.log (Real.exp (4.4 * n + 7) * (n : ℝ) ^ ((11 : ℝ) / 2) * D ^ 2 * Real.log (Real.exp 1 * D))

/-- Matveev's constant `W₀ = log(1.5 · e · B · D · log(eD))` (used by Theorem 2.1). -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def W₀ (B D : ℝ) : ℝ :=
  Real.log (3 / 2 * Real.exp 1 * B * D * Real.log (Real.exp 1 * D))

/-- Matveev's **modified height** `Aⱼ` of eq. (2.4) (with the `0.16` Lehmer floor):
`max(logHeight₁ α, ‖log φ(α)‖, 0.16)`.  Note `Height.logHeight₁ α` is the
*unnormalized* `D·h(α)`, so there is **no division by `D`** — see the module doc. -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def clampHeight {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  max (Height.logHeight₁ α) (max ‖Complex.log (φ α)‖ 0.16)

/-- Matveev's **modified height** `Aⱼ` of eq. (2.1) (no floor; used by Theorem 2.1, where the
`ℤ`-independence of the logs makes the floor unnecessary): `max(logHeight₁ α, ‖log φ(α)‖)`. -/
@[category API, AMS 11, ref "Mat00"]
noncomputable def clampHeightIndep {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  max (Height.logHeight₁ α) ‖Complex.log (φ α)‖

/-- **Matveev's theorem, Corollary 2.3** ([Mat00], eq. (2.6)).

Let `α₁, …, αₙ` (with `2 ≤ n`) be nonzero elements of a number field `K` of degree
`D := Module.finrank ℚ K`, embedded in `ℂ` via `φ`; let `κ = 1` if `φ(K) ⊆ ℝ` (the
guarded hypothesis) and `κ = 2` otherwise.  Let `b₁, …, bₙ` be rational integers with
`|bᵢ| ≤ B`, `1 ≤ B` (Matveev's `B` of (1.3) may be replaced by `B* = max|bⱼ|`, as done
here and in [BMS06] §9.1).  If `Λ := ∑ᵢ bᵢ · log(φ(αᵢ))` (principal branch) is nonzero,
then
`log |Λ| > -C₁(n,κ) · D² · Ω · log(eD) · log(eB)`,
where `Ω = ∏ᵢ clampHeight φ (αᵢ)` (the `0.16`-floored heights of (2.4)).

Recorded as a cited `axiom` on the authority of [Mat00] — an arithmetic–analytic
continuation / lattice argument we do not re-derive.  The `2 ≤ n` requirement and the
`κ = 1 → φ(K) ⊆ ℝ` guard are the soundness conditions discussed in the module doc. -/
@[category research solved, AMS 11, ref "Mat00", group "matveev_logforms"]
axiom linearForms_logs
    {n : ℕ} (hn : 2 ≤ n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (κ : ℕ) (hκ : (κ = 1 ∧ ∀ x : K, (φ x).im = 0) ∨ κ = 2)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) (B : ℝ) (hB : 1 ≤ B) (hbB : ∀ i, (|b i| : ℝ) ≤ B)
    (hΛ : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      > -(C₁ n κ * (Module.finrank ℚ K : ℝ) ^ 2 * (∏ i, clampHeight φ (α i))
          * Real.log (Real.exp 1 * (Module.finrank ℚ K : ℝ))
          * Real.log (Real.exp 1 * B))

/-- **Matveev's main theorem, Theorem 2.1** ([Mat00], eq. (2.3)).

The `5`–`8×` sharpening of Corollary 2.3, valid when the logarithms are `ℤ`-linearly
independent.  Notation as in `linearForms_logs`, with `2 ≤ n`, `κ` guarded as before,
and `i₀` the distinguished index (Matveev's "`n`") at which `b i₀ ≠ 0`.  If
`log(φ(α₁)), …, log(φ(αₙ))` are `ℤ`-linearly independent (hypothesis `hindep`), and
`B ≥ max{1, maxⱼ |bⱼ|·Aⱼ/A_{i₀}}` (the weighted `B` of (1.3), with `Aⱼ` the un-floored
`clampHeightIndep`), then
`log |Λ| > -C(n,κ) · C₀(n,D) · W₀(B,D) · D² · Ω`,
where `Ω = ∏ᵢ clampHeightIndep φ (αᵢ)` (the heights of (2.1), no `0.16` floor —
independence makes it unnecessary, Remark 2.2).

Recorded as a cited `axiom` on the authority of [Mat00].  `hindep` also forces
`Λ ≠ 0` and every log to be nonzero, so no separate hypotheses are needed. -/
@[category research solved, AMS 11, ref "Mat00", group "matveev_logforms"]
axiom linearForms_logs_indep
    {n : ℕ} (hn : 2 ≤ n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (κ : ℕ) (hκ : (κ = 1 ∧ ∀ x : K, (φ x).im = 0) ∨ κ = 2)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (hindep : ∀ c : Fin n → ℤ,
       (∑ i, (c i : ℂ) * Complex.log (φ (α i))) = 0 → ∀ i, c i = 0)
    (b : Fin n → ℤ) (i₀ : Fin n) (hbn : b i₀ ≠ 0)
    (B : ℝ) (hB : 1 ≤ B)
    (hBweight : ∀ j, (|b j| : ℝ) * clampHeightIndep φ (α j) / clampHeightIndep φ (α i₀) ≤ B) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      > -(C n κ * C₀ n (Module.finrank ℚ K) * W₀ B (Module.finrank ℚ K)
          * (Module.finrank ℚ K : ℝ) ^ 2 * (∏ i, clampHeightIndep φ (α i)))

/-- `log 2` and `log 3` are `ℤ`-linearly independent: if `a·log 2 + b·log 3 = 0`
(`a, b ∈ ℤ`) then `a = b = 0`.  Exponentiate to `2ᵃ·3ᵇ = 1` in `ℚ` and read off the
`2`- and `3`-adic valuations. -/
@[category API, AMS 11, ref "Mat00", group "matveev_logforms"]
theorem log_two_three_indep (a b : ℤ)
    (h : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 = 0) : a = 0 ∧ b = 0 := by
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  -- Exponentiate the linear relation to a multiplicative one over `ℝ`, then over `ℚ`.
  have hexp : (2 : ℝ) ^ a * (3 : ℝ) ^ b = 1 := by
    have hc := congrArg Real.exp h
    rw [Real.exp_add, Real.exp_zero,
        show (a : ℝ) * Real.log 2 = Real.log 2 * (a : ℝ) from mul_comm _ _,
        show (b : ℝ) * Real.log 3 = Real.log 3 * (b : ℝ) from mul_comm _ _,
        ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (a : ℝ),
        ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) (b : ℝ),
        Real.rpow_intCast, Real.rpow_intCast] at hc
    exact hc
  have hq : (2 : ℚ) ^ a * (3 : ℚ) ^ b = 1 := by
    have hcast : (((2 : ℚ) ^ a * (3 : ℚ) ^ b : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      push_cast; exact hexp
    exact_mod_cast hcast
  -- `padicValRat p` is additive over the integer power `q ^ k`.
  have hzp : ∀ (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ), q ≠ 0 → ∀ k : ℤ,
      padicValRat p (q ^ k) = k * padicValRat p q := by
    intro p _ q hq0 k
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, padicValRat.pow hq0]
    · rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow hq0]; ring
  have v22 : padicValRat 2 (2 : ℚ) = 1 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]; exact padicValRat.self (by norm_num)
  have v23 : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)]
  have v33 : padicValRat 3 (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num]; exact padicValRat.self (by norm_num)
  have v32 : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 2)]
  refine ⟨?_, ?_⟩
  · have h2 := congrArg (padicValRat 2) hq
    rw [padicValRat.mul (by positivity) (by positivity), hzp 2 (2 : ℚ) (by norm_num) a,
        hzp 2 (3 : ℚ) (by norm_num) b, v22, v23] at h2
    simp at h2; omega
  · have h3 := congrArg (padicValRat 3) hq
    rw [padicValRat.mul (by positivity) (by positivity), hzp 3 (2 : ℚ) (by norm_num) a,
        hzp 3 (3 : ℚ) (by norm_num) b, v32, v33] at h3
    simp at h3; omega

/-- The `ℤ`-independence of `log 2` and `log 3`, packaged as the exact `hindep`
hypothesis of `linearForms_logs_indep` for the flagship pair.  Taking `K = ℚ`,
`φ = algebraMap ℚ ℂ`, `α = ![2, 3]` one has `Complex.log (φ (α i)) ∈ {log 2, log 3}`, so
this lemma discharges the independence side condition of Matveev's Theorem 2.1 for
`(2, 3)` (with `κ = 1`, since `algebraMap ℚ ℂ` is real). -/
@[category research solved, AMS 11, ref "Mat00", group "matveev_logforms"]
theorem two_three (c : Fin 2 → ℤ)
    (h : ∑ i, (c i : ℂ) * Complex.log ((algebraMap ℚ ℂ) (![(2 : ℚ), 3] i)) = 0) :
    ∀ i, c i = 0 := by
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_ofNat] at h
  have e2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num)).symm
  have e3 : Complex.log (3 : ℂ) = (Real.log 3 : ℂ) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num)).symm
  rw [e2, e3] at h
  have hre : (c 0 : ℝ) * Real.log 2 + (c 1 : ℝ) * Real.log 3 = 0 := by
    have hcast : (((c 0 : ℝ) * Real.log 2 + (c 1 : ℝ) * Real.log 3 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero, ← h]; push_cast; ring
    exact_mod_cast hcast
  obtain ⟨e0, e1⟩ := log_two_three_indep (c 0) (c 1) hre
  intro i; fin_cases i
  · simpa using e0
  · simpa using e1

end Matveev
