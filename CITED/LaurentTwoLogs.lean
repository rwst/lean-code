/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.Adjoin.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Laurent's lower bound for a linear form in two logarithms

Laurent's theorem ([Lau08]): a sharp effective lower bound for a nonzero linear form
`Λ = b₂ log α₂ − b₁ log α₁` in **two** logarithms of algebraic numbers, obtained by the
interpolation-determinant method.  For the corpus's flagship pair `(2, 3)` this is the
sharpest *general* archimedean engine after Rhin's pair-specific Padé bound — but note
(plan §3) that **Rhin (`CITED/RhinLogForm`, exponent `13.3`) remains unbeaten on `(2, 3)`
at every `B`**, because every general two-log bound here carries a `(log b')²` factor and
a quadratic-in-`log B` bound never overtakes Rhin's linear `13.3 log H`.  Laurent is the
library engine for the pairs Rhin does *not* cover.

This file transcribes `plan-formalize-logforms.html` brief **F-2**: Corollary 2 (real
case) at the two Table-1 rows the plan selects, plus Corollary 1 (complex), plus the
proved `(2, 3)` instance.

## Statement conventions

* `α₁, α₂` are nonzero elements of a number field `K`, embedded in `ℂ` via `φ`; logs are
  `Complex.log ∘ φ` (principal branch).  The form is `Λ = b₂ log α₂ − b₁ log α₁` with
  `b₁, b₂` **positive** integers.
* `D := [ℚ(α₁,α₂):ℚ]/[ℝ(α₁,α₂):ℝ]` is Laurent's degree.  In the **real** case (Corollary
  2) `[ℝ(α₁,α₂):ℝ] = 1`, so `D = [ℚ(α₁,α₂):ℚ]` — and requiring `α₁, α₂` to *generate* `K`
  (`Algebra.adjoin ℚ {α₁,α₂} = ⊤`) makes this `Module.finrank ℚ K`.  For the complex
  Corollary 1 we carry a real-degree indicator `e ∈ {1,2}` and set `D = finrank/e`.
* `logA φ α D = max(h(α), |log α|/D, 1/D)` is Laurent's `log Aᵢ` clamp, where the height
  term `h(α) = Height.logHeight₁ α / [K:ℚ]` is the **normalized** absolute Weil height
  (`logHeight₁` divided by the field degree — the same normalization as
  `CITED/BakerWustholz.lean`, *unlike* `CITED/Matveev.lean` which uses the unnormalized
  `D·h`).
* `bPrime b₁ b₂ D logA₁ logA₂ = b₁/(D logA₂) + b₂/(D logA₁)` is Laurent's `b'` — note the
  **crossed indices** (`b₁` with `logA₂`, `b₂` with `logA₁`).
* `bound C add m D logA₁ logA₂ b' = C·D⁴·(max{log b' + add, m/D, 1})²·logA₁·logA₂` is the
  right-hand side; the `log b'` factor is **squared**.

## The three axioms

Table 1 of [Lau08] fixes, for `m ∈ {10,12,…,30}`, the constants `C₁(m)` (complex) and
`C₂(m)` (real).  Only the *listed* `(m, C)` pairs are proved — **there is no interpolation
between rows** — so each row is a separate axiom:

* `two_logs_real` — **Corollary 2** at `m = 30`, `C₂ = 17.9` (best asymptotic constant).
* `two_logs_real_smallB` — **Corollary 2** at `m = 10`, `C₂ = 25.2` (best small-`B`
  plateau, `m/D` dominating).
* `two_logs_complex` — **Corollary 1** at `m = 30`, `C₁ = 22.8` (complex determinations;
  additive constant `0.21` instead of `0.38`).

## The `(2, 3)` instance (proved)

`mulIndep_two_three`, `logA_two_eq_one`, `logA_three_eq_log_three`, and
`two_logs_two_three` discharge Corollary 2 for `α = (2, 3)` over `ℚ` (`D = 1`).  The
computation illustrates plan pitfall 4: at `α₁ = 2` the `1/D = 1` floor **bites**
(`logA = max{log 2, log 2, 1} = 1`, since `log 2 < 1`), while `logA(3) = log 3`; hence
`b' = b₁/log 3 + b₂` and the bound reads `log|Λ| ≥ −17.9·(max{log b' + 0.38, 30})²·log 3`.

## Lineage

[LMN95] Corollaire 2 (constant `24.34`) → [Mig98] Remark 4 (`22`, slack `0.06`) → [Lau08]
Corollary 2 (`17.9`–`25.2`, ≈ 20 % below LMN95 row by row).  The first two are *dominated
by [Lau08] in both the asymptote and the plateau* and are recorded here as provenance
only — not transcribed.

## References

* [Lau08] M. Laurent, "Linear forms in two logarithms and interpolation determinants II."
  *Acta Arithmetica* **133**.4 (2008), 325–348.  (Cor. 1/2 and Table 1, p. 328; Thm 2,
  p. 327; read in full 2026-07-10.)  Part I: *Acta Arith.* **66** (1994), 181–199.
* [LMN95] M. Laurent, M. Mignotte, Y. Nesterenko, "Formes linéaires en deux logarithmes
  et déterminants d'interpolation." *J. Number Theory* **55** (1995), 285–321.
* [Mig98] M. Mignotte, "A corollary to a theorem of Laurent–Mignotte–Nesterenko."
  *Acta Arith.* **86** (1998), 101–111.
* `plan-formalize-logforms.html` §4 brief F-2 (this repository).
-/

open Complex

namespace Laurent

/-- Laurent's clamped log-height `log Aᵢ = max{h(α), |log α|/D, 1/D}`, where
`h(α) = Height.logHeight₁ α / [K:ℚ]` is the **normalized** absolute Weil height and `D` is
Laurent's degree.  (In the real, generated case `D = [K:ℚ]` and all three denominators
agree.) -/
@[category API, AMS 11, ref "Lau08"]
noncomputable def logA {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) (D : ℝ) : ℝ :=
  max (Height.logHeight₁ α / (Module.finrank ℚ K : ℝ)) (max (‖Complex.log (φ α)‖ / D) (1 / D))

/-- Laurent's parameter `b' = b₁/(D log A₂) + b₂/(D log A₁)` — note the **crossed
indices**. -/
@[category API, AMS 11, ref "Lau08"]
noncomputable def bPrime (b₁ b₂ : ℕ) (D logA₁ logA₂ : ℝ) : ℝ :=
  (b₁ : ℝ) / (D * logA₂) + (b₂ : ℝ) / (D * logA₁)

/-- The right-hand side `C·D⁴·(max{log b' + add, m/D, 1})²·logA₁·logA₂` of Laurent's
corollaries.  The `log b'` term is **squared**; `add = 0.38` for the real Corollary 2 and
`0.21` for the complex Corollary 1. -/
@[category API, AMS 11, ref "Lau08"]
noncomputable def bound (C add m D logA₁ logA₂ bp : ℝ) : ℝ :=
  C * D ^ 4 * (max (Real.log bp + add) (max (m / D) 1)) ^ 2 * logA₁ * logA₂

/-- **Laurent's theorem, Corollary 2** ([Lau08], p. 328) at Table-1 row `m = 30`,
`C₂ = 17.9` (best asymptotic constant).

Let `α₁, α₂` be nonzero elements of a number field `K` that generate it
(`Algebra.adjoin ℚ {α₁,α₂} = ⊤`, so `D := Module.finrank ℚ K` is Laurent's degree in the
real case), embedded via a **real** `φ` (`φ(K) ⊆ ℝ`) with `φ(α₁), φ(α₂) > 1` (so the logs
are real and positive), multiplicatively independent.  For positive integers `b₁, b₂`,
`log |b₂ log α₂ − b₁ log α₁| ≥ −17.9·D⁴·(max{log b' + 0.38, 30/D, 1})²·log A₁·log A₂`,
with `A₁, A₂, b'` the clamps above.  A cited transcendence estimate (interpolation
determinants) recorded as an `axiom` on the authority of [Lau08]. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
axiom two_logs_real
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (hreal : ∀ x : K, (φ x).im = 0)
    (α₁ α₂ : K)
    (hgen : Algebra.adjoin ℚ ({α₁, α₂} : Set K) = ⊤)
    (h₁ : 1 < (φ α₁).re) (h₂ : 1 < (φ α₂).re)
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    Real.log ‖(b₂ : ℂ) * Complex.log (φ α₂) - (b₁ : ℂ) * Complex.log (φ α₁)‖
      ≥ -bound 17.9 0.38 30 (Module.finrank ℚ K : ℝ)
          (logA φ α₁ (Module.finrank ℚ K : ℝ)) (logA φ α₂ (Module.finrank ℚ K : ℝ))
          (bPrime b₁ b₂ (Module.finrank ℚ K : ℝ)
            (logA φ α₁ (Module.finrank ℚ K : ℝ)) (logA φ α₂ (Module.finrank ℚ K : ℝ)))

/-- **Laurent's theorem, Corollary 2** ([Lau08], p. 328) at Table-1 row `m = 10`,
`C₂ = 25.2` (best small-`B` plateau).  Same hypotheses as `two_logs_real`; the only change
is the pair `(m, C₂) = (10, 25.2)` — Table 1 rows are proved individually, **no
interpolation**. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
axiom two_logs_real_smallB
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (hreal : ∀ x : K, (φ x).im = 0)
    (α₁ α₂ : K)
    (hgen : Algebra.adjoin ℚ ({α₁, α₂} : Set K) = ⊤)
    (h₁ : 1 < (φ α₁).re) (h₂ : 1 < (φ α₂).re)
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    Real.log ‖(b₂ : ℂ) * Complex.log (φ α₂) - (b₁ : ℂ) * Complex.log (φ α₁)‖
      ≥ -bound 25.2 0.38 10 (Module.finrank ℚ K : ℝ)
          (logA φ α₁ (Module.finrank ℚ K : ℝ)) (logA φ α₂ (Module.finrank ℚ K : ℝ))
          (bPrime b₁ b₂ (Module.finrank ℚ K : ℝ)
            (logA φ α₁ (Module.finrank ℚ K : ℝ)) (logA φ α₂ (Module.finrank ℚ K : ℝ)))

/-- **Laurent's theorem, Corollary 1** ([Lau08], p. 328) at Table-1 row `m = 30`,
`C₁ = 22.8` (complex determinations; additive constant `0.21`).  Here `α₁, α₂` need only
be multiplicatively independent (not real); `e ∈ {1, 2}` is the real-subfield degree
`[ℝ(α₁,α₂):ℝ]` (guarded by the reality predicate for `e = 1`), and Laurent's degree is
`D = finrank/e`. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
axiom two_logs_complex
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α₁ α₂ : K)
    (hgen : Algebra.adjoin ℚ ({α₁, α₂} : Set K) = ⊤)
    (e : ℕ) (he : (e = 1 ∧ ∀ x : K, (φ x).im = 0) ∨ e = 2)
    (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    Real.log ‖(b₂ : ℂ) * Complex.log (φ α₂) - (b₁ : ℂ) * Complex.log (φ α₁)‖
      ≥ -bound 22.8 0.21 30 ((Module.finrank ℚ K : ℝ) / e)
          (logA φ α₁ ((Module.finrank ℚ K : ℝ) / e)) (logA φ α₂ ((Module.finrank ℚ K : ℝ) / e))
          (bPrime b₁ b₂ ((Module.finrank ℚ K : ℝ) / e)
            (logA φ α₁ ((Module.finrank ℚ K : ℝ) / e)) (logA φ α₂ ((Module.finrank ℚ K : ℝ) / e)))

/-- `2` and `3` are multiplicatively independent in `ℚ`: `2ᵐ·3ⁿ = 1 → m = n = 0`
(read off the `2`- and `3`-adic valuations).  Discharges the `hindep` hypothesis of the
corollaries for the flagship pair. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
theorem mulIndep_two_three :
    ∀ m n : ℤ, (2 : ℚ) ^ m * (3 : ℚ) ^ n = 1 → m = 0 ∧ n = 0 := by
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzp : ∀ (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ), q ≠ 0 → ∀ k : ℤ,
      padicValRat p (q ^ k) = k * padicValRat p q := by
    intro p _ q hq0 k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, padicValRat.pow _]
    · rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow _]; ring
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
  intro m n hmn
  refine ⟨?_, ?_⟩
  · have h2 := congrArg (padicValRat 2) hmn
    rw [padicValRat.mul (by positivity) (by positivity), hzp 2 (2 : ℚ) (by norm_num) m,
        hzp 2 (3 : ℚ) (by norm_num) n, v22, v23] at h2
    simp at h2; omega
  · have h3 := congrArg (padicValRat 3) hmn
    rw [padicValRat.mul (by positivity) (by positivity), hzp 3 (2 : ℚ) (by norm_num) m,
        hzp 3 (3 : ℚ) (by norm_num) n, v32, v33] at h3
    simp at h3; omega

/-- The `1/D` floor **bites at `α = 2`**: `logA(2) = max{log 2, log 2, 1} = 1`, because
`log 2 < 1`. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
theorem logA_two_eq_one : logA (algebraMap ℚ ℂ) (2 : ℚ) 1 = 1 := by
  have hlog : Complex.log ((algebraMap ℚ ℂ) (2 : ℚ)) = (Real.log 2 : ℂ) := by
    rw [show (algebraMap ℚ ℂ) (2 : ℚ) = ((2 : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log (by norm_num)).symm
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  unfold logA
  rw [Rat.logHeight₁_eq_log_max, hlog, Complex.norm_real, Module.finrank_self]
  norm_num [abs_of_nonneg hlog0]
  linarith [hlog2]

/-- At `α = 3` the floor does **not** bite: `logA(3) = log 3` (`log 3 > 1`). -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
theorem logA_three_eq_log_three : logA (algebraMap ℚ ℂ) (3 : ℚ) 1 = Real.log 3 := by
  have hlog : Complex.log ((algebraMap ℚ ℂ) (3 : ℚ)) = (Real.log 3 : ℂ) := by
    rw [show (algebraMap ℚ ℂ) (3 : ℚ) = ((3 : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log (by norm_num)).symm
  have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3 : 1 ≤ Real.log 3 := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
  unfold logA
  rw [Rat.logHeight₁_eq_log_max, hlog, Complex.norm_real, Module.finrank_self]
  norm_num [abs_of_nonneg hlog0]
  linarith [hlog3]

/-- **The flagship instance** ([Lau08] Corollary 2, `m = 30` at `α = (2, 3)`, `D = 1`).
With `b' = b₁/log 3 + b₂` (the `1/D` floor makes `log A₁ = 1`, `log A₂ = log 3`), for
positive integers `b₁, b₂`,
`log |b₂ log 3 − b₁ log 2| ≥ −17.9·(max{log(b₁/log 3 + b₂) + 0.38, 30})²·log 3`.
Proved by discharging the side conditions of `two_logs_real` and simplifying the clamps. -/
@[category research solved, AMS 11, ref "Lau08", group "laurent_two_logs"]
theorem two_logs_two_three (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    Real.log ‖(b₂ : ℂ) * Complex.log 3 - (b₁ : ℂ) * Complex.log 2‖
      ≥ -(17.9 * (max (Real.log ((b₁ : ℝ) / Real.log 3 + b₂) + 0.38) 30) ^ 2 * Real.log 3) := by
  have hreal : ∀ x : ℚ, ((algebraMap ℚ ℂ) x).im = 0 := fun x => by simp
  have hgen : Algebra.adjoin ℚ ({(2 : ℚ), 3} : Set ℚ) = ⊤ := by
    rw [eq_top_iff]; intro x _
    simpa using (Algebra.adjoin ℚ ({(2 : ℚ), 3} : Set ℚ)).algebraMap_mem x
  have h₁ : 1 < ((algebraMap ℚ ℂ) (2 : ℚ)).re := by
    rw [show (algebraMap ℚ ℂ) (2 : ℚ) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]; norm_num
  have h₂ : 1 < ((algebraMap ℚ ℂ) (3 : ℚ)).re := by
    rw [show (algebraMap ℚ ℂ) (3 : ℚ) = ((3 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]; norm_num
  have key := two_logs_real (algebraMap ℚ ℂ) hreal 2 3 hgen h₁ h₂ mulIndep_two_three b₁ b₂ hb₁ hb₂
  rw [show (algebraMap ℚ ℂ) (2 : ℚ) = (2 : ℂ) by norm_num,
      show (algebraMap ℚ ℂ) (3 : ℚ) = (3 : ℂ) by norm_num] at key
  simp only [Module.finrank_self, Nat.cast_one] at key
  rw [logA_two_eq_one, logA_three_eq_log_three] at key
  simp only [bound, bPrime, one_pow, mul_one, one_mul, div_one] at key
  rw [max_eq_left (by norm_num : (1 : ℝ) ≤ 30)] at key
  exact key
