/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import ForMathlib.Analysis.Complex.TaylorSeries
import BertinPisot.SchurAlgorithm
import BertinPisot.CompactFamily
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The Schur class `𝓜` (Bertin §3.2)

Bertin's **Notation 3.2.1** (*Pisot and Salem Numbers*, [Ber92], §3.2): `𝓜` denotes the set of
functions analytic and bounded by `1` on the open unit disk `D(0,1)`,
`𝓜 = { f | f analytic on D(0,1) and |f(z)| ≤ 1 for all z ∈ D(0,1) }`.

Classically this is the **Schur class** — the closed unit ball of `H^∞(D(0,1))` — and it is the
function class governed by the generalised Schur algorithm of `BertinPisot.SchurAlgorithm` (§3.1):
a power series `F` lies in `𝓜` exactly when all its Schur determinants `δₙ(F)` are `≥ 0`.

* `Complex.schurClass` is `𝓜`, encoded as a `Set (ℂ → ℂ)`. Analyticity on the disk is
  `AnalyticOnNhd ℂ f (ball 0 1)` (matching `Complex.MemHardy` in
  `ForMathlib.Analysis.Complex.HardySpace`), and the bound is `∀ z ∈ ball 0 1, ‖f z‖ ≤ 1`.
* `Complex.mem_schurClass` unfolds membership.

## Theorem 3.2.1 — the Schur-class characterisation

Bertin's **Theorem 3.2.1** (Schur's criterion, originally due to I. Schur [Sch17]): a power series
`F ∈ ℂ⟦z⟧` is the Taylor series at `0` of a function in `𝓜` **iff** *either* `δₙ(F) > 0` for all `n`
(the Schur algorithm never terminates — `F` is the Taylor series of a non-rational `𝓜`-function),
*or* there is a threshold `n₀` with `δₙ(F) > 0` for `n < n₀` and `δₙ(F) = 0` for `n ≥ n₀` (`F` is a
finite Blaschke product of degree `n₀` — the bounded-by-`1` instance of the `z^r·P*/P` form of
Theorem 3.1.1). As `δₙ(F)` is a real determinant, `δₙ(F) > 0` is encoded `0 < (δₙ F).re ∧ (δₙ F).im = 0`.

* `Complex.IsTaylorSeriesOfSchurClass F` is the left-hand side: `∃ g ∈ 𝓜` with
  `HasFPowerSeriesAt g (ofScalars ℂ (coeff · F)) 0` (`F` are the Taylor coefficients of `g` near `0`).
* `Complex.isTaylorSeriesOfSchurClass_iff` is the theorem, a `cited` axiom (`ref "Ber92" "Sch17"`). Its
  `informal_uses` record the not-yet-formalised classical pillars the proof needs: `schur-class-criterion`
  (Schur's bounded-analytic ⟺ Schur-determinant criterion) and the shared `montel-normal-families` node
  (Montel's theorem — the compactness behind the local-uniform convergence of the Lemma 3.2.1 convergents
  `Aₙ/Qₙ` to the limiting `𝓜`-function).

## Notation — Schur data of an analytic function; indefinite rank

Bertin transports the Schur matrices/determinants to an analytic function `f` near `0` through its
Taylor series: `δₙ(f) := δₙ(F)` with `F = Complex.taylorSeries f`. `f` has **indefinite rank**
(`Complex.HasIndefiniteRank`) when the `δₙ(f)` do not eventually all vanish (`¬ ∃ N, ∀ n ≥ N, δₙ(f) = 0`)
— the non-terminating / non-Blaschke case of Theorem 3.2.1; `Complex.hasIndefiniteRank_iff` restates it
as `δₙ(f) ≠ 0` infinitely often. (Bertin's wording is double-negative; this is the reading forced by the
Theorem 3.2.1 dichotomy — a finite Blaschke product of degree `d` has `δₙ = 0` for `n ≥ d`.)

## Corollary 3.2.1 — convergence of the Schur-parameter products

`schurOmega_tendsto_of_isTaylorSeriesOfSchurClass` is **Corollary 3.2.1** (Bertin): if `F` is the
Taylor series of a function in `𝓜` and has indefinite rank, then `δₙ(F) > 0` for all `n`, the ratio
`δₙ₊₁(F)/δₙ(F)` is the Schur-parameter product `ωₙ₊₁ = schurOmega F (n+1)`, and `(ωₙ)` is positive,
decreasing, and convergent. **Proved here** (modulo the cited Theorem 3.2.1): indefinite rank excludes
the finite-Blaschke branch, leaving `δₙ(F) > 0`; the analytic core
`schurOmega_pos_antitone_tendsto` then gives positivity, antitonicity (each factor
`δ₀(Fᵏ) = 1 − |γₖ|² ∈ (0,1]`) and convergence (monotone bounded below by `0`), with the ratio
collapsing via Lemma 3.2.1's `schurDelta_succ_eq_schurOmega_mul`.

## Corollary 3.2.2 — positivity of the Hermitian Schur matrices

`posSemidef_one_sub_schurToeplitz_of_mem_schurClass` is **Corollary 3.2.2** (Bertin): for `f ∈ 𝓜`,
each Hermitian matrix `Iₙ₊₁ − Fₙ F*ₙ` is positive semidefinite (`Matrix.PosSemidef`, taken with
`open scoped ComplexOrder`) — the matrix/operator form of Schur's criterion (`Fₙ` a contraction), of
which `δₙ(f) = det(Iₙ₊₁ − Fₙ F*ₙ) ≥ 0` is the determinant shadow. Recorded as a `cited` axiom with
`informal_uses` `schur-class-criterion` and `schur-toeplitz-contraction`.

## Corollary 3.2.3 — positivity of `Iₙ₊₁ ± Jₙ₊₁ Fₙ` for real `f`

`posSemidef_one_pm_exchangeMatrix_schurToeplitz_of_real` is **Corollary 3.2.3** (Bertin): for `f ∈ 𝓜`
with **real** Taylor series, both `Iₙ₊₁ ± Jₙ₊₁ Fₙ` are positive semidefinite. Hermitian by
Lemma 3.1.1 b); positive by the Cauchy–Schwarz/contraction argument off **Corollary 3.2.2**
(`‖Jₙ₊₁ Fₙ‖ ≤ 1`). **Proved here** modulo the cited Corollary 3.2.2 — a Cauchy–Schwarz / contraction
argument in the Euclidean inner product `(X∣Y) = star X ⬝ᵥ Y` on `ℂⁿ⁺¹` (`#print axioms` lists only
Corollary 3.2.2 and the standard three).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
* [Sch17] Schur, Issai. *Über Potenzreihen, die im Innern des Einheitskreises beschränkt sind.*
  J. Reine Angew. Math. **147** (1917), 205–232; **148** (1918), 122–145. (Schur's criterion for the
  class `𝓜`.)
-/

open Metric Filter
open scoped Topology ComplexOrder Matrix

namespace Complex

/-- **Notation 3.2.1.** The **Schur class** `𝓜`: the set of functions analytic and bounded by `1`
on the open unit disk `D(0,1)`, `𝓜 = { f | f analytic on D(0,1) and |f| ≤ 1 on D(0,1) }`. -/
@[category API, AMS 30, ref "Ber92"]
def schurClass : Set (ℂ → ℂ) :=
  { f | AnalyticOnNhd ℂ f (ball 0 1) ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1 }

/-- A function lies in the Schur class `𝓜` iff it is analytic on `D(0,1)` and bounded there by `1`. -/
@[category API, AMS 30, ref "Ber92", formal_uses schurClass]
theorem mem_schurClass {f : ℂ → ℂ} :
    f ∈ schurClass ↔
      AnalyticOnNhd ℂ f (ball 0 1) ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1 := Iff.rfl

/-! ### Theorem 3.2.1 — the Schur-class characterisation

Bertin's proof of Theorem 3.2.1 also rests on Montel's normal-families theorem, reused from the shared
`montel-normal-families` registry node (`BertinPisot.CompactFamily`); the one pillar specific to this
theorem and **not** in Mathlib is Schur's criterion, recorded here. -/

informal_result "schur-class-criterion"
  latex "Schur's criterion (I. Schur, 1917) for the class M of functions analytic and bounded by 1 on the open unit disk D(0,1): a power series is the Taylor series of a function in M if and only if its Schur parameters γₖ = Fᵏ(0) all lie in the closed unit disk (equivalently, the Schur determinants δₙ(F) = det(Iₙ₊₁ − Fₙ F*ₙ) are all ≥ 0); the Schur algorithm terminates — some |γ_{n₀}| = 1, i.e. δₙ(F) = 0 for n ≥ n₀ — exactly when F is a finite Blaschke product (a rational inner function) of degree n₀. The classical engine is the Schwarz lemma applied to the contractive Schur step F ↦ F¹, iterated. In the non-terminating case the Schur continued-fraction convergents Aₙ/Qₙ of Lemma 3.2.1 assemble into a limit in M by a Montel normal-families argument with Schwarz–Pick tail control."
  refs "Ber92" "Sch17"

/-- `F` is the Taylor series at `0` of a function in the Schur class `𝓜`: some `g ∈ 𝓜` has `F` as its
sequence of Taylor coefficients near `0` (`HasFPowerSeriesAt g (ofScalars ℂ (coeff · F)) 0`). -/
@[category API, AMS 30, ref "Ber92", formal_uses schurClass]
def IsTaylorSeriesOfSchurClass (F : PowerSeries ℂ) : Prop :=
  ∃ g : ℂ → ℂ, g ∈ schurClass ∧
    HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n F)) 0

/-- **Theorem 3.2.1** (Bertin; Schur's criterion [Sch17]). A power series `F ∈ ℂ⟦z⟧` is the Taylor
series at `0` of a function in the Schur class `𝓜` **iff** *either* `δₙ(F) > 0` for every `n`, *or*
there is a threshold `n₀` with `δₙ(F) > 0` for `n < n₀` and `δₙ(F) = 0` for `n ≥ n₀` (the finite
Blaschke / `z^r·P*/P` case of Theorem 3.1.1). `δₙ(F) > 0` is the positive-real condition
`0 < (δₙ F).re ∧ (δₙ F).im = 0`. Recorded as a `cited` axiom (`ref "Ber92" "Sch17"`); the
`informal_uses` edges name the classical pillars the proof needs (`schur-class-criterion` and the shared
`montel-normal-families` node), neither yet in Mathlib, so `#print axioms` surfaces this axiom downstream. -/
@[category research solved, AMS 30 15 13, ref "Ber92" "Sch17",
  formal_uses schurClass schurDelta IsTaylorSeriesOfSchurClass,
  informal_uses "schur-class-criterion" "montel-normal-families"]
axiom isTaylorSeriesOfSchurClass_iff (F : PowerSeries ℂ) :
    IsTaylorSeriesOfSchurClass F ↔
      (∀ n, 0 < (schurDelta F n).re ∧ (schurDelta F n).im = 0) ∨
      (∃ n₀, (∀ n < n₀, 0 < (schurDelta F n).re ∧ (schurDelta F n).im = 0) ∧
        (∀ n, n₀ ≤ n → schurDelta F n = 0))

/-! ### Notation — Schur data of an analytic function; indefinite rank

Bertin extends the Schur matrices/determinants from a power series to an analytic function `f` near
`0` through its **Taylor series** `F = Complex.taylorSeries f = ∑ₙ (f⁽ⁿ⁾(0) / n!) zⁿ` (imported from
`ForMathlib.Analysis.Complex.TaylorSeries`; for analytic `f` it is the power-series expansion of `f`,
so Bertin's Schur data of `f` are those of `F`: `Fₙ`, `F*ₙ`, `δₙ(f) := δₙ(F) = schurDelta (taylorSeries f) n`),
and names the non-terminating case of Theorem 3.2.1. -/

/-- **Notation** (Bertin): `f` has **indefinite rank** when its Schur determinants
`δₙ(f) = schurDelta (taylorSeries f) n` do **not** eventually all vanish — there is no `N` with
`δₙ(f) = 0` for every `n ≥ N`. By Theorem 3.2.1 this is the non-Blaschke case (for `f ∈ 𝓜`, indefinite
rank ⟺ `δₙ(f) > 0` for all `n`); a finite Blaschke product of degree `d` has `δₙ = 0` for `n ≥ d`,
hence *definite* (finite) rank. Bertin's defining sentence is double-negative; this is the reading
forced by the Theorem 3.2.1 dichotomy. -/
@[category API, AMS 30 15, ref "Ber92", formal_uses schurDelta taylorSeries]
def HasIndefiniteRank (f : ℂ → ℂ) : Prop :=
  ¬ ∃ N, ∀ n, N ≤ n → schurDelta (taylorSeries f) n = 0

/-- `f` has indefinite rank iff `δₙ(f) ≠ 0` for infinitely many `n` (`∀ N, ∃ n ≥ N, δₙ(f) ≠ 0`). -/
@[category API, AMS 30 15, ref "Ber92", formal_uses HasIndefiniteRank schurDelta taylorSeries]
theorem hasIndefiniteRank_iff (f : ℂ → ℂ) :
    HasIndefiniteRank f ↔ ∀ N, ∃ n, N ≤ n ∧ schurDelta (taylorSeries f) n ≠ 0 := by
  unfold HasIndefiniteRank; push Not; rfl

/-! ### Corollary 3.2.1 — the Schur-parameter products `ωₙ` converge

For `F` whose Schur determinants are all positive, the products `ωₙ = schurOmega F n` are positive,
decreasing, and convergent. -/

/-- **Corollary 3.2.1 (analytic core).** If every Schur determinant `δₙ(F)` is a positive real, then
the Schur-parameter products `ωₙ = schurOmega F n` are positive reals, the real sequence
`n ↦ (ωₙ).re` is **antitone**, and it **converges** (a decreasing sequence bounded below by `0`). The
key step is the ratio identity `schurDelta_succ_eq_schurOmega_mul` (Lemma 3.2.1). -/
@[category API, AMS 30 15 13, ref "Ber92",
  formal_uses schurDelta schurOmega schurTransform schurDelta_succ_eq_schurOmega_mul schurOmega_succ
    schurOmega_zero]
theorem schurOmega_pos_antitone_tendsto (F : PowerSeries ℂ)
    (hpos : ∀ n, 0 < (schurDelta F n).re ∧ (schurDelta F n).im = 0) :
    (∀ n, 0 < (schurOmega F n).re ∧ (schurOmega F n).im = 0) ∧
      Antitone (fun n => (schurOmega F n).re) ∧
      ∃ L : ℝ, Tendsto (fun n => (schurOmega F n).re) atTop (𝓝 L) := by
  have key : ∀ a b c : ℂ, 0 < b.re → b.im = 0 → 0 < c.re → c.im = 0 → c = a * b →
      0 < a.re ∧ a.im = 0 := by
    intro a b c hbre hbim hcre hcim h
    have hbne : b ≠ 0 := by intro hb; rw [hb] at hbre; simp at hbre
    have ha : a = c / b := by rw [h, mul_div_assoc, div_self hbne, mul_one]
    subst ha
    have hnsq : 0 < Complex.normSq b := Complex.normSq_pos.mpr hbne
    exact ⟨by rw [Complex.div_re, hbim, hcim]; simp only [mul_zero, add_zero, zero_div]; positivity,
      by rw [Complex.div_im, hbim, hcim]; simp⟩
  have hδ : ∀ i, schurDelta F i ≠ 0 := fun i h => by
    have := (hpos i).1; rw [h] at this; simp at this
  have hω : ∀ n, 0 < (schurOmega F n).re ∧ (schurOmega F n).im = 0 := by
    intro n; cases n with
    | zero => rw [schurOmega_zero]; exact hpos 0
    | succ m =>
      have hr := schurDelta_succ_eq_schurOmega_mul F m (fun i _ => hδ i)
      exact key _ _ _ (hpos m).1 (hpos m).2 (hpos (m + 1)).1 (hpos (m + 1)).2 hr
  have hδ0re : ∀ k, (schurDelta (schurTransform^[k] F) 0).re ≤ 1 := by
    intro k; rw [schurDelta_zero, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    exact sub_le_self _ (Complex.normSq_nonneg _)
  have hδ0im : ∀ k, (schurDelta (schurTransform^[k] F) 0).im = 0 := by
    intro k; rw [schurDelta_zero]; simp
  have hanti : Antitone (fun n => (schurOmega F n).re) := by
    apply antitone_nat_of_succ_le; intro n
    show (schurOmega F (n + 1)).re ≤ (schurOmega F n).re
    rw [schurOmega_succ, Complex.mul_re, (hω n).2, hδ0im (n + 1)]
    simp only [mul_zero, sub_zero]
    exact mul_le_of_le_one_right (le_of_lt (hω n).1) (hδ0re (n + 1))
  refine ⟨hω, hanti, (⨅ n, (schurOmega F n).re), tendsto_atTop_ciInf hanti ⟨0, ?_⟩⟩
  intro x hx; obtain ⟨n, rfl⟩ := hx; exact le_of_lt (hω n).1

/-- **Corollary 3.2.1** (Bertin). If `F` is the Taylor series of a function in the Schur class `𝓜`
(`IsTaylorSeriesOfSchurClass F`) and has **indefinite rank** — the determinants `δₙ(F)` do not
eventually all vanish — then `δₙ(F) > 0` for every `n`, the ratio `δₙ₊₁(F)/δₙ(F)` equals the
Schur-parameter product `ωₙ₊₁ = schurOmega F (n+1)`, and `(ωₙ)` is **positive, decreasing, and
convergent**. (For `F = taylorSeries f` with `f ∈ 𝓜` the hypothesis `IsTaylorSeriesOfSchurClass F`
holds with witness `f`, and `hrank` is `HasIndefiniteRank f`; this is Bertin's statement verbatim.)

**Proof.** Indefinite rank rules out the finite-Blaschke branch of **Theorem 3.2.1**
(`isTaylorSeriesOfSchurClass_iff`), leaving `δₙ(F) > 0` for all `n`. The ratio collapses to `ωₙ₊₁` by
the iterated formula (`schurDelta_succ_eq_schurOmega_mul`, Lemma 3.2.1), and `ωₙ = ∏_{k≤n}(1 − |γₖ|²)`
with `|γₖ| < 1` is positive decreasing, hence converges. Proved modulo the cited Theorem 3.2.1. -/
@[category research solved, AMS 30 15 13, ref "Ber92" "Sch17",
  formal_uses schurDelta schurOmega IsTaylorSeriesOfSchurClass isTaylorSeriesOfSchurClass_iff
    schurDelta_succ_eq_schurOmega_mul schurOmega_pos_antitone_tendsto]
theorem schurOmega_tendsto_of_isTaylorSeriesOfSchurClass (F : PowerSeries ℂ)
    (hF : IsTaylorSeriesOfSchurClass F) (hrank : ¬ ∃ N, ∀ n, N ≤ n → schurDelta F n = 0) :
    (∀ n, 0 < (schurDelta F n).re ∧ (schurDelta F n).im = 0) ∧
      (∀ n, schurDelta F (n + 1) / schurDelta F n = schurOmega F (n + 1)) ∧
      (∀ n, 0 < (schurOmega F n).re ∧ (schurOmega F n).im = 0) ∧
      Antitone (fun n => (schurOmega F n).re) ∧
      ∃ L : ℝ, Tendsto (fun n => (schurOmega F n).re) atTop (𝓝 L) := by
  have hpos : ∀ n, 0 < (schurDelta F n).re ∧ (schurDelta F n).im = 0 := by
    rcases (isTaylorSeriesOfSchurClass_iff F).mp hF with h | ⟨n₀, _, h2⟩
    · exact h
    · exact absurd ⟨n₀, h2⟩ hrank
  have hδ : ∀ i, schurDelta F i ≠ 0 := fun i h => by
    have := (hpos i).1; rw [h] at this; simp at this
  obtain ⟨hω, hanti, hconv⟩ := schurOmega_pos_antitone_tendsto F hpos
  refine ⟨hpos, fun n => ?_, hω, hanti, hconv⟩
  rw [schurDelta_succ_eq_schurOmega_mul F n (fun i _ => hδ i), mul_div_assoc, div_self (hδ n), mul_one]

/-! ### Corollary 3.2.2 — positivity of the Hermitian Schur matrices

The matrix/operator form of Schur's criterion that Bertin's Corollary 3.2.2 records, **not** in
Mathlib, kept as a registry node so the `informal_uses` edge below points at a canonical target. -/

informal_result "schur-toeplitz-contraction"
  latex "Operator/matrix form of Schur's criterion: a function f is in the Schur class M (analytic and bounded by 1 on D(0,1)) if and only if, for every n, the lower-triangular Toeplitz matrix Fₙ of its Taylor coefficients is a contraction (operator norm ≤ 1) — equivalently the Hermitian matrix Iₙ₊₁ − Fₙ F*ₙ is positive semidefinite. The Schur determinants δₙ(f) = det(Iₙ₊₁ − Fₙ F*ₙ) ≥ 0 are the determinant manifestation; full positive semidefiniteness is the Toeplitz/Carathéodory positivity, obtained from Schur's criterion through the nested (Toeplitz) structure of the leading principal minors δ₀, …, δₙ."
  refs "Ber92"

/-- **Corollary 3.2.2** (Bertin). If `f ∈ 𝓜` then for every `n` the Hermitian matrix `Iₙ₊₁ − Fₙ F*ₙ`
— with `Fₙ = schurToeplitz (taylorSeries f) n` and `F*ₙ = schurToeplitzStar (taylorSeries f) n` — is
**positive semidefinite**: the lower-triangular Toeplitz matrix `Fₙ` of a Schur function is a
contraction. The determinants `δₙ(f) = det(Iₙ₊₁ − Fₙ F*ₙ) ≥ 0` of Theorem 3.2.1 are the determinant
shadow of this matrix positivity (semidefinite, not definite, since `𝓜` is closed — finite Blaschke
products give singular cases). Recorded as a `cited` axiom (`ref "Ber92"`); the `informal_uses` edges
name the classical pillars — Schur's criterion (`schur-class-criterion`) and its
Toeplitz-contraction / positive-semidefinite form (`schur-toeplitz-contraction`), neither yet in
Mathlib. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurClass taylorSeries schurToeplitz schurToeplitzStar,
  informal_uses "schur-class-criterion" "schur-toeplitz-contraction"]
axiom posSemidef_one_sub_schurToeplitz_of_mem_schurClass {f : ℂ → ℂ} (hf : f ∈ schurClass) (n : ℕ) :
    (1 - schurToeplitz (taylorSeries f) n * schurToeplitzStar (taylorSeries f) n).PosSemidef

/-- **Corollary 3.2.3** (Bertin). If `f ∈ 𝓜` and its Taylor series `F = taylorSeries f` is **real**
(`F ∈ ℝ⟦z⟧`, i.e. every coefficient is real), then for every `n` both Hermitian matrices
`Iₙ₊₁ ± Jₙ₊₁ Fₙ` (`Jₙ₊₁ = exchangeMatrix n`, `Fₙ = schurToeplitz (taylorSeries f) n`) are **positive
semidefinite** ("positive hermitian").

**Proof** (Bertin). The matrices are Hermitian by Lemma 3.1.1 b) (`exchangeMatrix_schurToeplitzStar`:
`J F̄ₙ = F*ₙ J`, so for real `F`, `(J Fₙ)ᴴ = F*ₙ J = J Fₙ`). For positivity, equip `ℂⁿ⁺¹` with
`(X∣Y) = Σ x̄ᵢ yᵢ`. By the preceding **Corollary 3.2.2**, `(Iₙ₊₁ − Fₙ F*ₙ) X ∣ X) ≥ 0`, i.e.
`‖F*ₙ X‖ ≤ ‖X‖`; since `J` is an isometry, `‖F*ₙ J‖ ≤ 1`, hence `‖J Fₙ‖ = ‖F*ₙ J‖ ≤ 1`. Cauchy–Schwarz
then gives `|(J Fₙ X ∣ X)| ≤ ‖J Fₙ X‖‖X‖ ≤ ‖X‖²`, so `±(J Fₙ X ∣ X) ≤ (X∣X)` and `Iₙ₊₁ ± J Fₙ ⪰ 0`.

**Proved here** modulo the cited Corollary 3.2.2: a Cauchy–Schwarz / contraction argument in the
Euclidean inner product `(X∣Y) = star X ⬝ᵥ Y` on `ℂⁿ⁺¹`. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurClass taylorSeries schurToeplitz schurToeplitzStar exchangeMatrix
    exchangeMatrix_schurToeplitzStar exchangeMatrix_mul_self schurToeplitzStar_eq_conjTranspose
    posSemidef_one_sub_schurToeplitz_of_mem_schurClass]
theorem posSemidef_one_pm_exchangeMatrix_schurToeplitz_of_real {f : ℂ → ℂ} (hf : f ∈ schurClass)
    (hreal : ∀ n, (PowerSeries.coeff n (taylorSeries f)).im = 0) (n : ℕ) :
    (1 + exchangeMatrix n * schurToeplitz (taylorSeries f) n).PosSemidef ∧
      (1 - exchangeMatrix n * schurToeplitz (taylorSeries f) n).PosSemidef := by
  set F := taylorSeries f with hF
  set A := schurToeplitz F n with hA
  set As := schurToeplitzStar F n with hAs
  set J := exchangeMatrix n with hJ
  -- Structural facts: `F*ₙ = (Fₙ)ᴴ`, the cited contraction `Iₙ₊₁ − Fₙ F*ₙ ⪰ 0`, realness of `Fₙ`,
  -- `J Fₙ = F*ₙ J`, `J² = I`, `Jᴴ = J`, and hence `(J Fₙ)ᴴ = J Fₙ` (Hermitian).
  have hAsAH : As = Aᴴ := schurToeplitzStar_eq_conjTranspose F n
  have cor322 : (1 - A * As).PosSemidef :=
    Complex.posSemidef_one_sub_schurToeplitz_of_mem_schurClass hf n
  have hAreal : A.map (starRingEnd ℂ) = A := by
    ext i j
    simp only [hA, schurToeplitz, Matrix.map_apply]
    split_ifs with h
    · exact Complex.conj_eq_iff_im.mpr (hreal _)
    · exact map_zero _
  have hJA : J * A = As * J := by
    have h := (exchangeMatrix_schurToeplitzStar F n).2
    rwa [hAreal] at h
  have hJ2 : J * J = 1 := exchangeMatrix_mul_self n
  have hJH : Jᴴ = J := by
    ext i j
    simp only [hJ, exchangeMatrix, Matrix.conjTranspose_apply]
    split_ifs with h1 h2 h2
    · simp
    · omega
    · omega
    · simp
  have hHJA : (J * A)ᴴ = J * A := by
    rw [Matrix.conjTranspose_mul, hJH, ← hAsAH, ← hJA]
  -- Inner-product / norm infrastructure on `ℂⁿ⁺¹ ≃ EuclideanSpace ℂ (Fin (n+1))`,
  -- with `(X ∣ Y) = star X ⬝ᵥ Y = inner ℂ (toLp X) (toLp Y)`.
  have hadj : ∀ (y w : Fin (n + 1) → ℂ), star y ⬝ᵥ (A *ᵥ w) = star (Aᴴ *ᵥ y) ⬝ᵥ w := by
    intro y w
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have dotc : ∀ (u v : Fin (n + 1) → ℂ),
      star u ⬝ᵥ v = inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
    intro u v
    rw [dotProduct_comm (star u) v, EuclideanSpace.inner_toLp_toLp]
  have hnsq : ∀ (u : Fin (n + 1) → ℂ), (star u ⬝ᵥ u).re = ‖WithLp.toLp 2 u‖ ^ 2 := by
    intro u
    rw [dotc, ← RCLike.re_to_complex]
    exact inner_self_eq_norm_sq _
  have hnim : ∀ (u : Fin (n + 1) → ℂ), (star u ⬝ᵥ u).im = 0 := by
    intro u
    rw [dotc]
    have := inner_self_im (𝕜 := ℂ) (WithLp.toLp 2 u)
    rwa [RCLike.im_to_complex] at this
  -- `J` is an isometry: `‖J X‖ = ‖X‖` (since `J² = I`, `Jᴴ = J`).
  have hJiso : ∀ x, ‖WithLp.toLp 2 (J *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
    intro x
    have hdp : star (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ x := by
      rw [Matrix.star_mulVec, hJH, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJ2,
        Matrix.one_mulVec]
    have h2 : (‖WithLp.toLp 2 (J *ᵥ x)‖) ^ 2 = (‖WithLp.toLp 2 x‖) ^ 2 := by
      rw [← hnsq, ← hnsq, hdp]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (le_of_eq h2) |>.antisymm
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (le_of_eq h2.symm))
  -- Contraction `‖F*ₙ Y‖ ≤ ‖Y‖`, extracted from `Iₙ₊₁ − Fₙ F*ₙ ⪰ 0` (Corollary 3.2.2).
  have hcontr : ∀ y, ‖WithLp.toLp 2 (Aᴴ *ᵥ y)‖ ≤ ‖WithLp.toLp 2 y‖ := by
    intro y
    have hps := (Matrix.posSemidef_iff_dotProduct_mulVec.mp cor322).2 y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, hAsAH,
      hadj y (Aᴴ *ᵥ y)] at hps
    rw [Complex.le_def] at hps
    have hre := hps.1
    rw [Complex.sub_re, hnsq, hnsq] at hre
    simp only [Complex.zero_re] at hre
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)
  -- Crux bound: `|(J Fₙ X ∣ X)| ≤ ‖J Fₙ X‖ ‖X‖ ≤ ‖X‖² = (X ∣ X)` (Cauchy–Schwarz + isometry +
  -- contraction), since `J Fₙ X = F*ₙ J X = (Fₙ)ᴴ (J X)`.
  have hQabs : ∀ x, ‖star x ⬝ᵥ ((J * A) *ᵥ x)‖ ≤ (star x ⬝ᵥ x).re := by
    intro x
    rw [hJA, ← Matrix.mulVec_mulVec, hAsAH, dotc]
    calc ‖inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 (Aᴴ *ᵥ (J *ᵥ x)))‖
        ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (Aᴴ *ᵥ (J *ᵥ x))‖ := norm_inner_le_norm _ _
      _ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (J *ᵥ x)‖ :=
          mul_le_mul_of_nonneg_left (hcontr _) (norm_nonneg _)
      _ = ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 x‖ := by rw [hJiso]
      _ = ‖WithLp.toLp 2 x‖ ^ 2 := by rw [sq]
      _ = (star x ⬝ᵥ x).re := (hnsq x).symm
  -- The quadratic form of the Hermitian matrix `J Fₙ` is real.
  have hQim : ∀ x, (star x ⬝ᵥ ((J * A) *ᵥ x)).im = 0 := by
    intro x
    rw [← Complex.conj_eq_iff_im]
    have key : star (star x ⬝ᵥ ((J * A) *ᵥ x)) = star x ⬝ᵥ ((J * A) *ᵥ x) := by
      conv_lhs => rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hHJA,
        ← Matrix.dotProduct_mulVec]
    exact key
  -- Final assembly: `±(J Fₙ X ∣ X) ≤ (X ∣ X)` gives `Iₙ₊₁ ± J Fₙ ⪰ 0`.
  refine ⟨?_, ?_⟩
  · have hHerm : (1 + J * A).IsHermitian := by
      show (1 + J * A)ᴴ = 1 + J * A
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hHJA]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [Complex.zero_re, Complex.add_re]
      have hN : 0 ≤ (star x ⬝ᵥ x).re := by rw [hnsq]; positivity
      have h1 : |(star x ⬝ᵥ ((J * A) *ᵥ x)).re| ≤ ‖star x ⬝ᵥ ((J * A) *ᵥ x)‖ :=
        Complex.abs_re_le_norm _
      have := abs_le.mp (h1.trans (hQabs x))
      linarith [this.1]
    · rw [Complex.zero_im, Complex.add_im, hnim x, hQim x]; ring
  · have hHerm : (1 - J * A).IsHermitian := by
      show (1 - J * A)ᴴ = 1 - J * A
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hHJA]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [Complex.zero_re, Complex.sub_re]
      have hN : 0 ≤ (star x ⬝ᵥ x).re := by rw [hnsq]; positivity
      have h1 : |(star x ⬝ᵥ ((J * A) *ᵥ x)).re| ≤ ‖star x ⬝ᵥ ((J * A) *ᵥ x)‖ :=
        Complex.abs_re_le_norm _
      have := abs_le.mp (h1.trans (hQabs x))
      linarith [this.2]
    · rw [Complex.zero_im, Complex.sub_im, hnim x, hQim x]; ring

end Complex
