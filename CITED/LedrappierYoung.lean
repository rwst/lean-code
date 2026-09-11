/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.PressureCriterion
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The entropy floor for a counterexample to Problem 10.61 (Young; Ledrappier–Young)

The one cited axiom of the M3/M4 pressure lane: a `σ`-invariant measure on the full `2`-shift
whose image under the factor map `F` of `BB61/Factor.lean` is Lebesgue measure has entropy at
least `h_min(α)`.  This is Theorem 11 of `note-1061-M3.html`, and it is what the pressure
criterion contradicts.

## The statement

For a Pisot number `α` with conjugate modulus `ρ`, put

`h_min(α) = (1/log α + 1/log(1/ρ))⁻¹`,

which for a **quadratic unit** (`ρ = 1/α`, i.e. `α² = aα ± 1`) is `½ log α`.  If `μ` is
`σ`-invariant with `F_*μ = Leb`, then `h(μ) ≥ h_min(α)`.

## The source statements

* **[You82] p. 109, Thm 4.4** (dimension of hyperbolic measures on **surfaces**): an ergodic
  hyperbolic measure `λ` for a `C^{1+ε}` surface diffeomorphism is exact-dimensional with
  `dim λ = h(λ)(1/χ⁺ + 1/|χ⁻|)`.  Since `M̄` here acts on a **two**-dimensional torus, this is
  the case that actually applies, and it is an *equality*.
* **[LY85] II** (general dimension): `dim λ = ∑ᵢ γᵢ` with `γᵢ ∈ [0,1]` and
  `h(λ) = ∑_{i unst} γᵢ χᵢ = ∑_{i st} γᵢ|χᵢ|`, whence `dim λ ≤ h(λ)(1/χ⁺_min + 1/|χ⁻_min|)`.
* **[BPS99]** exact dimensionality of hyperbolic measures in any dimension, which [LY85] needs.

The floor follows: `λ = Φ_*μ` has `τ̄_*λ = Leb`, so `dim λ_e ≥ dim τ̄_*λ_e = 1` for a.e. ergodic
component (`τ̄` is Lipschitz and a probability measure `≪ Leb` on `𝕋` has dimension one), and
`1 ≤ dim λ_e ≤ h(λ_e) · (1/log α + 1/log(1/ρ))`.

## What the axiom folds in (none of it formalized here)

1. **The M1 §2/§4 coding.**  The torus `𝕋²_Λ = ℝ²/ι(ℤ[α])`, the automorphism `M̄` (an
   automorphism exactly because `α` is a **unit** — `note-1061-M1.html` F-fact, correcting §2.2),
   the coding `Φ : {0,1}^ℤ → 𝕋²_Λ` and the trace character `τ̄` with `τ̄ ∘ Φ = F`.  None of this is
   in `BB61/`, which carries `F` (`BB61/Factor.lean`) and nothing above it.
2. **Ergodic decomposition** of `λ` into `M̄`-ergodic components, and measurability in `e` of the
   Lebesgue decomposition `τ̄_*λ_e = a_e + s_e` (used to conclude `∫ s_e dP = 0` from uniqueness of
   the Lebesgue decomposition of `Leb`).
3. **Affinity of entropy** (Jacobs) over that decomposition, `h(λ) = ∫ h(λ_e) dP(e)` — [Wal82].
4. **The factor inequality** `h(μ) ≥ h(λ)`, `λ = Φ_*μ` being a factor of `μ`.
5. ⚠ **The Kolmogorov–Sinai generator theorem** — [Wal82] Ch. 4.  The note's `h(μ)` is the
   Kolmogorov–Sinai entropy `h_μ(σ)`; the conclusion below is stated with
   `entropyRate σ μ coordPartition`, the entropy **relative to the time-zero coordinate
   partition**.  They agree because that partition generates the two-sided shift, but that is the
   generator theorem, which `ForMathlib/Dynamics/KolmogorovSinai.lean` does not prove — and the
   inequality that *is* available runs the wrong way (`entropyRate ≤ kolmogorovSinai`).  So this
   step is folded in here rather than discharged, and every consumer must keep the relative
   spelling.  This is the one fold beyond the note's own reckoning.

## What is deliberately **not** axiomatized

Nothing about the orbit, the certificate or the pressure.  The Jensen half of the variational
principle is a theorem (`ForMathlib/Dynamics/TopologicalPressure.lean`), the reduction to
invariant measures is a theorem (`BB61/Saturation.lean`, M1 Cor. 9), and the whole `2 + √3`
certificate is a theorem (`BB61/Pressure.lean`, `BB61/Window.lean`).  This axiom is the single
external input of the lane, exactly as `note-1061-M3.html` says: *"These are the only external
inputs of this note, and they enter in exactly one place."*

## References

* [You82] L.-S. Young, "Dimension, entropy and Lyapunov exponents", *Ergodic Theory Dynam.
  Systems* **2** (1982), 109–124.
* [LY85] F. Ledrappier & L.-S. Young, "The metric entropy of diffeomorphisms I, II", *Ann. of
  Math.* **122** (1985), 509–539 and 540–574.
* [BPS99] L. Barreira, Ya. Pesin & J. Schmeling, "Dimension and product structure of hyperbolic
  measures", *Ann. of Math.* **149** (1999), 755–783.
* [Wal82] P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer 1982.  Ergodic
  decomposition of entropy (Jacobs); the Kolmogorov–Sinai generator theorem, Ch. 4.
* `note-1061-M3.html` Theorem 11 and its proof; `note-1061-M1.html` §2, §4.
-/

namespace LY

open MeasureTheory BB61

/-- `h_min(α) = (1/log α + 1/log(1/ρ))⁻¹` at degree two, with `ρ = |β|` the conjugate modulus.
For a unit this is `½ log α` (`hMin_eq_of_unit`). -/
noncomputable def hMin (P : QuadSetup) : ℝ :=
  (1 / Real.log P.α + 1 / Real.log (1 / |P.β|))⁻¹

/-- **The entropy floor** (`note-1061-M3.html` Theorem 11, quadratic-unit case; [You82] Thm 4.4,
[LY85] II, [BPS99]).

A `σ`-invariant Borel probability measure on the full `2`-shift whose push-forward under the
factor map `F` of `BB61/Factor.lean` is Lebesgue measure on the circle has entropy at least
`h_min(α)`, relative to the time-zero coordinate partition.

Recorded as a cited `axiom`.  The M1 coding, ergodic decomposition, affinity of entropy, the
factor inequality and the Kolmogorov–Sinai generator theorem are folded into the citation
(module doc, items 1–5); `α` is required to be a quadratic **unit** because that is what makes
`M̄` an automorphism, which the hyperbolic dimension theory needs. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99" "Wal82",
  group "bugeaud_10_61"]
axiom entropyRate_floor (P : QuadSetup) (hα : 2 < P.α) (hunit : P.b = 1 ∨ P.b = -1)
    (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ)
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) :
    hMin P ≤ entropyRate shiftZ μ coordPartition

/-! ## The unit specialization `h_min = ½ log α`

`α β = -b`, so a quadratic unit has `ρ = |β| = 1/α` and the two summands of `h_min` coincide. -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_beta (P : QuadSetup) : P.α * P.β = -(P.b : ℝ) := by
  have h := P.root
  rw [QuadSetup.β]
  nlinarith [h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_eq_inv (P : QuadSetup) (hα : 1 < P.α) (hunit : P.b = 1 ∨ P.b = -1) :
    |P.β| = 1 / P.α := by
  have hpos : (0 : ℝ) < P.α := by linarith
  have h : P.α * |P.β| = 1 := by
    have := alpha_mul_beta P
    rw [← abs_of_pos hpos, ← abs_mul, this, abs_neg]
    rcases hunit with h1 | h1 <;> rw [h1] <;> norm_num
  field_simp at h ⊢
  linarith [h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem hMin_eq_of_unit (P : QuadSetup) (hα : 1 < P.α) (hunit : P.b = 1 ∨ P.b = -1) :
    hMin P = Real.log P.α / 2 := by
  have hlog : 0 < Real.log P.α := Real.log_pos hα
  rw [hMin, abs_beta_eq_inv P hα hunit, one_div_one_div]
  field_simp
  ring

/-- The floor in the shape `BB61/Window.lean`'s capstones consume: for a quadratic unit
`α > 2`, every counterexample measure has `½ log α ≤ h_μ(σ, coordPartition)`. -/
@[category research solved, AMS 37 28 11, ref "You82" "LY85" "BPS99" "Wal82",
  group "bugeaud_10_61"]
theorem entropyRate_floor_unit (P : QuadSetup) (hα : 2 < P.α) (hunit : P.b = 1 ∨ P.b = -1)
    (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ)
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) :
    Real.log P.α / 2 ≤ entropyRate shiftZ μ coordPartition := by
  have h := entropyRate_floor P hα hunit μ hinv hmap
  rwa [hMin_eq_of_unit P (by linarith) hunit] at h

end LY
