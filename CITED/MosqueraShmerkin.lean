/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Mosquera–Shmerkin: Fourier decay of smooth images of self-similar measures (Thm. 3.1)

A variant, due to Mosquera and Shmerkin, of a theorem of Kaufman (1984): a non-linear smooth
image of a homogeneous self-similar measure on `ℝ` has power Fourier decay.

> **[MS18, Theorem 3.1].**  Let `F ∈ C²(ℝ)` with `F'' > 0`, and let `μ = μ^p_{a,t}` be a
> (homogeneous) self-similar measure on `ℝ` which is not a single atom.  Then there exist
> `σ = σ(μ) > 0` (independent of `F`) and `C = C(F, μ) > 0` such that
> `|\widehat{Fμ}(u)| ≤ C |u|^{-σ}`.

Here [MS18, §2] `μ^p_{a,t}` is the distribution of `∑_{n ≥ 1} X_n aⁿ`, the `X_n` i.i.d. with
`P(X_n = t_i) = p_i`, for `a ∈ (0, 1)`, translations `t = (t_1, …, t_m)` and weights
`p = (p_1, …, p_m)`.  It is `MS.ssMeasure P t a` below, with `P` the law of `X_n` on `Fin m`.

## Transcription choices (each makes the axiom weaker, i.e. safer)

* *Not a single atom* is replaced by the stronger hypothesis that `μ` has no atoms at all.
* `F ∈ C²(ℝ)`, `F'' > 0` is given by explicit derivatives `F'`, `F''` with `F''` continuous
  and positive everywhere.
* The decay is asserted only for `|u| ≥ 1` (at `u = 0` the transform is `1`).
* The Fourier transform is `u ↦ ∫ exp(-2πiux) d(Fμ)(x)`; another normalisation of the
  exponent changes only `C`.
* The weights are only required to be positive; the paper does not need more.

## Contents

* `MS.ssMeasure` — the homogeneous self-similar measure `μ^p_{a,t}`.
* `MS.fourierDecay_smoothImage` — **[MS18, Theorem 3.1]**, a cited `axiom`.

## References

* [MS18] Mosquera, Carolina A., and Pablo S. Shmerkin. "Self-similar measures: asymptotic
  bounds for the dimension and Fourier decay of smooth images." *Ann. Acad. Sci. Fenn. Math.*
  **43** (2018), 823–834; arXiv:1710.06812.  (Theorem 3.1, p. 6; definition of `μ^p_{a,t}`,
  §2, p. 4.)
* [Kau84] Kaufman, Robert. "On Bernoulli convolutions." *Conference in modern analysis and
  probability (New Haven, 1982)*, Contemp. Math. **26** (1984), 217–222.
-/

namespace MS

open MeasureTheory

/-- The homogeneous self-similar measure `μ^p_{a,t}` of [MS18, §2]: the law of
`∑_{n ≥ 1} t(Xₙ) aⁿ` for `Xₙ` i.i.d. with law `P` on `Fin m` (the index `k` below is `n - 1`). -/
@[category API, AMS 28 42, ref "MS18", group "isaac_tu"]
noncomputable def ssMeasure {m : ℕ} (P : Measure (Fin m)) [IsProbabilityMeasure P]
    (t : Fin m → ℝ) (a : ℝ) : Measure ℝ :=
  (Measure.infinitePi (fun _ : ℕ => P)).map (fun ι => ∑' k, t (ι k) * a ^ (k + 1))

/-- **[MS18, Theorem 3.1]** (after Kaufman [Kau84]).  The image of a non-atomic homogeneous
self-similar measure under a `C²` map with positive second derivative has power Fourier
decay. -/
@[category research solved, AMS 28 42, ref "MS18" "Kau84", group "isaac_tu"]
axiom fourierDecay_smoothImage {m : ℕ} (P : Measure (Fin m)) [IsProbabilityMeasure P]
    (hP : ∀ i, P {i} ≠ 0) (t : Fin m → ℝ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hatom : ∀ x, ssMeasure P t a {x} = 0)
    (F F' F'' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF''c : Continuous F'') (hF''pos : ∀ x, 0 < F'' x) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ C : ℝ, ∀ u : ℝ, 1 ≤ |u| →
      ‖∫ x, Complex.exp (-(2 * Real.pi * u * x : ℝ) * Complex.I) ∂((ssMeasure P t a).map F)‖
        ≤ C * |u| ^ (-σ)

end MS
