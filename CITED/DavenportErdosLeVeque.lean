/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Davenport–Erdős–LeVeque: power Fourier decay gives almost-sure normality

> **[DEL63, Theorem]** (p. 311, unnumbered).  Let `sₙ(x)` be bounded and integrable on
> `a ≤ x ≤ b`, `S(N, x) = N⁻¹ ∑_{n ≤ N} e(m sₙ(x))` and `I(N) = ∫_a^b |S(N, x)|² dx`.  If
> `∑ N⁻¹ I(N)` converges for each integer `m ≠ 0`, then `sₙ(x)` is uniformly distributed
> modulo 1 for almost all `x` in `[a, b]`.

The theorem is stated for Lebesgue measure.  Its proof (§2: interpolation along a lacunary
`N_r`, then Borel–Cantelli in `L²`) uses only that the measure is finite, so it holds verbatim
for any Borel probability measure `μ`, with `I(N) = ∫ |S(N, x)|² dμ(x)`.  For `sₙ(x) = sₙ x`
this is `I(N) = N⁻² ∑_{n,n' ≤ N} \hat μ(m(sₙ − sₙ'))`.

Take `sₙ = 2ⁿ`.  If `|\hat μ(u)| ≤ C|u|^{-σ}` for `|u| ≥ 1`, then the off-diagonal part of the
inner double sum is `O(1)` (since `|h(2ᵐ − 2ⁿ)| ≥ 2^{max(m,n)-1}`) and the diagonal is `N`, so
the series is `≪ ∑ N⁻²` and converges.  Hence `μ`-almost every `x` is normal to base `2`
(Wall's form of Weyl's criterion), and in particular **simply normal**: the proportion of the
digit `1` among the first `N` binary digits of `x` tends to `1/2`.  This is the form recorded
here; it is the standard corollary used e.g. in [PVZZ22, §1] and in [MS18, §1].

## Transcription choices

* Only the conclusion "simply normal to base 2" is asserted (normality gives it), which is
  weaker, hence safer, than the full DEL conclusion.
* The `k`-th binary digit of `x` (after the point) is `⌊2ᵏ x⌋ mod 2`, the convention that picks
  the terminating expansion of a dyadic rational; for `x` not dyadic it is the unique one.
* The Fourier transform is `u ↦ ∫ exp(-2πiux) dμ(x)`, as in `CITED/MosqueraShmerkin.lean`.

## Contents

* `DEL.ae_simplyNormal_of_fourierDecay` — the corollary above, a cited `axiom`.

## References

* [DEL63] Davenport, H., P. Erdős, and W. J. LeVeque. "On Weyl's criterion for uniform
  distribution." *Michigan Math. J.* **10** (1963), 311–314.  (Theorem, p. 311; stated for Lebesgue measure on an interval.)
* [PVZZ22] Pollington, A. D., S. Velani, A. Zafeiropoulos, and E. Zorin. "Inhomogeneous
  Diophantine approximation on M₀-sets with restricted denominators." *IMRN* 2022, 8571–8643.
* [MS18] Mosquera, C. A., and P. S. Shmerkin, *Ann. Acad. Sci. Fenn. Math.* **43** (2018).
-/

namespace DEL

open MeasureTheory Filter Topology

/-- **[DEL63, Theorem]** (for `μ`), power-decay corollary, base `2`, digit `1`: if the Fourier transform
of a probability measure decays like a power, almost every point is simply normal to base `2`. -/
@[category research solved, AMS 11 42, ref "DEL63", group "isaac_tu"]
axiom ae_simplyNormal_of_fourierDecay (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : 0 < σ) (C : ℝ)
    (hdecay : ∀ u : ℝ, 1 ≤ |u| →
      ‖∫ x, Complex.exp (-(2 * Real.pi * u * x : ℝ) * Complex.I) ∂μ‖ ≤ C * |u| ^ (-σ)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun N : ℕ => ((∑ k ∈ Finset.range N, (⌊(2 : ℝ) ^ (k + 1) * x⌋ % 2) : ℤ) : ℝ) / N)
      atTop (𝓝 (1 / 2))

end DEL
