/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Baker–Wüstholz theorem on linear forms in logarithms

The main theorem of Baker–Wüstholz ([BW93]): an effective lower bound for a nonzero
linear form `Λ = ∑ bᵢ · log αᵢ` in logarithms of algebraic numbers, with the outer
exponent on `log B` essentially `1` rather than the `(2n+1)²` of the 1966–68 Baker
bounds.  Recorded as a cited `axiom`; the general-purpose fallback transcendence
engine behind the two-logarithm specialists ([Rhi87] `CITED.RhinLogForm`, exponent
`13.3`; [Ell71] `CITED.EllisonsTheorem`) — any instantiation is polynomial in the
coefficient height `B`, but with the astronomically larger exponent
`C(n,d) · ∏ h'(αᵢ)`.

## Statement conventions

* `α₁, …, αₙ` are nonzero elements of a number field `K`. We work through a
  ring-hom embedding `φ : K →+* ℂ`, and use `Complex.log` (principal branch)
  for the logs of the images.
* `d := Module.finrank ℚ K` is the field degree.
* `h(α) := Height.logHeight₁ α / d` is the **normalized** logarithmic Weil
  height. (Mathlib's `logHeight₁` is the unnormalized product-over-places
  sum; dividing by `d` gives the classical absolute height.)
* `h'(α) := max(h(α), |log φ(α)| / d, 1 / d)` is the **modified height** used
  by Baker–Wüstholz. The extra terms handle the case where `α` is very close
  to 1 (so `h(α)` is small) or where the chosen log determination is large.
* `B := max(|b₁|, …, |bₙ|, 2)` is the maximum coefficient (clamped to 2 so
  `log B > 0`).
* `C(n, d) := 18 · (n + 1)! · n^(n+1) · (32d)^(n+2) · log(2nd)` is the
  Baker–Wüstholz constant.

## Contents
* `BakerWustholz.C` — the Baker–Wüstholz constant `C(n, d)`.
* `BakerWustholz.modifiedHeight` — the modified height `h'(α)`.
* `BakerWustholz.linearForms_logs` — **the Baker–Wüstholz main theorem** ([BW93]):
  `Λ ≠ 0 → log |Λ| ≥ −C(n,d) · max(log B, 1/d) · ∏ h'(αᵢ)`; a cited transcendence
  estimate recorded as an `axiom`.

## References
* [BW93] Baker, Alan, and Gisbert Wüstholz. "Logarithmic forms and group varieties."
  *Journal für die reine und angewandte Mathematik* **442** (1993): 19–62.
-/

open Complex

namespace BakerWustholz

/-- The Baker–Wüstholz constant
`C(n, d) = 18 · (n + 1)! · n^{n+1} · (32 d)^{n+2} · log (2nd)`. -/
@[category API, AMS 11, ref "BW93"]
noncomputable def C (n d : ℕ) : ℝ :=
  18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
    (32 * (d : ℝ)) ^ (n + 2) * Real.log (2 * n * d)

/-- The modified height `h'(α) = max(h(α), |log φ(α)| / d, 1 / d)` where
`h(α) := logHeight₁ α / d` is the normalized logarithmic Weil height. -/
@[category API, AMS 11, ref "BW93"]
noncomputable def modifiedHeight
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α / d) (max (‖Complex.log (φ α)‖ / d) (1 / d))

/-- **Baker–Wüstholz theorem on linear forms in logarithms**, effective form
([BW93], main theorem).

Let `α₁, …, αₙ` (with `1 ≤ n`) be nonzero elements of a number field `K` of
degree `d := Module.finrank ℚ K`, embedded in `ℂ` via `φ`. Let `b₁, …, bₙ`
be rational integers with `|bᵢ| ≤ B` and `B ≥ 2`. If the linear form
`Λ := ∑ᵢ bᵢ · log (φ (αᵢ))` (complex log, principal branch) is nonzero,
then
`log |Λ| ≥ -C(n, d) · max(log B, 1/d) · ∏ᵢ h'(αᵢ)`

where `C(n, d)` is `BakerWustholz.C n d` and `h'(α)` is
`BakerWustholz.modifiedHeight φ α`. The `max(log B, 1/d)` factor (rather
than bare `log B`) is the standard Baker–Wüstholz formulation; it avoids
spuriously sharpening the bound at `d = 1`, `B = 2`.  Recorded as a cited
`axiom` on the authority of [BW93] — a multiplicity-estimate / group-variety
argument we do not re-derive. -/
@[category research solved, AMS 11, ref "BW93", group "baker_wustholz"]
axiom linearForms_logs
    {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i))

end BakerWustholz
