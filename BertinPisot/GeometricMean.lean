/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ForMathlib.Analysis.Complex.HardySpace
import BertinPisot.SchurClass
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The geometric mean `ℒ(g)` and boundary values (Bertin §3.2, Definition 3.2.2)

Bertin's **Definition 3.2.2** (*Pisot and Salem Numbers*, [Ber92], §3.2) together with the four
classical properties of Hardy theory it recalls. For a positive real function `g ∈ L¹(T)` on the
unit circle `T = ∂D(0,1)`, the **geometric mean**
`ℒ(g) = exp((1/2π) ∫_{-π}^{π} log g(e^{iθ}) dθ)`  (and `ℒ(g) = 0` when `log g ∉ L¹(T)`)
is the central functional of the section — classically the limit of the Toeplitz/Szegő determinant
ratios and, in Bertin's number-theoretic setting, the analytic incarnation of the Mahler measure.

* `Complex.geometricMean g` is `ℒ(g)`, with the `(1/2π) ∫` over a period encoded as the unit-circle
  average `Real.circleAverage (Real.log ∘ g) 0 1` and `log g ∈ L¹(T)` as the canonical
  `CircleIntegrable (Real.log ∘ g) 0 1`. (`∫_{-π}^{π}` and `∫₀^{2π}` agree, the integrand being
  `2π`-periodic in `θ`.)
* `Complex.boundaryFun f` is the radial **boundary function** `f̂(w) = lim_{r→1⁻} f(r w)`
  (`Filter.limUnder` along `𝓝[<] 1`), the object of properties iii)–iv).

## Recalled properties (Bertin)

"We recall the following properties" — classical Hardy-space theorems, none yet in Mathlib, recorded
here as `cited` axioms (asserted on the authority of their citations):

* `Complex.geometricMean_mul` — **i)** multiplicativity `ℒ(g₁ g₂) = ℒ(g₁) ℒ(g₂)` for positive
  `g₁, g₂, g₁g₂ ∈ L¹(T)`.
* `Complex.geometricMean_eq_iInf_circleAverage` — **ii) Szegő's theorem**: `ℒ(g)` is the infimum,
  over polynomials `P` with `P(0) = 1`, of `(1/2π) ∫₀^{2π} |P(e^{iθ})|² g(e^{iθ}) dθ`.
* `Complex.boundaryFun_ae_and_memLp_of_memHardy` — **iii) Fatou's theorem**: for `α ≥ 1` and
  `f ∈ Hᵅ`, the radial limit `f̂` exists for almost every `θ` and `f̂ ∈ Lᵅ(T)`.
* `Complex.circleAverage_log_boundaryFun_ge` — **iv) Jensen's inequality** (`H¹`):
  `(1/2π) ∫₀^{2π} log|f̂| ≥ log|f(0)|` for `f ∈ H¹`, `f(0) ≠ 0`; and
* `Complex.geometricMean_boundaryFun_eq` — its corollary "in particular": `ℒ(|f̂|) = |f(0)|` when
  `f` and `1/f` both lie in `H¹` (then `f` is outer; apply iv) to `f` and to `1/f`).

`Complex.MemHardy` (`Hᵅ`) is reused from `ForMathlib.Analysis.Complex.HardySpace`.

## Theorem 3.2.2 — the Szegő limit for `𝓜`

`Complex.schurDelta_ratio_tendsto_geometricMean` is **Theorem 3.2.2** (Bertin; originally
D. W. Boyd [Boy77]), the analytic payoff:
for `f ∈ 𝓜` of infinite rank, the consecutive Schur-determinant ratios converge to the geometric
mean of the boundary spectral density,
`ℒ(1 − |f̂|²) = lim_{n→∞} δₙ(f)/δₙ₋₁(f)`.
The ratios `δₙ/δₙ₋₁ = ωₙ` are Corollary 3.2.1's Schur parameters and the identity is the Szegő limit
theorem in Toeplitz-determinant form. It links the `𝓜`/Schur-determinant strand of
`BertinPisot.SchurClass` (whence this file imports `schurDelta`, `taylorSeries`, `schurClass`,
`HasIndefiniteRank`) to the geometric mean `ℒ` and the boundary function `f̂` defined here. A `cited`
axiom.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
  (Definition 3.2.2.)
* [Boy77] Boyd, David W. *Pisot numbers and the width of meromorphic functions.* Privately circulated
  manuscript, 1977. (Original source of Theorem 3.2.2.)
* [Fat06] Fatou, Pierre. *Séries trigonométriques et séries de Taylor.* Acta Math. **30** (1906),
  335–400. (Radial boundary values, property iii.)
-/

/-! ## Informal-result registry

The classical Hardy-theory theorems these recalled properties name, recorded at the level of "what
notion the proof needs", registry-keyed so the `informal_uses` edges below resolve to canonical
nodes. -/

informal_result "szego-infimum-theorem"
  latex "Szegő's theorem (G. Szegő, 1915–1920): for a positive function g ∈ L¹ of the unit circle T, the geometric mean ℒ(g) = exp((1/2π)∫ log g(e^{iθ}) dθ) equals the infimum, over polynomials P with P(0)=1, of the weighted quadratic mean (1/2π)∫ |P(e^{iθ})|² g(e^{iθ}) dθ. Equivalently it is the limit of the ratios Dₙ/Dₙ₋₁ of the Toeplitz determinants of the Fourier coefficients of g, identifying ℒ(g) with the one-step prediction error of the stationary process with spectral density g."
  refs "Ber92"

informal_result "fatou-radial-boundary-values"
  latex "Fatou's theorem on radial boundary values (P. Fatou, 1906): a function f in the Hardy space Hᵅ (α ≥ 1) on the open unit disk D(0,1) has radial limits f̂(e^{iθ}) = lim_{r→1⁻} f(r e^{iθ}) for almost every θ, and the boundary function f̂ belongs to Lᵅ(T); moreover f is recovered from f̂ by the Poisson integral and ‖f‖_{Hᵅ} = ‖f̂‖_{Lᵅ}. (Distinct from Fatou's lemma in measure theory and from Fatou's theorem on rational power series.)"
  refs "Ber92" "Fat06"

informal_result "jensen-inequality-hardy"
  latex "Jensen's inequality for the Hardy space H¹: if f ∈ H¹ on the unit disk and f(0) ≠ 0, then the logarithmic average of the boundary modulus dominates the value at the centre, (1/2π)∫ log|f̂(e^{iθ})| dθ ≥ log|f(0)|. It is the boundary form of Jensen's formula, the inequality reflecting the non-negative contribution of the zeros of f inside the disk; equality holds iff f is zero-free (outer). In particular, if f and 1/f both lie in H¹ then f is outer and ℒ(|f̂|) = |f(0)|."
  refs "Ber92"

open Filter Topology MeasureTheory

namespace Complex

open Classical in
/-- **Definition 3.2.2** (Bertin). For a positive real function `g ∈ L¹(T)` on the unit circle
`T = ∂D(0,1)`, the **geometric mean** `ℒ(g)`: the exponential of the logarithmic average of `g` over
the circle when `log g ∈ L¹(T)`, and `0` otherwise —
`ℒ(g) = exp((1/2π) ∫_{-π}^{π} log g(e^{iθ}) dθ)` if `log g ∈ L¹(T)`, else `ℒ(g) = 0`. The `(1/2π) ∫`
over a period is `Real.circleAverage (Real.log ∘ g) 0 1`, the average over the unit circle, and
`log g ∈ L¹(T)` is `CircleIntegrable (Real.log ∘ g) 0 1`. -/
@[category API, AMS 30 42, ref "Ber92"]
noncomputable def geometricMean (g : ℂ → ℝ) : ℝ :=
  if CircleIntegrable (fun z => Real.log (g z)) 0 1 then
    Real.exp (Real.circleAverage (fun z => Real.log (g z)) 0 1)
  else 0

/-- The radial **boundary function** `f̂` of `f` on the unit circle `T`: `f̂(w) = lim_{r→1⁻} f(r w)`
(the radial limit, `Filter.limUnder` of `r ↦ f(r · w)` along `𝓝[<] 1`). For `f ∈ Hᵅ` (`α ≥ 1`) this
limit exists for almost every `w ∈ T` and `f̂ ∈ Lᵅ(T)` (`boundaryFun_ae_and_memLp_of_memHardy`,
Bertin's property iii). Where the radial limit fails to exist, `limUnder` returns a junk value. -/
@[category API, AMS 30, ref "Ber92"]
noncomputable def boundaryFun (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => limUnder (𝓝[<] (1 : ℝ)) (fun r : ℝ => f ((r : ℂ) * w))

/-- **Property i)** (Bertin, recalled). The geometric mean is **multiplicative**: if
`g₁, g₂, g₁g₂ ∈ L¹(T)` are all positive real functions on the unit circle, then
`ℒ(g₁ g₂) = ℒ(g₁) ℒ(g₂)`. (For `log g₁, log g₂ ∈ L¹(T)` this is `log(g₁g₂) = log g₁ + log g₂` under
the average and `exp(a+b) = exp a · exp b`; the value-`0` branches are part of the recalled
statement.) A `cited` axiom (`ref "Ber92"`). -/
@[category research solved, AMS 30 42, ref "Ber92", formal_uses geometricMean]
axiom geometricMean_mul {g₁ g₂ : ℂ → ℝ}
    (hg₁ : (∀ θ : ℝ, 0 < g₁ (circleMap 0 1 θ)) ∧ CircleIntegrable g₁ 0 1)
    (hg₂ : (∀ θ : ℝ, 0 < g₂ (circleMap 0 1 θ)) ∧ CircleIntegrable g₂ 0 1)
    (hg₁₂ : CircleIntegrable (fun z => g₁ z * g₂ z) 0 1) :
    geometricMean (fun z => g₁ z * g₂ z) = geometricMean g₁ * geometricMean g₂

/-- **Property ii)** (Bertin, recalled — **Szegő's theorem**). For a positive real function
`g ∈ L¹(T)`, the geometric mean equals the infimum, over polynomials `P` with `P(0) = 1`, of the
weighted quadratic mean `(1/2π) ∫₀^{2π} |P(e^{iθ})|² g(e^{iθ}) dθ`:
`ℒ(g) = inf_{P(0)=1} (1/2π) ∫₀^{2π} |P(e^{iθ})|² g(e^{iθ}) dθ`. A `cited` axiom
(`ref "Ber92"`; `informal_uses "szego-infimum-theorem"`). -/
@[category research solved, AMS 30 42, ref "Ber92",
  formal_uses geometricMean, informal_uses "szego-infimum-theorem"]
axiom geometricMean_eq_iInf_circleAverage {g : ℂ → ℝ}
    (hgpos : ∀ θ : ℝ, 0 < g (circleMap 0 1 θ)) (hg : CircleIntegrable g 0 1) :
    geometricMean g =
      ⨅ P ∈ {P : Polynomial ℂ | Polynomial.eval 0 P = 1},
        Real.circleAverage (fun z => ‖Polynomial.eval z P‖ ^ 2 * g z) 0 1

/-- **Property iii)** (Bertin, recalled — **Fatou's theorem** on radial boundary values). If `α ≥ 1`
and `f ∈ Hᵅ`, then the radial limit `f̂(e^{iθ}) = lim_{r→1⁻} f(r e^{iθ})` exists for almost every
`θ ∈ [0, 2π]`, and the boundary function `f̂ = boundaryFun f` belongs to `Lᵅ(T)` (i.e.
`|f̂|^α` is circle-integrable). A `cited` axiom (`ref "Ber92" "Fat06"`;
`informal_uses "fatou-radial-boundary-values"`). -/
@[category research solved, AMS 30, ref "Ber92" "Fat06",
  formal_uses boundaryFun MemHardy, informal_uses "fatou-radial-boundary-values"]
axiom boundaryFun_ae_and_memLp_of_memHardy {α : ℝ} (hα : 1 ≤ α) {f : ℂ → ℂ} (hf : MemHardy α f) :
    (∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))),
        ∃ L : ℂ, Tendsto (fun r : ℝ => f ((r : ℂ) * circleMap 0 1 θ)) (𝓝[<] 1) (𝓝 L)) ∧
      CircleIntegrable (fun z => ‖boundaryFun f z‖ ^ α) 0 1

/-- **Property iv)** (Bertin, recalled — **Jensen's inequality** for `H¹`). If `f ∈ H¹` and
`f(0) ≠ 0`, then the logarithmic average of the boundary modulus dominates the value at the centre:
`(1/2π) ∫₀^{2π} log|f̂(e^{iθ})| dθ ≥ log|f(0)|`. A `cited` axiom (`ref "Ber92"`;
`informal_uses "jensen-inequality-hardy"` — the boundary form of Jensen's formula). -/
@[category research solved, AMS 30, ref "Ber92",
  formal_uses boundaryFun MemHardy, informal_uses "jensen-inequality-hardy"]
axiom circleAverage_log_boundaryFun_ge {f : ℂ → ℂ} (hf : MemHardy 1 f) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ Real.circleAverage (fun z => Real.log ‖boundaryFun f z‖) 0 1

/-- **Property iv), "in particular"** (Bertin, recalled). If both `f` and `1/f` belong to `H¹` — so
`f` is **outer** and `f(0) ≠ 0` — then the geometric mean of the boundary modulus is exactly the
value at the centre: `ℒ(|f̂|) = |f(0)|`. (Bertin's derivation: apply property iv) to `f` and to
`1/f`; the two inequalities `(1/2π) ∫ log|f̂| ≥ log|f(0)|` and `≤` combine to equality, whence
`ℒ(|f̂|) = exp((1/2π) ∫ log|f̂|) = |f(0)|`.) A `cited` axiom (`ref "Ber92"`). -/
@[category research solved, AMS 30, ref "Ber92",
  formal_uses geometricMean boundaryFun MemHardy circleAverage_log_boundaryFun_ge,
  informal_uses "jensen-inequality-hardy"]
axiom geometricMean_boundaryFun_eq {f : ℂ → ℂ} (hf : MemHardy 1 f)
    (hfinv : MemHardy 1 (fun z => (f z)⁻¹)) :
    geometricMean (fun z => ‖boundaryFun f z‖) = ‖f 0‖

/-- **Theorem 3.2.2** (Bertin). Let `f ∈ 𝓜` be of **infinite rank** (`HasIndefiniteRank f`: the
Schur determinants `δₙ(f)` never eventually vanish — so for `f ∈ 𝓜` all `δₙ(f) > 0` by Theorem 3.2.1
and the ratios below are well defined), with radial boundary function `f̂ = boundaryFun f`
(`f̂(e^{iθ}) = lim_{r→1⁻} f(r e^{iθ})` a.e.; `f̂ ∈ L²(T)` since `𝓜 ⊆ H²`, by Fatou's theorem,
property iii). Then the **geometric mean of `1 − |f̂|²` is the limit of the consecutive
Schur-determinant ratios**:
`ℒ(1 − |f̂|²) = lim_{n→∞} δₙ(f) / δₙ₋₁(f)`.

This is the analytic payoff of the section: the ratios `δₙ/δₙ₋₁ = ωₙ` (Corollary 3.2.1) converge to
the geometric mean of the boundary spectral density `1 − |f̂|²` — the Szegő limit theorem in the
Schur/Toeplitz determinant form. Originally due to **D. W. Boyd** [Boy77]; recorded as a `cited`
axiom (`ref "Ber92" "Boy77"`); the `informal_uses` name Szegő's theorem (`szego-infimum-theorem`) and
the Fatou boundary values (`fatou-radial-boundary-values`). -/
@[category research solved, AMS 30 15 42, ref "Ber92" "Boy77",
  formal_uses geometricMean boundaryFun schurDelta taylorSeries schurClass HasIndefiniteRank,
  informal_uses "szego-infimum-theorem" "fatou-radial-boundary-values"]
axiom schurDelta_ratio_tendsto_geometricMean {f : ℂ → ℂ} (hf : f ∈ schurClass)
    (hrank : HasIndefiniteRank f) :
    Tendsto (fun n => schurDelta (taylorSeries f) (n + 1) / schurDelta (taylorSeries f) n)
      atTop (𝓝 ((geometricMean (fun z => 1 - ‖boundaryFun f z‖ ^ 2) : ℝ) : ℂ))

end Complex
