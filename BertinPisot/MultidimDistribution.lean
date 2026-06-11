/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.UniformDistribution
import Mathlib.Order.Interval.Set.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Uniform distribution modulo one in `ℝᵖ` (Bertin §4.6)

Bertin's extension of uniform distribution modulo one from `ℝ` to `ℝᵖ` (`p ≥ 2`), modelling `ℝᵖ`
as `Fin p → ℝ`. (Here we only set up the definitions; the theorems that use them come later. The
case `p = 1` recovers the scalar notion of `BertinPisot.UniformDistribution`.)

**Order and boxes.** Following Bertin, for `a b : ℝᵖ` we write `a < b` for the *strict product
order* `∀ k, a k < b k` (Mathlib's `StrongLT`); `a ≤ b` is the usual product order. The
`p`-dimensional half-open box `[a, b[ = ∏ₖ [aₖ, bₖ[` is `boxIco a b`, and the closed/half-open/open
variants `[a, b]`, `]a, b]`, `]a, b[` are `boxIcc`, `boxIoc`, `boxIoo`. The unit cubes are
`cube = [-1/2, 1/2[ᵖ` (Bertin's `Πᵖ`) and `closedCube = [-1/2, 1/2]ᵖ` (`Π̄ᵖ`); with the constant
vector `r = (r, …, r)` these are the boxes `[-1/2, 1/2[` and `[-1/2, 1/2]`.

**Residue.** `ε x = (ε xₖ)ₖ` applies the scalar centered fractional part coordinatewise and
`E x = (round xₖ)ₖ ∈ ℤᵖ` is the nearest-integer vector. Every `x ∈ ℝᵖ` decomposes in one and only
one way as `x = E x + ε x` with `E x ∈ ℤᵖ` and `ε x ∈ Πᵖ` (`existsUnique_intPart`, `ε_mem_cube`,
`self_eq_E_add_ε`).

**Definition 4.6.** A sequence `(xₙ)` in `ℝᵖ` is u.d. mod 1 iff for every pair `a, b ∈ Π̄ᵖ` with
`a < b`, the proportion `ν(a, b, N) / N → ∏ₖ (bₖ - aₖ)`, where `ν(a, b, N) = count` counts the
indices `n < N` with `ε(xₙ) ∈ [a, b[` (`UniformlyDistributedModOne`).

**Theorem 4.6.1** (`uniformlyDistributedModOne_iff_integralCriterion`, cited): the `ℝᵖ` Riemann-
integral criterion — `(xₙ)` is u.d. mod 1 iff `(1/N) Σ f(ε xₙ) → ∫_{Π̄ᵖ} f` for every Riemann-
integrable `f` on the closed cube. The integral is taken against the `p`-dimensional Lebesgue
measure (`volume` on `Fin p → ℝ`, the product measure). The `⟹` direction needs the multidimensional
step-approximation engine (the `ℝᵖ` analogue of `ForMathlib.…Equidistribution.IntegralCriterion`),
absent from Mathlib, so the equivalence is recorded as a cited axiom.

**Theorem 4.6.2** (`uniformlyDistributedModOne_iff_weylCriterion`, cited): the `ℝᵖ` Weyl criterion —
`(xₙ)` is u.d. mod 1 iff `(1/N) Σ exp(2πi ⟨h, xₙ⟩) → 0` for every lattice point `h ∈ ℤᵖ \ {0}`
(`⟨·,·⟩` the dot product). The forward direction reduces to Theorem 4.6.1 (plus a Fubini integral
computation), the converse to Fourier density on the `p`-torus; both cited.

**Theorem 4.6.3** (`uniformlyDistributedModOne_nα`): if `1, α₁, …, αₚ` are ℚ-linearly independent then
`(nα)` is u.d. mod 1 in `ℝᵖ` (the Kronecker–Weyl theorem). The Weyl-sum vanishing `weylCriterion_nα`
is **proved** axiom-free — `⟨h,α⟩` is irrational for `h ≠ 0`, reducing to the 1-D geometric bound — and
4.6.3 follows from it via the (cited) Theorem 4.6.2.

**Theorem 4.6.4** (`kronecker_theorem_4_6_4`, cited): the inhomogeneous Kronecker theorem — under the
same independence hypothesis, for any target `μ ∈ ℝᵖ`, index `N` and tolerance `η > 0` there is `n > N`
with `|εₖ(nα − μ)| < η` for all `k`. Follows from the equidistribution 4.6.3 (torus box-hitting);
cited.

**Theorem 4.6.5** (`uniformlyDistributedModOne_sum_comp_continuous_iff`, cited): for `(xₙ)` u.d. in
`ℝᵖ` and `φ` continuous on `[-1/2, 1/2]`, the real sequence `yₙ = Σₖ φ(εₖ(xₙ))` is u.d. mod 1 iff
`∫_{-1/2}^{1/2} exp(2πi h φ) = 0` for all `h ≠ 0` (the `ℝᵖ` analogue of Theorem 4.3.3). Proved in
Bertin via Weyl (4.3.2) + the integral criterion (4.6.1) + Fubini; cited.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.6.
-/

namespace Bertin.Multidim

open Filter MeasureTheory
open scoped Topology

variable {p : ℕ}

/-! ### `p`-dimensional intervals and the unit cubes

Bertin's order `a < b` on `ℝᵖ` ("strictly less in every coordinate") is Mathlib's `StrongLT a b`
(`∀ k, a k < b k`); `a ≤ b` is the product order `Pi.le`. -/

/-- The closed `p`-dimensional box `[a, b] = ∏ₖ [aₖ, bₖ]` (`a ≤ x ≤ b` coordinatewise). -/
@[category API, AMS 11, ref "Ber92"]
def boxIcc (a b : Fin p → ℝ) : Set (Fin p → ℝ) := Set.univ.pi (fun k => Set.Icc (a k) (b k))

/-- The half-open `p`-dimensional box `[a, b[ = ∏ₖ [aₖ, bₖ[` (`a ≤ x < b` coordinatewise) — Bertin's
`[a, b[`, the box that counts residues. -/
@[category API, AMS 11, ref "Ber92"]
def boxIco (a b : Fin p → ℝ) : Set (Fin p → ℝ) := Set.univ.pi (fun k => Set.Ico (a k) (b k))

/-- The half-open `p`-dimensional box `]a, b] = ∏ₖ ]aₖ, bₖ]`. -/
@[category API, AMS 11, ref "Ber92"]
def boxIoc (a b : Fin p → ℝ) : Set (Fin p → ℝ) := Set.univ.pi (fun k => Set.Ioc (a k) (b k))

/-- The open `p`-dimensional box `]a, b[ = ∏ₖ ]aₖ, bₖ[`. -/
@[category API, AMS 11, ref "Ber92"]
def boxIoo (a b : Fin p → ℝ) : Set (Fin p → ℝ) := Set.univ.pi (fun k => Set.Ioo (a k) (b k))

/-- Bertin's unit cube `Πᵖ = [-1/2, 1/2[ᵖ` of residues modulo one. -/
@[category API, AMS 11, ref "Ber92"]
def cube : Set (Fin p → ℝ) := Set.univ.pi (fun _ => Set.Ico (-(1/2) : ℝ) (1/2))

/-- Bertin's closed unit cube `Π̄ᵖ = [-1/2, 1/2]ᵖ`. -/
@[category API, AMS 11, ref "Ber92"]
def closedCube : Set (Fin p → ℝ) := Set.univ.pi (fun _ => Set.Icc (-(1/2) : ℝ) (1/2))

/-! ### The integer part `E` and the residue `ε` -/

/-- The coordinatewise integer part `E x = (round xₖ)ₖ ∈ ℤᵖ`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def E (x : Fin p → ℝ) : Fin p → ℤ := fun k => round (x k)

/-- The coordinatewise centered residue `ε x = (ε xₖ)ₖ`, with `ε` the scalar centered fractional
part of `BertinPisot.DistributionModOneBasics`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def ε (x : Fin p → ℝ) : Fin p → ℝ := fun k => Bertin.ε (x k)

/-- `ε x ∈ Πᵖ`: every coordinate of the residue lies in `[-1/2, 1/2)`. -/
@[category API, AMS 11, ref "Ber92", formal_uses Bertin.ε_mem_Ico]
theorem ε_mem_cube (x : Fin p → ℝ) : ε x ∈ cube := by
  rw [cube, Set.mem_univ_pi]
  exact fun k => Bertin.ε_mem_Ico (x k)

/-- The decomposition `x = E x + ε x`, coordinatewise `xₖ = round xₖ + ε xₖ`. -/
@[category API, AMS 11, ref "Ber92"]
theorem self_eq_E_add_ε (x : Fin p → ℝ) : x = (fun k => (E x k : ℝ)) + ε x := by
  funext k
  simp only [Pi.add_apply, E, ε, Bertin.ε]
  ring

/-- Bertin's decomposition `x = E x + ε x` holds in **one and only one way**: there is a unique
integer vector `e = E x` with `x - e ∈ Πᵖ` (equivalently `ε x ∈ Πᵖ`). -/
@[category textbook, AMS 11, ref "Ber92",
  formal_uses Bertin.existsUnique_intPart Bertin.ε_mem_Ico]
theorem existsUnique_intPart (x : Fin p → ℝ) :
    ∃! e : Fin p → ℤ, x - (fun k => (e k : ℝ)) ∈ cube := by
  refine ⟨E x, ?_, ?_⟩
  · simp only [cube, Set.mem_univ_pi, Pi.sub_apply]
    intro k
    have h := Bertin.ε_mem_Ico (x k)
    rw [Bertin.ε] at h
    simpa [E] using h
  · intro e he
    simp only [cube, Set.mem_univ_pi, Pi.sub_apply] at he
    funext k
    have hk : x k - (e k : ℝ) ∈ Set.Ico (-(1/2) : ℝ) (1/2) := he k
    have hround : x k - ((round (x k) : ℤ) : ℝ) ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
      have h := Bertin.ε_mem_Ico (x k); rwa [Bertin.ε] at h
    simpa [E] using (Bertin.existsUnique_intPart (x k)).unique hk hround

/-! ### Definition 4.6 — uniform distribution modulo one in `ℝᵖ` -/

/-- `ν(a, b, N)`: the number of indices `n < N` for which the residue `ε(xₙ)` lies in the half-open
box `[a, b[` (intended for `a, b ∈ Π̄ᵖ`, `a < b`). -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def count (x : ℕ → Fin p → ℝ) (a b : Fin p → ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun n => ε (x n) ∈ boxIco a b)).card

/-- Sanity check: the count `ν(a, b, N)` never exceeds `N`. -/
@[category test, AMS 11, ref "Ber92"]
theorem count_le (x : ℕ → Fin p → ℝ) (a b : Fin p → ℝ) (N : ℕ) : count x a b N ≤ N := by
  classical
  simp only [count]
  exact le_trans (Finset.card_filter_le _ _) (Finset.card_range N).le

/-- **Definition 4.6** (Bertin). A sequence `(xₙ)` in `ℝᵖ` is *uniformly distributed modulo one*
(u.d. mod 1) iff for every pair `a, b ∈ Π̄ᵖ` with `a < b` (strictly in every coordinate), the
proportion of indices `n < N` whose residue lies in `[a, b[` tends to the volume `∏ₖ (bₖ - aₖ)` of
the box:  `ν(a, b, N) / N → ∏ₖ (bₖ - aₖ)`. -/
@[category API, AMS 11, ref "Ber92"]
def UniformlyDistributedModOne (x : ℕ → Fin p → ℝ) : Prop :=
  ∀ a b : Fin p → ℝ, a ∈ closedCube → b ∈ closedCube → StrongLT a b →
    Tendsto (fun N : ℕ => (count x a b N : ℝ) / N) atTop (𝓝 (∏ k, (b k - a k)))

/-! ### Theorem 4.6.1 — the Riemann-integral criterion in `ℝᵖ` -/

/-- Lebesgue's criterion for Riemann-integrability of `f` on a set `s ⊆ ℝᵖ`: `f` is bounded on `s`
and its set of discontinuities within `s` is null for the `p`-dimensional Lebesgue measure (`volume`
on `Fin p → ℝ` is the product measure). Mirrors the scalar `Bertin.IsRiemannIntegrableOn`. -/
@[category API, AMS 11, ref "Ber92"]
def IsRiemannIntegrableOn (f : (Fin p → ℝ) → ℝ) (s : Set (Fin p → ℝ)) : Prop :=
  (∃ C, ∀ t ∈ s, |f t| ≤ C) ∧ volume {t ∈ s | ¬ ContinuousAt f t} = 0

/-- The Riemann-integral criterion for `(xₙ)` in `ℝᵖ`: for every Riemann-integrable `f` on the closed
cube `Π̄ᵖ`, the average `(1/N) Σ_{n<N} f(ε xₙ)` converges to `∫_{Π̄ᵖ} f` (the integral against the
`p`-dimensional Lebesgue measure). -/
@[category API, AMS 11, ref "Ber92"]
def IntegralCriterion (x : ℕ → Fin p → ℝ) : Prop :=
  ∀ f : (Fin p → ℝ) → ℝ, IsRiemannIntegrableOn f closedCube →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (ε (x n))) / N) atTop
      (𝓝 (∫ t in closedCube, f t))

informal_result "riemann-step-function-approximation-multidim"
  latex "On $\\mathbb{R}^p$, every Riemann-integrable function $f$ on a box is squeezed, for each $\\varepsilon > 0$, between step functions $g \\le f \\le h$ that are constant on the cells of a grid of sub-boxes, with $\\int (h - g) < \\varepsilon$ (the multidimensional Darboux / step-function approximation, equivalently convergence of upper and lower Darboux sums over dyadic box partitions to $\\int f$)."
  refs "Ber92"

/-- **Theorem 4.6.1** (Bertin). A sequence `(xₙ)` is uniformly distributed modulo one in `ℝᵖ` **if
and only if** for every Riemann-integrable function `f` on `Π̄ᵖ`,
`(1/N) Σ_{n<N} f(ε xₙ) → ∫_{Π̄ᵖ} f`.

Proof (cited). *(⟸)* Apply the criterion to the box indicator `𝟙_{[a,b[}`: it is Riemann-integrable
(bounded by `1`; its discontinuities lie in the `2p` faces of `∂[a,b[`, each contained in a coordinate
hyperplane and hence Lebesgue-null) with integral `∏ₖ (bₖ − aₖ)`, and its average is exactly
`ν(a,b,N)/N`, so the limit is the volume of the box — i.e. u.d. mod 1. *(⟹)* Approximate a Riemann-
integrable `f` from above and below by step functions constant on a grid of sub-boxes; u.d. controls
the average of each box indicator, and a dominated-convergence / step-approximation squeeze on `ℝᵖ`
passes to the limit `∫_{Π̄ᵖ} f`. This `(⟹)` direction needs the multidimensional Riemann step-
approximation engine — the `ℝᵖ` analogue of `ForMathlib.Analysis.Equidistribution.IntegralCriterion`
— which is not in Mathlib, so the equivalence is recorded as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  informal_uses "riemann-step-function-approximation-multidim"]
axiom uniformlyDistributedModOne_iff_integralCriterion (x : ℕ → Fin p → ℝ) :
    UniformlyDistributedModOne x ↔ IntegralCriterion x

/-! ### Theorem 4.6.2 — Weyl's criterion in `ℝᵖ` -/

/-- **Weyl's criterion** in `ℝᵖ`: the exponential sums `(1/N) Σ_{n<N} exp(2πi ⟨h, xₙ⟩)` vanish in the
limit, for every lattice point `h ∈ ℤᵖ \ {0}`. Here `⟨h, xₙ⟩ = Σⱼ hⱼ (xₙ)ⱼ` is the dot product. (As
in 1-D, the raw `xₙ` may stand in for the residue `ε xₙ`: `⟨h, E xₙ⟩ ∈ ℤ`, so both give the same
exponential.) -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def WeylCriterion (x : ℕ → Fin p → ℝ) : Prop :=
  ∀ h : Fin p → ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (h j : ℝ) * x n j : ℝ) : ℂ))) / N)
      atTop (𝓝 0)

informal_result "weyl-equidistribution-torus-multidim"
  latex "On the $p$-torus $\\mathbb{R}^p / \\mathbb{Z}^p$ the characters $t \\mapsto e^{2\\pi i \\langle h, t \\rangle}$, $h \\in \\mathbb{Z}^p$, span a dense subalgebra of the continuous functions (Stone–Weierstrass); hence a sequence whose Weyl sums $\\frac1N \\sum_{n<N} e^{2\\pi i \\langle h, x_n \\rangle}$ all tend to $0$ for $h \\ne 0$ is uniformly distributed modulo one — the converse half of Weyl's criterion in $\\mathbb{R}^p$."
  refs "Ber92"

/-- **Theorem 4.6.2** (Bertin). A sequence `(xₙ)` is uniformly distributed modulo one in `ℝᵖ` **if and
only if** for every lattice point `h ∈ ℤᵖ \ {0}`,
`lim_{N→∞} (1/N) Σ_{n<N} exp(2πi ⟨h, xₙ⟩) = 0`  (`WeylCriterion`).

Proof (cited). *(⟹)* By Theorem 4.6.1 applied to the continuous (hence Riemann-integrable on `Π̄ᵖ`)
functions `cos(2π⟨h,·⟩)` and `sin(2π⟨h,·⟩)`: the averages converge to `∫_{Π̄ᵖ} cos`, `∫_{Π̄ᵖ} sin`, and
`∫_{Π̄ᵖ} exp(2πi⟨h,t⟩) = ∏ⱼ ∫_{-1/2}^{1/2} exp(2πi hⱼ tⱼ) dtⱼ = 0`, since `h ≠ 0` forces some `hⱼ ≠ 0`.
*(⟸)* The multidimensional Weyl converse: the characters `exp(2πi⟨h,·⟩)`, `h ∈ ℤᵖ`, span a dense
subalgebra of `C(ℝᵖ/ℤᵖ)`, so the vanishing of every Weyl sum forces the box-counting limits of
Definition 4.6. The `⟹` direction rests on Theorem 4.6.1 (itself cited) and a product-measure (Fubini)
integral computation; the `⟸` direction on the Fourier/Stone–Weierstrass density argument on the
`p`-torus (`weyl-equidistribution-torus-multidim`), not available in Mathlib for `ℝᵖ` — so the
equivalence is recorded as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses uniformlyDistributedModOne_iff_integralCriterion,
  informal_uses "weyl-equidistribution-torus-multidim"]
axiom uniformlyDistributedModOne_iff_weylCriterion (x : ℕ → Fin p → ℝ) :
    UniformlyDistributedModOne x ↔ WeylCriterion x

/-! ### Theorem 4.6.3 — equidistribution of `(nα)` for ℚ-independent `α` -/

/-- The **Weyl sums** of `(nα)` vanish when `1, α₁, …, αₚ` are ℚ-linearly independent (encoded as
`LinearIndependent ℚ (Fin.cons 1 α)`): for every lattice point `h ∈ ℤᵖ \ {0}` the real number
`⟨h, α⟩ = Σⱼ hⱼ αⱼ` is irrational — otherwise `⟨h,α⟩ = q ∈ ℚ` would give the nontrivial ℚ-relation
`(-q)·1 + Σⱼ hⱼ·αⱼ = 0` — so the geometric Weyl-sum estimate (the 1-D
`Bertin.weylCriterion_nα_of_irrational` at exponent `1` and `α := ⟨h,α⟩`) drives the average to `0`.
Axiom-free. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses Bertin.weylCriterion_nα_of_irrational]
theorem weylCriterion_nα (α : Fin p → ℝ)
    (hα : LinearIndependent ℚ (Fin.cons (1 : ℝ) α)) :
    WeylCriterion (fun n k => (n : ℝ) * α k) := by
  intro h hh
  have hθ : Irrational (∑ j, (h j : ℝ) * α j) := by
    rw [Fintype.linearIndependent_iff] at hα
    intro hmem
    obtain ⟨q, hq⟩ := hmem
    have hsum : ∑ i, (Fin.cons (-q) (fun j => (h j : ℚ)) : Fin (p + 1) → ℚ) i •
        (Fin.cons (1 : ℝ) α : Fin (p + 1) → ℝ) i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Rat.smul_def]
      push_cast
      linear_combination -hq
    have hz := hα _ hsum
    apply hh
    funext j
    have hj := hz (Fin.succ j)
    simp only [Fin.cons_succ] at hj
    exact_mod_cast hj
  have h1d := Bertin.weylCriterion_nα_of_irrational hθ 1 one_ne_zero
  refine h1d.congr (fun N => ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have harg : ∑ j, (h j : ℝ) * ((n : ℝ) * α j) = (n : ℝ) * ∑ j, (h j : ℝ) * α j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [harg]
  push_cast
  ring

/-- **Theorem 4.6.3** (Bertin). If the reals `1, α₁, …, αₚ` are ℚ-linearly independent
(`LinearIndependent ℚ (Fin.cons 1 α)`), then the sequence `(nα) = (n α₁, …, n αₚ)` is uniformly
distributed modulo one in `ℝᵖ`. Immediate from Weyl's criterion (Theorem 4.6.2) and the vanishing of
the Weyl sums (`weylCriterion_nα`). The Weyl-sum vanishing is proved axiom-free; the passage to u.d.
goes through the cited Theorem 4.6.2, on which this result therefore rests. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses weylCriterion_nα uniformlyDistributedModOne_iff_weylCriterion]
theorem uniformlyDistributedModOne_nα (α : Fin p → ℝ)
    (hα : LinearIndependent ℚ (Fin.cons (1 : ℝ) α)) :
    UniformlyDistributedModOne (fun n k => (n : ℝ) * α k) :=
  (uniformlyDistributedModOne_iff_weylCriterion _).mpr (weylCriterion_nα α hα)

informal_result "equidistribution-dense-on-torus-multidim"
  latex "A sequence uniformly distributed modulo one in $\\mathbb{R}^p$ has residues that are dense in — indeed meet, for infinitely many indices, every sub-box of positive volume of — the torus $\\mathbb{R}^p / \\mathbb{Z}^p$. Equivalently, equidistribution modulo one implies inhomogeneous simultaneous Diophantine approximation: the orbit comes arbitrarily close, in every coordinate and for arbitrarily large index, to any prescribed target (Kronecker's theorem)."
  refs "Ber92"

/-- **Theorem 4.6.4** (Bertin — the inhomogeneous Kronecker approximation theorem). Suppose
`1, α₁, …, αₚ` are ℚ-linearly independent (`LinearIndependent ℚ (Fin.cons 1 α)`). Let `μ ∈ ℝᵖ` be an
arbitrary target vector, `N` an index and `η > 0` a tolerance. Then there is `n > N` with
`|εₖ(nα − μ)| < η` for every coordinate `k` — i.e. `nα` simultaneously approximates `μ` modulo one in
all coordinates, arbitrarily late and arbitrarily well. (Here `η` plays the role of Bertin's `ε`,
renamed to avoid the clash with the residue map `ε`.)

Proof (cited). By Theorem 4.6.3 the sequence `(nα)` is uniformly distributed modulo one in `ℝᵖ`;
hence its residues `ε(nα)` are equidistributed over — in particular dense in, and meeting for
infinitely many `n` — every sub-box of the cube of positive volume
(`equidistribution-dense-on-torus-multidim`). A small box around `ε(μ)` on the torus `ℝᵖ/ℤᵖ` (the
boundary identification absorbs the case `ε(μₖ)` near `±1/2`) is hit by infinitely many `n`, hence by
some `n > N`, and for such `n`, `εₖ(nα − μ) = εₖ(nα) − εₖ(μ)` is within `η` of `0` in each coordinate.
The result rests on the cited Theorem 4.6.2 (through 4.6.3), and the torus box-hitting argument is not
developed here, so it is recorded as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses uniformlyDistributedModOne_nα,
  informal_uses "equidistribution-dense-on-torus-multidim"]
axiom kronecker_theorem_4_6_4 (α : Fin p → ℝ)
    (hα : LinearIndependent ℚ (Fin.cons (1 : ℝ) α))
    (μ : Fin p → ℝ) (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, N < n ∧ ∀ k, |ε (fun j => (n : ℝ) * α j - μ j) k| < η

/-! ### Theorem 4.6.5 — image of a u.d. sequence under `Σₖ φ(εₖ ·)` -/

informal_result "uniform-distribution-image-continuous-map"
  latex "Weyl's principle on continuous images of a uniformly distributed sequence: if $(x_n)$ is uniformly distributed modulo one (in $\\mathbb{R}$ or $\\mathbb{R}^p$) and $\\varphi$ is Riemann-integrable, then $\\frac1N \\sum_{n<N} \\varphi(\\varepsilon(x_n)) \\to \\int \\varphi$ over the unit cube; consequently a continuous image is itself uniformly distributed if and only if the integrals $\\int \\exp(2\\pi i h\\,\\varphi)$ vanish for every $h \\ne 0$. This is the mechanism behind Theorems 4.3.3 and 4.6.5."
  refs "Ber92"

informal_result "product-measure-integral-factorization"
  latex "Factorization of the integral of a separable product over a product (cube) measure (Fubini/Tonelli): $\\int_{\\bar\\Pi^p} \\prod_{k=1}^p \\Phi(t_k)\\,dt = \\prod_{k=1}^p \\int_{-1/2}^{1/2} \\Phi(t_k)\\,dt_k = \\left(\\int_{-1/2}^{1/2} \\Phi\\right)^p$ for integrable $\\Phi$ — the integral over the cube of a function that separates as a product of one-variable factors is the product of the one-dimensional integrals."
  refs "Ber92"

/-- **Theorem 4.6.5** (Bertin). Let `(xₙ)` be uniformly distributed modulo one in `ℝᵖ` and `φ` a
function continuous on `[-1/2, 1/2]`. Then the **real** sequence `yₙ = Σₖ φ(εₖ(xₙ))` is uniformly
distributed modulo one **if and only if**
`∫_{-1/2}^{1/2} exp(2πi h φ(t)) dt = 0` for every non-zero integer `h`.

Proof (cited). By Weyl's criterion (Theorem 4.3.2) `(yₙ)` is u.d. mod 1 iff its Weyl sums
`(1/N) Σ exp(2πi h yₙ)` vanish. Since `exp(2πi h yₙ) = ∏ₖ exp(2πi h φ(εₖ xₙ))`, that sum is the
`ℝᵖ`-average `(1/N) Σ F_h(ε xₙ)` of `F_h(t) = ∏ₖ exp(2πi h φ(tₖ))`, which by the `ℝᵖ` integral
criterion (Theorem 4.6.1, applied to the continuous — hence Riemann-integrable on `Π̄ᵖ` — real and
imaginary parts of `F_h`) converges to `∫_{Π̄ᵖ} F_h = (∫_{-1/2}^{1/2} exp(2πi h φ(t)) dt)ᵖ` (Fubini
over the product measure, `product-measure-integral-factorization`). So the Weyl sums vanish for all
`h ≠ 0` iff `(∫…)ᵖ = 0`, i.e. iff the integral does — the image-under-a-continuous-map mechanism
(`uniform-distribution-image-continuous-map`). The argument rests on the cited Theorems 4.3.2 (1-D
Weyl) and 4.6.1 (`ℝᵖ` integral criterion), so it is recorded as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses _root_.Bertin.uniformlyDistributedModOne_iff_weylCriterion
    uniformlyDistributedModOne_iff_integralCriterion,
  informal_uses "uniform-distribution-image-continuous-map"
    "product-measure-integral-factorization"]
axiom uniformlyDistributedModOne_sum_comp_continuous_iff (x : ℕ → Fin p → ℝ)
    (hx : UniformlyDistributedModOne x) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc (-(1/2) : ℝ) (1/2))) :
    _root_.Bertin.UniformlyDistributedModOne (fun n => ∑ k, φ (ε (x n) k)) ↔
      ∀ h : ℤ, h ≠ 0 →
        (∫ t in (-(1/2) : ℝ)..(1/2), Complex.exp (2 * Real.pi * Complex.I * h * φ t)) = 0

end Bertin.Multidim
