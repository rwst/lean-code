/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Equidistribution.ModOne
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ForMathlib.Analysis.Equidistribution.VanDerCorput
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bugeaud, Chapter 1 — Uniform distribution modulo one

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, Cambridge University Press, 2012), Chapter 1.

**Definition 1.1** (uniform distribution / density modulo one) is upstream-flavoured and lives in
`ForMathlib.Analysis.Equidistribution.ModOne` as `IsEquidistributedModuloOne` and
`IsDenseModuloOne`. This file formalises **Theorem 1.2**, the two equivalent criteria for uniform
distribution modulo one:

* the **continuous-periodic (integral) criterion** (`theorem_1_2`): `(xₙ)` is u.d. mod 1 iff for
  every continuous, 1-periodic, complex-valued `f`, `(1/N) Σ_{n<N} f(xₙ) → ∫₀¹ f`;
* **Weyl's criterion** (`theorem_1_2_weyl`): equivalently, `(1/N) Σ_{n<N} e^{2πi h xₙ} → 0` for
  every non-zero integer `h`.

Bugeaud's proof: the first equivalence "follows from the definition of the Riemann integral"
(the indicator of a subinterval is squeezed between continuous 1-periodic functions); the second is
"an immediate application of the approximation theorem of Stone–Weierstrass", since finite
ℂ-linear combinations of the characters `x ↦ e^{2πi h x}`, `h ∈ ℤ`, are sup-norm dense in the
continuous 1-periodic functions.

The character half of `ContinuousPeriodicCriterion ↔ WeylCriterion` is proved here
(`weylCriterion_of_continuousPeriodicCriterion`); the two deep directions are recorded as cited
results, with axiom-free engines available in `ForMathlib`:
* the Riemann/step-function approximation in `ForMathlib.Analysis.Equidistribution.IntegralCriterion`;
* the harmonic-analytic Stone–Weierstrass core `tendsto_average_of_tendsto_fourier` (on `AddCircle 1`)
  in `ForMathlib.Analysis.Equidistribution.AddCircleWeyl`.

The Bertin-corpus counterparts state the same content for the centered-`ε` convention on
`[-1/2, 1/2]` and a larger (Riemann-integrable) test class:
`Bertin.uniformlyDistributedModOne_iff_integralCriterion` (Theorem 4.3.1) and
`Bertin.uniformlyDistributedModOne_iff_weylCriterion` (Theorem 4.3.2).

Bugeaud's **Theorem 1.3** (`(nα)` is u.d. mod 1 for every irrational `α`, via the geometric
Weyl-sum bound) and **Theorem 1.4** (`(P(n))` is u.d. mod 1 when the real polynomial `P` has an
irrational coefficient in some degree `≥ 1`, via van der Corput) are not restated here: both are
already in the corpus, as the stronger iffs `Bertin.uniformlyDistributedModOne_nα_iff_irrational`
and `Bertin.uniformlyDistributedModOne_eval_iff_exists_irrational_coeff` respectively.

**Lemma 1.5** (`vanDerCorput_lemma_1_5`) records **van der Corput's fundamental inequality** (with
step `a`) — the Cauchy–Schwarz/counting estimate underpinning the van der Corput difference method
(the engine of `Bertin.vanDerCorput_theorem_4_4_1`). It is cited, with Bugeaud's proof transcribed in
its docstring.

*References:*
  - [Bug12] Bugeaud, Yann. *Distribution Modulo One and Diophantine Approximation.* Cambridge
    Tracts in Mathematics 193, Cambridge University Press, 2012. Chapter 1 (Theorem 1.2, Lemma 1.5).
  - [vdC31] van der Corput, Johannes Gualtherus. "Diophantische Ungleichungen. I. Zur
    Gleichverteilung modulo Eins." *Acta Mathematica* 56.1 (1931), 373–456.
-/

namespace Bugeaud

open Filter Topology

/-- Bugeaud's **continuous-periodic test-function criterion**: for every continuous, 1-periodic,
complex-valued `f`, the averages `(1/N) Σ_{n<N} f(xₙ)` converge to `∫₀¹ f`. This is the
test-function class appearing in Theorem 1.2; cf. the larger Riemann-integrable class of Bertin's
Theorem 4.3.1 (`Bertin.IntegralCriterion`). -/
@[category API, AMS 11, ref "Bug12"]
def ContinuousPeriodicCriterion (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, Continuous f → Function.Periodic f 1 →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t))

/-- **Weyl's criterion** condition: the exponential sums `(1/N) Σ_{n<N} e^{2πi h xₙ}` vanish in the
limit, for every non-zero integer `h`. -/
@[category API, AMS 11, ref "Bug12"]
noncomputable def WeylCriterion (x : ℕ → ℝ) : Prop :=
  ∀ h : ℤ, h ≠ 0 →
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * x n)) / N) atTop (𝓝 0)

/-- The character half of the equivalence in Theorem 1.2 (the easy direction): each character
`t ↦ e^{2πi h t}` with `h ≠ 0` is continuous and 1-periodic with `∫₀¹ e^{2πi h t} dt = 0`
(`integral_exp_mul_complex`, using `e^{2πi h} = 1`), so applying the continuous-periodic criterion
to it yields the vanishing of the `h`-th Weyl sum. -/
@[category research solved, AMS 11, ref "Bug12"]
theorem weylCriterion_of_continuousPeriodicCriterion (x : ℕ → ℝ)
    (h : ContinuousPeriodicCriterion x) : WeylCriterion x := by
  intro m hm
  have hcont : Continuous (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * m * t)) := by
    fun_prop
  have hper : Function.Periodic (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * m * t)) 1 := by
    intro t
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((t : ℂ) + 1))
          = (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (t : ℂ))
            + (m : ℂ) * (2 * Real.pi * Complex.I) by ring,
       Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hint : (∫ t in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * m * t)) = 0 := by
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hm']
    rw [integral_exp_mul_complex hc]
    have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((1 : ℝ) : ℂ))
            = (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have hexp0 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((0 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((0 : ℝ) : ℂ)) = 0 by push_cast; ring,
        Complex.exp_zero]
    rw [hexp1, hexp0]; ring
  have hap := h _ hcont hper
  rwa [hint] at hap

/-- **Theorem 1.2** (Bugeaud), integral form. A sequence `(xₙ)` of real numbers is uniformly
distributed modulo one **iff**, for every continuous, 1-periodic, complex-valued `f`,
`(1/N) Σ_{n<N} f(xₙ) → ∫₀¹ f(x) dx`.

Bugeaud's proof: this "follows from the definition of the Riemann integral" — the indicator of a
subinterval `[c, d) ⊆ [0, 1)` is squeezed between continuous 1-periodic functions, so the
interval-counting Definition 1.1 (`IsEquidistributedModuloOne`) is equivalent to convergence of the
averages against every continuous periodic test function. The Riemann/step-function approximation
engine is formalised axiom-free in `ForMathlib.Analysis.Equidistribution.IntegralCriterion`; the
analogous statement for the larger Riemann-integrable test class (centered-`ε` convention) is
`Bertin.uniformlyDistributedModOne_iff_integralCriterion` (Theorem 4.3.1). Recorded here as a cited
result. -/
@[category research solved, AMS 11, ref "Bug12"]
axiom theorem_1_2 (x : ℕ → ℝ) :
    IsEquidistributedModuloOne x ↔ ContinuousPeriodicCriterion x

/-- The Stone–Weierstrass half of Theorem 1.2: vanishing Weyl sums imply the continuous-periodic
criterion. Bugeaud's proof: finite ℂ-linear combinations of the characters `x ↦ e^{2πi h x}`,
`h ∈ ℤ`, are sup-norm dense in the continuous 1-periodic functions (Stone–Weierstrass), so
convergence of the averages propagates from the characters to every continuous periodic `f` by a
uniform-approximation squeeze. The harmonic-analytic core is formalised axiom-free as
`tendsto_average_of_tendsto_fourier` (on `AddCircle 1`,
`ForMathlib.Analysis.Equidistribution.AddCircleWeyl`); transporting it across the
`ℝ/ℤ ≃ AddCircle 1` identification is a separate development, so this direction is recorded as a
cited result. -/
@[category research solved, AMS 11, ref "Bug12"]
axiom continuousPeriodicCriterion_of_weylCriterion (x : ℕ → ℝ)
    (h : WeylCriterion x) : ContinuousPeriodicCriterion x

/-- **Theorem 1.2** (Bugeaud), Weyl form. A sequence `(xₙ)` is uniformly distributed modulo one
**iff** `lim_{N→∞} (1/N) Σ_{n<N} e^{2πi h xₙ} = 0` for every non-zero integer `h`.

Proved here by chaining the integral form (`theorem_1_2`) with the two halves of
`ContinuousPeriodicCriterion ↔ WeylCriterion`: the character direction
`weylCriterion_of_continuousPeriodicCriterion` is proved, and the Stone–Weierstrass converse
`continuousPeriodicCriterion_of_weylCriterion` is cited. -/
@[category research solved, AMS 11, ref "Bug12",
  formal_uses theorem_1_2 weylCriterion_of_continuousPeriodicCriterion
    continuousPeriodicCriterion_of_weylCriterion]
theorem theorem_1_2_weyl (x : ℕ → ℝ) :
    IsEquidistributedModuloOne x ↔ WeylCriterion x := by
  constructor
  · intro hud
    exact weylCriterion_of_continuousPeriodicCriterion x ((theorem_1_2 x).mp hud)
  · intro hw
    exact (theorem_1_2 x).mpr (continuousPeriodicCriterion_of_weylCriterion x hw)

/-! ### Lemma 1.5 — van der Corput's fundamental inequality -/

/-- **Lemma 1.5** (Bugeaud). Let `a` and `N` be positive integers, `u₁, …, u_N` complex numbers, and
`L` an integer with `1 ≤ aL ≤ N`. Then
`L² · |Σ_{n=1}^N uₙ|² ≤ L(N + a(L-1)) · Σ_{n=1}^N |uₙ|²`
` + 2(N + a(L-1)) · Σ_{ℓ=1}^{L-1} (L-ℓ) · Re Σ_{n=1}^{N-aℓ} uₙ · conj(u_{n+aℓ})`,
where `Re` denotes the real part. This is **van der Corput's fundamental inequality** (with step
`a`), the Cauchy–Schwarz estimate underpinning the van der Corput difference method (the engine of
`Bertin.vanDerCorput_theorem_4_4_1`, Theorem 4.4.1).

**Proof** (Bugeaud). Extend `(uₙ)` by `uₙ = 0` for `n ≤ 0` and `n > N`. Regrouping by `p = n + aℓ`,
`L · Σ_{n=1}^N uₙ = Σ_{p=1}^{N+a(L-1)} Σ_{ℓ=0}^{L-1} u_{p-aℓ}`. The Cauchy–Schwarz inequality on the
outer `p`-sum (which runs over `N + a(L-1)` terms) gives
`L² · |Σ_{n=1}^N uₙ|² ≤ (N+a(L-1)) · Σ_{p=1}^{N+a(L-1)} |Σ_{ℓ=0}^{L-1} u_{p-aℓ}|²`. Writing the
squared modulus as `(Σ_ℓ u_{p-aℓ})·(Σ_j conj(u_{p-aj}))` and splitting into the diagonal `ℓ = j`
and the off-diagonal `ℓ > j` (paired with its conjugate) yields
`(N+a(L-1)) Σ_p Σ_{ℓ=0}^{L-1} |u_{p-aℓ}|² + 2(N+a(L-1)) Re Σ_p Σ_{ℓ=1}^{L-1} Σ_{j=0}^{ℓ-1}`
`u_{p-aℓ}·conj(u_{p-aj})`. In the diagonal term each `uₙ` occurs for exactly `L` values of `p`, so
`Σ_p Σ_ℓ |u_{p-aℓ}|² = L Σ_{n=1}^N |uₙ|²`, giving the first summand `L(N+a(L-1)) Σ |uₙ|²`. For the
off-diagonal term set
`Σ₁ := Re Σ_{p=1}^{N+a(L-1)} Σ_{ℓ=1}^{L-1} u_{p-aℓ}·(conj(u_p) + ⋯ + conj(u_{p-a(ℓ-1)}))`. For each
`ℓ ∈ {1, …, L-1}`, as `p` ranges over `{aℓ+1, …, N}` the product `u_{p-aℓ}·conj(u_p)` — that is,
`uₙ·conj(u_{n+aℓ})` with `n = p-aℓ` — occurs exactly `L-ℓ` times in this double sum, whence
`Σ₁ = Σ_{ℓ=1}^{L-1} (L-ℓ) · Re Σ_{n=1}^{N-aℓ} uₙ·conj(u_{n+aℓ})`. Substituting gives the claim.

This is **fully proved** (sorry/axiom-free) in `ForMathlib.Analysis.Equidistribution.VanDerCorput`
as `vanDerCorput_fundamental_inequality`, of which this is the verbatim restatement; the proof
formalises the Cauchy–Schwarz step (`sq_sum_le_card_mul_sum_sq`) and the difference-counting
reindexing over the zero-extension `w : ℤ → ℂ` of `(uₙ)`. -/
@[category research solved, AMS 11, ref "Bug12" "vdC31",
  formal_uses vanDerCorput_fundamental_inequality]
theorem vanDerCorput_lemma_1_5 (a N : ℕ) (ha : 0 < a) (hN : 0 < N) (u : ℕ → ℂ)
    (L : ℕ) (hL : 1 ≤ a * L) (hLN : a * L ≤ N) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.Icc 1 N, u n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) * ∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2
      + 2 * ((N : ℝ) + (a : ℝ) * ((L : ℝ) - 1)) *
        ∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (N - a * ℓ), u n * (starRingEnd ℂ) (u (n + a * ℓ))).re :=
  vanDerCorput_fundamental_inequality a N ha u L hL hLN

end Bugeaud
