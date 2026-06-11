/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowMod1
import BertinPisot.MeromorphicCoeffVanishing
import ForMathlib.RingTheory.PowerSeries.Rationality
import Mathlib.RingTheory.Localization.Integral
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# §5.4 — distribution of `λθⁿ` for a Pisot number `θ` (Bertin §5.4)

Bertin's **§5.4** opens the study of the sequences `(λθⁿ)` for `θ` an `S`-number (Pisot) and `λ` an
algebraic integer of `ℚ(θ)`:

> Let `θ` be an `S`-number and `λ` an algebraic integer of `ℚ(θ)`; the real
> `λθⁿ + ∑_{j=2}^{s} λ⁽ʲ⁾θ⁽ʲ⁾ⁿ` is a rational integer. One then proves as in Theorem 5.3.1 that the
> sequence `(‖λθⁿ‖)` converges to zero geometrically.

This file formalizes those two opening lemmas. They generalize Theorem 5.3.1 (the `λ = 1` case): write
`λ` as `μ : ℚ⟮θ⟯` with `μ` integral over `ℤ` (so `(μ : ℝ) = λ` is the real value).

**Lemma 1 — `trace_smul_pow_isInt` (proved).** `λθⁿ + ∑_{j=2}^{s} λ⁽ʲ⁾θ⁽ʲ⁾ⁿ` is exactly the trace
`Tr_{ℚ(θ)/ℚ}(λθⁿ) = ∑_σ σ(λθⁿ)` over the embeddings `σ : ℚ(θ) ↪ ℂ`. Since `λθⁿ` is an algebraic
integer (a product of the integers `λ` and `θⁿ`), its trace is an algebraic integer lying in `ℚ`,
hence in `ℤ` (`Algebra.isIntegral_trace`, `IsIntegrallyClosed.isIntegral_iff`). This is the direct
generalization of `conj_powerSum_isInt` (the `λ = 1` power sum of conjugates).

**Lemma 2 — `pisot_smul_pow_approx_int` (proved).** For `θ ∈ S` the embeddings split into the
distinguished real one `σ₀` (`σ₀ θ = θ`, `σ₀ λ = λ`) and the others, for which `|σ θ| < 1` (the Pisot
condition, since each `σ θ ≠ θ` is a conjugate of `θ`). Hence
`λθⁿ − Tr(λθⁿ) = −∑_{σ ≠ σ₀} σ(λ)·(σθ)ⁿ`, of modulus `≤ (∑_σ |σλ|)·δⁿ` with `δ = max_{σ≠σ₀}|σθ| < 1`.
With Lemma 1 (`Tr ∈ ℤ`) this gives an integer `k` with `|λθⁿ − k| ≤ C·δⁿ`, i.e. `‖λθⁿ‖ ≤ C·δⁿ`
("`(‖λθⁿ‖)` converges to zero geometrically"). The plain limit `‖λθⁿ‖ → 0` is the corollary
`pisot_smul_pow_tendsto_zero` (a squeeze, exactly as for Theorem 5.3.1).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.4.
-/

open Filter Topology Polynomial IntermediateField
open scoped PowerSeries

namespace Bertin

/-- The nearest integer minimises the distance: `distToNearestInt x ≤ |x − k|` for every integer `k`.
(Local copy of the helper from `AlphaPowMod1`; private there.) -/
private lemma distToNearestInt_le_int (x : ℝ) (k : ℤ) : distToNearestInt x ≤ |x - (k : ℝ)| := by
  rw [distToNearestInt]
  by_cases h : (1 : ℝ) / 2 ≤ |x - (k : ℝ)|
  · exact (abs_sub_round x).trans h
  · push Not at h
    have hrk : round x = k := by
      have hlt : |(round x : ℝ) - (k : ℝ)| < 1 := by
        have e : (round x : ℝ) - (k : ℝ) = ((round x : ℝ) - x) + (x - (k : ℝ)) := by ring
        rw [e]
        calc |((round x : ℝ) - x) + (x - (k : ℝ))|
            ≤ |(round x : ℝ) - x| + |x - (k : ℝ)| := abs_add_le _ _
          _ = |x - (round x : ℝ)| + |x - (k : ℝ)| := by rw [abs_sub_comm]
          _ < 1 := by linarith [abs_sub_round x]
      have h1 : |round x - k| < 1 := by
        have h2 : ((|round x - k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; push_cast; exact hlt
        exact_mod_cast h2
      have := Int.abs_lt_one_iff.mp h1
      omega
    exact le_of_eq (by rw [hrk])

/- The number-theoretic input of §5.4 — the generalized trace fact. For an algebraic integer `θ` and
an algebraic integer `λ ∈ ℚ(θ)`, the conjugate sum `λθⁿ + ∑_{j=2}^{s} λ⁽ʲ⁾θ⁽ʲ⁾ⁿ = Tr_{ℚ(θ)/ℚ}(λθⁿ)`
is a rational integer. Generalizes `conjugate-power-sum-integer` (the `λ = 1` case). **Proved** below. -/
informal_result "smul-conjugate-trace-integer"
  latex "Let $\\theta$ be an algebraic integer with conjugates $\\theta=\\theta^{(1)},\\dots,\\theta^{(s)}$, and let $\\lambda\\in\\mathbb{Q}(\\theta)$ be an algebraic integer with conjugates $\\lambda^{(j)}$ (paired with $\\theta^{(j)}$ via the embedding $\\sigma_j:\\mathbb{Q}(\\theta)\\hookrightarrow\\mathbb{C}$, $\\sigma_j(\\theta)=\\theta^{(j)}$). Then $\\lambda\\theta^n+\\sum_{j=2}^{s}\\lambda^{(j)}{\\theta^{(j)}}^{n}=\\sum_{j=1}^{s}\\lambda^{(j)}{\\theta^{(j)}}^{n}=\\operatorname{Tr}_{\\mathbb{Q}(\\theta)/\\mathbb{Q}}(\\lambda\\theta^n)$ is a rational integer: $\\lambda\\theta^n$ is an algebraic integer (a product of the algebraic integers $\\lambda$ and $\\theta^n$), so its trace is an algebraic integer lying in $\\mathbb{Q}$, hence in $\\mathbb{Z}$."
  refs "Ber92"

/-- **Lemma 1 of §5.4** (Bertin). For an algebraic integer `θ` and an algebraic integer
`μ ∈ ℚ(θ)` (here `μ : ℚ⟮θ⟯` with `IsIntegral ℤ μ`, so `λ = (μ : ℝ)`), the trace
`Tr_{ℚ(θ)/ℚ}(μ·θⁿ) = λθⁿ + ∑_{j=2}^{s} λ⁽ʲ⁾θ⁽ʲ⁾ⁿ` is a **rational integer**.

**Proved.** `μ · (AdjoinSimple.gen ℚ θ)ⁿ` is integral over `ℤ` (`μ` integral, `θ` integral), so its
trace is integral over `ℤ` (`Algebra.isIntegral_trace`) and lies in `ℚ`, hence in `ℤ`
(`IsIntegrallyClosed.isIntegral_iff`). The direct generalization of `conj_powerSum_isInt`
(the `λ = 1`, power-sum-of-conjugates case). -/
@[category research solved, AMS 11, ref "Ber92", informal_uses "smul-conjugate-trace-integer"]
theorem trace_smul_pow_isInt (θ : ℝ) (hθ : IsIntegral ℤ θ) (μ : ℚ⟮θ⟯) (hμ : IsIntegral ℤ μ)
    (n : ℕ) : ∃ m : ℤ, Algebra.trace ℚ ℚ⟮θ⟯ (μ * AdjoinSimple.gen ℚ θ ^ n) = (m : ℚ) := by
  have hintℚ : IsIntegral ℚ θ := hθ.tower_top
  haveI hfd : FiniteDimensional ℚ ℚ⟮θ⟯ := adjoin.finiteDimensional hintℚ
  have hgenInt : IsIntegral ℤ (AdjoinSimple.gen ℚ θ) := by
    have hf : Function.Injective ((IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ) :=
      (IntermediateField.val ℚ⟮θ⟯).injective
    rw [← isIntegral_algHom_iff _ hf]; show IsIntegral ℤ θ; exact hθ
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (algebraMap ℤ ℚ) m = Algebra.trace ℚ ℚ⟮θ⟯ (μ * AdjoinSimple.gen ℚ θ ^ n) :=
    IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hμ.mul (hgenInt.pow n)))
  exact ⟨m, by rw [← hm, eq_intCast (algebraMap ℤ ℚ) m]⟩

/- The structural Pisot estimate of §5.4 — the `λθⁿ` analogue of `pisot-power-geometric-approximation`.
**Proved** below from the trace fact (`trace_smul_pow_isInt`) and the embedding split. -/
informal_result "pisot-smul-power-geometric"
  latex "Let $\\theta$ be a Pisot ($S$-) number with conjugates $\\theta=\\theta^{(1)},\\dots,\\theta^{(s)}$ ($|\\theta^{(j)}|<1$ for $j\\ge 2$), and $\\lambda\\in\\mathbb{Q}(\\theta)$ an algebraic integer with conjugates $\\lambda^{(j)}$. By the trace fact $\\lambda\\theta^n+\\sum_{j=2}^{s}\\lambda^{(j)}{\\theta^{(j)}}^{n}$ is a rational integer $k_n$, and $\\big|\\sum_{j=2}^{s}\\lambda^{(j)}{\\theta^{(j)}}^{n}\\big|\\le\\big(\\sum_{j}|\\lambda^{(j)}|\\big)\\,\\delta^{n}$ with $\\delta=\\max_{j\\ge 2}|\\theta^{(j)}|<1$. Hence $|\\lambda\\theta^n-k_n|\\le C\\delta^{n}$ with $C=\\sum_{j}|\\lambda^{(j)}|$, i.e. $\\|\\lambda\\theta^n\\|\\le C\\delta^{n}\\to 0$ geometrically (proved as in Theorem 5.3.1)."
  refs "Ber92"

/-- **Lemma 2 of §5.4** (Bertin). For a Pisot number `θ ∈ S` and an algebraic integer `μ ∈ ℚ(θ)`
(`λ = (μ : ℝ)`), the sequence `(λθⁿ)` converges to `0` modulo `1` **geometrically**: there are
constants `C ≥ 0` and `δ ∈ [0, 1)` with, for every `n`, an integer `k` such that
`|λθⁿ − k| ≤ C·δⁿ` (Bertin's `‖λθⁿ‖ ≤ C δⁿ`).

**Proved.** The embeddings `σ : ℚ(θ) →ₐ[ℚ] ℂ` split into the real embedding `σ₀` (`σ₀ θ = θ`,
`σ₀ λ = λ`) and the rest; for `σ ≠ σ₀`, `σ θ` is a conjugate of `θ` other than `θ`, so `|σ θ| < 1`
(Pisot). The trace `λθⁿ + ∑_{σ≠σ₀} σ(λ)(σθ)ⁿ` is a rational integer `k` (`trace_smul_pow_isInt`), so
`λθⁿ − k = −∑_{σ≠σ₀} σ(λ)(σθ)ⁿ`, whose modulus is `≤ ∑_σ |σλ| · δⁿ` with
`δ = max_{σ≠σ₀} |σθ| < 1`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "pisot-smul-power-geometric"]
theorem pisot_smul_pow_approx_int (θ : ℝ) (hθ : θ ∈ S) (μ : ℚ⟮θ⟯) (hμ : IsIntegral ℤ μ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 ≤ δ ∧ δ < 1 ∧
      ∀ n : ℕ, ∃ k : ℤ, |(μ : ℝ) * θ ^ n - (k : ℝ)| ≤ C * δ ^ n := by
  classical
  obtain ⟨hθ1, hθint, hθconj⟩ := hθ
  have hintℚ : IsIntegral ℚ θ := hθint.tower_top
  haveI hfd : FiniteDimensional ℚ ℚ⟮θ⟯ := adjoin.finiteDimensional hintℚ
  set g : ℚ⟮θ⟯ := AdjoinSimple.gen ℚ θ with hg
  have hgenInt : IsIntegral ℤ g := by
    have hf : Function.Injective ((IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ) :=
      (IntermediateField.val ℚ⟮θ⟯).injective
    rw [← isIntegral_algHom_iff _ hf]; show IsIntegral ℤ θ; exact hθint
  let pb : PowerBasis ℚ ℚ⟮θ⟯ := adjoin.powerBasis hintℚ
  have hgenθ : pb.gen = g := adjoin.powerBasis_gen hintℚ
  let σ₀ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ := (Complex.ofRealAm.restrictScalars ℚ).comp (IntermediateField.val ℚ⟮θ⟯)
  have hg_real : σ₀ g = (θ : ℂ) := by
    show ((IntermediateField.val ℚ⟮θ⟯ g : ℝ) : ℂ) = (θ : ℂ); norm_cast
  have hμ_real : σ₀ μ = ((μ : ℝ) : ℂ) := rfl
  have hinj : Function.Injective (fun σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ => σ g) := fun σ τ h => by
    apply pb.algHom_ext; rw [hgenθ]; exact h
  have hmp : minpoly ℚ g = minpoly ℚ θ := by rw [hg]; exact minpoly_gen ℚ θ
  have hpne : minpoly ℚ θ ≠ 0 := minpoly.ne_zero hintℚ
  have hroot : ∀ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ g ∈ (minpoly ℚ θ).aroots ℂ := fun σ => by
    rw [Polynomial.mem_aroots]
    exact ⟨hpne, by rw [aeval_algHom_apply, ← hmp, minpoly.aeval, map_zero]⟩
  have hlt : ∀ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ ≠ σ₀ → ‖σ g‖ < 1 := fun σ hσ =>
    hθconj (σ g) (hroot σ) (fun h => hσ (hinj (show σ g = σ₀ g by rw [h, hg_real])))
  obtain ⟨δ, hδ0, hδ1, hδb⟩ :
      ∃ δ, 0 ≤ δ ∧ δ < 1 ∧ ∀ σ ∈ Finset.univ.erase σ₀, ‖σ g‖ ≤ δ := by
    rcases (Finset.univ.erase σ₀).eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_refl _, by norm_num, by simp [he]⟩
    · refine ⟨(Finset.univ.erase σ₀).sup' hne (fun σ => ‖σ g‖), ?_, ?_,
        fun σ hσ => Finset.le_sup' (fun σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ => ‖σ g‖) hσ⟩
      · obtain ⟨σ, hσ⟩ := hne
        exact le_trans (norm_nonneg _) (Finset.le_sup' (fun σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ => ‖σ g‖) hσ)
      · rw [Finset.sup'_lt_iff]; exact fun σ hσ => hlt σ (Finset.mem_erase.mp hσ).1
  refine ⟨∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, ‖σ μ‖, δ, Finset.sum_nonneg (fun _ _ => norm_nonneg _),
    hδ0, hδ1, fun n => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (algebraMap ℤ ℚ) m = Algebra.trace ℚ ℚ⟮θ⟯ (μ * g ^ n) :=
    IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hμ.mul (hgenInt.pow n)))
  refine ⟨m, ?_⟩
  have htr := trace_eq_sum_embeddings (K := ℚ) (L := ℚ⟮θ⟯) ℂ (x := μ * g ^ n)
  have hsum : (∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ μ * (σ g) ^ n) = (m : ℂ) := by
    have h0 : (∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ (μ * g ^ n)) = (m : ℂ) := by
      rw [← htr, ← hm, ← IsScalarTower.algebraMap_apply]; simp
    rw [← h0]; exact Finset.sum_congr rfl (fun σ _ => by rw [map_mul, map_pow])
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ => σ μ * (σ g) ^ n) (Finset.mem_univ σ₀)
  rw [hsum] at hsplit
  have hσ₀val : σ₀ μ * (σ₀ g) ^ n = (((μ : ℝ) * θ ^ n : ℝ) : ℂ) := by
    rw [hμ_real, hg_real]; push_cast; ring
  rw [hσ₀val] at hsplit
  push_cast at hsplit
  have hnorm : |(μ : ℝ) * θ ^ n - (m : ℝ)|
      = ‖∑ σ ∈ Finset.univ.erase σ₀, σ μ * (σ g) ^ n‖ := by
    rw [show |(μ : ℝ) * θ ^ n - (m : ℝ)|
      = ‖(((μ : ℝ) * θ ^ n - (m : ℝ) : ℝ) : ℂ)‖ from (Complex.norm_real _).symm,
      show (((μ : ℝ) * θ ^ n - (m : ℝ) : ℝ) : ℂ)
        = -∑ σ ∈ Finset.univ.erase σ₀, σ μ * (σ g) ^ n by push_cast; linear_combination hsplit,
      norm_neg]
  rw [hnorm]
  calc ‖∑ σ ∈ Finset.univ.erase σ₀, σ μ * (σ g) ^ n‖
      ≤ ∑ σ ∈ Finset.univ.erase σ₀, ‖σ μ * (σ g) ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ σ ∈ Finset.univ.erase σ₀, ‖σ μ‖ * δ ^ n := by
        refine Finset.sum_le_sum (fun σ hσ => ?_)
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hδb σ hσ) n) (norm_nonneg _)
    _ ≤ ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, ‖σ μ‖ * δ ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun σ _ _ => by positivity)
    _ = (∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, ‖σ μ‖) * δ ^ n := by rw [Finset.sum_mul]

/-- **§5.4, the limit form of Lemma 2** (Bertin). For a Pisot number `θ ∈ S` and an algebraic integer
`μ ∈ ℚ(θ)`, the powers `λθⁿ` (`λ = (μ : ℝ)`) converge to `0` modulo `1`:
`distToNearestInt (λθⁿ) → 0` as `n → ∞`. A squeeze on the geometric bound
`pisot_smul_pow_approx_int`, exactly as for Theorem 5.3.1. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "pisot-smul-power-geometric"]
theorem pisot_smul_pow_tendsto_zero (θ : ℝ) (hθ : θ ∈ S) (μ : ℚ⟮θ⟯) (hμ : IsIntegral ℤ μ) :
    Tendsto (fun n => distToNearestInt ((μ : ℝ) * θ ^ n)) atTop (𝓝 0) := by
  obtain ⟨C, δ, hC, hδ0, hδ1, happ⟩ := pisot_smul_pow_approx_int θ hθ μ hμ
  refine squeeze_zero (fun n => abs_nonneg _) (g := fun n => C * δ ^ n) (fun n => ?_) ?_
  · obtain ⟨k, hk⟩ := happ n
    exact (distToNearestInt_le_int ((μ : ℝ) * θ ^ n) k).trans hk
  · simpa using (tendsto_const_nhds (x := C)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1)

/- Bertin's proof of the hard (sufficiency) direction of Theorem 5.4.1, recorded. The genuine inputs
are: the integer linear recurrence forcing the generating series `∑ uₙ zⁿ` to be rational (as in
Theorem 5.1.1), the partial-fraction split `A/Q = λ/(1−θz) + ε`, Lemma 5.4 applied to `ε`, and the
identification of `Q` as the reciprocal of the minimal polynomial of `θ` from its single zero in the
closed disk. -/
informal_result "algebraic-smul-pow-tendsto-zero-imp-pisot"
  latex "Let $\\theta>1$ be algebraic, a root of $P=\\sum_{i=0}^{s} q_i X^i\\in\\mathbb{Z}[X]$, and suppose $\\lambda\\ne 0$ is real with $\\|\\lambda\\theta^n\\|\\to 0$. Write $\\lambda\\theta^n=u_n+\\varepsilon_n$ with $u_n=E(\\lambda\\theta^n)\\in\\mathbb{Z}$ and $\\varepsilon_n=\\varepsilon(\\lambda\\theta^n)$, so $|\\varepsilon_n|=\\|\\lambda\\theta^n\\|\\to 0$. From $P(\\theta)=0$ we get $\\lambda\\theta^n P(\\theta)=\\sum_i q_i\\lambda\\theta^{n+i}=0$, hence $\\sum_i q_i u_{n+i}=-\\sum_i q_i\\varepsilon_{n+i}$. As $\\varepsilon_n\\to 0$, $\\big|\\sum_i q_i\\varepsilon_{n+i}\\big|<1$ for $n$ large, and the left side is an integer, so $\\sum_i q_i u_{n+i}=0$ eventually: $(u_n)$ satisfies a linear recurrence with integer coefficients. Hence (as in Theorem 5.1.1) the generating series $f(z)=\\sum_n u_n z^n=A(z)/Q(z)$ is rational, with $A,Q\\in\\mathbb{Z}[X]$ coprime and $Q(0)=1$. Moreover $f(z)=\\dfrac{\\lambda}{1-\\theta z}+\\varepsilon(z)$ on $D(0,1/\\theta)$, where $\\varepsilon(z)=\\sum_n\\varepsilon_n z^n$ is rational, analytic at $0$, with Taylor coefficients $\\varepsilon_n\\to 0$. By Lemma 5.4, $\\varepsilon$ has no pole on $\\overline{D}(0,1)$. Therefore the only pole of $f$ in $\\overline{D}(0,1)$ is the simple pole $z=1/\\theta$ of $\\lambda/(1-\\theta z)$, i.e. $Q$ has a single zero in $\\overline{D}(0,1)$, namely $1/\\theta$. So $Q$ is (up to sign) the reciprocal polynomial of the minimal polynomial of $\\theta$, irreducible, and all conjugates $\\theta^{(j)}$ ($j\\ge 2$) satisfy $|\\theta^{(j)}|<1$: $\\theta\\in S$."
  refs "Ber92"

/-- **Stage 1 of Theorem 5.4.1's sufficiency — the integer recurrence (proved).** If `θ` is a root of
`P ∈ ℤ[X]` and `‖λθⁿ‖ → 0`, then the nearest-integer sequence `uₙ = round(λθⁿ)` *eventually* satisfies
the integer linear recurrence `∑ᵢ P.coeffᵢ · u_{n+i} = 0`.

From `P(θ) = 0` we get `λθⁿ·P(θ) = ∑ᵢ qᵢ·λθ^{n+i} = 0`; writing `λθ^m = u_m + ε_m`
(`ε_m = λθ^m − round(λθ^m)`, `|ε_m| = ‖λθ^m‖`) this reads `∑ᵢ qᵢ u_{n+i} = −∑ᵢ qᵢ ε_{n+i}`. The right
side has modulus `≤ (∑ᵢ|qᵢ|)·max_i|ε_{n+i}| < 1` once `n` is large (as `ε_m → 0`), and the left side is
an integer, so it vanishes. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem round_smul_pow_recurrence (θ lam : ℝ) (P : Polynomial ℤ) (hPθ : aeval θ P = 0)
    (hlim : Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * round (lam * θ ^ (n + i)) = 0 := by
  simp only [distToNearestInt] at hlim
  set s := P.natDegree with hs
  set ε : ℕ → ℝ := fun m => lam * θ ^ m - (round (lam * θ ^ m) : ℝ) with hε
  have haev : ∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * θ ^ i = 0 := by
    rw [← hPθ, aeval_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by rw [zsmul_eq_mul])
  set C : ℝ := ∑ i ∈ Finset.range (s + 1), |(P.coeff i : ℝ)| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (1 / (C + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hkey : ((∑ i ∈ Finset.range (s + 1), P.coeff i * round (lam * θ ^ (n + i)) : ℤ) : ℝ)
      = -∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * ε (n + i) := by
    have hzero : ∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * (lam * θ ^ (n + i)) = 0 := by
      have hfac : ∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * (lam * θ ^ (n + i))
          = lam * θ ^ n * ∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * θ ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [pow_add]; ring)
      rw [hfac, haev, mul_zero]
    push_cast
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← hzero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hε]; ring
  have hbound : |((∑ i ∈ Finset.range (s + 1),
      P.coeff i * round (lam * θ ^ (n + i)) : ℤ) : ℝ)| < 1 := by
    rw [hkey, abs_neg]
    calc |∑ i ∈ Finset.range (s + 1), (P.coeff i : ℝ) * ε (n + i)|
        ≤ ∑ i ∈ Finset.range (s + 1), |(P.coeff i : ℝ) * ε (n + i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (s + 1), |(P.coeff i : ℝ)| * (1 / (C + 1)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hni := hN (n + i) (le_trans hn (Nat.le_add_right _ _))
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)] at hni
          exact hni.le
      _ = C * (1 / (C + 1)) := by rw [← Finset.sum_mul]
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hlt1 : |∑ i ∈ Finset.range (s + 1), P.coeff i * round (lam * θ ^ (n + i))| < 1 := by
    have hcast : ((|∑ i ∈ Finset.range (s + 1),
        P.coeff i * round (lam * θ ^ (n + i))| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hbound
    exact_mod_cast hcast
  exact Int.abs_lt_one_iff.mp hlt1

/-- **Stage 2 of Theorem 5.4.1's sufficiency — the rational generating series (proved).** For an
algebraic `θ` with `‖λθⁿ‖ → 0`, the generating series `∑ₙ round(λθⁿ) Xⁿ ∈ ℤ⟦X⟧` is a **rational
series** (a ratio of polynomials). Proved from the integer recurrence (`round_smul_pow_recurrence`) by
reversing its coefficients (`q'ⱼ = P.coeff (s − j)`, leading coefficient `P.coeff s ≠ 0`) into the
backward form and applying Bertin's **Proposition 1.1** (`exists_recurrence.isRationalSeries`, proved
axiom-free in `ForMathlib`). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses round_smul_pow_recurrence]
theorem round_smul_pow_isRationalSeries (θ lam : ℝ) (halg : IsAlgebraic ℚ θ)
    (hlim : Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0)) :
    IsRationalSeries (PowerSeries.mk (fun n => round (lam * θ ^ n)) : ℤ⟦X⟧) := by
  obtain ⟨P, hP0, hPθ⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg
  obtain ⟨N, hN⟩ := round_smul_pow_recurrence θ lam P hPθ hlim
  set s := P.natDegree with hs
  refine exists_recurrence.isRationalSeries ⟨s, N + s, fun j => P.coeff (s - j), ?_, by omega,
    fun m hm => ?_⟩
  · simpa only [Nat.sub_zero, hs, Polynomial.leadingCoeff] using
      Polynomial.leadingCoeff_ne_zero.mpr hP0
  · simp only [PowerSeries.coeff_mk]
    have e1 : ∑ i ∈ Finset.range (s + 1), P.coeff (s - i) * round (lam * θ ^ (m - i))
        = ∑ i ∈ Finset.range (s + 1),
            P.coeff (s - i) * round (lam * θ ^ ((m - s) + (s - i))) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [show m - i = (m - s) + (s - i) from by omega]
    have e2 : ∑ i ∈ Finset.range (s + 1),
          P.coeff (s - i) * round (lam * θ ^ ((m - s) + (s - i)))
        = ∑ i ∈ Finset.range (s + 1), P.coeff i * round (lam * θ ^ ((m - s) + i)) := by
      rw [← Finset.sum_range_reflect
        (fun i => P.coeff i * round (lam * θ ^ ((m - s) + i))) (s + 1)]
      simp only [Nat.add_sub_cancel]
    rw [e1, e2]
    exact hN (m - s) (by omega)

/-- **Stages 3–4 of Theorem 5.4.1's sufficiency (cited).** Given that `θ > 1` is algebraic, that
`λ ≠ 0` with `‖λθⁿ‖ → 0`, and that the generating series `F = ∑ round(λθⁿ) Xⁿ ∈ ℤ⟦X⟧` is **rational**
(the proved conclusion of `round_smul_pow_isRationalSeries`), then `θ ∈ S`.

This is the deep analytic–algebraic core. Writing `F = A/Q` (`Q` the reversal of the characteristic
polynomial), the split `A/Q = λ/(1−θz) + ε` with `εₙ → 0` lets **Lemma 5.4** (`lemma_5_4`) place all
poles of `ε` outside `D̄(0,1)`, so `Q` has a single zero `1/θ` in the closed disk and (being the
irreducible reciprocal of the minimal polynomial of `θ`) forces every conjugate `< 1`, i.e. `θ ∈ S`.
The partial-fraction/pole analysis and the irreducibility↔conjugate correspondence are not assembled
here, so this is a `cited` axiom. (Stages 1–2 — the integer recurrence and the rationality of `F` —
are now **proved**: `round_smul_pow_recurrence`, `round_smul_pow_isRationalSeries`.) -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S lemma_5_4,
  informal_uses "algebraic-smul-pow-tendsto-zero-imp-pisot"]
axiom pisot_of_rational_round_series (θ : ℝ) (halg : IsAlgebraic ℚ θ) (hθ : 1 < θ)
    (lam : ℝ) (hlam : lam ≠ 0)
    (hlim : Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0))
    (hrat : IsRationalSeries (PowerSeries.mk (fun n => round (lam * θ ^ n)) : ℤ⟦X⟧)) :
    θ ∈ S

/-- **Theorem 5.4.1, sufficiency** (Bertin §5.4 — the deep direction). If `θ > 1` is **algebraic** and
there is a non-zero real `λ` with `‖λθⁿ‖ → 0`, then `θ ∈ S` (`θ` is a Pisot number).

The first two stages of Bertin's proof are now **proved**: the integer linear recurrence for the
nearest-integer sequence (`round_smul_pow_recurrence`) and the resulting rationality of the generating
series `∑ round(λθⁿ) Xⁿ` (`round_smul_pow_isRationalSeries`, via Bertin's Proposition 1.1). The
remaining analytic core — the partial fraction `A/Q = λ/(1−θz) + ε`, **Lemma 5.4** placing `ε`'s poles
outside `D̄(0,1)`, and the conclusion that `Q` is the irreducible reciprocal of the minimal polynomial
(all conjugates `< 1`) — is the cited `pisot_of_rational_round_series`. The **algebraicity hypothesis
is essential** — without it the implication is the open problem `pisot_of_smul_pow_tendsto_zero`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S round_smul_pow_isRationalSeries pisot_of_rational_round_series,
  informal_uses "algebraic-smul-pow-tendsto-zero-imp-pisot"]
theorem theorem_5_4_1_sufficiency (θ : ℝ) (halg : IsAlgebraic ℚ θ) (hθ : 1 < θ)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧
      Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0)) :
    θ ∈ S := by
  obtain ⟨lam, hlam, hlim⟩ := h
  exact pisot_of_rational_round_series θ halg hθ lam hlam hlim
    (round_smul_pow_isRationalSeries θ lam halg hlim)

/-- **Theorem 5.4.1** (Bertin §5.4 — the main theorem). An **algebraic** real `θ > 1` belongs to `S`
(is a Pisot number) **iff** there is a non-zero real `λ` with `‖λθⁿ‖ → 0`
(`distToNearestInt (λθⁿ) → 0`).

* **(⟹)** If `θ ∈ S` then already `λ = 1` works: `‖θⁿ‖ → 0` is Theorem 5.3.1 (`theorem_5_3_1`).
  **Proved.**
* **(⟸)** The converse for algebraic `θ` is `theorem_5_4_1_sufficiency` (cited), via Lemma 5.4.

Dropping algebraicity turns `(⟸)` into the open problem `pisot_of_smul_pow_tendsto_zero`: it is unknown
whether a *transcendental* `θ > 1` with `‖λθⁿ‖ → 0` (some `λ ≠ 0`) can exist. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S theorem_5_3_1 theorem_5_4_1_sufficiency,
  informal_uses "algebraic-smul-pow-tendsto-zero-imp-pisot"]
theorem theorem_5_4_1 (θ : ℝ) (halg : IsAlgebraic ℚ θ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam : ℝ, lam ≠ 0 ∧
      Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0) := by
  constructor
  · intro hθS
    exact ⟨1, one_ne_zero, by simpa using theorem_5_3_1 θ hθS⟩
  · exact theorem_5_4_1_sufficiency θ halg hθ

/-- **Open problem** (Bertin §5.4). Let `θ > 1` be real, and suppose there is a **non-zero** real `λ`
with `‖λθⁿ‖ → 0` (i.e. `distToNearestInt (λθⁿ) → 0`). **Does `θ` belong to `S` — must `θ` be a Pisot
number?**

This is the exact converse of `pisot_smul_pow_tendsto_zero` (there `θ ∈ S` together with an algebraic
integer `λ ∈ ℚ(θ)` yields `‖λθⁿ‖ → 0`; here one is *given* `‖λθⁿ‖ → 0` for some real `λ ≠ 0` — not
assumed to lie in `ℚ(θ)` — and asks whether `θ` is forced to be Pisot). It is a **long-standing open
problem**. For **algebraic** `θ` the answer is *yes* — that is Theorem 5.4.1 (`theorem_5_4_1`); what
is open is precisely whether **algebraicity can be dropped** (no transcendental `θ > 1` with this
property is known to exist). Pisot's theorem also settles the *stronger* hypothesis affirmatively
without algebraicity: if `∑ₙ ‖λθⁿ‖² < ∞` for some real `λ ≠ 0`, then `θ` is a Pisot number and
`λ ∈ ℚ(θ)`. Whether the *mere convergence* `‖λθⁿ‖ → 0` suffices for general (transcendental) `θ` is
unknown; the expected answer is "yes".

Recorded as a `research open` node: the statement below is the conjectured affirmative answer. It is
**not** proved (`sorry`) and **must not** be invoked as a lemma — it stands only as the formal
statement of the question. -/
@[category research open, AMS 11, ref "Ber92", formal_uses S]
theorem pisot_of_smul_pow_tendsto_zero (θ : ℝ) (hθ : 1 < θ)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧
      Tendsto (fun n : ℕ => distToNearestInt (lam * θ ^ n)) atTop (𝓝 0)) :
    θ ∈ S := by
  sorry

end Bertin
