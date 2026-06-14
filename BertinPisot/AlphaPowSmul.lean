/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowMod1
import BertinPisot.DistributionModOneBasics
import BertinPisot.MeromorphicCoeffVanishing
import ForMathlib.RingTheory.PowerSeries.Rationality
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.Asymptotics.Lemmas
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# §5.4 — distribution of `λθⁿ` for a Pisot number `θ`; §5.6 — countability of small-residue pairs (Bertin)

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

The file then develops the §5.4 characterizations — Theorem 5.4.1 (`theorem_5_4_1`, algebraic `θ` and
`‖λθⁿ‖ → 0`), 5.4.2 (`theorem_5_4_2`, the `L²` condition), 5.4.3 (`theorem_5_4_3`, `o(n^{-1/2})`), 5.4.4
(`theorem_5_4_4`, the explicit `O(n^{-1/2})` threshold) — and closes with §5.6.

## §5.6 — small-residue pairs (Theorem 5.6.1) and the finite-limit-point criterion (Theorem 5.6.2)

Bertin's **Theorem 5.6.1** (§5.6): the set of pairs `(λ, α)`, `λ > 0`, `α > 1`, with
`sup_{n ≥ n₀} ‖λαⁿ‖ < 1/(2(1+α)²)` for some integer `n₀`, is **countable**. With `uₙ = E(λαⁿ)` the
small residues force the integer recurrence `u_{n+2} = E(u²_{n+1}/uₙ)` for large `n` (via the proved
algebraic identity `smul_pow_recurrence_identity`), so each pair is determined by finitely many
integers; and `α = lim u_{n+1}/uₙ` (`tendsto_round_smul_pow_ratio`, proved) recovers `(λ, α)` from the
integer sequence `(uₙ)`. Both computational steps are **proved**; the injection-into-a-countable-set
argument is recorded in the `informal_result` `"good-pairs-countable"`, and `theorem_5_6_1` itself is a
`cited` axiom.

**Theorem 5.6.2** (`theorem_5_6_2`, cited): an *algebraic* `θ > 1` is Pisot **iff** some `λ ≠ 0` makes
`(λθⁿ)` have finitely many limit points modulo `1` — the companion of Theorem 5.4.1, with `‖λθⁿ‖ → 0`
replaced by finite `limitPointsModOne`. Its proof runs Pisot's Theorem 4.1 (`pisot_theorem_4_1`) to an
integer recurrence; the lead-up lemmas `exists_int_mul_isIntegral_of_isAlgebraic`,
`int_mul_eps_sub_eps_isInt` (both proved) and `finite_rational_clusterPt_distToNearestInt` (cited) sit
just before it.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.4, §5.6.
  - [Gel41] Gelfond (Guelfond), A. O. *Mat. Sb. (N.S.)* **9(51)** (1941), 721–725.
  - [Kor84] Korneyei, I. "On a theorem of Pisot." *Publ. Math. Debrecen* (1984), no. 3–4, 169–179.
-/

open Filter Topology Polynomial IntermediateField Asymptotics
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

/- The deep (sufficiency) direction of Theorem 5.4.3 (Bertin §5.4), recorded. The `o(n^{-1/2})` decay
of `‖λθⁿ‖` forces the integer sequence `uₙ = E(λθⁿ)` to have a *rational* generating series — and,
crucially, **without any algebraicity assumption on `θ`**: that rationality is supplied directly by
the corollary of Theorem 1.2.2 (a Hankel/L²-block rationality criterion), since the block sums
`∑_{m=n}^{2n-1}|εₘ|² = o(1)`. The remaining pole/conjugate analysis is then exactly as in
Theorem 5.4.1. -/
informal_result "smul-pow-littleO-imp-pisot"
  latex "Let $\\theta>1$ be real and $\\lambda\\ne 0$ real with $\\|\\lambda\\theta^n\\|=o(n^{-1/2})$. Write $\\lambda\\theta^n=u_n+\\varepsilon_n$ with $u_n=E(\\lambda\\theta^n)\\in\\mathbb{Z}$ the nearest integer and $\\varepsilon_n=\\varepsilon(\\lambda\\theta^n)$, so $|\\varepsilon_n|=\\|\\lambda\\theta^n\\|=o(n^{-1/2})$. This follows directly from the corollary of Theorem 1.2.2: the series $\\sum_{n\\in\\mathbb{N}}t_n X^n$ is a polynomial and the sequence $(s_n)$ satisfies $\\sum_{m=n}^{2n-1}|s_m|^2=o(1)$ (here $s_n=\\varepsilon_n$: from $|\\varepsilon_m|=o(m^{-1/2})$ one gets $|\\varepsilon_m|^2=o(1/m)$, and the $n$ terms $n\\le m<2n$ sum to $o(1)$); thus the series $\\sum_{n\\in\\mathbb{N}}u_n X^n$ is rational. As in Theorem 5.4.1 the only zero of its denominator in $\\overline{D}(0,1)$ is $1/\\theta$, the denominator is the reciprocal of the minimal polynomial of $\\theta$, and every other conjugate has modulus $<1$, i.e. $\\theta\\in S$. No algebraicity of $\\theta$ is assumed --- the $o(n^{-1/2})$ decay supplies the rationality directly. Conversely, if $\\theta\\in S$ then $\\|\\theta^n\\|\\le C\\delta^n$ with $\\delta<1$ decays geometrically, hence $\\|1\\cdot\\theta^n\\|=o(n^{-1/2})$ and $\\lambda=1$ works."
  refs "Ber92"

/-- A geometric sequence is `o(n^{-1/2})`: for `0 ≤ δ < 1` and any `C`, `n ↦ C·δⁿ = o(n^{-1/2})`.
(The decay `δⁿ` beats every negative power of `n`; concretely `δⁿ·√n → 0`.) -/
private lemma geom_isLittleO {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (C : ℝ) :
    (fun n : ℕ => C * δ ^ n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1/2) : ℝ)) := by
  apply IsLittleO.const_mul_left
  have hnorm : ‖δ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hδ0]; exact hδ1
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * δ ^ n) atTop (𝓝 0) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).tendsto_atTop_zero
  have key : Tendsto (fun n : ℕ => δ ^ n * (n : ℝ) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hmul
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [Real.zero_rpow]
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have hle : (n : ℝ) ^ (1/2 : ℝ) ≤ (n : ℝ) := by
        calc (n : ℝ) ^ (1/2 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
          _ = (n : ℝ) := Real.rpow_one _
      calc δ ^ n * (n : ℝ) ^ (1/2 : ℝ) ≤ δ ^ n * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (n : ℝ) * δ ^ n := by ring
  have hside : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1/2) : ℝ) = 0 → δ ^ n = 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn h0
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact absurd h0 (Real.rpow_pos_of_pos hnpos _).ne'
  rw [isLittleO_iff_tendsto' hside]
  exact key.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n), div_inv_eq_mul])

/-- **Theorem 5.4.3, necessity** (Bertin §5.4). If `θ ∈ S` (Pisot) then `λ = 1` already witnesses the
sharp decay: `‖θⁿ‖ = o(n^{-1/2})`.

**Proved.** `‖θⁿ‖ = distToNearestInt (θⁿ) ≤ C·δⁿ` decays geometrically (`pisot_smul_pow_approx_int`
with the integral element `μ = 1`, so `λ = 1`), and any geometric sequence is `o(n^{-1/2})`
(`geom_isLittleO`). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S]
theorem pisot_imp_smul_pow_isLittleO (θ : ℝ) (hθ : θ ∈ S) :
    (fun n : ℕ => distToNearestInt (θ ^ n)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1/2) : ℝ)) := by
  obtain ⟨C, δ, hC, hδ0, hδ1, happ⟩ := pisot_smul_pow_approx_int θ hθ 1 isIntegral_one
  have hnn : ∀ x : ℝ, 0 ≤ distToNearestInt x := fun x => by rw [distToNearestInt]; exact abs_nonneg _
  have hbound : ∀ n : ℕ, distToNearestInt (θ ^ n) ≤ C * δ ^ n := by
    intro n
    obtain ⟨k, hk⟩ := happ n
    refine (distToNearestInt_le_int (θ ^ n) k).trans ?_
    simpa using hk
  have hbig : (fun n : ℕ => distToNearestInt (θ ^ n)) =O[atTop] (fun n : ℕ => C * δ ^ n) := by
    refine isBigO_of_le atTop (fun n => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn _),
      abs_of_nonneg (mul_nonneg hC (pow_nonneg hδ0 n))]
    exact hbound n
  exact hbig.trans_isLittleO (geom_isLittleO hδ0 hδ1 C)

/-- **Theorem 5.4.3, sufficiency (cited).** If `θ > 1` is real — *no algebraicity assumed* — and there
is a non-zero real `λ` with `‖λθⁿ‖ = o(n^{-1/2})`, then `θ ∈ S` (`θ` is a Pisot number).

This is the deep direction (Bertin §5.4). The `o(n^{-1/2})` decay forces, via the **corollary of
Theorem 1.2.2** (a Hankel/L²-block rationality criterion), the generating series `∑ₙ E(λθⁿ) Xⁿ` to be
*rational* — *without* assuming `θ` algebraic, since the block sums `∑_{m=n}^{2n-1}|εₘ|² = o(1)`. From
the rationality the analysis concludes exactly as in Theorem 5.4.1
(`pisot_of_rational_round_series`): the denominator's single zero in `D̄(0,1)` is `1/θ`, it is the
reciprocal of the minimal polynomial of `θ`, and every other conjugate has modulus `< 1`, i.e.
`θ ∈ S`. The rationality criterion (the corollary of Theorem 1.2.2) is not assembled in the corpus,
so this is a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "smul-pow-littleO-imp-pisot"]
axiom theorem_5_4_3_sufficiency (θ : ℝ) (hθ : 1 < θ)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧
      (fun n : ℕ => distToNearestInt (lam * θ ^ n)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(1/2) : ℝ))) :
    θ ∈ S

/-- **Theorem 5.4.3** (Bertin §5.4). A real `θ > 1` belongs to `S` (is a Pisot number) **iff** there is
a non-zero real `λ` with `‖λθⁿ‖ = o(n^{-1/2})` (`distToNearestInt (λθⁿ) = o(n^{-1/2})`).

* **(⟹)** If `θ ∈ S` then `λ = 1` works: `‖θⁿ‖ ≤ C·δⁿ` decays geometrically, and a geometric sequence
  is `o(n^{-1/2})` (`pisot_imp_smul_pow_isLittleO`). **Proved.**
* **(⟸)** The converse is `theorem_5_4_3_sufficiency` (cited, via the corollary of Theorem 1.2.2).

Unlike Theorem 5.4.1 (`theorem_5_4_1`), **no algebraicity hypothesis is needed**: the sharper
`o(n^{-1/2})` decay yields the rationality of `∑ E(λθⁿ) Xⁿ` directly. So Theorem 5.4.3 settles, under
this stronger hypothesis, the question left open in `pisot_of_smul_pow_tendsto_zero` (where only the
plain limit `‖λθⁿ‖ → 0` is assumed). -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S pisot_imp_smul_pow_isLittleO theorem_5_4_3_sufficiency,
  informal_uses "smul-pow-littleO-imp-pisot"]
theorem theorem_5_4_3 (θ : ℝ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam : ℝ, lam ≠ 0 ∧
      (fun n : ℕ => distToNearestInt (lam * θ ^ n)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(1/2) : ℝ)) := by
  refine ⟨fun hθS => ⟨1, one_ne_zero, ?_⟩, theorem_5_4_3_sufficiency θ hθ⟩
  simpa only [one_mul] using pisot_imp_smul_pow_isLittleO θ hθS

/- Theorem 5.4.2 (Bertin §5.4 — Pisot's classical L² characterization) is developed here **after**
Theorem 5.4.3, since — at the user's request — its proof is *based on* 5.4.3 rather than on Bertin's
own `H²`/Theorem-1.2.1 argument. Bertin's proof is recorded below for the record. -/
informal_result "summable-sq-imp-pisot"
  latex "Let $\\theta>1$ be real and $\\lambda\\ne 0$ real with $\\sum_{n\\in\\mathbb{N}}\\|\\lambda\\theta^n\\|^2<\\infty$. Write $\\lambda\\theta^n=u_n+\\varepsilon_n$ with $u_n=E(\\lambda\\theta^n)\\in\\mathbb{Z}$ and $\\varepsilon_n=\\varepsilon(\\lambda\\theta^n)$, so $|\\varepsilon_n|=\\|\\lambda\\theta^n\\|$ and $\\sum_n\\varepsilon_n^2<\\infty$. The series $\\sum_n\\varepsilon_n^2$ being convergent, the function $\\varepsilon(z)=\\sum_n\\varepsilon_n z^n$ belongs to the Hardy space $H^2$ and is thus of bounded characteristic in the disk $D(0,1)$. The same is true for the function $f(z)=\\sum_n u_n z^n$, whose Taylor expansion has integer coefficients. Then by Theorem 1.2.1 the function $f$ is rational. As in Theorem 5.4.1 the only zero of its denominator in $\\overline{D}(0,1)$ is $1/\\theta$, the denominator is the reciprocal of the minimal polynomial of $\\theta$, and every other conjugate has modulus $<1$, i.e. $\\theta\\in S$ --- no algebraicity of $\\theta$ being assumed. (Equivalently, square-summability gives the block bound $\\sum_{m=n}^{2n-1}\\varepsilon_m^2=o(1)$, which is exactly the hypothesis of the corollary of Theorem 1.2.2 used for Theorem 5.4.3: the two characterizations share the same rational-generating-series core.) Conversely, if $\\theta\\in S$ then $\\|\\theta^n\\|\\le C\\delta^n$ with $\\delta<1$, whence $\\sum_n\\|\\theta^n\\|^2\\le C^2\\sum_n\\delta^{2n}<\\infty$ and $\\lambda=1$ works."
  refs "Ber92"

/-- **Theorem 5.4.2, necessity** (Bertin §5.4). If `θ ∈ S` (Pisot) then `λ = 1` witnesses
square-summability: `∑ₙ ‖θⁿ‖² < ∞`.

**Proved.** `‖θⁿ‖ = distToNearestInt (θⁿ) ≤ C·δⁿ` decays geometrically (`pisot_smul_pow_approx_int`
with the integral element `μ = 1`), so `‖θⁿ‖² ≤ C²·(δ²)ⁿ` is dominated by a convergent geometric
series (`δ² < 1`). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S]
theorem pisot_imp_summable_sq (θ : ℝ) (hθ : θ ∈ S) :
    Summable (fun n : ℕ => distToNearestInt (θ ^ n) ^ 2) := by
  obtain ⟨C, δ, hC, hδ0, hδ1, happ⟩ := pisot_smul_pow_approx_int θ hθ 1 isIntegral_one
  have hnn : ∀ x : ℝ, 0 ≤ distToNearestInt x := fun x => by rw [distToNearestInt]; exact abs_nonneg _
  have hbound : ∀ n : ℕ, distToNearestInt (θ ^ n) ≤ C * δ ^ n := by
    intro n
    obtain ⟨k, hk⟩ := happ n
    refine (distToNearestInt_le_int (θ ^ n) k).trans ?_
    simpa using hk
  have hsummable_geom : Summable (fun n : ℕ => C ^ 2 * (δ ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left (C ^ 2)
  refine hsummable_geom.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
  calc distToNearestInt (θ ^ n) ^ 2 ≤ (C * δ ^ n) ^ 2 := pow_le_pow_left₀ (hnn _) (hbound n) 2
    _ = C ^ 2 * (δ ^ 2) ^ n := by rw [mul_pow, pow_right_comm]

/-- **The deep step of Theorem 5.4.2, cited — and the bridge to Theorem 5.4.3.** From the
square-summability `∑ₙ ‖λθⁿ‖² < ∞` (some `λ ≠ 0`) one obtains the `o(n^{-1/2})` characterization of
Theorem 5.4.3 (some `λ' ≠ 0`).

Its mathematical content is **Pisot's theorem**: `∑ₙ ‖λθⁿ‖² < ∞` for a non-zero real `λ` forces
`θ ∈ S`. Bertin proves it (§5.4) via **Theorem 1.2.1**: the convergence `∑ εₙ² < ∞` puts
`ε(z) = ∑ εₙ zⁿ` in the Hardy space `H²` — of bounded characteristic on `D(0,1)` — hence so is
`f(z) = ∑ E(λθⁿ) zⁿ` (integer Taylor coefficients), and Theorem 1.2.1 makes `f` rational; the pole
analysis then gives `θ ∈ S` exactly as in Theorem 5.4.1, *without* assuming `θ` algebraic. Once
`θ ∈ S` is known, the `o(n^{-1/2})` decay is the proved `pisot_imp_smul_pow_isLittleO` (`λ' = 1`).
The `H²`/bounded-characteristic argument (Theorem 1.2.1) is not assembled in the corpus, so this is a
`cited` axiom; composed with `theorem_5_4_3` it yields `theorem_5_4_2`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "summable-sq-imp-pisot"]
axiom summable_sq_imp_smul_pow_isLittleO (θ : ℝ) (hθ : 1 < θ)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧ Summable (fun n : ℕ => distToNearestInt (lam * θ ^ n) ^ 2)) :
    ∃ lam : ℝ, lam ≠ 0 ∧
      (fun n : ℕ => distToNearestInt (lam * θ ^ n)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(1/2) : ℝ))

/-- **Theorem 5.4.2, sufficiency** (Pisot's theorem). If `θ > 1` is real and `∑ₙ ‖λθⁿ‖² < ∞` for some
non-zero real `λ`, then `θ ∈ S`.

**Proved from Theorem 5.4.3.** Square-summability yields the `o(n^{-1/2})` characterization
(`summable_sq_imp_smul_pow_isLittleO`), to which `theorem_5_4_3` applies. No algebraicity is needed. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S summable_sq_imp_smul_pow_isLittleO theorem_5_4_3,
  informal_uses "summable-sq-imp-pisot"]
theorem theorem_5_4_2_sufficiency (θ : ℝ) (hθ : 1 < θ)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧ Summable (fun n : ℕ => distToNearestInt (lam * θ ^ n) ^ 2)) :
    θ ∈ S :=
  (theorem_5_4_3 θ hθ).mpr (summable_sq_imp_smul_pow_isLittleO θ hθ h)

/-- **Theorem 5.4.2** (Bertin §5.4 — Pisot's classical `L²` characterization). A real `θ > 1` belongs
to `S` (is a Pisot number) **iff** there is a non-zero real `λ` with `∑ₙ ‖λθⁿ‖² < ∞`
(`∑ₙ distToNearestInt (λθⁿ)² < ∞`).

* **(⟹)** If `θ ∈ S` then `λ = 1` works: `‖θⁿ‖ ≤ C·δⁿ` decays geometrically, so
  `∑ ‖θⁿ‖² ≤ C²·∑(δ²)ⁿ < ∞` (`pisot_imp_summable_sq`). **Proved.**
* **(⟸)** `theorem_5_4_2_sufficiency` (Pisot's theorem), **based on Theorem 5.4.3**.

Like Theorem 5.4.3 — and unlike Theorem 5.4.1 — **no algebraicity hypothesis is needed**. The two are
companions: the `L²` condition here and the `o(n^{-1/2})` condition of Theorem 5.4.3 are *incomparable*
as pointwise decay rates, yet each forces (and is forced by) `θ ∈ S`, and both feed the same
rational-generating-series core. (Placed after Theorem 5.4.3 in the file because its proof invokes
it.) -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S pisot_imp_summable_sq theorem_5_4_2_sufficiency,
  informal_uses "summable-sq-imp-pisot"]
theorem theorem_5_4_2 (θ : ℝ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam : ℝ, lam ≠ 0 ∧ Summable (fun n : ℕ => distToNearestInt (lam * θ ^ n) ^ 2) := by
  refine ⟨fun hθS => ⟨1, one_ne_zero, ?_⟩, theorem_5_4_2_sufficiency θ hθ⟩
  simpa only [one_mul] using pisot_imp_summable_sq θ hθS

/- Theorem 5.4.4 (Bertin §5.4) — added without proof: the screenshot supplies the statement only, so
it is recorded as a `cited` axiom (the quantitative `O(n^{-1/2})` refinement of Theorems 5.4.2–5.4.3,
with an explicit threshold on the constant). -/
informal_result "smul-pow-sqrt-bound-iff-pisot"
  latex "A real $\\theta>1$ belongs to $S$ if and only if there exist two reals $\\lambda$ and $a$ with $\\lambda>0$ and $0<a<\\dfrac{1}{2\\sqrt{2}\\,(\\theta+1)^2}$ and an integer $n_0\\ge 1$ such that $\\|\\lambda\\theta^n\\|\\le\\dfrac{a}{\\sqrt{n}}$ for all $n\\ge n_0$. (Bertin §5.4: a quantitative refinement of Theorems 5.4.2--5.4.3, pinning the implied constant of the $O(n^{-1/2})$ bound below the explicit threshold $1/(2\\sqrt{2}\\,(\\theta+1)^2)$.)"
  refs "Ber92"

/-- **Theorem 5.4.4** (Bertin §5.4 — cited, stated without proof). A real `θ > 1` belongs to `S` (is a
Pisot number) **iff** there exist reals `λ > 0` and `a` with `0 < a < 1/(2√2·(θ+1)²)` and an integer
`n₀ ≥ 1` such that `‖λθⁿ‖ ≤ a/√n` for all `n ≥ n₀`.

A quantitative sharpening of the `o(n^{-1/2})` characterization (`theorem_5_4_3`): an `O(n^{-1/2})`
bound on `‖λθⁿ‖` (with `λ > 0`) already forces `θ ∈ S`, *provided* the implied constant `a` lies below
the explicit threshold `1/(2√2·(θ+1)²)`. Recorded as a `cited` axiom — the screenshot gives the
statement only; the proof (Bertin §5.4, the same `H²`/rational-generating-series circle as Theorems
5.4.2–5.4.3) is not formalized. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "smul-pow-sqrt-bound-iff-pisot"]
axiom theorem_5_4_4 (θ : ℝ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam a : ℝ, 0 < lam ∧ 0 < a ∧ a < 1 / (2 * Real.sqrt 2 * (θ + 1) ^ 2) ∧
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → distToNearestInt (lam * θ ^ n) ≤ a / Real.sqrt n

/- Gelfond's sharpening of Theorem 5.4.4 (A. O. Gelfond, 1941; rediscovered by Korneyei, 1984),
recorded from Bertin's §5.6 remark. Same `O(n^{-1/2})` criterion, with the larger admissible constant
`1/√(2e(θ+1))` in place of `1/(2√2(θ+1)²)`. Stated without proof in [Ber92] (a historical pointer), so
recorded as a `cited` axiom. -/
informal_result "gelfond-sharp-sqrt-bound"
  latex "A real $\\theta>1$ belongs to $S$ if and only if there exist reals $\\lambda>0$ and $a$ with $0<a<\\dfrac{1}{\\sqrt{2e(\\theta+1)}}$ and an integer $n_0\\ge 1$ such that $\\|\\lambda\\theta^n\\|\\le\\dfrac{a}{\\sqrt n}$ for all $n\\ge n_0$. This is Gelfond's theorem (A.~O.~Gelfond, 1941), sharpening Theorem 5.4.4: for $\\theta>1$ the admissible constant $1/\\sqrt{2e(\\theta+1)}$ exceeds the bound $1/(2\\sqrt2(\\theta+1)^2)$ of Theorem 5.4.4, so the criterion applies to a wider range of $a$. Owing to its date, the very small number of copies of the article, and the Russian language in which it was written, Pisot and Salem were unaware of this result; it was rediscovered by Korneyei in 1984."
  refs "Gel41" "Ber92" "Kor84"

/-- **Gelfond's theorem** (A. O. Gelfond, 1941; rediscovered by Korneyei, 1984 — recorded from Bertin's
§5.6 remark, cited). A **sharper** form of Theorem 5.4.4: a real `θ > 1` belongs to `S` (is a Pisot
number) **iff** there exist reals `λ > 0` and `a` with `0 < a < 1/√(2e(θ+1))` and an integer `n₀ ≥ 1`
such that `‖λθⁿ‖ ≤ a/√n` for all `n ≥ n₀`.

The constant `1/√(2e(θ+1))` improves on Theorem 5.4.4's `1/(2√2(θ+1)²)` (`theorem_5_4_4`): for `θ > 1`
the former is the larger threshold, so the `O(n^{-1/2})` Pisot criterion holds for a wider range of the
constant `a`. Bertin notes the result predates [Ber92] but — owing to its date, the scarcity of the
article, and its Russian language — was unknown to Pisot and Salem, and was rediscovered by Korneyei
(1984). Recorded as a `cited` axiom. (Reference keys `Gel41`/`Kor84` are placeholders for the exact
Gelfond 1941 and Korneyei 1984 bibliographic entries.) -/
@[category research solved, AMS 11, ref "Gel41" "Ber92" "Kor84",
  formal_uses S theorem_5_4_4, informal_uses "gelfond-sharp-sqrt-bound"]
axiom gelfond_sqrt_criterion (θ : ℝ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam a : ℝ, 0 < lam ∧ 0 < a ∧ a < 1 / Real.sqrt (2 * Real.exp 1 * (θ + 1)) ∧
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → distToNearestInt (lam * θ ^ n) ≤ a / Real.sqrt n

/-! ### §5.6 — countability of the pairs `(λ, α)` with small residues (Theorem 5.6.1) -/

/-- **The key algebraic identity of Theorem 5.6.1** (Bertin §5.6). For `uₙ = round (λαⁿ)` and the
centered residue `εₙ = ε (λαⁿ) = λαⁿ − uₙ`,
`u_{n+2}·uₙ − u²_{n+1} = −λαⁿ·(α²εₙ − 2αε_{n+1} + ε_{n+2}) + (εₙε_{n+2} − ε²_{n+1})`.

**Proved** — a `ring` identity after substituting `uₘ = λαᵐ − εₘ` (and `λα^{n+1} = α·λαⁿ`,
`λα^{n+2} = α²·λαⁿ`). Dividing by `uₙ` and bounding the right-hand side by `η = sup |εₙ|` is what
forces `|u_{n+2} − u²_{n+1}/uₙ| ≤ 1/2`, i.e. `u_{n+2} = E(u²_{n+1}/uₙ)`, the recurrence behind the
countability in Theorem 5.6.1. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem smul_pow_recurrence_identity (lam α : ℝ) (n : ℕ) :
    (round (lam * α ^ (n + 2)) : ℝ) * (round (lam * α ^ n) : ℝ)
        - (round (lam * α ^ (n + 1)) : ℝ) ^ 2
      = -(lam * α ^ n) * (α ^ 2 * ε (lam * α ^ n) - 2 * α * ε (lam * α ^ (n + 1))
          + ε (lam * α ^ (n + 2)))
        + (ε (lam * α ^ n) * ε (lam * α ^ (n + 2)) - ε (lam * α ^ (n + 1)) ^ 2) := by
  have h0 : (round (lam * α ^ n) : ℝ) = lam * α ^ n - ε (lam * α ^ n) := by rw [ε]; ring
  have h1 : (round (lam * α ^ (n + 1)) : ℝ) = α * (lam * α ^ n) - ε (lam * α ^ (n + 1)) := by
    rw [ε, pow_succ]; ring
  have h2 : (round (lam * α ^ (n + 2)) : ℝ) = α ^ 2 * (lam * α ^ n) - ε (lam * α ^ (n + 2)) := by
    rw [ε, pow_add]; ring
  rw [h0, h1, h2]; ring

/-- **`α = lim u_{n+1}/uₙ`** — the recovery step of Theorem 5.6.1 (Bertin §5.6). For `λ > 0`, `α > 1`
and `uₙ = round (λαⁿ)`, the ratios `u_{n+1}/uₙ` converge to `α`.

**Proved.** `uₙ → +∞` (since `λαⁿ → +∞` and `uₙ ≥ λαⁿ − 1/2`), and
`u_{n+1}/uₙ − α = (αεₙ − ε_{n+1})/uₙ` with `|αεₙ − ε_{n+1}| ≤ (α+1)/2`, so the difference is
`O(1/uₙ) → 0`. This recovers `α` (and then `λ`) from the integer sequence `(uₙ)` — the injectivity
underlying the countability of Theorem 5.6.1. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem tendsto_round_smul_pow_ratio (lam α : ℝ) (hlam : 0 < lam) (hα : 1 < α) :
    Tendsto (fun n : ℕ => (round (lam * α ^ (n + 1)) : ℝ) / (round (lam * α ^ n) : ℝ)) atTop (𝓝 α) := by
  have hpow : Tendsto (fun n : ℕ => lam * α ^ n) atTop atTop :=
    Tendsto.const_mul_atTop hlam (tendsto_pow_atTop_atTop_of_one_lt hα)
  have hround : Tendsto (fun n : ℕ => (round (lam * α ^ n) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right atTop (-(1 / 2 : ℝ)) hpow)
    have := (abs_le.mp (abs_sub_round (lam * α ^ n))).2; linarith
  have hg : Tendsto (fun n : ℕ => (α + 1) / 2 / (round (lam * α ^ n) : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hround
  have key : Tendsto (fun n : ℕ =>
      (round (lam * α ^ (n + 1)) : ℝ) / (round (lam * α ^ n) : ℝ) - α) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hround.eventually_gt_atTop 0] with n hn
    have hne : (round (lam * α ^ n) : ℝ) ≠ 0 := ne_of_gt hn
    have heq : (round (lam * α ^ (n + 1)) : ℝ) / (round (lam * α ^ n) : ℝ) - α
        = (α * (lam * α ^ n - round (lam * α ^ n))
            - (lam * α ^ (n + 1) - round (lam * α ^ (n + 1)))) / (round (lam * α ^ n)) := by
      simp only [pow_succ]; field_simp; ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hn]
    gcongr
    have e0 := abs_le.mp (abs_sub_round (lam * α ^ n))
    have e1 := abs_le.mp (abs_sub_round (lam * α ^ (n + 1)))
    rw [abs_le]; constructor <;> nlinarith [e0.1, e0.2, e1.1, e1.2, hα]
  simpa using key.add_const α

/- Bertin's full proof of Theorem 5.6.1 (§5.6), recorded faithfully. The two computational steps —
the algebraic identity and `α = lim u_{n+1}/uₙ` — are proved (`smul_pow_recurrence_identity`,
`tendsto_round_smul_pow_ratio`); what remains is the combinatorial injection of admissible pairs into
a countable set of finitely-generated integer sequences. -/
informal_result "good-pairs-countable"
  latex "Let $(\\lambda,\\alpha)$ satisfy $\\lambda>0$, $\\alpha>1$ and $\\sup_{n\\ge n_0}\\|\\lambda\\alpha^n\\|<\\frac{1}{2(1+\\alpha)^2}$ for some $n_0$. Put $u_n=E(\\lambda\\alpha^n)$ and $\\varepsilon_n=\\varepsilon(\\lambda\\alpha^n)=\\lambda\\alpha^n-u_n$, so $\\lambda\\alpha^n=u_n+\\varepsilon_n$; as $\\lambda\\alpha^n\\to+\\infty$, $u_n\\to+\\infty$. The identity $u_{n+2}-\\frac{u_{n+1}^2}{u_n}=-\\frac{\\lambda\\alpha^n}{u_n}\\bigl(\\alpha^2\\varepsilon_n-2\\alpha\\varepsilon_{n+1}+\\varepsilon_{n+2}\\bigr)+\\frac{\\varepsilon_n\\varepsilon_{n+2}-\\varepsilon_{n+1}^2}{u_n}$ holds, so with $\\eta=\\sup_{n\\ge n_0}|\\varepsilon_n|$, $\\bigl|u_{n+2}-\\frac{u_{n+1}^2}{u_n}\\bigr|\\le\\eta\\bigl(1+\\frac{\\eta}{u_n}\\bigr)(\\alpha+1)^2+\\frac{2\\eta^2}{u_n}\\le(\\alpha+1)^2\\eta+c\\,\\frac{\\eta^2}{u_n}$ for $n\\ge n_0$ ($c$ a real constant). Since $\\eta<\\frac{1}{2(1+\\alpha)^2}$ gives $(\\alpha+1)^2\\eta<\\frac12$, and $c\\eta^2/u_n\\to0$, the inequality $\\bigl|u_{n+2}-\\frac{u_{n+1}^2}{u_n}\\bigr|\\le\\frac12$ holds for $n\\ge n_1\\ge n_0$. Hence $u_{n+2}=E\\!\\left(\\frac{u_{n+1}^2}{u_n}\\right)$: $u_{n+2}$ is determined by $u_n,u_{n+1}$, so the whole sequence $(u_n)$ is fixed by its finitely many terms up to $u_{n_1+1}$. Two different pairs $(\\lambda,\\alpha)$ cannot give the same $(u_n)$ (from $(u_n)$ one recovers $\\alpha=\\lim u_{n+1}/u_n$, then $\\lambda$), so $(\\lambda,\\alpha)\\mapsto(u_n)$ is injective into the countable set of integer sequences generated by finite data; the set of admissible pairs is therefore countable. Finally $\\lambda\\alpha^{n+1}=u_{n+1}+\\varepsilon_{n+1}=\\alpha u_n+\\alpha\\varepsilon_n$ gives $\\bigl|\\alpha-\\frac{u_{n+1}}{u_n}\\bigr|=\\frac{|\\varepsilon_{n+1}-\\alpha\\varepsilon_n|}{u_n}\\to0$, so $\\alpha=\\lim_{n\\to\\infty}u_{n+1}/u_n$. $\\qquad\\blacksquare$"
  refs "Ber92"

/-- **Theorem 5.6.1** (Bertin §5.6 — cited). The set of pairs of reals `(λ, α)` with `λ > 0`, `α > 1`
for which `sup_{n ≥ n₀} ‖λαⁿ‖ < 1/(2(1+α)²)` holds for some integer `n₀` is **countable**. (The
condition `sup < 1/(2(1+α)²)` is encoded as `∃ K < 1/(2(1+α)²), ∀ n ≥ n₀, ‖λαⁿ‖ ≤ K`.)

Bertin's mechanism: with `uₙ = E(λαⁿ)`, the uniform smallness of the residues forces — via the proved
identity `smul_pow_recurrence_identity` — the integer recurrence `u_{n+2} = E(u²_{n+1}/uₙ)` for `n`
large, so each `(uₙ)` is determined by finitely many integers; and `α = lim u_{n+1}/uₙ`
(`tendsto_round_smul_pow_ratio`, proved) together with `λ` is recovered from `(uₙ)`, making
`(λ, α) ↦ (uₙ)` injective into a countable set. The two computational steps are **proved**; the
injection/countability combinatorics are recorded in the `informal_result` `"good-pairs-countable"`,
so the result is a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses smul_pow_recurrence_identity tendsto_round_smul_pow_ratio,
  informal_uses "good-pairs-countable"]
axiom theorem_5_6_1 :
    { p : ℝ × ℝ | 0 < p.1 ∧ 1 < p.2 ∧
        ∃ n₀ : ℕ, ∃ K : ℝ, K < 1 / (2 * (1 + p.2) ^ 2) ∧
          ∀ n : ℕ, n₀ ≤ n → distToNearestInt (p.1 * p.2 ^ n) ≤ K }.Countable

/-! ### Reduction to finitely many rational residue limit points (Bertin §5, lead-up to Theorem 4.1)

For a Pisot `θ` and `λ ∈ ℚ(θ)`, a non-zero integer `h` makes `hλ` an algebraic integer
(`exists_int_mul_isIntegral_of_isAlgebraic`); the combination `hε(λθⁿ) − ε(hλθⁿ)` is then an integer
(`int_mul_eps_sub_eps_isInt`); and if `‖hλθⁿ‖ → 0`, the sequence `(‖λθⁿ‖)` has finitely many limit
points, all rational (`finite_rational_clusterPt_distToNearestInt`). These supply the hypotheses of
Pisot's Theorem 4.1 (`Bertin.pisot_theorem_4_1`). -/

/-- **An algebraic real has a non-zero integer multiple that is an algebraic integer** (Bertin §5).
If `x : ℝ` is algebraic over `ℚ` — e.g. `x = λ ∈ ℚ(θ)` for a Pisot (or any algebraic) `θ` — then there
is a non-zero integer `h` with `h • x` integral over `ℤ`.

**Proved**: `IsFractionRing.isAlgebraic_iff` turns "algebraic over `ℚ`" into "algebraic over `ℤ`", then
`IsAlgebraic.exists_integral_multiple`. This is Bertin's "there exists an integer `h` such that `hλ` is
an algebraic integer". -/
@[category research solved, AMS 11, ref "Ber92"]
theorem exists_int_mul_isIntegral_of_isAlgebraic (x : ℝ) (hx : IsAlgebraic ℚ x) :
    ∃ h : ℤ, h ≠ 0 ∧ IsIntegral ℤ (h • x) :=
  ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hx).exists_integral_multiple

/-- **`h·ε(x) − ε(h·x)` is an integer** (Bertin §5). For any integer `h` and real `x`, the centered
residues satisfy `h·ε(x) − ε(h·x) = round(h·x) − h·round(x) ∈ ℤ`.

**Proved** (`ε y = y − round y`, then `ring`). With `x = λθⁿ` this is Bertin's observation, from
comparing the residues mod `1` of `λθⁿ` and `hλθⁿ`, that "the real `hε(λθⁿ) − ε(hλθⁿ)` is an
integer". -/
@[category research solved, AMS 11, ref "Ber92"]
theorem int_mul_eps_sub_eps_isInt (h : ℤ) (x : ℝ) :
    ∃ m : ℤ, (h : ℝ) * ε x - ε ((h : ℝ) * x) = (m : ℝ) :=
  ⟨round ((h : ℝ) * x) - h * round x, by rw [ε, ε]; push_cast; ring⟩

/- Bertin's argument that `‖hλθⁿ‖ → 0` forces finitely many rational residue limit points, recorded.
From `int_mul_eps_sub_eps_isInt` and `ε(hλθⁿ) → 0`, `h·ε(λθⁿ)` approaches `ℤ`, i.e. the residues
`(λθⁿ mod 1)` cluster only at the `h`-torsion points `{k/h}` of the circle — finitely many rationals;
hence the limit points of `‖λθⁿ‖ = |ε(λθⁿ)|` are finitely many rationals `|k/h|`. -/
informal_result "smul-pow-finite-rational-limit-points"
  latex "Let $h\\ne 0$ be an integer with $\\|h\\lambda\\theta^n\\|\\to 0$. Since $\\varepsilon(h\\lambda\\theta^n)=\\pm\\|h\\lambda\\theta^n\\|\\to 0$ and $h\\,\\varepsilon(\\lambda\\theta^n)-\\varepsilon(h\\lambda\\theta^n)\\in\\mathbb{Z}$, the quantity $h\\,\\varepsilon(\\lambda\\theta^n)$ stays within $o(1)$ of $\\mathbb{Z}$; equivalently, in $\\mathbb{R}/\\mathbb{Z}$ the residues of $h\\lambda\\theta^n$ tend to $0$. If $x$ is a limit point of $(\\|\\lambda\\theta^n\\|)$ then $x=\\|r\\|$ for some limit point $r$ of $(\\lambda\\theta^n\\bmod 1)$; as $r\\mapsto h\\,r$ is continuous, $h\\,r$ is a limit point of $(h\\lambda\\theta^n\\bmod 1)$, which converges to $0$, so $h\\,r=0$. Hence every such $r$ lies in the $h$-torsion subgroup of $\\mathbb{R}/\\mathbb{Z}$, which is finite (isomorphic to $\\mathbb{Z}/h\\mathbb{Z}$) and consists of the rational points $k/h$. Therefore $(\\|\\lambda\\theta^n\\|)$ has finitely many limit points, each of the form $|k/h|$ — finitely many rationals. $\\qquad\\blacksquare$"
  refs "Ber92"

/-- **Finitely many rational residue limit points** (Bertin §5 — cited). If `θ, λ` are real and some
non-zero integer `h` makes `‖hλθⁿ‖ → 0`, then `(‖λθⁿ‖)` (`= distToNearestInt (λθⁿ)`) has **finitely
many limit points, every one of which is rational**.

The converse companion of Pisot's Theorem 4.1 (`pisot_theorem_4_1`, which goes from finitely many
rational limit points to a multiplier `h` with `‖hλθⁿ‖` small): here the small-multiplier hypothesis
*produces* the finite rational limit-point set. Proof (in `"smul-pow-finite-rational-limit-points"`):
from `int_mul_eps_sub_eps_isInt` and `ε(hλθⁿ) → 0`, the residues `(λθⁿ mod 1)` cluster only at the
`h`-torsion points of `ℝ/ℤ` — finitely many rationals. The `h`-torsion finiteness of `AddCircle 1` is
not packaged shortly, so this is a `cited` axiom; the algebraic ingredients
(`int_mul_eps_sub_eps_isInt`, and `exists_int_mul_isIntegral_of_isAlgebraic` providing such an `h` for
`λ ∈ ℚ(θ)`) are proved. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses int_mul_eps_sub_eps_isInt exists_int_mul_isIntegral_of_isAlgebraic,
  informal_uses "smul-pow-finite-rational-limit-points"]
axiom finite_rational_clusterPt_distToNearestInt (lam θ : ℝ) (h : ℤ) (hh : h ≠ 0)
    (hlim : Tendsto (fun n : ℕ => distToNearestInt ((h : ℝ) * (lam * θ ^ n))) atTop (𝓝 0)) :
    {x : ℝ | MapClusterPt x atTop (fun n : ℕ => distToNearestInt (lam * θ ^ n))}.Finite ∧
      ∀ x, MapClusterPt x atTop (fun n : ℕ => distToNearestInt (lam * θ ^ n)) → ∃ q : ℚ, x = (q : ℝ)

/- Bertin's full proof of Theorem 5.6.2 (§5.6), recorded faithfully. The deep (⟸) direction runs the
Theorem-4.1 reduction (`pisot_theorem_4_1`): finitely many limit points mod 1 yield a multiplier `h`
with `hλθⁿ = vₙ + ηₙ`, `|ηₙ| ≤ 2/q`; then `P(θ) = 0` forces the integer recurrence `∑ qᵢ v_{n+i} = 0`,
so `∑ vₙ Xⁿ` is rational and (as in Theorem 5.4.1) `θ ∈ U`, while finiteness of the limit-point set
excludes the Salem case `T` (Salem powers are dense, Theorem 5.3.2), giving `θ ∈ S`. The easy (⟹)
direction is `λ = 1` via Theorem 5.3.1. -/
informal_result "algebraic-finite-limit-points-iff-pisot"
  latex "($\\Leftarrow$) Suppose $\\theta>1$ is algebraic, a zero of $P=\\sum_{i=0}^{s}q_iX^i\\in\\mathbb{Z}[X]$, and $\\lambda\\ne 0$ is real such that $(\\lambda\\theta^n)$ has finitely many limit points modulo $1$. Let $k$ be the number of irrational limit points of $(\\varepsilon(\\lambda\\theta^n))$, and pick an integer $q>2\\sum_{i=0}^{s}|q_i|$. By Theorem 4.1 there is an integer $h$ with $0<h\\le q^{k}$ such that $h\\lambda\\theta^n=v_n+\\eta_n$ with $v_n\\in\\mathbb{Z}$ and $|\\eta_n|\\le 2/q$ for $n\\ge n_0$. Since $P(\\theta)=0$, $\\sum_{i=0}^{s}q_i\\,h\\lambda\\theta^{n+i}=h\\lambda\\theta^n P(\\theta)=0$, so $\\sum_{i=0}^{s}q_iv_{n+i}=-\\sum_{i=0}^{s}q_i\\eta_{n+i}$ has absolute value $\\le\\big(\\sum_i|q_i|\\big)\\tfrac{2}{q}<1$; being an integer it vanishes, $\\sum_{i=0}^{s}q_iv_{n+i}=0$ for $n\\ge n_0$. Hence the generating series $\\sum_n v_nX^n$ is rational. As in Theorem 5.4.1 this forces $\\theta\\in U$; and $\\theta$ cannot belong to $T$ (a Salem number has $(\\theta^n)$ dense modulo $1$, hence infinitely many limit points, Theorem 5.3.2, contradicting finiteness), so $\\theta\\in S$. ($\\Rightarrow$) If $\\theta\\in S$ then $\\lambda=1$ works: by Theorem 5.3.1 $\\|\\theta^n\\|\\to 0$, so $(\\theta^n)$ has the single limit point $0$ modulo $1$ --- finitely many. $\\qquad\\blacksquare$"
  refs "Ber92"

/-- **Theorem 5.6.2** (Bertin §5.6 — cited). An **algebraic** real `θ > 1` belongs to `S` (is a Pisot
number) **iff** there is a non-zero real `λ` such that `(λθⁿ)` has **finitely many limit points modulo
1** (`(limitPointsModOne (fun n => λθⁿ)).Finite`).

* **(⟸)** the deep direction (Bertin §5.6): finitely many limit points feed Pisot's Theorem 4.1
  (`pisot_theorem_4_1`) to give a multiplier `h` with `hλθⁿ = vₙ + ηₙ`, `|ηₙ| ≤ 2/q`; `P(θ) = 0` then
  forces the integer recurrence `∑ qᵢ v_{n+i} = 0`, so `∑ vₙ Xⁿ` is rational and (as in Theorem 5.4.1)
  `θ ∈ U`; finiteness excludes the Salem case `T` (dense powers, Theorem 5.3.2), so `θ ∈ S`.
* **(⟹)** `λ = 1`: `‖θⁿ‖ → 0` (Theorem 5.3.1, `theorem_5_3_1`), a single limit point `0` mod 1.

The **algebraicity hypothesis is essential** (it supplies the integer polynomial `P` driving the
recurrence) — the companion of Theorem 5.4.1, with "`‖λθⁿ‖ → 0`" replaced by "finitely many limit
points mod 1". Resting on Theorem 4.1 and the rationality/`U\T` analysis (not assembled here), it is a
`cited` axiom; the proved lead-up lemmas `int_mul_eps_sub_eps_isInt` and
`finite_rational_clusterPt_distToNearestInt` are its companions, and the complete proof is in the
`informal_result` `"algebraic-finite-limit-points-iff-pisot"`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses S theorem_5_3_1 pisot_theorem_4_1 finite_rational_clusterPt_distToNearestInt,
  informal_uses "algebraic-finite-limit-points-iff-pisot"]
axiom theorem_5_6_2 (θ : ℝ) (hθalg : IsAlgebraic ℚ θ) (hθ : 1 < θ) :
    θ ∈ S ↔ ∃ lam : ℝ, lam ≠ 0 ∧ (limitPointsModOne (fun n : ℕ => lam * θ ^ n)).Finite

/-- **Open problem** (Bertin §5.6). Let `α > 1` be real, and suppose there is a **non-zero** real `λ`
such that `(λαⁿ)` has **finitely many limit points modulo 1** (`(limitPointsModOne (fun n => λαⁿ)).Finite`).
**Must `α` be a Pisot number — `α ∈ S`?**

This is the exact transcendental-case analogue of Theorem 5.6.2 (`theorem_5_6_2`): for **algebraic**
`α > 1` the answer is *yes* (that is Theorem 5.6.2). What is **open** — in Bertin's words — is the
existence of a pair `(λ, α)` with `α` **transcendental** and `α > 1` for which `(ε(λαⁿ))` has finitely
many limit points: it is **unknown whether any such transcendental pair exists**. The expected answer
is *no* (none exist), in which case the finiteness hypothesis would force `α` algebraic, hence Pisot,
making the conclusion `α ∈ S` hold unconditionally. It is the finite-limit-point counterpart of the
open problem `pisot_of_smul_pow_tendsto_zero` (where the hypothesis is the stronger `‖λαⁿ‖ → 0`).

Recorded as a `research open` node: the statement below is the conjectured affirmative answer. It is
**not** proved (`sorry`) and **must not** be invoked as a lemma — it stands only as the formal
statement of the question. -/
@[category research open, AMS 11, ref "Ber92", formal_uses S]
theorem pisot_of_finite_limitPointsModOne (α : ℝ) (hα : 1 < α)
    (h : ∃ lam : ℝ, lam ≠ 0 ∧ (limitPointsModOne (fun n : ℕ => lam * α ^ n)).Finite) :
    α ∈ S := by
  sorry

end Bertin
