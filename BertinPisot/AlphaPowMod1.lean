/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import ForMathlib.Data.Real.NearestInt
import BertinPisot.SetSTU
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem 5.3.1 — powers of a Pisot number converge to `0` mod `1` (Bertin §5.3)

Bertin's **Theorem 5.3.1** (*Pisot and Salem Numbers* [Ber92], §5.3): if `θ` is an `S`-number (a
Pisot number) then the sequence `(θⁿ)` converges to `0` modulo `1`, i.e. the distance
`‖θⁿ‖ = distToNearestInt (θⁿ)` from `θⁿ` to the nearest integer tends to `0` — in fact
geometrically.

**Proof, layered.** Write the conjugates of `θ` as `θ = θ⁽¹⁾, θ⁽²⁾, …, θ⁽ˢ⁾` with `|θ⁽ʲ⁾| < 1` for
`j ≥ 2`, and set `δ = max_{j≥2} |θ⁽ʲ⁾| < 1`. The trace `θⁿ + ∑_{j=2}^{s} θ⁽ʲ⁾ⁿ` is a **rational
integer**, and `|∑_{j=2}^{s} θ⁽ʲ⁾ⁿ| ≤ (s−1)δⁿ`; hence `θⁿ` lies within `(s−1)δⁿ` of an integer
(`pisot_pow_approx_int`). That the power sum of conjugates `∑ βⁿ` is a rational integer
(`conj_powerSum_isInt`) is the trace `Tr_{ℚ(θ)/ℚ}(θⁿ) ∈ ℤ`, **proved** via `trace_eq_sum_embeddings`
and `Algebra.isIntegral_trace`. Every step — the power-sum integrality, the extraction of `θ` from its
conjugates, the geometric bound `|θⁿ − k| ≤ (#conj)·δⁿ`, and the final convergence
`distToNearestInt (θⁿ) → 0` (a squeeze) — is **proved**, so Theorem 5.3.1 is **fully axiom-free** (no
`cited` input).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.3, Thm 5.3.1.
-/

open Filter Topology

namespace Bertin

/-- The nearest integer minimises the distance: `distToNearestInt x ≤ |x − k|` for every integer `k`.
(If `|x − k| ≥ 1/2` this is the universal bound `|x − round x| ≤ 1/2`; otherwise `round x = k`.) -/
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

/-- For a finite multiset `m` of reals each `< 1` (and `≥ 0`), there is a uniform bound `δ ∈ [0, 1)`
with `x ≤ δ` for every `x ∈ m`. (Used to extract `δ = max_{β ≠ θ} ‖β‖ < 1` over the finitely many
contracting conjugates.) -/
private lemma exists_unif_bound (m : Multiset ℝ) (h : ∀ x ∈ m, x < 1) (h0 : ∀ x ∈ m, 0 ≤ x) :
    ∃ δ, 0 ≤ δ ∧ δ < 1 ∧ ∀ x ∈ m, x ≤ δ := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, le_refl _, by norm_num, by simp⟩
  | cons a s ih =>
    obtain ⟨δ, hδ0, hδ1, hδb⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
    refine ⟨max δ a, le_max_of_le_left hδ0, max_lt hδ1 (h a (Multiset.mem_cons_self a s)), ?_⟩
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hxs
    · exact le_max_right _ _
    · exact le_trans (hδb x hxs) (le_max_left _ _)

/- The number-theoretic input to Theorem 5.3.1: the power sum `∑ βⁿ` over the conjugates `β` of an
algebraic integer `θ` (the roots of `minpoly ℚ θ`) is a rational integer — the trace
`Tr_{ℚ(θ)/ℚ}(θⁿ) = ∑_σ σ(θ)ⁿ`, an algebraic integer lying in `ℚ`, hence in `ℤ`. **Proved** below
(`conj_powerSum_isInt`); kept as documentation of the argument. -/
informal_result "conjugate-power-sum-integer"
  latex "For an algebraic integer $\\theta$ with conjugates $\\theta^{(1)},\\dots,\\theta^{(s)}$ (the roots of its minimal polynomial over $\\mathbb{Q}$), every power sum $p_n=\\sum_{j=1}^{s}{\\theta^{(j)}}^{n}$ is a rational integer. Indeed $p_n=\\mathrm{Tr}_{\\mathbb{Q}(\\theta)/\\mathbb{Q}}(\\theta^n)=\\sum_{\\sigma}\\sigma(\\theta)^n$ over the embeddings $\\sigma:\\mathbb{Q}(\\theta)\\hookrightarrow\\mathbb{C}$; the trace of the algebraic integer $\\theta^n$ is an algebraic integer in $\\mathbb{Q}$, hence in $\\mathbb{Z}$ (equivalently, $p_n$ is an integer symmetric function of the roots via Newton's identities in the integer coefficients of the monic $\\mathrm{minpoly}_{\\mathbb{Z}}\\theta$)."
  refs "Ber92"

open Polynomial IntermediateField in
/-- **Power sum of conjugates is a rational integer** (the trace input to Theorem 5.3.1). For an
algebraic integer `θ` and every `n`, the sum `∑ βⁿ` over the roots `β` of `minpoly ℚ θ` is a rational
integer. **Proved**: with `K = ℚ(θ)` (a `PowerBasis`), `PowerBasis.liftEquiv` matches the embeddings
`σ : K →ₐ[ℚ] ℂ` with the (distinct — separability) roots, so `∑ βⁿ = ∑_σ (σ θ)ⁿ =
algebraMap ℚ ℂ (Tr_{K/ℚ}(θⁿ))` (`trace_eq_sum_embeddings`); the trace of the algebraic integer `θⁿ` is
an algebraic integer in `ℚ` (`Algebra.isIntegral_trace`), hence in `ℤ`
(`IsIntegrallyClosed.isIntegral_iff`). -/
@[category research solved, AMS 11, ref "Ber92", informal_uses "conjugate-power-sum-integer"]
theorem conj_powerSum_isInt (θ : ℝ) (hθ : IsIntegral ℤ θ) (n : ℕ) :
    ∃ m : ℤ, (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum = (m : ℂ) := by
  have hintℚ : IsIntegral ℚ θ := hθ.tower_top
  have hfd : FiniteDimensional ℚ ℚ⟮θ⟯ := adjoin.finiteDimensional hintℚ
  let pb : PowerBasis ℚ ℚ⟮θ⟯ := adjoin.powerBasis hintℚ
  have hgenθ : pb.gen = AdjoinSimple.gen ℚ θ := adjoin.powerBasis_gen hintℚ
  have hgenInt : IsIntegral ℤ pb.gen := by
    have hf : Function.Injective ((IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ) :=
      (IntermediateField.val ℚ⟮θ⟯).injective
    rw [← isIntegral_algHom_iff _ hf]
    have hv : (IntermediateField.val ℚ⟮θ⟯).restrictScalars ℤ pb.gen = θ := by rw [hgenθ]; rfl
    rw [hv]; exact hθ
  have htrInt : IsIntegral ℤ (Algebra.trace ℚ ℚ⟮θ⟯ (pb.gen ^ n)) :=
    Algebra.isIntegral_trace (hgenInt.pow n)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrInt
  refine ⟨m, ?_⟩
  have hemb := trace_eq_sum_embeddings (K := ℚ) (L := ℚ⟮θ⟯) ℂ (x := pb.gen ^ n)
  have hbridge : ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, (σ pb.gen) ^ n
      = (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum := by
    have hgI : IsIntegral ℚ pb.gen := hgenInt.tower_top
    have hpne : minpoly ℚ pb.gen ≠ 0 := minpoly.ne_zero hgI
    have hsep : (minpoly ℚ pb.gen).Separable := (minpoly.irreducible hgI).separable
    have hnodup : ((minpoly ℚ pb.gen).aroots ℂ).Nodup := by
      rw [Polynomial.aroots]; exact Polynomial.nodup_roots hsep.map
    have hmp : minpoly ℚ pb.gen = minpoly ℚ θ := by rw [hgenθ]; exact minpoly_gen ℚ θ
    haveI : Fintype {y : ℂ // (aeval y) (minpoly ℚ pb.gen) = 0} := Fintype.ofEquiv _ pb.liftEquiv
    rw [Fintype.sum_equiv pb.liftEquiv (fun σ => (σ pb.gen) ^ n) (fun y => ((y : ℂ)) ^ n)
        (fun σ => by rw [pb.liftEquiv_apply_coe])]
    rw [← Finset.sum_subtype ((minpoly ℚ pb.gen).aroots ℂ).toFinset
        (fun x => by
          rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
          exact ⟨fun h => h.2, fun h => ⟨hpne, h⟩⟩)
        (fun y => y ^ n)]
    rw [hmp] at hnodup ⊢
    rw [Finset.sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  calc (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum
      = ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, (σ pb.gen) ^ n := hbridge.symm
    _ = ∑ σ : ℚ⟮θ⟯ →ₐ[ℚ] ℂ, σ (pb.gen ^ n) := by simp_rw [map_pow]
    _ = (algebraMap ℚ ℂ) (Algebra.trace ℚ ℚ⟮θ⟯ (pb.gen ^ n)) := hemb.symm
    _ = (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) m) := by rw [hm]
    _ = (m : ℂ) := by rw [← IsScalarTower.algebraMap_apply]; simp

/- The structural Pisot estimate behind Theorem 5.3.1 — now proved from `conj_powerSum_isInt`. -/
informal_result "pisot-power-geometric-approximation"
  latex "Let $\\theta$ be a Pisot ($S$-) number with conjugates $\\theta=\\theta^{(1)},\\dots,\\theta^{(s)}$, so $|\\theta^{(j)}|<1$ for $j\\ge 2$; set $\\delta=\\max_{j\\ge 2}|\\theta^{(j)}|<1$. The power sum $\\theta^n+\\sum_{j=2}^{s}{\\theta^{(j)}}^{n}=\\mathrm{Tr}_{\\mathbb{Q}(\\theta)/\\mathbb{Q}}(\\theta^n)$ is a rational integer (a symmetric function of the conjugates with integer coefficients), and $\\big|\\sum_{j=2}^{s}{\\theta^{(j)}}^{n}\\big|\\le(s-1)\\delta^{n}$. Hence there is an integer $k_n$ (the trace) with $|\\theta^n-k_n|\\le(s-1)\\delta^{n}$, i.e. $\\|\\theta^n\\|\\le(s-1)\\delta^{n}$."
  refs "Ber92"

/-- **Pisot geometric approximation** (Bertin §5.3, the estimate in the proof of Theorem 5.3.1). For a
Pisot number `θ ∈ S` there are constants `C ≥ 0` and `δ ∈ [0, 1)` such that, for every `n`, `θⁿ` lies
within `C · δⁿ` of some integer `k`: `|θⁿ − k| ≤ C · δⁿ` (Bertin's `‖θⁿ‖ ≤ (s−1)δⁿ`).

**Proved.** The roots of `minpoly ℚ θ` are the conjugates of `θ`; they are distinct (separability) and
`(θ : ℂ)` is one of them. The power sum over all roots is a rational integer `k`
(`conj_powerSum_isInt`), and splitting off `θ` gives `θⁿ − k = −∑_{β ≠ θ} βⁿ`, whose modulus equals
`|θⁿ − k|`. Each remaining root satisfies `‖β‖ < 1` (the Pisot condition), so with
`δ = max_{β ≠ θ} ‖β‖ < 1` (`exists_unif_bound`) and `C = #{β ≠ θ}` the triangle inequality gives
`|θⁿ − k| ≤ ∑_{β ≠ θ} ‖β‖ⁿ ≤ C · δⁿ`. The power-sum integrality (`conj_powerSum_isInt`) is itself
proved via the trace, so this is fully axiom-free. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "pisot-power-geometric-approximation"]
theorem pisot_pow_approx_int (θ : ℝ) (hθ : θ ∈ S) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 ≤ δ ∧ δ < 1 ∧ ∀ n : ℕ, ∃ k : ℤ, |θ ^ n - (k : ℝ)| ≤ C * δ ^ n := by
  obtain ⟨hθ1, hθint, hθconj⟩ := hθ
  have hintℚ : IsIntegral ℚ θ := hθint.tower_top
  have hpne : minpoly ℚ θ ≠ 0 := minpoly.ne_zero hintℚ
  have hθmem : (θ : ℂ) ∈ (minpoly ℚ θ).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    exact ⟨hpne, by rw [show (θ : ℂ) = algebraMap ℝ ℂ θ from rfl,
      Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]⟩
  have hsep : (minpoly ℚ θ).Separable := (minpoly.irreducible hintℚ).separable
  have hnodup : ((minpoly ℚ θ).aroots ℂ).Nodup := by
    rw [Polynomial.aroots]; exact Polynomial.nodup_roots hsep.map
  set rest := ((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ) with hrest
  have hrestlt : ∀ β ∈ rest, ‖β‖ < 1 := by
    intro β hβ
    have hβr : β ∈ (minpoly ℚ θ).aroots ℂ := Multiset.mem_of_mem_erase hβ
    have hβne : β ≠ (θ : ℂ) := by
      intro hc; subst hc
      have h3 : Multiset.count (θ : ℂ) ((minpoly ℚ θ).aroots ℂ) ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hnodup _
      have h2 : Multiset.count (θ : ℂ) rest = 0 := by rw [hrest, Multiset.count_erase_self]; omega
      exact absurd hβ (Multiset.count_eq_zero.mp h2)
    exact hθconj β hβr hβne
  obtain ⟨δ, hδ0, hδ1, hδb⟩ := exists_unif_bound (rest.map (fun β => ‖β‖))
    (by intro x hx; obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx; exact hrestlt β hβ)
    (by intro x hx; obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg β)
  refine ⟨(rest.card : ℝ), δ, by positivity, hδ0, hδ1, fun n => ?_⟩
  obtain ⟨mm, hm⟩ := conj_powerSum_isInt θ hθint n
  refine ⟨mm, ?_⟩
  have hcons : (minpoly ℚ θ).aroots ℂ = (θ : ℂ) ::ₘ rest := (Multiset.cons_erase hθmem).symm
  have hsplit : (((minpoly ℚ θ).aroots ℂ).map (· ^ n)).sum
      = (θ : ℂ) ^ n + (rest.map (· ^ n)).sum := by
    rw [hcons, Multiset.map_cons, Multiset.sum_cons]
  rw [hsplit] at hm
  have hnorm : |θ ^ n - (mm : ℝ)| = ‖(rest.map (· ^ n)).sum‖ := by
    have hc : ((θ ^ n - (mm : ℝ) : ℝ) : ℂ) = -(rest.map (· ^ n)).sum := by
      push_cast; rw [← hm]; ring
    rw [show |θ ^ n - (mm : ℝ)| = ‖((θ ^ n - (mm : ℝ) : ℝ) : ℂ)‖ from (Complex.norm_real _).symm,
      hc, norm_neg]
  rw [hnorm]
  calc ‖(rest.map (· ^ n)).sum‖
      ≤ ((rest.map (· ^ n)).map (‖·‖)).sum := norm_multiset_sum_le _
    _ = (rest.map (fun β => ‖β‖ ^ n)).sum := by rw [Multiset.map_map]; simp [norm_pow]
    _ ≤ (rest.map (fun _ => δ ^ n)).sum := by
        apply Multiset.sum_map_le_sum_map
        intro β hβ
        exact pow_le_pow_left₀ (norm_nonneg β) (hδb _ (Multiset.mem_map_of_mem _ hβ)) n
    _ = (rest.card : ℝ) * δ ^ n := by
        rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]

/-- **Theorem 5.3.1** (Bertin §5.3). The powers of a Pisot number converge to `0` modulo `1`: for
`θ ∈ S`, `distToNearestInt (θⁿ) → 0` as `n → ∞` (in fact geometrically). Proved by squeezing
`0 ≤ distToNearestInt (θⁿ) ≤ C · δⁿ → 0`, where the geometric bound is `pisot_pow_approx_int` and the
lower step is that the nearest integer minimises the distance. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "pisot-power-geometric-approximation"]
theorem theorem_5_3_1 (θ : ℝ) (hθ : θ ∈ S) :
    Tendsto (fun n => distToNearestInt (θ ^ n)) atTop (𝓝 0) := by
  obtain ⟨C, δ, hC, hδ0, hδ1, happ⟩ := pisot_pow_approx_int θ hθ
  refine squeeze_zero (fun n => abs_nonneg _) (g := fun n => C * δ ^ n) (fun n => ?_) ?_
  · obtain ⟨k, hk⟩ := happ n
    exact (distToNearestInt_le_int (θ ^ n) k).trans hk
  · simpa using (tendsto_const_nhds (x := C)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1)

end Bertin
