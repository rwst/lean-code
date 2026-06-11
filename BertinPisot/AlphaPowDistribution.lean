/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.DistributionModOneBasics
import ForMathlib.Data.Real.NearestInt
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Distribution of `αⁿ` modulo one (Bertin §5.0–5.1)

Notation for Bertin's **Chapter 5** (*Pisot and Salem Numbers*, [Ber92]) on the distribution modulo
one of the powers of a real number `α > 1` (the Pisot/Salem theory), and the chapters that follow,
together with its first theorem.

**The integer sequence and its residues.** Fix a real `α > 1` (sometimes written `θ` or `τ`) and a
non-zero real `λ`. To the pair `(λ, α)` Bertin associates the integer sequence `uₙ = E(λαⁿ)` (the
nearest integer, `u`) and the residue sequence `εₙ = ε(λαⁿ) ∈ [-1/2, 1/2)` (`ε`, the centered
fractional part of `BertinPisot.DistributionModOneBasics`), so that `λαⁿ = uₙ + εₙ`
(`self_eq_u_add_ε`) and the nearest-integer distance is `‖λαⁿ‖ = |εₙ|`
(`distToNearestInt_eq_abs_ε`) — the quantity whose decay drives the Pisot theory. Distinct pairs
`(λ, α)` give distinct sequences `(uₙ)` (`u_injective`: equal sequences force `|λαⁿ − λ'α'ⁿ| < 1` for
all `n`, impossible for `α ≠ α'` or `λ ≠ λ'`).

**Generating series.** Many proofs rest on the formal power series `Σ uₙ Xⁿ` (`uSeries`): a real `α`
is algebraic as soon as some non-zero `λ` makes `Σ uₙ Xⁿ` rational (ForMathlib's `IsRationalSeries`,
the Chapter 1 criteria). Analytically, `Σ uₙ zⁿ` and `Σ εₙ zⁿ` are the Taylor expansions of functions
`f` and `ε` (`fTaylor`, `εTaylor`), analytic on `D(0, 1/α)` and `D(0, 1)` respectively — the radius
bounds `inv_le_fTaylor_radius` (`uₙ` grows like `αⁿ`, `abs_u_le`) and `one_le_εTaylor_radius` (`εₙ`
bounded); when `Σ uₙ Xⁿ` is rational both are rational functions. (For an algebraic `α` of degree `s`,
`α⁽ʲ⁾`, `j = 2, …, s`, denote the remaining conjugates of `α` — here taken as the roots of
`minpoly ℚ α` other than `α`, cf. Theorem 5.1.1.)

**Theorem 5.1.1** (`pisotSalem_theorem_5_1_1`, cited): if some `λ ≥ 1` makes `‖λαⁿ‖` uniformly small
(bounded by `1/(2eα(α+1)(1+log λ))`), then `α` is an algebraic integer with all remaining conjugates
of modulus `≤ 1` (a Pisot or Salem number) and `λ ∈ ℚ(α)`. The proof rests on the rationality of the
generating series `Σ uₙ Xⁿ` (Chapter 1 criteria) plus the analytic functions `f`, `ε`; cited.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.0–5.1.
  - [Pat69] Pathiaux, Martine. "Répartition modulo 1 de la suite `λαⁿ`."
    *Séminaire Delange-Pisot-Poitou. Théorie des nombres* 11.1 (1969), 1–6. (Theorem 5.1.1.)
-/

namespace Bertin.AlphaPow

open Filter
open scoped Topology

/-- `uₙ = E(λαⁿ)`: the nearest integer to `λαⁿ` (Bertin's integer part `E = round`); the integer
sequence associated to the pair `(λ, α)`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def u (lam α : ℝ) (n : ℕ) : ℤ := round (lam * α ^ n)

/-- `εₙ = ε(λαⁿ) ∈ [-1/2, 1/2)`: the centered residue of `λαⁿ` modulo one (the scalar `ε` of
`BertinPisot.DistributionModOneBasics`); its absolute value is the nearest-integer distance
`‖λαⁿ‖`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def ε (lam α : ℝ) (n : ℕ) : ℝ := Bertin.ε (lam * α ^ n)

/-- The defining decomposition `λαⁿ = uₙ + εₙ`. -/
@[category API, AMS 11, ref "Ber92"]
theorem self_eq_u_add_ε (lam α : ℝ) (n : ℕ) :
    lam * α ^ n = (u lam α n : ℝ) + ε lam α n :=
  Bertin.self_eq_round_add_ε (lam * α ^ n)

/-- `εₙ ∈ [-1/2, 1/2)`. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_mem_Ico (lam α : ℝ) (n : ℕ) : ε lam α n ∈ Set.Ico (-(1/2) : ℝ) (1/2) :=
  Bertin.ε_mem_Ico (lam * α ^ n)

/-- `|εₙ| ≤ 1/2`. -/
@[category API, AMS 11, ref "Ber92"]
theorem abs_ε_le (lam α : ℝ) (n : ℕ) : |ε lam α n| ≤ 1/2 := by
  have h := ε_mem_Ico lam α n
  rw [Set.mem_Ico] at h
  rw [abs_le]
  exact ⟨h.1, le_of_lt h.2⟩

/-- The nearest-integer distance equals `|εₙ|`: `‖λαⁿ‖ = |εₙ|` (Bertin's identity). -/
@[category API, AMS 11, ref "Ber92"]
theorem distToNearestInt_eq_abs_ε (lam α : ℝ) (n : ℕ) :
    distToNearestInt (lam * α ^ n) = |ε lam α n| := by
  simp only [distToNearestInt, ε, Bertin.ε]

/-- The formal generating series `Σ uₙ Xⁿ ∈ ℤ⟦X⟧` of the integer sequence. Bertin's central tool:
`α` is algebraic as soon as some non-zero `λ` makes this series rational (ForMathlib's
`IsRationalSeries`); its reduced normalized form `P/Q` with `Q(0) = 1` (generalized Fatou,
`IsRationalSeries.exists_coprime_quotient`) drives the proof of Theorem 5.1.1. The associated analytic
function `f = Σ uₙ zⁿ` is `fTaylor`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def uSeries (lam α : ℝ) : PowerSeries ℤ := PowerSeries.mk (u lam α)

/-- The generating series `Σ εₙ Xⁿ` of the residues — the Taylor expansion of a function analytic on
`D(0, 1)`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def εSeries (lam α : ℝ) : PowerSeries ℝ := PowerSeries.mk (ε lam α)

/-! ### Coefficient growth and analyticity of the generating functions

The residues are bounded (`|εₙ| ≤ 1/2`) and the integers grow like `αⁿ` (`abs_u_le`). Hence the
Taylor series of `ε = Σ εₙ zⁿ` and `f = Σ uₙ zⁿ` (`εTaylor`, `fTaylor`, as complex power series)
have radii of convergence at least `1` and `1/α` — i.e. `ε` is analytic on `D(0, 1)` and `f` on
`D(0, 1/α)`, as Bertin states. -/

/-- The integer `uₙ = E(λαⁿ)` differs from `λαⁿ` by at most `1/2`, hence `|uₙ| ≤ |λαⁿ| + 1/2`. This
`αⁿ`-growth is what gives `f = Σ uₙ zⁿ` radius of convergence `1/α`. -/
@[category API, AMS 11, ref "Ber92"]
theorem abs_u_le (lam α : ℝ) (n : ℕ) : |(u lam α n : ℝ)| ≤ |lam * α ^ n| + 1/2 := by
  have hu : (u lam α n : ℝ) = lam * α ^ n - ε lam α n := by linarith [self_eq_u_add_ε lam α n]
  have hb := abs_le.mp (abs_ε_le lam α n)
  rw [hu, abs_le]
  exact ⟨by linarith [neg_abs_le (lam * α ^ n), hb.2], by linarith [le_abs_self (lam * α ^ n), hb.1]⟩

/-- The Taylor series of `ε`, the analytic function `ε(z) = Σ εₙ zⁿ` (as a complex power series). -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def εTaylor (lam α : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (ε lam α n : ℂ))

/-- The Taylor series of `f`, the analytic function `f(z) = Σ uₙ zⁿ` (as a complex power series). -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def fTaylor (lam α : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (u lam α n : ℂ))

/-- `ε = Σ εₙ zⁿ` is analytic on the unit disk `D(0, 1)`: its radius of convergence is `≥ 1`
(the residues are bounded by `1/2`). -/
@[category API, AMS 11, ref "Ber92"]
theorem one_le_εTaylor_radius (lam α : ℝ) : 1 ≤ (εTaylor lam α).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound (εTaylor lam α) (1/2) (r := 1) (fun n => ?_)
  rw [εTaylor, FormalMultilinearSeries.ofScalars_norm]
  simp only [NNReal.coe_one, one_pow, mul_one, Complex.norm_real]
  exact abs_ε_le lam α n

/-- `f = Σ uₙ zⁿ` is analytic on the disk `D(0, 1/α)`: its radius of convergence is `≥ 1/α`
(the coefficients grow like `αⁿ`). -/
@[category API, AMS 11, ref "Ber92", formal_uses abs_u_le]
theorem inv_le_fTaylor_radius (lam α : ℝ) (hα : 1 < α) :
    ENNReal.ofReal (1 / α) ≤ (fTaylor lam α).radius := by
  have hαpos : (0 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) ≤ 1 / α := by positivity
  refine FormalMultilinearSeries.le_radius_of_bound (fTaylor lam α) (|lam| + 1 / 2)
    (r := (1 / α).toNNReal) (fun n => ?_)
  rw [fTaylor, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal (1 / α) hα0,
    Complex.norm_intCast]
  have habs : |(u lam α n : ℝ)| ≤ |lam| * α ^ n + 1 / 2 := by
    have := abs_u_le lam α n
    rwa [abs_mul, abs_pow, abs_of_pos hαpos] at this
  have hcancel : α ^ n * (1 / α) ^ n = 1 := by
    rw [← mul_pow, mul_one_div, div_self (ne_of_gt hαpos), one_pow]
  have hle1 : (1 / α) ^ n ≤ 1 := pow_le_one₀ hα0 (by rw [div_le_one hαpos]; linarith)
  have hpos : (0 : ℝ) ≤ (1 / α) ^ n := by positivity
  calc |(u lam α n : ℝ)| * (1 / α) ^ n
      ≤ (|lam| * α ^ n + 1 / 2) * (1 / α) ^ n := mul_le_mul_of_nonneg_right habs hpos
    _ = |lam| * (α ^ n * (1 / α) ^ n) + (1 / 2) * (1 / α) ^ n := by ring
    _ = |lam| + (1 / 2) * (1 / α) ^ n := by rw [hcancel, mul_one]
    _ ≤ |lam| + 1 / 2 := by nlinarith [hle1]

/-! ### Distinct pairs give distinct sequences

Two different pairs `(λ, α)` and `(λ', α')` (with `α, α' > 1`, `λ, λ' ≠ 0`) cannot define the same
integer sequence `(uₙ)`: equal sequences would force `|λαⁿ − λ'α'ⁿ| < 1` for all `n`, but the
faster-growing power dominates unless `α = α'` and `λ = λ'`. -/

/-- If `1 < β`, `0 < γ < β` and `c ≠ 0`, the differences `|c βⁿ − d γⁿ|` cannot stay below `1`: the
quotient by `βⁿ` tends both to `c` (as `(γ/β)ⁿ → 0`) and to `0` (by the bound), forcing `c = 0`. -/
private theorem exp_diff_bounded_imp {c d β γ : ℝ} (hβ : 1 < β) (hγpos : 0 < γ) (hγβ : γ < β)
    (hc : c ≠ 0) (hbd : ∀ n : ℕ, |c * β ^ n - d * γ ^ n| < 1) : False := by
  have hβpos : 0 < β := by linarith
  have hgb : |γ / β| < 1 := by rw [abs_of_pos (by positivity), div_lt_one hβpos]; exact hγβ
  have hpow : Tendsto (fun n : ℕ => (γ / β) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hgb
  have heq : ∀ n : ℕ, (c * β ^ n - d * γ ^ n) / β ^ n = c - d * (γ / β) ^ n := by
    intro n
    rw [sub_div, mul_div_assoc, div_self (pow_ne_zero n (ne_of_gt hβpos)), mul_one,
      mul_div_assoc, ← div_pow]
  have hqc : Tendsto (fun n : ℕ => (c * β ^ n - d * γ ^ n) / β ^ n) atTop (𝓝 c) := by
    have ht : Tendsto (fun n : ℕ => c - d * (γ / β) ^ n) atTop (𝓝 (c - d * 0)) :=
      tendsto_const_nhds.sub (hpow.const_mul d)
    rw [mul_zero, sub_zero] at ht
    exact (tendsto_congr heq).mpr ht
  have hq0 : Tendsto (fun n : ℕ => (c * β ^ n - d * γ ^ n) / β ^ n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => 1 / β ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hβpos n)]; gcongr; exact le_of_lt (hbd n)
    · simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hβ)
  exact hc (tendsto_nhds_unique hqc hq0)

/-- **Uniqueness of the pair** (Bertin, §5.0). For `α, α' > 1` and `λ, λ' ≠ 0`, if `(λ, α)` and
`(λ', α')` define the same integer sequence `uₙ = E(λαⁿ) = E(λ'α'ⁿ)` for all `n`, then `λ = λ'` and
`α = α'`. -/
@[category textbook, AMS 11, ref "Ber92", formal_uses self_eq_u_add_ε ε_mem_Ico]
theorem u_injective {lam α lam' α' : ℝ} (hα : 1 < α) (hα' : 1 < α')
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0)
    (h : ∀ n, u lam α n = u lam' α' n) : lam = lam' ∧ α = α' := by
  have hres : ∀ n : ℕ, |lam * α ^ n - lam' * α' ^ n| < 1 := by
    intro n
    have hcast : (u lam α n : ℝ) = (u lam' α' n : ℝ) := by exact_mod_cast h n
    have hd : lam * α ^ n - lam' * α' ^ n = ε lam α n - ε lam' α' n := by
      have e1 := self_eq_u_add_ε lam α n
      have e2 := self_eq_u_add_ε lam' α' n
      rw [hcast] at e1; linarith [e1, e2]
    rw [hd]
    have ha := ε_mem_Ico lam α n; rw [Set.mem_Ico] at ha
    have hb := ε_mem_Ico lam' α' n; rw [Set.mem_Ico] at hb
    rw [abs_lt]
    exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
  have hαeq : α = α' := by
    rcases lt_trichotomy α α' with h1 | h1 | h1
    · exact (exp_diff_bounded_imp (c := lam') (d := lam) (β := α') (γ := α)
        hα' (by linarith) h1 hlam' (fun n => by rw [abs_sub_comm]; exact hres n)).elim
    · exact h1
    · exact (exp_diff_bounded_imp (c := lam) (d := lam') (β := α) (γ := α')
        hα (by linarith) h1 hlam hres).elim
  subst hαeq
  refine ⟨?_, rfl⟩
  by_contra hne
  have hpos : 0 < |lam - lam'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have htend : Tendsto (fun n : ℕ => |lam - lam'| * α ^ n) atTop atTop :=
    Tendsto.const_mul_atTop hpos (tendsto_pow_atTop_atTop_of_one_lt hα)
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop 1).exists
  have hb := hres n
  rw [show lam * α ^ n - lam' * α ^ n = (lam - lam') * α ^ n from by ring, abs_mul,
    abs_of_pos (pow_pos (by linarith : (0:ℝ) < α) n)] at hb
  linarith [hn, hb]

/-! ### Theorem 5.1.1 — algebraicity from a uniform bound on `‖λαⁿ‖` -/

informal_result "generating-series-rationality-from-norm-bound"
  latex "A sufficiently strong uniform bound $\\lVert \\lambda\\alpha^n\\rVert \\le C$ on the residues of $(\\lambda\\alpha^n)$ forces the formal generating series $\\sum u_n X^n$ ($u_n = E(\\lambda\\alpha^n)$) to be rational: the bound drives the Hankel/Kronecker determinants of $(u_n)$ eventually to zero, equivalently makes the Taylor function $f = \\sum u_n z^n$ (analytic on $D(0,1/\\alpha)$) continue to a rational function. Rationality then forces $\\alpha$ to be an algebraic integer whose remaining conjugates lie in the closed unit disk (a Pisot or Salem number), with $\\lambda \\in \\mathbb{Q}(\\alpha)$ — the mechanism of Bertin's Theorem 5.1.1."
  refs "Ber92"

/-- **Theorem 5.1.1** (Bertin). Let `α > 1` be real and suppose there is a real `λ ≥ 1` with
`‖λαⁿ‖ ≤ 1 / (2eα(α+1)(1+log λ))` for every `n ∈ ℕ` (the bound `(1)`, with `‖·‖` the distance to the
nearest integer, `distToNearestInt`, and `e = exp 1`). Then `α` is an algebraic integer whose
remaining conjugates all have modulus `≤ 1` (so `α` is a Pisot or Salem number), and `λ ∈ ℚ(α)`.

Proof (cited; **the cited excerpt shows only the statement**, see the accompanying assessment). The
standard shape of Bertin's argument: the bound `(1)` forces the generating series `Σ uₙ Xⁿ` to be
rational — the smallness of the residues `εₙ` makes the Hankel/Kronecker determinants of `(uₙ)`
eventually vanish (equivalently the Taylor function `f = Σ uₙ zⁿ`, analytic on `D(0, 1/α)`, continues
to a rational function), via the rationality criteria of Chapter 1 (ForMathlib's `IsRationalSeries` /
Kronecker-determinant characterisation, `generating-series-rationality-from-norm-bound`). Rationality
of `f` exhibits `1/α` as a pole, forcing `α` to be an algebraic integer; the companion function
`ε = Σ εₙ zⁿ` (analytic on `D(0, 1)`) bounds the remaining conjugates by `1` in modulus; and
`λ ∈ ℚ(α)` follows from the same rational structure. A full formalization additionally needs the
analytic functions `f`, `ε` (radius of convergence, poles), not yet built, so the theorem is recorded
as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92" "Pat69",
  formal_uses uSeries,
  informal_uses "generating-series-rationality-from-norm-bound"]
axiom pisotSalem_theorem_5_1_1 (α lam : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (hbound : ∀ n : ℕ, distToNearestInt (lam * α ^ n) ≤
      1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))) :
    IsIntegral ℤ α ∧
      (∀ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) → ‖β‖ ≤ 1) ∧
      (lam : ℝ) ∈ IntermediateField.adjoin ℚ ({α} : Set ℝ)

end Bertin.AlphaPow
