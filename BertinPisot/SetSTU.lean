/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The sets `U`, `S`, `T` of Pisot and Salem numbers (Bertin §5, Defs 5.1, 5.2.1, 5.2.2)

Three sets of real algebraic integers `> 1`, classified by the moduli of their *other* conjugates.
The conjugates of `α` are the complex roots of its minimal polynomial `minpoly ℚ α` (well defined:
an algebraic integer is in particular algebraic over `ℚ`), and the *other* conjugates are those
different from `α` itself.

* **`U`** (Bertin **Definition 5.1**, [Ber92] Chapter 5): every other conjugate has modulus `≤ 1`.
  This is the union of the Pisot and the Salem numbers.
* **`S`** (Bertin **Definition 5.2.1**): the **Pisot** numbers — every other conjugate has modulus
  *strictly* smaller than `1`.
* **`T`** (Bertin **Definition 5.2.2**): the **Salem** numbers — every other conjugate has modulus
  at most `1`, at least one having modulus exactly `1`.

By construction `U = S ∪ T` (`U_eq_S_union_T`): an element of `U` either has *all* other conjugates
of modulus `< 1` (so it lies in `S`) or has at least one of modulus `1` (so it lies in `T`).

`U` is the central object of Chapter 5. **Theorem 5.1.1**
(`Bertin.AlphaPow.pisotSalem_theorem_5_1_1'`) characterizes membership through the distribution of
`λαⁿ` modulo one: if some `λ ≥ 1` makes the nearest-integer distance `‖λαⁿ‖` uniformly small, then
`α ∈ U` (and moreover `λ ∈ ℚ(α)`). The conjugate condition here is stated exactly as in that
theorem, so the two are definitionally aligned.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5, Defs 5.1,
    5.2.1, 5.2.2.
-/

namespace Bertin

/-- **Definition 5.1.** The set `U` of real algebraic integers `α > 1` whose other conjugates —
the roots of `minpoly ℚ α` other than `α` — all have modulus at most `1`. Equivalently, the set of
Pisot and Salem numbers (`U_eq_S_union_T`). -/
@[category API, AMS 11, ref "Ber92"]
def U : Set ℝ :=
  {α | 1 < α ∧ IsIntegral ℤ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) → ‖β‖ ≤ 1}

/-- Membership in `U` unfolded: `α ∈ U` iff `α > 1`, `α` is an algebraic integer, and every
conjugate of `α` other than `α` itself has modulus `≤ 1`. -/
@[category API, AMS 11, ref "Ber92"]
theorem mem_U_iff (α : ℝ) :
    α ∈ U ↔
      1 < α ∧ IsIntegral ℤ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) → ‖β‖ ≤ 1 :=
  Iff.rfl

/-- **Definition 5.2.1.** The set `S` of **Pisot** numbers: real algebraic integers `θ > 1` whose
other conjugates — the roots of `minpoly ℚ θ` other than `θ` — all have modulus *strictly* smaller
than `1`. -/
@[category API, AMS 11, ref "Ber92"]
def S : Set ℝ :=
  {θ | 1 < θ ∧ IsIntegral ℤ θ ∧ ∀ β ∈ (minpoly ℚ θ).aroots ℂ, β ≠ (θ : ℂ) → ‖β‖ < 1}

/-- Membership in `S` (Pisot numbers) unfolded: `θ ∈ S` iff `θ > 1`, `θ` is an algebraic integer,
and every conjugate of `θ` other than `θ` itself has modulus `< 1`. -/
@[category API, AMS 11, ref "Ber92"]
theorem mem_S_iff (θ : ℝ) :
    θ ∈ S ↔
      1 < θ ∧ IsIntegral ℤ θ ∧ ∀ β ∈ (minpoly ℚ θ).aroots ℂ, β ≠ (θ : ℂ) → ‖β‖ < 1 :=
  Iff.rfl

/-- **All rational integers `> 1` are Pisot numbers** (Bertin §5.2): for `n : ℤ` with `n > 1`,
`(n : ℝ) ∈ S`. The minimal polynomial of `n` over `ℚ` is `X - C n` (degree one), so `n` has no
conjugate other than itself and the strict Pisot condition holds vacuously. -/
@[category API, AMS 11, ref "Ber92", formal_uses S]
theorem intCast_mem_S (n : ℤ) (hn : 1 < n) : (n : ℝ) ∈ S := by
  refine ⟨by exact_mod_cast hn, ?_, ?_⟩
  · -- `(n : ℝ)` is an algebraic integer (it is a rational integer).
    have h : ((n : ℝ)) = algebraMap ℤ ℝ n := (eq_intCast (algebraMap ℤ ℝ) n).symm
    rw [h]; exact isIntegral_algebraMap
  · -- The minimal polynomial `X - C n` has `n` as its only complex root, so there is no *other*
    -- conjugate: the universally quantified strict bound is satisfied vacuously.
    intro β hβ hβn
    exfalso
    apply hβn
    have hmin : minpoly ℚ ((n : ℝ)) = Polynomial.X - Polynomial.C ((n : ℚ)) := by
      have h : ((n : ℝ)) = algebraMap ℚ ℝ ((n : ℚ)) := by rw [eq_ratCast, Rat.cast_intCast]
      rw [h]; exact minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℝ).injective
    rw [hmin, Polynomial.aroots_X_sub_C] at hβ
    simp only [Multiset.mem_singleton] at hβ
    rw [hβ, eq_ratCast]; norm_cast

/-- **Quadratic Pisot numbers are zeros of `X² + q₁X + q₀` with `q₁ + |1 + q₀| < 0`** (Bertin §5.2).
A quadratic number in `S` — a Pisot number `θ` of degree `2` over `ℚ` — is a zero of a monic integer
polynomial `X² + q₁ X + q₀` whose coefficients satisfy `q₁ + |1 + q₀| < 0`. Indeed its two
conjugates are `θ > 1` and `θ' = -q₁ - θ` with `|θ'| < 1` (the strict Pisot condition), and the
inequality is precisely `f(1) < 0` together with `f(-1) > 0` for `f = X² + q₁ X + q₀`, i.e.
`(1 - θ)(1 - θ') < 0` and `(1 + θ)(1 + θ') > 0`. -/
@[category API, AMS 11, ref "Ber92", formal_uses S]
theorem quadratic_mem_S (θ : ℝ) (hθ : θ ∈ S) (hdeg : (minpoly ℚ θ).natDegree = 2) :
    ∃ q₁ q₀ : ℤ, θ ^ 2 + (q₁ : ℝ) * θ + (q₀ : ℝ) = 0 ∧ q₁ + |1 + q₀| < 0 := by
  obtain ⟨hθ1, hθint, hconj⟩ := hθ
  -- The minimal polynomial of the algebraic integer `θ` over `ℚ` has integer coefficients: it is
  -- the image of the monic integer polynomial `minpoly ℤ θ`, which is therefore also of degree `2`.
  have hbridge : minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint
  have hmonic : (minpoly ℤ θ).Monic := minpoly.monic hθint
  have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  have hdeg2 : (minpoly ℤ θ).natDegree = 2 := by
    rw [hbridge, Polynomial.natDegree_map_eq_of_injective hinj] at hdeg; exact hdeg
  have hc2 : (minpoly ℤ θ).coeff 2 = 1 := by
    have := hmonic.coeff_natDegree; rwa [hdeg2] at this
  set q₁ := (minpoly ℤ θ).coeff 1 with hq1
  set q₀ := (minpoly ℤ θ).coeff 0 with hq0
  -- `θ` is a root: `θ² + q₁ θ + q₀ = 0`.
  have hroot : θ ^ 2 + (q₁ : ℝ) * θ + (q₀ : ℝ) = 0 := by
    have haeval : (Polynomial.aeval θ) (minpoly ℤ θ) = 0 := minpoly.aeval ℤ θ
    rw [Polynomial.aeval_eq_sum_range, hdeg2] at haeval
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zsmul_eq_mul,
      pow_zero, pow_one, mul_one, hc2] at haeval
    push_cast at haeval ⊢; linarith [haeval]
  refine ⟨q₁, q₀, hroot, ?_⟩
  -- The other conjugate `θ' = -q₁ - θ` is the second root.
  set θ' : ℝ := -(q₁ : ℝ) - θ with hθ'def
  have hroot' : θ' ^ 2 + (q₁ : ℝ) * θ' + (q₀ : ℝ) = 0 := by rw [hθ'def]; nlinarith [hroot]
  have hmin_ne : minpoly ℚ θ ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; exact two_ne_zero hdeg.symm
  -- `(θ' : ℂ)` is a complex root of `minpoly ℚ θ`.
  have haeval_c : (Polynomial.aeval ((θ' : ℝ) : ℂ)) (minpoly ℚ θ) = 0 := by
    rw [hbridge, Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_sum_range, hdeg2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zsmul_eq_mul,
      pow_zero, pow_one, mul_one, hc2]
    have hcast : ((θ' : ℝ) : ℂ) ^ 2 + (q₁ : ℂ) * ((θ' : ℝ) : ℂ) + (q₀ : ℂ) = 0 := by
      exact_mod_cast hroot'
    push_cast; linear_combination hcast
  have hmem : ((θ' : ℝ) : ℂ) ∈ (minpoly ℚ θ).aroots ℂ :=
    (Polynomial.mem_aroots).mpr ⟨hmin_ne, haeval_c⟩
  -- `θ' ≠ θ`: otherwise `2θ = -q₁` makes `θ` rational, forcing degree `1`, not `2`.
  have hne : ((θ' : ℝ) : ℂ) ≠ ((θ : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    have hθrat : θ = (algebraMap ℚ ℝ) (-(q₁ : ℚ) / 2) := by
      rw [eq_ratCast]; push_cast; rw [hθ'def] at h; linarith [h]
    have hdeg1 : (minpoly ℚ θ).natDegree = 1 := by
      rw [hθrat, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℝ).injective,
        Polynomial.natDegree_X_sub_C]
    rw [hdeg1] at hdeg; omega
  -- The strict Pisot condition gives `|θ'| < 1`, i.e. `-1 < θ' < 1`.
  have hbound : ‖((θ' : ℝ) : ℂ)‖ < 1 := hconj _ hmem hne
  rw [Complex.norm_real, Real.norm_eq_abs, abs_lt] at hbound
  obtain ⟨hlo, hhi⟩ := hbound
  -- Conclude: `q₁ + |1 + q₀| < 0`, equivalently `f(1) < 0 ∧ f(-1) > 0`.
  have hreal : (q₁ : ℝ) + |1 + (q₀ : ℝ)| < 0 := by
    have habs : |1 + (q₀ : ℝ)| < -(q₁ : ℝ) := by
      rw [abs_lt]; constructor <;> nlinarith [hθ1, hlo, hhi, hroot, hθ'def]
    linarith [habs]
  have hcastℤ : ((q₁ + |1 + q₀| : ℤ) : ℝ) < 0 := by push_cast [Int.cast_abs]; linarith [hreal]
  exact_mod_cast hcastℤ

/-- **Definition 5.2.2.** The set `T` of **Salem** numbers: real algebraic integers `τ > 1` whose
other conjugates — the roots of `minpoly ℚ τ` other than `τ` — all have modulus at most `1`, with
at least one having modulus exactly `1`. -/
@[category API, AMS 11, ref "Ber92"]
def T : Set ℝ :=
  {τ | 1 < τ ∧ IsIntegral ℤ τ ∧ (∀ β ∈ (minpoly ℚ τ).aroots ℂ, β ≠ (τ : ℂ) → ‖β‖ ≤ 1) ∧
    ∃ β ∈ (minpoly ℚ τ).aroots ℂ, β ≠ (τ : ℂ) ∧ ‖β‖ = 1}

/-- Membership in `T` (Salem numbers) unfolded: `τ ∈ T` iff `τ > 1`, `τ` is an algebraic integer,
every conjugate of `τ` other than `τ` itself has modulus `≤ 1`, and at least one such conjugate has
modulus exactly `1`. -/
@[category API, AMS 11, ref "Ber92"]
theorem mem_T_iff (τ : ℝ) :
    τ ∈ T ↔
      1 < τ ∧ IsIntegral ℤ τ ∧ (∀ β ∈ (minpoly ℚ τ).aroots ℂ, β ≠ (τ : ℂ) → ‖β‖ ≤ 1) ∧
        ∃ β ∈ (minpoly ℚ τ).aroots ℂ, β ≠ (τ : ℂ) ∧ ‖β‖ = 1 :=
  Iff.rfl

/-- The set of Pisot and Salem numbers is the disjoint union of the two: `U = S ∪ T`. An algebraic
integer `α > 1` whose other conjugates all have modulus `≤ 1` either has every such conjugate of
modulus `< 1` (a Pisot number, `α ∈ S`) or has at least one of modulus `1` (a Salem number,
`α ∈ T`). -/
@[category API, AMS 11, ref "Ber92", formal_uses S T U]
theorem U_eq_S_union_T : U = S ∪ T := by
  ext α
  simp only [Set.mem_union]
  constructor
  · rintro ⟨hα, hint, hle⟩
    by_cases hex : ∃ β ∈ (minpoly ℚ α).aroots ℂ, β ≠ (α : ℂ) ∧ ‖β‖ = 1
    · exact Or.inr ⟨hα, hint, hle, hex⟩
    · refine Or.inl ⟨hα, hint, fun β hβ hβα => ?_⟩
      exact lt_of_le_of_ne (hle β hβ hβα) (fun h => hex ⟨β, hβ, hβα, h⟩)
  · rintro (⟨hα, hint, hlt⟩ | ⟨hα, hint, hle, -⟩)
    · exact ⟨hα, hint, fun β hβ hβα => (hlt β hβ hβα).le⟩
    · exact ⟨hα, hint, hle⟩

/-! ### Further results on `S` (Bertin §5.2): a Rouché criterion and closure under powers -/

open Polynomial Filter in
/-- **Existence of a real zero `> 1`.** A monic integer polynomial `f` with `f(1) < 0` has a real
zero `> 1`. Being monic, `f(x) → +∞` as `x → +∞`; with `f(1) < 0` the intermediate value theorem
produces a root in `(1, ∞)`. This is the elementary part of Bertin's §5.2 remark — it uses only the
first condition `1 + Σᵢ qᵢ = f(1) < 0`; the dominant-coefficient condition is what additionally
forces the root to be a Pisot number (see `exists_mem_S_root_of_dominant`). -/
@[category API, AMS 11, ref "Ber92"]
theorem exists_real_root_gt_one (f : Polynomial ℤ) (hf : f.Monic) (h1 : f.eval 1 < 0) :
    ∃ θ : ℝ, 1 < θ ∧ (Polynomial.aeval θ) f = 0 := by
  set g : Polynomial ℝ := f.map (Int.castRingHom ℝ) with hg
  have hgmonic : g.Monic := hf.map _
  have hg1 : g.eval 1 < 0 := by rw [hg, Polynomial.eval_one_map]; simpa using h1
  -- `g` is nonconstant: a constant monic polynomial is `1`, with `eval 1 = 1 ≥ 0`.
  have hndpos : g.natDegree ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
    have ha1 : a = 1 := by
      have := hgmonic.leadingCoeff; rw [← ha, Polynomial.leadingCoeff_C] at this; exact this
    rw [← ha, Polynomial.eval_C, ha1] at hg1; exact absurd hg1 (by norm_num)
  have hdeg : 0 < g.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hndpos)
  -- `g(x) → +∞`, so `g` is positive at some `M > 1`; IVT on `[1, M]` gives the root.
  have htend : Tendsto (fun x => g.eval x) atTop atTop :=
    g.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by rw [hgmonic.leadingCoeff]; norm_num)
  obtain ⟨M, hM0, hM1⟩ := ((htend.eventually_gt_atTop 0).and (eventually_gt_atTop 1)).exists
  have hcont : ContinuousOn (fun x => g.eval x) (Set.Icc 1 M) :=
    (Polynomial.continuous g).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (g.eval 1) (g.eval M) := ⟨hg1, hM0⟩
  obtain ⟨θ, hθmem, hθ0⟩ := intermediate_value_Ioo hM1.le hcont hmem
  refine ⟨θ, hθmem.1, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq, ← hg]
  exact hθ0

/- The classical Rouché argument behind Bertin's §5.2 dominant-coefficient criterion (no packaged
Rouché / argument principle is available in Mathlib): a monic integer polynomial whose subleading
coefficient dominates the sum of the others has exactly `s - 1` zeros in the open unit disk, so its
remaining real zero `> 1` is a Pisot number. -/
informal_result "rouche-dominant-coefficient-pisot"
  latex "Let $f(X)=X^s+q_{s-1}X^{s-1}+\\cdots+q_0\\in\\mathbb{Z}[X]$ with $|q_{s-1}|>1+\\sum_{i=0}^{s-2}|q_i|$. On $|z|=1$, $|f(z)-q_{s-1}z^{s-1}|\\le 1+\\sum_{i=0}^{s-2}|q_i|<|q_{s-1}z^{s-1}|$, so by Rouch\\'e's theorem $f$ has the same number of zeros in the open unit disk as $q_{s-1}z^{s-1}$, namely $s-1$. If moreover $f(1)<0$, the remaining zero is real and $>1$; its $s-1$ conjugates lie in the open unit disk, so it is a Pisot number."
  refs "Ber92"

/-- **Dominant-coefficient criterion for membership in `S`** (Bertin §5.2). A monic integer
polynomial `f = Xˢ + q_{s-1}Xˢ⁻¹ + ⋯ + q₀` such that
* `f(1) < 0`  (equivalently `1 + Σᵢ qᵢ < 0`), and
* `|q_{s-1}| > 1 + Σ_{i ≤ s-2} |qᵢ|`  (the subleading coefficient dominates the others)

has a real zero `> 1`, and that zero is a Pisot number (`∈ S`). Existence of the zero `> 1` is
elementary (`exists_real_root_gt_one`); that it lies in `S` is Bertin's Rouché argument counting the
`s - 1` conjugates inside the unit disk, which is **not available in Mathlib** (no packaged Rouché /
argument principle). Recorded as a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "rouche-dominant-coefficient-pisot"]
axiom exists_mem_S_root_of_dominant (f : Polynomial ℤ) (hf : f.Monic) (hi : f.eval 1 < 0)
    (hii : 1 + ∑ i ∈ Finset.range (f.natDegree - 1), |f.coeff i| < |f.coeff (f.natDegree - 1)|) :
    ∃ θ : ℝ, 1 < θ ∧ θ ∈ S ∧ (Polynomial.aeval θ) f = 0

/- The Galois-orbit fact behind closure of `S` under powers: every conjugate of `θⁿ` over `ℚ` is
the `n`-th power of a conjugate of `θ`. Provable in principle (each `ℚ`-embedding of `ℚ(θⁿ)` extends
to `ℚ(θ)`), but the conjugate/embedding-extension machinery is not packaged for this in Mathlib. -/
informal_result "conjugates-of-power-are-powers-of-conjugates"
  latex "For an algebraic number $\\theta$ and $n\\ge 1$, every $\\mathbb{Q}$-conjugate of $\\theta^n$ equals $\\beta^n$ for some $\\mathbb{Q}$-conjugate $\\beta$ of $\\theta$: each embedding $\\mathbb{Q}(\\theta^n)\\hookrightarrow\\mathbb{C}$ extends to $\\mathbb{Q}(\\theta)$, sending $\\theta\\mapsto\\beta$ and $\\theta^n\\mapsto\\beta^n$. Hence if every conjugate of $\\theta$ other than $\\theta$ has modulus $<1$, then so does every conjugate of $\\theta^n$ other than $\\theta^n$."
  refs "Ber92"

/-- **`S` is closed under powers** (Bertin §5.2): if `θ` is a Pisot number then so is `θⁿ` for every
`n ≥ 1`. Indeed `θⁿ > 1` and `θⁿ` is an algebraic integer, and every conjugate `≠ θⁿ` of `θⁿ` is
`βⁿ` for a conjugate `β ≠ θ` of `θ`, hence has modulus `|β|ⁿ < 1`. The conjugate-of-power step rests
on field-embedding extension; recorded here as a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "conjugates-of-power-are-powers-of-conjugates"]
axiom pow_mem_S (θ : ℝ) (hθ : θ ∈ S) (n : ℕ) (hn : 1 ≤ n) : θ ^ n ∈ S

/-! ### Salem numbers have degree at least 4 (Bertin §5.2) -/

/-- The product of a three-element multiset with three known distinct entries. (Private helper for
`no_salem_lt_four`; kept out of the corpus graph.) -/
private theorem prod_of_card_three {M : Type*} [CommMonoid M] [DecidableEq M] (R : Multiset M)
    (hcard : R.card = 3) (a b c : M) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : R.prod = a * b * c := by
  rw [← Multiset.prod_erase ha]
  have hcard1 : (R.erase a).card = 2 := by rw [Multiset.card_erase_of_mem ha, hcard]; rfl
  have hb' : b ∈ R.erase a := (Multiset.mem_erase_of_ne hab.symm).mpr hb
  rw [← Multiset.prod_erase hb']
  have hcard2 : ((R.erase a).erase b).card = 1 := by
    rw [Multiset.card_erase_of_mem hb', hcard1]; rfl
  have hc' : c ∈ (R.erase a).erase b :=
    (Multiset.mem_erase_of_ne hbc.symm).mpr ((Multiset.mem_erase_of_ne hac.symm).mpr hc)
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard2
  rw [hx, Multiset.mem_singleton] at hc'
  rw [hx, hc', Multiset.prod_singleton, mul_assoc]

/-- **No Salem number has degree less than `4`** (Bertin §5.2): every Salem number `τ ∈ T` satisfies
`4 ≤ (minpoly ℚ τ).natDegree`. A modulus-`1` conjugate `β ≠ τ` cannot be real — a real conjugate of
modulus `1` is the rational `±1`, which would force `τ` to have degree `1` — so its complex conjugate
`β̄ ≠ β` is a third distinct root (alongside `τ`), giving degree `≥ 3`. Degree exactly `3` is
impossible: the three roots would be `τ, β, β̄`, so by Vieta their product `τ · β · β̄ = τ`
(using `β · β̄ = |β|² = 1`) equals `±` the rational constant term of the minimal polynomial, making
`τ` rational. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T]
theorem no_salem_lt_four (τ : ℝ) (hτ : τ ∈ T) : 4 ≤ (minpoly ℚ τ).natDegree := by
  obtain ⟨hτ1, hτint, hle, β, hβmem, hβne, hβ1⟩ := hτ
  have hτintℚ : IsIntegral ℚ τ := hτint.tower_top
  set a : ℂ := ((τ : ℝ) : ℂ) with ha_def
  have hbridge : minpoly ℚ a = minpoly ℚ τ := minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective τ
  have hτintℂ : IsIntegral ℚ a := by
    have h := hτintℚ.map (Algebra.ofId ℝ ℂ); simpa [Algebra.ofId_apply] using h
  -- `τ` itself is a (complex) root of its minimal polynomial.
  have hamem : a ∈ (minpoly ℚ τ).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hτintℚ, ?_⟩
    rw [ha_def, show ((τ : ℝ) : ℂ) = algebraMap ℝ ℂ τ from rfl, Polynomial.aeval_algebraMap_apply,
      minpoly.aeval, map_zero]
  -- `β` and its complex conjugate `β̄` are conjugates of `τ`, hence roots.
  have hβconj : IsConjRoot ℚ a β := by
    rw [isConjRoot_iff_mem_minpoly_aroots hτintℂ, hbridge]; exact hβmem
  have hconjβ : IsConjRoot ℚ β ((starRingEnd ℂ) β) := by
    have h := isConjRoot_of_algEquiv β (Complex.conjAe.restrictScalars ℚ)
    rwa [show (Complex.conjAe.restrictScalars ℚ) β = (starRingEnd ℂ) β from by
      rw [AlgEquiv.restrictScalars_apply]; exact congrFun Complex.conjAe_coe β] at h
  have hbβmem : (starRingEnd ℂ) β ∈ (minpoly ℚ τ).aroots ℂ := by
    rw [← hbridge, ← isConjRoot_iff_mem_minpoly_aroots hτintℂ]; exact hβconj.trans hconjβ
  have hab : a ≠ β := Ne.symm hβne
  have hββ : β * (starRingEnd ℂ) β = 1 := by
    rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq, hβ1]; norm_num
  have hconja : (starRingEnd ℂ) a = a := by rw [ha_def]; exact Complex.conj_ofReal τ
  have hac : a ≠ (starRingEnd ℂ) β := by
    intro h; apply hab
    calc a = (starRingEnd ℂ) a := hconja.symm
      _ = (starRingEnd ℂ) ((starRingEnd ℂ) β) := by rw [h]
      _ = β := Complex.conj_conj β
  -- A set of distinct roots is no larger than the degree.
  have hdeg_ge : ∀ (s : Finset ℂ), (∀ x ∈ s, x ∈ (minpoly ℚ τ).aroots ℂ) →
      s.card ≤ (minpoly ℚ τ).natDegree := fun s hs =>
    calc s.card ≤ ((minpoly ℚ τ).aroots ℂ).toFinset.card :=
          Finset.card_le_card (fun x hx => Multiset.mem_toFinset.mpr (hs x hx))
      _ ≤ ((minpoly ℚ τ).aroots ℂ).card := Multiset.toFinset_card_le _
      _ ≤ (minpoly ℚ τ).natDegree := (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le
  by_cases hreal : β = (starRingEnd ℂ) β
  · -- `β` real: `β² = 1`, so `β = ±1` is rational, forcing degree `1` — contradicting two roots.
    exfalso
    rw [← hreal] at hββ
    obtain ⟨s, hs⟩ : ∃ s : ℚ, β = algebraMap ℚ ℂ s := by
      rcases mul_self_eq_one_iff.mp hββ with h | h
      · exact ⟨1, by rw [h]; simp⟩
      · exact ⟨-1, by rw [h]; simp⟩
    have hdβ : (minpoly ℚ β).natDegree = 1 := by
      rw [hs, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℂ).injective,
        Polynomial.natDegree_X_sub_C]
    have hd1 : (minpoly ℚ τ).natDegree = 1 := by rw [← hbridge, hβconj, hdβ]
    have hd2 : 2 ≤ (minpoly ℚ τ).natDegree := by
      have := hdeg_ge {a, β} (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exacts [hamem, hβmem])
      rwa [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at this
    omega
  · -- `β` non-real: `τ, β, β̄` are three distinct roots, so degree `≥ 3`.
    have hbc : β ≠ (starRingEnd ℂ) β := hreal
    have h3 : 3 ≤ (minpoly ℚ τ).natDegree := by
      have := hdeg_ge {a, β, (starRingEnd ℂ) β} (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl; exacts [hamem, hβmem, hbβmem])
      rwa [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton] at this
    -- Degree `3` is impossible: Vieta forces `τ` rational.
    have hne3 : (minpoly ℚ τ).natDegree ≠ 3 := by
      intro hd3
      set p := minpoly ℚ τ with hp
      have hmonicℂ : (p.map (algebraMap ℚ ℂ)).Monic := (minpoly.monic hτintℚ).map _
      have hsplits : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
      have hndℂ : (p.map (algebraMap ℚ ℂ)).natDegree = 3 := by
        rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]; exact hd3
      have hcardr : (p.map (algebraMap ℚ ℂ)).roots.card = 3 := by
        rw [← hndℂ]; exact Polynomial.splits_iff_card_roots.mp hsplits
      have hprod : (p.map (algebraMap ℚ ℂ)).roots.prod = a * β * (starRingEnd ℂ) β :=
        prod_of_card_three _ hcardr a β _ hamem hβmem hbβmem hab hac hbc
      have hvieta := hsplits.coeff_zero_eq_prod_roots_of_monic hmonicℂ
      rw [hndℂ, hprod, mul_assoc, hββ, mul_one, Polynomial.coeff_map] at hvieta
      have heq : (algebraMap ℚ ℂ) (p.coeff 0) = -a := by rw [hvieta]; ring
      rw [ha_def, eq_ratCast] at heq
      have hrl : ((p.coeff 0 : ℚ) : ℝ) = -τ := by exact_mod_cast heq
      have hτrat : τ = algebraMap ℚ ℝ (-(p.coeff 0)) := by rw [eq_ratCast]; push_cast; linarith
      have hdeg1 : (minpoly ℚ τ).natDegree = 1 := by
        rw [hτrat, minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℝ).injective,
          Polynomial.natDegree_X_sub_C]
      rw [hdeg1] at hd3; omega
    omega

/-! ### Conjugates and the `γ = τ + 1/τ` notation (Bertin §5.2) -/

/-- **`γ = τ + 1/τ > 2`** (Bertin §5.2). For a Salem number `τ > 1` the real number `γ := τ + 1/τ`
exceeds `2`, since `τ + 1/τ - 2 = (τ - 1)² / τ > 0`. -/
@[category API, AMS 11, ref "Ber92"]
theorem salem_gamma_gt_two (τ : ℝ) (hτ : 1 < τ) : 2 < τ + τ⁻¹ := by
  have h0 : (0 : ℝ) < τ := by linarith
  rw [← sub_pos, show τ + τ⁻¹ - 2 = (τ - 1) ^ 2 / τ by field_simp; ring]
  exact div_pos (pow_pos (by linarith) 2) h0

/-- **`-2 < γ⁽ʲ⁾ < 2`** (Bertin §5.2). For a conjugate `β` of a Salem number lying on the unit circle
(`‖β‖ = 1`, `β ≠ ±1`), the quantity `γ⁽ʲ⁾ := β + 1/β` is the *real* number `2·Re β` — using
`1/β = β̄` for `‖β‖ = 1` — and it lies strictly between `-2` and `2` (strictly, because `β ≠ ±1`
forces `|Re β| < 1`). -/
@[category API, AMS 11, ref "Ber92"]
theorem circle_conj_gamma (β : ℂ) (hβ : ‖β‖ = 1) (h1 : β ≠ 1) (h2 : β ≠ -1) :
    β + β⁻¹ = (2 * β.re : ℝ) ∧ 2 * β.re ∈ Set.Ioo (-2 : ℝ) 2 := by
  have heq : β + β⁻¹ = (2 * β.re : ℝ) := by
    rw [Complex.inv_eq_conj hβ, Complex.add_conj]
  refine ⟨heq, ?_⟩
  have hnorm : β.re ^ 2 + β.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq β
    rw [hβ, Complex.normSq_apply] at h; nlinarith [h]
  have him : β.im ≠ 0 := by
    intro h
    have hre2 : (β.re - 1) * (β.re + 1) = 0 := by nlinarith [hnorm, h]
    have hβr : β = (β.re : ℂ) := Complex.ext rfl (by simp [h])
    rcases mul_eq_zero.mp hre2 with hr | hr
    · have : β.re = 1 := by linarith
      exact h1 (by rw [hβr, this]; norm_num)
    · have : β.re = -1 := by linarith
      exact h2 (by rw [hβr, this]; norm_num)
  have him2 : 0 < β.im ^ 2 := by positivity
  have hre2 : β.re ^ 2 < 1 := by nlinarith [hnorm, him2]
  rw [Set.mem_Ioo]
  constructor <;> nlinarith [hre2, sq_nonneg (β.re - 1), sq_nonneg (β.re + 1)]

/- The reciprocal structure of Salem minimal polynomials behind the conjugate enumeration
`1/τ, τ⁽ʲ⁾, 1/τ⁽ʲ⁾ = τ̄⁽ʲ⁾` — a literature fact not available in Mathlib. -/
informal_result "salem-minpoly-reciprocal"
  latex "The minimal polynomial of a Salem number is reciprocal (self-inversive): if $\\tau$ is a Salem number then $1/\\tau$ is also a conjugate, and the remaining conjugates pair as $\\{\\tau,1/\\tau\\}$ together with unit-circle pairs $\\{\\tau^{(j)}, 1/\\tau^{(j)}=\\overline{\\tau^{(j)}}\\}$. Equivalently $X^{\\deg P}P(1/X)=P(X)$."
  refs "Ber92"

/-- **`1/τ` is a conjugate of a Salem number** (Bertin §5.2). The minimal polynomial of a Salem
number `τ ∈ T` is reciprocal, so `1/τ` is again a conjugate (`∈ aroots`); this underlies the
conjugate enumeration `1/τ, τ⁽ʲ⁾, 1/τ⁽ʲ⁾ = τ̄⁽ʲ⁾` of Bertin §5.2. The reciprocal/palindromic
structure of Salem minimal polynomials is **not available in Mathlib**, so this is recorded as a
`cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T,
  informal_uses "salem-minpoly-reciprocal"]
axiom salem_inv_mem_aroots (τ : ℝ) (hτ : τ ∈ T) :
    ((τ⁻¹ : ℝ) : ℂ) ∈ (minpoly ℚ τ).aroots ℂ

/-! ### Salem numbers of degree 4 (Bertin §5.2) -/

/- The determination of the degree-4 Salem numbers: it uses the reciprocal structure of their
minimal polynomials and the Rouché-type argument that a zero `> 1` of such a quartic is Salem —
neither available in Mathlib. -/
informal_result "salem-degree-four-classification"
  latex "The Salem numbers of degree $4$ are exactly the zeros $>1$ of the reciprocal integer quartics $X^4+q_1X^3+q_2X^2+q_1X+1$ with $2(q_1-1)<q_2<-2(q_1+1)$. Under $Y=X+1/X$ the quartic becomes $Q(Y)=Y^2+q_1Y+(q_2-2)$, with roots $\\gamma=\\tau+1/\\tau>2$ and $\\gamma'=\\tau'+1/\\tau'\\in(-2,2)$; the two inequalities are exactly $Q(2)<0$ and $Q(-2)>0$."
  refs "Ber92"

open Polynomial in
/-- **Classification of degree-4 Salem numbers** (Bertin §5.2). The Salem numbers of degree `4` are
exactly the real numbers `τ > 1` that are a zero of a reciprocal integer quartic
`X⁴ + q₁X³ + q₂X² + q₁X + 1` whose coefficients satisfy `2(q₁ - 1) < q₂ < -2(q₁ + 1)`. (The
substitution `Y = X + 1/X` turns the quartic into `Y² + q₁Y + (q₂ - 2)`, whose roots `γ = τ + 1/τ > 2`
and `γ' ∈ (-2, 2)` give the conditions `Q(2) < 0` and `Q(-2) > 0`.) This rests on the reciprocal
structure of Salem minimal polynomials and the Rouché-type membership argument, **not available in
Mathlib** — recorded as a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T,
  informal_uses "salem-degree-four-classification"]
axiom quartic_salem_iff (τ : ℝ) :
    (τ ∈ T ∧ (minpoly ℚ τ).natDegree = 4) ↔
      (1 < τ ∧ ∃ q₁ q₂ : ℤ, 2 * (q₁ - 1) < q₂ ∧ q₂ < -2 * (q₁ + 1) ∧
        (aeval τ) (X ^ 4 + C q₁ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + 1 : Polynomial ℤ) = 0)

open Polynomial in
/-- **The smallest degree-4 Salem number** (Bertin §5.2) is the real zero `> 1` of
`X⁴ - X³ - X² - X + 1` (the reciprocal `q`-form with `q₁ = q₂ = -1`, and indeed
`2(q₁ - 1) = -4 < -1 = q₂ < 0 = -2(q₁ + 1)`). Its existence as a real root `> 1` is elementary; that
it is genuinely a degree-4 Salem number is `smallest_quartic_mem_T`. -/
@[category API, AMS 11, ref "Ber92", formal_uses exists_real_root_gt_one]
theorem smallest_quartic_salem_root :
    ∃ θ : ℝ, 1 < θ ∧ (aeval θ) (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : Polynomial ℤ) = 0 :=
  exists_real_root_gt_one _ (by monicity!) (by simp)

open Polynomial in
/-- **The smallest degree-4 Salem number is a Salem number** (Bertin §5.2): the real zero `> 1` of
`X⁴ - X³ - X² - X + 1` lies in `T` and has degree `4`. Proved from the classification
`quartic_salem_iff`, since `q₁ = q₂ = -1` satisfies the `q`-condition. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses quartic_salem_iff smallest_quartic_salem_root T]
theorem smallest_quartic_mem_T :
    ∃ θ : ℝ, θ ∈ T ∧ (minpoly ℚ θ).natDegree = 4 ∧
      (aeval θ) (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : Polynomial ℤ) = 0 := by
  obtain ⟨θ, hθ1, hroot⟩ := smallest_quartic_salem_root
  have hq : (aeval θ)
      (X ^ 4 + C (-1 : ℤ) * X ^ 3 + C (-1) * X ^ 2 + C (-1) * X + 1 : Polynomial ℤ) = 0 := by
    rwa [show (X ^ 4 + C (-1 : ℤ) * X ^ 3 + C (-1) * X ^ 2 + C (-1) * X + 1 : Polynomial ℤ)
        = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 by simp only [map_neg, map_one]; ring]
  obtain ⟨hT, hdeg⟩ := (quartic_salem_iff θ).mpr ⟨hθ1, -1, -1, by decide, by decide, hq⟩
  exact ⟨θ, hT, hdeg, hroot⟩

/- Bertin's Theorem 5.2.2 — the existence of Pisot numbers generating a prescribed real number
field — rests on the geometry of numbers (Minkowski's linear forms theorem, Thm 5.2.1): in a real
field `K` of degree `n` one uses Minkowski to find algebraic integers `θ ∈ K` with `θ > 1` and all
other conjugates inside the unit disk, i.e. Pisot numbers with `ℚ(θ) = K`; a norm refinement
(Dirichlet's unit theorem) yields units among them. Not formalized — recorded as a `cited` axiom. -/
informal_result "pisot-numbers-full-degree-real-field"
  latex "Let $K\\subset\\mathbb{R}$ be a real number field of degree $n=[K:\\mathbb{Q}]\\ge 2$, with real embedding $\\sigma_1$ (the inclusion $K\\hookrightarrow\\mathbb{R}$) and remaining embeddings $\\sigma_2,\\dots,\\sigma_n:K\\to\\mathbb{C}$. Applying Minkowski's linear forms theorem (Thm 5.2.1) to the lattice $\\mathcal{O}_K$ of algebraic integers, one finds, for every sufficiently large bound, an algebraic integer $\\theta\\in K$ with $\\sigma_1(\\theta)=\\theta>1$ and $|\\sigma_j(\\theta)|<1$ for all $j\\ge 2$. Such a $\\theta$ is a Pisot ($S$-) number with $\\mathbb{Q}(\\theta)=K$, hence of degree exactly $n$; distinct bounds yield infinitely many. Controlling the norm $\\prod_j\\sigma_j(\\theta)=\\pm1$ (Dirichlet's unit theorem) produces, among them, Pisot numbers that are algebraic units."
  refs "Ber92"

/-- **Theorem 5.2.2** (Bertin §5.2). Every real algebraic extension `K` of `ℚ` of finite degree
`n = [K : ℚ] ≥ 2` contains **infinitely many `S`-numbers** (Pisot numbers) whose degree over `ℚ`
equals `n` — equivalently, infinitely many Pisot numbers `θ ∈ K` with `ℚ(θ) = K` — and **some of
these are units** (algebraic integers `θ` whose inverse `θ⁻¹` is again an algebraic integer).

Modeled with `K : IntermediateField ℚ ℝ` (a real, hence finite, algebraic extension of `ℚ`). The
membership `θ ∈ K`, the Pisot condition `θ ∈ S`, and `(minpoly ℚ θ).natDegree = finrank ℚ K`
together say `θ` is a Pisot number generating `K`. The hypothesis `2 ≤ finrank ℚ K` is needed for the
units clause: a degree-one extension is `ℚ` itself, whose only integer units are `±1` (no Pisot unit
of degree one).

The proof is Bertin's geometry-of-numbers construction built on Minkowski's linear forms theorem
(Theorem 5.2.1, `Bertin.minkowski_linear_forms`), with a unit refinement via Dirichlet's unit
theorem; it is not formalized here, so this is recorded as a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S,
  informal_uses "pisot-numbers-full-degree-real-field"]
axiom infinitely_many_pisot_in_real_field (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    (hK : 2 ≤ Module.finrank ℚ K) :
    {θ : ℝ | θ ∈ K ∧ θ ∈ S ∧ (minpoly ℚ θ).natDegree = Module.finrank ℚ K}.Infinite ∧
    ∃ θ : ℝ, θ ∈ K ∧ θ ∈ S ∧ (minpoly ℚ θ).natDegree = Module.finrank ℚ K ∧
      IsIntegral ℤ θ⁻¹

/-- **Defining quadratic relation of a Salem number over its real-quadratic base** (Bertin §5.2, the
elementary core of Theorem 5.2.3's first claim). For `τ ∈ T` and `γ = τ + τ⁻¹`, both `τ` and `τ⁻¹`
are roots of `X² - γ X + 1`: `τ² - γτ + 1 = 0` and `τ⁻² - γτ⁻¹ + 1 = 0`. This is the elementary
content of "`K = ℚ(τ)` is a quadratic extension of `ℚ(γ)`": `τ` satisfies a degree-2 polynomial over
`ℚ(γ)`, with conjugate root `τ⁻¹`. -/
@[category API, AMS 11, ref "Ber92", formal_uses T]
theorem salem_roots_quadratic (τ : ℝ) (hτ : τ ∈ T) :
    τ ^ 2 - (τ + τ⁻¹) * τ + 1 = 0 ∧ (τ⁻¹) ^ 2 - (τ + τ⁻¹) * τ⁻¹ + 1 = 0 := by
  have hτ0 : τ ≠ 0 := ne_of_gt (by have := hτ.1; linarith)
  refine ⟨?_, ?_⟩ <;> (field_simp; ring)

/-! #### Theorem 5.2.3, claim 1 (proved, modulo Salem's structural theorem)

`ℚ(γ)` is totally real and `[K : ℚ(γ)] = 2` (`γ = τ + τ⁻¹`, `K = ℚ(τ)`). These reduce — by genuine
Mathlib field theory and complex analysis — to **Salem's theorem** on the conjugate structure of a
Salem number (its minimal polynomial is reciprocal, and the off-real conjugates lie on the unit
circle), which is *not* in Mathlib and enters here as two `cited` structural axioms. -/

/-- **Salem reciprocity** (Salem's theorem, Bertin §5.2): the conjugates of a Salem number are closed
under inversion — if `δ` is a root of `minpoly ℚ τ` then `δ ≠ 0` and `δ⁻¹` is again a root.
Equivalently the minimal polynomial of a Salem number is reciprocal (palindromic). This generalises
`salem_inv_mem_aroots` (the case `δ = τ`). **Not available in Mathlib** — a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T,
  informal_uses "salem-minpoly-reciprocal"]
axiom salem_aroots_inv_closed (τ : ℝ) (hτ : τ ∈ T) :
    ∀ δ ∈ (minpoly ℚ τ).aroots ℂ, δ ≠ 0 ∧ δ⁻¹ ∈ (minpoly ℚ τ).aroots ℂ

/-- **Every conjugate of a Salem number is real or on the unit circle** (Salem's theorem). For
`τ ∈ T`, each root `δ` of `minpoly ℚ τ` has `δ.im = 0` (the real conjugates `τ`, `τ⁻¹`) or `‖δ‖ = 1`.
Proved from Salem reciprocity and the defining bound: a conjugate `δ ≠ τ` has `‖δ‖ ≤ 1`, and its
reciprocal `δ⁻¹` (also a conjugate) is `≠ τ` unless `δ = τ⁻¹` is real, so `‖δ⁻¹‖ = ‖δ‖⁻¹ ≤ 1` forces
`‖δ‖ = 1`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T]
theorem salem_conj_real_or_unit (τ : ℝ) (hτ : τ ∈ T) :
    ∀ δ ∈ (minpoly ℚ τ).aroots ℂ, δ.im = 0 ∨ ‖δ‖ = 1 := by
  intro δ hδ
  rcases eq_or_ne δ (τ : ℂ) with h | h
  · left; rw [h]; simp
  · have hle : ‖δ‖ ≤ 1 := hτ.2.2.1 δ hδ h
    obtain ⟨hδ0, hinv⟩ := salem_aroots_inv_closed τ hτ δ hδ
    rcases eq_or_ne δ⁻¹ (τ : ℂ) with h2 | h2
    · left
      have hd : δ = ((τ : ℝ) : ℂ)⁻¹ := by rw [← h2, inv_inv]
      rw [hd]; simp [Complex.inv_im]
    · have hle2 : ‖δ‖⁻¹ ≤ 1 := by rw [← norm_inv]; exact hτ.2.2.1 δ⁻¹ hinv h2
      have hpos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
      right
      have hc := mul_inv_cancel₀ (ne_of_gt hpos)
      nlinarith [mul_le_mul_of_nonneg_left hle2 hpos.le, hc, hle]

/-- The trace `δ + δ⁻¹` of any conjugate of a Salem number is real (real conjugate ⟹ real trace;
unit-modulus conjugate ⟹ `δ⁻¹ = conj δ`, so `δ + δ⁻¹ = 2 Re δ`). -/
private lemma salem_conj_trace_real (τ : ℝ) (hτ : τ ∈ T) :
    ∀ δ ∈ (minpoly ℚ τ).aroots ℂ, (δ + δ⁻¹).im = 0 := by
  intro δ hδ
  rcases salem_conj_real_or_unit τ hτ δ hδ with him | hu
  · simp [Complex.add_im, Complex.inv_im, him]
  · rw [Complex.inv_eq_conj hu, Complex.add_conj]; simp

/- The conjugate–trace structure behind Theorem 5.2.3's claim 1 — the embedding/resolvent
relationship between `minpoly ℚ τ` and `minpoly ℚ (τ+τ⁻¹)`; not packaged in Mathlib. -/
informal_result "salem-gamma-conjugate-trace"
  latex "For a Salem number $\\tau$ with $\\gamma=\\tau+\\tau^{-1}$, the conjugates of $\\gamma$ are exactly the traces $\\delta+\\delta^{-1}$ of the conjugates $\\delta$ of $\\tau$ (an embedding $\\tau\\mapsto\\delta$ sends $\\gamma\\mapsto\\delta+\\delta^{-1}$), and the two-to-one pairing $\\delta\\leftrightarrow\\delta^{-1}$ gives $\\deg\\tau=2\\deg\\gamma$. Hence $\\mathbb{Q}(\\gamma)$ is totally real (each trace is real, since $\\delta$ is real or $|\\delta|=1$) and $[\\mathbb{Q}(\\tau):\\mathbb{Q}(\\gamma)]=2$."
  refs "Ber92"

/-- **Conjugate–trace structure of `γ = τ + τ⁻¹`** (Salem's theorem, Bertin §5.2): every conjugate of
`γ` is the trace `δ + δ⁻¹` of a conjugate `δ` of `τ`, and `deg τ = 2 · deg γ`. The first part is the
embedding fact that an embedding `τ ↦ δ` sends `γ ↦ δ + δ⁻¹`; the second is the two-to-one pairing
`δ ↔ δ⁻¹` of `τ`-conjugates over `γ`-conjugates. **Not available in Mathlib** (the embedding-extension
machinery is not packaged) — a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T,
  informal_uses "salem-gamma-conjugate-trace"]
axiom salem_gamma_minpoly_structure (τ : ℝ) (hτ : τ ∈ T) :
    (∀ α ∈ (minpoly ℚ (τ + τ⁻¹)).aroots ℂ, ∃ δ ∈ (minpoly ℚ τ).aroots ℂ, α = δ + δ⁻¹) ∧
      (minpoly ℚ τ).natDegree = 2 * (minpoly ℚ (τ + τ⁻¹)).natDegree

/-- **Theorem 5.2.3, claim 1a — `ℚ(γ)` is totally real** (Bertin §5.2). For `τ ∈ T` and `γ = τ + τ⁻¹`,
every conjugate of `γ` (root of `minpoly ℚ γ` in `ℂ`) is real. Proof: each such conjugate is a trace
`δ + δ⁻¹` of a `τ`-conjugate (`salem_gamma_minpoly_structure`), and every such trace is real
(`salem_conj_real_or_unit`). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T]
theorem salem_gamma_totally_real (τ : ℝ) (hτ : τ ∈ T) :
    ∀ α ∈ (minpoly ℚ (τ + τ⁻¹)).aroots ℂ, α.im = 0 := by
  intro α hα
  obtain ⟨δ, hδ, rfl⟩ := (salem_gamma_minpoly_structure τ hτ).1 α hα
  exact salem_conj_trace_real τ hτ δ hδ

/-- **Theorem 5.2.3, claim 1b — `[K : ℚ(γ)] = 2`** (Bertin §5.2). For `τ ∈ T`, `K = ℚ(τ)` is a
quadratic extension of the field `ℚ(γ)`, `γ = τ + τ⁻¹`: `finrank ℚ K = 2 · finrank ℚ (ℚ(γ))`. Proof:
`deg τ = 2 · deg γ` (`salem_gamma_minpoly_structure`) together with
`IntermediateField.adjoin.finrank` (`finrank ℚ ℚ⟮x⟯ = (minpoly ℚ x).natDegree` for `x` integral over
`ℚ`); `τ` is integral (`τ ∈ T`) and `γ = τ + τ⁻¹` is integral (sum of algebraic numbers). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T]
theorem salem_field_finrank_two (τ : ℝ) (hτ : τ ∈ T) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({τ} : Set ℝ))
      = 2 * Module.finrank ℚ (IntermediateField.adjoin ℚ ({τ + τ⁻¹} : Set ℝ)) := by
  have hτQ : IsIntegral ℚ τ := hτ.2.1.tower_top
  have hγQ : IsIntegral ℚ (τ + τ⁻¹) := by
    have hinv : IsIntegral ℚ τ⁻¹ := by
      rw [← isAlgebraic_iff_isIntegral] at hτQ ⊢; exact hτQ.inv
    exact hτQ.add hinv
  rw [IntermediateField.adjoin.finrank hτQ, IntermediateField.adjoin.finrank hγQ]
  exact (salem_gamma_minpoly_structure τ hτ).2

/- Bertin's Theorem 5.2.3 describes the fine structure of the Salem numbers inside `K = ℚ(τ)`: the
field is a real quadratic extension of the totally real field `ℚ(γ)` (γ = τ + τ⁻¹); the Salem numbers
in `K` are exactly the positive powers of a fundamental Salem number `τ₀` generating `K`; and each is
a ratio of two Pisot numbers of `K`. The proof rests on Dirichlet's unit theorem (finitely many units
of `K` in a bounded region ⟹ `{log τ : τ ∈ K ∩ T} ∪ {0}` is a discrete subgroup of `ℝ`, hence cyclic
with generator `log τ₀`) together with Salem-number-specific facts (closure of `K ∩ T` under
products, the totally-real structure of `ℚ(γ)`, and `θτ ∈ K ∩ S` for `θ ∈ K ∩ S`) — machinery not
available in Mathlib. Recorded as a `cited` axiom. -/
informal_result "salem-field-structure-5-2-3"
  latex "Let $\\tau$ be a Salem ($T$-) number and $K=\\mathbb{Q}(\\tau)$, $\\gamma=\\tau+\\tau^{-1}$. The conjugates of $\\gamma$ are the real numbers $\\beta+\\beta^{-1}=2\\operatorname{Re}\\beta$ over the conjugates $\\beta$ of $\\tau$, so $\\mathbb{Q}(\\gamma)$ is totally real and $K$ is a real quadratic extension of it ($\\tau^2-\\gamma\\tau+1=0$). The product of two elements of $K\\cap T$ lies in $K\\cap T$, and (Dirichlet) only finitely many units of $K$ lie in a bounded part of $\\mathbb{C}$, so $\\{\\log\\tau:\\tau\\in K\\cap T\\}\\cup\\{0\\}$ is a discrete additive subgroup of $\\mathbb{R}$, hence $=\\mathbb{Z}\\,\\log\\tau_0$ for a fundamental $\\tau_0\\in K\\cap T$ with $\\mathbb{Q}(\\tau_0)=K$; thus $K\\cap T=\\{\\tau_0^{\\,n}:n\\ge 1\\}$. Finally, for $\\theta\\in K\\cap S$ the number $\\theta'=\\theta\\tau$ is an algebraic integer whose remaining conjugates have modulus $<1$, so $\\theta'\\in K\\cap S$ and $\\tau=\\theta'/\\theta$ is a quotient of two numbers of $K\\cap S$."
  refs "Ber92"

/-- **Theorem 5.2.3** (Bertin §5.2). Let `τ` be a `T`-number (Salem number) and `K = ℚ(τ)`. Then:
1. `K` is a **real quadratic extension of the totally real field `ℚ(γ)`**, `γ = τ + τ⁻¹` — every
   conjugate of `γ` is real, and `[K : ℚ(γ)] = 2` (here `finrank ℚ K = 2 · finrank ℚ (ℚ(γ))`);
2. the Salem numbers of `K` are exactly the **positive powers `τ₀ⁿ` of a fundamental Salem number
   `τ₀ ∈ K ∩ T` generating `K`**;
3. **every Salem number of `K` is a quotient of two Pisot numbers of `K`** (`σ = a / b` with
   `a, b ∈ K ∩ S`).

Bertin's proof uses Dirichlet's unit theorem and the discreteness of `{log τ : τ ∈ K ∩ T}` together
with Salem-specific facts (`salem-field-structure-5-2-3`); it needs machinery beyond current Mathlib,
so this is recorded as a `cited` axiom. The elementary first-claim relation `τ² - γτ + 1 = 0` is
proved separately in `salem_roots_quadratic`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses S T,
  informal_uses "salem-field-structure-5-2-3"]
axiom theorem_5_2_3 (τ : ℝ) (hτ : τ ∈ T) :
    -- (1) K = ℚ(τ) is a real quadratic extension of the totally real field ℚ(γ), γ = τ + τ⁻¹
    ((∀ β ∈ (minpoly ℚ (τ + τ⁻¹)).aroots ℂ, β.im = 0) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ ({τ} : Set ℝ))
        = 2 * Module.finrank ℚ (IntermediateField.adjoin ℚ ({τ + τ⁻¹} : Set ℝ))) ∧
    -- (2) K ∩ T = { τ₀ⁿ : n ≥ 1 } for a fundamental τ₀ ∈ K ∩ T generating K
    (∃ τ₀ : ℝ, τ₀ ∈ T ∧ τ₀ ∈ IntermediateField.adjoin ℚ ({τ} : Set ℝ) ∧
      IntermediateField.adjoin ℚ ({τ₀} : Set ℝ) = IntermediateField.adjoin ℚ ({τ} : Set ℝ) ∧
      ∀ σ : ℝ, (σ ∈ IntermediateField.adjoin ℚ ({τ} : Set ℝ) ∧ σ ∈ T)
        ↔ ∃ n : ℕ, 1 ≤ n ∧ σ = τ₀ ^ n) ∧
    -- (3) every number of K ∩ T is a quotient of two numbers of K ∩ S
    (∀ σ : ℝ, σ ∈ IntermediateField.adjoin ℚ ({τ} : Set ℝ) → σ ∈ T →
      ∃ a b : ℝ, a ∈ IntermediateField.adjoin ℚ ({τ} : Set ℝ) ∧ a ∈ S ∧
        b ∈ IntermediateField.adjoin ℚ ({τ} : Set ℝ) ∧ b ∈ S ∧ σ = a / b)

end Bertin
