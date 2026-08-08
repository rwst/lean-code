/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonTools
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The machinery of [AF17] §4 (plan-formalize-AF17, WP4)

The Mahler alternative at an algebraic point — the theorem that settled **Cobham's 1968
conjecture** — is reached along [AF17] §4 from a lifting theorem about *regular* points, instead of
being assumed wholesale, as `AF.transcendental_or_rat_of_automatic` was until WP5 retired it
(2026-08-04; that declaration is now a theorem resting on this route).

**Since WP20 this file carries none of the three theorems and no axiom.**  `AF.theoreme_1_7_i`,
`AF.corollaire_1_8` and `AF.corollaire_1_8_rat` are in
`CITED/AdamczewskiFaverjonTheoreme17.lean`, and the lifting theorem they use is
`AF.theoreme_2_1`, proved in `CITED/AdamczewskiFaverjonTheoreme21.lean` from [AF22] §2.  The reason
is only an import direction: every file of Stage 2 imports *this* one, for the dictionary
`AF.IsSumOnBall` and for Lemme 4.2's doubling construction, so this file cannot see the end of
Stage 2.  What is left here is that machinery, and it is `std3`.

## The route, and why it is not the one the plan expected

`plans/plan-formalize-AF17.html` budgeted WP4 for [AF17] **§5** (Théorèmes 1.10, 1.9, 1.7).  WP3
found that §5 is avoidable: §4 gives a *first* proof of Théorème 1.7 (i) from the three auxiliary
lemmas and a lifting theorem applied to a **linear** form, and Corollaire 1.8 is Théorème 1.7 (i)
for the pair `(f, 1)`.  So this file follows §4:

`RB/MahlerAnalytic` → `lemme_4_1_of_polynomial` → `lemme_4_2` → `theoreme_2_1`
  → `relation_formal_of_functional` → `lemme_4_3` → `theoreme_1_7_i` → `corollaire_1_8`

**Théorème 1.10 is never used**, and neither are Théorème 1.9 or Théorème 1.7 (ii).  That removes
the one genuinely analytic argument of §5 — Laurent truncation, operator-norm estimates, the
integers `N₀`, `N₁` — from the critical path; the plan had budgeted 800–1500 lines for it.

## What the route assumes, and what that assumption may *not* be relaxed to

The lifting theorem — [AF17] Théorème 1.4 in degree one, equivalently [AF22] Théorème 2.1 in the
linear case — is the one deep input of the route, and gate G1 of the plan established that this is
the only form of it the whole route needs.  It was an axiom (`AF.lifting_regular`) until WP20; it
is now `AF.theoreme_2_1`.

**The hypothesis `hLalg` (every element of the coefficient field is algebraic over `ℚ`) is
load-bearing, not decoration.**  Dropped, the axiom is *false*: take `f(z) = Σ_{n≥0} z^{2ⁿ}`, which
satisfies `f(z) = z + f(z²)`, a system with `det = 1`, regular everywhere, and a transcendental
`α` in the unit disc; lifting the relation `1·f(α) + (−f(α))·1 = 0` would give `w₁(z)f(z) + w₂(z) =
0` with `w₁(α) = 1 ≠ 0`, making `f` rational, which it is not — the unit circle is its natural
boundary.  Mahler's method is a
statement about algebraic points; the type-level generality of an abstract `L` must therefore be
cut back by an explicit hypothesis.  Similarly, the ambient field is fixed to `ℂ` rather than left
as an abstract complete normed field: the archimedean analysis is part of the theorem.

## The dictionary `AF.IsSumOnBall`, and the bridge

[AF17] work with *«des fonctions analytiques dans un voisinage de l'origine et à coefficients dans
`k`»*, and use both aspects: the Mahler system, the point `α` and the lifting theorem see the
**function**, the descent of Lemme 4.3 sees the **coefficients**.  `AF.IsSumOnBall r f H` carries
both, and the two directions of the passage are proved here:

* `AF.IsSumOnBall.polyMul` (formal ⟹ functional) is elementary — a *polynomial* multiplier is a
  finite shift, so no Cauchy product appears;
* `AF.relation_formal_of_functional` (functional ⟹ formal) is the uniqueness of Taylor
  coefficients, obtained from Mathlib's `HasFPowerSeriesAt.eq_zero` through
  `AF.eq_zero_of_hasSum_zero`.  This is the *«analytic-to-formal bridge»* that
  `CITED/AdamczewskiFaverjonTools.lean` recorded as owed.

## Two departures from the printed statements, both deliberate

* **Théorème 1.7 (i) is proved with its support statement.**  [AF17] state the conclusion as
  «linéairement dépendants sur `k`»; their proof gives more, and the extra is what makes
  Corollaire 1.8 immediate: the descended relation `mu` vanishes wherever the given relation `lam`
  vanishes, and keeps a nonzero coefficient at the chosen index `i₀`.  (This is the set `I` of
  Lemme 4.3, taken to be `{i : λᵢ = 0}`.)
* **`k` need not be a number field.**  [AF17] say *«un corps de nombres»*; the descent used here
  applies one `k`-linear functional and uses neither finiteness nor separability, so an arbitrary
  subfield of the coefficient field works.

## Not built here

* [AF17] §5 in its own right — Théorèmes 1.9, 1.10 and Théorème 1.7 (ii), which describe
  `Rel_k(f₁(α),…,fₙ(α))` completely.  They are off the route to Corollaire 1.8.
* The wiring to the corpus — **done**, `RB/AutomaticValue.lean` (WP5, 2026-08-04): the corpus's
  automatic series live on `ℝ`, so `RB.genFun a (α : ℝ)` is transported to `ℂ`
  (`RB.genFun_ofReal`), `RB.mahlerMatrix`'s entries are mapped from `ℤ[z]` to `ℚ[z]`
  (`RB.mahlerMatrixOver`), and `AS.IsAutomatic` is turned into a system with `det ≠ 0`.  The last
  of these is *not* Becker's theorem — [Bec94] Thm 1 does not give the determinant condition in
  polynomial form — but an elementary repair over `K(z)`, `RB.exists_nonsingular_mahlerSystem`
  (gate G4).  So retiring `AF.transcendental_or_rat_of_automatic` cost **no** second axiom.
* Stage 2 of the plan (WP7–WP20): discharging the lifting theorem from [AF22] §2 — **done**,
  `CITED/AdamczewskiFaverjonTheoreme21.lean`.

## Contents

* `AF.IsSumOnBall`, `AF.IsSumOnBall.mapCoeff`, `AF.isSumOnBall_one`, `AF.IsSumOnBall.X_pow_mul`,
  `AF.IsSumOnBall.C_mul`, **`AF.IsSumOnBall.polyMul`** — the series/function dictionary.
* **`AF.eq_zero_of_hasSum_zero`**, `AF.eq_zero_of_isSumOnBall_zero`,
  **`AF.relation_formal_of_functional`**, **`AF.eval_of_relation_formal`** — the bridge.
* `AF.substPowSeries`, `AF.dblIterSer`, `AF.isSumOnBall_dblIterSer` — the series of the doubled solution
  vector of `AF.lemme_4_2`.
* `AF.dblExt`, `AF.dblExt_dblEmb`, `AF.dblExt_eq_zero`, **`AF.sum_dblIdx`** — extending a relation
  vector by zero, and collapsing a sum over the doubled index set.
* `AF.IsMahlerSolution.mapCoeff`, `AF.det_mapCoeff_ne_zero`, `AF.adjoinOne`, `AF.det_adjoinOne`,
  **`AF.isMahlerSolution_adjoinOne`** — enlarging the coefficient field, and adjoining `g ≡ 1`.
* `AF.aeval_algebraMap_eq` — evaluation over a subfield, read in `ℂ`.

The three theorems themselves — `AF.theoreme_1_7_i`, `AF.corollaire_1_8`,
`AF.corollaire_1_8_rat` — are in `CITED/AdamczewskiFaverjonTheoreme17.lean`.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90
  (arXiv:1508.07158v2; Thm 1.4 p. 3, Cor 1.5 p. 4, Thm 1.7 and Cor 1.8 p. 5, §4 pp. 16–22, whose
  numbering is used throughout).
* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022).  Théorème 2.1 is `AF.theoreme_2_1`; its §2 is Stage 2 of the plan.
* [Cob68] A. Cobham. The 1968 conjecture on automatic series at rational points, settled by
  Corollaire 1.8.
* [AF17f] `plans/plan-formalize-AF17.html` (2026-08-03): WP4, gate G1, risk R6.
-/

namespace AF

open Polynomial

/-! ## Power series with coefficients in a subfield, read as functions on a disc -/

section Dictionary

variable {K 𝕜 : Type*} [Field K] [NormedField 𝕜] [Algebra K 𝕜]

/-- `H : 𝕜 → 𝕜` **is the sum on the open disc of radius `r`** of the power series `f`, whose
coefficients lie in the subfield `K`.

This is [AF17]'s standing phrase *«des fonctions analytiques dans un voisinage de l'origine et à
coefficients dans `k`»* (Lemme 4.3) made explicit: it carries both the analytic object `H`, which
the Mahler system and the evaluation at `α` talk about, and the formal object `f`, which the
descent of Lemme 4.3 talks about. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
def IsSumOnBall (r : ℝ) (f : PowerSeries K) (H : 𝕜 → 𝕜) : Prop :=
  ∀ z : 𝕜, ‖z‖ < r → HasSum (fun n => algebraMap K 𝕜 (PowerSeries.coeff n f) * z ^ n) (H z)

/-- Reading the coefficients in a larger field changes nothing. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.mapCoeff {L : Type*} [Field L] [Algebra K L] [Algebra L 𝕜]
    [IsScalarTower K L 𝕜] {r : ℝ} {f : PowerSeries K} {H : 𝕜 → 𝕜} (h : IsSumOnBall r f H) :
    IsSumOnBall r (f.map (algebraMap K L)) H := by
  intro z hz
  have e : ∀ n, algebraMap L 𝕜 (PowerSeries.coeff n (f.map (algebraMap K L)))
      = algebraMap K 𝕜 (PowerSeries.coeff n f) := by
    intro n; rw [PowerSeries.coeff_map, ← IsScalarTower.algebraMap_apply]
  simpa only [e] using h z hz

/-- The constant function `1` is the sum of the power series `1`: [AF17]'s remark that `g ≡ 1` is
`q`-Mahlerian for every `q ≥ 2`, on the series side. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma isSumOnBall_one (r : ℝ) :
    IsSumOnBall (𝕜 := 𝕜) r (1 : PowerSeries K) (fun _ => 1) := by
  intro z _
  have e : (fun n => algebraMap K 𝕜 (PowerSeries.coeff n (1 : PowerSeries K)) * z ^ n)
      = fun n => if n = 0 then (1 : 𝕜) else 0 := by
    funext n
    by_cases h : n = 0 <;> simp [h, PowerSeries.coeff_one]
  rw [e]
  exact hasSum_ite_eq (0 : ℕ) (1 : 𝕜)

@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.add {r : ℝ} {f g : PowerSeries K} {H₁ H₂ : 𝕜 → 𝕜} (hf : IsSumOnBall r f H₁)
    (hg : IsSumOnBall r g H₂) : IsSumOnBall r (f + g) (fun z => H₁ z + H₂ z) := by
  intro z hz
  have e : ∀ n, algebraMap K 𝕜 (PowerSeries.coeff n (f + g)) * z ^ n
      = algebraMap K 𝕜 (PowerSeries.coeff n f) * z ^ n
        + algebraMap K 𝕜 (PowerSeries.coeff n g) * z ^ n := by
    intro n; rw [map_add, map_add, add_mul]
  simpa only [e] using (hf z hz).add (hg z hz)

@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.finsetSum {ι : Type*} {r : ℝ} {g : ι → PowerSeries K} {H : ι → 𝕜 → 𝕜}
    (s : Finset ι) (h : ∀ i ∈ s, IsSumOnBall r (g i) (H i)) :
    IsSumOnBall r (∑ i ∈ s, g i) (fun z => ∑ i ∈ s, H i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro z _; simp
  | @insert i s hi ih =>
      have h1 : IsSumOnBall r (g i) (H i) := h i (Finset.mem_insert_self i s)
      have h2 : IsSumOnBall (𝕜 := 𝕜) r (∑ j ∈ s, g j) (fun z => ∑ j ∈ s, H j z) :=
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have := h1.add h2
      simpa only [Finset.sum_insert hi] using this

/-- Multiplying the series by `X ^ m` multiplies the sum by `z ^ m`. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.X_pow_mul {r : ℝ} {f : PowerSeries K} {H : 𝕜 → 𝕜} (h : IsSumOnBall r f H)
    (m : ℕ) : IsSumOnBall r ((PowerSeries.X : PowerSeries K) ^ m * f) (fun z => z ^ m * H z) := by
  intro z hz
  have hinj : Function.Injective (fun j : ℕ => j + m) := add_left_injective m
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => j + m) →
      algebraMap K 𝕜 (PowerSeries.coeff n ((PowerSeries.X : PowerSeries K) ^ m * f)) * z ^ n = 0 := by
    intro n hn
    have hlt : ¬ m ≤ n := fun hle => hn ⟨n - m, by simpa using Nat.sub_add_cancel hle⟩
    simp [PowerSeries.coeff_X_pow_mul', hlt]
  rw [← hinj.hasSum_iff hzero]
  have e : ((fun n => algebraMap K 𝕜
        (PowerSeries.coeff n ((PowerSeries.X : PowerSeries K) ^ m * f)) * z ^ n) ∘
      fun j : ℕ => j + m)
      = fun j => z ^ m * (algebraMap K 𝕜 (PowerSeries.coeff j f) * z ^ j) := by
    funext j
    simp only [Function.comp_apply, PowerSeries.coeff_X_pow_mul, pow_add]
    ring
  rw [e]
  exact (h z hz).mul_left (z ^ m)

/-- Multiplying the series by a scalar of `K`. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.C_mul {r : ℝ} {f : PowerSeries K} {H : 𝕜 → 𝕜} (h : IsSumOnBall r f H) (c : K) :
    IsSumOnBall r (PowerSeries.C c * f) (fun z => algebraMap K 𝕜 c * H z) := by
  intro z hz
  have e : ∀ n, algebraMap K 𝕜 (PowerSeries.coeff n (PowerSeries.C c * f)) * z ^ n
      = algebraMap K 𝕜 c * (algebraMap K 𝕜 (PowerSeries.coeff n f) * z ^ n) := by
    intro n; rw [PowerSeries.coeff_C_mul, map_mul, mul_assoc]
  simpa only [e] using (h z hz).mul_left (algebraMap K 𝕜 c)

@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma coe_monomial_eq (n : ℕ) (a : K) :
    ((Polynomial.monomial n a : Polynomial K) : PowerSeries K)
      = PowerSeries.C a * PowerSeries.X ^ n := by
  ext m
  rcases eq_or_ne m n with rfl | hm
  · simp [PowerSeries.coeff_C_mul]
  · simp [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hm]

/-- **Multiplying the series by a polynomial multiplies the sum by the value of the polynomial.**
The one place where the passage between the formal and the analytic pictures is needed in the easy
direction; note that it is elementary precisely because the multiplier is a *polynomial* (a finite
shift), no Cauchy product being involved. -/
@[category research solved, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.polyMul {r : ℝ} {f : PowerSeries K} {H : 𝕜 → 𝕜} (h : IsSumOnBall r f H)
    (w : Polynomial K) :
    IsSumOnBall r ((w : PowerSeries K) * f) (fun z => aeval z w * H z) := by
  induction w using Polynomial.induction_on' with
  | add p q hp hq =>
      have := hp.add hq
      simpa only [Polynomial.coe_add, add_mul, map_add, Polynomial.aeval_add] using this
  | monomial n a =>
      have := (h.X_pow_mul n).C_mul a
      rw [coe_monomial_eq, mul_assoc]
      simpa only [Polynomial.aeval_monomial, mul_assoc] using this

end Dictionary

/-! ## The analytic-to-formal bridge -/

section Bridge

variable {K 𝕜 : Type*} [Field K] [NontriviallyNormedField 𝕜] [Algebra K 𝕜]

/-- **A power series that sums to `0` on a disc has zero coefficients.**  This is the uniqueness of
Taylor coefficients, in the only form needed here; it is what lets a relation between *functions*
be read off coefficientwise, as in the proof of [AF17] Lemme 4.3 (*«comme l'indéterminée `z` est
transcendante sur `ℂ` …»*). -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem eq_zero_of_hasSum_zero {c : ℕ → 𝕜} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : 𝕜, ‖z‖ < r → HasSum (fun n => c n * z ^ n) 0) : c = 0 := by
  obtain ⟨z₀, hz₀0, hz₀r⟩ := NormedField.exists_norm_lt 𝕜 hr
  set p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := FormalMultilinearSeries.ofScalars 𝕜 c with hp
  have hrad : ((‖z₀‖₊ : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_eventually_le 1 ?_
    have htend : Filter.Tendsto (fun n => ‖c n * z₀ ^ n‖) Filter.atTop (nhds 0) := by
      simpa using ((h z₀ hz₀r).summable.tendsto_atTop_zero).norm
    filter_upwards [htend.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn
    simpa only [hp, FormalMultilinearSeries.ofScalars_norm, coe_nnnorm, norm_mul, norm_pow]
      using hn
  have hball : HasFPowerSeriesOnBall (0 : 𝕜 → 𝕜) p 0 ((‖z₀‖₊ : NNReal) : ENNReal) :=
    { r_le := hrad
      r_pos := by simpa [ENNReal.coe_pos, nnnorm_pos] using hz₀0
      hasSum := by
        intro y hy
        have hy' : ‖y‖ < ‖z₀‖ := by
          simpa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_coe_iff,
            coe_nnnorm] using hy
        have := h y (hy'.trans hz₀r)
        simpa only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
          Pi.zero_apply] using this }
  have hzero : p = 0 := hball.hasFPowerSeriesAt.eq_zero
  simpa only [hp, FormalMultilinearSeries.ofScalars_series_eq_zero] using hzero

/-- The formal shadow of a function is unique: a series summing to `0` on a disc is `0`. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem eq_zero_of_isSumOnBall_zero {r : ℝ} (hr : 0 < r) {f : PowerSeries K}
    (h : IsSumOnBall (𝕜 := 𝕜) r f (fun _ => 0)) : f = 0 := by
  have := eq_zero_of_hasSum_zero (𝕜 := 𝕜) (c := fun n => algebraMap K 𝕜 (PowerSeries.coeff n f)) hr h
  ext n
  have hn : algebraMap K 𝕜 (PowerSeries.coeff n f) = 0 := congrFun this n
  simpa using (map_eq_zero_iff _ (algebraMap K 𝕜).injective).mp hn

/-- **The analytic-to-formal bridge.**  A linear relation with polynomial coefficients between
functions that are sums of power series over `K` on a disc *is* a relation between those power
series.  This is what turns the output of the lifting theorem — an identity of analytic functions —
into the hypothesis of the descent lemma `AF.lemme_4_3`, which is an identity of formal series. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem relation_formal_of_functional {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    {f : ι → PowerSeries K} {H : ι → 𝕜 → 𝕜} (hf : ∀ i, IsSumOnBall r (f i) (H i))
    (w : ι → Polynomial K) (hrel : ∀ z : 𝕜, ‖z‖ < r → ∑ i, aeval z (w i) * H i z = 0) :
    ∑ i, (w i : PowerSeries K) * f i = 0 := by
  refine eq_zero_of_isSumOnBall_zero (𝕜 := 𝕜) hr ?_
  have hsum := IsSumOnBall.finsetSum (𝕜 := 𝕜) Finset.univ fun i _ => (hf i).polyMul (w i)
  intro z hz
  simpa only [hrel z hz] using hsum z hz

/-- The converse direction, and the only other place the dictionary is used: a *formal* relation
may be evaluated at any point of the disc. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem eval_of_relation_formal {ι : Type*} [Fintype ι] {r : ℝ} {f : ι → PowerSeries K}
    {H : ι → 𝕜 → 𝕜} (hf : ∀ i, IsSumOnBall r (f i) (H i)) (w : ι → Polynomial K)
    (hrel : ∑ i, (w i : PowerSeries K) * f i = 0) {z : 𝕜} (hz : ‖z‖ < r) :
    ∑ i, aeval z (w i) * H i z = 0 := by
  have hsum := IsSumOnBall.finsetSum (𝕜 := 𝕜) Finset.univ fun i _ => (hf i).polyMul (w i)
  have h1 := hsum z hz
  rw [hrel] at h1
  exact h1.unique (by simp)

end Bridge

/-! ## Substituting `z ↦ z ^ q`, and the series of the doubled solution vector -/

section Subst

variable {K 𝕜 : Type*} [Field K] [NormedField 𝕜] [Algebra K 𝕜]

/-- `f(z^q)`, on power series. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
noncomputable def substPowSeries (q : ℕ) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => if q ∣ n then PowerSeries.coeff (n / q) f else 0

@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma IsSumOnBall.substPowSeries {r : ℝ} {f : PowerSeries K} {H : 𝕜 → 𝕜} (h : IsSumOnBall r f H)
    {q : ℕ} (hq : 0 < q) (hstab : ∀ z : 𝕜, ‖z‖ < r → ‖z ^ q‖ < r) :
    IsSumOnBall r (AF.substPowSeries q f) (fun z => H (z ^ q)) := by
  intro z hz
  have hinj : Function.Injective (fun j : ℕ => q * j) :=
    mul_right_injective₀ (by omega : q ≠ 0)
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => q * j) →
      algebraMap K 𝕜 (PowerSeries.coeff n (AF.substPowSeries q f)) * z ^ n = 0 := by
    intro n hn
    have : ¬ q ∣ n := by
      rintro ⟨j, rfl⟩; exact hn ⟨j, rfl⟩
    simp [AF.substPowSeries, PowerSeries.coeff_mk, this]
  rw [← hinj.hasSum_iff hzero]
  have e : ((fun n => algebraMap K 𝕜 (PowerSeries.coeff n (AF.substPowSeries q f)) * z ^ n) ∘
      fun j : ℕ => q * j)
      = fun j => algebraMap K 𝕜 (PowerSeries.coeff j f) * (z ^ q) ^ j := by
    funext j
    simp only [Function.comp_apply, AF.substPowSeries, PowerSeries.coeff_mk, Dvd.intro j rfl,
      if_pos, Nat.mul_div_cancel_left j hq, ← pow_mul]
  rw [e]
  exact h (z ^ q) (hstab z hz)

/-- The power series of the `j`-fold doubled solution vector `AF.dblIterSol`. -/
@[category API, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
noncomputable def dblIterSer {ι : Type*} (q : ℕ) (f : ι → PowerSeries K) :
    (j : ℕ) → dblIdx ι j → PowerSeries K
  | 0 => f
  | j + 1 => Sum.elim (dblIterSer q f j) fun x => AF.substPowSeries q (dblIterSer q f j x)

@[category research solved, AMS 11 30 40, ref "AF17", group "af_mahler_alternative"]
lemma isSumOnBall_dblIterSer {ι : Type*} {r : ℝ} {f : ι → PowerSeries K} {F : ι → 𝕜 → 𝕜} {q : ℕ}
    (hq : 0 < q) (hstab : ∀ z : 𝕜, ‖z‖ < r → ‖z ^ q‖ < r) (hf : ∀ i, IsSumOnBall r (f i) (F i)) :
    ∀ (j : ℕ) (x : dblIdx ι j), IsSumOnBall r (dblIterSer q f j x) (dblIterSol q F j x)
  | 0, x => hf x
  | _ + 1, Sum.inl x => isSumOnBall_dblIterSer hq hstab hf _ x
  | _ + 1, Sum.inr x => (isSumOnBall_dblIterSer hq hstab hf _ x).substPowSeries hq hstab

end Subst

/-! ## Bookkeeping on the doubled index set -/

section Bookkeeping

variable {ι : Type*}

/-- A relation vector, extended by zero to the index set of the `j`-fold doubled system. -/
@[category API, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
def dblExt {L : Type*} [Zero L] (lam : ι → L) : (j : ℕ) → dblIdx ι j → L
  | 0 => lam
  | j + 1 => Sum.elim (dblExt lam j) 0

@[category API, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
lemma dblExt_dblEmb {L : Type*} [Zero L] (lam : ι → L) :
    ∀ (j : ℕ) (i : ι), dblExt lam j (dblEmb ι j i) = lam i
  | 0, _ => rfl
  | j + 1, i => dblExt_dblEmb lam j i

@[category API, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
lemma dblExt_eq_zero {L : Type*} [Zero L] (lam : ι → L) :
    ∀ (j : ℕ) (x : dblIdx ι j), (∀ i, x ≠ dblEmb ι j i) → dblExt lam j x = 0
  | 0, x, hx => absurd rfl (hx x)
  | j + 1, Sum.inl y, hx =>
      dblExt_eq_zero lam j y fun i hi => hx i (congrArg Sum.inl hi)
  | _ + 1, Sum.inr _, _ => rfl

/-- A sum over the doubled index set collapses to a sum over the original one as soon as the
summand vanishes off the canonical copy. -/
@[category research solved, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
lemma sum_dblIdx {M : Type*} [Fintype ι] [AddCommMonoid M] :
    ∀ (j : ℕ) (g : dblIdx ι j → M), (∀ x, (∀ i, x ≠ dblEmb ι j i) → g x = 0) →
      ∑ x, g x = ∑ i, g (dblEmb ι j i)
  | 0, _, _ => rfl
  | j + 1, g, hg => by
      have hsplit : (∑ x, g x) = (∑ y, g (Sum.inl y)) + ∑ y, g (Sum.inr y) := by
        show (∑ x : dblIdx ι j ⊕ dblIdx ι j, g x) = _
        exact Fintype.sum_sum_type g
      have hr : ∀ y, g (Sum.inr y) = 0 := fun y => hg _ fun _ h => Sum.inr_ne_inl h
      rw [hsplit, Finset.sum_congr rfl fun y _ => hr y, Finset.sum_const_zero, add_zero]
      exact sum_dblIdx j (fun y => g (Sum.inl y))
        fun y hy => hg _ fun i h => hy i (Sum.inl_injective h)

end Bookkeeping

/-! ## Transporting a system to a larger coefficient field -/

section Transport

variable {k L 𝕜 : Type*} [Field k] [Field L] [Field 𝕜] [Algebra k L] [Algebra L 𝕜] [Algebra k 𝕜]
  [IsScalarTower k L 𝕜] {ι : Type*} [Fintype ι]

@[category API, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
lemma IsMahlerSolution.mapCoeff {q : ℕ} {A : Matrix ι ι (Polynomial k)} {F : ι → 𝕜 → 𝕜}
    {S : Set 𝕜} (h : IsMahlerSolution q A F S) :
    IsMahlerSolution q (A.map (Polynomial.map (algebraMap k L))) F S := by
  intro z hz i
  rw [h z hz i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Polynomial.aeval_map_algebraMap]

@[category API, AMS 11 12 15, ref "AF17", group "af_mahler_alternative"]
lemma det_mapCoeff_ne_zero [DecidableEq ι] {A : Matrix ι ι (Polynomial k)} (hA : A.det ≠ 0) :
    (A.map (Polynomial.map (algebraMap k L))).det ≠ 0 := by
  have he : (A.map (Polynomial.map (algebraMap k L))).det
      = Polynomial.map (algebraMap k L) A.det := by
    have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap k L)) A
    simpa [RingHom.mapMatrix_apply] using h.symm
  rw [he]
  exact fun h => hA (Polynomial.map_injective _ (algebraMap k L).injective (by simpa using h))

end Transport

/-! ## Adjoining the constant function `1` -/

section AdjoinOne

variable {L : Type*} [Field L] [Algebra L ℂ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The system enlarged by the constant function `1`** ([AF17] p. 4, the matrix
`[[A(z), 0], [0, 1]]`): *«on peut toujours transformer une relation inhomogène en une relation
homogène en ajoutant au système la fonction `f_{n+1}` constante et égale à 1»*. -/
@[category API, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
noncomputable def adjoinOne (A : Matrix ι ι (Polynomial L)) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) (Polynomial L) :=
  Matrix.fromBlocks A 0 0 1

omit [Algebra L ℂ] in
/-- «et l'ensemble des points réguliers reste inchangé» — the determinant is unchanged. -/
@[category research solved, AMS 11 12 15, ref "AF17", group "af_mahler_alternative"]
lemma det_adjoinOne (A : Matrix ι ι (Polynomial L)) : (adjoinOne A).det = A.det := by
  rw [adjoinOne, Matrix.det_fromBlocks_zero₂₁]
  simp

omit [DecidableEq ι] in
@[category research solved, AMS 11 12 39, ref "AF17", group "af_mahler_alternative"]
lemma isMahlerSolution_adjoinOne {q : ℕ} {A : Matrix ι ι (Polynomial L)} {F : ι → ℂ → ℂ}
    {S : Set ℂ} (hF : IsMahlerSolution q A F S) :
    IsMahlerSolution q (adjoinOne A) (Sum.elim F fun _ _ => 1) S := by
  intro z hz i
  rw [Fintype.sum_sum_type]
  cases i with
  | inl i =>
      have h1 := hF z hz i
      simpa [adjoinOne] using h1
  | inr i => simp [adjoinOne]

end AdjoinOne

/-! ## Evaluation over a subfield -/

section Main

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Algebra L ℂ] [Algebra k ℂ]
  [IsScalarTower k L ℂ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of a polynomial over `k` at a point of `k`, read in `ℂ`. -/
@[category API, AMS 11 12, ref "AF17", group "af_mahler_alternative"]
lemma aeval_algebraMap_eq (α : k) (p : Polynomial k) :
    aeval (algebraMap k ℂ α) p = algebraMap k ℂ (p.eval α) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_apply]


end Main


end AF
