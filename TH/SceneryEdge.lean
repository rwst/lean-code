/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.NumberTheory.PisotNumber
import BertinPisot.AlphaPowMod1
import TH.Solenoid.LimitMeasures
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.RingTheory.Polynomial.RationalRoot
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A15: the set-to-point edge — the [HS15] habitat, and why `3/2` lies outside it

Angle A15 of `plans/plan-A1+.html` §5, together with its blocking gate **G3** (§3.4):

> Read [HS15]: the exact hypotheses and conclusion of its `(ξλⁿ)`, `λ = p/q` theorem (which fractal
> measures; which genericity); what the criterion demands at `ξ = 1`.

Executed here against the paper itself.  **Gate verdict: the theorem the plan assumed does not
exist.**  [HS15] covers two classes of bases — integers `n ≥ 2` (Thm 1.1, p. 3) and Pisot numbers
`β > 1` (Thm 1.2, p. 4, with the convention "integers `≥ 2` are Pisot", p. 4) — and no others; the
mod-1 conclusion the plan wanted is Corollary 1.3 (p. 4), which is Pisot-only twice over (once for
Thm 1.2, once for the Bertrand-Mathis transfer "`β` Pisot and `x` `β`-normal ⟹ `{βⁿx}` equidistributes
on the circle").  A *non-integer rational* base such as `3/2` is in neither class, and the paper says
why the Pisot hypothesis is there: it is "the main place where the Pisot property is used in the
non-integer case" — the characterization of the Parry measure by dimension growth under convolution
(p. 4), a step whose piecewise-linearity input "seems to fail … for most non-linear and many
piecewise linear maps" (p. 10).  The authors add "It is possible that the Pisot assumption is
unnecessary but currently we are unable to prove this" (p. 4).

Consequently the pre-registered failure branch of G3 fires: **the "first checkable sufficient
condition on a point" is not available from [HS15]**, and A15's edge claim is dropped.  What this
file delivers instead is the machine-checked anatomy of the failure — five parts, each a statement
the corpus can quote.

## Contents

1. **The habitat, and the exclusion of `3/2`.**  `IsHS15Base` is the disjunction of the two classes.
   `not_isIntegral_three_halves` is the whole obstruction in one line — a rational algebraic integer
   is an integer — and it kills *both* disjuncts at once (`three_halves_not_pisot`,
   `three_halves_not_isHS15Base`).  Non-vacuity: `isHS15Base_two`, `isHS15Base_goldenRatio`.
2. **The criterion is vacuous at every given point.**  Theorem 1.1 needs a **non-trivial** generated
   distribution, and [HS15] p. 3 identifies triviality exactly: a measure that generates a
   distribution generates the trivial one **iff** it gives full mass to a set of zero Hausdorff
   dimension ("this limitation is intrinsic to our methods", p. 3).  `fullMassZeroDim_dirac`: the
   Dirac at a point fails that clause.  `fullMassZeroDim_of_countable`: so does *every* measure
   carried by a countable set — in particular every empirical measure of the orbit of `ξ`, and every
   measure carried by the orbit.  The hypothesis therefore cannot be met by any measure canonically
   attached to a single point.
3. **The one surviving candidate is circular.**  The only measures attached to `ξ` that escape
   part 2 are the weak-∗ *limits* of its empirical measures — W4's `limitMeasures`.  But
   `limitMeasures_criterion_circular`: any property `Φ` of that set which is sufficient for
   equidistribution and holds at `{Haar}` is *equivalent* to equidistribution.  A criterion read off
   the orbit's own limit measures carries exactly the information of the conclusion — never less.
4. **The gap is real, not a formality — and it is total.**
   `not_isEquidistributedModuloOne_pow_of_isHS15Base`: at **every** base [HS15] covers, Pisot or
   integer, the *given* point `ξ = 1` fails, while Corollary 1.3 supplies u.d. mod 1 for `μ`-a.e.
   point at that same base.  The engine is `Bertin.not_isEquidistributedModuloOne_pow`, the corollary
   of Bertin's Theorem 5.3.1 added to `BertinPisot/AlphaPowMod1.lean` for this purpose (powers of a
   Pisot number cluster at the integers, so the band `[1/4, 1/2)` collects only finitely many
   indices); integer bases come along because `Bertin.S` contains the rational integers `> 1`, which
   is [HS15]'s own convention.  `exists_hs15Base_point_failure` names `φ` as the explicit witness.
   So an a.e. theorem of exactly the strength A15 hoped to import is true, and false at the point,
   for the whole class at once — no enlargement of the a.e. class can produce a point statement
   (`ae_avoids_point`).
5. **`3/2` fails even the weaker finiteness input, self-referentially.**  Pisot ⟹ Parry (the
   `T_β`-orbit of `1` is eventually periodic), and Parry is what gives `T_β` a finite Markov
   structure.  `not_eventuallyPeriodic_parryOrbit`: for `β = 3/2` that orbit is *injective* — its
   denominators are exactly `2ⁿ` (`parryOrbit_eq`, `odd_parryNum`) — so `3/2` is not a Parry base
   either, and the reason is the same 2-adic denominator growth that governs the whole `(3/2)ⁿ`
   problem.  Finally `three_halves_only_gamma`: in the pair `(β, γ)` of [HS15] Thm 1.10 / Cor 1.11
   (p. 8) — `β` Pisot, `γ` arbitrary, `β ≁ γ` — the number `3/2` is admissible **only in the `γ`
   slot**, i.e. as a source of invariance, never as the base whose powers equidistribute.
   `multiplicativelyIndependent_two_three_halves` checks the `≁` side elementarily.

## Scoop-watch (G3's second question)

[Shm19] and [Wu19], the two papers the plan lists as A15's ceiling technology, are about
`×p`/`×q`-invariant *sets* and self-similar measures for **integers** `p, q ≥ 2` (Furstenberg's
intersection conjecture, `L^q` dimensions); neither states anything for a non-integer rational base,
and [Wu19]'s pointwise companion (its Conjecture 1.2, `dimH O_p(x) + dimH O_q(x) ≥ 1`) is both open
and stated only for irrational `x`, so it does not reach `ξ = 1` even in principle.

## References

* [HS15] M. Hochman & P. Shmerkin, "Equidistribution from fractal measures," *Invent. Math.* **202**
  (2015), 427–479 (arXiv:1302.5792v3).  **G3 locators:** scaling flow, scenery and "generates a
  distribution" pp. 2–3; triviality ⟺ full mass on a zero-dimensional set, and the intrinsic
  limitation, p. 3; Thm 1.1 p. 3; Pisot definition and convention, Thm 1.2, Cor 1.3 and the
  "main place where the Pisot property is used", p. 4; Thm 1.9 (Host) and Thm 1.10 / Cor 1.11 p. 8;
  the open Pisot-elimination remark p. 9; the piecewise-linearity remark p. 10; Thm 2.1 (orbits ↔
  measure, `μ`-a.e.) p. 11.
* [Shm19] P. Shmerkin, *Ann. of Math.* **189** (2019), 319–391; [Wu19] M. Wu, *Ann. of Math.* **189**
  (2019), 707–751.
* Plan A1+ §3.4 (gate G3), §5 (A15), §9 trigger (f).  Part 3 consumes W4
  (`TH/Solenoid/LimitMeasures.lean`); part 4 consumes the Bertin estate through
  `Bertin.not_isEquidistributedModuloOne_pow` and `Bertin.mem_S_iff_isPisot`, the two lemmas this
  work package added to `BertinPisot/{AlphaPowMod1,SetSTU}.lean` — the latter being the bridge that
  makes `ForMathlib/NumberTheory/PisotNumber.lean` (previously unconsumed) the same predicate as
  Bertin's Definition 5.2.1.
-/

namespace TH

open Filter MeasureTheory Set
open scoped Topology goldenRatio

/-! ### 1. The habitat: which bases [HS15] actually covers -/

/-- The bases for which [HS15] has a pointwise-normality theorem: the Pisot numbers (Thm 1.2) and
the integers `n ≥ 2` (Thm 1.1).  The paper's own convention makes the second class part of the
first ("we adopt the convention that integers `≥ 2` are Pisot numbers", p. 4); both are listed here
so that the exclusion below does not depend on that convention. -/
@[category API, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
def IsHS15Base (β : ℝ) : Prop := IsPisot β ∨ ∃ n : ℕ, 2 ≤ n ∧ β = (n : ℝ)

/-- Non-vacuity, integer side. -/
@[category test, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem isHS15Base_two : IsHS15Base 2 := Or.inr ⟨2, le_rfl, by norm_num⟩

/-- Non-vacuity, Pisot side: the golden ratio is a base [HS15] covers.  This is the first consumer
of `ForMathlib/NumberTheory/PisotNumber.lean`. -/
@[category test, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem isHS15Base_goldenRatio : IsHS15Base φ := Or.inl isPisot_goldenRatio

/-- **The obstruction, in one line.**  `3/2` is not an algebraic integer: a rational integral over
`ℤ` lies in `ℤ`, and `3/2` does not.  Everything in part 1 follows from this. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem not_isIntegral_three_halves : ¬ IsIntegral ℤ ((3 : ℝ) / 2) := by
  intro h
  have hcast : ((3 : ℝ) / 2) = algebraMap ℚ ℝ ((3 : ℚ) / 2) := by
    rw [eq_ratCast (algebraMap ℚ ℝ) ((3 : ℚ) / 2)]; norm_num
  rw [hcast] at h
  have hQ : IsIntegral ℤ ((3 : ℚ) / 2) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective).mp h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hQ
  have hz' : (z : ℚ) = 3 / 2 := by simpa using hz
  have h2 : (2 * z : ℤ) = 3 := by
    have : ((2 * z : ℤ) : ℚ) = ((3 : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-- `3/2` is not a Pisot number — it fails the algebraic-integer clause of `IsPisot`.  So [HS15]
Thm 1.2 and Cor 1.3, the mod-1 statement A15 wanted to import, do not apply to it. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem three_halves_not_pisot : ¬ IsPisot ((3 : ℝ) / 2) := fun h =>
  not_isIntegral_three_halves h.2.1

/-- `3/2` is not an integer base either. -/
@[category API, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem three_halves_ne_natCast (n : ℕ) : ((3 : ℝ) / 2) ≠ (n : ℝ) := by
  intro h
  have h3 : (3 : ℝ) = 2 * n := by linarith [h]
  have : (3 : ℕ) = 2 * n := by exact_mod_cast h3
  omega

/-- **G3, machine-checked.**  `3/2` lies in neither hypothesis class of [HS15]. -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
theorem three_halves_not_isHS15Base : ¬ IsHS15Base ((3 : ℝ) / 2) := by
  rintro (h | ⟨n, -, hn⟩)
  · exact three_halves_not_pisot h
  · exact three_halves_ne_natCast n hn

/-! ### 2. The criterion is vacuous at every given point

[HS15] Thm 1.1 assumes that `μ` generates a **non-trivial** `S`-ergodic distribution, and p. 3
records exactly when triviality happens: a measure generating a distribution generates the trivial
one iff it gives full mass to a set of zero Hausdorff dimension.  `FullMassZeroDim` is that clause;
the two lemmas below say it is satisfied by every measure a single point can produce. -/

/-- "`μ` gives full mass to a set of zero Hausdorff dimension" ([HS15] p. 3): the negation of the
non-triviality hypothesis of Theorem 1.1. -/
@[category API, AMS 11 28, ref "HS15", group "weyl_a15_scenery"]
def FullMassZeroDim (μ : Measure ℝ) : Prop := ∃ A : Set ℝ, dimH A = 0 ∧ μ Aᶜ = 0

/-- Any measure carried by a countable set fails [HS15]'s non-triviality clause.  This covers every
**empirical** measure of an orbit and every measure carried by the orbit `{ξ, (3/2)ξ, (3/2)²ξ, …}`:
the criterion has nothing to say about any of them. -/
@[category research solved, AMS 11 28, ref "HS15", group "weyl_a15_scenery"]
theorem fullMassZeroDim_of_countable {μ : Measure ℝ} {S : Set ℝ} (hS : S.Countable)
    (h : μ Sᶜ = 0) : FullMassZeroDim μ :=
  ⟨S, dimH_countable hS, h⟩

/-- The Dirac mass at a point fails the non-triviality clause — the sharpest form of the paper's own
remark that "the theorem does not apply to measures supported on zero-dimensional sets.  This
limitation is intrinsic to our methods" (p. 3). -/
@[category research solved, AMS 11 28, ref "HS15", group "weyl_a15_scenery"]
theorem fullMassZeroDim_dirac (ξ : ℝ) : FullMassZeroDim (Measure.dirac ξ) :=
  ⟨{ξ}, dimH_singleton ξ, by
    rw [Measure.dirac_apply' _ (measurableSet_singleton ξ).compl]
    simp⟩

/-- The orbit form of the same statement: every measure carried by the (countable) forward orbit of
a point is zero-dimensional, hence outside the criterion's reach.  Only weak-∗ *limits* of such
measures can escape — which is part 3. -/
@[category research solved, AMS 11 28, ref "HS15", group "weyl_a15_scenery"]
theorem fullMassZeroDim_of_orbit (x : ℕ → ℝ) {μ : Measure ℝ} (h : μ (Set.range x)ᶜ = 0) :
    FullMassZeroDim μ :=
  fullMassZeroDim_of_countable (Set.countable_range x) h

/-! ### 3. The surviving candidate is circular -/

open S6 in
/-- **Any criterion read off the orbit's own limit measures is equivalent to its conclusion.**  Let
`Φ` be a property of sets of probability measures on `Σ₆` which holds at `{Haar}` and which, applied
to `limitMeasures ζ`, implies equidistribution of the orbit of `ζ`.  Then `Φ (limitMeasures ξ)` is
*equivalent* to equidistribution, for every `ξ`: the "check" carries exactly the information of the
conclusion.  This is W4's `equidistributed_iff_limitMeasures` used as an audit — the second
canonical measure attached to a point (after the Diracs of part 2) yields no independent test. -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
theorem limitMeasures_criterion_circular {Φ : Set (ProbabilityMeasure S6) → Prop}
    (hHaar : Φ {haarProb}) (hsuff : ∀ ζ : ℝ, Φ (limitMeasures ζ) → Equidistributed ζ) (ξ : ℝ) :
    Φ (limitMeasures ξ) ↔ Equidistributed ξ :=
  ⟨hsuff ξ, fun h => by rw [(equidistributed_iff_limitMeasures ξ).mp h]; exact hHaar⟩

/-! ### 4. The set-to-point gap, with a witness in [HS15]'s own class -/

/-- No `μ`-a.e. statement constrains a point of `μ`-measure zero: the full-measure set can always be
taken to avoid it.  Trivial, and it is the whole content of the "missing set-to-point edge". -/
@[category research solved, AMS 11 28, ref "A1plus", group "weyl_a15_scenery"]
theorem ae_avoids_point {μ : Measure ℝ} {ξ : ℝ} (h : μ {ξ} = 0) :
    ∃ A : Set ℝ, μ Aᶜ = 0 ∧ ξ ∉ A :=
  ⟨{ξ}ᶜ, by simpa using h, by simp⟩

/-- **The gap, at every base [HS15] covers.**  For a Pisot base this is
`Bertin.not_isEquidistributedModuloOne_pow` (the corollary of Bertin's Theorem 5.3.1 proved in
`BertinPisot/AlphaPowMod1.lean`: `distToNearestInt (βⁿ) → 0`, so the band `[1/4, 1/2)` receives only
finitely many indices); for an integer base `n ≥ 2` it is the same statement, since `Bertin.S`
contains the rational integers `> 1` (`Bertin.intCast_mem_S`) — which is exactly [HS15]'s own
convention that integers `≥ 2` count as Pisot.  So the given point `ξ = 1` fails for **every** base
the paper covers, while Cor. 1.3 supplies u.d. for `μ`-a.e. point at each of them. -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15" "Ber92", group "weyl_a15_scenery"]
theorem not_isEquidistributedModuloOne_pow_of_isHS15Base {β : ℝ} (hβ : IsHS15Base β) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => β ^ n) := by
  refine Bertin.not_isEquidistributedModuloOne_pow β ?_
  rcases hβ with h | ⟨n, hn, rfl⟩
  · exact (Bertin.mem_S_iff_isPisot β).mpr h
  · have hcast : ((n : ℕ) : ℝ) = (((n : ℤ)) : ℝ) := by push_cast; ring
    rw [hcast]
    exact Bertin.intCast_mem_S (n : ℤ) (by exact_mod_cast lt_of_lt_of_le one_lt_two hn)

/-- **The witness.**  The given point `ξ = 1` at the Pisot base `φ`: `(φⁿ)` is *not* u.d. mod 1,
because `‖φⁿ‖ → 0` — the powers cluster at the integers instead of spreading out.  [HS15] Cor. 1.3
supplies u.d. for `μ`-a.e. point at this same base, so the a.e. theorem and the failure at a given
point coexist. -/
@[category research solved, AMS 11 37, ref "HS15" "Ber92", group "weyl_a15_scenery"]
theorem not_isEquidistributedModuloOne_goldenRatio_pow :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => φ ^ n) :=
  not_isEquidistributedModuloOne_pow_of_isHS15Base isHS15Base_goldenRatio

/-- The same statement in Bertin's centered convention. -/
@[category research solved, AMS 11 37, ref "HS15" "Ber92", group "weyl_a15_scenery"]
theorem not_uniformlyDistributedModOne_goldenRatio_pow :
    ¬ Bertin.UniformlyDistributedModOne (fun n : ℕ => φ ^ n) :=
  Bertin.not_uniformlyDistributedModOne_pow φ Bertin.goldenRatio_mem_S

/-- **The set-to-point gap, in the form the audit needs.**  Every base [HS15] covers — Pisot or
integer — carries its a.e. conclusion (Cor. 1.3) *and* fails at the given point `ξ = 1`.  Hence no
enlargement of the a.e. class, which is all [HS15] provides, can be converted into a statement about
a specified point.  The existential form names `φ` as an explicit witness. -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
theorem exists_hs15Base_point_failure :
    ∃ β : ℝ, IsPisot β ∧ IsHS15Base β ∧
      ¬ IsEquidistributedModuloOne (fun n : ℕ => 1 * β ^ n) :=
  ⟨φ, isPisot_goldenRatio, isHS15Base_goldenRatio, by
    simpa using not_isEquidistributedModuloOne_goldenRatio_pow⟩

/-! ### 5. `3/2` fails the weaker finiteness input too, and only fits the `γ` slot

A Pisot base is in particular a **Parry** base: the `T_β`-orbit of `1` is eventually periodic, which
is what gives `x ↦ βx mod 1` a finite Markov structure.  For `β = 3/2` that orbit is computed here
in exact rational arithmetic and shown to be *injective*: its denominators are exactly the powers of
`2`.  So the failure is not a near miss at the Pisot boundary — `3/2` is outside the strictly larger
Parry class as well, for the same 2-adic reason that drives the `(3/2)ⁿ` problem itself. -/

/-- The `T_β`-orbit of `1` for `β = 3/2`, in exact rational arithmetic:
`x₀ = 1`, `x_{n+1} = {(3/2)·xₙ}`.  Eventual periodicity of this orbit is the definition of a Parry
(β-)number. -/
@[category API, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
def parryOrbit : ℕ → ℚ
  | 0 => 1
  | n + 1 => Int.fract (3 / 2 * parryOrbit n)

/-- The numerators of `parryOrbit` over the denominator `2ⁿ`. -/
@[category API, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
def parryNum : ℕ → ℕ
  | 0 => 1
  | n + 1 => (3 * parryNum n) % 2 ^ (n + 1)

/-- Every numerator is odd: `3·(odd)` is odd, and reducing mod a power of `2` preserves parity. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem odd_parryNum : ∀ n : ℕ, Odd (parryNum n)
  | 0 => by simp [parryNum]
  | n + 1 => by
    have h := odd_parryNum n
    rw [Nat.odd_iff] at h ⊢
    rw [show parryNum (n + 1) = (3 * parryNum n) % 2 ^ (n + 1) from rfl,
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero n))]
    omega

/-- The orbit in closed form: `xₙ = cₙ / 2ⁿ`. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem parryOrbit_eq : ∀ n : ℕ, parryOrbit n = (parryNum n : ℚ) / 2 ^ n
  | 0 => by simp [parryOrbit, parryNum]
  | n + 1 => by
    rw [show parryOrbit (n + 1) = Int.fract (3 / 2 * parryOrbit n) from rfl, parryOrbit_eq n]
    have hstep : (3 : ℚ) / 2 * ((parryNum n : ℚ) / 2 ^ n)
        = ((3 * parryNum n : ℕ) : ℚ) / ((2 ^ (n + 1) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [hstep, Int.fract_div_natCast_eq_div_natCast_mod,
      show parryNum (n + 1) = (3 * parryNum n) % 2 ^ (n + 1) from rfl]
    push_cast
    ring

/-- Distinct indices give distinct orbit points: the denominator `2ⁿ` is never cancelled, because
the numerator stays odd. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem parryOrbit_ne_of_lt {m n : ℕ} (h : m < n) : parryOrbit m ≠ parryOrbit n := by
  intro heq
  rw [parryOrbit_eq m, parryOrbit_eq n] at heq
  have h2m : (0 : ℚ) < 2 ^ m := by positivity
  have h2n : (0 : ℚ) < 2 ^ n := by positivity
  have hQ : (parryNum m : ℚ) * 2 ^ n = (parryNum n : ℚ) * 2 ^ m := by
    field_simp at heq
    linarith [heq]
  have hN : parryNum m * 2 ^ n = parryNum n * 2 ^ m := by exact_mod_cast hQ
  obtain ⟨k, hk⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  subst hk
  have hsplit : parryNum m * 2 ^ (k + 1) * 2 ^ m = parryNum (m + (k + 1)) * 2 ^ m := by
    rw [← hN, pow_add]; ring
  have hcancel : parryNum m * 2 ^ (k + 1) = parryNum (m + (k + 1)) :=
    Nat.eq_of_mul_eq_mul_right (by positivity) hsplit
  have hodd := odd_parryNum (m + (k + 1))
  rw [← hcancel, Nat.odd_iff] at hodd
  have : (parryNum m * 2 ^ (k + 1)) % 2 = 0 := by
    have : 2 ∣ parryNum m * 2 ^ (k + 1) :=
      Dvd.dvd.mul_left (dvd_pow_self 2 (Nat.succ_ne_zero k)) _
    omega
  omega

/-- **`3/2` is not a Parry base.**  The `T_{3/2}`-orbit of `1` is injective, hence not eventually
periodic — so the finite Markov structure that the Pisot hypothesis of [HS15] Thm 1.2 supplies is
unavailable at `3/2` for a reason of the problem's own kind (2-adic denominator growth). -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
theorem not_eventuallyPeriodic_parryOrbit :
    ¬ ∃ n₀ p : ℕ, 0 < p ∧ ∀ n, n₀ ≤ n → parryOrbit (n + p) = parryOrbit n := by
  rintro ⟨n₀, p, hp, h⟩
  exact parryOrbit_ne_of_lt (show n₀ < n₀ + p by omega) (h n₀ le_rfl).symm

/-- Multiplicative independence in the elementary form: `a` and `b` share no common integer power.
For `a, b > 1` this is [HS15]'s `a ≁ b` (`log a / log b ∉ ℚ`, p. 6). -/
@[category API, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
def MultiplicativelyIndependent (a b : ℝ) : Prop := ∀ p q : ℕ, a ^ p = b ^ q → p = 0 ∧ q = 0

/-- `2 ≁ 3/2`: a common power would give `2^{p+q} = 3^q`. -/
@[category research solved, AMS 11 37, ref "HS15", group "weyl_a15_scenery"]
theorem multiplicativelyIndependent_two_three_halves :
    MultiplicativelyIndependent 2 ((3 : ℝ) / 2) := by
  intro p q h
  have h1 : (2 : ℝ) ^ (p + q) = 3 ^ q := by
    rw [pow_add, h, div_pow]
    field_simp
  have h2 : (2 : ℕ) ^ (p + q) = 3 ^ q := by exact_mod_cast h1
  have hq : q = 0 := by
    by_contra hq
    have h3 : (3 : ℕ) ∣ 2 ^ (p + q) := h2 ▸ dvd_pow_self 3 hq
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  subst hq
  refine ⟨?_, rfl⟩
  by_contra hp
  have hone : (2 : ℕ) ^ p = 1 := by simpa using h2
  have : 1 < (2 : ℕ) ^ p := Nat.one_lt_two_pow_iff.mpr hp
  omega

/-- **The wrong-side statement.**  In the pair `(β, γ)` of [HS15] Thm 1.10 / Cor 1.11 (p. 8) — `β`
Pisot, `γ > 1` arbitrary, `β ≁ γ` — the number `3/2` is admissible only as `γ`, the base supplying
*invariance*, never as `β`, the base whose powers equidistribute.  Taking `β = 2` shows the pair
`(2, 3/2)` does satisfy the independence requirement, so the exclusion is about the Pisot slot
alone. -/
@[category research solved, AMS 11 37, ref "A1plus" "HS15", group "weyl_a15_scenery"]
theorem three_halves_only_gamma :
    MultiplicativelyIndependent 2 ((3 : ℝ) / 2) ∧ IsHS15Base 2 ∧ ¬ IsHS15Base ((3 : ℝ) / 2) :=
  ⟨multiplicativelyIndependent_two_three_halves, isHS15Base_two, three_halves_not_isHS15Base⟩

end TH
