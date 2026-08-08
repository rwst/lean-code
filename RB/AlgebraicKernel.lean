/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
-- `CITED.CorvajaZannierAlgebraic` is no longer *used* here (the slices moved to
-- `Subspace.schmidt1D'` on 2026-08-07); the import is kept so that the cited transcription
-- stays inside a loaded module and is still extracted by the corpus tooling.
import CITED.CorvajaZannierAlgebraic
import RB.OnePowerRational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The algebraic-multiplier kernel — the CZ half ([report2] S13, first milestone)

Referee strategy **S13** asks to extend the Diophantine kernel
(`RB.scaledViolators_finite`) from rational multipliers `δ` to **algebraic** ones, so
that Theorem A upgrades from "`K` algebraic ⇒ `w` not automatic" to "`K` algebraic ⇒
superlinear complexity".  This file executes the half of that program that is within
reach of the *printed* literature, and reduces the rest to a single named obligation.

## What changes for algebraic `δ` — and what does not

`RB.algViolators δ θ` is `RB.scaledViolators` with `δ : ℝ` and the `ℝ`-valued
`distToNearestInt`.  Three structural facts, against `RB/ScaledKernel.lean`'s ledger:

1. **The degeneracy box disappears.**  For *irrational* `δ` the value
   `δ·((3/2)^c − (3/2)^a)` — an irrational times a nonzero rational — is never an
   integer, so `‖·‖ > 0` holds for **every** pair (`RB.algDist_pos_of_irrational`);
   no `c < |δ.num|` box, no parity argument.  The referee's expected "first casualty"
   is in fact a simplification: multiplying by an algebraic *irrational* cannot cancel
   the `2`-power, only a rational can.
2. **The bounded-gap slices survive verbatim**, and since 2026-08-07 they are *derived*
   rather than cited: a fixed-gap slice is the homogeneous one-power problem
   `‖δ'(3/2)^a‖ ≤ θ^a` for the algebraic irrational multiplier `δ' = δ((3/2)^{s₀} − 1)`,
   which `RB.onePower_finite_of_irrational` (`RB/OnePowerRational.lean`) settles at every
   scale from `Subspace.schmidt1D'`.  The route through [CZ04]'s Main Theorem for
   algebraic multipliers (`CZ.pseudoPisot_approx_alg`, itself no longer an axiom) — with
   its size proviso and its pseudo-Pisot conjugate discharge
   `CZ.not_isPseudoPisot_mul_ratCast` — is **retired** here:
   the data of a slice is rational (`q = 1`, `u = (3/2)^a`) with only the multiplier
   algebraic, which is Schmidt's 1D′ configuration and needs none of that bookkeeping.
3. **The unbounded-gap branch is the open half.**  The rational case used the repaired
   [NKR25] pair theorem, *derived* from the Subspace Theorem over `ℚ`.  For algebraic
   coefficients no refereed source exists ([NKR25] is an unrefereed preprint whose
   Theorem 1.3(i) is false as printed — `NKR.thm13i_unrepaired_false` — so nothing can
   be cited), and the derivation must run over the number field `ℚ(δ)`: places above
   `2, 3, ∞`, relative heights, `S`-enlargement — the months-scale program [report2]
   S13 budgets.  This file **names that obligation** (the `hpair` hypothesis: families
   of violators with pairwise-distinct gaps are finite) and proves everything up to it:

   * `RB.algViolators_finite_of_pairBranch` — pair branch ⇒ the full algebraic kernel;
   * `RB.superlinear_of_algKernel` — algebraic kernel ⇒ superlinear complexity
     (the Stage-1 reduction, re-run on `ℝ`-distances: pigeonhole, Bernoulli scale,
     growth ceiling — none of it needed `δ ∈ ℚ`);
   * **`RB.superlinear_of_K_algebraic_of_pairBranch`** — the S13 payoff, conditional
     on the pair branch only: *`K` algebraic ⇒ `p_w(m)/m → ∞`*, with the rational
     case discharged by the existing full kernel (T1a).

## The unconditional milestone

What the CZ half alone already buys, with **no** open hypothesis:

* **`RB.closeRepetitions_finite_of_K_algebraic`** — if `K(x₀)` is algebraic, then for
  every gap bound `S` and slope `1/L`, only finitely many repetitions `(a, c)` have
  gap `c − a ≤ S` and window length `> c/L` — long repeats at bounded distance die
  out.  Strictly stronger than `RB.not_eventually_periodic` (which is unconditional
  but only excludes one *infinite* tail): here every *family* of period-`≤ S`
  stretches of length proportional to position is finite.  Nonvacuous for `L ≥ 2`:
  the repetition ceiling (`RB.repetition_linear_bound`, slope `0.585`) caps windows
  at `0.585·c`, so slope-`1/2` windows are the widest interesting ones; at `L = 1`
  the ceiling already empties the set.
* **`RB.transcendental_of_closeRepetitions_infinite`** — the transcendence criterion:
  infinitely many such repetitions for a single `(S, L)` force `K(x₀)` transcendental.
  A second, structurally different criterion next to `RB.transcendental_of_automatic`
  (automaticity there, periodicity-adjacent repetition structure here).
* `RB.closeRepetitions_finite_or_K_transcendental` — the honest dichotomy headline.

**Honest scope**: `K` is expected transcendental, so the algebraic hypotheses are
plausibly vacuous and the criteria's triggers (automaticity; infinite close
repetitions) are expected to fail for `w` — the empirical full-complexity data
([report2] S24: all `2^m` residues occupied) leaves no room for close repetitions.
As with T1b, the value is the *criterion* direction, not the classification.

## Axiom lanes

* `algBoundedGap_slice_finite`, `algGapBounded_slice_finite`, and everything
  `Irrational`-cased through them: std3 + **`Subspace.schmidt1D'`** ([S] LNM 1467,
  Thm 1D′), via `RB.onePower_finite_of_irrational`.  Until 2026-08-07 this was a
  separate lane on `CZ.pseudoPisot_approx_alg`; that statement is now itself a **theorem**
  on `std3 + Subspace.schmidt1D'` (`CITED/CorvajaZannierProof.lean`, 2026-08-07), so the
  lane is gone in both senses — no consumer, and no axiom.
* the capstones (`closeRepetitions_finite_of_K_algebraic`, …) combine it with
  `Subspace.evertseSchlickewei` (for the rational-`K` case via
  `RB.scaledViolators_finite`).  All M0–M5 footprints of [B1E2] are unchanged.
* `RB.algViolators_ratCast`, `RB.algDist_pos_of_irrational`: std3 only.

Verified by `#print axioms` (see [report2] S13).

## Contents

* `RB.algViolators`, `RB.algDist_pos_of_irrational`, `RB.algViolators_ratCast`.
* `RB.algBoundedGap_slice_finite`, `RB.algGapBounded_slice_finite` — the CZ half,
  derived from `RB/OnePowerRational.lean`.
* `RB.algViolators_finite_of_ratCast` — the rational instance, from the old kernel.
* `RB.algViolators_finite_of_pairBranch` — dichotomy assembly, residual named.
* `RB.superlinear_of_algKernel`, **`RB.superlinear_of_K_algebraic_of_pairBranch`**.
* `RB.closeRepetitions`, **`RB.closeRepetitions_finite_of_K_algebraic`**,
  **`RB.transcendental_of_closeRepetitions_infinite`**,
  `RB.closeRepetitions_finite_or_K_transcendental`.

## References

* [S] W. M. Schmidt, LNM **1467**, Chapter V, Theorem 1D′ — the engine of the slices
  since 2026-08-07 (`CITED/SchmidtSubspace.lean`, consumed via
  `RB/OnePowerRational.lean`).
* [CZ04] Corvaja, Zannier. Acta Math. **193** (2004), 175–191 (Main Theorem, p. 2 —
  the algebraic-`δ` form, cited in `CITED/CorvajaZannierAlgebraic.lean`; the route this
  file no longer takes).
* [NKR25] Nair, Kumar, Rout. arXiv:2506.02898 (v3) — *statement template only*; see
  `CITED/NairKumarRout.lean` for the refutation of its Theorem 1.3(i).
* [B1E2] `plans/plan-B1E2.html`; [B2A2] `plans/plan-B2A2.html` (§2.2 multiplier gate).
* [report2] `plans/report2-B1E2.html`, **S13** (this file), S14, S24.
-/

namespace RB

open ForMathlib.SubwordComplexity IntermediateField

/-! ## The algebraic-multiplier violator set -/

/-- The **`δ`-scaled (K)-violating pairs** at scale `θ`, for a *real* multiplier:
`2 ≤ a < c` with `‖δ·((3/2)^c − (3/2)^a)‖ ≤ θ^c`, the distance now taken in `ℝ`
(`distToNearestInt`).  For `δ ∈ ℚ` this is `RB.scaledViolators`
(`RB.algViolators_ratCast`); the intended instances are algebraic `δ`, in particular
`δ = K(x₀)`. -/
@[category API, AMS 11, ref "CZ04" "B1E2", group "rb_rational_base"]
def algViolators (δ : ℝ) (θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    distToNearestInt (δ * ((3 / 2 : ℝ) ^ p.2 - (3 / 2 : ℝ) ^ p.1)) ≤ (θ : ℝ) ^ p.2}

private lemma orbit_diff_ratCast (a c : ℕ) :
    (3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a
      = (((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a : ℚ) : ℝ) := by
  push_cast
  ring

private lemma orbit_diff_pos {a c : ℕ} (hac : a < c) :
    (0 : ℚ) < (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a :=
  sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) hac)

/-- **No degeneracy for irrational multipliers**: `δ·((3/2)^c − (3/2)^a)` is an
irrational times a nonzero rational, hence never an integer — `‖·‖ > 0` for *every*
pair `a < c`.  Contrast `RB.dist_pos_of_num_le`: a rational `δ` can cancel the
`2`-power inside a bounded box; an irrational one never can. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem algDist_pos_of_irrational {δ : ℝ} (hirr : Irrational δ) {a c : ℕ} (hac : a < c) :
    0 < distToNearestInt (δ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a)) := by
  apply distToNearestInt_pos_of_irrational
  rw [orbit_diff_ratCast]
  exact hirr.mul_ratCast (orbit_diff_pos hac).ne'

/-- For a rational multiplier the two violator sets coincide — the `ℝ`-valued and
`ℚ`-valued distances agree on rationals (`distToNearestInt_ratCast`).  So
`algViolators` is a conservative extension of `RB.scaledViolators`. -/
@[category API, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem algViolators_ratCast (δ θ : ℚ) :
    algViolators (δ : ℝ) θ = scaledViolators δ θ := by
  ext p
  simp only [algViolators, scaledViolators, Set.mem_setOf_eq]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [orbit_diff_ratCast, show ((δ : ℚ) : ℝ) * (((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1 : ℚ) : ℝ)
      = ((δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℚ) : ℝ) from by push_cast; ring,
    distToNearestInt_ratCast, show ((θ : ℚ) : ℝ) ^ p.2 = ((θ ^ p.2 : ℚ) : ℝ) from by
      push_cast; ring]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- The rational instance of the algebraic kernel, inherited from
`RB.scaledViolators_finite`: for `δ ∈ ℚ*` the full `ℝ`-valued violator set is finite.
Footprint std3 + `Subspace.evertseSchlickewei`.  The `hpair` obligation of
`algViolators_finite_of_pairBranch` is exactly the extension of this statement to
algebraic irrational `δ`. -/
@[category research solved, AMS 11, ref "CZ04" "NKR25" "B1E2", group "rb_rational_base"]
theorem algViolators_finite_of_ratCast (δ : ℚ) (hδ : δ ≠ 0) (θ : ℚ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : (algViolators (δ : ℝ) θ).Finite := by
  rw [algViolators_ratCast]
  exact scaledViolators_finite δ hδ θ hθ0 hθ1

/-! ## `ℝ`-side helpers

The `ε = log θ⁻¹/(2 log 3)` machinery that used to live here (`log_inv_pos`,
`pow_lt_rpow_neg`) and the `S`-unit rewriting `two_zpow_neg_mul_three_zpow` were the glue
between the slice statement and [CZ04]'s `H(u)^{-ε}q^{-1-ε}` threshold.  Both went away with
the route change of 2026-08-07: `RB.onePower_finite_of_irrational` is stated directly at the
geometric scale `θ^a`, so no threshold translation is needed. -/

private lemma ratCast_isAlgebraic (q : ℚ) : IsAlgebraic ℚ ((q : ℚ) : ℝ) := by
  rw [show ((q : ℚ) : ℝ) = algebraMap ℚ ℝ q from (eq_ratCast (algebraMap ℚ ℝ) q).symm]
  exact isAlgebraic_algebraMap q

/-! ## The CZ bounded-gap slices, for algebraic irrational `δ` -/

/-- **The fixed-gap slice, algebraic multiplier** ([report2] S13; mirroring
`RB.boundedGap_slice_finite`): for algebraic irrational `δ` and every fixed gap
`s₀ ≥ 1`, only finitely many `a` satisfy `‖δ((3/2)^{a+s₀} − (3/2)^a)‖ ≤ θ^{a+s₀}`.

Data: the slice multiplier `δ' = δ·((3/2)^{s₀} − 1)` is again algebraic irrational, and the
slice quantity factors as `δ((3/2)^{a+s₀} − (3/2)^a) = δ'(3/2)^a` — the **homogeneous**
one-power problem.  `RB.onePower_finite_of_irrational` (`RB/OnePowerRational.lean`) kills it at
every scale `θ < 1`, and `θ^{a+s₀} ≤ θ^a` puts the slice inside its solution set.

**Route change, 2026-08-07.**  This proof used to run through what was then the cited axiom
`CZ.pseudoPisot_approx_alg` ([CZ04]'s Main Theorem for algebraic multipliers), which forced
three discarded initial segments — the size proviso `1 < |δ'(3/2)^a|`, the pseudo-Pisot
conjugate discharge `CZ.not_isPseudoPisot_mul_ratCast`, and the `q`-tax bookkeeping.  None of
that is needed: the data here is *rational* (`q = 1`, `u = (3/2)^a`) with only the multiplier
algebraic, which is Schmidt's Theorem 1D′ configuration, not [CZ04]'s.  (The Main Theorem in
that specialization is itself now derived from 1D′ — `CITED/CorvajaZannierProof.lean` — so
both routes rest on the same axiom; this one is simply shorter.)

Ineffective; footprint std3 + `Subspace.schmidt1D'` ([S] LNM 1467, Thm 1D′). -/
@[category research solved, AMS 11, ref "S" "CZ04" "B1E2", group "rb_rational_base"]
theorem algBoundedGap_slice_finite (δ : ℝ) (halg : IsAlgebraic ℚ δ)
    (hirr : Irrational δ) (s₀ : ℕ) (hs₀ : 1 ≤ s₀) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {a : ℕ | 2 ≤ a ∧
      distToNearestInt (δ * ((3 / 2 : ℝ) ^ (a + s₀) - (3 / 2 : ℝ) ^ a))
        ≤ (θ : ℝ) ^ (a + s₀)}.Finite := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hfacq : (0 : ℚ) < (3 / 2 : ℚ) ^ s₀ - 1 := by
    have h1 : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2 : ℚ) ^ s₀ := pow_le_pow_right₀ (by norm_num) hs₀
    rw [pow_one] at h1
    linarith
  set δ' : ℝ := δ * (((3 / 2 : ℚ) ^ s₀ - 1 : ℚ) : ℝ) with hδ'def
  have hirr' : Irrational δ' := hirr.mul_ratCast hfacq.ne'
  have halg' : IsAlgebraic ℚ δ' := halg.mul (ratCast_isAlgebraic _)
  haveI : NumberField ℚ⟮δ'⟯ := adjoin_real_numberField halg'
  refine Set.Finite.subset (onePower_finite_of_irrational δ' hirr' hθ0 hθ1) ?_
  rintro a ⟨-, hdist⟩
  have hval : δ * ((3 / 2 : ℝ) ^ (a + s₀) - (3 / 2 : ℝ) ^ a) = δ' * (3 / 2 : ℝ) ^ a := by
    rw [hδ'def]
    push_cast
    rw [pow_add]
    ring
  rw [Set.mem_setOf_eq, ← hval]
  calc distToNearestInt (δ * ((3 / 2 : ℝ) ^ (a + s₀) - (3 / 2 : ℝ) ^ a))
      ≤ (θ : ℝ) ^ (a + s₀) := hdist
    _ ≤ (θ : ℝ) ^ a := pow_le_pow_of_le_one hθ0'.le hθ1'.le (Nat.le_add_right a s₀)

/-- The **gap-bounded slice** for algebraic irrational `δ`: violators of gap `≤ S` are
finite in number — the union of the fixed-gap slices.  Mirrors
`RB.gapBounded_slice_finite`. -/
@[category research solved, AMS 11, ref "CZ04" "B1E2", group "rb_rational_base"]
theorem algGapBounded_slice_finite (δ : ℝ) (halg : IsAlgebraic ℚ δ)
    (hirr : Irrational δ) (S : ℕ) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {p ∈ algViolators δ θ | p.2 ≤ p.1 + S}.Finite := by
  have hsub : {p ∈ algViolators δ θ | p.2 ≤ p.1 + S} ⊆
      ⋃ s₀ ∈ Finset.Icc 1 S, (fun a => (a, a + s₀)) ''
        {a : ℕ | 2 ≤ a ∧
          distToNearestInt (δ * ((3 / 2 : ℝ) ^ (a + s₀) - (3 / 2 : ℝ) ^ a))
            ≤ (θ : ℝ) ^ (a + s₀)} := by
    rintro ⟨a, c⟩ ⟨⟨ha, hac, hdist⟩, hgap⟩
    have hs₀ : c - a ∈ Finset.Icc 1 S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Set.mem_biUnion hs₀ ⟨a, ⟨ha, ?_⟩, ?_⟩
    · rw [show a + (c - a) = c by omega]
      exact hdist
    · simp only [Prod.mk.injEq, true_and]
      omega
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun s₀ hs₀ => ?_
  exact Set.Finite.image _
    (algBoundedGap_slice_finite δ halg hirr s₀ (Finset.mem_Icc.mp hs₀).1 θ hθ0 hθ1)

/-! ## The dichotomy assembly — the residual obligation named -/

/-- **Pair branch ⇒ the full algebraic kernel**: if every family of violators with
pairwise-distinct gaps is finite (`hpair` — the number-field analogue of the repaired
[NKR25] pair theorem, S13's *open half*), then the whole violator set of an algebraic
irrational `δ` is finite.  The gap dichotomy of `RB.scaledViolators_finite`, with the
CZ branch discharged by `algGapBounded_slice_finite` and no degeneracy box.

`hpair` is provable for rational `δ` (from `Subspace.evertseSchlickewei` at `n = 3`,
`CITED/NairKumarRoutProof.lean`); for algebraic irrational `δ` it is exactly the
Subspace-over-`ℚ(δ)` program budgeted in [report2] S13. -/
@[category research solved, AMS 11, ref "CZ04" "NKR25" "B1E2", group "rb_rational_base"]
theorem algViolators_finite_of_pairBranch (δ : ℝ) (halg : IsAlgebraic ℚ δ)
    (hirr : Irrational δ) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpair : ∀ T ⊆ algViolators δ θ, Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T →
      T.Finite) :
    (algViolators δ θ).Finite := by
  by_contra hVfin
  have hVinf : (algViolators δ θ).Infinite := hVfin
  set V : Set (ℕ × ℕ) := algViolators δ θ with hVdef
  set gap : ℕ × ℕ → ℕ := fun p => p.2 - p.1 with hgapdef
  by_cases hg : (gap '' V).Finite
  · -- bounded gaps: the CZ slice
    obtain ⟨S, hS⟩ := hg.bddAbove
    apply hVinf
    apply Set.Finite.subset (algGapBounded_slice_finite δ halg hirr S θ hθ0 hθ1)
    intro p hp
    refine ⟨hp, ?_⟩
    have h1 := hS (Set.mem_image_of_mem gap hp)
    obtain ⟨-, hac, -⟩ := hp
    have h2 : gap p = p.2 - p.1 := rfl
    omega
  · -- unbounded gaps: a gap-injective section, then the pair branch
    have hginf : (gap '' V).Infinite := hg
    have hsec : ∀ y ∈ gap '' V, ∃ a ∈ V, gap a = y := by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    have hgapinv : ∀ y ∈ gap '' V, gap (Function.invFunOn gap V y) = y :=
      fun y hy => Function.invFunOn_eq (hsec y hy)
    have hTsub : Function.invFunOn gap V '' (gap '' V) ⊆ V := by
      rintro t ⟨y, hy, rfl⟩
      exact Function.invFunOn_mem (hsec y hy)
    have hinvinj : Set.InjOn (Function.invFunOn gap V) (gap '' V) := by
      intro y1 hy1 y2 hy2 h
      rw [← hgapinv y1 hy1, ← hgapinv y2 hy2, h]
    have hTinf : (Function.invFunOn gap V '' (gap '' V)).Infinite := hginf.image hinvinj
    have hinjT : Set.InjOn gap (Function.invFunOn gap V '' (gap '' V)) := by
      rintro t1 ⟨y1, hy1, rfl⟩ t2 ⟨y2, hy2, rfl⟩ h
      rw [hgapinv y1 hy1, hgapinv y2 hy2] at h
      rw [h]
    exact hTinf (hpair _ hTsub hinjT)

/-! ## The Stage-1 reduction, over `ℝ` -/

/-- Rational Bernoulli certificate (verbatim `TH.exists_pow_ge`; kept private here for
the same reason as in `RB/RationalK.lean` — not a third public copy). -/
private lemma exists_pow_ge (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ r ≤ θ ^ N := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hdivle : (1 - r) / N ≤ 1 - r := div_le_self (by linarith) (by exact_mod_cast hN)
  have hdivpos : 0 < (1 - r) / N := div_pos (by linarith) hN0
  refine ⟨1 - (1 - r) / N, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -((1 - r) / N)) (by linarith) N
  calc r = 1 + (N : ℚ) * (-((1 - r) / N)) := by field_simp; ring
    _ ≤ (1 + -((1 - r) / N)) ^ N := hb
    _ = (1 - (1 - r) / N) ^ N := by rw [← sub_eq_add_neg]

/-- **Algebraic kernel ⇒ superlinear complexity**: the Stage-1 reduction of
`RB.superlinear_of_K_rat`, re-run on `ℝ`-valued distances — pigeonhole, the Bernoulli
scale `θ(C)`, the repetition gate `real_dist_le_of_repetition`, and the growth ceiling
never needed `K ∈ ℚ`.  The kernel hypothesis `hker` is the *only* missing piece for
any given `K`: it holds for rational `K` (`algViolators_finite_of_ratCast`), and for
algebraic irrational `K` it follows from the pair branch
(`algViolators_finite_of_pairBranch`). -/
@[category research solved, AMS 11 68, ref "CZ04" "B1E2", group "rb_rational_base"]
theorem superlinear_of_algKernel {x₀ : ℕ} (hx₀ : 0 < x₀)
    (hker : ∀ θ : ℚ, 0 < θ → θ < 1 → (algViolators (K x₀) θ).Finite) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := by
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ :=
    exists_pow_ge (2 / 3) (by norm_num) (by norm_num) (C + 2) (by omega)
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ p ∈ algViolators (K x₀) θ, p.2 ≤ M := by
    obtain ⟨M, hM⟩ := ((hker θ hθ0 hθ1).image Prod.snd).bddAbove
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  refine ⟨M + x₀ + 1, by omega, ?_⟩
  set k := M + x₀ + 1 with hkdef
  by_contra hle
  obtain ⟨a, c, ha, hac, hc, hrep⟩ := exists_repetition_of_complexity_le (Nat.not_lt.mp hle)
  have hck : c ≤ (C + 2) * k := by
    have h2k : 2 ≤ 2 * k := by omega
    calc c ≤ C * k + 2 := hc
      _ ≤ C * k + 2 * k := Nat.add_le_add_left h2k _
      _ = (C + 2) * k := by ring
  have hkv : (a, c) ∈ algViolators (K x₀) θ := by
    refine ⟨ha, hac, ?_⟩
    calc distToNearestInt (K x₀ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a))
        ≤ (2 / 3 : ℝ) ^ k := real_dist_le_of_repetition hx₀ hrep
      _ ≤ ((θ : ℝ) ^ (C + 2)) ^ k := by
          have hcast : (2 / 3 : ℝ) ≤ (θ : ℝ) ^ (C + 2) := by
            calc (2 / 3 : ℝ) = ((2 / 3 : ℚ) : ℝ) := by norm_num
              _ ≤ ((θ ^ (C + 2) : ℚ) : ℝ) := by exact_mod_cast hθpow
              _ = (θ : ℝ) ^ (C + 2) := by push_cast; ring
          exact pow_le_pow_left₀ (by norm_num) hcast k
      _ = (θ : ℝ) ^ ((C + 2) * k) := (pow_mul _ _ _).symm
      _ ≤ (θ : ℝ) ^ c := pow_le_pow_of_le_one hθ0'.le hθ1'.le hck
  have hcM : c ≤ M := hM (a, c) hkv
  have hbound := repetition_le_add hx₀ hac hrep
  omega

/-- **The S13 payoff, conditional on the pair branch only**: if families of violators
with pairwise-distinct gaps are finite (the number-field pair theorem, S13's open
half), then **`K(x₀)` algebraic ⇒ the carry word's complexity is superlinear** — the
upgrade of [B1E2] T1b from non-automaticity to superlinearity, with complexity content
in every algebraic case.  The rational case needs no hypothesis (T1a); the algebraic
irrational case assembles the CZ half with `hpair`.

Once `hpair` is discharged, `RB.not_automatic_of_K_algebraic` and this theorem's
composition with Cobham retire the AF lane from the algebraic story entirely. -/
@[category research solved, AMS 11 68, ref "CZ04" "NKR25" "B1E2", group "rb_rational_base"]
theorem superlinear_of_K_algebraic_of_pairBranch {x₀ : ℕ} (hx₀ : 0 < x₀)
    (halg : IsAlgebraic ℚ (K x₀))
    (hpair : ∀ θ : ℚ, 0 < θ → θ < 1 → ∀ T ⊆ algViolators (K x₀) θ,
      Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T → T.Finite) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := by
  by_cases hirr : Irrational (K x₀)
  · exact superlinear_of_algKernel hx₀ (fun θ hθ0 hθ1 =>
      algViolators_finite_of_pairBranch (K x₀) halg hirr θ hθ0 hθ1 (hpair θ hθ0 hθ1)) C
  · exact superlinear_of_K_notIrrational hx₀ hirr C

/-! ## The unconditional milestone: close repetitions die out -/

/-- **Close repetitions**: pairs `2 ≤ a < c` with gap `c − a ≤ S` whose windows of
length `⌊c/L⌋ + 1 > c/L` coincide — a period-`(c−a)` stretch of the word from `a`
through `c + c/L`, i.e. long repeats at bounded distance, window a fixed fraction of
position.  Nonvacuous only for `L ≥ 2`: the repetition ceiling
(`RB.repetition_linear_bound`) caps windows at slope `0.585`, so `L = 1` (slope `1`)
is empty for large `c` while `L = 2` (slope `1/2`) is the widest interesting class. -/
@[category API, AMS 11 68, ref "B1E2", group "rb_rational_base"]
def closeRepetitions (x₀ S L : ℕ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ p.1 + S ∧ IsRepetition x₀ p.1 p.2 (p.2 / L + 1)}

/-- **Close repetitions die out for algebraic `K`** — the unconditional S13 milestone:
if `K(x₀)` is algebraic then for every gap bound `S` and every slope `1/L`, only
finitely many close repetitions exist.  Strictly stronger than
`RB.not_eventually_periodic` on its overlap (that excludes one infinite tail; this
bounds every bounded-period family of proportional-length stretches), and **new**
content for algebraic irrational `K`, where no complexity statement was previously
available at all.

Proof: a close repetition at `(a, c)` is a violator at the Bernoulli scale `θ(L)`
(`real_dist_le_of_repetition`, `(2/3)^{⌊c/L⌋+1} ≤ θ^c`), of gap `≤ S`; for irrational
`K` the CZ slices (`algGapBounded_slice_finite`) kill the set, for rational `K` the
full kernel does (`algViolators_finite_of_ratCast`).

Footprint: std3 + `Subspace.schmidt1D'` + `Subspace.evertseSchlickewei` (the latter only
through the rational case). -/
@[category research solved, AMS 11 68, ref "S" "CZ04" "B1E2", group "rb_rational_base"]
theorem closeRepetitions_finite_of_K_algebraic {x₀ : ℕ} (hx₀ : 0 < x₀)
    (halg : IsAlgebraic ℚ (K x₀)) (S L : ℕ) (hL : 1 ≤ L) :
    (closeRepetitions x₀ S L).Finite := by
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ := exists_pow_ge (2 / 3) (by norm_num) (by norm_num) L hL
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hsub : closeRepetitions x₀ S L ⊆ {p ∈ algViolators (K x₀) θ | p.2 ≤ p.1 + S} := by
    rintro ⟨a, c⟩ ⟨ha2, hac, hgap, hrep⟩
    refine ⟨⟨ha2, hac, ?_⟩, hgap⟩
    have hcL : c ≤ L * (c / L + 1) := by
      have hlt : c < c / L * L + L := Nat.lt_div_mul_add (by omega)
      calc c ≤ c / L * L + L := hlt.le
        _ = L * (c / L + 1) := by ring
    calc distToNearestInt (K x₀ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a))
        ≤ (2 / 3 : ℝ) ^ (c / L + 1) := real_dist_le_of_repetition hx₀ hrep
      _ ≤ ((θ : ℝ) ^ L) ^ (c / L + 1) := by
          have hcast : (2 / 3 : ℝ) ≤ (θ : ℝ) ^ L := by
            calc (2 / 3 : ℝ) = ((2 / 3 : ℚ) : ℝ) := by norm_num
              _ ≤ ((θ ^ L : ℚ) : ℝ) := by exact_mod_cast hθpow
              _ = (θ : ℝ) ^ L := by push_cast; ring
          exact pow_le_pow_left₀ (by norm_num) hcast _
      _ = (θ : ℝ) ^ (L * (c / L + 1)) := (pow_mul _ _ _).symm
      _ ≤ (θ : ℝ) ^ c := pow_le_pow_of_le_one hθ0'.le hθ1'.le hcL
  by_cases hirr : Irrational (K x₀)
  · exact (algGapBounded_slice_finite (K x₀) halg hirr S θ hθ0 hθ1).subset hsub
  · have hmem : K x₀ ∈ Set.range ((↑) : ℚ → ℝ) := by
      by_contra hc
      exact hirr hc
    obtain ⟨δ, hδ⟩ := hmem
    have hδ0 : δ ≠ 0 := by
      intro h
      rw [h, Rat.cast_zero] at hδ
      linarith [one_le_K hx₀, hδ]
    have hfin : (algViolators (K x₀) θ).Finite := by
      rw [← hδ]
      exact algViolators_finite_of_ratCast δ hδ0 θ hθ0 hθ1
    exact hfin.subset fun p hp => (hsub hp).1

/-- **The transcendence criterion from repetition structure**: infinitely many close
repetitions at a single gap bound `S` and slope `1/L` force `K(x₀)` to be
transcendental.  A second criterion next to `RB.transcendental_of_automatic`, with a
periodicity-adjacent combinatorial trigger in place of automaticity.  (Honest scope:
the trigger is expected to *fail* for `w` — see the module doc.) -/
@[category research solved, AMS 11 68, ref "CZ04" "B1E2", group "rb_rational_base"]
theorem transcendental_of_closeRepetitions_infinite {x₀ : ℕ} (hx₀ : 0 < x₀) {S L : ℕ}
    (hL : 1 ≤ L) (hinf : (closeRepetitions x₀ S L).Infinite) :
    Transcendental ℚ (K x₀) :=
  fun halg => hinf (closeRepetitions_finite_of_K_algebraic hx₀ halg S L hL)

/-- The dichotomy headline of the milestone: **either** every close-repetition family
of the carry word is finite, **or** `K(x₀)` is transcendental. -/
@[category research solved, AMS 11 68, ref "CZ04" "B1E2", group "rb_rational_base"]
theorem closeRepetitions_finite_or_K_transcendental {x₀ : ℕ} (hx₀ : 0 < x₀) :
    (∀ S L, 1 ≤ L → (closeRepetitions x₀ S L).Finite) ∨ Transcendental ℚ (K x₀) := by
  by_cases halg : IsAlgebraic ℚ (K x₀)
  · exact Or.inl fun S L hL => closeRepetitions_finite_of_K_algebraic hx₀ halg S L hL
  · exact Or.inr halg

end RB
