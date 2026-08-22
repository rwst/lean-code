/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.TwoAdic
import TH.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Order.Interval.Finset.Nat

/-!
# Coarse-scale pair separation for the (3/2)ⁿ orbit (A5, T3)

Plan A5's T3, as re-scoped by its WP0 audit (`plans/plan-A5.html` §0.1 Finding 2).

## What is *not* here: the `2^{-n}` separation

The exact separation `‖(3/2)^n − (3/2)^m‖ ≥ 2^{-n}` is **already proved** in the corpus and
is not restated:

* `TH.one_le_two_pow_mul_distToNearestInt_orbit` (`TH/Basic.lean`) — the kernel/`‖·‖` form;
* `TH.one_le_two_pow_mul_abs_eps_sub` (`TH/RepetitionIdentity.lean`) — the `ε`-form twin;
* `TH.distToNearestInt_orbit_pos`, `TH.distToNearestInt_orbit_le` — positivity and bridge.

Both rest on the same odd-numerator observation this file's `TH.odd_three_pow_sub_two_pow`
records: `(3/2)^n − (3/2)^m = 3^m(3^{n-m} − 2^{n-m})/2^n` has odd numerator, so its reduced
denominator is exactly `2^n`.

## What *is* here: coarse-scale multiplicity

The genuinely missing content is one level up, at the **second** differences.  Writing
`D_d = 3^d − 2^d` for the gap-`d` numerator, `two_pow_dvd_secondDifference_iff` says that
for `3 ≤ v ≤ d'` and `d > d'`,

  `2^v ∣ D_d − D_{d'}  ↔  2^(v-2) ∣ d − d'`,

an *exact* criterion: high 2-divisibility between two gap-numerators is equivalent to a
congruence on the gaps themselves.  The counting consequence is `card_le_of_two_pow_dvd`:
for fixed `d' ≥ v`, at most `(N − d')/2^(v-2)` gaps `d ≤ N` can meet the target — a full
factor `2^(v-2)` below the trivial count.  This is the elementary substrate for coarse-scale
additive-energy counting at scales `s = 2^{-γn}`.

The hypothesis `v ≤ d'` is **necessary, not an artefact** — `not_two_pow_dvd_secondDifference_iff`
exhibits `d' = 1`, `d = 4`, `v = 3`: `D_4 − D_1 = 64` is divisible by `2^3` while
`2^1 ∤ 3`.  Above `d'` one is in the diagonal regime of `TH.v2_second_difference_diagonal`,
where the leading digits cancel and the valuation is no longer read off the gap.

## Where this stops: the fine scale is not elementary ([A5] §2.4, risk R2)

The bounds above are *coarse-scale*: they control multiplicity at dyadic scales `2^{-v}`
with `v` a fixed proportion of the gap.  The Poissonian regime `s ≍ 1/N` that an additive-
energy programme (angle A6) would actually need is **not** reachable from here, and no
claim toward it is made.  That regime is the Diophantine kernel (K) of [M4A3] §4–5 —
`TH/KernelReduction.lean`, `TH/GapSlices.lean`, `TH/GapDichotomy.lean`, resting on the
Subspace-grade input `Subspace.evertseSchlickewei` via `CITED/CorvajaZannier.lean`.  The
boundary is exactly the one drawn in `TH/TwoAdic.lean`'s module doc: two-term forms over
`Γ = ⟨2,3⟩` are LTE-exact and elementary; everything past them is Subspace-grade or is the
distribution problem itself.

## Contents

* `two_pow_dvd_three_pow_sub_one_int_iff` — the `ℕ`/`ℤ` bridge for the `W1` criterion.
* `two_pow_dvd_secondDifference_iff` — the exact divisibility criterion (`3 ≤ v ≤ d'`).
* `not_two_pow_dvd_secondDifference_iff` — sharpness: `v ≤ d'` cannot be dropped.
* `card_le_of_two_pow_dvd` — the coarse-scale multiplicity bound.

## References

* [A5] `plans/plan-A5.html`: T3/WP3 as re-scoped by §0.1 Finding 2; §2.4 (what may and may
  not be claimed at the fine scale).
* [M4A3] `plans/plan-M4A3.html` §4–5: the Diophantine kernel that owns the `1/N` regime.
-/

namespace TH

/-- `ℕ`/`ℤ` bridge: `2^v ∣ 3^e − 1` may be read in either ring. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
lemma two_pow_dvd_three_pow_sub_one_int_iff (v e : ℕ) :
    (2 : ℤ) ^ v ∣ (3 : ℤ) ^ e - 1 ↔ (2 : ℕ) ^ v ∣ 3 ^ e - 1 := by
  have h1e : (1 : ℕ) ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have hc : ((3 : ℤ) ^ e - 1) = ((3 ^ e - 1 : ℕ) : ℤ) := by push_cast [h1e]; ring
  rw [hc, show ((2 : ℤ) ^ v) = (((2 ^ v : ℕ)) : ℤ) by push_cast; ring, Int.natCast_dvd_natCast]

/-- **Exact divisibility criterion for second differences** ([A5] T3): for `3 ≤ v ≤ d'` and
`d > d'`,

  `2^v ∣ (3^d − 2^d) − (3^{d'} − 2^{d'})  ↔  2^(v-2) ∣ d − d'`.

Below `d'` the term `2^{d'}(2^e − 1)` is invisible mod `2^v`, so the whole question reduces
to `2^v ∣ 3^e − 1` — which `two_pow_dvd_three_pow_sub_one_iff` converts into a congruence on
the gap.  Both directions are exact; nothing is estimated. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem two_pow_dvd_secondDifference_iff {v d d' : ℕ} (hv : 3 ≤ v) (hvd : v ≤ d')
    (hlt : d' < d) :
    (2 : ℤ) ^ v ∣ ((3 : ℤ) ^ d - 2 ^ d) - ((3 : ℤ) ^ d' - 2 ^ d') ↔ 2 ^ (v - 2) ∣ d - d' := by
  obtain ⟨e, rfl⟩ : ∃ e, d = d' + e := ⟨d - d', by omega⟩
  simp only [show d' + e - d' = e by omega]
  have hsplit : ((3 : ℤ) ^ (d' + e) - 2 ^ (d' + e)) - ((3 : ℤ) ^ d' - 2 ^ d')
      = 3 ^ d' * ((3 : ℤ) ^ e - 1) - 2 ^ d' * ((2 : ℤ) ^ e - 1) := by ring
  have hdvd2 : (2 : ℤ) ^ v ∣ 2 ^ d' * ((2 : ℤ) ^ e - 1) :=
    Dvd.dvd.mul_right (pow_dvd_pow 2 hvd) _
  have hcop : IsCoprime ((2 : ℤ) ^ v) ((3 : ℤ) ^ d') :=
    IsCoprime.pow (⟨-1, 1, by ring⟩ : IsCoprime (2 : ℤ) 3)
  rw [hsplit, ← two_pow_dvd_three_pow_sub_one_iff (e := e) hv,
    ← two_pow_dvd_three_pow_sub_one_int_iff]
  refine ⟨fun h => ?_, fun h => dvd_sub (h.mul_left _) hdvd2⟩
  have h1 : (2 : ℤ) ^ v ∣ 3 ^ d' * ((3 : ℤ) ^ e - 1) := by
    have := dvd_add h hdvd2
    simpa using this
  exact hcop.dvd_of_dvd_mul_left h1

/-- **Sharpness of `two_pow_dvd_secondDifference_iff`**: the hypothesis `v ≤ d'` cannot be
dropped.  At `d' = 1`, `d = 4`, `v = 3` the second difference is `D_4 − D_1 = 65 − 1 = 64`,
divisible by `2^3`, while `2^(3-2) = 2` does not divide the gap `3`.  Above `d'` one is in
the diagonal regime of `v2_second_difference_diagonal`, where the leading digits cancel and
the valuation is no longer determined by the gap. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem not_two_pow_dvd_secondDifference_iff :
    ¬ ((2 : ℤ) ^ 3 ∣ ((3 : ℤ) ^ 4 - 2 ^ 4) - ((3 : ℤ) ^ 1 - 2 ^ 1) ↔ 2 ^ (3 - 2) ∣ 4 - 1) := by
  decide

/-- **Coarse-scale multiplicity bound** ([A5] T3): for a fixed base gap `d' ≥ v ≥ 3`, the
gaps `d ∈ (d', N]` whose second difference is divisible by `2^v` lie in a single arithmetic
progression of modulus `2^(v-2)`, so there are at most `(N − d')/2^(v-2)` of them — a factor
`2^(v-2)` below the trivial count `N − d'`.

This is the elementary input a coarse-scale additive-energy count consumes.  It does *not*
reach the Poissonian scale `s ≍ 1/N`; see the module doc. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem card_le_of_two_pow_dvd {v d' N : ℕ} (hv : 3 ≤ v) (hvd : v ≤ d') :
    ((Finset.Ioc d' N).filter
      (fun d => (2 : ℤ) ^ v ∣ ((3 : ℤ) ^ d - 2 ^ d) - ((3 : ℤ) ^ d' - 2 ^ d'))).card
      ≤ (N - d') / 2 ^ (v - 2) := by
  have hq0 : 0 < 2 ^ (v - 2) := by positivity
  refine le_trans (Finset.card_le_card_of_injOn (f := fun d => (d - d') / 2 ^ (v - 2))
    (s := (Finset.Ioc d' N).filter
      (fun d => (2 : ℤ) ^ v ∣ ((3 : ℤ) ^ d - 2 ^ d) - ((3 : ℤ) ^ d' - 2 ^ d')))
    (t := Finset.Icc 1 ((N - d') / 2 ^ (v - 2))) ?_ ?_) ?_
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd1, hd2⟩, hdvd⟩ := hd
    rw [two_pow_dvd_secondDifference_iff hv hvd hd1] at hdvd
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hq0).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right (by omega)⟩
  · intro d1 h1 d2 h2 heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc] at h1 h2
    obtain ⟨⟨h11, h12⟩, hv1⟩ := h1
    obtain ⟨⟨h21, h22⟩, hv2⟩ := h2
    rw [two_pow_dvd_secondDifference_iff hv hvd h11] at hv1
    rw [two_pow_dvd_secondDifference_iff hv hvd h21] at hv2
    have e1 : (d1 - d') / 2 ^ (v - 2) * 2 ^ (v - 2) = d1 - d' := Nat.div_mul_cancel hv1
    have e2 : (d2 - d') / 2 ^ (v - 2) * 2 ^ (v - 2) = d2 - d' := Nat.div_mul_cancel hv2
    simp only at heq
    rw [heq] at e1
    omega
  · simp

end TH
