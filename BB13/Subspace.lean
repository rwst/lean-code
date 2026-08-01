/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.CorvajaZannierProof
import BB13.GapPrinciple

/-!
# Subspace layer for Problem 10.13: finiteness and the per-line relation (D2 / M3)

Milestone **M3** of `plans/plan-1013.html` — the Diophantine core (deliverable **D2**): bound the
number of `n` with `‖(3/2)ⁿ‖ < (3/4)ⁿ` through the Subspace theorem.  This file carries the
**qualitative** half (T1 finiteness) and the elementary per-line relation; the *quantitative* half
lives in `BB13/LineCover.lean` (the line cover) and `BB13/FailureCount.lean` (the counts).

## Reuse of the corpus subspace lane

The plan's §2.1 frame — the point `(3ⁿ, m·2ⁿ) ∈ ℤ²`, `S = {∞, 2, 3}`, place-product `(3/4)ⁿ =
H^{-ε}` — is the `ℚ`, `δ ∈ ℚ`, `Γ = ⟨2, 3⟩` case of the **Corvaja–Zannier Main Theorem** on
`‖αⁿ‖`, already in `CITED/` as `CZ.pseudoPisot_approx_of_subspace` (finiteness, on the single
`Subspace.evertseSchlickewei`).  Problem 10.13 is its instance `δ = 1`, `q = 1`,
`u = (3/2)ⁿ = 2⁻ⁿ·3ⁿ`: at the sharp `ε* = log(4/3)/log 3` a failure gives
`‖(3/2)ⁿ‖ < (3/4)ⁿ = (3ⁿ)^{-ε*} = H(u)^{-ε*}q^{-1-ε*}` — no headroom is needed, the failure
inequality is already strict — so `n ↦ (1, -n, n)` injects the failure set into the
Corvaja–Zannier exceptional set `CZ.approxSet 1 ε*`.

## What is proved

* `failures_finite` / `failures_bounded` — the failure set is **finite** (T1 finiteness; Mahler's
  theorem via the corpus subspace engine).  Footprint `std3 + Subspace.evertseSchlickewei`.
  Ineffective: the Subspace Theorem bounds no cardinality.
* `collinear_imp_link`, `collinear_scaling`, `collinear_resid` — the **§3 per-line analysis**:
  collinear failure points satisfy the M2 linkage *scaling relation* `mₐ = 2ᵈμ`, `m_b = 3ᵈμ`,
  `k_b = 3ᵈkₐ` (`std3`-clean, reusing `BB13.GapPrinciple`).  This is the beginning of the
  "counting inside the exceptional subspace" that Evertse–Ferretti (p. 6) leave open — but note
  what it does *not* say: collinearity forces the scaling relation, **not** the §3 threshold
  relation `Linkable`, and a single line can carry several `Linkable`-towers.  The failures
  `n = 2` and `n = 3` are the witness: their frame points `(8, 9)` and `(24, 27) = 3·(8, 9)` are
  collinear, yet `2·(3/4)²·3 = 27/8 > 1`, so they are not `Linkable`.  The vocabulary of
  `BB13/LineTower.lean` keeps the two notions apart.

## A note on the retired effective count

Earlier versions of this file carried `failures_card_le : F(∞) ≤ CZ.effectiveCard 1 ε`, on a
cited axiom asserting an effective *solution* count.  That axiom overstated its source: Bugeaud–
Evertse Cor. 5.2 bounds the number of **lines**, above a height threshold, and the passage to a
solution count is the open per-line problem.  The axiom was deleted on 2026-07-21 and the counts
rebuilt honestly in `BB13/LineCover.lean` and `BB13/FailureCount.lean`; see
`CITED/BugeaudEvertseRidout.lean` and `plans/plan2-BB13.html`.

## References

* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) — the `‖αⁿ‖` Subspace engine (`CITED/`).
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the quantitative Ridout line
  count (`CITED/BugeaudEvertseRidout.lean`).
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
-/

namespace BB13

open scoped Real

/-! ### The Corvaja–Zannier instantiation for `‖(3/2)ⁿ‖ < (3/4)ⁿ` -/

/-- The exponent `ε₀ = log(4/3)/(2·log 3) = ε*/2`.  The `(3/4)ⁿ`-lane no longer needs it — at
`ε*` the failure threshold is met exactly (`BB13.rpow_neg_epsStar`) — but the Waring lane of
`BB13/Waring.lean` runs on the *weaker* smallness event `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹`, which needs an
exponent strictly below `ε*`; `ε₀` is the one it uses.  (W5 of `plans/plan2-BB13.html` replaces
it by the sharper `ε_W = ε* − θ/257`.) -/
noncomputable def epsZero : ℝ := Real.log (4 / 3) / (2 * Real.log 3)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsZero_pos : 0 < epsZero :=
  div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- The failure-to-triple map `n ↦ (1, -n, n)` (i.e. `q = 1`, `u = 2⁻ⁿ·3ⁿ = (3/2)ⁿ`). -/
def toTriple (n : ℕ) : ℕ × ℤ × ℤ := (1, -(n : ℤ), (n : ℤ))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem toTriple_injective : Function.Injective toTriple := by
  intro a b hab; simp only [toTriple, Prod.mk.injEq] at hab; omega

/-- **General Corvaja–Zannier membership.**  For `n ≥ 1`, whenever the nearest-integer distance
of `(3/2)ⁿ` lies below the Subspace threshold `(3ⁿ)^{-ε}`, the point `n ↦ (1, -n, n)` lands in
the Corvaja–Zannier exceptional set `CZ.approxSet 1 ε`.  The analytic hypothesis `hlt` is supplied
by the caller (any `‖(3/2)ⁿ‖`-smallness event — a genuine `(3/4)ⁿ`-failure, or the Waring
`(3/4)ⁿ⁻¹`-failure of `BB13.Waring`); everything else is the fixed frame data. -/
@[category API, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem mem_approxSet_of_distBound {n : ℕ} (hn1 : 1 ≤ n) {ε : ℝ}
    (hlt : distToNearestInt (((3 : ℝ) / 2) ^ n) < ((3 : ℝ) ^ n) ^ (-ε)) :
    toTriple n ∈ CZ.approxSet 1 ε := by
  rw [CZ.approxSet, Set.mem_setOf_eq, toTriple]
  have hval : CZ.sval 1 1 (-(n : ℤ)) (n : ℤ) = (3 / 2 : ℚ) ^ n := by
    rw [CZ.sval, zpow_neg, zpow_natCast, zpow_natCast, div_pow]; push_cast; ring
  have hpos : 0 < ((3 / 2 : ℚ) ^ n).distToNearestInt := by
    apply Rat.distToNearestInt_pos_of_two_pow_mul_odd hn1 (O := (3 : ℤ) ^ n)
    · exact Int.odd_iff.mp (Odd.pow (by decide))
    · push_cast; rw [div_pow]; field_simp
  refine ⟨le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hval, abs_of_pos (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
  · rw [hval]; exact Rat.not_exists_intCast_eq_of_distToNearestInt_pos hpos
  · rw [hval]; exact hpos
  · rw [hval, CZ.height23_neg_natCast, Nat.cast_one, Real.one_rpow, mul_one]
    have hbridge : (((3 / 2 : ℚ) ^ n).distToNearestInt : ℝ) = distToNearestInt (((3 : ℝ) / 2) ^ n) := by
      rw [← distToNearestInt_ratCast]; congr 1; push_cast; ring
    have hcast : ((3 ^ n : ℕ) : ℝ) = ((3 : ℝ) ^ n) := by push_cast; ring
    rw [hbridge, hcast]; exact hlt

/-- **Membership for a genuine failure**, at the sharp exponent.  `‖(3/2)ⁿ‖ < (3/4)ⁿ` (`n ≥ 1`)
lands in the Corvaja–Zannier exceptional set at `ε*`, since `(3/4)ⁿ = (3ⁿ)^{-ε*}` exactly
(`rpow_neg_epsStar`): the strictness of the failure inequality is all the headroom needed. -/
private theorem toTriple_mem {n : ℕ} (hn1 : 1 ≤ n) (hnf : IsFailure 3 2 (3 / 4) n) :
    toTriple n ∈ CZ.approxSet 1 epsStar := by
  apply mem_approxSet_of_distBound hn1
  rw [rpow_neg_epsStar]
  have h := (isFailure_iff 3 2 (3 / 4) n (by norm_num)).mp hnf
  norm_num at h
  exact h

/-! ### T1: finiteness -/

/-- **The failure set of `‖(3/2)ⁿ‖ < (3/4)ⁿ` is finite** (T1 finiteness; Mahler's theorem via the
Subspace theorem).  Instance `δ = 1`, `q = 1`, `u = (3/2)ⁿ` of `CZ.pseudoPisot_approx_of_subspace`.
Footprint `std3 + Subspace.evertseSchlickewei` — no new axiom.  Ineffective: for a *count* see
`BB13.failures_card_le_of_heightBound`. -/
@[category research solved, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem failures_finite : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.Finite := by
  apply Set.Finite.of_finite_image (f := toTriple) _ toTriple_injective.injOn
  apply (CZ.approxSet_finite 1 (by norm_num) epsStar epsStar_pos).subset
  rintro _ ⟨n, ⟨hn1, hnf⟩, rfl⟩
  exact toTriple_mem hn1 hnf

/-- **Only finitely many failures** (boundedness form): there is `N₀` past which
`‖(3/2)ⁿ‖ ≥ (3/4)ⁿ` always — hence the ideal Waring formula holds for all large `n`. -/
@[category research solved, AMS 11, ref "CZ04" "Bug12", group "bugeaud_10_13"]
theorem failures_bounded : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ IsFailure 3 2 (3 / 4) n := by
  obtain ⟨N₀, hN₀⟩ := failures_finite.bddAbove
  refine ⟨N₀ + 1, fun n hn hfail => ?_⟩
  have hmem : n ∈ {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n} := ⟨by omega, hfail⟩
  have := hN₀ hmem; omega

/-! ### §3 per-line analysis: collinearity forces the scaling relation -/

/-- The subspace-frame point `x = (pⁿ, m·qⁿ) ∈ ℤ²` of §2.1, `m = round((p/q)ⁿ)`. -/
noncomputable def failPoint (p q n : ℕ) : ℤ × ℤ := ((p : ℤ) ^ n, Mnum p q n * (q : ℤ) ^ n)

/-- Two integer points are **collinear** (on one line through the origin) when their cross
product vanishes. -/
def CollinearPts (x y : ℤ × ℤ) : Prop := x.1 * y.2 = x.2 * y.1

/-- **Collinear ⟹ the linkage equation.**  If the frame points of two failures `a ≤ b` are
collinear, then `pᵇ⁻ᵃ·mₐ = qᵇ⁻ᵃ·m_b` — the M2 linkage relation, here with *no* threshold
hypothesis: collinearity alone forces it. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem collinear_imp_link (p q a b : ℕ) (hp : 0 < p) (hq : 0 < q) (hab : a ≤ b)
    (hc : CollinearPts (failPoint p q a) (failPoint p q b)) :
    (p : ℤ) ^ (b - a) * Mnum p q a = (q : ℤ) ^ (b - a) * Mnum p q b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  simp only [failPoint, CollinearPts] at hc
  rw [Nat.add_sub_cancel_left]
  have key : ((p : ℤ) ^ a * (q : ℤ) ^ a) * ((q : ℤ) ^ d * Mnum p q (a + d))
           = ((p : ℤ) ^ a * (q : ℤ) ^ a) * ((p : ℤ) ^ d * Mnum p q a) := by
    rw [pow_add, pow_add] at hc; ring_nf; ring_nf at hc; linarith [hc]
  have hpq : (0 : ℤ) < (p : ℤ) ^ a * (q : ℤ) ^ a := by positivity
  have := mul_left_cancel₀ (ne_of_gt hpq) key
  linarith [this]

/-- **One line = one scaling family.**  Two collinear failures `a ≤ b` are a `pᵇ⁻ᵃ`-scaling of a
single reduced base `μ = mₐ/qᵇ⁻ᵃ`: `mₐ = qᵇ⁻ᵃ·μ`, `m_b = pᵇ⁻ᵃ·μ` — proved by reducing
collinearity to M2's `link_scaling`.  This is the *relation* half of §3's per-line structure; the
threshold half (`Linkable`) does **not** follow from collinearity, and the two must not be
conflated (`BB13/LineTower.lean`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem collinear_scaling (p q a b : ℕ) (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime p q)
    (hab : a ≤ b) (hc : CollinearPts (failPoint p q a) (failPoint p q b)) :
    ∃ μ : ℤ, Mnum p q a = (q : ℤ) ^ (b - a) * μ ∧ Mnum p q b = (p : ℤ) ^ (b - a) * μ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_sub_cancel_left]
  have hlink := collinear_imp_link p q a (a + d) hp hq hab hc
  rw [Nat.add_sub_cancel_left] at hlink
  exact link_scaling p q hq hcop hlink

/-- On one line the residues scale: `k_b = pᵇ⁻ᵃ·kₐ` (the quality of the base propagates up the
tower).  From `collinear_imp_link` and M2's `link_resid`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem collinear_resid (p q a b : ℕ) (hp : 0 < p) (hq : 0 < q) (hab : a ≤ b)
    (hc : CollinearPts (failPoint p q a) (failPoint p q b)) :
    resid p q b = (p : ℤ) ^ (b - a) * resid p q a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_sub_cancel_left]
  have hlink := collinear_imp_link p q a (a + d) hp hq hab hc
  rw [Nat.add_sub_cancel_left] at hlink
  exact link_resid p q hlink

end BB13
