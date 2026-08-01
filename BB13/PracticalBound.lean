/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.Subspace
import BB13.TowerCount
import ForMathlib.Data.Set.Card

/-!
# The elementary practical bound `F(N) ≤ (max-tower) · #towers(N)` (D4)

Deliverable **D4** of `plans/plan-1013.html` — the elementary, `O(log N)` arm of the
"resolution-in-practice": the number `F(N)` of failures `‖(3/2)ⁿ‖ < (3/4)ⁿ` with `n ≤ N` is
bounded through the §3 tower decomposition.

`exists_towerBase_le` (strong induction, std3-clean) shows **every failure `n ≥ 1` sits over a
tower base `b ≤ n`**: if `n` is not itself a tower base it is linked to a smaller failure, and the
base is reached by descent.  Assigning each failure to a base (`assignedBase`) and counting fibres
(`Set.ncard_le_mul_ncard_image`) gives `F(N) ≤ (max-tower) · #{tower bases ≤ N}` for any bound
`max-tower` on a threshold-tower's height (`failuresUpTo_card_le_towers`).  Feeding
`BB13.towerBases_card_le_three_halves` turns `#{tower bases ≤ N}` into the explicit
`11 + (1 + log_{6/5} N) ≈ 12 + 5.49 ln N` (the sharp `4.30 ln N` needs a `log 3` bound absent from
Mathlib; the parametric M2 count is what we have): `practical_bound_log`.

The per-tower height is a *hypothesis*, and the two tower notions must be kept apart
(`BB13/LineTower.lean`).  In the certified range `E ∩ [1, 256] = {1, 2, 3, 4, 7}`
(`BB13.failuresUpTo_256_eq`) the **threshold**-tower height is `1` — the five failures are
pairwise unlinked, each its own base — while the **relation**-tower height is `2`, since `n = 2`
and `n = 3` share the line of slope `8/9` without being `Linkable`.  Bounding either height in
general is the level-2 problem, out of this elementary layer's scope.

The second arm — the Diophantine one — is no longer a global constant `C`: what the quantitative
literature supports is a bound on the number of *lines* (`BB13/LineCover.lean`), and the combined
`min` form now lives in `BB13/FailureCount.lean` (`practical_bound_min`), where the certified
kernel segment is spliced in as well.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13.
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count
  (`CITED/BugeaudEvertseRidout.lean`).
-/

namespace BB13

open scoped Real
open Classical

/-! ### Failures and tower bases up to `N` -/

/-- The failures `‖(3/2)ⁿ‖ < (3/4)ⁿ` with `1 ≤ n ≤ N`; `F(N) = #failuresUpTo N`. -/
def failuresUpTo (N : ℕ) : Set ℕ := {n | 1 ≤ n ∧ n ≤ N ∧ IsFailure 3 2 (3 / 4) n}

/-- The tower bases (failures not linked to any smaller failure) with `1 ≤ b ≤ N`. -/
def towerBasesUpTo (N : ℕ) : Set ℕ := {b | 1 ≤ b ∧ b ≤ N ∧ IsTowerBase 3 2 (3 / 4) b}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_finite (N : ℕ) : (failuresUpTo N).Finite :=
  (Set.finite_Icc 1 N).subset fun _ ⟨h1, hN, _⟩ => Set.mem_Icc.mpr ⟨h1, hN⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem towerBasesUpTo_finite (N : ℕ) : (towerBasesUpTo N).Finite :=
  (Set.finite_Icc 1 N).subset fun _ ⟨h1, hN, _⟩ => Set.mem_Icc.mpr ⟨h1, hN⟩

/-! ### The tower arm: every failure sits over a tower base -/

/-- **Tower covering** (std3-clean): every failure `n ≥ 1` has a tower base `b ≤ n`.  Strong
induction — if `n` is not itself a tower base it is linked to a smaller failure `a` (with `1 ≤ a`,
since `Linkable 0 n = 2·3ⁿ ≤ 1` is false), and the base is inherited from `a`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exists_towerBase_le : ∀ n, 1 ≤ n → IsFailure 3 2 (3 / 4) n →
    ∃ b, 1 ≤ b ∧ b ≤ n ∧ IsTowerBase 3 2 (3 / 4) b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1 hfn
    by_cases hbase : IsTowerBase 3 2 (3 / 4) n
    · exact ⟨n, hn1, le_refl n, hbase⟩
    · rw [IsTowerBase] at hbase
      push Not at hbase
      obtain ⟨a, ha_lt, ha_f, ha_link⟩ := hbase hfn
      have ha1 : 1 ≤ a := by
        by_contra h
        have ha0 : a = 0 := by omega
        subst ha0
        rw [Linkable] at ha_link
        simp only [pow_zero, mul_one, Nat.sub_zero] at ha_link
        push_cast at ha_link
        have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        nlinarith [ha_link, h3]
      obtain ⟨b, hb1, hb_le, hb_base⟩ := ih a ha_lt ha1 ha_f
      exact ⟨b, hb1, le_trans hb_le (le_of_lt ha_lt), hb_base⟩

/-- The base a failure is assigned to: a tower base `≤ n` when one exists (it does for every
failure, `exists_towerBase_le`), else `n`.  Classically chosen; `assignedBase_mem` is all we use. -/
noncomputable def assignedBase (n : ℕ) : ℕ :=
  if h : ∃ b, 1 ≤ b ∧ b ≤ n ∧ IsTowerBase 3 2 (3 / 4) b then h.choose else n

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem assignedBase_mem {N n : ℕ} (hn : n ∈ failuresUpTo N) : assignedBase n ∈ towerBasesUpTo N := by
  obtain ⟨h1, hN, hf⟩ := hn
  have hex : ∃ b, 1 ≤ b ∧ b ≤ n ∧ IsTowerBase 3 2 (3 / 4) b := exists_towerBase_le n h1 hf
  unfold assignedBase
  rw [dif_pos hex]
  obtain ⟨hb1, hbn, hbase⟩ := hex.choose_spec
  exact ⟨hb1, le_trans hbn hN, hbase⟩

/-- **The tower arm:** `F(N) ≤ (1 + max-tower) · #{tower bases ≤ N}`, for any `H` bounding the
number of failures assigned to a single tower base.  Fibre count over `assignedBase`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_card_le_towers (N H : ℕ)
    (hfib : ∀ b, {n ∈ failuresUpTo N | assignedBase n = b}.ncard ≤ H) :
    (failuresUpTo N).ncard ≤ H * (towerBasesUpTo N).ncard := by
  have himg : assignedBase '' failuresUpTo N ⊆ towerBasesUpTo N := by
    rintro _ ⟨n, hn, rfl⟩; exact assignedBase_mem hn
  calc (failuresUpTo N).ncard
      ≤ H * (assignedBase '' failuresUpTo N).ncard :=
        Set.ncard_le_mul_ncard_image (failuresUpTo_finite N) assignedBase H hfib
    _ ≤ H * (towerBasesUpTo N).ncard :=
        Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg (towerBasesUpTo_finite N))

/-! ### The `O(log N)` tower count and the practical bound -/

/-- The tower count in `[1, N]` is `O(log N)`: `#{tower bases ≤ N} ≤ 11 + (1 + log_{6/5} N)`,
from `BB13.towerBases_card_le_three_halves` (M2), modulo the standard `log 2 ≥ 0.6931`,
`log 3 ≤ 1.0987`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem towerBasesUpTo_card_le_log (N : ℕ)
    (hlog2 : (0.6931 : ℝ) ≤ Real.log 2) (hlog3 : Real.log 3 ≤ (1.0987 : ℝ)) :
    ((towerBasesUpTo N).ncard : ℝ) ≤ 11 + (1 + Real.logb (6 / 5) N) := by
  have hfin := towerBasesUpTo_finite N
  have hcard : (towerBasesUpTo N).ncard = hfin.toFinset.card := by
    rw [← Set.ncard_coe_finset, hfin.coe_toFinset]
  rw [hcard]
  apply towerBases_card_le_three_halves N hfin.toFinset
  · intro n hn; rw [Set.Finite.mem_toFinset] at hn; exact hn.2.2
  · intro n hn; rw [Set.Finite.mem_toFinset] at hn; exact hn.1
  · intro n hn; rw [Set.Finite.mem_toFinset] at hn; exact hn.2.1
  · exact hlog2
  · exact hlog3

/-- **The practical bound in `O(log N)` form** (D4, elementary arm): with `H` bounding the
threshold-tower height, `F(N) ≤ H · (11 + 1 + log_{6/5} N) ≈ H·(12 + 5.49 ln N)`.  Combined with
the line count and the certified kernel segment in `BB13.practical_bound_min`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem practical_bound_log (N H : ℕ)
    (hfib : ∀ b, {n ∈ failuresUpTo N | assignedBase n = b}.ncard ≤ H)
    (hlog2 : (0.6931 : ℝ) ≤ Real.log 2) (hlog3 : Real.log 3 ≤ (1.0987 : ℝ)) :
    ((failuresUpTo N).ncard : ℝ) ≤ (H : ℝ) * (11 + (1 + Real.logb (6 / 5) N)) := by
  calc ((failuresUpTo N).ncard : ℝ)
      ≤ ((H * (towerBasesUpTo N).ncard : ℕ) : ℝ) := by
        exact_mod_cast failuresUpTo_card_le_towers N H hfib
    _ = (H : ℝ) * ((towerBasesUpTo N).ncard : ℝ) := by push_cast; ring
    _ ≤ (H : ℝ) * (11 + (1 + Real.logb (6 / 5) N)) :=
        mul_le_mul_of_nonneg_left (towerBasesUpTo_card_le_log N hlog2 hlog3) (by positivity)

end BB13
