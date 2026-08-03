/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import TH.Solenoid.LimitMeasures
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The defect taxonomy: atoms are periodic, periodic is torsion, torsion is finite

Work package **W13** of plan-A1+ (§4, L11): classify the ways a limit measure of the `(3/2)ⁿ`
orbit can fail to be Haar, and kill the cheap classes.  The three targets the plan names are all
here, and they chain:

* `atom_of_invariant_periodic` — an atom of a `T`-invariant finite measure is a **periodic point**
  (else its forward orbit is infinite and carries infinite mass);
* `periodic_iff_torsion` — the period-`π` points are exactly the `(3^π − 2^π)`-**torsion** of `Σ₆`
  (multiply `((3/2)^π − 1)x ∈ ℤ[1/6]` by the unit `2^π`);
* `torsionSub_finite` — every torsion set is **finite** (a torsion point has a diagonal rational
  representative, and `ℤ[1/6] ∩ ℤ₂ ∩ ℤ₃ = ℤ` forces it to be `0` near the origin);
* `invariant_closed_subgroup_finite` — a closed subgroup of `Σ₆` carried onto itself by both `σ₂`
  and `σ₃` is **finite or everything**.

Consequences for L11.  The atomic defect class is carried by the countable set of periodic points
(`atoms_subset_periodicPoints`, `countable_periodicPoints`), each of which is an explicit rational
with odd denominator — the circle-level shadow is `Z32.cycle_point_eq`.  The **algebraic-leaf class
collapses**: the only proper closed `ℤ²`-invariant subgroups are finite torsion sets
(`invariant_closed_subgroup_finite` + `exists_nsmul_eq_zero_of_finite`), so no limit measure can
hide on a positive-dimensional invariant subgroup.  The affine transfer of L11(i) is
`T32_iter_sub_periodic`: `T` is a group automorphism, so the dynamics at a periodic point is the
dynamics at `0` translated.  What this does **not** do is exclude the remaining classes; per the
2026-08-02 revision of the K1 exit (W11), the atomic class is reduced to A13-N1 and no further, and
the positive-entropy non-invariant residual is untouched.

## The proof of the subgroup theorem, and why there is no duality here

The plan's sketch was dual: annihilators of closed subgroups are ideals of `ℤ[1/6]`, and a nonzero
ideal has finite index.  Mathlib has no Pontryagin duality, so that route would have to build the
bipolar theorem first.  It is not needed.  Everything follows from two elementary sequences
(`eulerTwo`, `eulerThree`) supplied by Fermat–Euler:

`3^(φ(2ⁿ)·n) → 1` in `ℚ₂` and `→ 0` in `ℚ₃`, and the mirror image with `2` and `3` exchanged.

Multiplying a fibre element `(0, y, z)` of a closed subgroup by these *integers* therefore splits
it: `(0, y, 0)` and `(0, 0, z)` are separately in the subgroup (`fiber_kill_three`,
`fiber_kill_two`).  A single nonzero point on a `p`-adic axis then fills that axis — integer
multiples give the ball of radius `‖y‖` by density of `ℤ` in `ℤ_p`, and the halving hypothesis
inflates it to `ℚ_p` (`padicTwo_axis`, `padicThree_axis`).  Subtracting lattice points converts an
axis into the real axis (`real_axis_of_padicTwo`), and the real axis plus one more application of
the Euler sequences gives everything (`eq_top_of_real_axis`).  The dichotomy that starts the
machine (`ambient_eq_top`) is: either the subgroup has arbitrarily small elements with a *nonzero
real coordinate* — whose integer multiples then `|g₁|`-fill `ℝ`, since integer multiples never
increase a `p`-adic norm — or some small element lies in the fibre, and the Euler split applies.
Compactness of `Σ₆` converts "isolated at `0`" into "finite" (`finite_of_boxNbhd_isolated`).

Two-sided `σ`-invariance is used exactly twice, to supply the halving hypotheses `×(1/2)` and
`×(1/3)`; one-sided invariance is genuinely insufficient (the fibre `{0} × ℤ₂ × ℤ₃` is a closed
infinite proper subgroup mapped *into* itself by `σ₂`).

## Main statements

* `ambient_eq_top` — the rigidity theorem upstairs in `G₆`.
* `atom_of_invariant_periodic`, `periodic_iff_torsion`, `invariant_closed_subgroup_finite` — the
  three W13 targets.
* `torsionSub_finite`, `finite_periodicPoints`, `countable_periodicPoints` — the torsion sets.
* `T32_iter_sub_periodic` — the affine transfer.
* `torsion_of_atom_mem_limitMeasures`, `atoms_subset_periodicPoints` — the taxonomy applied to W4's
  limit measures.

## References

Plan A1+ §4 L11 and §7.2 W13; report-M7A1 Lemma A1.1.  The classification of closed subgroups of a
solenoid is classical ([EW11, Ch. 8], [Sch95]); the proof here is self-contained and axiom-free.
-/

namespace TH.S6

open Metric Set Filter Topology MeasureTheory

/-! ### Euler exponents

Two elementary sequences carry the whole geometric argument below: an exponent `E` with `3ᴱ`
`2`-adically close to `1` and `3`-adically close to `0`, and its mirror image with the roles of the
two primes exchanged.  Both come from Fermat–Euler, `qᶲ⁽ᵖⁿ⁾ ≡ 1 (mod pⁿ)`; multiplying the totient
by `n` makes the exponent itself grow, which is what makes the *other* place converge to `0`. -/

/-- `eulerExp p n = φ(pⁿ)·n`: an exponent which is `≥ n` and kills `q` modulo `pⁿ` for every `q`
coprime to `p`. -/
def eulerExp (p n : ℕ) : ℕ := Nat.totient (p ^ n) * n

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem self_le_eulerExp {p : ℕ} (hp : 0 < p) (n : ℕ) : n ≤ eulerExp p n :=
  Nat.le_mul_of_pos_left n (Nat.totient_pos.mpr (pow_pos hp n))

/-- **Fermat–Euler in the form used here**: `q^(eulerExp p n) ≡ 1 (mod pⁿ)`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem dvd_pow_eulerExp_sub_one {p q : ℕ} (h : Nat.Coprime q p) (n : ℕ) :
    ((p : ℤ) ^ n) ∣ ((q : ℤ) ^ eulerExp p n - 1) := by
  have h1 : q ^ Nat.totient (p ^ n) ≡ 1 [MOD p ^ n] := Nat.ModEq.pow_totient (h.pow_right n)
  have h2 : q ^ eulerExp p n ≡ 1 [MOD p ^ n] := by
    have := h1.pow n
    rwa [one_pow, ← pow_mul] at this
  have h3 := h2.dvd
  have : ((p : ℤ) ^ n) ∣ ((1 : ℤ) - (q : ℤ) ^ eulerExp p n) := by
    push_cast at h3 ⊢
    exact h3
  simpa using this.neg_right

/-! ### The two arithmetic sequences -/

/-- The `2`-adic Euler sequence `aₙ = 3^(eulerExp 2 n)`. -/
def eulerTwo (n : ℕ) : ℤ := 3 ^ eulerExp 2 n

/-- The `3`-adic Euler sequence `bₙ = 2^(eulerExp 3 n)`. -/
def eulerThree (n : ℕ) : ℤ := 2 ^ eulerExp 3 n

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem norm_eulerTwo_sub_one (n : ℕ) :
    ‖((eulerTwo n - 1 : ℤ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ n := by
  have hdvd : ((2 : ℤ) ^ n) ∣ (eulerTwo n - 1) := by
    simpa [eulerTwo] using dvd_pow_eulerExp_sub_one (p := 2) (q := 3) (by decide) n
  have := (Padic.norm_int_le_pow_iff_dvd (p := 2) (eulerTwo n - 1) n).mpr (by exact_mod_cast hdvd)
  calc ‖((eulerTwo n - 1 : ℤ) : ℚ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-n : ℤ) := this
    _ = (1 / 2 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]; norm_num

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem norm_eulerTwo_three (n : ℕ) : ‖((eulerTwo n : ℤ) : ℚ_[3])‖ ≤ (1 / 3 : ℝ) ^ n := by
  have hdvd : ((3 : ℤ) ^ n) ∣ eulerTwo n :=
    pow_dvd_pow_of_dvd (by norm_num) _ |>.trans (pow_dvd_pow 3 (self_le_eulerExp (by norm_num) n))
  have := (Padic.norm_int_le_pow_iff_dvd (p := 3) (eulerTwo n) n).mpr (by exact_mod_cast hdvd)
  calc ‖((eulerTwo n : ℤ) : ℚ_[3])‖ ≤ ((3 : ℕ) : ℝ) ^ (-n : ℤ) := this
    _ = (1 / 3 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]; norm_num

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem norm_eulerThree_sub_one (n : ℕ) :
    ‖((eulerThree n - 1 : ℤ) : ℚ_[3])‖ ≤ (1 / 3 : ℝ) ^ n := by
  have hdvd : ((3 : ℤ) ^ n) ∣ (eulerThree n - 1) := by
    simpa [eulerThree] using dvd_pow_eulerExp_sub_one (p := 3) (q := 2) (by decide) n
  have := (Padic.norm_int_le_pow_iff_dvd (p := 3) (eulerThree n - 1) n).mpr (by exact_mod_cast hdvd)
  calc ‖((eulerThree n - 1 : ℤ) : ℚ_[3])‖ ≤ ((3 : ℕ) : ℝ) ^ (-n : ℤ) := this
    _ = (1 / 3 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]; norm_num

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem norm_eulerThree_two (n : ℕ) : ‖((eulerThree n : ℤ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ n := by
  have hdvd : ((2 : ℤ) ^ n) ∣ eulerThree n :=
    pow_dvd_pow 2 (self_le_eulerExp (by norm_num) n)
  have := (Padic.norm_int_le_pow_iff_dvd (p := 2) (eulerThree n) n).mpr (by exact_mod_cast hdvd)
  calc ‖((eulerThree n : ℤ) : ℚ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-n : ℤ) := this
    _ = (1 / 2 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]; norm_num

private theorem tendsto_geom (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ c ^ n) :
    Tendsto f atTop (𝓝 0) :=
  squeeze_zero hf hle (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem tendsto_eulerTwo_two : Tendsto (fun n => ((eulerTwo n : ℤ) : ℚ_[2])) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_geom (1 / 2) (by norm_num) (by norm_num) (fun n => norm_nonneg _) fun n => ?_
  simpa using norm_eulerTwo_sub_one n

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem tendsto_eulerTwo_three : Tendsto (fun n => ((eulerTwo n : ℤ) : ℚ_[3])) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_geom (1 / 3) (by norm_num) (by norm_num) (fun n => norm_nonneg _) fun n => ?_
  simpa using norm_eulerTwo_three n

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem tendsto_eulerThree_three :
    Tendsto (fun n => ((eulerThree n : ℤ) : ℚ_[3])) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_geom (1 / 3) (by norm_num) (by norm_num) (fun n => norm_nonneg _) fun n => ?_
  simpa using norm_eulerThree_sub_one n

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem tendsto_eulerThree_two : Tendsto (fun n => ((eulerThree n : ℤ) : ℚ_[2])) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_geom (1 / 2) (by norm_num) (by norm_num) (fun n => norm_nonneg _) fun n => ?_
  simpa using norm_eulerThree_two n

/-! ### Closed `ℤ[1/6]`-stable subgroups of `G₆`

The geometric core of W13.  A closed subgroup `M ≤ G₆` which contains the lattice and is stable
under multiplication by `1/2` and `1/3` cannot contain a nonzero point of any one of the three
coordinate axes without being everything.  The three axes are linked by the Euler sequences: from
`(0, y, z) ∈ M` one gets `(0, y, 0)` and `(0, 0, z)` *separately*, because multiplying by `3ᴱ`
leaves the `2`-adic coordinate essentially fixed while contracting the `3`-adic one, and vice
versa.  No Pontryagin duality, no strong approximation, no Chinese remainder theorem. -/

section Ambient

variable {M : AddSubgroup G6}

/-- **Splitting the fibre, `3`-adic half.**  Multiplying by `3^(eulerExp 2 n)` fixes the `2`-adic
coordinate in the limit and kills the `3`-adic one. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem fiber_kill_three (hcl : IsClosed (M : Set G6)) {y : ℚ_[2]} {z : ℚ_[3]}
    (h : ((0 : ℝ), y, z) ∈ M) : ((0 : ℝ), y, (0 : ℚ_[3])) ∈ M := by
  have hmem : ∀ n : ℕ,
      (((0 : ℝ), ((eulerTwo n : ℤ) : ℚ_[2]) * y, ((eulerTwo n : ℤ) : ℚ_[3]) * z) : G6) ∈ M := by
    intro n
    have := AddSubgroup.zsmul_mem M h (eulerTwo n)
    simpa [Prod.smul_mk, zsmul_eq_mul] using this
  refine hcl.mem_of_tendsto (b := atTop) (f := fun n : ℕ =>
    (((0 : ℝ), ((eulerTwo n : ℤ) : ℚ_[2]) * y, ((eulerTwo n : ℤ) : ℚ_[3]) * z) : G6))
    ?_ (Eventually.of_forall hmem)
  refine tendsto_const_nhds.prodMk_nhds (Tendsto.prodMk_nhds ?_ ?_)
  · simpa using tendsto_eulerTwo_two.mul_const y
  · simpa using tendsto_eulerTwo_three.mul_const z

/-- **Splitting the fibre, `2`-adic half.** -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem fiber_kill_two (hcl : IsClosed (M : Set G6)) {y : ℚ_[2]} {z : ℚ_[3]}
    (h : ((0 : ℝ), y, z) ∈ M) : ((0 : ℝ), (0 : ℚ_[2]), z) ∈ M := by
  have hmem : ∀ n : ℕ,
      (((0 : ℝ), ((eulerThree n : ℤ) : ℚ_[2]) * y, ((eulerThree n : ℤ) : ℚ_[3]) * z) : G6) ∈ M := by
    intro n
    have := AddSubgroup.zsmul_mem M h (eulerThree n)
    simpa [Prod.smul_mk, zsmul_eq_mul] using this
  refine hcl.mem_of_tendsto (b := atTop) (f := fun n : ℕ =>
    (((0 : ℝ), ((eulerThree n : ℤ) : ℚ_[2]) * y, ((eulerThree n : ℤ) : ℚ_[3]) * z) : G6))
    ?_ (Eventually.of_forall hmem)
  refine tendsto_const_nhds.prodMk_nhds (Tendsto.prodMk_nhds ?_ ?_)
  · simpa using tendsto_eulerThree_two.mul_const y
  · simpa using tendsto_eulerThree_three.mul_const z

/-- Iterated halving inside `M`. -/
@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem smul_pow_mem {q : ℚ} (hq : ∀ g ∈ M, q • g ∈ M) (k : ℕ) {g : G6} (hg : g ∈ M) :
    (q ^ k) • g ∈ M := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hq _ ih

/-- **The `2`-adic axis is all-or-nothing.**  One nonzero point of `{0} × ℚ₂ × {0}` in a closed
`×(1/2)`-stable subgroup drags in the whole axis: integer multiples fill the ball of radius `‖y‖`
by density of `ℤ` in `ℤ₂`, and halving inflates the ball to all of `ℚ₂`. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem padicTwo_axis (hcl : IsClosed (M : Set G6))
    (hhalf : ∀ g ∈ M, ((2 : ℚ)⁻¹) • g ∈ M) {y : ℚ_[2]} (hy : y ≠ 0)
    (h : ((0 : ℝ), y, (0 : ℚ_[3])) ∈ M) : ∀ w : ℚ_[2], ((0 : ℝ), w, (0 : ℚ_[3])) ∈ M := by
  -- integer multiples of `y`, then their closure: the whole ball `ℤ₂ · y`
  have hball : ∀ c : ℤ_[2], (((0 : ℝ), (c : ℚ_[2]) * y, (0 : ℚ_[3])) : G6) ∈ M := by
    have hcont : Continuous (fun c : ℤ_[2] => (((0 : ℝ), (c : ℚ_[2]) * y, (0 : ℚ_[3])) : G6)) := by
      fun_prop
    have hT : IsClosed ((fun c : ℤ_[2] => (((0 : ℝ), (c : ℚ_[2]) * y, (0 : ℚ_[3])) : G6)) ⁻¹'
        (M : Set G6)) := hcl.preimage hcont
    have hsub : Set.range (Int.cast : ℤ → ℤ_[2]) ⊆
        (fun c : ℤ_[2] => (((0 : ℝ), (c : ℚ_[2]) * y, (0 : ℚ_[3])) : G6)) ⁻¹' (M : Set G6) := by
      rintro _ ⟨m, rfl⟩
      have := AddSubgroup.zsmul_mem M h m
      simpa [Prod.smul_mk, zsmul_eq_mul] using this
    have hall := closure_minimal hsub hT
    rw [PadicInt.denseRange_intCast.closure_range] at hall
    exact fun c => hall (Set.mem_univ c)
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · exact M.zero_mem
  -- scale `w` into that ball by a power of `2`, then halve back
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(2 : ℚ_[2]) ^ k * w‖ ≤ ‖y‖ := by
    have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
    have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hy0 hw0) (by norm_num : (2⁻¹ : ℝ) < 1)
    rw [lt_div_iff₀ hw0] at hk
    refine ⟨k, ?_⟩
    have hnp : ‖(2 : ℚ_[2]) ^ k * w‖ = (2⁻¹ : ℝ) ^ k * ‖w‖ := by
      rw [norm_mul, norm_pow]
      congr 2
      simpa using Padic.norm_p (p := 2)
    rw [hnp]
    linarith
  have hc : ‖(2 : ℚ_[2]) ^ k * w / y‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hy)]
    exact hk
  have hmem : (((0 : ℝ), (2 : ℚ_[2]) ^ k * w, (0 : ℚ_[3])) : G6) ∈ M := by
    have := hball ⟨(2 : ℚ_[2]) ^ k * w / y, hc⟩
    simpa [div_mul_cancel₀ _ hy] using this
  have hkey : (((2 : ℚ) ^ k)⁻¹) • ((2 : ℚ_[2]) ^ k * w) = w := by
    rw [Rat.smul_def]
    push_cast
    rw [inv_mul_cancel_left₀ (pow_ne_zero k (two_ne_zero))]
  have := smul_pow_mem hhalf k hmem
  simpa [Prod.smul_mk, hkey] using this

/-- **The `3`-adic axis is all-or-nothing.**  Mirror of `padicTwo_axis`. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem padicThree_axis (hcl : IsClosed (M : Set G6))
    (hthird : ∀ g ∈ M, ((3 : ℚ)⁻¹) • g ∈ M) {z : ℚ_[3]} (hz : z ≠ 0)
    (h : ((0 : ℝ), (0 : ℚ_[2]), z) ∈ M) : ∀ w : ℚ_[3], ((0 : ℝ), (0 : ℚ_[2]), w) ∈ M := by
  have hball : ∀ c : ℤ_[3], (((0 : ℝ), (0 : ℚ_[2]), (c : ℚ_[3]) * z) : G6) ∈ M := by
    have hcont : Continuous (fun c : ℤ_[3] => (((0 : ℝ), (0 : ℚ_[2]), (c : ℚ_[3]) * z) : G6)) := by
      fun_prop
    have hT : IsClosed ((fun c : ℤ_[3] => (((0 : ℝ), (0 : ℚ_[2]), (c : ℚ_[3]) * z) : G6)) ⁻¹'
        (M : Set G6)) := hcl.preimage hcont
    have hsub : Set.range (Int.cast : ℤ → ℤ_[3]) ⊆
        (fun c : ℤ_[3] => (((0 : ℝ), (0 : ℚ_[2]), (c : ℚ_[3]) * z) : G6)) ⁻¹' (M : Set G6) := by
      rintro _ ⟨m, rfl⟩
      have := AddSubgroup.zsmul_mem M h m
      simpa [Prod.smul_mk, zsmul_eq_mul] using this
    have hall := closure_minimal hsub hT
    rw [PadicInt.denseRange_intCast.closure_range] at hall
    exact fun c => hall (Set.mem_univ c)
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · exact M.zero_mem
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(3 : ℚ_[3]) ^ k * w‖ ≤ ‖z‖ := by
    have hz0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hz0 hw0) (by norm_num : (3⁻¹ : ℝ) < 1)
    rw [lt_div_iff₀ hw0] at hk
    refine ⟨k, ?_⟩
    have hnp : ‖(3 : ℚ_[3]) ^ k * w‖ = (3⁻¹ : ℝ) ^ k * ‖w‖ := by
      rw [norm_mul, norm_pow]
      congr 2
      simpa using Padic.norm_p (p := 3)
    rw [hnp]
    linarith
  have hc : ‖(3 : ℚ_[3]) ^ k * w / z‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hz)]
    exact hk
  have hmem : (((0 : ℝ), (0 : ℚ_[2]), (3 : ℚ_[3]) ^ k * w) : G6) ∈ M := by
    have := hball ⟨(3 : ℚ_[3]) ^ k * w / z, hc⟩
    simpa [div_mul_cancel₀ _ hz] using this
  have hkey : (((3 : ℚ) ^ k)⁻¹) • ((3 : ℚ_[3]) ^ k * w) = w := by
    rw [Rat.smul_def]
    push_cast
    rw [inv_mul_cancel_left₀ (pow_ne_zero k (three_ne_zero))]
  have := smul_pow_mem hthird k hmem
  simpa [Prod.smul_mk, hkey] using this

/-! #### From an axis to everything -/

/-- A rational in `ℤ[1/6]` which is archimedean-close to `t` and `3`-adically small: the dyadic
approximation of `t/3ⁿ`, multiplied back by `3ⁿ`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem exists_Z16_approx_two (t : ℝ) (n : ℕ) :
    ∃ q ∈ Z16, |(q : ℝ) - t| ≤ (3 / 4 : ℝ) ^ n ∧ ‖((q : ℚ) : ℚ_[3])‖ ≤ (1 / 3 : ℝ) ^ n := by
  set m : ℤ := ⌊t * 2 ^ (2 * n) / 3 ^ n⌋ with hm
  refine ⟨(m : ℚ) * 3 ^ n / 2 ^ (2 * n), ⟨m * 3 ^ (3 * n), 2 * n, ?_⟩, ?_, ?_⟩
  · push_cast
    rw [show (6 : ℚ) = 2 * 3 by norm_num, mul_pow]
    field_simp
    ring
  · have hkey : ((m : ℚ) * 3 ^ n / 2 ^ (2 * n) : ℚ) = (m : ℝ) * 3 ^ n / 2 ^ (2 * n) := by
      push_cast; ring
    rw [hkey]
    have hfl : |(m : ℝ) - t * 2 ^ (2 * n) / 3 ^ n| ≤ 1 := by
      rw [hm]
      have h1 := Int.floor_le (t * 2 ^ (2 * n) / 3 ^ n)
      have h2 := Int.lt_floor_add_one (t * 2 ^ (2 * n) / 3 ^ n)
      rw [abs_le]
      constructor <;> linarith
    have hsplit : (m : ℝ) * 3 ^ n / 2 ^ (2 * n) - t
        = (3 ^ n / 2 ^ (2 * n)) * ((m : ℝ) - t * 2 ^ (2 * n) / 3 ^ n) := by
      field_simp
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 ^ n / 2 ^ (2 * n))]
    calc (3 : ℝ) ^ n / 2 ^ (2 * n) * |(m : ℝ) - t * 2 ^ (2 * n) / 3 ^ n|
        ≤ 3 ^ n / 2 ^ (2 * n) * 1 := by
          exact mul_le_mul_of_nonneg_left hfl (by positivity)
      _ = (3 / 4 : ℝ) ^ n := by
          rw [mul_one, pow_mul, div_pow]
          norm_num
  · have h2 : ‖(2 : ℚ_[3])‖ = 1 := by
      simpa using (Padic.norm_natCast_eq_one_iff (p := 3) (n := 2)).mpr (by decide)
    have h3 : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by simpa using Padic.norm_p (p := 3)
    have hcast : (((m : ℚ) * 3 ^ n / 2 ^ (2 * n) : ℚ) : ℚ_[3])
        = (m : ℚ_[3]) * 3 ^ n / 2 ^ (2 * n) := by push_cast; ring
    rw [hcast, norm_div, norm_mul, norm_pow, norm_pow, h2, h3, one_pow, div_one]
    calc ‖(m : ℚ_[3])‖ * ((3 : ℝ)⁻¹) ^ n ≤ 1 * ((3 : ℝ)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (Padic.norm_int_le_one m) (by positivity)
      _ = (1 / 3 : ℝ) ^ n := by rw [one_mul, one_div]

/-- Mirror of `exists_Z16_approx_two`: archimedean-close to `t`, `2`-adically small. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem exists_Z16_approx_three (t : ℝ) (n : ℕ) :
    ∃ q ∈ Z16, |(q : ℝ) - t| ≤ (2 / 9 : ℝ) ^ n ∧ ‖((q : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ n := by
  set m : ℤ := ⌊t * 3 ^ (2 * n) / 2 ^ n⌋ with hm
  refine ⟨(m : ℚ) * 2 ^ n / 3 ^ (2 * n), ⟨m * 2 ^ (3 * n), 2 * n, ?_⟩, ?_, ?_⟩
  · push_cast
    rw [show (6 : ℚ) = 3 * 2 by norm_num, mul_pow]
    field_simp
    ring
  · have hkey : ((m : ℚ) * 2 ^ n / 3 ^ (2 * n) : ℚ) = (m : ℝ) * 2 ^ n / 3 ^ (2 * n) := by
      push_cast; ring
    rw [hkey]
    have hfl : |(m : ℝ) - t * 3 ^ (2 * n) / 2 ^ n| ≤ 1 := by
      rw [hm]
      have h1 := Int.floor_le (t * 3 ^ (2 * n) / 2 ^ n)
      have h2 := Int.lt_floor_add_one (t * 3 ^ (2 * n) / 2 ^ n)
      rw [abs_le]
      constructor <;> linarith
    have hsplit : (m : ℝ) * 2 ^ n / 3 ^ (2 * n) - t
        = (2 ^ n / 3 ^ (2 * n)) * ((m : ℝ) - t * 3 ^ (2 * n) / 2 ^ n) := by
      field_simp
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ n / 3 ^ (2 * n))]
    calc (2 : ℝ) ^ n / 3 ^ (2 * n) * |(m : ℝ) - t * 3 ^ (2 * n) / 2 ^ n|
        ≤ 2 ^ n / 3 ^ (2 * n) * 1 := mul_le_mul_of_nonneg_left hfl (by positivity)
      _ = (2 / 9 : ℝ) ^ n := by
          rw [mul_one, pow_mul, div_pow]
          norm_num
  · have h3 : ‖(3 : ℚ_[2])‖ = 1 := by
      simpa using (Padic.norm_natCast_eq_one_iff (p := 2) (n := 3)).mpr (by decide)
    have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by simpa using Padic.norm_p (p := 2)
    have hcast : (((m : ℚ) * 2 ^ n / 3 ^ (2 * n) : ℚ) : ℚ_[2])
        = (m : ℚ_[2]) * 2 ^ n / 3 ^ (2 * n) := by push_cast; ring
    rw [hcast, norm_div, norm_mul, norm_pow, norm_pow, h2, h3, one_pow, div_one]
    calc ‖(m : ℚ_[2])‖ * ((2 : ℝ)⁻¹) ^ n ≤ 1 * ((2 : ℝ)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (Padic.norm_int_le_one m) (by positivity)
      _ = (1 / 2 : ℝ) ^ n := by rw [one_mul, one_div]

/-- **The `2`-adic axis produces the real axis.**  Subtracting the lattice point `diag q` from the
axis point `(0, q, 0)` leaves `(q, 0, q)`; letting `q` run through rationals that approximate `t`
archimedean-ly and vanish `3`-adically gives `(t, 0, 0)` in the limit. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem real_axis_of_padicTwo (hcl : IsClosed (M : Set G6)) (hΔ : Δ₆ ≤ M)
    (h : ∀ w : ℚ_[2], ((0 : ℝ), w, (0 : ℚ_[3])) ∈ M) (t : ℝ) :
    ((t, (0 : ℚ_[2]), (0 : ℚ_[3])) : G6) ∈ M := by
  have hq : ∀ q ∈ Z16, (((q : ℝ), (0 : ℚ_[2]), ((q : ℚ_[3]))) : G6) ∈ M := by
    intro q hqZ
    have h1 : diag q ∈ M := hΔ (diag_mem_Δ₆ hqZ)
    have h2 : ((0 : ℝ), ((q : ℚ_[2])), (0 : ℚ_[3])) ∈ M := h _
    simpa [diag_apply, Prod.mk_sub_mk] using M.sub_mem h1 h2
  choose q hqZ hqR hqP using exists_Z16_approx_two t
  refine hcl.mem_of_tendsto (b := atTop)
    (f := fun n : ℕ => (((q n : ℝ), (0 : ℚ_[2]), ((q n : ℚ_[3]))) : G6))
    ?_ (Eventually.of_forall fun n => hq _ (hqZ n))
  refine Tendsto.prodMk_nhds ?_ (tendsto_const_nhds.prodMk_nhds ?_)
  · rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_geom (3 / 4) (by norm_num) (by norm_num) (fun n => dist_nonneg) fun n => ?_
    simpa [Real.dist_eq] using hqR n
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_geom (1 / 3) (by norm_num) (by norm_num) (fun n => norm_nonneg _) hqP

/-- Mirror of `real_axis_of_padicTwo`. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem real_axis_of_padicThree (hcl : IsClosed (M : Set G6)) (hΔ : Δ₆ ≤ M)
    (h : ∀ w : ℚ_[3], ((0 : ℝ), (0 : ℚ_[2]), w) ∈ M) (t : ℝ) :
    ((t, (0 : ℚ_[2]), (0 : ℚ_[3])) : G6) ∈ M := by
  have hq : ∀ q ∈ Z16, (((q : ℝ), ((q : ℚ_[2])), (0 : ℚ_[3])) : G6) ∈ M := by
    intro q hqZ
    have h1 : diag q ∈ M := hΔ (diag_mem_Δ₆ hqZ)
    have h2 : ((0 : ℝ), (0 : ℚ_[2]), ((q : ℚ_[3]))) ∈ M := h _
    simpa [diag_apply, Prod.mk_sub_mk] using M.sub_mem h1 h2
  choose q hqZ hqR hqP using exists_Z16_approx_three t
  refine hcl.mem_of_tendsto (b := atTop)
    (f := fun n : ℕ => (((q n : ℝ), ((q n : ℚ_[2])), (0 : ℚ_[3])) : G6))
    ?_ (Eventually.of_forall fun n => hq _ (hqZ n))
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ tendsto_const_nhds)
  · rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_geom (2 / 9) (by norm_num) (by norm_num) (fun n => dist_nonneg) fun n => ?_
    simpa [Real.dist_eq] using hqR n
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_geom (1 / 2) (by norm_num) (by norm_num) (fun n => norm_nonneg _) hqP

/-- **The real axis produces everything.**  `(0,1,1) = diag 1 - (1,0,0)` lies in `M`; the two Euler
sequences split it into `(0,1,0)` and `(0,0,1)`, and each axis then fills out. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem eq_top_of_real_axis (hcl : IsClosed (M : Set G6)) (hΔ : Δ₆ ≤ M)
    (hhalf : ∀ g ∈ M, ((2 : ℚ)⁻¹) • g ∈ M) (hthird : ∀ g ∈ M, ((3 : ℚ)⁻¹) • g ∈ M)
    (hreal : ∀ t : ℝ, ((t, (0 : ℚ_[2]), (0 : ℚ_[3])) : G6) ∈ M) : M = ⊤ := by
  have h011 : (((0 : ℝ), (1 : ℚ_[2]), (1 : ℚ_[3])) : G6) ∈ M := by
    have h1 : diag 1 ∈ M := hΔ (diag_mem_Δ₆ (Subring.one_mem _))
    have h2 := hreal (-1)
    simpa [diag_apply] using M.add_mem h1 h2
  have hax2 := padicTwo_axis hcl hhalf one_ne_zero (fiber_kill_three hcl h011)
  have hax3 := padicThree_axis hcl hthird one_ne_zero (fiber_kill_two hcl h011)
  refine (AddSubgroup.eq_top_iff' M).mpr fun g => ?_
  have hsum : g = (((g.1, (0 : ℚ_[2]), (0 : ℚ_[3])) : G6) + ((0, g.2.1, 0) : G6)
      + ((0, (0 : ℚ_[2]), g.2.2) : G6)) := by
    simp
  rw [hsum]
  exact M.add_mem (M.add_mem (hreal _) (hax2 _)) (hax3 _)

/-- **The ambient rigidity theorem** (the engine of `invariant_closed_subgroup_finite`).  A closed
`ℤ[1/6]`-stable subgroup of `G₆` containing the lattice and having *nonzero elements arbitrarily
close to the origin* is the whole group.  Two cases: if arbitrarily small elements with a nonzero
real coordinate exist, their integer multiples fill the real axis (integer multiples never increase
a `p`-adic norm); otherwise a small element sits in the fibre `{0} × ℚ₂ × ℚ₃` and the Euler
sequences pull it onto one of the two finite axes. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem ambient_eq_top (hcl : IsClosed (M : Set G6)) (hΔ : Δ₆ ≤ M)
    (hhalf : ∀ g ∈ M, ((2 : ℚ)⁻¹) • g ∈ M) (hthird : ∀ g ∈ M, ((3 : ℚ)⁻¹) • g ∈ M)
    (hsmall : ∀ ε > 0, ∃ g ∈ M, g ∉ Δ₆ ∧ |g.1| < ε ∧ ‖g.2.1‖ ≤ ε ∧ ‖g.2.2‖ ≤ ε) :
    M = ⊤ := by
  refine eq_top_of_real_axis hcl hΔ hhalf hthird ?_
  by_cases hflat : ∃ ε > 0, ∀ g ∈ M, |g.1| < ε → ‖g.2.1‖ ≤ ε → ‖g.2.2‖ ≤ ε → g.1 = 0
  · -- the fibre case
    obtain ⟨ε, hε, hz⟩ := hflat
    obtain ⟨g, hgM, hgΔ, h1, h2, h3⟩ := hsmall ε hε
    have hg1 : g.1 = 0 := hz g hgM h1 h2 h3
    have hgform : g = ((0 : ℝ), g.2.1, g.2.2) := by
      rw [← hg1]
    have hne : g.2.1 ≠ 0 ∨ g.2.2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hgΔ
      have : g = 0 := by
        rw [hgform, hcon.1, hcon.2]
        rfl
      rw [this]
      exact Δ₆.zero_mem
    rw [hgform] at hgM
    rcases hne with hy | hz'
    · exact real_axis_of_padicTwo hcl hΔ
        (padicTwo_axis hcl hhalf hy (fiber_kill_three hcl hgM))
    · exact real_axis_of_padicThree hcl hΔ
        (padicThree_axis hcl hthird hz' (fiber_kill_two hcl hgM))
  · -- the transverse case: small elements with nonzero real coordinate
    push Not at hflat
    intro t
    choose g hgM hg1 hg2 hg3 hg4 using fun n : ℕ => hflat (1 / (n + 1)) (by positivity)
    -- the integer multiple of `g n` that lands within `|g n|` of `t`
    have key : ∀ n : ℕ, ∃ k : ℤ, |(k : ℝ) * (g n).1 - t| ≤ |(g n).1| := by
      intro n
      refine ⟨⌊t / (g n).1⌋, ?_⟩
      have hgn : (g n).1 ≠ 0 := hg4 n
      have ha := Int.floor_le (t / (g n).1)
      have hb := Int.lt_floor_add_one (t / (g n).1)
      have hsplit : (⌊t / (g n).1⌋ : ℝ) * (g n).1 - t
          = (g n).1 * ((⌊t / (g n).1⌋ : ℝ) - t / (g n).1) := by
        field_simp
      have habs : |(⌊t / (g n).1⌋ : ℝ) - t / (g n).1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      rw [hsplit, abs_mul]
      nlinarith [abs_nonneg (g n).1, abs_nonneg ((⌊t / (g n).1⌋ : ℝ) - t / (g n).1)]
    choose m hmk using key
    have hmem : ∀ n : ℕ, (((m n : ℝ) * (g n).1, (m n : ℚ_[2]) * (g n).2.1,
        (m n : ℚ_[3]) * (g n).2.2) : G6) ∈ M := by
      intro n
      have heq : (((m n : ℝ) * (g n).1, (m n : ℚ_[2]) * (g n).2.1,
          (m n : ℚ_[3]) * (g n).2.2) : G6) = (m n) • g n := by
        simp [Prod.ext_iff, zsmul_eq_mul]
      rw [heq]
      exact AddSubgroup.zsmul_mem M (hgM n) (m n)
    refine hcl.mem_of_tendsto (b := atTop) (f := fun n : ℕ =>
      (((m n : ℝ) * (g n).1, (m n : ℚ_[2]) * (g n).2.1, (m n : ℚ_[3]) * (g n).2.2) : G6)) ?_
      (Eventually.of_forall hmem)
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
    · rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hzero
      rw [Real.dist_eq]
      exact le_trans (hmk n) (le_of_lt (abs_lt.mpr ⟨by linarith [(abs_lt.mp (hg1 n)).1],
        (abs_lt.mp (hg1 n)).2⟩ : |(g n).1| < 1 / ((n : ℝ) + 1)))
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hzero
      rw [norm_mul]
      calc ‖(m n : ℚ_[2])‖ * ‖(g n).2.1‖ ≤ 1 * ‖(g n).2.1‖ :=
            mul_le_mul_of_nonneg_right (Padic.norm_int_le_one _) (norm_nonneg _)
        _ = ‖(g n).2.1‖ := one_mul _
        _ ≤ 1 / ((n : ℝ) + 1) := hg2 n
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hzero
      rw [norm_mul]
      calc ‖(m n : ℚ_[3])‖ * ‖(g n).2.2‖ ≤ 1 * ‖(g n).2.2‖ :=
            mul_le_mul_of_nonneg_right (Padic.norm_int_le_one _) (norm_nonneg _)
        _ = ‖(g n).2.2‖ := one_mul _
        _ ≤ 1 / ((n : ℝ) + 1) := hg3 n

end Ambient

/-! ### Discrete subgroups of `Σ₆` are finite

`Σ₆` is compact, so a closed subgroup meeting one neighbourhood of `0` only at `0` is finite.  The
neighbourhood used throughout is the image of the box `(-(1/2)ᵏ, (1/2)ᵏ) × 2ᵏℤ₂ × 3ᵏℤ₃`. -/

/-- The image in `Σ₆` of the open box of size `(1/2)ᵏ` at all three places. -/
noncomputable def boxNbhd (k : ℕ) : Set S6 :=
  QuotientAddGroup.mk '' (Ioo (-((1 : ℝ) / 2) ^ k) (((1 : ℝ) / 2) ^ k) ×ˢ
    (Padic.residueBall 2 k 0 ×ˢ Padic.residueBall 3 k 0))

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem isOpen_boxNbhd (k : ℕ) : IsOpen (boxNbhd k) :=
  QuotientAddGroup.isOpenMap_coe _
    (isOpen_Ioo.prod ((Padic.isOpen_residueBall k 0).prod (Padic.isOpen_residueBall k 0)))

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem zero_mem_boxNbhd (k : ℕ) : (0 : S6) ∈ boxNbhd k := by
  have hpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ k := by positivity
  refine ⟨0, ⟨⟨neg_lt_zero.mpr hpos, hpos⟩, ?_, ?_⟩, rfl⟩
  · simp [Padic.mem_residueBall]
  · simp [Padic.mem_residueBall]

/-- Unpacking membership in the box: a representative small at all three places. -/
@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem exists_rep_of_mem_boxNbhd {k : ℕ} {x : S6} (hx : x ∈ boxNbhd k) :
    ∃ g : G6, QuotientAddGroup.mk g = x ∧ |g.1| < ((1 : ℝ) / 2) ^ k ∧
      ‖g.2.1‖ ≤ ((1 : ℝ) / 2) ^ k ∧ ‖g.2.2‖ ≤ ((1 : ℝ) / 2) ^ k := by
  obtain ⟨g, ⟨hg1, hg2, hg3⟩, rfl⟩ := hx
  refine ⟨g, rfl, abs_lt.mpr hg1, ?_, ?_⟩
  · have := (Padic.mem_residueBall (p := 2)).mp hg2
    rw [sub_zero] at this
    refine this.trans (le_of_eq ?_)
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    norm_num
  · have := (Padic.mem_residueBall (p := 3)).mp hg3
    rw [sub_zero] at this
    refine this.trans ?_
    have h1 : ((3 : ℕ) : ℝ) ^ (-k : ℤ) = ((1 : ℝ) / 3) ^ k := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]; norm_num
    rw [h1]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k

/-- **Compact plus discrete is finite.**  A closed subgroup of `Σ₆` isolated at the origin by one
box is finite. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem finite_of_boxNbhd_isolated (H : AddSubgroup S6) (hcl : IsClosed (H : Set S6)) (k : ℕ)
    (hiso : ∀ x ∈ H, x ∈ boxNbhd k → x = 0) : (H : Set S6).Finite := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hcl.isCompact
  haveI : DiscreteTopology H := by
    rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨boxNbhd k, isOpen_boxNbhd k, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => Subtype.ext (hiso x x.2 hx),
      fun hx => by rw [hx]; simpa using zero_mem_boxNbhd k⟩
  exact Set.finite_coe_iff.mp finite_of_compact_of_discrete

/-- Contrapositive: an infinite closed subgroup has nonzero elements in every box. -/
@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem exists_ne_zero_mem_boxNbhd {H : AddSubgroup S6} (hcl : IsClosed (H : Set S6))
    (hinf : ¬ (H : Set S6).Finite) (k : ℕ) : ∃ x ∈ H, x ≠ 0 ∧ x ∈ boxNbhd k := by
  by_contra hcon
  push Not at hcon
  refine hinf (finite_of_boxNbhd_isolated H hcl k fun x hx hb => ?_)
  by_contra hne
  exact hcon x hx hne hb

/-! ### Torsion in `Σ₆` -/

/-- Multiplication by an integer, as an endomorphism of `Σ₆`. -/
noncomputable def zsmulHom (m : ℤ) : S6 →+ S6 :=
  AddMonoidHom.mk' (fun x => m • x) (fun a b => smul_add m a b)

/-- The `m`-torsion subgroup of `Σ₆`. -/
noncomputable def torsionSub (m : ℤ) : AddSubgroup S6 := (zsmulHom m).ker

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem mem_torsionSub {m : ℤ} {x : S6} : x ∈ torsionSub m ↔ m • x = 0 :=
  AddMonoidHom.mem_ker

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem isClosed_torsionSub (m : ℤ) : IsClosed ((torsionSub m : AddSubgroup S6) : Set S6) := by
  have hc : Continuous (zsmulHom m) := continuous_zsmul m
  rw [torsionSub, AddMonoidHom.coe_ker]
  exact isClosed_singleton.preimage hc

/-- **The torsion sets are finite.**  If `m • x = 0` then a box representative `g` of `x` has
`m • g = diag r` with `r ∈ ℤ[1/6]` integral at both finite places, hence a rational integer of
absolute value `< 1`, hence `0`.  So the `m`-torsion is isolated at the origin, and `Σ₆` is
compact. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem torsionSub_finite {m : ℤ} (hm : m ≠ 0) :
    ((torsionSub m : AddSubgroup S6) : Set S6).Finite := by
  have hm0 : (0 : ℝ) < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hm0) (by norm_num : (1 / 2 : ℝ) < 1)
  refine finite_of_boxNbhd_isolated _ (isClosed_torsionSub m) k ?_
  intro x hx hbox
  have hx' : m • x = 0 := mem_torsionSub.mp hx
  obtain ⟨g, rfl, hg1, hg2, hg3⟩ := exists_rep_of_mem_boxNbhd hbox
  have hmg : (m • g : G6) ∈ Δ₆ := by
    have hmk : (QuotientAddGroup.mk (m • g) : S6) = m • (QuotientAddGroup.mk g : S6) := by
      simp only [← QuotientAddGroup.mk'_apply, map_zsmul]
    have : (QuotientAddGroup.mk (m • g) : S6) = 0 := by rw [hmk]; exact hx'
    exact (QuotientAddGroup.eq_zero_iff _).mp this
  obtain ⟨r, hrZ, hr⟩ := mem_Δ₆.mp hmg
  -- the three coordinates of `diag r = m • g`
  have hr1 : (r : ℝ) = (m : ℝ) * g.1 := congrArg (fun w : G6 => w.1) hr |>.trans (by simp)
  have hr2 : ((r : ℚ) : ℚ_[2]) = (m : ℚ_[2]) * g.2.1 :=
    congrArg (fun w : G6 => w.2.1) hr |>.trans (by simp)
  have hr3 : ((r : ℚ) : ℚ_[3]) = (m : ℚ_[3]) * g.2.2 :=
    congrArg (fun w : G6 => w.2.2) hr |>.trans (by simp)
  have hp2 : padicNorm 2 r ≤ 1 := by
    have : ‖((r : ℚ) : ℚ_[2])‖ ≤ 1 := by
      rw [hr2, norm_mul]
      calc ‖(m : ℚ_[2])‖ * ‖g.2.1‖ ≤ 1 * 1 :=
            mul_le_mul (Padic.norm_int_le_one m) (hg2.trans (by
              simpa using pow_le_one₀ (by norm_num) (by norm_num : (1/2:ℝ) ≤ 1)))
              (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    rw [Padic.eq_padicNorm] at this
    exact_mod_cast this
  have hp3 : padicNorm 3 r ≤ 1 := by
    have : ‖((r : ℚ) : ℚ_[3])‖ ≤ 1 := by
      rw [hr3, norm_mul]
      calc ‖(m : ℚ_[3])‖ * ‖g.2.2‖ ≤ 1 * 1 :=
            mul_le_mul (Padic.norm_int_le_one m) (hg3.trans (by
              simpa using pow_le_one₀ (by norm_num) (by norm_num : (1/2:ℝ) ≤ 1)))
              (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    rw [Padic.eq_padicNorm] at this
    exact_mod_cast this
  obtain ⟨n, rfl⟩ := exists_intCast_of_mem_Z16 hrZ hp2 hp3
  -- `|n| < 1`, so `n = 0`
  have hlt : |(n : ℝ)| < 1 := by
    have : |(n : ℝ)| = |(m : ℝ)| * |g.1| := by
      rw [show ((n : ℚ) : ℝ) = (n : ℝ) by push_cast; ring] at hr1
      rw [hr1, abs_mul]
    rw [this]
    have h1 : |g.1| < (|(m : ℝ)|)⁻¹ := lt_of_lt_of_le hg1 hk.le
    calc |(m : ℝ)| * |g.1| < |(m : ℝ)| * (|(m : ℝ)|)⁻¹ := by
          exact mul_lt_mul_of_pos_left h1 hm0
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hm0)
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs (by omega)
    linarith
  subst hn0
  -- hence `m • g = 0`, hence `g = 0`
  have hg0 : g = 0 := by
    have e1 : g.1 = 0 := by
      have : (0 : ℝ) = (m : ℝ) * g.1 := by simpa using hr1
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h (Int.cast_ne_zero.mpr hm)
      · exact h
    have e2 : g.2.1 = 0 := by
      have : (0 : ℚ_[2]) = (m : ℚ_[2]) * g.2.1 := by simpa using hr2
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h (Int.cast_ne_zero.mpr hm)
      · exact h
    have e3 : g.2.2 = 0 := by
      have : (0 : ℚ_[3]) = (m : ℚ_[3]) * g.2.2 := by simpa using hr3
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h (Int.cast_ne_zero.mpr hm)
      · exact h
    exact Prod.ext e1 (Prod.ext e2 e3)
  rw [hg0]
  simp

/-! ### The three W13 targets

`atom_of_invariant_periodic` (atoms of an invariant measure are periodic points),
`periodic_iff_torsion` (periodic points are the `3^π − 2^π` torsion) and
`invariant_closed_subgroup_finite` (proper closed `ℤ²`-invariant subgroups are finite). -/

/-- Iterating the diagonal upstairs. -/
@[category API, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem T32_iter_mk (g : G6) (π : ℕ) :
    T32^[π] (QuotientAddGroup.mk g) = QuotientAddGroup.mk ((((3 : ℚ) / 2) ^ π) • g) := by
  induction π with
  | zero => simp
  | succ π ih =>
      rw [Function.iterate_succ_apply', ih, T32_mk, smul_smul, ← pow_succ']

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem IsZ16Unit.pow {q : ℚ} (hq : IsZ16Unit q) (k : ℕ) : IsZ16Unit (q ^ k) where
  ne_zero := pow_ne_zero k hq.ne_zero
  mem := Subring.pow_mem _ hq.mem k
  inv_mem := by rw [← inv_pow]; exact Subring.pow_mem _ hq.inv_mem k

/-- Multiplying by a unit of `ℤ[1/6]` does not change membership in the lattice. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem smul_mem_Δ₆_iff {q : ℚ} (hq : IsZ16Unit q) (g : G6) : q • g ∈ Δ₆ ↔ g ∈ Δ₆ := by
  constructor
  · intro h
    have := Δ₆_le_comap hq.inv_mem h
    rw [AddSubgroup.mem_comap, smulHom_apply, smul_smul, inv_mul_cancel₀ hq.ne_zero,
      one_smul] at this
    exact this
  · intro h
    have := Δ₆_le_comap hq.mem h
    rwa [AddSubgroup.mem_comap, smulHom_apply] at this

/-- **W13 target 2: periodic ⟺ torsion.**  `T^π x = x` says `((3/2)^π − 1)x ∈ ℤ[1/6]`, and
multiplying by the unit `2^π` turns this into `(3^π − 2^π)x = 0`.  The period-`π` points are
therefore exactly the `(3^π − 2^π)`-torsion, an explicit finite set of points with odd
denominators — downstairs this is `Z32.cycle_point_eq`. -/
@[category research solved, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem periodic_iff_torsion (p : S6) (π : ℕ) :
    T32^[π] p = p ↔ ((3 : ℤ) ^ π - 2 ^ π) • p = 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective p
  have hscal : ((2 : ℚ) ^ π) * ((((3 : ℚ) / 2) ^ π) - 1) = (3 : ℚ) ^ π - 2 ^ π := by
    rw [mul_sub, mul_one, ← mul_pow]
    norm_num
  have hzs : (((3 : ℤ) ^ π - 2 ^ π) • g : G6)
      = ((2 : ℚ) ^ π) • (((((3 : ℚ) / 2) ^ π) - 1) • g) := by
    rw [smul_smul, hscal, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    ring_nf
  calc T32^[π] (QuotientAddGroup.mk g) = QuotientAddGroup.mk g
      ↔ ((((3 : ℚ) / 2) ^ π) - 1) • g ∈ Δ₆ := by
        rw [T32_iter_mk, QuotientAddGroup.eq_iff_sub_mem, sub_smul, one_smul]
    _ ↔ ((2 : ℚ) ^ π) • (((((3 : ℚ) / 2) ^ π) - 1) • g) ∈ Δ₆ :=
        (smul_mem_Δ₆_iff (isZ16Unit_two.pow π) _).symm
    _ ↔ ((3 : ℤ) ^ π - 2 ^ π) • (QuotientAddGroup.mk g : S6) = 0 := by
        rw [← hzs, ← QuotientAddGroup.eq_zero_iff]
        constructor
        · intro h
          rw [show ((3 : ℤ) ^ π - 2 ^ π) • (QuotientAddGroup.mk g : S6)
            = QuotientAddGroup.mk (((3 : ℤ) ^ π - 2 ^ π) • g) by
              simp only [← QuotientAddGroup.mk'_apply, map_zsmul]]
          exact h
        · intro h
          rw [show ((3 : ℤ) ^ π - 2 ^ π) • (QuotientAddGroup.mk g : S6)
            = QuotientAddGroup.mk (((3 : ℤ) ^ π - 2 ^ π) • g) by
              simp only [← QuotientAddGroup.mk'_apply, map_zsmul]] at h
          exact h

/-- Period-`π` points, `π > 0`, form a finite set. -/
@[category research solved, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem finite_periodicPoints {π : ℕ} (hπ : 0 < π) : {p : S6 | T32^[π] p = p}.Finite := by
  have hne : ((3 : ℤ) ^ π - 2 ^ π) ≠ 0 := by
    have : (2 : ℤ) ^ π < 3 ^ π := by
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num) hπ.ne'
    omega
  have hset : {p : S6 | T32^[π] p = p} = ((torsionSub ((3 : ℤ) ^ π - 2 ^ π) : AddSubgroup S6) :
      Set S6) := by
    ext p
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_torsionSub]
    exact periodic_iff_torsion p π
  rw [hset]
  exact torsionSub_finite hne

/-- The set of all periodic points is countable: a countable union of finite torsion sets. -/
@[category research solved, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem countable_periodicPoints : {p : S6 | ∃ π : ℕ, 0 < π ∧ T32^[π] p = p}.Countable := by
  have : {p : S6 | ∃ π : ℕ, 0 < π ∧ T32^[π] p = p} ⊆ ⋃ π : ℕ, {p : S6 | T32^[π + 1] p = p} := by
    rintro p ⟨π, hπ, hp⟩
    exact Set.mem_iUnion.mpr ⟨π - 1, by rwa [Nat.sub_add_cancel hπ]⟩
  exact Set.Countable.mono this
    (Set.countable_iUnion fun π => (finite_periodicPoints (Nat.succ_pos π)).countable)

/-- **W13 target 1: atoms of an invariant measure are periodic.**  An invariant measure gives every
point of an orbit the same mass, so an atom with an infinite forward orbit would carry infinite
mass. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "th_solenoid_defects"]
theorem atom_of_invariant_periodic {ν : Measure S6} [IsFiniteMeasure ν]
    (hν : Measure.map T32 ν = ν) {p : S6} (hp : 0 < ν {p}) :
    ∃ π : ℕ, 0 < π ∧ T32^[π] p = p := by
  have hmeas : Measurable (T32 : S6 → S6) := measurable_solAut isZ16Unit_threeHalves
  have hinj : Function.Injective (T32 : S6 → S6) := T32.injective
  have hstep : ∀ x : S6, ν {T32 x} = ν {x} := by
    intro x
    have h := congrArg (fun μ : Measure S6 => μ {T32 x}) hν
    rw [Measure.map_apply hmeas (measurableSet_singleton _)] at h
    rw [show (T32 : S6 → S6) ⁻¹' {T32 x} = {x} by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hy => hinj hy, fun hy => by rw [hy]⟩] at h
    exact h.symm
  have horbit : ∀ n : ℕ, ν {T32^[n] p} = ν {p} := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hstep]; exact ih
  by_contra hcon
  push Not at hcon
  have hiter_inj : ∀ k : ℕ, Function.Injective (T32^[k] : S6 → S6) := by
    intro k
    induction k with
    | zero => simpa using Function.injective_id
    | succ k ih => rw [Function.iterate_succ]; exact ih.comp hinj
  have horb_inj : Function.Injective (fun n : ℕ => T32^[n] p) := by
    intro i j hij
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · have : T32^[i] (T32^[j - i] p) = T32^[i] p := by
        rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
        exact hij.symm
      exact absurd (hiter_inj i this) (hcon (j - i) (by omega))
    · have hlt' : j < i := lt_of_le_of_ne hge (fun h => hne h.symm)
      have : T32^[j] (T32^[i - j] p) = T32^[j] p := by
        rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt'.le]
        exact hij
      exact absurd (hiter_inj j this) (hcon (i - j) (by omega))
  have hdisj : Pairwise (Function.onFun Disjoint (fun n : ℕ => ({T32^[n] p} : Set S6))) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_singleton]
    exact fun h => hij (horb_inj h)
  have hle : ν (⋃ n : ℕ, ({T32^[n] p} : Set S6)) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
  rw [measure_iUnion hdisj fun n => measurableSet_singleton _] at hle
  simp only [horbit] at hle
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt hp)] at hle
  exact absurd (top_le_iff.mp hle) (measure_ne_top ν Set.univ)

/-! #### Target 3: invariant closed subgroups -/

/-- The preimage in `G₆` of a subgroup of `Σ₆`. -/
noncomputable def lift (H : AddSubgroup S6) : AddSubgroup G6 :=
  H.comap (QuotientAddGroup.mk' Δ₆)

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem mem_lift {H : AddSubgroup S6} {g : G6} :
    g ∈ lift H ↔ (QuotientAddGroup.mk g : S6) ∈ H := Iff.rfl

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem Δ₆_le_lift (H : AddSubgroup S6) : Δ₆ ≤ lift H := by
  intro g hg
  rw [mem_lift, (QuotientAddGroup.eq_zero_iff g).mpr hg]
  exact H.zero_mem

@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem isClosed_lift {H : AddSubgroup S6} (hcl : IsClosed (H : Set S6)) :
    IsClosed ((lift H : AddSubgroup G6) : Set G6) := by
  rw [lift, AddSubgroup.coe_comap]
  exact hcl.preimage QuotientAddGroup.continuous_mk

/-- **W13 target 3, the one genuinely new lemma.**  A closed subgroup of `Σ₆` carried onto itself
by both `σ₂` and `σ₃` is either finite or everything.  Equivalently: *the only proper closed
`ℤ²`-invariant subgroups of `Σ₆` are the finite torsion sets*, so the "algebraic leaf" defect class
of L11 collapses.  The proof is `ambient_eq_top` applied to the preimage in `G₆`; two-sided
`σ`-invariance is what supplies the two halving hypotheses. -/
@[category research solved, AMS 11 22 37, ref "A1plus", group "th_solenoid_defects"]
theorem invariant_closed_subgroup_finite {H : AddSubgroup S6} (hcl : IsClosed (H : Set S6))
    (h2 : σ2 '' (H : Set S6) = H) (h3 : σ3 '' (H : Set S6) = H) (hne : H ≠ ⊤) :
    (H : Set S6).Finite := by
  by_contra hinf
  apply hne
  have hhalf : ∀ g ∈ lift H, ((2 : ℚ)⁻¹) • g ∈ lift H := by
    intro g hg
    have hx : (QuotientAddGroup.mk g : S6) ∈ σ2 '' (H : Set S6) := by rw [h2]; exact hg
    obtain ⟨y, hyH, hy⟩ := hx
    have hy' : y = QuotientAddGroup.mk (((2 : ℚ)⁻¹) • g) := by
      have := congrArg (fun t => σ2.symm t) hy
      simpa [σ2, solAut_symm_mk] using this
    rw [mem_lift, ← hy']
    exact hyH
  have hthird : ∀ g ∈ lift H, ((3 : ℚ)⁻¹) • g ∈ lift H := by
    intro g hg
    have hx : (QuotientAddGroup.mk g : S6) ∈ σ3 '' (H : Set S6) := by rw [h3]; exact hg
    obtain ⟨y, hyH, hy⟩ := hx
    have hy' : y = QuotientAddGroup.mk (((3 : ℚ)⁻¹) • g) := by
      have := congrArg (fun t => σ3.symm t) hy
      simpa [σ3, solAut_symm_mk] using this
    rw [mem_lift, ← hy']
    exact hyH
  have hsmall : ∀ ε > 0, ∃ g ∈ lift H, g ∉ Δ₆ ∧ |g.1| < ε ∧ ‖g.2.1‖ ≤ ε ∧ ‖g.2.2‖ ≤ ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨x, hxH, hx0, hxb⟩ := exists_ne_zero_mem_boxNbhd hcl hinf k
    obtain ⟨g, rfl, hg1, hg2, hg3⟩ := exists_rep_of_mem_boxNbhd hxb
    exact ⟨g, hxH, fun hgΔ => hx0 ((QuotientAddGroup.eq_zero_iff g).mpr hgΔ),
      hg1.trans hk, hg2.trans hk.le, hg3.trans hk.le⟩
  have htop := ambient_eq_top (isClosed_lift hcl) (Δ₆_le_lift H) hhalf hthird hsmall
  refine (AddSubgroup.eq_top_iff' H).mpr fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  have : g ∈ lift H := by rw [htop]; trivial
  exact this

/-- Every element of a finite subgroup is a torsion point: the finiteness of
`invariant_closed_subgroup_finite` really does say *torsion set*. -/
@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem exists_nsmul_eq_zero_of_finite {H : AddSubgroup S6} (hfin : (H : Set S6).Finite)
    {x : S6} (hx : x ∈ H) : ∃ m : ℕ, 0 < m ∧ m • x = 0 := by
  haveI : Finite H := Set.finite_coe_iff.mpr hfin
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨n • x, AddSubgroup.nsmul_mem H hx n⟩ : H))
  have heq' : i • x = j • x := congrArg Subtype.val heq
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨j - i, by omega, ?_⟩
    have hadd : (i + (j - i)) • x = i • x + (j - i) • x := add_nsmul x i (j - i)
    rw [Nat.add_sub_cancel' hlt.le, ← heq'] at hadd
    have hz : i • x + (0 : S6) = i • x + (j - i) • x := by rw [add_zero]; exact hadd
    exact (add_left_cancel hz).symm
  · have hlt' : j < i := lt_of_le_of_ne hge (fun h => hij h.symm)
    refine ⟨i - j, by omega, ?_⟩
    have hadd : (j + (i - j)) • x = j • x + (i - j) • x := add_nsmul x j (i - j)
    rw [Nat.add_sub_cancel' hlt'.le, heq'] at hadd
    have hz : j • x + (0 : S6) = j • x + (i - j) • x := by rw [add_zero]; exact hadd
    exact (add_left_cancel hz).symm

/-! #### Sharpness: the finite torsion subgroups really are invariant and proper -/

/-- Every torsion subgroup is carried onto itself by every `ℤ[1/6]`-unit automorphism. -/
@[category API, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem solAut_image_torsionSub {q : ℚ} (hq : IsZ16Unit q) (m : ℤ) :
    (solAut hq) '' ((torsionSub m : AddSubgroup S6) : Set S6) = (torsionSub m : Set S6) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (solAut hq) y ∈ torsionSub m
    rw [mem_torsionSub, ← map_zsmul, mem_torsionSub.mp hy, map_zero]
  · intro hx
    refine ⟨(solAut hq).symm x, ?_, by simp⟩
    show (solAut hq).symm x ∈ torsionSub m
    rw [mem_torsionSub, ← map_zsmul, mem_torsionSub.mp hx, map_zero]

/-- A nonzero torsion subgroup is proper: `Σ₆` is infinite because the winding line is injective. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem torsionSub_ne_top {m : ℤ} (hm : m ≠ 0) : (torsionSub m : AddSubgroup S6) ≠ ⊤ := by
  intro h
  have hfin : (Set.univ : Set S6).Finite := by
    have := torsionSub_finite hm
    rwa [h, AddSubgroup.coe_top] at this
  exact Set.infinite_range_of_injective wind_injective (hfin.subset (Set.subset_univ _))

@[category API, AMS 11, ref "A1plus", group "th_solenoid_defects"]
theorem five_inv_notMem_Z16 : ((1 : ℚ) / 5) ∉ Z16 := by
  rintro ⟨a, k, hk⟩
  have hq : (6 : ℚ) ^ k = 5 * a := by
    field_simp at hk
    linarith
  have hz : (6 : ℤ) ^ k = 5 * a := by exact_mod_cast hq
  have hdvd : (5 : ℤ) ∣ 6 ^ k := ⟨a, hz⟩
  have hp : Prime (5 : ℤ) := by norm_num
  have := hp.dvd_of_dvd_pow hdvd
  norm_num at this

/-- **Sharpness of `invariant_closed_subgroup_finite`.**  The `5`-torsion of `Σ₆` is a *nonzero*
finite proper subgroup carried onto itself by both `σ₂` and `σ₃`: the conclusion "finite" cannot be
improved to "trivial", and the hypothesis class is not empty. -/
@[category research solved, AMS 11 22, ref "A1plus", group "th_solenoid_defects"]
theorem exists_nontrivial_invariant_closed_subgroup :
    ∃ H : AddSubgroup S6, IsClosed (H : Set S6) ∧ σ2 '' (H : Set S6) = H ∧
      σ3 '' (H : Set S6) = H ∧ H ≠ ⊤ ∧ H ≠ ⊥ ∧ (H : Set S6).Finite := by
  refine ⟨torsionSub 5, isClosed_torsionSub 5, solAut_image_torsionSub isZ16Unit_two 5,
    solAut_image_torsionSub isZ16Unit_three 5, torsionSub_ne_top (by norm_num), ?_,
    torsionSub_finite (by norm_num)⟩
  -- the class of `diag (1/5)` is a nonzero `5`-torsion point
  have hne : (QuotientAddGroup.mk (diag ((1 : ℚ) / 5)) : S6) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    obtain ⟨r, hr, hrq⟩ := mem_Δ₆.mp h
    have hreal := congrArg (fun w : G6 => w.1) hrq
    simp only [diag_apply] at hreal
    have : r = (1 : ℚ) / 5 := by exact_mod_cast hreal
    exact five_inv_notMem_Z16 (this ▸ hr)
  have hmem : (QuotientAddGroup.mk (diag ((1 : ℚ) / 5)) : S6) ∈ torsionSub 5 := by
    rw [mem_torsionSub, show ((5 : ℤ) • (QuotientAddGroup.mk (diag ((1 : ℚ) / 5)) : S6))
      = QuotientAddGroup.mk ((5 : ℤ) • diag ((1 : ℚ) / 5)) by
        simp only [← QuotientAddGroup.mk'_apply, map_zsmul]]
    rw [← map_zsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      (diag_mem_Δ₆ (by norm_num : ((5 : ℤ) • ((1 : ℚ) / 5)) ∈ Z16))
  intro hbot
  rw [hbot, AddSubgroup.mem_bot] at hmem
  exact hne hmem

/-! ### Consequences for the defect taxonomy -/

/-- **The affine transfer** (L11(i)).  `T` is a group automorphism, so at a `T^π`-fixed point the
dynamics is exactly the dynamics at the origin, translated: every statement proved at `0` transfers
verbatim to every periodic point. -/
@[category API, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem T32_iter_sub (π : ℕ) (x y : S6) : T32^[π] (x - y) = T32^[π] x - T32^[π] y := by
  induction π generalizing x y with
  | zero => simp
  | succ π ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        ← ih]
      congr 1
      exact map_sub T32 x y

@[category research solved, AMS 11 37, ref "A1plus", group "th_solenoid_defects"]
theorem T32_iter_sub_periodic {p : S6} {π : ℕ} (hp : T32^[π] p = p) (x : S6) :
    T32^[π] x - p = T32^[π] (x - p) := by
  rw [T32_iter_sub, hp]

/-- **The atomic defect class is torsion.**  Every atom of every limit measure of the orbit of
`ξ` is a periodic point, hence a `(3^π − 2^π)`-torsion point of `Σ₆`.  Combined with
`finite_periodicPoints` and `countable_periodicPoints`, the atomic part of any limit measure is
carried by an explicit countable set of rationals with odd denominators. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "th_solenoid_defects"]
theorem torsion_of_atom_mem_limitMeasures {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) {p : S6} (hp : 0 < (ν : Measure S6) {p}) :
    ∃ π : ℕ, 0 < π ∧ ((3 : ℤ) ^ π - 2 ^ π) • p = 0 := by
  obtain ⟨π, hπ, hper⟩ := atom_of_invariant_periodic (map_T32_of_mem_limitMeasures hν) hp
  exact ⟨π, hπ, (periodic_iff_torsion p π).mp hper⟩

/-- The atoms of a limit measure lie in the countable set of periodic points. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "th_solenoid_defects"]
theorem atoms_subset_periodicPoints {ξ : ℝ} {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) :
    {p : S6 | 0 < (ν : Measure S6) {p}} ⊆ {p : S6 | ∃ π : ℕ, 0 < π ∧ T32^[π] p = p} := by
  intro p hp
  exact atom_of_invariant_periodic (map_T32_of_mem_limitMeasures hν) hp

end TH.S6
