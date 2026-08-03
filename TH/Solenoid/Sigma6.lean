/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TH.Solenoid.StrongApprox
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The solenoid `Σ₆`, its `ℤ²`-action, and the diagonal `×3/2`

The compact group `Σ₆ = (ℝ × ℚ₂ × ℚ₃) / ℤ[1/6]` (plan-A1+, §2.1, work package W1) is the natural
extension of Furstenberg's `×2, ×3` system: the two commuting automorphisms `σ₂, σ₃` generate a
genuine `ℤ²`-action, and the object of study is their **diagonal**
`T = σ₃ ∘ σ₂⁻¹ = ×(3/2)`, evaluated along the winding line `ξ ↦ [(ξ, 0, 0)]`, where it produces
exactly the orbit `(3/2)ⁿ ξ`:

`T32_iter_wind : T32^[n] (wind ξ) = wind (ξ * (3/2)ⁿ)`.

Everything topological comes out of `StrongApprox.lean` and instance search:

* **Compactness** is *not* inherited from the ambient group — `G₆` is not compact.  It comes from
  the fundamental domain: `Σ₆` is the continuous image of the compact box `[0,1] × ℤ₂ × ℤ₃`
  (`mk_image_Dcl`, `instCompactSpaceS6`).
* **Hausdorffness** comes from discreteness of the lattice, via
  `QuotientAddGroup.instT1Space`/`instT3Space` and the `IsClosed Δ₆` instance of the previous file.
* **Metrizability** (`metrizableSpace_S6`) is then free — second countability plus `T3` and
  Urysohn.  No invariant metric has to be built by hand.
* The **measurable** structure is *inherited*, not declared: `QuotientAddGroup.measurableSpace`
  (= `Quotient.instMeasurableSpace`, the pushforward σ-algebra) fires for the spelling
  `G₆ ⧸ Δ₆`, and `QuotientAddGroup.borelSpace` — Polish group modulo a closed normal subgroup —
  proves it *is* the Borel σ-algebra (`borelSpace_S6`).  This is Mathlib's own `AddCircle` pattern.
  Declaring `borel _` here instead would create a genuine σ-algebra diamond and would put `Σ₆`
  outside `Mathlib/MeasureTheory/Measure/Haar/Quotient.lean`, whose `…MeasureEqMeasurePreimage`
  layer is stated for the pushforward σ-algebra (it takes no `MeasurableSpace (G ⧸ Γ)` variable).

The automorphisms are produced uniformly: a rational `q` which is a *unit* of `ℤ[1/6]`
(`IsZ16Unit`) acts on `G₆` by multiplication, preserves the lattice, and therefore descends to a
topological group automorphism `solAut` of `Σ₆`.  `σ₂ = ×2`, `σ₃ = ×3` and `T = ×(3/2)` are the
three instances used, and the same construction gives `σ₂⁻¹`, `σ₃⁻¹` for free.

The last statement, `eq_zero_of_T32_eq_self`, is the fixed-point lemma: `T` has **no** fixed point
except `0`, because `T x = x` forces `(1/2) x = 0` and `×(1/2)` is an automorphism.  It is the
input to the "no Dirac limit measure away from `0`" rung (plan-A1+ L4/A13).

## Main statements

* `instCompactSpaceS6`, `metrizableSpace_S6`, `borelSpace_S6` — the group `Σ₆` is a compact,
  metrizable, second-countable Borel group.
* `solAut`, `σ2`, `σ3`, `T32` — the `ℤ²`-action and its diagonal; `σ2_comm_σ3`,
  `T32_eq_σ3_trans_σ2_symm`.
* `wind`, `T32_iter_wind`, `wind_injective` — the winding line and the `(3/2)ⁿ` orbit.
* `eq_zero_of_T32_eq_self` — the only fixed point of `T` is `0`.

## References

Plan A1+ §2.1.  For the general theory of solenoids as algebraic dynamical systems see
[EW11, Ch. 8] and [Sch95]; nothing beyond the elementary construction is used here.
-/

namespace TH.S6

open Metric Set

set_option linter.dupNamespace false in
/-- The solenoid `Σ₆ = (ℝ × ℚ₂ × ℚ₃) / ℤ[1/6]`. -/
abbrev S6 : Type := G6 ⧸ Δ₆

/-! ### The compact group structure -/

/-- Every point of `Σ₆` is represented in the compact box `Dcl = [0,1] × ℤ₂ × ℤ₃`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem mk_image_Dcl : (QuotientAddGroup.mk '' Dcl : Set S6) = Set.univ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨d, hd, hmem⟩ := exists_mem_Dcl_sub_mem_Δ₆ g
  refine ⟨d, hd, ?_⟩
  rw [QuotientAddGroup.eq]
  simpa [neg_add_eq_sub] using hmem

/-- **`Σ₆` is compact.**  Note that the ambient group `G₆` is *not* compact: compactness of the
quotient is exactly the statement that the lattice `Δ₆` is cocompact, and it comes from the
fundamental domain, not from any instance of `QuotientAddGroup`. -/
instance instCompactSpaceS6 : CompactSpace S6 :=
  ⟨by rw [← mk_image_Dcl]; exact isCompact_Dcl.image QuotientAddGroup.continuous_mk⟩

/-- `Σ₆` is metrizable: it is `T3` (the lattice is closed) and second countable, so Urysohn
applies.  No invariant metric needs to be constructed by hand. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem metrizableSpace_S6 : TopologicalSpace.MetrizableSpace S6 := inferInstance

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem t2Space_S6 : T2Space S6 := inferInstance

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem secondCountable_S6 : SecondCountableTopology S6 := inferInstance

/-- **`Σ₆` is a Borel space for the σ-algebra it already has.**  The measurable structure is
*not* declared here: `QuotientAddGroup.measurableSpace` (the pushforward σ-algebra, which is
`Quotient.instMeasurableSpace` under another name) fires for the spelling `G₆ ⧸ Δ₆`, and it *is*
the Borel σ-algebra — `QuotientAddGroup.borelSpace` proves exactly that for a quotient of a Polish
group by a closed normal subgroup, which `Δ₆ ⊆ G₆` is.  This is also what Mathlib does for
`AddCircle` (`MeasureSpace (AddCircle T)` is built on `QuotientAddGroup.measurableSpace _`).
Declaring `borel _` on top of it would create a σ-algebra diamond and, worse, put `Σ₆` outside the
`AddQuotientMeasureEqMeasurePreimage` machinery, which is stated for the pushforward σ-algebra. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem borelSpace_S6 : BorelSpace S6 := inferInstance

/-! ### Multiplication by a unit of `ℤ[1/6]` -/

/-- `q` is a unit of the ring `ℤ[1/6]`: `q ≠ 0` and both `q` and `q⁻¹` lie in `ℤ[1/6]`.  Exactly
these rationals induce automorphisms of `Σ₆`. -/
structure IsZ16Unit (q : ℚ) : Prop where
  ne_zero : q ≠ 0
  mem : q ∈ Z16
  inv_mem : q⁻¹ ∈ Z16

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem IsZ16Unit.inv {q : ℚ} (hq : IsZ16Unit q) : IsZ16Unit q⁻¹ :=
  ⟨inv_ne_zero hq.ne_zero, hq.inv_mem, by rw [inv_inv]; exact hq.mem⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem isZ16Unit_two : IsZ16Unit 2 :=
  ⟨by norm_num, ⟨2, 0, by norm_num⟩, ⟨3, 1, by norm_num⟩⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem isZ16Unit_three : IsZ16Unit 3 :=
  ⟨by norm_num, ⟨3, 0, by norm_num⟩, ⟨2, 1, by norm_num⟩⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem isZ16Unit_threeHalves : IsZ16Unit (3 / 2) :=
  ⟨by norm_num, ⟨9, 1, by norm_num⟩, ⟨4, 1, by norm_num⟩⟩

/-- Multiplication by a rational on `G₆`, as an additive endomorphism. -/
noncomputable def smulHom (q : ℚ) : G6 →+ G6 :=
  AddMonoidHom.mk' (fun g => q • g) (smul_add q)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem smulHom_apply (q : ℚ) (g : G6) : smulHom q g = q • g := rfl

/-- Multiplication is `ℚ`-linear along the diagonal: `q • (r, r, r) = (qr, qr, qr)`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem smul_diag (q r : ℚ) : q • diag r = diag (q * r) := by
  simp only [diag_apply, Prod.smul_mk, Rat.smul_def]
  push_cast
  rfl

/-- Multiplication by an element of `ℤ[1/6]` maps the lattice into itself. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem Δ₆_le_comap {q : ℚ} (hq : q ∈ Z16) : Δ₆ ≤ AddSubgroup.comap (smulHom q) Δ₆ := by
  rintro g hg
  obtain ⟨r, hr, rfl⟩ := mem_Δ₆.mp hg
  refine AddSubgroup.mem_comap.mpr ?_
  rw [smulHom_apply, smul_diag]
  exact diag_mem_Δ₆ (Subring.mul_mem _ hq hr)

/-- **The automorphism of `Σ₆` induced by a unit of `ℤ[1/6]`.**  Multiplication by `q` on `G₆`
preserves the lattice in both directions, hence descends to a topological group automorphism. -/
noncomputable def solAut {q : ℚ} (hq : IsZ16Unit q) : S6 ≃ₜ+ S6 where
  toAddEquiv :=
    { toFun := QuotientAddGroup.map Δ₆ Δ₆ (smulHom q) (Δ₆_le_comap hq.mem)
      invFun := QuotientAddGroup.map Δ₆ Δ₆ (smulHom q⁻¹) (Δ₆_le_comap hq.inv_mem)
      left_inv := by
        rintro ⟨g⟩
        show (QuotientAddGroup.mk (q⁻¹ • (q • g)) : S6) = QuotientAddGroup.mk g
        rw [smul_smul, inv_mul_cancel₀ hq.ne_zero, one_smul]
      right_inv := by
        rintro ⟨g⟩
        show (QuotientAddGroup.mk (q • (q⁻¹ • g)) : S6) = QuotientAddGroup.mk g
        rw [smul_smul, mul_inv_cancel₀ hq.ne_zero, one_smul]
      map_add' := map_add _ }
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk Δ₆).continuous_iff]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const_smul q)
  continuous_invFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk Δ₆).continuous_iff]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const_smul q⁻¹)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem solAut_mk {q : ℚ} (hq : IsZ16Unit q) (g : G6) :
    solAut hq (QuotientAddGroup.mk g) = QuotientAddGroup.mk (q • g) := rfl

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem solAut_symm_mk {q : ℚ} (hq : IsZ16Unit q) (g : G6) :
    (solAut hq).symm (QuotientAddGroup.mk g) = QuotientAddGroup.mk (q⁻¹ • g) := rfl

/-! ### The `ℤ²`-action and its diagonal -/

/-- `σ₂ = ×2`, one generator of the `ℤ²`-action. -/
noncomputable def σ2 : S6 ≃ₜ+ S6 := solAut isZ16Unit_two

/-- `σ₃ = ×3`, the other generator of the `ℤ²`-action. -/
noncomputable def σ3 : S6 ≃ₜ+ S6 := solAut isZ16Unit_three

/-- The diagonal `T = σ₃ ∘ σ₂⁻¹ = ×(3/2)`, the automorphism whose orbits are the object of
study. -/
noncomputable def T32 : S6 ≃ₜ+ S6 := solAut isZ16Unit_threeHalves

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem σ2_mk (g : G6) : σ2 (QuotientAddGroup.mk g) = QuotientAddGroup.mk ((2 : ℚ) • g) := rfl

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem σ3_mk (g : G6) : σ3 (QuotientAddGroup.mk g) = QuotientAddGroup.mk ((3 : ℚ) • g) := rfl

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem T32_mk (g : G6) :
    T32 (QuotientAddGroup.mk g) = QuotientAddGroup.mk ((3 / 2 : ℚ) • g) := rfl

/-- **The two generators commute**: `Σ₆` carries a genuine `ℤ²`-action, the natural extension of
Furstenberg's `×2, ×3`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem σ2_comm_σ3 (x : S6) : σ2 (σ3 x) = σ3 (σ2 x) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [σ2_mk, σ3_mk, smul_smul]
  norm_num

/-- **The diagonal is `σ₃` followed by `σ₂⁻¹`.** -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem T32_eq_σ3_trans_σ2_symm (x : S6) : T32 x = σ2.symm (σ3 x) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  show _ = (solAut isZ16Unit_two).symm _
  rw [σ3_mk, solAut_symm_mk, T32_mk, smul_smul]
  norm_num

/-- The same statement for the bundled automorphisms: `T = σ₂⁻¹ ∘ σ₃`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem T32_eq : T32 = σ3.trans σ2.symm := by
  ext x
  exact T32_eq_σ3_trans_σ2_symm x

/-! ### The winding line -/

/-- The winding line `ξ ↦ [(ξ, 0, 0)]`: the image of `ℝ` in `Σ₆`, along which the `×(3/2)`-orbit
is the sequence `(3/2)ⁿ ξ`. -/
noncomputable def wind (ξ : ℝ) : S6 := QuotientAddGroup.mk (ξ, 0, 0)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem T32_wind (ξ : ℝ) : T32 (wind ξ) = wind (3 / 2 * ξ) := by
  rw [wind, T32_mk]
  congr 1
  simp [Prod.smul_mk, Rat.smul_def]

/-- **The orbit of the winding line is `(3/2)ⁿ ξ`.**  This is the identity that makes `Σ₆` the
right home for the problem: the arithmetic sequence `(3/2)ⁿ ξ` *is* the orbit of one point under
one automorphism of one compact group. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem T32_iter_wind (ξ : ℝ) (n : ℕ) : T32^[n] (wind ξ) = wind (ξ * (3 / 2) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, T32_wind]
    ring_nf

/-- **The winding line is injective.**  Distinct reals give distinct points of `Σ₆`: an element of
`Δ₆` with vanishing `2`-adic coordinate is `0`.  So the orbit `T^[n] (wind ξ)` is a genuine copy of
the sequence `(3/2)ⁿ ξ` and nothing is collapsed by passing to the solenoid. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem wind_injective : Function.Injective wind := by
  intro ξ η h
  rw [wind, wind, QuotientAddGroup.eq] at h
  obtain ⟨r, hr, hrg⟩ := mem_Δ₆.mp h
  have h1 := congrArg (fun g : G6 => g.1) hrg
  have h2 := congrArg (fun g : G6 => g.2.1) hrg
  simp only [diag_apply, Prod.fst_add, Prod.fst_neg, Prod.snd_add, Prod.snd_neg, neg_zero,
    add_zero] at h1 h2
  have hr0 : r = 0 := by exact_mod_cast h2
  rw [hr0] at h1
  simp only [Rat.cast_zero] at h1
  linarith

/-! ### Fixed points -/

/-- **The only fixed point of the diagonal is the origin.**  `T x = x` says `(1/2) x = 0`, and
multiplication by `1/2` is an automorphism of `Σ₆` because `2` is a unit of `ℤ[1/6]`.  (Contrast
the individual generators: `σ₂` and `σ₃` have plenty of fixed points, e.g. all of the finite
`(q-1)`-torsion.)  This is the input to the "no Dirac limit measure away from `0`" rung. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_sigma6"]
theorem eq_zero_of_T32_eq_self (x : S6) (h : T32 x = x) : x = 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [T32_mk, QuotientAddGroup.eq] at h
  obtain ⟨r, hr, hrg⟩ := mem_Δ₆.mp h
  have hhalf : (-1 / 2 : ℚ) • g = diag r := by
    rw [hrg, neg_add_eq_sub]
    rw [show (-1 / 2 : ℚ) = 1 - 3 / 2 by norm_num, sub_smul, one_smul]
  have hg : g = diag ((-2 : ℚ) * r) := by
    rw [← smul_diag, ← hhalf, smul_smul]
    norm_num
  rw [QuotientAddGroup.eq_zero_iff, hg]
  exact diag_mem_Δ₆ (Subring.mul_mem _ ⟨-2, 0, by norm_num⟩ hr)

end TH.S6
