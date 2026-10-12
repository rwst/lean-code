import B3.HeightVsRate
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.LinearAlgebra.Dual.Defs
import CITED.SubspaceTheorem
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Function Height Height.AdmissibleAbsValues Filter

/-- **Theorem E of [AB07] over `ℚ`** (the Subspace Theorem in Evertse's form, all places, in
Mathlib's height normalisation): the nonzero `x ∈ ℚᵐ` with
`∏_{v∈S} ∏ᵢ |Lᵢ,ᵥ(x)|ᵥ / |x|ᵥ ≤ H(x)^{−m−ε}` lie in finitely many proper subspaces.  Formerly the
cited axiom `AB.subspace_theorem_E`; now `Subspace.evertseSchlickewei`, whose place hypothesis is
`hS_place`.  Neither `S ⊇ archAbsVal` nor `ε < 1` is needed. -/
@[category research solved, AMS 11, ref "Eve96" "Sch76" "Sch77" "AB07", group "ab_subspace_theorem"]
theorem subspace_theorem_E {m : ℕ} (hm : 2 ≤ m) (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v)) (ε : ℝ) (hε : 0 < ε) :
    ∃ W : Finset (Submodule ℚ (Fin m → ℚ)), (∀ U ∈ W, U ≠ ⊤) ∧
      ∀ x : Fin m → ℚ, x ≠ 0 →
        (∏ v ∈ S, ∏ i : Fin m, v ((L v i) x) / (⨆ j, v (x j))) ≤
          Height.mulHeight x ^ (-(m : ℝ) - ε) →
        ∃ U ∈ W, x ∈ U :=
  Subspace.evertseSchlickewei hm S (fun v hv ↦ Subspace.isPlace_of_mem_admissible (hS_place v hv))
    L hL ε hε

@[category API, AMS 11 37, ref "Eve96" "AB07"]
def Confinable {m : ℕ} (x : ℕ → (Fin m → ℚ)) : Prop :=
  ∃ U : Submodule ℚ (Fin m → ℚ), U ≠ ⊤ ∧ {k | x k ∈ U}.Infinite

@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_pigeonhole {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0)
    (hineq : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε)) :
    Confinable x := by
  obtain ⟨W, hWtop, hWcov⟩ := subspace_theorem_E hm S hS_place L hL ε hε
  have hmem : ∀ k, ∃ U, U ∈ W ∧ x k ∈ U := fun k => hWcov (x k) (hx0 k) (hineq k)
  choose g hgW hgmem using hmem
  obtain ⟨U₀, hU₀⟩ := Finite.exists_infinite_fiber (fun k => (⟨g k, hgW k⟩ : {U // U ∈ W}))
  refine ⟨(U₀ : Submodule ℚ (Fin m → ℚ)), hWtop _ U₀.2, ?_⟩
  rw [Set.infinite_coe_iff] at hU₀
  have hsub : (fun k => (⟨g k, hgW k⟩ : {U // U ∈ W})) ⁻¹' {U₀} ⊆
      {k | x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))} := by
    intro k hk
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
    have hgk : g k = (U₀ : Submodule ℚ (Fin m → ℚ)) := congrArg Subtype.val hk
    show x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))
    rw [← hgk]
    exact hgmem k
  exact hU₀.mono hsub

@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_reduction {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0)
    (hineq : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε))
    (hncf : ¬ Confinable x) :
    False :=
  hncf (subspace_pigeonhole hm S hS_place L hL ε hε x hx0 hineq)

@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∀ k, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε))
    (hncf : ¬ Confinable x) :
    False :=
  subspace_reduction hm S hS_place L hL ε hε x hx0
    (fun k => le_trans (hover k) (hrate k)) hncf

@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate_sharp {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hHpos : ∀ k, 0 < Height.mulHeight (x k))
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∀ k, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1))
    (hncf : ¬ Confinable x) :
    False := by
  apply subspace_reduction hm S hS_place L hL ε hε x hx0 _ hncf
  intro k
  have hH := hHpos k
  calc (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j)))
      ≤ (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)) := hover k
    _ ≤ (Height.mulHeight (x k))⁻¹ * Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1) :=
        mul_le_mul_of_nonneg_left (hrate k) (inv_nonneg.mpr hH.le)
    _ = Height.mulHeight (x k) ^ (-(m : ℝ) - ε) := by
        rw [show (Height.mulHeight (x k))⁻¹ = Height.mulHeight (x k) ^ (-1 : ℝ) from
          (Real.rpow_neg_one _).symm, ← Real.rpow_add hH]
        congr 1; ring

@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem subspace_pigeonhole_infinite {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (I : Set ℕ) (hI : I.Infinite) (hx0 : ∀ k ∈ I, x k ≠ 0)
    (hineq : ∀ k ∈ I, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      Height.mulHeight (x k) ^ (-(m : ℝ) - ε)) :
    Confinable x := by
  obtain ⟨W, hWtop, hWcov⟩ := subspace_theorem_E hm S hS_place L hL ε hε
  have hIinf := hI.to_subtype
  have hmem : ∀ k : ↥I, ∃ U, U ∈ W ∧ x ↑k ∈ U := fun k => hWcov (x ↑k) (hx0 ↑k k.2) (hineq ↑k k.2)
  choose g hgW hgmem using hmem
  obtain ⟨U₀, hU₀⟩ := Finite.exists_infinite_fiber (fun k : ↥I => (⟨g k, hgW k⟩ : {U // U ∈ W}))
  refine ⟨(U₀ : Submodule ℚ (Fin m → ℚ)), hWtop _ U₀.2, ?_⟩
  rw [Set.infinite_coe_iff] at hU₀
  have hsub : Subtype.val '' {k : ↥I | (⟨g k, hgW k⟩ : {U // U ∈ W}) = U₀} ⊆
      {k | x k ∈ (U₀ : Submodule ℚ (Fin m → ℚ))} := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_ofPred_eq] at hk ⊢
    have hgk : g k = (U₀ : Submodule ℚ (Fin m → ℚ)) := congrArg Subtype.val hk
    rw [← hgk]; exact hgmem k
  exact ((Set.infinite_image_iff Subtype.val_injective.injOn).mpr hU₀).mono hsub

@[category research solved, AMS 11 37, ref "Eve96" "AB07" "BL96", group "b3_missing_lemma"]
theorem subspace_contradiction_of_rate_sharp_frequently {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (AbsoluteValue ℚ ℝ))
    (hS_place : ∀ v ∈ S, v ∈ archAbsVal (K := ℚ) ∨ v ∈ nonarchAbsVal (K := ℚ))
    (L : AbsoluteValue ℚ ℝ → Fin m → Module.Dual ℚ (Fin m → ℚ))
    (hL : ∀ v ∈ S, LinearIndependent ℚ (L v))
    (ε : ℝ) (hε : 0 < ε)
    (x : ℕ → (Fin m → ℚ)) (hx0 : ∀ k, x k ≠ 0) (N : ℕ → ℕ)
    (hHpos : ∀ k, 0 < Height.mulHeight (x k))
    (hover : ∀ k, (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j))) ≤
      (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)))
    (hrate : ∃ᶠ k in atTop, (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1))
    (hncf : ¬ Confinable x) :
    False := by
  apply hncf
  refine subspace_pigeonhole_infinite hm S hS_place L hL ε hε x
    {k | (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1)}
    (Nat.frequently_atTop_iff_infinite.mp hrate) (fun k _ => hx0 k) (fun k hk => ?_)
  have hH := hHpos k
  calc (∏ v ∈ S, ∏ i : Fin m, v ((L v i) (x k)) / (⨆ j, v (x k j)))
      ≤ (Height.mulHeight (x k))⁻¹ * (2 : ℝ) ^ (-(N k : ℝ)) := hover k
    _ ≤ (Height.mulHeight (x k))⁻¹ * Height.mulHeight (x k) ^ (-(m : ℝ) - ε + 1) :=
        mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hH.le)
    _ = Height.mulHeight (x k) ^ (-(m : ℝ) - ε) := by
        rw [show (Height.mulHeight (x k))⁻¹ = Height.mulHeight (x k) ^ (-1 : ℝ) from
          (Real.rpow_neg_one _).symm, ← Real.rpow_add hH]
        congr 1; ring

end B3
