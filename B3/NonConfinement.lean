import B3.SubspaceConfinement
import B3.PlaceTwoProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open Function Filter

@[category research solved, AMS 11 37, ref "Eve96" "AB07", group "b3_missing_lemma"]
theorem confinable_iff_exists_dual {m : ℕ} (x : ℕ → (Fin m → ℚ)) :
    Confinable x ↔ ∃ f : Module.Dual ℚ (Fin m → ℚ), f ≠ 0 ∧ {k | f (x k) = 0}.Infinite := by
  constructor
  · rintro ⟨U, hU, hUinf⟩
    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.mpr hU)
    exact ⟨f, hf0, hUinf.mono (fun k hk => LinearMap.mem_ker.mp (hfU hk))⟩
  · rintro ⟨f, hf0, hinf⟩
    refine ⟨LinearMap.ker f, ?_, hinf.mono (fun k hk => LinearMap.mem_ker.mpr hk)⟩
    rw [Ne, LinearMap.ker_eq_top]
    exact hf0

@[category API, AMS 11 37, ref "AB07", group "b3_missing_lemma"]
theorem unused_placePoint_dual_apply (f : Module.Dual ℚ (Fin 3 → ℚ)) (D P : ℚ) :
    f (placePoint D P) = D * f (Pi.single 0 1) - f (Pi.single 1 1) + P * f (Pi.single 2 1) := by
  have hdecomp : placePoint D P
      = D • Pi.single 0 1 - Pi.single 1 1 + P • Pi.single (2 : Fin 3) 1 := by
    funext i; fin_cases i <;> simp [placePoint]
  rw [hdecomp]; simp [map_add, map_sub, map_smul, smul_eq_mul]

end B3
