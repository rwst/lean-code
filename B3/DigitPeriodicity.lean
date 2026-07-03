import B3.AutomaticParityVectors
import AB.StammeringSequences
import L90.DivergentAperiodic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function

@[category API, AMS 11 37, ref "BL96"]
theorem digitExpansion_injective {x y : ℤ_[2]}
    (h : ∀ k, parity (S^[k] x) = parity (S^[k] y)) : x = y := by
  rw [← tsum_parity_S x, ← tsum_parity_S y]
  exact tsum_congr fun i => by rw [h i]

@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem shiftPeriodicPoint_mem_ratInt {w : ℤ_[2]} {p : ℕ} (hp : 0 < p)
    (hfix : S^[p] w = w) : w ∈ RatInt := by
  set C : ℕ := ∑ i ∈ Finset.range p, parity (S^[i] w) * 2 ^ i with hC
  have hCcast : ((C : ℕ) : ℤ_[2]) = ∑ i ∈ Finset.range p, (parity (S^[i] w) : ℤ_[2]) * 2 ^ i := by
    rw [hC]; push_cast; ring
  have hexp := parity_partial_expansion w p
  rw [hfix, ← hCcast] at hexp
  have hkey : (1 - (2 : ℤ_[2]) ^ p) * w = (C : ℤ_[2]) := by linear_combination hexp
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hRnorm : ‖(2 : ℤ_[2]) ^ p‖ < 1 := by
    rw [norm_pow]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) h2lt1.le hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hne2 : (1 : ℤ_[2]) - 2 ^ p ≠ 0 := by
    intro hh
    have h1 : (2 : ℤ_[2]) ^ p = 1 := by linear_combination -hh
    rw [h1, norm_one] at hRnorm; exact lt_irrefl 1 hRnorm
  have hcQ : ((1 : ℚ_[2]) - 2 ^ p) * (w : ℚ_[2]) = (C : ℚ_[2]) := by
    exact_mod_cast congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hkey
  have hneQ : (1 : ℚ_[2]) - 2 ^ p ≠ 0 := by
    have h0 : ((1 - 2 ^ p : ℤ_[2]) : ℚ_[2]) ≠ ((0 : ℤ_[2]) : ℚ_[2]) :=
      fun hh => hne2 (PadicInt.ext hh)
    push_cast at h0; exact h0
  refine ⟨(C : ℚ) / ((1 : ℚ) - 2 ^ p), ?_⟩
  push_cast
  rw [eq_div_iff hneQ]
  linear_combination hcQ

@[category research solved, AMS 11, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem not_isEventuallyPeriodic_binaryDigit (v : ℤ_[2]) (h : v ∉ RatInt) :
    ¬ AB.IsEventuallyPeriodic (binaryDigit v) := by
  intro hper
  apply h
  obtain ⟨N, p, hp, hper⟩ := hper
  have hfix : S^[p] (S^[N] v) = S^[N] v := by
    apply digitExpansion_injective
    intro k
    simp only [← Function.iterate_add_apply]
    have hk := hper (k + N) (Nat.le_add_left N k)
    simp only [binaryDigit] at hk
    rw [show k + (p + N) = k + N + p from by omega]
    exact hk
  obtain ⟨qw, hqw⟩ := shiftPeriodicPoint_mem_ratInt hp hfix
  set A : ℕ := ∑ i ∈ Finset.range N, parity (S^[i] v) * 2 ^ i with hA
  have hAcast : ((A : ℕ) : ℤ_[2]) = ∑ i ∈ Finset.range N, (parity (S^[i] v) : ℤ_[2]) * 2 ^ i := by
    rw [hA]; push_cast; ring
  have hexp := parity_partial_expansion v N
  rw [← hAcast] at hexp
  refine ⟨(A : ℚ) + 2 ^ N * qw, ?_⟩
  have hvQ : (v : ℚ_[2]) = (A : ℚ_[2]) + 2 ^ N * ((S^[N] v : ℤ_[2]) : ℚ_[2]) := by
    exact_mod_cast congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hexp
  rw [hvQ, hqw]
  push_cast
  ring

@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem ratInt_eventuallyPeriodic_binaryDigit {v : ℤ_[2]} (hv : v ∈ RatInt) :
    AB.IsEventuallyPeriodic (binaryDigit v) := by
  have hni : ¬ Injective (fun k => S^[k] v) :=
    fun hinj => (Set.infinite_range_of_injective hinj) (ratInt_S_orbit_finite hv)
  rw [Function.not_injective_iff] at hni
  obtain ⟨a, b, hfab, hne⟩ := hni
  have key : ∀ i j : ℕ, i < j → S^[i] v = S^[j] v → AB.IsEventuallyPeriodic (binaryDigit v) := by
    intro i j hlt heq
    refine ⟨i, j - i, by omega, fun k hk => ?_⟩
    show binaryDigit v (k + (j - i)) = binaryDigit v k
    unfold binaryDigit
    have hper : S^[k + (j - i)] v = S^[k] v := by
      conv_lhs => rw [show k + (j - i) = (k - i) + j from by omega, Function.iterate_add_apply,
        ← heq, ← Function.iterate_add_apply, show (k - i) + i = k from by omega]
    rw [hper]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key a b hlt hfab
  · exact key b a hgt hfab.symm

@[category API, AMS 11 37, ref "BL96" "Lag90"]
theorem parityBridge (m : ℕ) : parity (m : ℤ_[2]) = L90.parity (m : ℚ) := by
  have h1 : parity (m : ℤ_[2]) = m % 2 := by unfold parity; rw [map_natCast, ZMod.val_natCast]
  have h2 : L90.parity (m : ℚ) = m % 2 := by unfold L90.parity; rw [Rat.num_natCast]; omega
  rw [h1, h2]

@[category API, AMS 11 37, ref "BL96" "Lag90"]
theorem digit_eq (n j : ℕ) :
    binaryDigit (parityVector n) j = L90.parity (L90.T^[j] (n : ℚ)) := by
  have hsc : ∀ w, Φ.symm (T₂ w) = S (Φ.symm w) := by
    intro w; apply Φ.injective
    rw [Φ.apply_symm_apply, Φ_semiconj (Φ.symm w), Φ.apply_symm_apply]
  have hiter : ∀ (i : ℕ) (x : ℤ_[2]), S^[i] (Φ.symm x) = Φ.symm (T₂^[i] x) := by
    intro i x; induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hsc]
  have hpar : ∀ z, parity (Φ.symm z) = parity z := by
    intro z; have h := Φ_parity (Φ.symm z); rw [Φ.apply_symm_apply] at h; exact h.symm
  unfold binaryDigit parityVector
  rw [← Φ_symm_eq_Q, hiter, hpar, T₂_iterate_natCast, parityBridge, L90.T_iterate_natCast,
    T_iter_eq_iterate]

@[category research solved, AMS 11 37, ref "AB07" "BL96" "Lag90", group "b3_missing_lemma"]
theorem ratInt_imp_eventuallyPeriodicParity (n : ℕ) (h : parityVector n ∈ RatInt) :
    L90.EventuallyPeriodicParity (n : ℚ) := by
  obtain ⟨N, p, hp, hper⟩ := ratInt_eventuallyPeriodic_binaryDigit h
  refine ⟨N, p, hp, fun j hj => ?_⟩
  rw [← digit_eq n (j + p), ← digit_eq n j]
  exact hper j hj

end B3
