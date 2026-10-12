/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import CITED.NairKumarRout
import CITED.SubspaceTriple
import CITED.CorvajaZannierProof
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Machinery for deriving the Nair–Kumar–Rout pair theorem from the Subspace Theorem

Support lemmas for `CITED/NairKumarRoutProof.lean` (the `n = 3` half of the one-axiom
refactor, `report-formalize-subspace.html` §4/§6).  The generic three-variable
Subspace engine (the `S`-unit `uval = 2^x·3^y` API, the forms `Lforms3`, the closed-form
Subspace product on gcd-1 integer triples and **`member_solves`**) now lives in
`CITED/SubspaceTriple.lean`, where `TH/KernelDirect.lean` consumes it directly; what
remains here are the two NKR-specific Diophantine finiteness leaves:
`sUnit_near_ratio_finite` (`S`-units approaching a fixed positive rational — the
`q = 1` Corvaja–Zannier instance, via `CZ.pseudoPisot_approx_of_subspace`) and the
opposite-sign case `opposite_case_finite`.

Everything here is **sorry-free**; axiom footprint `std3 + Subspace.evertseSchlickewei`
(through the derived CZ theorem — no bespoke axiom).

## References

* [NKR25] Nair–Kumar–Rout, arXiv:2506.02898v3 (`CITED/NairKumarRout.lean`).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004) (`CITED/CorvajaZannierProof.lean`).
* [S] W. M. Schmidt, LNM **1467**, Theorem 1D′ (`CITED/SubspaceTheorem.lean`).
* `report-formalize-subspace.html` §4, §6 (this repository).
-/

namespace NKR

open Subspace Rat.AbsoluteValue Height CZ SubspaceTriple

attribute [local instance] Classical.propDecidable

/-! ### Stage 4a: `S`-units near a fixed positive rational (the CZ reduction) -/

/-- **Finitely many `S`-units approach a fixed positive rational** — the `q = 1`
instance of the Corvaja–Zannier Main Theorem, reached through the nearest-integer
trick at `δ = 2·den(ρ)`: only finitely many `(s, t) ∈ ℤ²` satisfy
`2^s·3^t ≠ ρ` and `|2^s·3^t − ρ| < K·height23^{-ε}`. -/
@[category API, AMS 11, ref "NKR25", group "three_halves_m4"]
lemma sUnit_near_ratio_finite (ρ : ℚ) (hρ : 0 < ρ) (K : ℝ) (ε : ℝ) (hε : 0 < ε) :
    {st : ℤ × ℤ | uval st.1 st.2 ≠ ρ ∧
      ((|uval st.1 st.2 - ρ| : ℚ) : ℝ)
        < K * ((height23 st.1 st.2 : ℕ) : ℝ) ^ (-ε)}.Finite := by
  rcases le_or_gt K 0 with hK | hK
  · apply Set.Finite.subset Set.finite_empty
    rintro ⟨s, t⟩ ⟨hne, hlt⟩
    exfalso
    have h1 : (0 : ℝ) ≤ ((|uval s t - ρ| : ℚ) : ℝ) := by positivity
    have h2 : K * ((height23 s t : ℕ) : ℝ) ^ (-ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK (Real.rpow_nonneg (by positivity) _)
    linarith
  set e : ℕ := ρ.den with hedef
  set c : ℤ := ρ.num with hcdef
  have hc1 : 1 ≤ c := Rat.num_pos.mpr hρ
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero ρ.den_nz
  set δ : ℚ := 2 * (e : ℚ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
    linarith
  set KE : ℝ := 2 * (e : ℝ) * K with hKEdef
  have hKE : 0 < KE := by
    rw [hKEdef]
    have : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    positivity
  set Bval : ℝ := max ((2 * KE) ^ ε⁻¹) (KE ^ (2 / ε)) with hBdef
  have hCZ := CZ.pseudoPisot_approx_of_subspace δ hδpos.ne' (ε / 2) (by positivity)
  have himg : {st : ℤ × ℤ | (uval st.1 st.2 ≠ ρ ∧
      ((|uval st.1 st.2 - ρ| : ℚ) : ℝ) < K * ((height23 st.1 st.2 : ℕ) : ℝ) ^ (-ε)) ∧
      Bval < ((height23 st.1 st.2 : ℕ) : ℝ)}.Finite := by
    apply Set.Finite.of_finite_image (f := fun st : ℤ × ℤ => ((1 : ℕ), st.1, st.2))
    swap
    · intro a _ b _ hab
      simpa [Prod.ext_iff] using hab
    apply Set.Finite.subset hCZ
    rintro p ⟨⟨s, t⟩, ⟨⟨hne, hlt⟩, hbig⟩, rfl⟩
    have hh1 : (1 : ℕ) ≤ height23 s t := one_le_height23 s t
    have hhR0 : (0 : ℝ) < ((height23 s t : ℕ) : ℝ) := by exact_mod_cast hh1
    have hw0 : (0 : ℚ) < uval s t := uval_pos s t
    set w : ℚ := uval s t with hwdef
    -- `sval δ 1 s t = δ·w`
    have hsval : sval δ 1 s t = δ * w := by
      unfold CZ.sval
      rw [hwdef]
      show δ * ((1 : ℕ) : ℚ) * ((2 : ℚ) ^ s * (3 : ℚ) ^ t) = δ * uval s t
      unfold SubspaceTriple.uval
      push_cast
      ring
    -- `c = ρ·e`
    have hce : (c : ℚ) = ρ * (e : ℚ) := by
      rw [hcdef, hedef]
      have hden : ((ρ.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ρ.den_nz
      exact (div_eq_iff hden).mp (Rat.num_div_den ρ)
    -- the exact distance identity `|δw − 2c| = 2e·|w − ρ|`
    have hid : |δ * w - ((2 * c : ℤ) : ℚ)| = 2 * (e : ℚ) * |w - ρ| := by
      have harg : δ * w - ((2 * c : ℤ) : ℚ) = 2 * (e : ℚ) * (w - ρ) := by
        push_cast
        rw [hδdef, hce]
        ring
      rw [harg, abs_mul, abs_of_pos (show (0:ℚ) < 2 * (e:ℚ) by
        have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
        linarith)]
    -- the real bound `|δw − 2c| < KE·h^{-ε}`
    have hlt' : ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ)
        < KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by
      have hltR : |(w : ℝ) - (ρ : ℝ)| < K * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by
        have h := hlt
        push_cast at h
        exact h
      have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
      rw [hid]
      push_cast
      calc (2 : ℝ) * (e : ℝ) * |(w : ℝ) - (ρ : ℝ)|
          < 2 * (e : ℝ) * (K * ((height23 s t : ℕ) : ℝ) ^ (-ε)) :=
            mul_lt_mul_of_pos_left hltR (by linarith)
        _ = KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by rw [hKEdef]; ring
    -- the two rpow thresholds from `Bval < h`
    have hKE2 : 2 * KE ≤ ((height23 s t : ℕ) : ℝ) ^ ε := by
      have h1 : (2 * KE) ^ ε⁻¹ ≤ Bval := le_max_left _ _
      have h2 : (2 * KE) ^ ε⁻¹ < ((height23 s t : ℕ) : ℝ) := lt_of_le_of_lt h1 hbig
      have h3 : ((2 * KE) ^ ε⁻¹) ^ ε ≤ ((height23 s t : ℕ) : ℝ) ^ ε :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h2.le hε.le
      rwa [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2 * KE), inv_mul_cancel₀ hε.ne',
        Real.rpow_one] at h3
    have hKEhalf : KE ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) := by
      have h1 : KE ^ (2 / ε) ≤ Bval := le_max_right _ _
      have h2 : KE ^ (2 / ε) < ((height23 s t : ℕ) : ℝ) := lt_of_le_of_lt h1 hbig
      have h3 : (KE ^ (2 / ε)) ^ (ε / 2) ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hKE.le _) h2.le (by positivity)
      rwa [← Real.rpow_mul hKE.le, div_mul_div_comm, mul_comm (2:ℝ) ε,
        div_self (by positivity : ε * 2 ≠ 0), Real.rpow_one] at h3
    have hrp0 : (0 : ℝ) < ((height23 s t : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hhR0 _
    have hhalf : KE * ((height23 s t : ℕ) : ℝ) ^ (-ε) ≤ 1 / 2 := by
      have h1 : 2 * (KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)) ≤ 1 := by
        calc 2 * (KE * ((height23 s t : ℕ) : ℝ) ^ (-ε))
            = (2 * KE) * ((height23 s t : ℕ) : ℝ) ^ (-ε) := by ring
          _ ≤ ((height23 s t : ℕ) : ℝ) ^ ε * ((height23 s t : ℕ) : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_right hKE2 hrp0.le
          _ = 1 := by
              rw [← Real.rpow_add hhR0]
              norm_num
      linarith
    -- ℚ-version of the half-bound
    have hhalfQ : |δ * w - ((2 * c : ℤ) : ℚ)| < 1 / 2 := by
      have h1 : ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ) < 1 / 2 :=
        lt_of_lt_of_le hlt' hhalf
      rw [show ((1 : ℝ) / 2) = (((1 / 2 : ℚ) : ℚ) : ℝ) by norm_num] at h1
      exact_mod_cast h1
    -- `δw ≠ 2c` (else `w = ρ`)
    have hne2c : δ * w ≠ ((2 * c : ℤ) : ℚ) := by
      intro h0
      apply hne
      have : 2 * (e : ℚ) * (w - ρ) = 0 := by
        have harg : δ * w - ((2 * c : ℤ) : ℚ) = 2 * (e : ℚ) * (w - ρ) := by
          push_cast
          rw [hδdef, hce]
          ring
        rw [← harg, h0]
        ring
      have he0 : (0 : ℚ) < 2 * (e : ℚ) := by
        have : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he1
        linarith
      have := mul_eq_zero.mp this
      rcases this with h | h
      · exact absurd h he0.ne'
      · linarith [sub_eq_zero.mp h]
    -- not an integer
    have hnotint : ¬ ∃ n : ℤ, δ * w = (n : ℚ) := by
      rintro ⟨n, hn⟩
      rcases eq_or_ne n (2 * c) with rfl | hne_n
      · exact hne2c hn
      · have h1 : (1 : ℚ) ≤ |(n : ℚ) - ((2 * c : ℤ) : ℚ)| := by
          have h2 : n - 2 * c ≠ 0 := sub_ne_zero.mpr hne_n
          have h2' := abs_pos.mpr h2
          have h3 : (1 : ℤ) ≤ |n - 2 * c| := by omega
          calc (1 : ℚ) ≤ ((|n - 2 * c| : ℤ) : ℚ) := by exact_mod_cast h3
            _ = |(n : ℚ) - ((2 * c : ℤ) : ℚ)| := by
                rw [Int.cast_abs]
                push_cast
                ring_nf
        rw [hn] at hhalfQ
        linarith
    -- positive distance
    have hdistpos : 0 < (δ * w).distToNearestInt := by
      rcases lt_or_eq_of_le (Rat.distToNearestInt_nonneg (δ * w)) with h | h
      · exact h
      · exfalso
        exact hnotint (Rat.distToNearestInt_eq_zero_iff.mp h.symm)
    -- 1 < |sval|
    have honelt : 1 < |sval δ 1 s t| := by
      rw [hsval]
      have hc2 : (2 : ℚ) ≤ ((2 * c : ℤ) : ℚ) := by
        push_cast
        have : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
        linarith
      have hlow : (3 : ℚ) / 2 < δ * w := by
        have h1 : ((2 * c : ℤ) : ℚ) - δ * w ≤ |δ * w - ((2 * c : ℤ) : ℚ)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      rw [abs_of_pos (by linarith : (0 : ℚ) < δ * w)]
      linarith
    -- the distance bound at exponent ε/2
    have hdlt : (((sval δ 1 s t).distToNearestInt : ℚ) : ℝ)
        < ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) * ((1 : ℕ) : ℝ) ^ (-1 - ε / 2) := by
      have hd1 : (sval δ 1 s t).distToNearestInt ≤ |δ * w - ((2 * c : ℤ) : ℚ)| := by
        rw [hsval]
        exact Rat.distToNearestInt_le_abs_sub_intCast _ _
      have hd2 : (((sval δ 1 s t).distToNearestInt : ℚ) : ℝ)
          ≤ ((|δ * w - ((2 * c : ℤ) : ℚ)| : ℚ) : ℝ) := by exact_mod_cast hd1
      have hd3 : KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)
          ≤ ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
        calc KE * ((height23 s t : ℕ) : ℝ) ^ (-ε)
            ≤ ((height23 s t : ℕ) : ℝ) ^ (ε / 2) * ((height23 s t : ℕ) : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_right hKEhalf hrp0.le
          _ = ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
              rw [← Real.rpow_add hhR0]
              congr 1
              ring
      have hrhs : ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) * ((1 : ℕ) : ℝ) ^ (-1 - ε / 2)
          = ((height23 s t : ℕ) : ℝ) ^ (-(ε / 2)) := by
        rw [Nat.cast_one, Real.one_rpow, mul_one]
      rw [hrhs]
      exact lt_of_le_of_lt hd2 (lt_of_lt_of_le hlt' hd3)
    exact ⟨le_refl 1, honelt, by rw [hsval]; exact hnotint, by rw [hsval]; exact hdistpos, hdlt⟩
  apply Set.Finite.subset ((finite_height23_le Bval).union himg)
  rintro ⟨s, t⟩ hst
  rcases le_or_gt ((height23 s t : ℕ) : ℝ) Bval with hsmall | hbig
  · exact Or.inl hsmall
  · exact Or.inr ⟨hst, hbig⟩

/-- The **opposite-sign sub-case** of the relation analysis: if along a family
with injective exponent-differences the distance equals `|b₁u₁ + b₂u₂|` with
`b₁ > 0 > b₂`, the family is finite — the ratios `u₁/u₂` approximate `ρ = -b₂/b₁`
and `sUnit_near_ratio_finite` applies. -/
@[category API, AMS 11, ref "NKR25", group "three_halves_m4"]
lemma opposite_case_finite (α₁ α₂ b₁ b₂ : ℚ) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (hb₁ : 0 < b₁) (hb₂ : b₂ < 0) (F : Set ((ℤ × ℤ) × (ℤ × ℤ)))
    (habs₂ : ∀ q ∈ F, 1 ≤ uval q.2.1 q.2.2)
    (hinjF : Set.InjOn (fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2)) F)
    (hdeq : ∀ q ∈ F, (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt
        = |b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2|)
    (hposF : ∀ q ∈ F,
        0 < (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt)
    (happroxF : ∀ q ∈ F,
        ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) :
    F.Finite := by
  set ρ : ℚ := -b₂ / b₁ with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact div_pos (by linarith) hb₁
  have hb₁R : (0 : ℝ) < ((b₁ : ℚ) : ℝ) := by exact_mod_cast hb₁
  have hfin := sUnit_near_ratio_finite ρ hρ (((b₁ : ℚ) : ℝ)⁻¹) ε₁ hε₁
  apply Set.Finite.of_finite_image
    (f := fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2))
  swap
  · exact hinjF
  apply Set.Finite.subset hfin
  rintro st ⟨q, hqF, rfl⟩
  have hu₁0 : (0 : ℚ) < uval q.1.1 q.1.2 := uval_pos _ _
  have hu₂0 : (0 : ℚ) < uval q.2.1 q.2.2 := uval_pos _ _
  have hu₂1 : 1 ≤ uval q.2.1 q.2.2 := habs₂ q hqF
  have hw : uval (q.1.1 - q.2.1) (q.1.2 - q.2.2)
      = uval q.1.1 q.1.2 / uval q.2.1 q.2.2 := (uval_div _ _ _ _).symm
  have hkey : b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2
      = b₁ * uval q.2.1 q.2.2 * (uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ) := by
    rw [hρdef]
    field_simp
    ring
  have hdq := hdeq q hqF
  have hwne : uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ ρ := by
    intro h0
    have hp := hposF q hqF
    rw [hdq, hkey, h0, sub_self, mul_zero, abs_zero] at hp
    exact lt_irrefl 0 hp
  have habs_eq : |b₁ * uval q.1.1 q.1.2 + b₂ * uval q.2.1 q.2.2|
      = b₁ * uval q.2.1 q.2.2 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := by
    rw [hkey, abs_mul, abs_of_pos (mul_pos hb₁ hu₂0)]
  have hge : b₁ * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ|
      ≤ (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt := by
    rw [hdq, habs_eq]
    have h0 : (0 : ℚ) ≤ |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := abs_nonneg _
    have h1 : b₁ * 1 ≤ b₁ * uval q.2.1 q.2.2 := mul_le_mul_of_nonneg_left hu₂1 hb₁.le
    have h2 := mul_le_mul_of_nonneg_right h1 h0
    calc b₁ * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ|
        = b₁ * 1 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := by ring
      _ ≤ b₁ * uval q.2.1 q.2.2 * |uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| := h2
  -- pass to ℝ and weaken the height
  have hh_w0 : (0 : ℝ) < ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) := by
    have := one_le_height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2)
    exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
  have hHH0 : (0 : ℝ) < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) := by
    have h1 := one_le_height23 q.1.1 q.1.2
    have h2 := one_le_height23 q.2.1 q.2.2
    exact_mod_cast Nat.mul_pos h1 h2
  have hanti : ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)
      ≤ ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
    rw [Real.rpow_neg hHH0.le, Real.rpow_neg hh_w0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hh_w0 _)
    apply Real.rpow_le_rpow hh_w0.le _ hε₁.le
    exact_mod_cast height23_sub_le q.1.1 q.1.2 q.2.1 q.2.2
  have hlt : ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
      < ((b₁ : ℚ) : ℝ)⁻¹
        * ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
    have h1 : ((b₁ : ℚ) : ℝ) * ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
        < ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) ^ (-ε₁) := by
      have h2 : ((b₁ : ℚ) : ℝ) * ((|uval q.1.1 q.1.2 / uval q.2.1 q.2.2 - ρ| : ℚ) : ℝ)
          ≤ (((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℚ) : ℝ) := by
        exact_mod_cast hge
      exact lt_of_le_of_lt h2 (lt_of_lt_of_le (happroxF q hqF) hanti)
    rw [inv_mul_eq_div, lt_div_iff₀' hb₁R]
    exact h1
  exact ⟨by rw [hw]; exact hwne, by rw [hw]; exact hlt⟩

end NKR

