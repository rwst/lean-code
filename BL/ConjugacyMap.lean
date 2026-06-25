/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.Basic
import BL.SolenoidalMaps
import Mathlib.Analysis.SpecificLimits.Normed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — The 3x+1 conjugacy map `Φ` (BL96, §1)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

This file defines **the** `3x + 1` conjugacy map `Φ`, the named object of the paper's title. By
`(1.3)` (`BL.exists_conjugacy`) there is a homeomorphism conjugating the 2-adic shift `S` to the
3x+1 map `T₂`; it is unique only up to right-multiplication by `Aut(S) = {id, V} ≅ ℤ/2ℤ`
(`BL.conjugacy_unique`, `BL.shiftAut_eq_id_or_V`). Adding the **normalisation `Φ(0) = 0`** singles
out a unique map — the **3x+1 conjugacy map**:

  `Φ ∘ S ∘ Φ⁻¹ = T₂`   and   `Φ(0) = 0`.

Existence of a normalised conjugacy is recorded as a cited `axiom` (`exists_normalized_conjugacy`;
the map has been constructed several times in the literature, e.g. [BFK90]); `Φ` is then this map,
with defining properties `Φ_semiconj` and `Φ_apply_zero`. **Uniqueness is proved**
(`eq_Φ_of_normalized`, `existsUnique_normalized_conjugacy`): a second normalised conjugacy would
differ from `Φ` by an `Aut(S)`-factor `ψ ∈ {id, V}`, and `ψ = V` is excluded because
`V 0 = -1 ≠ 0`. The only other conjugacy is `Φ ∘ V` (`ΦV_semiconj`).

An important further property: `Φ` is **solenoidal** (`Solenoidal`, `Φ_solenoidal`, cited) — it
respects congruence modulo `2ⁿ` for every `n`, i.e. induces a map on each `ℤ/2ⁿℤ`. Solenoidality at
`n = 1` together with `Φ 0 = 0` gives equation **`(1.4)`** `Φ(x) ≡ x (mod 2)` (`Φ_mod_two`, proved),
equivalently `parity (Φ x) = parity x` (`Φ_parity`).

The inverse `Φ⁻¹` has the **explicit formula `(1.5)`** `Φ⁻¹(x) = ∑_{i≥0} (Tⁱ(x) mod 2)·2ⁱ` (`Q`,
Lagarias's parity-vector map `Q∞`; `Φ_symm_eq_Q`, **proved** — this is **Bernstein's noniterative 2-adic
statement** [Ber94]): it packs the parities of the `T₂`-orbit of `x` — exactly the `CC.Parity`
vectors (cf. the bridges in `BL.Basic`). This formula re-derives
`(1.3)`/`(1.4)` and shows `Φ⁻¹` is solenoidal (`Q_solenoidal`).

The **forward** map `Φ` has the dual **explicit formula `(1.6)`** [Ber94]: expand `x` in binary by
its `1`-bit positions, `x = ∑ᵢ 2^{dᵢ}` (`0 ≤ d₀ < d₁ < ⋯`); then `Φ(x) = − ∑ᵢ 3^{−(i+1)} 2^{dᵢ}`
(`Φ_eq_neg_tsum` for an infinite bit-sequence, `Φ_eq_neg_sum` for the finite case `x ∈ ℕ`; the
inverse `3⁻¹ = Ring.inverse 3` exists since `3` is a unit, `isUnit_three`/`three_mul_inverse`). This
too implies `(1.3)`/`(1.4)` and shows `Φ` is solenoidal.

Finally, as `T₂` extends the integer map, the **3x+1 conjecture** is recorded in 2-adic form as a
*proved equivalence* `t2_reachesOne_iff_collatz`: `(∀ n>0, ∃ j, T₂ʲ(↑n)=1) ↔ (∀ n>0, ∃ j, Tʲ(n)=1)`.
Only the equivalence is asserted — the conjecture itself is left open and unnamed.

The paper's **Periodicity Conjecture** (`periodicity_conjecture`, `research open`) is
`Φ(ℚ ∩ ℤ₂) = ℚ ∩ ℤ₂` (`RatInt`): `Φ` preserves the rational 2-adic integers. It would imply the 3x+1
map has **no divergent trajectory** (`periodicity_imp_no_divergent_trajectories`, `research open`),
where a trajectory is **divergent** (`Divergent`) if it has infinitely many distinct elements —
equivalently `Tᵏ(n) → ∞` (`divergent_iff_tendsto_atTop`, proved via the iteration dichotomy
`range_iterate_infinite_iff_tendsto`).

The **Fixed Point Conjecture** (`fixed_point_conjecture`, `research open`) asserts `Φ` has exactly two
*odd* fixed points, `-1` and `1/3`. We verify both are odd (`parity_neg_one`, `parity_inv_three`),
distinct (`neg_one_ne_inv_three`), and that `-1` is genuinely fixed (`Φ_neg_one`, proved via
`S_neg_one` and the `T₂`-fixed-point characterization `eq_zero_or_neg_one_of_T₂_fixed`); only `⊆` —
that there is no *other* odd fixed point — stays open.

The **Conjugacy Finiteness Conjecture** (`conjugacy_finiteness_conjecture`, `research open`) generalises
this: for each `j ≥ 0`, `Φ` has finitely many odd periodic points of period `2ʲ` (`Φ^[2ʲ] x = x`). Its
`j = 0` case is exactly the odd-fixed-point finiteness that the Fixed Point Conjecture sharpens to
"exactly two" (`conjugacy_finiteness_zero_of_fixed_point`).

A first **analytic** fact is recorded (cited): `Φ` and `Φ⁻¹` are **nowhere differentiable** on `ℤ₂`
(`Φ_nowhereDifferentiable`, `Φsymm_nowhereDifferentiable`/`Q_nowhereDifferentiable`) — a BL96 §1 remark
(p. 1156) attributed to [Mueller91] and [Ber94]. Deeper analytic / self-similar structure is deferred to
later files.

## Contents
* `exists_normalized_conjugacy` — cited: a conjugacy with `Φ 0 = 0` exists.
* `Φ`, `Φ_semiconj`, `Φ_apply_zero` — the 3x+1 conjugacy map and its two defining properties.
* `eq_Φ_of_normalized`, `existsUnique_normalized_conjugacy` — uniqueness (proved): `Φ` is *the*
  unique normalised conjugacy.
* `ΦV_semiconj` — the only other conjugacy is `Φ ∘ V`.
* `two_dvd_iff_toZMod_eq_zero`, `Φ_solenoidal` — the solenoidal property (cited for `Φ`; the notion
  `Solenoidal` itself lives in `BL.SolenoidalMaps`, Appendix A).
* `Φ_mod_two` (1.4), `Φ_parity` — proved: `Φ(x) ≡ x (mod 2)`.
* `Q` (1.5), `tsum_parity_S`, `Φ_symm_eq_Q`, `Q_solenoidal` — the explicit formula
  `Φ⁻¹(x) = ∑ (Tⁱx mod 2)·2ⁱ` (`= Q∞`) and its properties (`Φ_symm_eq_Q` **proved** via the binary
  digit expansion `tsum_parity_S`; `Q_solenoidal` cited).
* `isUnit_three`, `three_mul_inverse` — `3` is a unit in `ℤ₂`; `Ring.inverse 3 = 3⁻¹` (proved).
* `Φ_eq_neg_tsum` (1.6), `Φ_eq_neg_sum` — the explicit formula `Φ(x) = − ∑ 3^{−(i+1)} 2^{dᵢ}` for the
  forward map `Φ` (infinite / finite `1`-bit sequence; cited).
* `t2_reachesOne_iff_collatz` — the 3x+1 conjecture: 2-adic form ⟺ integer form (proved equivalence).
* `RatInt`, `periodicity_conjecture` — `ℚ ∩ ℤ₂` and the **Periodicity Conjecture** `Φ(ℚ∩ℤ₂)=ℚ∩ℤ₂`
  (research open).
* `Divergent`, `divergent_iff_tendsto_atTop` — a divergent 3x+1 trajectory (∞-many distinct elements)
  ⟺ `Tᵏ(n) → ∞`; helpers `orbit_range_finite_of_eq`, `range_iterate_infinite_iff_tendsto`,
  `T_iter_eq_iterate` — the general iteration dichotomy behind it.
* `periodicity_imp_no_divergent_trajectories` — Periodicity Conjecture ⟹ no divergent trajectory
  (research open).
* `parity_neg_one`, `parity_inv_three`, `eq_zero_or_neg_one_of_T₂_fixed`, `S_neg_one`, `Φ_neg_one`,
  `neg_one_ne_inv_three`, `fixed_point_conjecture` — the **Fixed Point Conjecture** (`Φ` has exactly two
  odd fixed points `-1`, `1/3`; research open) and the verified facts: `-1` is fixed, both are odd and
  distinct.
* `conjugacy_finiteness_conjecture`, `conjugacy_finiteness_zero_of_fixed_point` — the **Conjugacy
  Finiteness Conjecture** (finitely many odd period-`2ʲ` points; research open) and its `j = 0`
  reduction to the Fixed Point Conjecture.
* `diffQuotient`, `DifferentiableAt2`, `NowhereDifferentiable2`, `Φ_nowhereDifferentiable`,
  `Φsymm_nowhereDifferentiable`, `Q_nowhereDifferentiable` — `Φ` and `Φ⁻¹` are nowhere differentiable
  on `ℤ₂` (cited).

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169.
* [BFK90] Boyle, Mike, John Franks, and Bruce Kitchens. *Automorphisms of one-sided subshifts of
  finite type.* Ergodic Theory and Dynamical Systems 10 (1990), no. 3, 421–449.
* [Ber94] Bernstein, Daniel J. *A noniterative 2-adic statement of the 3N+1 conjecture.* Proceedings
  of the American Mathematical Society 121 (1994), no. 2, 405–408 (the paper's reference [2]: the
  explicit formulas `(1.5)` for `Φ⁻¹` and `(1.6)` for `Φ`, i.e. the noniterative 2-adic form).
* [Lag85] Lagarias, Jeffrey C. *The 3x+1 problem and its generalizations.* American Mathematical
  Monthly 92 (1985), no. 1, 3–23 (the paper's reference [8]).
* [Mueller91] Müller, Helmut. *Das '3n+1' Problem.* Mitteilungen der Mathematischen Gesellschaft in
  Hamburg 12 (1991), 231–251 (the paper's reference [10]: `Φ`, `Φ⁻¹` nowhere differentiable on `ℤ₂`).
-/

namespace BL

open PadicInt Function Filter

/-- **(cited; Bernstein–Lagarias 1996, also [BFK90].)** A conjugacy satisfying `(1.3)` can be chosen
with the **normalisation `Φ 0 = 0`**. (The map has been constructed several times in the
literature.) Existence is cited; uniqueness is proved below. -/
@[category research solved, AMS 37 11, ref "BL96" "BFK90" "Ber94", group "bl_conjugacy_map"]
axiom exists_normalized_conjugacy :
    ∃ Φ : ℤ_[2] ≃ₜ ℤ_[2], Function.Semiconj (⇑Φ) S T₂ ∧ Φ 0 = 0

/-- **The 3x+1 conjugacy map** `Φ : ℤ₂ → ℤ₂`: the unique homeomorphism with `Φ ∘ S ∘ Φ⁻¹ = T₂`
(`Φ_semiconj`) and `Φ 0 = 0` (`Φ_apply_zero`). -/
@[category API, AMS 37 11, ref "BL96"]
noncomputable def Φ : ℤ_[2] ≃ₜ ℤ_[2] := exists_normalized_conjugacy.choose

/-- `Φ` conjugates the shift `S` to the 3x+1 map `T₂`: `Φ ∘ S = T₂ ∘ Φ` (i.e. `Φ ∘ S ∘ Φ⁻¹ = T₂`). -/
@[category API, AMS 37 11, ref "BL96"]
theorem Φ_semiconj : Function.Semiconj (⇑Φ) S T₂ := exists_normalized_conjugacy.choose_spec.1

/-- The normalisation `Φ 0 = 0`. -/
@[category API, AMS 37 11, ref "BL96"]
theorem Φ_apply_zero : Φ 0 = 0 := exists_normalized_conjugacy.choose_spec.2

/-- **Uniqueness of the normalised conjugacy.** Any homeomorphism `Ψ` with `Ψ ∘ S ∘ Ψ⁻¹ = T₂` and
`Ψ 0 = 0` equals `Φ`. Proof: by `conjugacy_unique`, `Ψ = Φ ∘ ψ` with `ψ ∈ Aut(S) = {id, V}`
(`shiftAut_eq_id_or_V`); `ψ = V` would give `0 = Ψ 0 = Φ (V 0) = Φ (-1) = Φ 0`, so `-1 = 0` by
injectivity — impossible; hence `ψ = id`. -/
@[category research solved, AMS 37 11, ref "BL96", group "bl_conjugacy_map"]
theorem eq_Φ_of_normalized (Ψ : ℤ_[2] ≃ₜ ℤ_[2]) (hΨ : Function.Semiconj (⇑Ψ) S T₂)
    (hΨ0 : Ψ 0 = 0) : Ψ = Φ := by
  obtain ⟨ψ, hψ, hcomp⟩ := conjugacy_unique Φ Ψ Φ_semiconj hΨ
  rcases shiftAut_eq_id_or_V ψ hψ with hid | hV
  · have hcoe : (⇑Ψ : ℤ_[2] → ℤ_[2]) = ⇑Φ := by rw [hcomp, hid]; rfl
    exact DFunLike.coe_injective hcoe
  · exfalso
    have h0 : (⇑Ψ) 0 = (⇑Φ ∘ ⇑ψ) 0 := by rw [hcomp]
    rw [hV] at h0
    simp only [comp_apply] at h0
    rw [hΨ0, V_apply_zero] at h0
    have heq : Φ 0 = Φ (-1) := by rw [Φ_apply_zero]; exact h0
    exact one_ne_zero (by linear_combination (Φ.injective heq))

/-- **`Φ` is the unique normalised conjugacy** — the precise sense in which `(1.3) + Φ 0 = 0`
*determines* `Φ`. -/
@[category research solved, AMS 37 11, ref "BL96", group "bl_conjugacy_map"]
theorem existsUnique_normalized_conjugacy :
    ∃! Ξ : ℤ_[2] ≃ₜ ℤ_[2], Function.Semiconj (⇑Ξ) S T₂ ∧ Ξ 0 = 0 :=
  ⟨Φ, ⟨Φ_semiconj, Φ_apply_zero⟩, fun Ψ ⟨hΨ, hΨ0⟩ => eq_Φ_of_normalized Ψ hΨ hΨ0⟩

/-- The **other** conjugacy map is `Φ ∘ V`: it too satisfies `(1.3)` (but not the normalisation,
since `(Φ ∘ V) 0 = Φ (-1) ≠ 0`). These two are all of them, by `eq_Φ_of_normalized`. -/
@[category API, AMS 37 11, ref "BL96"]
theorem ΦV_semiconj : Function.Semiconj (⇑Φ ∘ V) S T₂ := by
  intro x
  show Φ (V (S x)) = T₂ (Φ (V x))
  rw [V_semiconj_S x]
  exact Φ_semiconj (V x)

/-! ### Solenoidality and `Φ(x) ≡ x (mod 2)` (1.4)

`Solenoidal` (a map respecting congruence mod `2ⁿ` for every `n`) is defined in `BL.SolenoidalMaps`
(Appendix A); here we record that `Φ` and `Φ⁻¹` are solenoidal and derive `(1.4)`. -/

/-- `2 ∣ z` in `ℤ₂` iff `z ≡ 0 (mod 2)` (`toZMod z = 0`): the bridge between divisibility and the
residue map (`toZMod 2 = 0`; kernel of `toZMod` is the maximal ideal `(2)`). -/
@[category API, AMS 11, ref "BL96"]
theorem two_dvd_iff_toZMod_eq_zero (z : ℤ_[2]) : (2 : ℤ_[2]) ∣ z ↔ PadicInt.toZMod z = 0 := by
  have h2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
    have : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [this, map_natCast]; decide
  constructor
  · rintro ⟨w, rfl⟩; rw [map_mul, h2, zero_mul]
  · intro h
    have hk : z ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := h
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hk
    simpa using hk

/-- **(cited; Bernstein–Lagarias 1996.)** An important property of `Φ`: it is **solenoidal** — for
every `n` it induces a map on `ℤ/2ⁿℤ`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_conjugacy_map"]
axiom Φ_solenoidal : Solenoidal (⇑Φ)

/-- **(1.4)** `Φ(x) ≡ x (mod 2)`. **Proved** from solenoidality (`Φ_solenoidal`) and `Φ 0 = 0`: even
inputs map to even (via `Φ 0 = 0`), and surjectivity of `Φ` forces some — hence, by solenoidality at
`n = 1`, every — odd input to map to an odd value. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_conjugacy_map"]
theorem Φ_mod_two (x : ℤ_[2]) : PadicInt.toZMod (Φ x) = PadicInt.toZMod x := by
  have c2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hsol1 : ∀ a b : ℤ_[2], PadicInt.toZMod a = PadicInt.toZMod b →
      PadicInt.toZMod (Φ a) = PadicInt.toZMod (Φ b) := by
    intro a b hab
    have hdvd : (2 : ℤ_[2]) ∣ (a - b) := by rw [two_dvd_iff_toZMod_eq_zero, map_sub, hab, sub_self]
    have hs := Φ_solenoidal 1 a b (by rw [pow_one]; exact hdvd)
    rw [pow_one, two_dvd_iff_toZMod_eq_zero, map_sub, sub_eq_zero] at hs
    exact hs
  have heven : ∀ z, PadicInt.toZMod z = 0 → PadicInt.toZMod (Φ z) = 0 := by
    intro z hz
    have hz0 : PadicInt.toZMod (Φ z) = PadicInt.toZMod (Φ 0) := hsol1 z 0 (by rw [hz, map_zero])
    rw [hz0, Φ_apply_zero, map_zero]
  obtain ⟨w, hw⟩ := Φ.surjective 1
  have hΦw : PadicInt.toZMod (Φ w) = 1 := by rw [hw, map_one]
  have hwodd : PadicInt.toZMod w = 1 := by
    rcases c2 (PadicInt.toZMod w) with h | h
    · rw [heven w h] at hΦw; exact absurd hΦw (by decide)
    · exact h
  rcases c2 (PadicInt.toZMod x) with h | h
  · rw [heven x h, h]
  · have hxw : PadicInt.toZMod (Φ x) = PadicInt.toZMod (Φ w) := hsol1 x w (by rw [h, hwodd])
    rw [hxw, hΦw, h]

/-- (1.4) in terms of `parity`: `Φ` preserves the lowest binary digit, `parity (Φ x) = parity x` —
i.e. the `0`-th digit of `Q∞`/`Φ` is the identity. -/
@[category API, AMS 11 37, ref "BL96"]
theorem Φ_parity (x : ℤ_[2]) : parity (Φ x) = parity x := by
  unfold parity; rw [Φ_mod_two]

/-! ### The explicit formula for `Φ⁻¹` (1.5) -/

/-- **(1.5)** The explicit formula for the inverse conjugacy map: `Φ⁻¹(x) = ∑_{i≥0} (Tⁱ(x) mod 2)·2ⁱ`
— the 2-adic integer whose `i`-th binary digit is the parity `parity (T₂ⁱ x)` of the `i`-th iterate.
This is Lagarias's **parity-vector map `Q∞`**; on `ℕ` its digits are exactly the `CC.Parity` parity
vectors of the Collatz orbit (`parity_T₂_iterate_natCast`). -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def Q (x : ℤ_[2]) : ℤ_[2] := ∑' i : ℕ, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i

/-- **The binary digit expansion via the shift.** Every `2`-adic integer is recovered from its binary
digits, the `i`-th being `parity (Sⁱ y)`: `y = ∑_{i≥0} (parity (Sⁱ y)) · 2ⁱ`. *Proof:* the bit-peel
`parity_add_two_mul_S` (`parity x + 2·S x = x`) telescopes to
`y = ∑_{i<N} parity(Sⁱy)·2ⁱ + 2ᴺ·Sᴺ y`, and the remainder `2ᴺ·Sᴺ y → 0` in `ℤ₂` (norm `≤ 2⁻ᴺ`, the
series being geometric-dominated hence summable). This is the convergence fact behind the explicit
formula `(1.5)` for `Φ⁻¹`. -/
@[category API, AMS 11 37, ref "BL96" "Ber94"]
theorem tsum_parity_S (y : ℤ_[2]) :
    ∑' i : ℕ, (parity (S^[i] y) : ℤ_[2]) * 2 ^ i = y := by
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hbound : ∀ i, ‖(parity (S^[i] y) : ℤ_[2]) * 2 ^ i‖ ≤ ‖(2 : ℤ_[2])‖ ^ i := by
    intro i
    have h1 : ‖(parity (S^[i] y) : ℤ_[2]) * 2 ^ i‖
        ≤ ‖((parity (S^[i] y) : ℕ) : ℤ_[2])‖ * ‖(2 : ℤ_[2]) ^ i‖ := norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) i) (PadicInt.norm_le_one _))
  have hsum : Summable (fun i : ℕ => (parity (S^[i] y) : ℤ_[2]) * 2 ^ i) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt) hbound
  have hrem : ∀ N : ℕ, y = (∑ i ∈ Finset.range N, (parity (S^[i] y) : ℤ_[2]) * 2 ^ i)
      + 2 ^ N * S^[N] y := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      have hp := parity_add_two_mul_S (S^[N] y)
      linear_combination ih - (2 : ℤ_[2]) ^ N * hp
  have hb0 : ∀ N, ‖(2 : ℤ_[2]) ^ N * S^[N] y‖ ≤ ‖(2 : ℤ_[2])‖ ^ N := by
    intro N
    have h1 : ‖(2 : ℤ_[2]) ^ N * S^[N] y‖ ≤ ‖(2 : ℤ_[2]) ^ N‖ * ‖S^[N] y‖ := norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) N) (PadicInt.norm_le_one _))
  have htend0 : Tendsto (fun N => (2 : ℤ_[2]) ^ N * S^[N] y) atTop (nhds 0) :=
    squeeze_zero_norm hb0 (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h2lt)
  have htendpart : Tendsto (fun N => ∑ i ∈ Finset.range N, (parity (S^[i] y) : ℤ_[2]) * 2 ^ i)
      atTop (nhds y) := by
    have heq : (fun N => ∑ i ∈ Finset.range N, (parity (S^[i] y) : ℤ_[2]) * 2 ^ i)
        = fun N => y - (2 : ℤ_[2]) ^ N * S^[N] y := by
      funext N; exact eq_sub_of_add_eq (hrem N).symm
    rw [heq]
    simpa using tendsto_const_nhds.sub htend0
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat htendpart

/-- **(1.5) (proved).** The inverse conjugacy map is given by the explicit formula `Φ⁻¹ = Q` —
**Bernstein's noniterative 2-adic statement** [Ber94], here **proved** (was a cited `axiom`). *Proof:*
by `tsum_parity_S`, `Φ⁻¹ x = ∑ᵢ parity(Sⁱ(Φ⁻¹ x))·2ⁱ`; the inverse semiconjugacy `Sⁱ ∘ Φ⁻¹ = Φ⁻¹ ∘ T₂ⁱ`
(from `Φ_semiconj`) and the parity preservation `parity ∘ Φ⁻¹ = parity` (from `Φ_parity`) rewrite the
`i`-th digit as `parity(T₂ⁱ x)` — exactly the `i`-th digit of `Q x`. (From this formula one re-derives
`(1.3)` and `(1.4)`, and reads off that `Φ⁻¹` is solenoidal — see `Q_solenoidal`.) It now rests only on
the more basic cited axioms `exists_normalized_conjugacy` (for `Φ`) and `Φ_solenoidal` (via `Φ_parity`),
not on a standalone `(1.5)` axiom. -/
@[category research solved, AMS 11 37, ref "BL96" "Lag85" "Ber94", group "bl_conjugacy_map"]
theorem Φ_symm_eq_Q : ⇑Φ.symm = Q := by
  have hsc : ∀ w, Φ.symm (T₂ w) = S (Φ.symm w) := by
    intro w
    apply Φ.injective
    rw [Φ.apply_symm_apply, Φ_semiconj (Φ.symm w), Φ.apply_symm_apply]
  have hiter : ∀ (i : ℕ) (x : ℤ_[2]), S^[i] (Φ.symm x) = Φ.symm (T₂^[i] x) := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hsc]
  have hpar : ∀ z, parity (Φ.symm z) = parity z := by
    intro z
    have h := Φ_parity (Φ.symm z)
    rw [Φ.apply_symm_apply] at h
    exact h.symm
  funext x
  unfold Q
  rw [← tsum_parity_S (Φ.symm x)]
  apply tsum_congr
  intro i
  rw [hiter i x, hpar (T₂^[i] x)]

/-- **(cited; via the formula (1.5).)** `Φ⁻¹` (`= Q`) is **solenoidal**: a congruence `x ≡ y (mod 2ⁿ)`
makes the first `n` orbit parities agree, so `Q x ≡ Q y (mod 2ⁿ)`. -/
@[category research solved, AMS 11 37, ref "BL96" "Lag85", group "bl_conjugacy_map"]
axiom Q_solenoidal : Solenoidal Q

/-! ### The explicit formula for `Φ` (1.6)

The dual of `(1.5)`: an explicit formula for the **forward** map `Φ` in terms of the **binary
expansion** of `x` (rather than the parities of its `T₂`-orbit). It uses the multiplicative inverse
of `3`, which exists because `3` is a unit in `ℤ₂` (it is odd). -/

/-- `3` is a **unit** in `ℤ₂`: it is odd (`3 ≢ 0 (mod 2)`, equivalently `2 ∤ 3`, so `‖3‖ = 1`).
Hence `3` has a genuine multiplicative inverse in `ℤ₂` (`Ring.inverse 3`, `three_mul_inverse`),
needed to state the explicit formula `(1.6)`. (Note `ℤ₂` is *not* a field — `2` is not a unit — so
there is no blanket `⁻¹`; only units like `3` are invertible.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem isUnit_three : IsUnit (3 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  have h : ¬ (2 : ℤ_[2]) ∣ (3 : ℤ_[2]) := by
    rw [two_dvd_iff_toZMod_eq_zero]
    have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 1 := by
      have e : (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) := by norm_num
      rw [e, map_natCast]; decide
    rw [h3]; decide
  rcases lt_or_eq_of_le (PadicInt.norm_le_one (3 : ℤ_[2])) with hlt | heq
  · exact absurd ((PadicInt.norm_lt_one_iff_dvd _).mp hlt) h
  · exact heq

/-- The genuine inverse of `3` in `ℤ₂`: `3 · Ring.inverse 3 = 1` (since `3` is a unit,
`isUnit_three`). So in the formula `(1.6)`, `Ring.inverse 3` is the true `3⁻¹ ∈ ℤ₂`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem three_mul_inverse : (3 : ℤ_[2]) * Ring.inverse 3 = 1 :=
  Ring.mul_inverse_cancel 3 isUnit_three

/-- **(1.6) (cited; [2] = [Ber94]).** **Explicit formula for `Φ` itself**, dual to `(1.5)`. Expand
`x ∈ ℤ₂` in binary by the positions of its `1`-bits, `x = ∑ᵢ 2^{dᵢ}` with `0 ≤ d₀ < d₁ < ⋯` a
strictly increasing sequence (here the *infinite* case, `d : ℕ → ℕ` strictly monotone — e.g. any
`x ∉ ℕ`, which has infinitely many `1`-bits). Then
`Φ(x) = − ∑ᵢ 3^{−(i+1)} 2^{dᵢ}`:
the `i`-th `1`-bit (at position `dᵢ`) contributes `−3^{−(i+1)} 2^{dᵢ}` (`3⁻¹ = Ring.inverse 3`,
`three_mul_inverse`; the exponent `i+1` is the `1`-based rank of the bit). E.g. `Φ 1 = Φ (2⁰) = −3⁻¹`.
From `(1.6)` one re-derives `(1.3)` and `(1.4)`, and reads off that `Φ` is solenoidal
(`Φ_solenoidal`). The finite case `x ∈ ℕ` is `Φ_eq_neg_sum`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94", group "bl_conjugacy_map"]
axiom Φ_eq_neg_tsum (d : ℕ → ℕ) (hd : StrictMono d) :
    Φ (∑' i, (2 : ℤ_[2]) ^ (d i)) = - ∑' i, (Ring.inverse (3 : ℤ_[2])) ^ (i + 1) * 2 ^ (d i)

/-- **(1.6), finite case** (cited; [2] = [Ber94]). For a **nonnegative integer**
`x = ∑_{i<m} 2^{dᵢ} ∈ ℕ` — finitely many `1`-bits, `d : Fin m → ℕ` strictly increasing — the explicit
formula reads `Φ(x) = − ∑_{i<m} 3^{−(i+1)} 2^{dᵢ}`. (The general `(1.6)` allows a *finite or
infinite* `1`-bit sequence; this is the finite branch, `Φ_eq_neg_tsum` the infinite one.) -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94", group "bl_conjugacy_map"]
axiom Φ_eq_neg_sum (m : ℕ) (d : Fin m → ℕ) (hd : StrictMono d) :
    Φ (∑ i, (2 : ℤ_[2]) ^ (d i)) = - ∑ i, (Ring.inverse (3 : ℤ_[2])) ^ (i.val + 1) * 2 ^ (d i)

/-! ### The 3x+1 conjecture in 2-adic form -/

/-- **The 3x+1 conjecture: 2-adic form ⟺ integer form.** Since `T₂` extends the integer 3x+1 map
(`T₂_natCast`/`T₂_iterate_natCast`), the 2-adic reachability statement
`∀ n>0, ∃ j, T₂ʲ(↑n) = 1` is **equivalent** to the elementary **3x+1 conjecture**
`∀ n>0, ∃ j, Tʲ(n) = 1` (every positive integer reaches `1` under the accelerated map
`CC.T`). **Proved** (sorry-free), *not* assumed: both directions follow from
`T₂ʲ ↑n = ↑(Tʲ n)` and injectivity of `ℕ ↪ ℤ₂`. We assert neither side — only their equivalence;
the conjecture itself stays open and is never named as a `Prop` (per the corpus policy, it is written
inline in the `∀ n>0, ∃ j, Tʲ(n)=1` form). The 2-adic side is exactly the assertion that `T₂` sends
every positive integer to `1`; the conjugacy map `Φ` and the explicit formulas `(1.5)`/`(1.6)` are the
machinery the paper builds toward studying it. -/
@[category API, AMS 11 37, ref "BL96"]
theorem t2_reachesOne_iff_collatz :
    (∀ n : ℕ, 0 < n → ∃ j, (T₂^[j]) (n : ℤ_[2]) = 1) ↔
    (∀ n : ℕ, 0 < n → ∃ j, CC.T_iter j n = 1) := by
  constructor
  · intro h n hn
    obtain ⟨j, hj⟩ := h n hn
    refine ⟨j, ?_⟩
    rw [T₂_iterate_natCast] at hj
    exact_mod_cast hj
  · intro h n hn
    obtain ⟨j, hj⟩ := h n hn
    exact ⟨j, by rw [T₂_iterate_natCast, hj, Nat.cast_one]⟩

/-! ### The Periodicity Conjecture and divergent trajectories (BL96, §1) -/

/-- The **rational 2-adic integers** `ℚ ∩ ℤ₂`: the `x : ℤ₂` whose image in `ℚ₂` is a rational number.
Equivalently, the `x ∈ ℤ₂` with eventually-periodic binary expansion — the rationals with odd
denominator. The conjugacy map `Φ` is conjectured to preserve this set. -/
@[category API, AMS 11 37, ref "BL96"]
def RatInt : Set ℤ_[2] := {x | ∃ q : ℚ, (x : ℚ_[2]) = (q : ℚ_[2])}

/-- **Periodicity Conjecture (Bernstein–Lagarias 1996).** The 3x+1 conjugacy map `Φ` maps the
rational 2-adic integers **onto themselves**: `Φ(ℚ ∩ ℤ₂) = ℚ ∩ ℤ₂`. This is **open** — recorded as a
`sorry`ed `research open` statement (never an `axiom`, per the corpus policy on open conjectures). It
would imply that the 3x+1 map has no divergent trajectories
(`periodicity_imp_no_divergent_trajectories`). -/
@[category research open, AMS 11 37, ref "BL96", group "bl_periodicity_conjecture"]
theorem periodicity_conjecture : (⇑Φ) '' RatInt = RatInt := by
  sorry

/-! #### Divergent trajectories and the iteration dichotomy

`divergent_iff_tendsto_atTop` proves the equivalence of the two descriptions BL96 gives of a
*divergent* trajectory ("infinitely many distinct elements" `=` "`Tᵏ(n) → ∞`"), via a general fact
about iterating a map on `ℕ`. -/

/-- If an orbit `k ↦ f^[k] n` of a map `f : ℕ → ℕ` **repeats** a value (`f^[i] n = f^[j] n`, `i < j`)
then it is eventually periodic, so it takes only **finitely many** distinct values: `f^[i] n` is a
periodic point of period `j - i`, and `IsPeriodicPt.iterate_mod_apply` folds every later iterate back
into the first `j`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem orbit_range_finite_of_eq {f : ℕ → ℕ} {n i j : ℕ} (hlt : i < j)
    (heq : f^[i] n = f^[j] n) : (Set.range fun k => f^[k] n).Finite := by
  have hp0 : 0 < j - i := by omega
  have hper : Function.IsPeriodicPt f (j - i) (f^[i] n) := by
    show f^[j - i] (f^[i] n) = f^[i] n
    rw [← Function.iterate_add_apply]
    have hji : j - i + i = j := by omega
    rw [hji, ← heq]
  apply Set.Finite.subset (Set.finite_range (fun m : Fin j => f^[m.val] n))
  rintro y ⟨k, rfl⟩
  rcases lt_or_ge k j with hk | hk
  · exact ⟨⟨k, hk⟩, rfl⟩
  · refine ⟨⟨(k - i) % (j - i) + i, ?_⟩, ?_⟩
    · have := Nat.mod_lt (k - i) hp0; omega
    · show f^[(k - i) % (j - i) + i] n = f^[k] n
      rw [Function.iterate_add_apply, hper.iterate_mod_apply, ← Function.iterate_add_apply]
      congr 1; omega

/-- **The iteration dichotomy.** For an iterated map `f : ℕ → ℕ`, the orbit `k ↦ f^[k] n` has
**infinitely many distinct values iff it diverges to `∞`**:
`(range (f^[·] n)).Infinite ↔ f^[·] n → ∞`. Determinism forces the dichotomy: an orbit either repeats
— then it is eventually periodic and bounded (`orbit_range_finite_of_eq`) — or is injective — then it
tends to `∞` (`Injective.nat_tendsto_atTop`, each value of `ℕ` being hit at most once). This underlies
the two equivalent descriptions of a *divergent* trajectory in BL96 §1. -/
@[category API, AMS 11 37, ref "BL96"]
theorem range_iterate_infinite_iff_tendsto (f : ℕ → ℕ) (n : ℕ) :
    (Set.range fun k => f^[k] n).Infinite ↔ Tendsto (fun k => f^[k] n) atTop atTop := by
  constructor
  · intro hinf
    have hinj : Function.Injective (fun k => f^[k] n) := by
      by_contra hni
      rw [Function.not_injective_iff] at hni
      obtain ⟨a, b, hfab, hne⟩ := hni
      refine hinf ?_
      rcases lt_or_gt_of_ne hne with h | h
      · exact orbit_range_finite_of_eq h hfab
      · exact orbit_range_finite_of_eq h hfab.symm
    exact hinj.nat_tendsto_atTop
  · intro htend
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨k, hk⟩ := (htend.eventually_ge_atTop (B + 1)).exists
    have : f^[k] n ≤ B := hB ⟨k, rfl⟩
    omega

/-- The `CC` Collatz/Terras iterate `T_iter` is `Function.iterate` of `CC.T`:
`T_iter k n = T^[k] n` — bridging `CC`'s bespoke recursion to the general `f^[k]` API. -/
@[category API, AMS 11 37, ref "BL96"]
theorem T_iter_eq_iterate (k n : ℕ) :
    CC.T_iter k n = CC.T^[k] n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [CC.T_iter, Function.iterate_succ_apply', ih]

/-- A 3x+1 trajectory `{Tᵏ(n)}` is **divergent** if it contains **infinitely many distinct
elements** (BL96 §1). Stated with `CC.T_iter`, the accelerated map of `CC`
(cf. `CC/Elementary.lean`). Equivalent to `Tᵏ(n) → ∞` (`divergent_iff_tendsto_atTop`). -/
@[category API, AMS 11 37, ref "BL96"]
def Divergent (n : ℕ) : Prop := (Set.range fun k => CC.T_iter k n).Infinite

/-- **Equivalence of the two descriptions of a divergent trajectory** (BL96 §1, the "so that"):
`Divergent n ↔ Tᵏ(n) → ∞`. A 3x+1 trajectory has infinitely many distinct elements iff
`|Tᵏ(n)| → ∞ as k → ∞`. **Proved** from the iteration dichotomy
(`range_iterate_infinite_iff_tendsto`) and `T_iter_eq_iterate`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem divergent_iff_tendsto_atTop (n : ℕ) :
    Divergent n ↔ Tendsto (fun k => CC.T_iter k n) atTop atTop := by
  simp only [Divergent, T_iter_eq_iterate]
  exact range_iterate_infinite_iff_tendsto CC.T n

/-- **The Periodicity Conjecture implies no divergent trajectories** (BL96 §1). If `Φ` preserves
`ℚ ∩ ℤ₂` (`periodicity_conjecture`), then the 3x+1 map has **no divergent trajectory**: every positive
integer's trajectory has only finitely many distinct values (`∀ n > 0, ¬ Divergent n`, equivalently no
`Tᵏ(n) → ∞`). **Open** (`sorry`ed `research open`): this is the paper's stated consequence, not proved
here. The no-divergence statement is kept **inline** as `∀ n > 0, ¬ Divergent n`, never named — as with
the 3x+1 conjecture itself (`t2_reachesOne_iff_collatz`). -/
@[category research open, AMS 11 37, ref "BL96", group "bl_periodicity_conjecture"]
theorem periodicity_imp_no_divergent_trajectories
    (_hper : (⇑Φ) '' RatInt = RatInt) : ∀ n : ℕ, 0 < n → ¬ Divergent n := by
  sorry

/-! ### The Fixed Point Conjecture (BL96, §1)

`Φ` has the obvious fixed point `0` (`Φ 0 = 0`). Bernstein–Lagarias searched for *odd* (rational) fixed
points and found exactly two — `-1` and `1/3` — and conjecture these are the only ones. We verify both
are odd, prove that `-1` is genuinely a fixed point, and record the conjecture (open). -/

/-- `-1 = …111₂` is **odd**: `parity (-1) = 1` (`toZMod (-1) = -1 = 1` in `ZMod 2`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_neg_one : parity (-1 : ℤ_[2]) = 1 := by
  unfold parity
  have h : PadicInt.toZMod (-1 : ℤ_[2]) = 1 := by rw [map_neg, map_one]; decide
  rw [h]; decide

/-- `1/3 = Ring.inverse 3` is **odd**: `parity (1/3) = 1`. (`toZMod` is a ring hom and `toZMod 3 = 1`, so
`toZMod (1/3) = (toZMod 3)⁻¹ = 1`; `3` and its inverse are units, hence odd.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_inv_three : parity (Ring.inverse 3 : ℤ_[2]) = 1 := by
  unfold parity
  have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 1 := by
    have e : (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) := by norm_num
    rw [e, map_natCast]; decide
  have hmul : PadicInt.toZMod (3 : ℤ_[2]) * PadicInt.toZMod (Ring.inverse 3 : ℤ_[2]) = 1 := by
    rw [← map_mul, three_mul_inverse, map_one]
  rw [h3, one_mul] at hmul
  rw [hmul]; decide

/-- **The fixed points of `T₂` are exactly `0` and `-1`.** If `T₂ y = y` then
`2y = y·3^{parity y} + parity y`: for even `y` this collapses to `y = 0`, for odd `y` to `3y + 1 = 2y`,
i.e. `y = -1`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem eq_zero_or_neg_one_of_T₂_fixed {y : ℤ_[2]} (h : T₂ y = y) : y = 0 ∨ y = -1 := by
  have hnum := two_mul_T₂ y
  rw [h] at hnum
  unfold numer at hnum
  have hp : parity y = 0 ∨ parity y = 1 := by
    have hlt : parity y < 2 := by unfold parity; exact (PadicInt.toZMod y).val_lt
    omega
  rcases hp with hp0 | hp1
  · left
    rw [hp0] at hnum
    simp only [pow_zero, mul_one, Nat.cast_zero, add_zero] at hnum
    linear_combination hnum
  · right
    rw [hp1] at hnum
    simp only [pow_one, Nat.cast_one] at hnum
    linear_combination -hnum

/-- `-1` is the **fixed point of the shift** `S` (besides `0`): `S(-1) = -1`. As `-1 = …111₂`, deleting
its lowest digit leaves `…111₂ = -1`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem S_neg_one : S (-1 : ℤ_[2]) = -1 := by
  have h2 : (2 : ℤ_[2]) * S (-1) = 2 * (-1) := by
    rw [two_mul_S, parity_neg_one]; push_cast; ring
  exact mul_left_cancel₀ (by norm_num) h2

/-- **`-1` is a fixed point of `Φ`** — one of the two odd fixed points the paper found. Proof: `S` fixes
`-1` (`S_neg_one`), so `Φ(-1) = Φ(S(-1)) = T₂(Φ(-1))` (`Φ_semiconj`) is a `T₂`-fixed point, hence `0` or
`-1` (`eq_zero_or_neg_one_of_T₂_fixed`); it is not `0`, since `Φ 0 = 0` with `Φ` injective. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_fixed_point_conjecture"]
theorem Φ_neg_one : Φ (-1 : ℤ_[2]) = -1 := by
  have hfix : T₂ (Φ (-1)) = Φ (-1) := by
    have hs := Φ_semiconj (-1 : ℤ_[2])
    rw [S_neg_one] at hs
    exact hs.symm
  rcases eq_zero_or_neg_one_of_T₂_fixed hfix with h0 | hm1
  · exfalso
    rw [← Φ_apply_zero] at h0
    have hcontra := Φ.injective h0
    norm_num at hcontra
  · exact hm1

/-- The two found odd fixed points are **distinct**: `-1 ≠ 1/3` (else `-3 = 3·(-1) = 3·(1/3) = 1`). So
"exactly two" really is two. -/
@[category API, AMS 11 37, ref "BL96"]
theorem neg_one_ne_inv_three : (-1 : ℤ_[2]) ≠ Ring.inverse 3 := by
  intro h
  have hcontra : (3 : ℤ_[2]) * (-1) = 1 := by rw [h, three_mul_inverse]
  norm_num at hcontra

/-- **Fixed Point Conjecture (Bernstein–Lagarias 1996).** The 3x+1 conjugacy map `Φ` has **exactly two
odd fixed points**, `-1` and `1/3`: the set of odd fixed points is `{-1, 1/3}`. **Open** — recorded as a
`sorry`ed `research open` statement (never an `axiom`). The `⊇` inclusion is *known*: `-1` is a fixed
point (`Φ_neg_one`, proved here) and `1/3 = Ring.inverse 3` is one (the paper's computation, via the
explicit formula `(1.6)`), both odd (`parity_neg_one`, `parity_inv_three`) and distinct
(`neg_one_ne_inv_three`); the open content is `⊆`, that there is no *other* odd fixed point. -/
@[category research open, AMS 11 37, ref "BL96", group "bl_fixed_point_conjecture"]
theorem fixed_point_conjecture :
    {x : ℤ_[2] | Φ x = x ∧ parity x = 1} = {-1, Ring.inverse 3} := by
  sorry

/-! ### The Conjugacy Finiteness Conjecture (BL96, §1) -/

/-- **3x+1 Conjugacy Finiteness Conjecture (Bernstein–Lagarias 1996).** For each `j ≥ 0`, the conjugacy
map `Φ` has **finitely many odd periodic points of period `2ʲ`** — i.e. the set of odd `x` with
`Φ^[2ʲ] x = x` (`Function.IsPeriodicPt Φ (2ʲ) x`) is finite. **Open** — recorded as a `sorry`ed
`research open` statement (never an `axiom`). It generalises the Fixed Point Conjecture: the `j = 0`
case (period `2⁰ = 1`) is finiteness of the odd *fixed* points, which `fixed_point_conjecture` sharpens
to "exactly two" (`conjugacy_finiteness_zero_of_fixed_point`). -/
@[category research open, AMS 11 37, ref "BL96", group "bl_finiteness_conjecture"]
theorem conjugacy_finiteness_conjecture (j : ℕ) :
    {x : ℤ_[2] | (⇑Φ)^[2 ^ j] x = x ∧ parity x = 1}.Finite := by
  sorry

/-- The `j = 0` case of the Finiteness Conjecture (period `2⁰ = 1`, i.e. odd *fixed* points) **follows
from the Fixed Point Conjecture**: if the odd fixed points are exactly `{-1, 1/3}`, they are in
particular finite. (`Φ^[2⁰] = Φ^[1] = Φ`.) A `sorry`-free reduction between the two conjectures. -/
@[category API, AMS 11 37, ref "BL96", group "bl_finiteness_conjecture"]
theorem conjugacy_finiteness_zero_of_fixed_point
    (h : {x : ℤ_[2] | Φ x = x ∧ parity x = 1} = {-1, Ring.inverse 3}) :
    {x : ℤ_[2] | (⇑Φ)^[2 ^ 0] x = x ∧ parity x = 1}.Finite := by
  simp only [pow_zero, Function.iterate_one]
  rw [h]
  exact (Set.finite_singleton _).insert _

/-! ### Nowhere differentiability of `Φ` and `Φ⁻¹` (cited)

A first **analytic** property of the conjugacy map. BL96 only *remarks* it (§1, p. 1156) and attributes
the proof to the literature ([10] = Müller, [2] = Ber94); we record it as cited `axiom`s. -/

/-- The **2-adic difference quotient** of `f : ℤ₂ → ℤ₂` at `x`, evaluated at `y`: `(f y - f x)/(y - x)`
computed in the fraction field `ℚ₂` (so the division makes sense for `y ≠ x`). -/
@[category API, AMS 11 26, ref "BL96"]
noncomputable def diffQuotient (f : ℤ_[2] → ℤ_[2]) (x y : ℤ_[2]) : ℚ_[2] :=
  ((f y - f x : ℤ_[2]) : ℚ_[2]) / ((y : ℚ_[2]) - (x : ℚ_[2]))

/-- `f : ℤ₂ → ℤ₂` is **2-adically differentiable at `x`** if its difference quotient
`(f y - f x)/(y - x)` (in `ℚ₂`) converges to some limit as `y → x` with `y ≠ x`. -/
@[category API, AMS 11 26, ref "BL96"]
def DifferentiableAt2 (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : Prop :=
  ∃ L : ℚ_[2], Filter.Tendsto (diffQuotient f x) (nhdsWithin x {x}ᶜ) (nhds L)

/-- `f : ℤ₂ → ℤ₂` is **nowhere 2-adically differentiable** if it is differentiable at no point of `ℤ₂`. -/
@[category API, AMS 11 26, ref "BL96"]
def NowhereDifferentiable2 (f : ℤ_[2] → ℤ_[2]) : Prop := ∀ x, ¬ DifferentiableAt2 f x

/-- **(cited; BL96 §1 remark, p. 1156; [10] = [Mueller91], [2] = [Ber94].)** The 3x+1 conjugacy map `Φ`
is **nowhere differentiable** on `ℤ₂`. Not proved in BL96 (a remark attributed to Müller and Bernstein);
recorded here as a cited `axiom`, not formalised from those sources. -/
@[category research solved, AMS 11 26, ref "BL96" "Mueller91" "Ber94", group "bl_differentiability"]
axiom Φ_nowhereDifferentiable : NowhereDifferentiable2 (⇑Φ)

/-- **(cited; BL96 §1 remark, p. 1156; [10] = [Mueller91], [2] = [Ber94].)** The inverse conjugacy map
`Φ⁻¹` is **nowhere differentiable** on `ℤ₂`. -/
@[category research solved, AMS 11 26, ref "BL96" "Mueller91" "Ber94", group "bl_differentiability"]
axiom Φsymm_nowhereDifferentiable : NowhereDifferentiable2 (⇑Φ.symm)

/-- The explicit inverse `Q = Φ⁻¹` (`(1.5)`, `Φ_symm_eq_Q`) is **nowhere differentiable** — the same
statement as `Φsymm_nowhereDifferentiable`, transported along `(1.5)`. -/
@[category research solved, AMS 11 26, ref "BL96" "Mueller91" "Ber94", group "bl_differentiability"]
theorem Q_nowhereDifferentiable : NowhereDifferentiable2 Q :=
  Φ_symm_eq_Q ▸ Φsymm_nowhereDifferentiable

end BL
