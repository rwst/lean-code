/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — Appendix B: functions solenoidally conjugate to the shift (BL96, §8)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

Appendix B (§8) of the paper. For any two solenoidal bijections `V₀, V₁ : ℤ₂ → ℤ₂` one builds a new
map `U_{V₀,V₁} : ℤ₂ → ℤ₂` by **interleaving them through the shift**:

  `U(x) = V₀(x/2)`      if `x ≡ 0 (mod 2)`,
  `U(x) = V₁((x-1)/2)`  if `x ≡ 1 (mod 2)`.

Both branches feed `V` the **shift** `S x` of `x` (`BL.S`, which deletes the lowest binary digit:
`S x = x/2` for even `x`, `(x-1)/2` for odd `x` — `BL.two_mul_S`). So uniformly

  `U(x) = V_{parity x}(S x)`   (`shiftConj`).

The functions `U` arising this way are the ones "solenoidally conjugate to the shift": `V₀, V₁`
act on the deleted-digit part while the lowest bit selects which one.

**The example (BL96, §8).** Taking `V₀ = id` and `V₁(y) = a·y + (a+b)/2` makes `U` the
**`ax+b` function** — even `x ↦ x/2`, odd `x ↦ (ax+b)/2` (`shiftConj_id_axbMap`). For `a = 3, b = 1`
this is the `3x+1` map `T₂` of `BL.Basic` (`axbMap_three_one`, `shiftConj_eq_T₂`).

## Contents
* `shiftConj` — the construction `U_{V₀,V₁}(x) = V_{parity x}(S x)`, with the case lemmas
  `shiftConj_even`, `shiftConj_odd`.
* `lemma_B1` — **Lemma B.1**: for a solenoidal bijection `V`, `z ≡ w (mod 2ᵐ) ⟹
  V(z) ≡ V(w) + (z − w) (mod 2ᵐ⁺¹)` (via the isometry `corollary_A3` and the two-lift fact
  `dvd_sub_pow_of_not_dvd`).
* `lemma_B2` — **Lemma B.2**: for `U = U_{V₀,V₁}` (solenoidal-bijection inputs) and `m = k+1 ≥ 1`,
  `y ≡ x + 2ᵐ·e (mod 2ᵐ⁺¹) ⟹ U(y) ≡ U(x) + 2ᵐ⁻¹·e (mod 2ᵐ)` (same-branch reduction + `lemma_B1`).
* `lemma_B3` — **Lemma B.3**: the iterate `Uʲ(y) ≡ Uʲ(x) + 2ᵐ⁻ʲ·e (mod 2ᵐ⁻ʲ⁺¹)` for `m ≥ j ≥ 1`
  (induction on `j` from `lemma_B2`; indexed `m = j+d`, holds for all `j ≥ 0`).
* `lemma_B4` — **Lemma B.4**: the `j = m` case, `Uᵐ(y) ≡ Uᵐ(x) + e (mod 2)` (top bit survives to the
  bottom after `m` iterations).
* `xSeq`, `lemma_B5` — **Lemma B.5**: the sequence `x₀=0`, `x_{m+1}=x_m+2ᵐ(b_m−Uᵐ(x_m))` and the
  equivalence `y ≡ x_m (mod 2ᵐ) ↔ ∀ i<m, Uⁱ(y) ≡ b_i (mod 2)` (induction on `m` via `lemma_B4`).
* `qIter`, `qConj`, `theorem_B1` — **Theorem B.1**: the itinerary map `qIter f x = ∑ᵢ parity(fⁱ x)·2ⁱ`
  (general, mirrors `BL.qMap`) and its specialisation `Q = qConj V₀ V₁` to `U = U_{V₀,V₁}`; `Q` is a
  **solenoidal bijection** conjugating `U` to the shift (`Q∘U = S∘Q`, i.e. `U = Q⁻¹∘S∘Q`). Built from
  `qIter_semiconj` (conjugacy) and `lemma_B5` (injective/surjective/solenoidal, since `U` itself is
  not solenoidal). So every `U_{V₀,V₁}` is solenoidally conjugate to `S`.
* `theorem_B2` — **Theorem B.2** (converse): for any solenoidal bijection `Q`, the conjugate
  `U = Q⁻¹∘S∘Q` of the shift is `U_{V₀,V₁}` for solenoidal bijections `V_b(w) = U(2w+b)` (each an
  isometry by `corollary_A3`). With B.1: the `U_{V₀,V₁}` are *exactly* the solenoidal conjugates of `S`.
* `axbNumer`, `even_axbNumer`, `axbMap`, `two_mul_axbMap` — the `ax+b` function as `numer/2`
  (generalising `BL.numer`/`BL.T₂`; needs `2 ∣ a+b` so the odd branch halves).
* `shiftConj_id_axbMap` — **the example**: `U_{id, a·+(a+b)/2}` is the `ax+b` function.
* `axbMap_three_one`, `shiftConj_eq_T₂` — the `a=3, b=1` case recovers the `3x+1` map `T₂`.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169 (Appendix B / §8).
-/

namespace BL

open PadicInt

/-! ### The construction `U_{V₀,V₁}` -/

/-- **Appendix B construction (BL96 §8).** For functions `V₀, V₁ : ℤ₂ → ℤ₂` (the paper takes them
solenoidal bijections), `U_{V₀,V₁}` interleaves them through the shift:
`U(x) = V₀(x/2)` if `x` is even, `V₁((x-1)/2)` if `x` is odd. As `x/2` (even) and `(x-1)/2` (odd) are
both the shift `S x` (`BL.two_mul_S`), uniformly `U(x) = V_{parity x}(S x)`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def shiftConj (V₀ V₁ : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : ℤ_[2] :=
  if parity x = 0 then V₀ (S x) else V₁ (S x)

/-- On **even** `x` the construction is `U(x) = V₀(x/2) = V₀(S x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem shiftConj_even (V₀ V₁ : ℤ_[2] → ℤ_[2]) {x : ℤ_[2]} (h : parity x = 0) :
    shiftConj V₀ V₁ x = V₀ (S x) := by
  rw [shiftConj, ite_eq_left h]

/-- On **odd** `x` the construction is `U(x) = V₁((x-1)/2) = V₁(S x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem shiftConj_odd (V₀ V₁ : ℤ_[2] → ℤ_[2]) {x : ℤ_[2]} (h : parity x = 1) :
    shiftConj V₀ V₁ x = V₁ (S x) := by
  rw [shiftConj, ite_eq_right (by rw [h]; decide)]

/-- The parity of a 2-adic integer is `0` or `1`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_eq_zero_or_one (x : ℤ_[2]) : parity x = 0 ∨ parity x = 1 := by
  have hlt : parity x < 2 := by unfold parity; exact (PadicInt.toZMod x).val_lt
  omega

/-- The residue `toZMod x` equals the (cast) parity: `↑(parity x) = toZMod x` in `ZMod 2`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem toZMod_eq_parity (x : ℤ_[2]) : ((parity x : ℕ) : ZMod 2) = PadicInt.toZMod x := by
  unfold parity; rw [ZMod.natCast_val, ZMod.cast_id]

/-! ### Lemma B.1: the residue-`2ᵐ` derivative of a solenoidal bijection

A solenoidal bijection `V` is a 2-adic isometry (Corollary A.3), so it not only *preserves* a
congruence `mod 2ᵐ` but is "rigid one bit further": the next bit of `V(z) − V(w)` is forced to equal
the next bit of `z − w`. Concretely (BL96 Lemma B.1, here indexed `m-1 ↦ m`, `m ↦ m+1` to avoid
`ℕ`-subtraction): `z ≡ w (mod 2ᵐ) ⟹ V(z) ≡ V(w) + (z − w) (mod 2ᵐ⁺¹)`. -/

/-- **Two lifts mod `2ᵐ⁺¹`.** If `2ᵐ ∣ a` but `2ᵐ⁺¹ ∤ a`, then `a ≡ 2ᵐ (mod 2ᵐ⁺¹)`, i.e.
`2ᵐ⁺¹ ∣ (a − 2ᵐ)`. (Writing `a = 2ᵐ·u`, the hypotheses force `u` odd, so `u − 1` is even.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem dvd_sub_pow_of_not_dvd {a : ℤ_[2]} {m : ℕ} (hm : (2 : ℤ_[2]) ^ m ∣ a)
    (hnm : ¬ (2 : ℤ_[2]) ^ (m + 1) ∣ a) : (2 : ℤ_[2]) ^ (m + 1) ∣ (a - 2 ^ m) := by
  obtain ⟨u, rfl⟩ := hm
  have hu : ¬ (2 : ℤ_[2]) ∣ u :=
    fun hdvd => hnm (by rw [pow_succ]; exact mul_dvd_mul_left _ hdvd)
  have hu0 : PadicInt.toZMod u ≠ 0 := fun h => hu ((two_dvd_iff_toZMod_eq_zero u).mpr h)
  have hu1 : PadicInt.toZMod u = 1 := by
    have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases hcases (PadicInt.toZMod u) with h | h
    · exact absurd h hu0
    · exact h
  have hdvdu1 : (2 : ℤ_[2]) ∣ (u - 1) := by
    rw [two_dvd_iff_toZMod_eq_zero, map_sub, hu1, map_one, sub_self]
  have heq : (2 : ℤ_[2]) ^ m * u - 2 ^ m = 2 ^ m * (u - 1) := by ring
  rw [heq, pow_succ]
  exact mul_dvd_mul_left _ hdvdu1

/-- **Lemma B.1 (Bernstein–Lagarias).** Let `V` be a **solenoidal bijection**. If `z ≡ w (mod 2ᵐ)`
then `V(z) ≡ V(w) + (z − w) (mod 2ᵐ⁺¹)`. (The paper's statement, with `m-1, m` rather than `m, m+1`.)
**Proved.** Split on whether `2ᵐ⁺¹ ∣ (z − w)`. If so, solenoidality gives `2ᵐ⁺¹ ∣ (V z − V w)` and the
claim is a subtraction. If not, then `z − w ≡ 2ᵐ (mod 2ᵐ⁺¹)` (`dvd_sub_pow_of_not_dvd`); since `V` is
an **isometry** (`corollary_A3`) it reflects congruences, so `2ᵐ⁺¹ ∤ (V z − V w)` as well, whence
`V z − V w ≡ 2ᵐ (mod 2ᵐ⁺¹)` too — the two `2ᵐ`'s cancel. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem lemma_B1 {V : ℤ_[2] → ℤ_[2]} (hsol : Solenoidal V) (hbij : Function.Bijective V)
    (m : ℕ) {z w : ℤ_[2]} (hzw : (2 : ℤ_[2]) ^ m ∣ (z - w)) :
    (2 : ℤ_[2]) ^ (m + 1) ∣ (V z - (V w + (z - w))) := by
  have hb_m : (2 : ℤ_[2]) ^ m ∣ (V z - V w) := hsol m z w hzw
  have hiso : ∀ x y, ‖V x - V y‖ = ‖x - y‖ :=
    ((corollary_A3 V).out 1 3).mp (⟨hsol, hbij⟩ : Solenoidal V ∧ Function.Bijective V)
  have hrefl : ∀ n : ℕ, ((2 : ℤ_[2]) ^ n ∣ (V z - V w) ↔ (2 : ℤ_[2]) ^ n ∣ (z - w)) := fun n => by
    rw [dvd_pow_iff_norm_le, dvd_pow_iff_norm_le, hiso z w]
  by_cases hc : (2 : ℤ_[2]) ^ (m + 1) ∣ (z - w)
  · have hb : (2 : ℤ_[2]) ^ (m + 1) ∣ (V z - V w) := hsol (m + 1) z w hc
    have he : V z - (V w + (z - w)) = (V z - V w) - (z - w) := by ring
    rw [he]; exact dvd_sub hb hc
  · have ha' : (2 : ℤ_[2]) ^ (m + 1) ∣ ((z - w) - 2 ^ m) := dvd_sub_pow_of_not_dvd hzw hc
    have hbnm : ¬ (2 : ℤ_[2]) ^ (m + 1) ∣ (V z - V w) := fun h => hc ((hrefl (m + 1)).mp h)
    have hb' : (2 : ℤ_[2]) ^ (m + 1) ∣ ((V z - V w) - 2 ^ m) := dvd_sub_pow_of_not_dvd hb_m hbnm
    have he : V z - (V w + (z - w)) = ((V z - V w) - 2 ^ m) - ((z - w) - 2 ^ m) := by ring
    rw [he]; exact dvd_sub hb' ha'

/-- **Lemma B.2 (Bernstein–Lagarias).** For `U = U_{V₀,V₁}` built from solenoidal bijections
`V₀, V₁`, and `m = k+1 ≥ 1`: if `y ≡ x + 2ᵐ·e (mod 2ᵐ⁺¹)` then `U(y) ≡ U(x) + 2ᵐ⁻¹·e (mod 2ᵐ)`.
Here `e : ℤ₂` is an arbitrary perturbation direction (a free variable, not a fixed constant). Indexed
`m = k+1`, the statement reads `y ≡ x + 2^{k+1}·e (mod 2^{k+2}) ⟹ U(y) ≡ U(x) + 2ᵏ·e (mod 2^{k+1})`.
**Proved**, following the paper: with `b = x mod 2`, the hypothesis forces `y ≡ x (mod 2)`, so the
two values use the **same** branch, `U(x) = V_b(S x)` and `U(y) = V_b(S y)`. Halving the congruence
(`2·(S y − S x) = y − x`) gives `S y ≡ S x + 2ᵏ·e (mod 2^{k+1})`, and `lemma_B1` applied to `V_b`
turns `S y ≡ S x (mod 2ᵏ)` into `V_b(S y) ≡ V_b(S x) + (S y − S x) ≡ V_b(S x) + 2ᵏ·e (mod 2^{k+1})`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem lemma_B2 {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) (k : ℕ) {x y e : ℤ_[2]}
    (hxy : (2 : ℤ_[2]) ^ (k + 2) ∣ (y - (x + 2 ^ (k + 1) * e))) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ (shiftConj V₀ V₁ y - (shiftConj V₀ V₁ x + 2 ^ k * e)) := by
  -- `y ≡ x (mod 2)`, so the parities agree and both values use the same branch
  have h2yx : (2 : ℤ_[2]) ∣ (y - x) := by
    have hd1 : (2 : ℤ_[2]) ∣ (y - (x + 2 ^ (k + 1) * e)) :=
      (dvd_pow_self 2 (Nat.succ_ne_zero (k + 1))).trans hxy
    have hd2 : (2 : ℤ_[2]) ∣ (2 ^ (k + 1) * e) :=
      (dvd_pow_self 2 (Nat.succ_ne_zero k)).mul_right e
    have he : y - x = (y - (x + 2 ^ (k + 1) * e)) + 2 ^ (k + 1) * e := by ring
    rw [he]; exact dvd_add hd1 hd2
  have hpar : parity y = parity x := by
    have htoz : PadicInt.toZMod y = PadicInt.toZMod x := by
      rw [← sub_eq_zero, ← map_sub]; exact (two_dvd_iff_toZMod_eq_zero _).mp h2yx
    unfold parity; rw [htoz]
  -- the shift halves the congruence: `2·(S y − S x) = y − x`
  have hSrel : 2 * (S y - S x) = y - x := by
    rw [mul_sub, two_mul_S, two_mul_S, hpar]; ring
  -- `S y ≡ S x + 2ᵏ·e (mod 2^{k+1})`, and a fortiori `S y ≡ S x (mod 2ᵏ)`
  have hSe : (2 : ℤ_[2]) ^ (k + 1) ∣ ((S y - S x) - 2 ^ k * e) := by
    have hrw : y - (x + 2 ^ (k + 1) * e) = 2 * ((S y - S x) - 2 ^ k * e) := by
      linear_combination -hSrel
    have hpow : (2 : ℤ_[2]) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    rw [hrw, hpow] at hxy
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ_[2]) ≠ 0)).mp hxy
  have hSdvd : (2 : ℤ_[2]) ^ k ∣ (S y - S x) := by
    have hA : (2 : ℤ_[2]) ^ k ∣ ((S y - S x) - 2 ^ k * e) :=
      (pow_dvd_pow 2 (Nat.le_succ k)).trans hSe
    have heq : S y - S x = ((S y - S x) - 2 ^ k * e) + 2 ^ k * e := by ring
    rw [heq]; exact dvd_add hA (dvd_mul_right _ _)
  -- core estimate for either branch `V`, via Lemma B.1
  have core : ∀ V : ℤ_[2] → ℤ_[2], Solenoidal V → Function.Bijective V →
      (2 : ℤ_[2]) ^ (k + 1) ∣ (V (S y) - (V (S x) + 2 ^ k * e)) := by
    intro V hV hVb
    have hB1 := lemma_B1 hV hVb k hSdvd
    have hcomb : V (S y) - (V (S x) + 2 ^ k * e)
        = (V (S y) - (V (S x) + (S y - S x))) + ((S y - S x) - 2 ^ k * e) := by ring
    rw [hcomb]; exact dvd_add hB1 hSe
  rcases parity_eq_zero_or_one x with h0 | h1
  · rw [shiftConj_even V₀ V₁ (hpar.trans h0), shiftConj_even V₀ V₁ h0]
    exact core V₀ h₀ hb₀
  · rw [shiftConj_odd V₀ V₁ (hpar.trans h1), shiftConj_odd V₀ V₁ h1]
    exact core V₁ h₁ hb₁

/-- **Lemma B.3 (Bernstein–Lagarias).** For `U = U_{V₀,V₁}` (solenoidal bijections) and `m ≥ j ≥ 1`:
if `y ≡ x + 2ᵐ·e (mod 2ᵐ⁺¹)` then `Uʲ(y) ≡ Uʲ(x) + 2ᵐ⁻ʲ·e (mod 2ᵐ⁻ʲ⁺¹)`. Indexed `m = j + d`
(`d = m − j ≥ 0`), the statement reads `y ≡ x + 2^{j+d}·e (mod 2^{j+d+1}) ⟹
Uʲ(y) ≡ Uʲ(x) + 2ᵈ·e (mod 2ᵈ⁺¹)` — and now holds for **all** `j ≥ 0` (the `j = 0` case is the
identity, exactly the hypothesis). **Proved** by induction on `j` (`Lemma B.2` and the paper's
"induction on `j`"): peel one iterate with the inductive hypothesis at `d+1`, then apply `lemma_B2`
to the iterated pair. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem lemma_B3 {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) (j d : ℕ) {x y e : ℤ_[2]}
    (hxy : (2 : ℤ_[2]) ^ (j + d + 1) ∣ (y - (x + 2 ^ (j + d) * e))) :
    (2 : ℤ_[2]) ^ (d + 1) ∣
      ((shiftConj V₀ V₁)^[j] y - ((shiftConj V₀ V₁)^[j] x + 2 ^ d * e)) := by
  induction j generalizing d with
  | zero => simpa using hxy
  | succ i ih =>
    have key : (2 : ℤ_[2]) ^ (d + 1 + 1) ∣
        ((shiftConj V₀ V₁)^[i] y - ((shiftConj V₀ V₁)^[i] x + 2 ^ (d + 1) * e)) := by
      apply ih (d + 1)
      have e1 : i + (d + 1) + 1 = i + 1 + d + 1 := by omega
      have e2 : i + (d + 1) = i + 1 + d := by omega
      rw [e1, e2]; exact hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact lemma_B2 h₀ hb₀ h₁ hb₁ d key

/-- **Lemma B.4 (Bernstein–Lagarias).** For `U = U_{V₀,V₁}` (solenoidal bijections) and `m ≥ 1`: if
`y ≡ x + 2ᵐ·e (mod 2ᵐ⁺¹)` then `Uᵐ(y) ≡ Uᵐ(x) + e (mod 2)`. **Proved** as `lemma_B3` with `j = m`
(i.e. `d = 0`): then `2ᵐ⁻ʲ = 2⁰ = 1` and the modulus is `2¹ = 2`. So the top bit of the perturbation
survives `m` iterations into the lowest bit. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem lemma_B4 {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) (m : ℕ) {x y e : ℤ_[2]}
    (hxy : (2 : ℤ_[2]) ^ (m + 1) ∣ (y - (x + 2 ^ m * e))) :
    (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[m] y - ((shiftConj V₀ V₁)^[m] x + e)) := by
  have h := lemma_B3 h₀ hb₀ h₁ hb₁ m 0 (by simpa using hxy)
  simpa using h

/-! ### Lemma B.5: prescribing the iterate-parities

Given a target bit sequence `b₀, b₁, …`, Lemma B.5 builds, step by step, the residues `x_m` such that
`y ≡ x_m (mod 2ᵐ)` is **equivalent** to "the first `m` iterate-parities of `y` under `U = U_{V₀,V₁}`
are `b₀,…,b_{m-1}`". The increment uses Lemma B.4: the `2ᵐ`-bit of the correction `b_m − Uᵐ(x_m)` is
exactly what fixes the `m`-th parity. (The lemma holds for an arbitrary `b : ℕ → ℤ₂`; the paper's
`b_i ∈ {0,1}` is the intended bit case but is not needed for the proof.) -/

/-- The Lemma B.5 sequence: `x₀ = 0` and `x_{m+1} = x_m + 2ᵐ·(b_m − Uᵐ(x_m))`, where
`U = U_{V₀,V₁} = shiftConj V₀ V₁`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def xSeq (V₀ V₁ : ℤ_[2] → ℤ_[2]) (b : ℕ → ℤ_[2]) : ℕ → ℤ_[2]
  | 0 => 0
  | m + 1 => xSeq V₀ V₁ b m + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] (xSeq V₀ V₁ b m))

/-- **Lemma B.5 (Bernstein–Lagarias).** For `U = U_{V₀,V₁}` (solenoidal bijections) and the sequence
`xSeq` defined by `x₀ = 0`, `x_{m+1} = x_m + 2ᵐ·(b_m − Uᵐ(x_m))`:
`y ≡ x_m (mod 2ᵐ)` **iff** `Uⁱ(y) ≡ b_i (mod 2)` for all `0 ≤ i < m`. **Proved** by induction on `m`,
following the paper. Step `m → m+1`: writing `e = b_m − Uᵐ(x_m)`, the congruence `y ≡ x_{m+1}
(mod 2ᵐ⁺¹)` is `y ≡ x_m + 2ᵐ·e (mod 2ᵐ⁺¹)`, so `Lemma B.4` gives `Uᵐ(y) ≡ Uᵐ(x_m) + e = b_m
(mod 2)` (the `i = m` parity), while `y ≡ x_m (mod 2ᵐ)` feeds the inductive hypothesis for `i < m`;
the converse runs the same equivalences backwards (`e` is recovered from `y = x_m + 2ᵐ·e`). -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem lemma_B5 {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) (b : ℕ → ℤ_[2]) (m : ℕ) (y : ℤ_[2]) :
    (2 : ℤ_[2]) ^ m ∣ (y - xSeq V₀ V₁ b m)
      ↔ ∀ i, i < m → (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[i] y - b i) := by
  induction m generalizing y with
  | zero => simp [xSeq]
  | succ m ih =>
    have hx : xSeq V₀ V₁ b (m + 1)
        = xSeq V₀ V₁ b m + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] (xSeq V₀ V₁ b m)) := rfl
    rw [hx]
    set xm := xSeq V₀ V₁ b m with hxm
    constructor
    · intro hdvd
      -- `Uᵐ(y) ≡ b_m (mod 2)` via Lemma B.4 with `e = b m − Uᵐ(x_m)`
      have hB4 := lemma_B4 h₀ hb₀ h₁ hb₁ m hdvd
      have hm_bit : (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[m] y - b m) := by
        have he : (shiftConj V₀ V₁)^[m] y - b m
            = (shiftConj V₀ V₁)^[m] y
              - ((shiftConj V₀ V₁)^[m] xm + (b m - (shiftConj V₀ V₁)^[m] xm)) := by ring
        rw [he]; exact hB4
      -- `y ≡ x_m (mod 2ᵐ)`, so the inductive hypothesis covers `i < m`
      have hym : (2 : ℤ_[2]) ^ m ∣ (y - xm) := by
        have h1 : (2 : ℤ_[2]) ^ m ∣ (y - (xm + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] xm))) :=
          (pow_dvd_pow 2 (Nat.le_succ m)).trans hdvd
        have he : y - xm = (y - (xm + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] xm)))
            + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] xm) := by ring
        rw [he]; exact dvd_add h1 (dvd_mul_right _ _)
      have hlt := (ih y).mp hym
      intro i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlti | heqi
      · exact hlt i hlti
      · subst heqi; exact hm_bit
    · intro hbits
      have hym : (2 : ℤ_[2]) ^ m ∣ (y - xm) :=
        (ih y).mpr (fun i hi => hbits i (Nat.lt_succ_of_lt hi))
      obtain ⟨e, he⟩ := hym
      have hB4 := lemma_B4 h₀ hb₀ h₁ hb₁ m
        (show (2 : ℤ_[2]) ^ (m + 1) ∣ (y - (xm + 2 ^ m * e)) by
          have h0 : y - (xm + 2 ^ m * e) = 0 := by linear_combination he
          rw [h0]; exact dvd_zero _)
      have hbitm : (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[m] y - b m) := hbits m (Nat.lt_succ_self m)
      have hediff : (2 : ℤ_[2]) ∣ (e - (b m - (shiftConj V₀ V₁)^[m] xm)) := by
        have hcomb : e - (b m - (shiftConj V₀ V₁)^[m] xm)
            = ((shiftConj V₀ V₁)^[m] y - b m)
              - ((shiftConj V₀ V₁)^[m] y - ((shiftConj V₀ V₁)^[m] xm + e)) := by ring
        rw [hcomb]; exact dvd_sub hbitm hB4
      have hgoal : y - (xm + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] xm))
          = 2 ^ m * (e - (b m - (shiftConj V₀ V₁)^[m] xm)) := by linear_combination he
      rw [hgoal, pow_succ]
      exact mul_dvd_mul_left _ hediff

/-! ### Theorem B.1: `U_{V₀,V₁}` is solenoidally conjugate to the shift

The map `Q(x) = ∑_{m≥0} (Uᵐ(x) mod 2)·2ᵐ` records the **itinerary** of `x` under `U = U_{V₀,V₁}`: its
`m`-th binary digit is the parity of `Uᵐ(x)`. Theorem B.1 says `Q` is a **solenoidal bijection**
conjugating `U` to the shift, `Q ∘ U = S ∘ Q`. We first develop the itinerary map `qIter f` for an
arbitrary self-map `f` (the structural lemmas — convergence, the bit-peel recursion, lowest digit,
semiconjugacy — need nothing about `f`; this is the same construction as `BL.qMap` for `f = T₂`), then
specialise to `f = shiftConj V₀ V₁` and use `lemma_B5` for the bijection and solenoidality. -/

/-- The **itinerary map** of a self-map `f` of `ℤ₂`: `qIter f x = ∑_{i≥0} (parity (fⁱ x))·2ⁱ`, the
`2`-adic integer whose `i`-th binary digit is the parity of `fⁱ x`. (For `f = T₂` this is `BL.qMap`;
for `f = shiftConj V₀ V₁` it is the `Q` of Theorem B.1, `qConj`.) -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def qIter (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : ℤ_[2] :=
  ∑' i : ℕ, (parity (f^[i] x) : ℤ_[2]) * 2 ^ i

/-- The defining series of `qIter f` **converges** (geometric domination by `‖2‖ⁱ`, `‖2‖ < 1`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_summable (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) :
    Summable (fun i : ℕ => (parity (f^[i] x) : ℤ_[2]) * 2 ^ i) := by
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hbound : ∀ i, ‖(parity (f^[i] x) : ℤ_[2]) * 2 ^ i‖ ≤ ‖(2 : ℤ_[2])‖ ^ i := by
    intro i
    have h1 : ‖(parity (f^[i] x) : ℤ_[2]) * 2 ^ i‖
        ≤ ‖((parity (f^[i] x) : ℕ) : ℤ_[2])‖ * ‖(2 : ℤ_[2]) ^ i‖ := norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) i) (PadicInt.norm_le_one _))
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt) hbound

/-- **Bit-peel recursion** `qIter f x = parity x + 2·qIter f (f x)` (split off `i = 0`, reindex). -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_peel (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) :
    qIter f x = (parity x : ℤ_[2]) + 2 * qIter f (f x) := by
  rw [qIter, (qIter_summable f x).tsum_eq_zero_add]
  congr 1
  · simp
  · rw [qIter, ← (qIter_summable f (f x)).tsum_mul_left]
    apply tsum_congr
    intro i
    rw [Function.iterate_succ_apply, pow_succ]
    ring

/-- **Lowest binary digit** `parity (qIter f x) = parity x` (the `2·(…)` term is even). -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_parity (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : parity (qIter f x) = parity x := by
  unfold parity
  rw [qIter_peel f x, map_add, map_mul, toZMod_two, zero_mul, add_zero, toZMod_natCast_parity]

/-- **`qIter f` conjugates `f` to the shift `S`**: `qIter f (f x) = S (qIter f x)`. (`2·S(qIter f x) =
qIter f x − parity x = 2·qIter f (f x)`, cancel `2`.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem qIter_semiconj (f : ℤ_[2] → ℤ_[2]) (x : ℤ_[2]) : qIter f (f x) = S (qIter f x) := by
  have h := two_mul_S (qIter f x)
  rw [qIter_parity f x] at h
  have h2 : (2 : ℤ_[2]) * S (qIter f x) = 2 * qIter f (f x) := by rw [h, qIter_peel f x]; ring
  exact (mul_left_cancel₀ (by norm_num) h2).symm

/-- Iterating the semiconjugacy: `Sⁱ (qIter f x) = qIter f (fⁱ x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_iterate_semiconj (f : ℤ_[2] → ℤ_[2]) (i : ℕ) (x : ℤ_[2]) :
    S^[i] (qIter f x) = qIter f (f^[i] x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, ← qIter_semiconj, Function.iterate_succ_apply']

/-- The `i`-th binary digit of `qIter f x` is the parity of `fⁱ x`:
`parity (Sⁱ (qIter f x)) = parity (fⁱ x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_digit (f : ℤ_[2] → ℤ_[2]) (i : ℕ) (x : ℤ_[2]) :
    parity (S^[i] (qIter f x)) = parity (f^[i] x) := by
  rw [qIter_iterate_semiconj, qIter_parity]

/-- `qIter f x` agrees with its degree-`< n` partial sum mod `2ⁿ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qIter_partialSum_dvd (f : ℤ_[2] → ℤ_[2]) (n : ℕ) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ^ n ∣ (qIter f x - ∑ i ∈ Finset.range n, (parity (f^[i] x) : ℤ_[2]) * 2 ^ i) := by
  have hsum := qIter_summable f x
  have hg : Summable (fun i => (parity (f^[i + n] x) : ℤ_[2]) * 2 ^ i) := by
    simpa [Function.iterate_add_apply] using qIter_summable f (f^[n] x)
  have htail : ∑' i, (parity (f^[i + n] x) : ℤ_[2]) * 2 ^ (i + n)
             = 2 ^ n * ∑' i, (parity (f^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [← hg.tsum_mul_left]
    apply tsum_congr; intro i; rw [pow_add]; ring
  have key : qIter f x = (∑ i ∈ Finset.range n, (parity (f^[i] x) : ℤ_[2]) * 2 ^ i)
      + 2 ^ n * ∑' i, (parity (f^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [qIter, ← htail, ← hsum.sum_add_tsum_nat_add n]
  rw [key, add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- **`Q` of Theorem B.1**: the itinerary map of `U = U_{V₀,V₁}`,
`qConj V₀ V₁ x = ∑_{m≥0} (parity (Uᵐ x))·2ᵐ`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def qConj (V₀ V₁ : ℤ_[2] → ℤ_[2]) : ℤ_[2] → ℤ_[2] := qIter (shiftConj V₀ V₁)

/-- `z − (parity z)` is even: `2 ∣ (z − parity z)` (it equals `2·S z`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem two_dvd_sub_parity (z : ℤ_[2]) : (2 : ℤ_[2]) ∣ (z - (parity z : ℤ_[2])) :=
  ⟨S z, (two_mul_S z).symm⟩

/-- The parity of a (cast) parity is itself: `parity ((parity w : ℤ₂)) = parity w` (a bit is `0/1`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_natCast_parity (w : ℤ_[2]) : parity ((parity w : ℤ_[2])) = parity w := by
  have hlt : parity w < 2 := by unfold parity; exact (PadicInt.toZMod w).val_lt
  rw [parity_natCast, CC.X_eq_mod, Nat.mod_eq_of_lt hlt]

/-- The `i`-th binary digit of `Q x` is the parity of `Uⁱ(x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qConj_digit (V₀ V₁ : ℤ_[2] → ℤ_[2]) (i : ℕ) (x : ℤ_[2]) :
    parity (S^[i] (qConj V₀ V₁ x)) = parity ((shiftConj V₀ V₁)^[i] x) :=
  qIter_digit (shiftConj V₀ V₁) i x

/-- **Theorem B.1, conjugacy half:** `Q` conjugates `U = U_{V₀,V₁}` to the shift,
`Q ∘ U = S ∘ Q` (`Function.Semiconj (qConj V₀ V₁) (shiftConj V₀ V₁) S`). Immediate from the
definition of `Q` (`qIter_semiconj`). -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem qConj_semiconj (V₀ V₁ : ℤ_[2] → ℤ_[2]) :
    Function.Semiconj (qConj V₀ V₁) (shiftConj V₀ V₁) S :=
  fun x => qIter_semiconj (shiftConj V₀ V₁) x

/-- **Theorem B.1, injectivity.** If `Q x = Q y` then all iterate-parities of `x` and `y` agree, so by
`lemma_B5` (applied with `b_m = parity(Uᵐ x)`) both `x` and `y` are `≡ x_m (mod 2ᵐ)` for every `m`,
forcing `x = y`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem qConj_injective {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) : Function.Injective (qConj V₀ V₁) := by
  intro x y hxy
  have hdig : ∀ i, parity ((shiftConj V₀ V₁)^[i] x) = parity ((shiftConj V₀ V₁)^[i] y) := fun i => by
    rw [← qConj_digit, ← qConj_digit, hxy]
  set b : ℕ → ℤ_[2] := fun m => (parity ((shiftConj V₀ V₁)^[m] x) : ℤ_[2]) with hbdef
  have hxsat : ∀ i, (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[i] x - b i) := fun i =>
    two_dvd_sub_parity ((shiftConj V₀ V₁)^[i] x)
  have hysat : ∀ i, (2 : ℤ_[2]) ∣ ((shiftConj V₀ V₁)^[i] y - b i) := fun i => by
    have hbi : b i = ((parity ((shiftConj V₀ V₁)^[i] y) : ℕ) : ℤ_[2]) := by
      show ((parity ((shiftConj V₀ V₁)^[i] x) : ℕ) : ℤ_[2]) = _
      rw [hdig i]
    rw [hbi]; exact two_dvd_sub_parity ((shiftConj V₀ V₁)^[i] y)
  have hall : ∀ m, (2 : ℤ_[2]) ^ m ∣ (x - y) := fun m => by
    have hx := (lemma_B5 h₀ hb₀ h₁ hb₁ b m x).mpr (fun i _ => hxsat i)
    have hy := (lemma_B5 h₀ hb₀ h₁ hb₁ b m y).mpr (fun i _ => hysat i)
    have hd := dvd_sub hx hy
    have he : (x - xSeq V₀ V₁ b m) - (y - xSeq V₀ V₁ b m) = x - y := by ring
    rwa [he] at hd
  exact PadicInt.ext_of_toZModPow.mp
    (fun n => (toZModPow_eq_iff_dvd_sub x y n).mpr (hall n))

/-- **Theorem B.1, surjectivity.** Given `z`, run `lemma_B5`'s sequence with `b_m = parity(Sᵐ z)`
(the binary digits of `z`); the partial points `x_m` form a `2`-adic Cauchy thread, so they have a
limit `y` with `y ≡ x_m (mod 2ᵐ)`. By `lemma_B5`, `parity(Uᵐ y) = parity(Sᵐ z)` for all `m`, whence
`Q y = ∑ parity(Sᵐ z)·2ᵐ = z` (`tsum_parity_S`). -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem qConj_surjective {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) : Function.Surjective (qConj V₀ V₁) := by
  intro z
  set b : ℕ → ℤ_[2] := fun m => (parity (S^[m] z) : ℤ_[2]) with hbdef
  have hstep : ∀ m, (2 : ℤ_[2]) ^ m ∣ (xSeq V₀ V₁ b (m + 1) - xSeq V₀ V₁ b m) := fun m => by
    have hx : xSeq V₀ V₁ b (m + 1)
        = xSeq V₀ V₁ b m + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] (xSeq V₀ V₁ b m)) := rfl
    rw [hx]
    have he : xSeq V₀ V₁ b m + 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] (xSeq V₀ V₁ b m))
        - xSeq V₀ V₁ b m = 2 ^ m * (b m - (shiftConj V₀ V₁)^[m] (xSeq V₀ V₁ b m)) := by ring
    rw [he]; exact dvd_mul_right _ _
  have hc : ∀ n, (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))
      (PadicInt.toZModPow (n + 1) (xSeq V₀ V₁ b (n + 1)))
        = PadicInt.toZModPow n (xSeq V₀ V₁ b n) := by
    intro n
    rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)]
    exact (toZModPow_eq_iff_dvd_sub _ _ n).mpr (hstep n)
  obtain ⟨y, hy⟩ := exists_toZModPow_eq_thread
    (fun n => PadicInt.toZModPow n (xSeq V₀ V₁ b n)) hc
  have hyx : ∀ m, (2 : ℤ_[2]) ^ m ∣ (y - xSeq V₀ V₁ b m) := fun m =>
    (toZModPow_eq_iff_dvd_sub y (xSeq V₀ V₁ b m) m).mp (hy m)
  have hmatch : ∀ m, parity ((shiftConj V₀ V₁)^[m] y) = parity (S^[m] z) := fun m => by
    have hb5 := (lemma_B5 h₀ hb₀ h₁ hb₁ b (m + 1) y).mp (hyx (m + 1)) m (Nat.lt_succ_self m)
    have hp := parity_eq_of_two_dvd_sub hb5
    rw [hp, show b m = ((parity (S^[m] z) : ℕ) : ℤ_[2]) from rfl, parity_natCast_parity]
  refine ⟨y, ?_⟩
  show qIter (shiftConj V₀ V₁) y = z
  rw [qIter, ← tsum_parity_S z]
  exact tsum_congr (fun m => by rw [hmatch m])

/-- **Theorem B.1, solenoidality.** If `x ≡ y (mod 2ⁿ)`, then (with `b_m = parity(Uᵐ x)`)
`lemma_B5` gives `x ≡ x_n (mod 2ⁿ)`, hence `y ≡ x_n (mod 2ⁿ)`, hence `parity(Uⁱ y) = parity(Uⁱ x)`
for `i < n`. So the first `n` binary digits of `Q x` and `Q y` agree, i.e. `Q x ≡ Q y (mod 2ⁿ)`. (The
naive "`Uⁱ` solenoidal" argument fails — `U` itself loses a bit — which is why `lemma_B5` is used.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem qConj_solenoidal {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) : Solenoidal (qConj V₀ V₁) := by
  intro n x y hxy
  set b : ℕ → ℤ_[2] := fun m => (parity ((shiftConj V₀ V₁)^[m] x) : ℤ_[2]) with hbdef
  have hxn : (2 : ℤ_[2]) ^ n ∣ (x - xSeq V₀ V₁ b n) :=
    (lemma_B5 h₀ hb₀ h₁ hb₁ b n x).mpr (fun i _ => two_dvd_sub_parity ((shiftConj V₀ V₁)^[i] x))
  have hyn : (2 : ℤ_[2]) ^ n ∣ (y - xSeq V₀ V₁ b n) := by
    have h2 : (2 : ℤ_[2]) ^ n ∣ (y - x) := by rw [← neg_sub]; exact dvd_neg.mpr hxy
    have he : y - xSeq V₀ V₁ b n = (y - x) + (x - xSeq V₀ V₁ b n) := by ring
    rw [he]; exact dvd_add h2 hxn
  have hdig : ∀ i, i < n →
      parity ((shiftConj V₀ V₁)^[i] x) = parity ((shiftConj V₀ V₁)^[i] y) := fun i hi => by
    have hb5 := (lemma_B5 h₀ hb₀ h₁ hb₁ b n y).mp hyn i hi
    have hp := parity_eq_of_two_dvd_sub hb5
    rw [show b i = ((parity ((shiftConj V₀ V₁)^[i] x) : ℕ) : ℤ_[2]) from rfl,
      parity_natCast_parity] at hp
    exact hp.symm
  have hpx := qIter_partialSum_dvd (shiftConj V₀ V₁) n x
  have hpy := qIter_partialSum_dvd (shiftConj V₀ V₁) n y
  have hsumeq : (∑ i ∈ Finset.range n, (parity ((shiftConj V₀ V₁)^[i] x) : ℤ_[2]) * 2 ^ i)
      = ∑ i ∈ Finset.range n, (parity ((shiftConj V₀ V₁)^[i] y) : ℤ_[2]) * 2 ^ i :=
    Finset.sum_congr rfl (fun i hi => by rw [hdig i (Finset.mem_range.mp hi)])
  have he : qConj V₀ V₁ x - qConj V₀ V₁ y
      = (qConj V₀ V₁ x - ∑ i ∈ Finset.range n, (parity ((shiftConj V₀ V₁)^[i] x) : ℤ_[2]) * 2 ^ i)
        - (qConj V₀ V₁ y
            - ∑ i ∈ Finset.range n, (parity ((shiftConj V₀ V₁)^[i] y) : ℤ_[2]) * 2 ^ i) := by
    rw [hsumeq]; ring
  rw [he]
  exact dvd_sub hpx hpy

/-- **Theorem B.1 (Bernstein–Lagarias).** For solenoidal bijections `V₀, V₁`, the itinerary map
`Q = qConj V₀ V₁` of `U = U_{V₀,V₁}` is a **solenoidal bijection** conjugating `U` to the shift:
`Q ∘ U = S ∘ Q` (so `U = Q⁻¹ ∘ S ∘ Q`). Thus **any** `U_{V₀,V₁}` is solenoidally conjugate to `S`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem theorem_B1 {V₀ V₁ : ℤ_[2] → ℤ_[2]} (h₀ : Solenoidal V₀) (hb₀ : Function.Bijective V₀)
    (h₁ : Solenoidal V₁) (hb₁ : Function.Bijective V₁) :
    Solenoidal (qConj V₀ V₁) ∧ Function.Bijective (qConj V₀ V₁)
      ∧ Function.Semiconj (qConj V₀ V₁) (shiftConj V₀ V₁) S :=
  ⟨qConj_solenoidal h₀ hb₀ h₁ hb₁,
    ⟨qConj_injective h₀ hb₀ h₁ hb₁, qConj_surjective h₀ hb₀ h₁ hb₁⟩,
    qConj_semiconj V₀ V₁⟩

/-- **Theorem B.2 (Bernstein–Lagarias), converse to B.1.** Let `Q` be **any** solenoidal bijection and
`U = Q⁻¹ ∘ S ∘ Q` (the conjugate of the shift by `Q`). Then `U = U_{V₀,V₁}` for some solenoidal
bijections `V₀, V₁`. **Proved.** The branches are forced: `V_b(w) := U(2w + b)` makes
`U = shiftConj V₀ V₁` immediate (since `x = 2·S x + parity x`). Each `V_b = Q⁻¹ ∘ S ∘ Q ∘ (·↦2·+b)` is
an **isometry** — `(·↦2w+b)` halves the norm, `Q` preserves it, `S` doubles it on the equal-parity
pair `Q(2w+b), Q(2w'+b)` (equal parity because `Q` is solenoidal), and `Q⁻¹` preserves it — hence a
solenoidal bijection by `corollary_A3`. (This isometry argument replaces the paper's explicit `W₀, W₁`
decomposition and its `Q(0) even / odd` case split, which it makes unnecessary.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem theorem_B2 {Q : ℤ_[2] → ℤ_[2]} (hQsol : Solenoidal Q) (hQbij : Function.Bijective Q) :
    ∃ V₀ V₁ : ℤ_[2] → ℤ_[2],
      (Solenoidal V₀ ∧ Function.Bijective V₀) ∧ (Solenoidal V₁ ∧ Function.Bijective V₁)
        ∧ Function.invFun Q ∘ S ∘ Q = shiftConj V₀ V₁ := by
  have hQiso : ∀ a a', ‖Q a - Q a'‖ = ‖a - a'‖ :=
    ((corollary_A3 Q).out 1 3).mp (⟨hQsol, hQbij⟩ : Solenoidal Q ∧ Function.Bijective Q)
  have hkey := ((corollary_A3 Q).out 1 2).mp (⟨hQsol, hQbij⟩ : Solenoidal Q ∧ Function.Bijective Q)
  have hQinvBij : Function.Bijective (Function.invFun Q) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨Q, Function.rightInverse_invFun hQbij.surjective, Function.leftInverse_invFun hQbij.injective⟩
  have hQinvIso : ∀ a a', ‖Function.invFun Q a - Function.invFun Q a'‖ = ‖a - a'‖ :=
    ((corollary_A3 (Function.invFun Q)).out 1 3).mp
      (⟨hkey.2.2, hQinvBij⟩ : Solenoidal (Function.invFun Q) ∧ Function.Bijective (Function.invFun Q))
  have hVb : ∀ b : ℤ_[2],
      Solenoidal (fun w => Function.invFun Q (S (Q (2 * w + b))))
        ∧ Function.Bijective (fun w => Function.invFun Q (S (Q (2 * w + b)))) := by
    intro b
    have hiso : ∀ w w', ‖Function.invFun Q (S (Q (2 * w + b)))
        - Function.invFun Q (S (Q (2 * w' + b)))‖ = ‖w - w'‖ := by
      intro w w'
      rw [hQinvIso]
      have hpar : parity (Q (2 * w + b)) = parity (Q (2 * w' + b)) := by
        have h := hQsol 1 (2 * w + b) (2 * w' + b) ⟨w - w', by ring⟩
        rw [pow_one] at h
        exact parity_eq_of_two_dvd_sub h
      have hSrel : (2 : ℤ_[2]) * (S (Q (2 * w + b)) - S (Q (2 * w' + b)))
          = Q (2 * w + b) - Q (2 * w' + b) := by
        rw [mul_sub, two_mul_S, two_mul_S, hpar]; ring
      have e1 : ‖(2 : ℤ_[2])‖ * ‖S (Q (2 * w + b)) - S (Q (2 * w' + b))‖
          = ‖(2 : ℤ_[2])‖ * ‖w - w'‖ := by
        rw [← norm_mul, hSrel, hQiso, ← norm_mul]
        congr 1; ring
      exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (by norm_num)) e1
    exact ((corollary_A3 _).out 3 1).mp hiso
  refine ⟨fun w => Function.invFun Q (S (Q (2 * w + 0))),
    fun w => Function.invFun Q (S (Q (2 * w + 1))), hVb 0, hVb 1, ?_⟩
  funext x
  show Function.invFun Q (S (Q x)) = shiftConj _ _ x
  rcases parity_eq_zero_or_one x with h0 | h1
  · rw [shiftConj_even _ _ h0]
    have hx : (2 : ℤ_[2]) * S x + 0 = x := by
      have h := parity_add_two_mul_S x; rw [h0] at h; push_cast at h; linear_combination h
    show Function.invFun Q (S (Q x)) = Function.invFun Q (S (Q (2 * S x + 0)))
    rw [hx]
  · rw [shiftConj_odd _ _ h1]
    have hx : (2 : ℤ_[2]) * S x + 1 = x := by
      have h := parity_add_two_mul_S x; rw [h1] at h; push_cast at h; linear_combination h
    show Function.invFun Q (S (Q x)) = Function.invFun Q (S (Q (2 * S x + 1)))
    rw [hx]

/-! ### The `ax+b` function

Generalising `BL.numer`/`BL.T₂` (the `a=3, b=1` case): the **`ax+b` numerator** is
`x·a^{parity x} + b·(parity x)` — equal to `x` on even `x` (halve to `x/2`) and `ax+b` on odd `x`
(halve to `(ax+b)/2`). For the odd branch to be halvable in `ℤ₂` one needs `2 ∣ a+b` (so that `ax+b`
is even when `x` is odd); then `axbMap = axbNumer / 2`. -/

/-- The **`ax+b` numerator** `x·a^{parity x} + b·(parity x)`: it is `x` for even `x` and `a·x + b` for
odd `x`. (The `a=3, b=1` case is `BL.numer`.) -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def axbNumer (a b x : ℤ_[2]) : ℤ_[2] := x * a ^ parity x + b * (parity x : ℤ_[2])

/-- The `ax+b` numerator is **even** in `ℤ₂` when `2 ∣ a+b`: for even `x` it is `x` (even); for odd
`x` it is `ax+b ≡ a+b ≡ 0 (mod 2)`. So `axbMap` is well defined. -/
@[category API, AMS 11 37, ref "BL96"]
theorem even_axbNumer {a b : ℤ_[2]} (hab : (2 : ℤ_[2]) ∣ (a + b)) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ∣ axbNumer a b x := by
  rcases parity_eq_zero_or_one x with h0 | h1
  · have hx : axbNumer a b x = x := by unfold axbNumer; rw [h0]; simp
    rw [hx, two_dvd_iff_toZMod_eq_zero]
    have h := toZMod_eq_parity x; rw [h0] at h; simpa using h.symm
  · have hx : axbNumer a b x = x * a + b := by unfold axbNumer; rw [h1]; simp
    have hxz : PadicInt.toZMod x = 1 := by
      have h := toZMod_eq_parity x; rw [h1] at h; simpa using h.symm
    rw [hx, two_dvd_iff_toZMod_eq_zero, map_add, map_mul, hxz, one_mul]
    have hz : PadicInt.toZMod (a + b) = 0 := (two_dvd_iff_toZMod_eq_zero _).mp hab
    rwa [map_add] at hz

/-- The **`ax+b` function** on `ℤ₂` (the Terras-style accelerated map, `2 ∣ a+b`): the unique half of
the even numerator `axbNumer a b x`. So `axbMap a b x = x/2` for even `x` and `(ax+b)/2` for odd `x`.
The `a=3, b=1` case is the `3x+1` map `BL.T₂` (`axbMap_three_one`). -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def axbMap {a b : ℤ_[2]} (hab : (2 : ℤ_[2]) ∣ (a + b)) (x : ℤ_[2]) : ℤ_[2] :=
  half (even_axbNumer hab x)

/-- Defining identity of the `ax+b` function: `2 · axbMap x = x·a^{parity x} + b·(parity x)`. On even
`x` it reads `2·axbMap x = x`, on odd `x` it reads `2·axbMap x = a·x + b`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem two_mul_axbMap {a b : ℤ_[2]} (hab : (2 : ℤ_[2]) ∣ (a + b)) (x : ℤ_[2]) :
    2 * axbMap hab x = axbNumer a b x := two_mul_half (even_axbNumer hab x)

/-! ### The example: `U_{id, a·+(a+b)/2}` is the `ax+b` function -/

/-- **The example (BL96 §8).** Taking `V₀ = id` and `V₁(y) = a·y + (a+b)/2` (with `(a+b)/2 = half hab`,
since `2 ∣ a+b`), the construction `U_{V₀,V₁}` is exactly the **`ax+b` function**: `shiftConj id
(fun y => a·y + half hab) = axbMap hab`. *Proof:* compare `2·U(x)` with `2·axbMap x = axbNumer a b x`
case-wise. Even `x`: `2·S x = x`. Odd `x`: `2·(a·S x + half hab) = a·(2 S x) + (a+b) = a(x-1)+(a+b)
= ax+b`, using `2·S x = x-1` and `2·half hab = a+b`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem shiftConj_id_axbMap {a b : ℤ_[2]} (hab : (2 : ℤ_[2]) ∣ (a + b)) :
    shiftConj id (fun y => a * y + half hab) = axbMap hab := by
  funext x
  refine mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) ?_
  rw [two_mul_axbMap]
  rcases parity_eq_zero_or_one x with h0 | h1
  · rw [shiftConj_even _ _ h0]
    simp only [id_eq]
    unfold axbNumer
    rw [h0]
    have hs : 2 * S x = x := by rw [two_mul_S, h0]; simp
    push_cast; linear_combination hs
  · rw [shiftConj_odd _ _ h1]
    unfold axbNumer
    rw [h1]
    have hs : 2 * S x = x - 1 := by rw [two_mul_S, h1]; push_cast; ring
    push_cast; linear_combination a * hs + two_mul_half hab

/-! ### Specialisation to the `3x+1` map `T₂` (`a = 3, b = 1`) -/

/-- The `a = 3, b = 1` case of the `ax+b` function is the **`3x+1` map** `BL.T₂`: its numerator
`x·3^{parity x} + 1·(parity x)` is exactly `BL.numer x`, so the two halves agree. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem axbMap_three_one (hab : (2 : ℤ_[2]) ∣ ((3 : ℤ_[2]) + 1)) :
    axbMap hab = T₂ := by
  funext x
  refine mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) ?_
  rw [two_mul_axbMap, two_mul_T₂]
  unfold axbNumer numer
  simp

/-- **The `3x+1` map as a shift-conjugate (BL96 §8).** With `V₀ = id` and `V₁(y) = 3y + 2`
(`= a·y + (a+b)/2` at `a=3, b=1`, since `(3+1)/2 = 2`), the construction `U_{V₀,V₁}` is the `3x+1` map
`T₂`: `shiftConj id (fun y => 3·y + 2) = T₂`. The canonical instance of the Appendix B example. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_conjugate"]
theorem shiftConj_eq_T₂ : shiftConj id (fun y => 3 * y + 2) = T₂ := by
  funext x
  refine mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) ?_
  rw [two_mul_T₂]
  unfold numer
  rcases parity_eq_zero_or_one x with h0 | h1
  · rw [shiftConj_even _ _ h0]
    simp only [id_eq]
    rw [h0]
    have hs : 2 * S x = x := by rw [two_mul_S, h0]; simp
    push_cast; linear_combination hs
  · rw [shiftConj_odd _ _ h1]
    rw [h1]
    have hs : 2 * S x = x - 1 := by rw [two_mul_S, h1]; push_cast; ring
    push_cast; linear_combination 3 * hs

end BL
