/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.Approximants
import BL.ForwardFormula
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `Φ` on an arbitrary repeated block (Route (i), Phase 2–3, general block)

**The general repeated-block case.** Phase 2 (`B3.StammeringApproximants`,
[[b3-automatic-cc-corpus-root]]) set up the *single-`1`-bit-per-period* pattern
`dᵢ = s·i` — the `c = 1` case. The stammering block `Vₘ` produced by a finite automaton is in general a
*multi-bit* block: `c ≥ 1` ones at offsets `0 ≤ e₀ < e₁ < ⋯ < e_{c−1} < p` inside a period of length
`p`. This file computes `Φ` on the periodic completion of such a block, the genuine geometric-series
form the plan's Step 2.3 calls for.

Write the `1`-bit positions of the periodic completion as `dᵢ = (i / c)·p + e (i % c)` (`blockPos`): the
`j`-th repetition of the block contributes its `c` ones at `j·p + eᵣ`. This `d` is strictly increasing
(`blockPos_strictMono`), so the explicit Bernstein–Lagarias formula `(1.6)` (`BL.Φ_eq_neg_tsum`)
applies. The key combinatorial identity is `blockPos (i + c) = blockPos i + p`
(`blockPos_add_period`): advancing the bit-index by one whole block shifts the position by exactly one
period. Hence, with `R := 3⁻¹^c · 2^p` and the **block polynomial**
`blockPoly = ∑_{r < c} 3⁻ʳ · 2^{eᵣ}`, the series telescopes (`R · Fᵢ = F_{i+c}`) and

> `Φ(blockVal) = −(3⁻¹ · blockPoly · (1 − 3⁻¹^c·2^p)⁻¹)`   (`Φ_blockValue`).

For `c = 1`, `e ≡ 0` this is the single-bit value (`blockPoly = 1`, `R = 3⁻¹·2^p`). Clearing
denominators gives the **integer linear relation** (`Φ_blockValue_linear_relation`)

> `(3^c − 2^p) · Φ(blockVal) = − ∑_{r < c} 3^{c−1−r} · 2^{eᵣ}`,

a `2`-adic integer with `3^c − 2^p ∈ ℤ` odd (a unit), whence `Φ(blockVal)` is a **rational**
`2`-adic number (`Φ_blockValue_mem_ratInt`) — the general rational approximant `Φ(αₘ)` of Phase 3,
a ratio of integer combinations of powers of
`2` and `3` (Adamczewski–Bugeaud's Lemma 1 form `Pₙ(β)/(βʳ(βˢ − 1))`).

All ratios have `2`-adic norm `2^{−p} < 1`, so the geometric series converge in the complete ring `ℤ₂`
and `1 − R`, `3^c − 2^p` are units. No new `axiom` is introduced; everything rests on the cited
`(1.6)` already used in Phase 2.

## Contents
* `blockPos`, `blockVal`, `blockPoly` — the bit positions `dᵢ = (i/c)p + e(i%c)`, the periodic
  completion `∑ᵢ 2^{dᵢ}`, and the block polynomial `∑_{r<c} 3⁻ʳ 2^{eᵣ}`.
* `blockPos_eq_of_lt`, `blockPos_add_period`, `blockPos_strictMono` — the combinatorics of `blockPos`.
* `Φ_blockValue` — (proved) `Φ` of a general repeated block as a geometric series.
* `Φ_blockValue_linear_relation` — (proved) the integer linear relation `(3^c−2^p)·Φ = −∑ 3^{c−1−r}2^{eᵣ}`.
* `Φ_blockValue_mem_ratInt` — (proved) the general approximant `Φ(αₘ)` is a rational `2`-adic number.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the explicit formula `(1.6)`).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4, Lemma 1: the periodic-completion approximants of a stammering
  expansion).
-/

namespace B3

open BL AB Function Filter

/-! ### Bit positions of a periodically repeated block -/

/-- The position of the `i`-th `1`-bit of the periodic completion of a block of `c` ones at offsets
`e 0 < e 1 < ⋯ < e (c−1)` inside a period of length `p`: `dᵢ = (i / c)·p + e (i % c)`. The `j`-th
repetition of the block (`j = i / c`) places its `r`-th one (`r = i % c`) at `j·p + eᵣ`. For `c = 1`,
`e ≡ 0` this is `i·p`, the single-`1`-bit-per-period pattern. -/
@[category API, AMS 11 37, ref "BL96"]
def blockPos (c p : ℕ) (e : ℕ → ℕ) (i : ℕ) : ℕ := (i / c) * p + e (i % c)

/-- For `i` inside the first block (`i < c`), the position is just the offset: `blockPos i = e i`
(`i / c = 0`, `i % c = i`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_eq_of_lt {c p : ℕ} {e : ℕ → ℕ} {i : ℕ} (hi : i < c) :
    blockPos c p e i = e i := by
  simp only [blockPos, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.zero_mul, Nat.zero_add]

/-- **The period identity.** Advancing the bit-index by one whole block (`i ↦ i + c`) shifts the
position by exactly one period: `blockPos (i + c) = blockPos i + p`. This is what makes the series for
`Φ` telescope geometrically. -/
@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_add_period {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (i : ℕ) :
    blockPos c p e (i + c) = blockPos c p e i + p := by
  simp only [blockPos, Nat.add_div_right i hc, Nat.add_mod_right]
  ring

/-- **`blockPos` is strictly increasing.** Within a block the offsets increase (`e` strictly monotone
on `[0, c)`); across a block boundary the period term `p` dominates (`eᵣ < p`). Hence the `1`-bit
positions form a strictly increasing sequence, as the formula `(1.6)` requires. -/
@[category API, AMS 11 37, ref "BL96"]
theorem blockPos_strictMono {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    StrictMono (blockPos c p e) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hsplit : c * (i / c) + i % c = i := Nat.div_add_mod i c
  have hmod_lt : i % c < c := Nat.mod_lt i hc
  rcases Nat.lt_or_ge (i % c + 1) c with hlt | hge
  · -- same block: `(i+1)/c = i/c`, `(i+1)%c = i%c + 1`
    have hrep : i + 1 = c * (i / c) + (i % c + 1) := by omega
    have hd : (i + 1) / c = i / c := by
      rw [hrep, Nat.mul_add_div hc, Nat.div_eq_of_lt hlt, add_zero]
    have hm : (i + 1) % c = i % c + 1 := by
      rw [hrep, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hlt_e : e (i % c) < e (i % c + 1) := he_mono (i % c) (i % c + 1) (Nat.lt_succ_self _) hlt
    simp only [blockPos, hd, hm]
    omega
  · -- block boundary: `i % c + 1 = c`, `(i+1)/c = i/c + 1`, `(i+1)%c = 0`
    have hbc : i % c + 1 = c := by omega
    have hrep : i + 1 = c * (i / c) + c := by omega
    have hd : (i + 1) / c = i / c + 1 := by
      rw [hrep, Nat.mul_add_div hc, Nat.div_self hc]
    have hm : (i + 1) % c = 0 := by
      rw [hrep, Nat.mul_add_mod, Nat.mod_self]
    have hlt_e : e (i % c) < p := he_lt _ hmod_lt
    have hmul : (i / c + 1) * p = (i / c) * p + p := by ring
    simp only [blockPos, hd, hm]
    omega

/-! ### The block polynomial and the periodic completion -/

/-- The **block polynomial** `∑_{r < c} 3⁻ʳ · 2^{eᵣ}` (`3⁻¹ = Ring.inverse 3`): the contribution of a
single block to `Φ` under the explicit formula `(1.6)`, before the geometric collapse over repetitions.
For `c = 1`, `e ≡ 0` it is `1`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def blockPoly (c : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  ∑ r ∈ Finset.range c, Ring.inverse 3 ^ r * 2 ^ e r

/-- The **periodic completion** `αₘ = ∑ᵢ 2^{blockPos i}` of a block: the `2`-adic integer whose binary
expansion is the block `Vₘ` repeated forever. For `c = 1`, `e ≡ 0` it is `∑ᵢ 2^{p·i} = (1 − 2^p)⁻¹`.
The **empty block** `c = 0` (no `1`-bits per period) is sent to `0` (`blockVal_zero`): its periodic
completion is all-zero. This is the degenerate case the Adamczewski–Bugeaud construction hits when a
stammering window of `v` happens to be all zeros (so the block value `B = 0`, `c = popcount B = 0`). -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def blockVal (c p : ℕ) (e : ℕ → ℕ) : ℤ_[2] :=
  if 0 < c then ∑' i, (2 : ℤ_[2]) ^ blockPos c p e i else 0

/-- For a nonempty block (`0 < c`) the periodic completion is the genuine series `∑ᵢ 2^{blockPos i}`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem blockVal_of_pos {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) :
    blockVal c p e = ∑' i, (2 : ℤ_[2]) ^ blockPos c p e i := by
  unfold blockVal; exact if_pos hc

/-- The **empty block** `c = 0` has periodic completion `0`: there are no `1`-bits to place. -/
@[category API, AMS 11 37, ref "BL96"]
theorem blockVal_zero {p : ℕ} {e : ℕ → ℕ} : blockVal 0 p e = 0 := by
  unfold blockVal; exact if_neg (lt_irrefl 0)

/-! ### `Φ` on a general repeated block -/

/-- **The geometric-series form of `Φ` on an arbitrary block (proved).** With `R = 3⁻¹^c · 2^p`,
`Φ(blockVal) = −(3⁻¹ · blockPoly · (1 − R)⁻¹)`. *Proof.* By the explicit formula `(1.6)`
(`Φ_eq_neg_tsum`, valid since `blockPos` is strictly increasing), `Φ(blockVal) = −∑ᵢ Fᵢ` with
`Fᵢ = 3⁻¹^{i+1} 2^{blockPos i}`. The period identity gives `R·Fᵢ = F_{i+c}` (`blockPos_add_period`),
so `∑ᵢ Fᵢ` telescopes: `(1 − R)·∑ᵢ Fᵢ = ∑_{i<c} Fᵢ = 3⁻¹ · blockPoly` (the first block), and `1 − R`
is a unit (`‖R‖ = 2^{−p} < 1`). This is the multi-bit version of the single-`1`-bit-per-period
(`c = 1`, `e ≡ 0`) case. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    Φ (blockVal c p e) =
      -(Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - Ring.inverse 3 ^ c * 2 ^ p)) := by
  have hmono := blockPos_strictMono hc he_lt he_mono
  rw [blockVal_of_pos hc, Φ_eq_neg_tsum (blockPos c p e) hmono]
  congr 1
  set R : ℤ_[2] := Ring.inverse 3 ^ c * 2 ^ p with hR_def
  set F : ℕ → ℤ_[2] := fun i => Ring.inverse 3 ^ (i + 1) * 2 ^ blockPos c p e i with hF_def
  have hinv3norm : ‖Ring.inverse (3 : ℤ_[2])‖ = 1 :=
    PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one 3 (by rw [mul_comm]; exact three_mul_inverse))
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hRnorm : ‖R‖ < 1 := by
    rw [hR_def, norm_mul, norm_pow, norm_pow, hinv3norm, one_pow, one_mul]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hunit : IsUnit (1 - R) := isUnit_one_sub_of_norm_lt_one hRnorm
  have hsummable : Summable F := by
    apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt1)
    intro i
    have hge : i ≤ blockPos c p e i := hmono.le_apply
    simp only [hF_def, norm_mul, norm_pow, hinv3norm, one_pow, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hge
  have hshift : ∀ i, R * F i = F (i + c) := by
    intro i
    simp only [hF_def, hR_def, blockPos_add_period hc i]
    rw [pow_add (2 : ℤ_[2]) (blockPos c p e i) p,
        show i + c + 1 = (i + 1) + c from by ring, pow_add (Ring.inverse (3 : ℤ_[2])) (i + 1) c]
    ring
  have hfirst : ∑ i ∈ Finset.range c, F i = Ring.inverse 3 * blockPoly c e := by
    rw [blockPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hF_def, blockPos_eq_of_lt hi]
    rw [pow_succ']
    ring
  have hmul : ∑' i, R * F i = R * ∑' i, F i := Summable.tsum_mul_left R hsummable
  have hregroup : (∑ i ∈ Finset.range c, F i) + ∑' i, F (i + c) = ∑' i, F i :=
    hsummable.sum_add_tsum_nat_add c
  have hshift_sum : ∑' i, F (i + c) = R * ∑' i, F i := by
    rw [← hmul]; exact (tsum_congr hshift).symm
  have key : (1 - R) * ∑' i, F i = ∑ i ∈ Finset.range c, F i := by
    rw [hshift_sum] at hregroup
    linear_combination -hregroup
  have hunit_inv : Ring.inverse (1 - R) * (1 - R) = 1 := Ring.inverse_mul_cancel _ hunit
  calc ∑' i, F i
      = Ring.inverse (1 - R) * ((1 - R) * ∑' i, F i) := by rw [← mul_assoc, hunit_inv, one_mul]
    _ = Ring.inverse (1 - R) * (Ring.inverse 3 * blockPoly c e) := by rw [key, hfirst]
    _ = Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - R) := by ring

/-! ### The integer linear relation and rationality -/

/-- **The integer linear relation (proved).** Clearing denominators in `Φ_blockValue`:
`(3^c − 2^p) · Φ(blockVal) = − ∑_{r < c} 3^{c−1−r} · 2^{eᵣ}`. *Proof.* `3^c − 2^p = 3^c·(1 − R)`
(since `3^c·R = (3·3⁻¹)^c·2^p = 2^p`), so the unit `(1 − R)⁻¹` cancels, leaving `3^c·3⁻¹·blockPoly`;
and `3^{c−1}·3⁻ʳ = 3^{c−1−r}` for `r < c` turns the block polynomial into an integer sum. The right
side is `(N : ℤ₂)` for `N = ∑_{r<c} 3^{c−1−r} 2^{eᵣ} ∈ ℕ`. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue_linear_relation {c p : ℕ} {e : ℕ → ℕ} (hc : 0 < c) (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    ((3 : ℤ_[2]) ^ c - 2 ^ p) * Φ (blockVal c p e)
      = - ∑ r ∈ Finset.range c, (3 : ℤ_[2]) ^ (c - 1 - r) * 2 ^ e r := by
  rw [Φ_blockValue hc hp he_lt he_mono]
  set R : ℤ_[2] := Ring.inverse 3 ^ c * 2 ^ p with hR_def
  have h3κ : (3 : ℤ_[2]) ^ c * Ring.inverse 3 ^ c = 1 := by
    rw [← mul_pow, three_mul_inverse, one_pow]
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hinv3norm : ‖Ring.inverse (3 : ℤ_[2])‖ = 1 :=
    PadicInt.isUnit_iff.mp (IsUnit.of_mul_eq_one 3 (by rw [mul_comm]; exact three_mul_inverse))
  have hRnorm : ‖R‖ < 1 := by
    rw [hR_def, norm_mul, norm_pow, norm_pow, hinv3norm, one_pow, one_mul]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt h2lt1) hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hunit : IsUnit (1 - R) := isUnit_one_sub_of_norm_lt_one hRnorm
  have hfact : (3 : ℤ_[2]) ^ c - 2 ^ p = 3 ^ c * (1 - R) := by
    rw [hR_def, mul_sub, mul_one, ← mul_assoc, h3κ, one_mul]
  have hc1 : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc
  have h3cκ : (3 : ℤ_[2]) ^ c * Ring.inverse 3 = 3 ^ (c - 1) := by
    conv_lhs => rw [← hc1, pow_succ]
    rw [mul_assoc, three_mul_inverse, mul_one]
  rw [hfact, mul_neg]
  congr 1
  rw [show (3 : ℤ_[2]) ^ c * (1 - R) *
        (Ring.inverse 3 * blockPoly c e * Ring.inverse (1 - R))
      = (3 ^ c * Ring.inverse 3) * blockPoly c e * ((1 - R) * Ring.inverse (1 - R)) from by ring,
      Ring.mul_inverse_cancel _ hunit, mul_one, h3cκ, blockPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrle : r ≤ c - 1 := by omega
  have hsplit : (3 : ℤ_[2]) ^ (c - 1) = 3 ^ (c - 1 - r) * 3 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrle]
  rw [← mul_assoc]
  congr 1
  rw [hsplit, mul_assoc, ← mul_pow, three_mul_inverse, one_pow, mul_one]

/-- **The general approximant is a rational `2`-adic number (proved).** `Φ(blockVal) ∈ RatInt = ℚ ∩ ℤ₂`:
explicitly `Φ(blockVal) = −N / (3^c − 2^p)` with `N = ∑_{r<c} 3^{c−1−r} 2^{eᵣ} ∈ ℕ` and denominator
`3^c − 2^p ∈ ℤ` odd (hence nonzero, a unit in `ℤ₂`). This is the general rational approximant `Φ(αₘ)` of
Phase 3, establishing that a stammering block,
periodically completed, evaluates under `Φ` to a rational, as the Subspace Theorem (Phase 4) requires.
For the **empty block** `c = 0` (all-zero stammering window) it is the degenerate `Φ(0) = 0 ∈ ℚ`
(`blockVal_zero`, `Φ_apply_zero`); no positivity of `c` is needed. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem Φ_blockValue_mem_ratInt {c p : ℕ} {e : ℕ → ℕ} (hp : 0 < p)
    (he_lt : ∀ r, r < c → e r < p) (he_mono : ∀ r r', r < r' → r' < c → e r < e r') :
    Φ (blockVal c p e) ∈ RatInt := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [blockVal_zero, Φ_apply_zero]; exact ⟨0, by norm_cast⟩
  set x := Φ (blockVal c p e) with hx
  set N : ℕ := ∑ r ∈ Finset.range c, 3 ^ (c - 1 - r) * 2 ^ e r with hN
  have hrel : ((3 : ℤ_[2]) ^ c - 2 ^ p) * x = -(N : ℤ_[2]) := by
    rw [hx, Φ_blockValue_linear_relation hc hp he_lt he_mono, hN]
    push_cast
    ring
  have hk0 : (3 : ℤ) ^ c - 2 ^ p ≠ 0 := by
    have hodd : Odd ((3 : ℤ) ^ c - 2 ^ p) :=
      (Odd.pow ⟨1, by ring⟩).sub_even (Int.even_pow.mpr ⟨even_two, hp.ne'⟩)
    rintro h
    rw [h, Int.odd_iff] at hodd
    omega
  have hk0Q : (3 : ℚ_[2]) ^ c - 2 ^ p ≠ 0 := by
    have he : (3 : ℚ_[2]) ^ c - 2 ^ p = (((3 ^ c - 2 ^ p : ℤ)) : ℚ_[2]) := by push_cast; ring
    rw [he]; exact_mod_cast hk0
  have hkzQ : ((3 : ℚ_[2]) ^ c - 2 ^ p) * (x : ℚ_[2]) = -(N : ℚ_[2]) := by
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hrel
    push_cast at h; exact h
  refine ⟨(-(N : ℚ)) / ((3 : ℚ) ^ c - 2 ^ p), ?_⟩
  push_cast
  rw [eq_div_iff hk0Q]
  linear_combination hkzQ

end B3
