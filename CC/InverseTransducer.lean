/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The inverse CTUHSK transducer: the `mod 3` matching conditions (Eqns 17–20)

This file formalises the four congruence identities `[Eqn.17]`–`[Eqn.20]` of [CTUHSK], the
"*Restrictions on the CTUHSK Generative Parameters*" (§12.1). They are the arithmetic constraints that
tie a node of `BELnet` to its predecessor — the algebra of the **inverse CTUHSK function** (the
predecessor-set map `{P(BEL(n))}`, `[Eqn.6]`–`[Eqn.9]`).

## Set-up (following [CTUHSK] §2–§8)

The compact map uses a "push-Up" operator `U#(d) = 3d + 1` and a "pull-Down" operator that divides out
all `2`s. A **U-ceiling number** `U#` is the value `3d + 1` produced from an odd **D-floor number** `d`
(its predecessor, the `D#` of the paper). Every odd positive integer `D#` is one of three residue
classes mod `6`; the U-ceiling numbers landing in the two non-degenerate ladders are

* `BEL(6m-5)` : `U# = (6m-5)·4^x` at the `4^x` rungs (the "`QEL(6m-5)`" active rungs), and
* `BEL(6m-1)` : `U# = (6m-1)·2·4^y` at the `2·4^y` rungs.

Given such a `U#`, its predecessor `d = D# = (U# − 1)/3` is a genuine integer precisely because
`U# ≡ 1 (mod 3)` (`qel5_modThree`, `qel1_modThree`). The four identities pin down `d (mod 3)` — i.e.
which of the three residue classes the predecessor lives in — purely from the exponent and `m`.

We state each equation on the predecessor `d` characterised by the push-Up relation `3·d + 1 = U#`,
which *is* `d = (U# − 1)/3`; this is the honest inverse of `U#`. A congruence `d ≡ e [ZMOD 3]` is
equivalent to the paper's `d MOD 3 = e MOD 3`.

## The four identities

* `eqn17` — `BEL(6m-5)`, QEL form (`4^x` rung): `d ≡ x − m + 1 [ZMOD 3]`.
* `eqn18` — `BEL(6m-1)`, QEL form (`2·4^y` rung): `d ≡ y + m − 1 [ZMOD 3]`.
  (The paper prints this as "[Eqn.19]" in §12.1 but introduces it as Eqn.18; it is the `6m-1`
  companion of Eqn.17. We follow the intended numbering.)
* `eqn19` — `BEL(6m-5)`, BEL form (`2^w` rung, `w` even, `w = 2x`): `d ≡ ⌊w/2⌋ − m + 1 [ZMOD 3]`.
* `eqn20` — `BEL(6m-1)`, BEL form (`2^v` rung, `v` odd, `v = 2y+1`): `d ≡ ⌊(v-1)/2⌋ + m − 1 [ZMOD 3]`.

`eqn19`/`eqn20` are exactly `eqn17`/`eqn18` rewritten for the binary-exponential ladders via
`2^{2x} = 4^x` and `2^{2y+1} = 2·4^y` — "*Rewriting [Eqn.17]&[Eqn.18] for the Binary-Exponential-
Ladders*" (§12.1). All four are ordinary modular arithmetic; nothing here depends on the Collatz
Conjecture and there are no axioms.

## References
* [CTUHSK] Halemane, Keshava Prasad. *Collatz-Thwaites-Ulam-Hasse-Syracuse-Kakutani (CTUHSK) Theorem.*
  (2026), §12.1 Eqns 17–20: the `mod 3` matching between a D-floor predecessor and its U-ceiling
  successor along the binary/quaternary exponential ladders.
-/

namespace CC.InverseTransducer

/-! ### Periodicity helpers (`4^·` and `3·↑·` mod 9) -/

/-- `4^x mod 9` has period `3` in the exponent, since `4^3 = 64 ≡ 1 (mod 9)`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma pow4_periodic (x : ℕ) : (4 : ℤ) ^ x ≡ 4 ^ (x % 3) [ZMOD 9] := by
  conv_lhs => rw [← Nat.div_add_mod x 3, pow_add, pow_mul]
  have h64 : (4 : ℤ) ^ 3 ≡ 1 [ZMOD 9] := by decide
  simpa using (h64.pow (x / 3)).mul_right ((4 : ℤ) ^ (x % 3))

/-- `3·x ≡ 3·(x mod 3) (mod 9)`: tripling collapses the period-`3` structure of `x` mod `9`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma three_mul_periodic (x : ℕ) :
    (3 : ℤ) * (x : ℤ) ≡ 3 * ((x % 3 : ℕ) : ℤ) [ZMOD 9] := by
  have hx : (x : ℤ) = 3 * ((x / 3 : ℕ) : ℤ) + ((x % 3 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod x 3).symm
  rw [Int.modEq_iff_dvd]
  exact ⟨-((x / 3 : ℕ) : ℤ), by rw [hx]; ring⟩

/-! ### The `mod 9` core of the numerators -/

/-- Mod-`9` value of the U-ceiling number `(6m-5)·4^x`: it is `3·(x − m + 1) + 1`. This is the
content behind `[Eqn.17]`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma numer17 (m : ℤ) (x : ℕ) :
    (6 * m - 5) * 4 ^ x ≡ 3 * ((x : ℤ) - m + 1) + 1 [ZMOD 9] := by
  have h3 := three_mul_periodic x
  have base : (6 * m - 5) * (4 : ℤ) ^ (x % 3)
      ≡ 3 * (((x % 3 : ℕ) : ℤ) - m + 1) + 1 [ZMOD 9] := by
    rcases (show x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 by omega) with h | h | h <;>
      rw [h] <;> (rw [Int.modEq_iff_dvd]; push_cast; ring_nf; omega)
  calc (6 * m - 5) * (4 : ℤ) ^ x
      ≡ (6 * m - 5) * (4 : ℤ) ^ (x % 3) [ZMOD 9] := (pow4_periodic x).mul_left _
    _ ≡ 3 * (((x % 3 : ℕ) : ℤ) - m + 1) + 1 [ZMOD 9] := base
    _ ≡ 3 * ((x : ℤ) - m + 1) + 1 [ZMOD 9] := by
        have h := h3.symm.add_right (-3 * m + 4)
        have e1 : 3 * (((x % 3 : ℕ) : ℤ) - m + 1) + 1
            = 3 * ((x % 3 : ℕ) : ℤ) + (-3 * m + 4) := by ring
        have e2 : 3 * ((x : ℤ) - m + 1) + 1 = 3 * (x : ℤ) + (-3 * m + 4) := by ring
        rw [e1, e2]; exact h

/-- Mod-`9` value of the U-ceiling number `(6m-1)·2·4^y`: it is `3·(y + m − 1) + 1`. This is the
content behind `[Eqn.18]`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma numer18 (m : ℤ) (y : ℕ) :
    (6 * m - 1) * 2 * 4 ^ y ≡ 3 * ((y : ℤ) + m - 1) + 1 [ZMOD 9] := by
  have h3 := three_mul_periodic y
  have base : (6 * m - 1) * 2 * (4 : ℤ) ^ (y % 3)
      ≡ 3 * (((y % 3 : ℕ) : ℤ) + m - 1) + 1 [ZMOD 9] := by
    rcases (show y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 by omega) with h | h | h <;>
      rw [h] <;> (rw [Int.modEq_iff_dvd]; push_cast; ring_nf; omega)
  calc (6 * m - 1) * 2 * (4 : ℤ) ^ y
      ≡ (6 * m - 1) * 2 * (4 : ℤ) ^ (y % 3) [ZMOD 9] := (pow4_periodic y).mul_left _
    _ ≡ 3 * (((y % 3 : ℕ) : ℤ) + m - 1) + 1 [ZMOD 9] := base
    _ ≡ 3 * ((y : ℤ) + m - 1) + 1 [ZMOD 9] := by
        have h := h3.symm.add_right (3 * m - 2)
        have e1 : 3 * (((y % 3 : ℕ) : ℤ) + m - 1) + 1
            = 3 * ((y % 3 : ℕ) : ℤ) + (3 * m - 2) := by ring
        have e2 : 3 * ((y : ℤ) + m - 1) + 1 = 3 * (y : ℤ) + (3 * m - 2) := by ring
        rw [e1, e2]; exact h

/-- Passing from the `mod 9` value of a U-ceiling number `U = 3d+1` to the `mod 3` residue of its
predecessor `d`: if `U ≡ 3r + 1 (mod 9)` then `d ≡ r (mod 3)`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma pred_of_numer (d r U : ℤ) (hU : 3 * d + 1 = U)
    (hnum : U ≡ 3 * r + 1 [ZMOD 9]) : d ≡ r [ZMOD 3] := by
  have h1 : (3 * d + 1 : ℤ) ≡ 3 * r + 1 [ZMOD 9] := by rw [hU]; exact hnum
  have h2 : (3 : ℤ) * d ≡ 3 * r [ZMOD 9] := by simpa using h1.sub_right 1
  rw [Int.modEq_iff_dvd] at h2
  rw [Int.modEq_iff_dvd]
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by omega⟩

/-! ### U-ceiling numbers are `≡ 1 (mod 3)` (so the predecessor `D#` is an integer) -/

/-- Every U-ceiling number of `BEL(6m-5)` satisfies `U# ≡ 1 (mod 3)`, so `D# = (U# − 1)/3 ∈ ℤ`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma qel5_modThree (m : ℤ) (x : ℕ) : (6 * m - 5) * (4 : ℤ) ^ x ≡ 1 [ZMOD 3] := by
  have h4 : (4 : ℤ) ^ x ≡ 1 [ZMOD 3] := by
    simpa using (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide).pow x
  have h6 : (6 * m - 5) ≡ 1 [ZMOD 3] := by rw [Int.modEq_iff_dvd]; exact ⟨2 - 2 * m, by ring⟩
  simpa using h6.mul h4

/-- Every U-ceiling number of `BEL(6m-1)` satisfies `U# ≡ 1 (mod 3)`, so `D# = (U# − 1)/3 ∈ ℤ`. -/
@[category API, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
lemma qel1_modThree (m : ℤ) (y : ℕ) : (6 * m - 1) * 2 * (4 : ℤ) ^ y ≡ 1 [ZMOD 3] := by
  have h4 : (4 : ℤ) ^ y ≡ 1 [ZMOD 3] := by
    simpa using (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide).pow y
  have h6 : (6 * m - 1) * 2 ≡ 1 [ZMOD 3] := by rw [Int.modEq_iff_dvd]; exact ⟨1 - 4 * m, by ring⟩
  simpa using h6.mul h4

/-! ### The four identities -/

/-- **[CTUHSK, Eqn.17]** (`BEL(6m-5)`, QEL `4^x` rung). If `d` is the D-floor predecessor of the
U-ceiling number `(6m-5)·4^x` — that is, `3·d + 1 = (6m-5)·4^x`, so `d = [(6m-5)·4^x − 1]/3` — then
`d ≡ x − m + 1 (mod 3)`. -/
@[category research solved, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
theorem eqn17 (m : ℤ) (x : ℕ) (d : ℤ) (h : 3 * d + 1 = (6 * m - 5) * 4 ^ x) :
    d ≡ (x : ℤ) - m + 1 [ZMOD 3] :=
  pred_of_numer d ((x : ℤ) - m + 1) _ h (numer17 m x)

/-- **[CTUHSK, Eqn.18]** (`BEL(6m-1)`, QEL `2·4^y` rung). If `d` is the D-floor predecessor of the
U-ceiling number `(6m-1)·2·4^y` — that is, `3·d + 1 = (6m-1)·2·4^y`, so `d = [(6m-1)·2·4^y − 1]/3` —
then `d ≡ y + m − 1 (mod 3)`. -/
@[category research solved, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
theorem eqn18 (m : ℤ) (y : ℕ) (d : ℤ) (h : 3 * d + 1 = (6 * m - 1) * 2 * 4 ^ y) :
    d ≡ (y : ℤ) + m - 1 [ZMOD 3] :=
  pred_of_numer d ((y : ℤ) + m - 1) _ h (numer18 m y)

/-- **[CTUHSK, Eqn.19]** (`BEL(6m-5)`, BEL `2^w` rung, `w` even). The binary-ladder form of Eqn.17:
with `w = 2x` even, `d ≡ ⌊w/2⌋ − m + 1 (mod 3)`. Obtained from `eqn17` via `2^w = 4^{w/2}`. -/
@[category research solved, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
theorem eqn19 (m : ℤ) (w : ℕ) (hw : Even w) (d : ℤ) (h : 3 * d + 1 = (6 * m - 5) * 2 ^ w) :
    d ≡ ((w / 2 : ℕ) : ℤ) - m + 1 [ZMOD 3] := by
  obtain ⟨x, rfl⟩ := hw
  have e : (2 : ℤ) ^ (x + x) = 4 ^ x := by rw [← two_mul, pow_mul]; norm_num
  rw [e] at h
  have hx : (x + x) / 2 = x := by omega
  rw [hx]
  exact eqn17 m x d h

/-- **[CTUHSK, Eqn.20]** (`BEL(6m-1)`, BEL `2^v` rung, `v` odd). The binary-ladder form of Eqn.18:
with `v = 2y+1` odd, `d ≡ ⌊(v-1)/2⌋ + m − 1 (mod 3)`. Obtained from `eqn18` via `2^v = 2·4^{(v-1)/2}`. -/
@[category research solved, AMS 11, ref "CTUHSK", group "ctuhsk_inverse_transducer"]
theorem eqn20 (m : ℤ) (v : ℕ) (hv : Odd v) (d : ℤ) (h : 3 * d + 1 = (6 * m - 1) * 2 ^ v) :
    d ≡ (((v - 1) / 2 : ℕ) : ℤ) + m - 1 [ZMOD 3] := by
  obtain ⟨y, rfl⟩ := hv
  have e : (6 * m - 1) * (2 : ℤ) ^ (2 * y + 1) = (6 * m - 1) * 2 * 4 ^ y := by
    have h2 : (2 : ℤ) ^ (2 * y + 1) = 2 * 4 ^ y := by
      rw [pow_add, pow_mul, pow_one]; norm_num; ring
    rw [h2]; ring
  rw [e] at h
  have hv2 : (2 * y + 1 - 1) / 2 = y := by omega
  rw [hv2]
  exact eqn18 m y d h

end CC.InverseTransducer
