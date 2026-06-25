/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Periodicity
import CC.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Terras–Everett parity-vector bijection (Ter76, Eve77)

The **parity vector** `E_vec k n = (X n, X(T n), …, X(T^{k-1} n))` records the first `k` parities of the
accelerated Collatz orbit of `n` (`CC.E_vec`, in `CC.Parity`). The **Terras–Everett
periodicity theorem** (`terras_periodicity`, in `CC.Periodicity`) says this length-`k` vector depends
**only on `n mod 2^k`** and **conversely determines it**:

  `E_vec k m = E_vec k n  ↔  m % 2^k = n % 2^k`   (for `m, n ≥ 1`).

That is the *well-definedness* (`terras_backward`) and *injectivity* (`terras_forward`) of the induced
map `residue ↦ parity vector`. This file packages the immediate consequence those two halves were
built for — that the map is an honest **bijection**:

> **`terras_bijection`** : the map `parityVec k : ZMod (2^k) → (Fin k → ZMod 2)`,
> `r ↦ (i ↦ E_vec k r.val i)`, is **bijective**; `terrasEquiv k` is the resulting equivalence
> `ZMod (2^k) ≃ (Fin k → ZMod 2)`.

The proof is the standard cardinality argument: the map is injective (`terras_forward`, here in its
positivity-free form `terras_forward'`, composed with the fact that the cast `ℕ → ZMod 2` is injective
on bits `{0,1}`), and `ZMod (2^k)` and `Fin k → ZMod 2` are finite of the same cardinality `2^k`, so
injective ⟹ bijective (`Fintype.bijective_iff_injective_and_card`).

**Downstream.** This is the finite-level input the 2-adic conjugacy construction needs: re-encoding the
bit-vector `Fin k → ZMod 2` as a residue makes `parityVec k` the level map of Lagarias's parity-vector
map `Q∞`, whose level-wise bijectivity feeds `BL.lemma_A2` / `BL.corollary_A3` (a solenoidal map that is
bijective on every `ZMod (2^n)` is a homeomorphism of `ℤ₂`) — the route to discharging the cited
existence axiom `BL.exists_normalized_conjugacy` for the 3x+1 conjugacy map `Φ`.

## Contents
* `terras_forward'` — (proved) `terras_forward` without the positivity hypotheses (the `m, n ≥ 1` in
  `terras_forward` are unused; recovered here for all `m, n` by the shift `m ↦ m + 2^k`).
* `parityVec` — the map `ZMod (2^k) → (Fin k → ZMod 2)` sending a residue to its length-`k` parity
  vector (over the canonical representative `r.val`).
* `terras_bijection` — (proved) `parityVec k` is bijective: the Terras–Everett bijection.
* `terrasEquiv` — the bijection packaged as an `Equiv` `ZMod (2^k) ≃ (Fin k → ZMod 2)`.

## References
* [Ter76] Terras, Riho. *A stopping time problem on the positive integers.* Acta Arithmetica 30
  (1976), no. 3, 241–252 (the parity-vector periodicity / residue bijection).
* [Eve77] Everett, C. J. *Iteration of the number-theoretic function `f(2n) = n`, `f(2n+1) = 3n+2`.*
  Advances in Mathematics 25 (1977), no. 1, 42–45 (independent proof of the parity-vector statement).
-/

namespace CC

/-- **`terras_forward` without positivity.** `terras_forward` carries unused hypotheses `m, n ≥ 1`;
the parity vector still determines the residue for *all* `m, n`. *Proof:* apply `terras_forward` to the
shifted pair `m + 2^k`, `n + 2^k` (both `≥ 1`), whose parity vectors agree with those of `m`, `n` by
`terras_backward` (shifting by `2^k` fixes the residue mod `2^k`), then undo the shift. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_everett"]
theorem terras_forward' (k m n : ℕ) (h : E_vec k m = E_vec k n) : m % 2 ^ k = n % 2 ^ k := by
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
  have hm : (m + 2 ^ k) % 2 ^ k = m % 2 ^ k := Nat.add_mod_right m (2 ^ k)
  have hn : (n + 2 ^ k) % 2 ^ k = n % 2 ^ k := Nat.add_mod_right n (2 ^ k)
  have hev : E_vec k (m + 2 ^ k) = E_vec k (n + 2 ^ k) := by
    rw [terras_backward k (m + 2 ^ k) m hm, terras_backward k (n + 2 ^ k) n hn]; exact h
  have key := terras_forward k (m + 2 ^ k) (n + 2 ^ k) (by omega) (by omega) hev
  rwa [hm, hn] at key

/-- The **parity-vector map on residues**: `parityVec k r` is the length-`k` parity vector
`(X r, X(T r), …, X(T^{k-1} r))` of the canonical representative `r.val` of `r : ZMod (2^k)`, with each
bit cast into `ZMod 2`. Well-defined on residues because `E_vec k ·` is `2^k`-periodic
(`terras_backward`); this is the finite level map of Lagarias's parity-vector map `Q∞`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_everett"]
def parityVec (k : ℕ) (r : ZMod (2 ^ k)) : Fin k → ZMod 2 :=
  fun i => (E_vec k r.val i : ZMod 2)

/-- **The Terras–Everett bijection** [Ter76, Eve77]. The parity-vector map
`parityVec k : ZMod (2^k) → (Fin k → ZMod 2)` is **bijective**: every length-`k` bit pattern is the
parity vector of exactly one residue class mod `2^k`. *Proof:* injectivity is `terras_forward'` (two
residues with equal parity vectors are congruent mod `2^k`, hence equal as `val < 2^k`), using that
`ℕ → ZMod 2` is injective on the bits `{0,1}`; both types are finite of cardinality `2^k`, so an
injection is a bijection (`Fintype.bijective_iff_injective_and_card`). -/
@[category research solved, AMS 11 37, ref "Ter76" "Eve77", group "terras_everett"]
theorem terras_bijection (k : ℕ) : Function.Bijective (parityVec k) := by
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r s hrs => ?_, ?_⟩
  · have hev : E_vec k r.val = E_vec k s.val := by
      funext i
      have hi : (E_vec k r.val i : ZMod 2) = (E_vec k s.val i : ZMod 2) := congr_fun hrs i
      rw [ZMod.natCast_eq_natCast_iff] at hi
      have hi2 : E_vec k r.val i % 2 = E_vec k s.val i % 2 := hi
      have h1 := E_vec_le_one k r.val i
      have h2 := E_vec_le_one k s.val i
      omega
    have hmod := terras_forward' k r.val s.val hev
    rw [Nat.mod_eq_of_lt (ZMod.val_lt r), Nat.mod_eq_of_lt (ZMod.val_lt s)] at hmod
    exact ZMod.val_injective _ hmod
  · simp [ZMod.card, Fintype.card_pi, Finset.prod_const, Fintype.card_fin]

/-- The Terras–Everett bijection (`terras_bijection`) as an **equivalence**
`ZMod (2^k) ≃ (Fin k → ZMod 2)`: residues mod `2^k` are in canonical bijection with length-`k` parity
vectors. -/
@[category API, AMS 11 37, ref "Ter76" "Eve77", group "terras_everett"]
noncomputable def terrasEquiv (k : ℕ) : ZMod (2 ^ k) ≃ (Fin k → ZMod 2) :=
  Equiv.ofBijective (parityVec k) (terras_bijection k)

end CC
