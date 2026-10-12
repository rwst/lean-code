/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AlloucheShallitBasic
import AdamczewskiBugeaud2007.AutomaticComplexity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Condition (∗)_w in index form (AB07, §4)

Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in
integer bases*, Annals of Mathematics **165** (2007), 547–565, **Section 4**.

The `B3` Missing-Lemma chain consumes AB07's **Condition (∗)_w** in an *index form* on a digit
sequence `a : ℕ → ℕ`: the block `[rₙ + sₙ, rₙ + ⌊w·sₙ⌋)` of `a` is `sₙ`-periodic, with `rₙ/sₙ`
bounded and `sₙ` strictly increasing.  The Subspace-Theorems library (`DiophantineApproximation`,
`AdamczewskiBugeaud2007`) states the same condition with words (`Function.IsStammeringWith`, the
prefix `Uₙ Vₙ^w`) and proves the paper's results about it.  This file keeps the index form the
chain was written against and derives it from the library:

* `B3.ConditionStar` — the index form (formerly `AB.ConditionStar`).
* `B3.exists_conditionStar_of_isStammering` — a word-form stammering sequence over `ℕ` that is not
  eventually periodic satisfies the index form, with the **same** `w` (the word form gives the
  longer block `⌈w·sₙ⌉`).
* `B3.exists_conditionStar_of_isAutomatic` — **a non-eventually-periodic automatic sequence
  satisfies Condition (∗)_w for some `w > 1`** (AB07, proof of Theorem 2).  Formerly the cited
  axiom `AB.isStammering_of_automatic`; now a theorem, from the library's
  `Function.IsAutomatic.isStammering` (Cobham's bound `p(n) ≤ C n`).

Eventual periodicity is the library's `Function.IsEventuallyPeriodic`, which has the same body as
the former `Function.IsEventuallyPeriodic`.

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I. Expansions in
  integer bases.* Annals of Mathematics 165 (2007), 547–565 (Section 4: Condition (∗)_w; Section 5:
  proof of Theorem 2).
-/

namespace B3

open Function

/-- **Condition (∗)_w (Adamczewski–Bugeaud 2007, §4), index form.** For `w > 1`, the sequence
`a = a₀a₁…` satisfies Condition (∗)_w if it is **not eventually periodic** and admits prefix words
`Uₙ Vₙ^w` (lengths `rₙ = |Uₙ|`, `sₙ = |Vₙ| > 0`) with `(rₙ/sₙ)` bounded above and `(sₙ)`
increasing. Clause (i) ("`Uₙ Vₙ^w` is a prefix") is encoded as `sₙ`-periodicity of `a` on the
positions `[rₙ + sₙ, rₙ + ⌊w·sₙ⌋)`: `a i = a (i - sₙ)` there. -/
@[category API, AMS 11 68, ref "AB07"]
def ConditionStar (w : ℝ) (a : ℕ → ℕ) : Prop :=
  ¬ IsEventuallyPeriodic a ∧
  ∃ r s : ℕ → ℕ,
    (∀ n, 0 < s n) ∧
    (∀ n i, r n + s n ≤ i → i < r n + ⌊w * (s n : ℝ)⌋₊ → a i = a (i - s n)) ∧
    (∃ C : ℝ, ∀ n, (r n : ℝ) ≤ C * (s n : ℝ)) ∧
    StrictMono s

/-- **The word form gives the index form.** A sequence satisfying the library's Condition (∗)_w
(`Function.IsStammeringWith`, `w ≥ 0`) and not eventually periodic satisfies `ConditionStar w`. -/
@[category API, AMS 11 68, ref "AB07"]
theorem conditionStar_of_isStammeringWith {w : ℝ} (hw : 0 ≤ w) {a : ℕ → ℕ}
    (h : IsStammeringWith w a) (hnep : ¬ IsEventuallyPeriodic a) : ConditionStar w a := by
  obtain ⟨C, -, r, s, hs, hs1, hrs, hper⟩ := h.exists_periodic hw
  refine ⟨hnep, r, s, fun n ↦ hs1 n, fun n i hi1 hi2 ↦ ?_, ⟨C, hrs⟩, hs⟩
  have hfc : ⌊w * (s n : ℝ)⌋₊ ≤ ⌈w * (s n : ℝ)⌉₊ := Nat.floor_le_ceil _
  have := hper n (i - s n) (by omega) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- **Stammering gives Condition (∗)_w** for some `w > 1`, over the alphabet `ℕ`. -/
@[category API, AMS 11 68, ref "AB07"]
theorem exists_conditionStar_of_isStammering {a : ℕ → ℕ} (h : IsStammering a)
    (hnep : ¬ IsEventuallyPeriodic a) : ∃ w : ℝ, 1 < w ∧ ConditionStar w a := by
  obtain ⟨w, hw, hst⟩ := h
  exact ⟨w, hw, conditionStar_of_isStammeringWith (by linarith) hst hnep⟩

/-- **A non-eventually-periodic automatic sequence satisfies Condition (∗)_w for some `w > 1`**
(Adamczewski–Bugeaud 2007, proof of Theorem 2).  The sequence takes finitely many values, so it is
a relabelling of an automatic sequence over the finite alphabet `Set.range a`, which is stammering
by Cobham's bound (`Function.IsAutomatic.isStammering`); its periodic blocks are blocks of `a`.
Formerly the cited axiom `AB.isStammering_of_automatic`. -/
@[category research solved, AMS 11 68, ref "AB07" "Cob72", group "ab_stammering"]
theorem exists_conditionStar_of_isAutomatic {a : ℕ → ℕ} (hauto : AS.IsAutomatic a)
    (hnep : ¬ IsEventuallyPeriodic a) : ∃ w : ℝ, 1 < w ∧ ConditionStar w a := by
  have hauto' : Function.IsAutomatic a := hauto
  have : Finite (Set.range a) := hauto'.finite_range.to_subtype
  set a' : ℕ → Set.range a := fun n ↦ ⟨a n, n, rfl⟩
  have ha' : Function.IsAutomatic a' :=
    (isAutomatic_comp_iff (g := Subtype.val) Subtype.val_injective.injOn).mp hauto'
  obtain ⟨w, hw, hst⟩ := ha'.isStammering
  obtain ⟨C, -, r, s, hs, hs1, hrs, hper⟩ := hst.exists_periodic (by linarith)
  refine ⟨w, hw, hnep, r, s, fun n ↦ hs1 n, fun n i hi1 hi2 ↦ ?_, ⟨C, hrs⟩, hs⟩
  have hfc : ⌊w * (s n : ℝ)⌋₊ ≤ ⌈w * (s n : ℝ)⌉₊ := Nat.floor_le_ceil _
  have := congrArg Subtype.val (hper n (i - s n) (by omega) (by omega))
  rwa [Nat.sub_add_cancel (by omega)] at this

end B3
