/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Rauzy

/-!
# Degrees in the reduced Rauzy graph, and the unique right-special block

This completes §3 of `BB47/M1M2.tex` (Prop. 3.3) and supplies the degree bookkeeping that
[M3, Lem. 3.2] — the shape lemma behind Theorem B — runs on.

Sending an edge to its source is a map from the `p_∞(n+1, w)` recurrent length-`(n+1)` blocks
**onto** the `p_∞(n, w)` recurrent length-`n` blocks (`BB47.exists_outEdge`), so

  `p_∞(n+1, w) = ∑_{a recurrent, |a| = n} outDeg a`,  every `outDeg a ≥ 1`.

Under `p_∞(n+1) = p_∞(n) + 1` — which by `BB47.pInf_lt_succ` and `BB47.succ_le_pInf` is exactly
what the hypothesis of Problem 10.47 gives at every scale — the sum exceeds the number of
summands by one, so exactly one vertex has out-degree `2` and every other has out-degree `1`.
That single vertex is the unique **right-special** recurrent block `R_n`; the mirror argument
gives the unique left-special block `L_n`.  Together with strong connectivity
(`BB47.reach_recFactorSet`) this pins `G'_n(w)` down to a cycle with one chord, which is where the
classification analysis of [BKK26, §2.3] and of [M3, §4] starts.

**What this file proves and what it imports.**  *Existence* and *uniqueness* of the special block
are not proved here: since WP8 of `plans/plan-subshift.html` they are
`SymbolicDynamics.FullShift.exists_isRightSpecial` and `eq_of_isRightSpecial` (with their left
mirrors), stated in `ForMathlib` for the language of an arbitrary subshift and proved there
*without* degree sums — the counting lemma deletes two superfluous edges instead.  What remains
genuinely local is the degree bookkeeping, which `ForMathlib` does not express: `outDeg`/`inDeg`
as `Finset.card`s of fibres, the two sum identities, and the bridge
`isRightSpecial_iff_two_le_outDeg`.  The exact values `2` and `1` then follow from the sum
identity, which is the one place a degree sum is still needed.

## Main results

* `BB47.outDeg`, `BB47.inDeg` — the degrees, as `Finset.card`s of fibres.
* `BB47.one_le_outDeg`, `BB47.one_le_inDeg` — every vertex has degree at least one.
* `BB47.sum_outDeg`, `BB47.sum_inDeg` — the two degree-sum identities.
* `BB47.isRightSpecial_iff_two_le_outDeg`, `BB47.isLeftSpecial_iff_two_le_inDeg` — the bridge to
  `ForMathlib`'s specialness predicates.
* `BB47.exists_unique_rightSpecial` — **[M1M2, Prop. 3.3]**: under `p_∞(n+1) = p_∞(n) + 1` there
  is exactly one right-special recurrent length-`n` block.
* `BB47.exists_unique_leftSpecial` — and exactly one left-special one.

## References

* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — Prop. 3.3.
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Lem. 4.2 (shape).
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — §2.3.
-/

namespace BB47

open ForMathlib.SubwordComplexity SymbolicDynamics.FullShift

variable {α : Type*} [Finite α] [DecidableEq α]

/-- The recurrent length-`n` blocks, as a `Finset` — the vertex set of `G'_n(w)`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
noncomputable def recVerts (u : ℕ → α) (n : ℕ) : Finset (Fin n → α) :=
  (Set.toFinite (recFactorSet u n)).toFinset

omit [DecidableEq α] in
@[simp]
lemma mem_recVerts {u : ℕ → α} {n : ℕ} {a : Fin n → α} :
    a ∈ recVerts u n ↔ Recurrent u n a := by
  simp [recVerts]

omit [DecidableEq α] in
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
lemma card_recVerts (u : ℕ → α) (n : ℕ) : (recVerts u n).card = pInf u n := by
  rw [recVerts, pInf, Set.ncard_eq_toFinset_card]

/-- The **out-degree** of a vertex: the number of recurrent length-`(n+1)` blocks extending it to
the right. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
noncomputable def outDeg (u : ℕ → α) (n : ℕ) (a : Fin n → α) : ℕ :=
  ((recVerts u (n + 1)).filter fun e => edgeSrc e = a).card

/-- The **in-degree** of a vertex. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
noncomputable def inDeg (u : ℕ → α) (n : ℕ) (a : Fin n → α) : ℕ :=
  ((recVerts u (n + 1)).filter fun e => edgeTgt e = a).card

/-- [M1M2, Prop. 3.3]: out-degrees are at least one. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem one_le_outDeg {u : ℕ → α} {n : ℕ} {a : Fin n → α} (ha : Recurrent u n a) :
    1 ≤ outDeg u n a := by
  obtain ⟨e, he, hsrc⟩ := exists_outEdge ha
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨mem_recVerts.mpr he, hsrc⟩⟩

/-- [M1M2, Prop. 3.3]: in-degrees are at least one. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem one_le_inDeg {u : ℕ → α} {n : ℕ} {a : Fin n → α} (ha : Recurrent u n a) :
    1 ≤ inDeg u n a := by
  obtain ⟨e, he, htgt⟩ := exists_inEdge ha
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨mem_recVerts.mpr he, htgt⟩⟩

/-- The out-degree sum identity: edges are counted once each, by their source. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem sum_outDeg (u : ℕ → α) (n : ℕ) :
    ∑ a ∈ recVerts u n, outDeg u n a = pInf u (n + 1) := by
  rw [← card_recVerts u (n + 1)]
  exact (Finset.card_eq_sum_card_fiberwise fun e he =>
    mem_recVerts.mpr (recurrent_edgeSrc (mem_recVerts.mp he))).symm

/-- The in-degree sum identity. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem sum_inDeg (u : ℕ → α) (n : ℕ) :
    ∑ a ∈ recVerts u n, inDeg u n a = pInf u (n + 1) := by
  rw [← card_recVerts u (n + 1)]
  exact (Finset.card_eq_sum_card_fiberwise fun e he =>
    mem_recVerts.mpr (recurrent_edgeTgt (mem_recVerts.mp he))).symm

/-! ## The bridge to `ForMathlib`'s specialness predicates -/

/-- Right-special *is* out-degree at least two. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem isRightSpecial_iff_two_le_outDeg {u : ℕ → α} {n : ℕ} {a : Fin n → α} :
    IsRightSpecial (recFactorSet u) n a ↔ 2 ≤ outDeg u n a := by
  rw [outDeg, show (2 : ℕ) ≤ _ ↔ 1 < _ from Iff.rfl, Finset.one_lt_card]
  constructor
  · rintro ⟨e₁, he₁, e₂, he₂, hs₁, hs₂, hne⟩
    exact ⟨e₁, Finset.mem_filter.mpr ⟨mem_recVerts.mpr he₁, hs₁⟩, e₂,
      Finset.mem_filter.mpr ⟨mem_recVerts.mpr he₂, hs₂⟩, hne⟩
  · rintro ⟨e₁, h₁, e₂, h₂, hne⟩
    obtain ⟨hv₁, hs₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨hv₂, hs₂⟩ := Finset.mem_filter.mp h₂
    exact ⟨e₁, mem_recVerts.mp hv₁, e₂, mem_recVerts.mp hv₂, hs₁, hs₂, hne⟩

/-- Left-special *is* in-degree at least two. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem isLeftSpecial_iff_two_le_inDeg {u : ℕ → α} {n : ℕ} {a : Fin n → α} :
    IsLeftSpecial (recFactorSet u) n a ↔ 2 ≤ inDeg u n a := by
  rw [inDeg, show (2 : ℕ) ≤ _ ↔ 1 < _ from Iff.rfl, Finset.one_lt_card]
  constructor
  · rintro ⟨e₁, he₁, e₂, he₂, ht₁, ht₂, hne⟩
    exact ⟨e₁, Finset.mem_filter.mpr ⟨mem_recVerts.mpr he₁, ht₁⟩, e₂,
      Finset.mem_filter.mpr ⟨mem_recVerts.mpr he₂, ht₂⟩, hne⟩
  · rintro ⟨e₁, h₁, e₂, h₂, hne⟩
    obtain ⟨hv₁, ht₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨hv₂, ht₂⟩ := Finset.mem_filter.mp h₂
    exact ⟨e₁, mem_recVerts.mp hv₁, e₂, mem_recVerts.mp hv₂, ht₁, ht₂, hne⟩

/-! ## Exactly one special block -/

/-- The degree ledger, given existence and uniqueness of the special vertex: the special vertex
has degree `2` and every other has degree `1`.  Stated once for a general degree function so that
the right and the left case are the *same* proof. -/
private theorem degrees_of_unique_special {u : ℕ → α} {n : ℕ} (d : (Fin n → α) → ℕ)
    (hpos : ∀ a ∈ recVerts u n, 1 ≤ d a) (hsum : ∑ a ∈ recVerts u n, d a = pInf u (n + 1))
    (h : pInf u (n + 1) = pInf u n + 1) {a : Fin n → α} (haV : a ∈ recVerts u n)
    (huniq : ∀ c ∈ recVerts u n, 2 ≤ d c → c = a) :
    d a = 2 ∧ ∀ c ∈ recVerts u n, c ≠ a → d c = 1 := by
  have hother : ∀ c ∈ recVerts u n, c ≠ a → d c = 1 := by
    intro c hc hca
    have h1 := hpos c hc
    by_contra hne
    exact hca (huniq c hc (by omega))
  refine ⟨?_, hother⟩
  have hsplit := Finset.add_sum_erase (recVerts u n) d haV
  have herase : ∑ c ∈ (recVerts u n).erase a, d c = (recVerts u n).card - 1 := by
    rw [Finset.sum_congr rfl fun c hc =>
      hother c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)]
    simp [Finset.card_erase_of_mem haV]
  have hcard : 1 ≤ (recVerts u n).card := Finset.card_pos.mpr ⟨a, haV⟩
  rw [card_recVerts] at hcard herase
  omega

/-- **[M1M2, Prop. 3.3]: the unique right-special block.**  If `p_∞(n+1, w) = p_∞(n, w) + 1` then
exactly one recurrent length-`n` block has two recurrent right extensions; every other has
exactly one.

Under the hypothesis of Problem 10.47 — `p_∞(n) = n + 1` for all `n` — the premise holds at every
scale, so `R_n` is well defined for every `n`.  It is the `R_n` of [M3, Lem. 3.2]. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_unique_rightSpecial (u : ℕ → α) (n : ℕ) (h : pInf u (n + 1) = pInf u n + 1) :
    ∃ a ∈ recVerts u n, outDeg u n a = 2 ∧ ∀ c ∈ recVerts u n, c ≠ a → outDeg u n c = 1 := by
  have hL : IsLanguage (recFactorSet u) := isLanguage_recurrentLanguage u
  have hlt : (recFactorSet u n).ncard < (recFactorSet u (n + 1)).ncard := by
    rw [show (recFactorSet u n).ncard = pInf u n from rfl,
      show (recFactorSet u (n + 1)).ncard = pInf u (n + 1) from rfl, h]
    omega
  have hle : (recFactorSet u (n + 1)).ncard ≤ (recFactorSet u n).ncard + 1 := by
    rw [show (recFactorSet u n).ncard = pInf u n from rfl,
      show (recFactorSet u (n + 1)).ncard = pInf u (n + 1) from rfl, h]
  obtain ⟨a, haL, hRS⟩ := exists_isRightSpecial hL hlt
  refine ⟨a, mem_recVerts.mpr haL, degrees_of_unique_special _ (fun c hc =>
    one_le_outDeg (mem_recVerts.mp hc)) (sum_outDeg u n) h (mem_recVerts.mpr haL) ?_⟩
  exact fun c _ hc => eq_of_isRightSpecial hL hle (isRightSpecial_iff_two_le_outDeg.mpr hc) hRS

/-- **[M1M2, Prop. 3.3]: the unique left-special block.** -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_unique_leftSpecial (u : ℕ → α) (n : ℕ) (h : pInf u (n + 1) = pInf u n + 1) :
    ∃ a ∈ recVerts u n, inDeg u n a = 2 ∧ ∀ c ∈ recVerts u n, c ≠ a → inDeg u n c = 1 := by
  have hL : IsLanguage (recFactorSet u) := isLanguage_recurrentLanguage u
  have hlt : (recFactorSet u n).ncard < (recFactorSet u (n + 1)).ncard := by
    rw [show (recFactorSet u n).ncard = pInf u n from rfl,
      show (recFactorSet u (n + 1)).ncard = pInf u (n + 1) from rfl, h]
    omega
  have hle : (recFactorSet u (n + 1)).ncard ≤ (recFactorSet u n).ncard + 1 := by
    rw [show (recFactorSet u n).ncard = pInf u n from rfl,
      show (recFactorSet u (n + 1)).ncard = pInf u (n + 1) from rfl, h]
  obtain ⟨a, haL, hLS⟩ := exists_isLeftSpecial hL hlt
  refine ⟨a, mem_recVerts.mpr haL, degrees_of_unique_special _ (fun c hc =>
    one_le_inDeg (mem_recVerts.mp hc)) (sum_inDeg u n) h (mem_recVerts.mpr haL) ?_⟩
  exact fun c _ hc => eq_of_isLeftSpecial hL hle (isLeftSpecial_iff_two_le_inDeg.mpr hc) hLS

/-- The form in which Problem 10.47's hypothesis delivers the premise: under `p_∞(n) = n + 1` for
every `n`, the graph `G'_n(w)` has `n + 1` vertices and `n + 2` edges, and there is exactly one
right-special and exactly one left-special recurrent block at every scale. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem rightSpecial_of_minimal (u : ℕ → α) (hp : ∀ n, pInf u n = n + 1) (n : ℕ) :
    (recVerts u n).card = n + 1 ∧ (recVerts u (n + 1)).card = n + 2 ∧
      ∃ a ∈ recVerts u n, outDeg u n a = 2 ∧ ∀ c ∈ recVerts u n, c ≠ a → outDeg u n c = 1 := by
  refine ⟨by rw [card_recVerts, hp], by rw [card_recVerts, hp], ?_⟩
  exact exists_unique_rightSpecial u n (by rw [hp, hp])

end BB47
