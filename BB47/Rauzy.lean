/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Basic
import ForMathlib.Dynamics.SymbolicDynamics.Rauzy

/-!
# The reduced Rauzy graph, and why the Coven–Hedlund non-Sturmian branch cannot occur

This is §3 of `BB47/M1M2.tex` (milestone M1) together with the graph-theoretic engine of
[M3, Prop. 5.2], the result that removes one of Coven and Hedlund's three classes from Problem
10.47 entirely.

The **reduced Rauzy graph** `G'_n(u)` of [BKK26, Def. 2.5] has the recurrent length-`n` blocks as
vertices and the recurrent length-`(n+1)` blocks as edges, `e` running from `e ∘ Fin.castSucc`
(drop the last letter) to `e ∘ Fin.succ` (drop the first).

**This file no longer proves anything.**  Since WP8 of `plans/plan-subshift.html` the graph, its
reachability relation and its exclusion engine live in
`ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean`, stated for the language of an arbitrary
subshift; `BB47.recFactorSet u = recurrentLanguage u` is `rfl`, so everything below is that
general theory read in the vocabulary of Problem 10.47.  `edgeSrc` and `edgeTgt` are `export`ed,
not redefined: there is one constant with two names.

## Main results

* `BB47.recFactorSet_eq_recurrentLanguage` — the bridge, definitional.
* `BB47.recurrent_edgeSrc`, `BB47.recurrent_edgeTgt` — the graph is well defined: the two ends of
  a recurrent edge are recurrent vertices.
* `BB47.reach_recFactorSet` — **[M1M2, Prop. 3.2]: `G'_n(u)` is strongly connected**, for every
  `n` and every infinite word `u`, with no hypothesis whatsoever.
* `BB47.exists_outEdge`, `BB47.exists_inEdge` — [M1M2, Prop. 3.3], degree half: every vertex has
  in- and out-degree at least one.
* `BB47.mem_of_outClosed` — **the exclusion engine.**  A set of vertices closed under out-edges
  and meeting the vertex set contains *every* vertex.  Equivalently `BB47.not_properOutClosed`:
  `G'_n(u)` has no proper non-empty out-closed set of vertices.

## Why this is the load-bearing statement for 10.47

Coven and Hedlund classify the bisequences with `P(x, n) ≤ n + 1` into Sturmian ones (which for
them includes the periodic and the *skew* type) and one further family, parametrised by two
periodic bisequences of coprime periods glued at a single defect [CH73, Thm. 4.12].  For a word
in that family the length-`N` blocks of the right periodic tail form a non-empty **proper** set of
vertices closed under out-edges — no block of one tail occurs in the other, and the gluing block
occurs exactly once, hence not at all in a recurrent window ([M3, Prop. 5.2]).  By
`BB47.not_properOutClosed` that is impossible for an `ω`-limit set.  So the classification
collapses from three branches to two, which is Theorem B of `BB47/M3.tex`.

Note the asymmetry that makes this work: strong connectivity uses the **one-sidedness** of `u`
essentially — it is a statement about `ω`-limit sets, not about subshifts.  A general subshift
with `p(n) = n + 1` need *not* have strongly connected Rauzy graphs, and [M3, Ex. 5.3] exhibits
one that does not, namely `…000 · 0101…`.  That word is also the counterexample to deriving strong
connectivity from topological transitivity; see the implementation notes of the `ForMathlib` file.

Strong connectivity does **not** imply that `Ω(u)` is topologically transitive; see
[M1M2, Rem. 3.4, Ex. 3.5], where `u = ∏ₘ 0ᵐ1ᵐ` has every `G'_n(u)` strongly connected,
`p_∞(n) = 2n`, and `Ω(u)` non-transitive.  Under the hypothesis `p_∞(n) = n + 1` transitivity does
hold, but only as a consequence of the structure theorem.

## References

* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — Def. 2.5 (the reduced Rauzy
  graph) and §2.3.
* [CH73] E. M. Coven, G. A. Hedlund, *Sequences with minimal block growth*, Math. Systems Theory
  **7** (1973), 138–153 — Thm. 4.12 (the non-Sturmian normal form), Thm. 5.03.
* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — §3 (Props. 3.2, 3.3, Rem. 3.4, Ex. 3.5).
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Prop. 5.2 and Ex. 5.3.
-/

namespace BB47

open ForMathlib.SubwordComplexity SymbolicDynamics.FullShift

variable {α : Type*}

/-! ## The bridge to `ForMathlib` -/

/-- `BB47.Recurrent` and `ForMathlib.SubwordComplexity.IsRecurrentFactor` are the same
definition. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
lemma recurrent_iff_isRecurrentFactor {u : ℕ → α} {n : ℕ} {v : Fin n → α} :
    Recurrent u n v ↔ IsRecurrentFactor u n v := Iff.rfl

/-- …hence the vertex set of `G'_n(u)` *is* the `ForMathlib` recurrent language, and every
statement about the latter is a statement about Problem 10.47. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
lemma recFactorSet_eq_recurrentLanguage (u : ℕ → α) (n : ℕ) :
    recFactorSet u n = recurrentLanguage u n := rfl

/-! ## Edges

`edgeSrc` and `edgeTgt` are not redefined here: these are the `ForMathlib` constants, re-exported
so that `BB47.edgeSrc` resolves.  Their `simp` lemmas `edgeSrc_factor` and `edgeTgt_factor` come
with them. -/

export SymbolicDynamics.FullShift (edgeSrc edgeTgt)

/-- The graph is well defined: the source of a recurrent edge is a recurrent vertex. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem recurrent_edgeSrc {u : ℕ → α} {n : ℕ} {e : Fin (n + 1) → α} (he : Recurrent u (n + 1) e) :
    Recurrent u n (edgeSrc e) := IsRecurrentFactor.init he

/-- …and so is its target. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem recurrent_edgeTgt {u : ℕ → α} {n : ℕ} {e : Fin (n + 1) → α} (he : Recurrent u (n + 1) e) :
    Recurrent u n (edgeTgt e) := IsRecurrentFactor.tail he

variable [Finite α]

/-! ## Strong connectivity -/

/-- **[M1M2, Prop. 3.2]: the reduced Rauzy graph is strongly connected.**  Every recurrent
length-`n` block reaches every other along edges of `G'_n(u)`.

Note what is **not** assumed: `u` is an arbitrary infinite word over a finite alphabet.  The proof
(in `ForMathlib`) is the two-line argument of the note — `a` occurs beyond the horizon `s_{n+1}`,
`b` occurs later still, and the stretch of `u` between the two occurrences is the walk.

This replaces the former `BB47.exists_walk`, which exhibited the walk as an explicit window
`[i, j]` of `u`; the window was never used for anything but this reachability statement. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem reach_recFactorSet {u : ℕ → α} {n : ℕ} {a b : Fin n → α}
    (ha : Recurrent u n a) (hb : Recurrent u n b) : Reach (recFactorSet u) n a b :=
  reach_recurrentLanguage u n ha hb

/-! ## Degrees -/

/-- [M1M2, Prop. 3.3]: every vertex of `G'_n(u)` has **out-degree at least one**. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_outEdge {u : ℕ → α} {n : ℕ} {a : Fin n → α} (ha : Recurrent u n a) :
    ∃ e : Fin (n + 1) → α, Recurrent u (n + 1) e ∧ edgeSrc e = a :=
  IsRecurrentFactor.extendRight ha

/-- [M1M2, Prop. 3.3]: every vertex of `G'_n(u)` has **in-degree at least one**. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_inEdge {u : ℕ → α} {n : ℕ} {a : Fin n → α} (ha : Recurrent u n a) :
    ∃ e : Fin (n + 1) → α, Recurrent u (n + 1) e ∧ edgeTgt e = a :=
  IsRecurrentFactor.extendLeft ha

/-! ## The exclusion engine -/

/-- **No proper out-closed set of vertices** (positive form).  If a set `S` of length-`n` blocks
is closed under recurrent out-edges and contains one recurrent block, it contains every recurrent
block.

This is the whole content of [M3, Prop. 5.2] — the exclusion of the Coven–Hedlund non-Sturmian
branch.  There, `S` is the set of length-`N` blocks of the right periodic tail of a bisequence of
[CH73, Thm. 4.12]: the disjointness of the two tails' languages makes `S` proper, the gluing block
occurs exactly once and so blocks no escape, and closure under out-edges is immediate.  Everything
else in that proof is bookkeeping in `[CH73]`'s normal form. -/
@[category research solved, AMS 11 37 68, ref "CH73" "BKK26", group "bugeaud_10_47"]
theorem mem_of_outClosed {u : ℕ → α} {n : ℕ} {S : Set (Fin n → α)}
    (hclosed : ∀ e : Fin (n + 1) → α, Recurrent u (n + 1) e → edgeSrc e ∈ S → edgeTgt e ∈ S)
    {a : Fin n → α} (ha : Recurrent u n a) (haS : a ∈ S)
    {b : Fin n → α} (hb : Recurrent u n b) : b ∈ S :=
  mem_of_reach hclosed (reach_recFactorSet ha hb) haS

/-- **[M3, Prop. 5.2], contrapositive form.**  The reduced Rauzy graph of an `ω`-limit set has no
**proper non-empty** set of vertices closed under out-edges.  A subshift whose Rauzy graph does
have one — such as the Coven–Hedlund non-Sturmian bisequences — therefore never arises as the
`ω`-limit set of a one-sided word. -/
@[category research solved, AMS 11 37 68, ref "CH73" "BKK26", group "bugeaud_10_47"]
theorem not_properOutClosed {u : ℕ → α} {n : ℕ} {S : Set (Fin n → α)}
    (hclosed : ∀ e : Fin (n + 1) → α, Recurrent u (n + 1) e → edgeSrc e ∈ S → edgeTgt e ∈ S)
    (hne : ∃ a ∈ recFactorSet u n, a ∈ S) (hproper : ∃ b ∈ recFactorSet u n, b ∉ S) : False := by
  obtain ⟨a, ha, haS⟩ := hne
  obtain ⟨b, hb, hbS⟩ := hproper
  exact hbS (mem_of_outClosed hclosed ha haS hb)

end BB47
