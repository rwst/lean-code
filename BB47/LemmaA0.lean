/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Basic

/-!
# The repetition function `r(n, w)` and Lemma A0

This is §4 of `BB47/M1M2.tex`, milestone M1 of `plans/plan-1047.html`: **the whole combinatorial
content** of Theorems A and A′ of that note, and the declaration the plan names as the
formalization target of milestone M9.

Following Bugeaud–Kim [BK19], `r(n, w)` is the length of the shortest prefix of `w` containing two
distinct (possibly overlapping) occurrences of one and the same block of length `n`.  Lemma A0
says

  `r(n, w) ≤ s_n + n + p_∞(n, w)`,

with `s_n` the non-recurrent prefix and `p_∞` the eventual block complexity.  The proof is one
application of the pigeonhole principle to the `p_∞(n) + 1` blocks read at the first
`p_∞(n) + 1` positions of the tail `z_n`: they all lie in the recurrent language, which has only
`p_∞(n)` elements.

What is **absent** from the hypothesis is the point.  There is no classification of
low-complexity subshifts, no Sturmian standard word, no critical exponent, no syndeticity, and no
assumption on `w` at all beyond the finiteness of the alphabet — which already makes `p_∞(n, w)`
finite.  Everything else in Theorems A/A′ is the quoted Diophantine input (`BB47/Cited.lean`).

## Main results

* `BB47.HasRepetitionBy`, `BB47.repLen` — the repetition function `r(n, ·)` of [BK19, §10].
* `BB47.lemma_A0` — `r(n, w) ≤ s_n + n + p_∞(n, w)`.
* `BB47.hasRepetitionBy_repLen` — over a finite alphabet the infimum is attained, so `repLen` is
  a genuine minimum and not a junk value.
* `BB47.repLen_le_pComplexity_add` — `r(n, w) ≤ p(n, w) + n`, the same pigeonhole run at the
  origin ([BK26, Lem. 2.2]).
* `BB47.pComplexity_le_horizon_add_pInf` — `p(n, w) ≤ s_n + p_∞(n, w)`: the horizon splits the
  factor set.
* `BB47.pComplexity_add_le_lemma_A0_bound` — hence Lemma A0 is a consequence of the previous two
  and is **never sharper** than [BK26, Lem. 2.2].  See the caveat below.

## Lemma A0 is not the sharp form, and Theorems A/A′ do not need `r` at all

Added 2026-09-13 after the forward-citation sweep of [BK19] (`BB47/L0.md` §L0(ii-bis)).  The two
extra lemmas above give

  `r(n, w) ≤ p(n, w) + n ≤ s_n + n + p_∞(n, w)`,

so Lemma A0's bound is dominated by the published [BK26, Lem. 2.2].  What Lemma A0 buys is not a
better bound but a better *hypothesis*: its right-hand side is controlled by the eventual
complexity, which is what Theorem W constrains, while `p(n, w)` is not.

The second inequality has a further, deflationary consequence worth stating plainly in the paper:
`p(n, w) ≤ s_n + p_∞(n, w)` sends the hypothesis of Theorem A directly into
`lim p(n, ξ, b)/n = +∞` for algebraic irrationals ([AB07]) and that of Theorem A′ directly into
the `(log n)^η` refinement ([BE08]).  Neither theorem needs the repetition function, [BK19,
Thm. 10.4], or this file.  The `r`-route is kept because it is the one the note writes up and
because `repLen` is the object the sliver of `BB47/Sliver.lean` is phrased against.

## Indexing

Positions are `0`-based (see `BB47/Basic.lean`).  A repetition *within the prefix of length `m`*
means two positions `i < j` with the same length-`n` block and `j + n ≤ m`, i.e. the later
occurrence ends inside the prefix.  With the `1`-based convention of [BK19] and of
`BB47/M1M2.tex` this is the same number `m`.

## References

* [BK19] Y. Bugeaud, D. H. Kim, *A new complexity function, repetitions in Sturmian words, and
  irrationality exponents of Sturmian numbers*, Trans. Amer. Math. Soc. **371** (2019),
  3281–3308 (arXiv:1510.00279) — the function `r(n, x)`, `rep(x) = liminf r(n,x)/n`, Lem. 10.3
  and Thm. 10.4.
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — §2.2 (`s_n`).  Note that the
  symbol `r(n, ·)` there denotes a quantity smaller by `n`.
* [BK26] Y. Bugeaud, D. H. Kim, *On the `b`-ary expansion of a real number whose irrationality
  exponent is close to 2*, arXiv:2510.02059v2 (rev. 2026-04-20), on disk as
  `BB47/BugeaudKim2026-mu2324.pdf` — Lem. 2.2 (`p(n,x) ≥ r(n,x) - n`), Thm. 2.1, Prop. 1.6.
  **Not** [BKK26], which is a different October-2025 posting.
* [AB07] B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in
  integer bases*, Ann. of Math. **165** (2007), 547–565 — `lim p(n, ξ, b)/n = +∞`.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*,
  Acta Arith. **133** (2008), 221–250, Thm. 2.1.
* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — §4, rewritten 2026-09-13: Lem. 4.1 is now
  the horizon bound `p(n,w) ≤ s_n + p_∞(n,w)` and Lem. 4.2 is Lemma A0.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-- The prefix of `w` of length `m` contains two distinct occurrences of one and the same
length-`n` block. -/
@[category API, AMS 11 37 68, ref "BK19", group "bugeaud_10_47"]
def HasRepetitionBy (u : ℕ → α) (n m : ℕ) : Prop :=
  ∃ i j : ℕ, i < j ∧ j + n ≤ m ∧ factor u n i = factor u n j

/-- **The repetition function `r(n, w)` of [BK19].**  The length of the shortest prefix of `w`
containing two distinct (possibly overlapping) occurrences of the same length-`n` block. -/
@[category API, AMS 11 37 68, ref "BK19", group "bugeaud_10_47"]
noncomputable def repLen (u : ℕ → α) (n : ℕ) : ℕ := sInf {m | HasRepetitionBy u n m}

@[category API, AMS 11 37 68, ref "BK19", group "bugeaud_10_47"]
theorem repLen_le {u : ℕ → α} {n m : ℕ} (h : HasRepetitionBy u n m) : repLen u n ≤ m :=
  Nat.sInf_le h

/-- Having a repetition within a prefix is inherited by longer prefixes. -/
@[category API, AMS 11 37 68, ref "BK19", group "bugeaud_10_47"]
theorem HasRepetitionBy.mono {u : ℕ → α} {n m m' : ℕ} (h : HasRepetitionBy u n m) (hm : m ≤ m') :
    HasRepetitionBy u n m' := by
  obtain ⟨i, j, hij, hjm, heq⟩ := h
  exact ⟨i, j, hij, by omega, heq⟩

/-- The pigeonhole itself: a repetition of a length-`n` block already occurs inside the prefix of
length `s_n + n + p_∞(n, w)`.

Read the `p_∞(n) + 1` length-`n` blocks at the positions `s_n, s_n + 1, …, s_n + p_∞(n)`.  All of
them are recurrent, and there are only `p_∞(n)` recurrent blocks, so two coincide; the later of
the two ends at position `≤ s_n + p_∞(n) + n`. -/
@[category API, AMS 11 37 68, ref "BK19" "BKK26", group "bugeaud_10_47"]
theorem hasRepetitionBy_horizon_add [Finite α] (u : ℕ → α) (n : ℕ) :
    HasRepetitionBy u n (horizon u n + n + pInf u n) := by
  classical
  have hfin : (recFactorSet u n).Finite := Set.toFinite _
  set h := horizon u n with hh
  set K := pInf u n with hKdef
  have hcardK : hfin.toFinset.card = K := by
    rw [hKdef, pInf, Set.ncard_eq_toFinset_card _ hfin]
  have hmaps : ∀ t ∈ Finset.range (K + 1), factor u n (h + t) ∈ hfin.toFinset := by
    intro t _
    rw [Set.Finite.mem_toFinset]
    exact recurrent_of_horizon_le (by omega)
  have hlt : hfin.toFinset.card < (Finset.range (K + 1)).card := by
    rw [hcardK, Finset.card_range]; omega
  obtain ⟨t, ht, t', ht', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [Finset.mem_range] at ht ht'
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · exact ⟨h + t, h + t', by omega, by omega, heq⟩
  · exact ⟨h + t', h + t, by omega, by omega, heq.symm⟩

/-- **Lemma A0** [M1M2, Lem. 4.2]: `r(n, w) ≤ s_n + n + p_∞(n, w)`.

This single inequality is the entire combinatorial content of Theorems A and A′: it converts a
hypothesis on the *eventual* complexity and the non-recurrent prefix into a hypothesis on the
repetition function, which is what the Diophantine criterion of [BK19, Thm. 10.4] consumes. -/
@[category research solved, AMS 11 37 68, ref "BK19" "BKK26", group "bugeaud_10_47"]
theorem lemma_A0 [Finite α] (u : ℕ → α) (n : ℕ) :
    repLen u n ≤ horizon u n + n + pInf u n :=
  repLen_le (hasRepetitionBy_horizon_add u n)

/-- Over a finite alphabet the infimum defining `r(n, w)` is attained, so `repLen` is a genuine
minimum: there really is a repeated length-`n` block inside the prefix of length `r(n, w)`. -/
@[category API, AMS 11 37 68, ref "BK19", group "bugeaud_10_47"]
theorem hasRepetitionBy_repLen [Finite α] (u : ℕ → α) (n : ℕ) :
    HasRepetitionBy u n (repLen u n) := by
  have hne : {m | HasRepetitionBy u n m}.Nonempty :=
    ⟨horizon u n + n + pInf u n, hasRepetitionBy_horizon_add u n⟩
  exact Nat.sInf_mem hne

/-- **[BK26, Lem. 2.2]**: `p(n, w) ≥ r(n, w) - n`, stated without truncated subtraction as
`r(n, w) ≤ p(n, w) + n`.

The same pigeonhole as `hasRepetitionBy_horizon_add`, run at the **origin** instead of at the
horizon: by minimality of `r(n, w)` the `r(n, w) - n` blocks read at the positions
`0, 1, …, r(n, w) - n - 1` are pairwise distinct — any coincidence would exhibit a repetition
inside a strictly shorter prefix — and they all lie in the factor set, which has `p(n, w)`
elements.

Bugeaud and Kim use it in the opposite direction, to convert a *lower* bound on the repetition
function into a lower bound on the complexity. -/
@[category research solved, AMS 11 37 68, ref "BK26" "BK19", group "bugeaud_10_47"]
theorem repLen_le_pComplexity_add [Finite α] (u : ℕ → α) (n : ℕ) :
    repLen u n ≤ pComplexity u n + n := by
  classical
  have hfin : (factorSet u n).Finite := Set.toFinite _
  have hcard : hfin.toFinset.card = pComplexity u n := by
    rw [pComplexity, Set.ncard_eq_toFinset_card _ hfin]
  have hmaps : ∀ i ∈ Finset.range (repLen u n - n), factor u n i ∈ hfin.toFinset := by
    intro i _
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_range_self i
  have hinj : Set.InjOn (factor u n) ↑(Finset.range (repLen u n - n)) := by
    intro i hi j hj heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := repLen_le (u := u) (n := n) (m := j + n) ⟨i, j, h, le_rfl, heq⟩
      omega
    · have := repLen_le (u := u) (n := n) (m := i + n) ⟨j, i, h, le_rfl, heq.symm⟩
      omega
  have hle := Finset.card_le_card_of_injOn (factor u n) hmaps hinj
  rw [Finset.card_range, hcard] at hle
  omega

/-- **The horizon splits the factor set**: `p(n, w) ≤ s_n + p_∞(n, w)`.

Every block read at a position `≥ s_n` is recurrent, so the factor set is covered by the
`≤ s_n` blocks read before the horizon together with the `p_∞(n, w)` recurrent ones.

This is the comparison that relates `BB47.lemma_A0` to `BB47.repLen_le_pComplexity_add`; see
`BB47.pComplexity_add_le_lemma_A0_bound`. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem pComplexity_le_horizon_add_pInf [Finite α] (u : ℕ → α) (n : ℕ) :
    pComplexity u n ≤ horizon u n + pInf u n := by
  classical
  have hfs : (factorSet u n).Finite := Set.toFinite _
  have hrec : (recFactorSet u n).Finite := Set.toFinite _
  have h1 : pComplexity u n = hfs.toFinset.card := by
    rw [pComplexity, Set.ncard_eq_toFinset_card _ hfs]
  have h2 : pInf u n = hrec.toFinset.card := by
    rw [pInf, Set.ncard_eq_toFinset_card _ hrec]
  have key : hfs.toFinset ⊆
      (Finset.range (horizon u n)).image (factor u n) ∪ hrec.toFinset := by
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    obtain ⟨i, rfl⟩ := hv
    rw [Finset.mem_union]
    by_cases h : i < horizon u n
    · exact Or.inl (Finset.mem_image.2 ⟨i, Finset.mem_range.2 h, rfl⟩)
    · refine Or.inr ?_
      rw [Set.Finite.mem_toFinset]
      exact recurrent_of_horizon_le (by omega)
  have himg : ((Finset.range (horizon u n)).image (factor u n)).card ≤ horizon u n := by
    have := Finset.card_image_le (s := Finset.range (horizon u n)) (f := factor u n)
    rwa [Finset.card_range] at this
  have hunion := Finset.card_union_le
    ((Finset.range (horizon u n)).image (factor u n)) hrec.toFinset
  have := Finset.card_le_card key
  omega

/-- **[BK26, Lem. 2.2] is never weaker than Lemma A0**: its bound `p(n, w) + n` is at most
Lemma A0's bound `s_n + n + p_∞(n, w)`.

So `BB47.lemma_A0` is a formal consequence of `BB47.repLen_le_pComplexity_add` together with
`BB47.pComplexity_le_horizon_add_pInf`, and never sharper.  What Lemma A0 buys is not a better
bound but a better *hypothesis*: its right-hand side is controlled by the eventual complexity,
which is what Theorem W constrains, whereas `p(n, w)` is not.

The same comparison shows that Theorems A and A′ do not in fact need the repetition function at
all — `pComplexity_le_horizon_add_pInf` feeds their hypotheses straight into the complexity
theorems of [AB07] and [BE08]. See `BB47/L0.md` §L0(ii-bis). -/
@[category research solved, AMS 11 37 68, ref "BK26" "BKK26", group "bugeaud_10_47"]
theorem pComplexity_add_le_lemma_A0_bound [Finite α] (u : ℕ → α) (n : ℕ) :
    pComplexity u n + n ≤ horizon u n + n + pInf u n := by
  have := pComplexity_le_horizon_add_pInf u n
  omega

end BB47
