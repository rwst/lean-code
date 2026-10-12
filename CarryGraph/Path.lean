/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Walks, words and paths of a carry graph ([LM95] §1.3, §2.2, §3.1; [BJG09] §1.4)

A walk of a carry graph is read in two ways: as a vertex sequence along the underlying digraph
(`CarryGraph.IsWalk`), or as a word of labels (`CarryGraph.Reads v w u`: reading `w` from `v`
can end at `u`).  Infinite paths carry both a vertex and a label sequence
(`CarryGraph.IsIPath`).

## Contents

* `IsWalk`, `IsIPath`, `Reads`, `IsWord` (the label language from a vertex), `ends` (the set of
  end vertices after reading a word — the state of the subset construction, ch. 5).
* `words v n` (the words of length `n` from `v`), `npaths v n` (the number of labelled paths),
  `card_words_le_npaths`, and equality for right-resolving graphs, `card_words_eq_npaths`
  ([LM95] §3.3).
* `Functional` (at most one arc out of each vertex) and `RightResolving`.
* `HasWalk` and **Kőnig's lemma** `exists_ipath_of_forall_hasWalk`: in a carry graph with a
  finite label set, a vertex with walks of every length starts an infinite path.  The vertex set
  may be infinite.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
-/

namespace CarryGraph

variable {V A : Type*} (X : CarryGraph V A)

/-! ### Walks and infinite paths -/

/-- `g` is a walk of length `n` of the underlying digraph: `g 0 → g 1 → ⋯ → g n`. -/
def IsWalk (g : ℕ → V) (n : ℕ) : Prop := ∀ i < n, X.under (g i) (g (i + 1))

/-- `(s, ℓ)` is an infinite labelled path: `s 0 →[ℓ 0] s 1 →[ℓ 1] ⋯`. -/
def IsIPath (s : ℕ → V) (ℓ : ℕ → A) : Prop := ∀ n, X.Adj (s n) (ℓ n) (s (n + 1))

/-- Reading the word `w` from `v` can end at `u`. -/
def Reads : V → List A → V → Prop
  | v, [], u => u = v
  | v, a :: w, u => ∃ t ∈ X.succ v a, Reads t w u

/-- `w` labels some path from `v`: the **label language** from `v`. -/
def IsWord (v : V) (w : List A) : Prop := ∃ u, X.Reads v w u

variable {X}

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem reads_nil {v u : V} : X.Reads v [] u ↔ u = v := Iff.rfl

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem reads_cons {v u : V} {a : A} {w : List A} :
    X.Reads v (a :: w) u ↔ ∃ t, X.Adj v a t ∧ X.Reads t w u := Iff.rfl

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem reads_append : ∀ {v u : V} {w₁ w₂ : List A},
    X.Reads v (w₁ ++ w₂) u ↔ ∃ t, X.Reads v w₁ t ∧ X.Reads t w₂ u
  | v, u, [], w₂ => by simp [reads_nil]
  | v, u, a :: w₁, w₂ => by
    simp only [List.cons_append, reads_cons, reads_append]
    constructor
    · rintro ⟨t, ht, s, h1, h2⟩
      exact ⟨s, ⟨t, ht, h1⟩, h2⟩
    · rintro ⟨s, ⟨t, ht, h1⟩, h2⟩
      exact ⟨t, ht, s, h1, h2⟩

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem isWord_nil (v : V) : X.IsWord v [] := ⟨v, rfl⟩

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem isWord_cons {v : V} {a : A} {w : List A} :
    X.IsWord v (a :: w) ↔ ∃ t, X.Adj v a t ∧ X.IsWord t w := by
  simp only [IsWord, reads_cons]
  exact ⟨fun ⟨u, t, ht, h⟩ => ⟨t, ht, u, h⟩, fun ⟨t, ht, u, h⟩ => ⟨u, t, ht, h⟩⟩

/-- The label language is prefix-closed (factorial from the left). -/
@[category textbook, AMS 05, ref "LM95", group "carry_path"]
theorem IsWord.of_append {v : V} {w₁ w₂ : List A} (h : X.IsWord v (w₁ ++ w₂)) :
    X.IsWord v w₁ :=
  let ⟨_, h⟩ := h
  let ⟨t, h1, _⟩ := reads_append.1 h
  ⟨t, h1⟩

/-- `Reads` is decidable (bounded search through the finite successor sets). -/
def decReads [DecidableEq V] : ∀ (v : V) (w : List A) (u : V), Decidable (X.Reads v w u)
  | v, [], u => inferInstanceAs (Decidable (u = v))
  | v, a :: w, u =>
    haveI := fun t => decReads t w u
    inferInstanceAs (Decidable (∃ t ∈ X.succ v a, X.Reads t w u))

instance [DecidableEq V] (v : V) (w : List A) (u : V) : Decidable (X.Reads v w u) :=
  decReads v w u

/-- `IsWord` is decidable. -/
def decIsWord [DecidableEq V] : ∀ (v : V) (w : List A), Decidable (X.IsWord v w)
  | v, [] => isTrue (isWord_nil v)
  | v, a :: w =>
    haveI := fun t => decIsWord t w
    decidable_of_iff (∃ t ∈ X.succ v a, X.IsWord t w) (by rw [isWord_cons]; rfl)

instance [DecidableEq V] (v : V) (w : List A) : Decidable (X.IsWord v w) := decIsWord v w

/-! ### The end set of a word -/

variable (X) in
/-- The vertices reachable from `S` by reading `w`. -/
def ends [DecidableEq V] : Finset V → List A → Finset V
  | S, [] => S
  | S, a :: w => ends (S.biUnion fun v => X.succ v a) w

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem mem_ends [DecidableEq V] : ∀ {S : Finset V} {w : List A} {u : V},
    u ∈ X.ends S w ↔ ∃ v ∈ S, X.Reads v w u
  | S, [], u => by simp [ends, reads_nil]
  | S, a :: w, u => by
    simp only [ends, mem_ends, Finset.mem_biUnion, reads_cons, Adj]
    constructor
    · rintro ⟨t, ⟨v, hv, ht⟩, h⟩
      exact ⟨v, hv, t, ht, h⟩
    · rintro ⟨v, hv, t, ht, h⟩
      exact ⟨t, ⟨v, hv, ht⟩, h⟩

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem isWord_iff_ends_nonempty [DecidableEq V] {v : V} {w : List A} :
    X.IsWord v w ↔ (X.ends {v} w).Nonempty := by
  simp [Finset.Nonempty, mem_ends, IsWord]

/-! ### Words and path counts of a given length -/

variable (X) in
/-- The words of length `n` read from `v`. -/
def words [Fintype A] [DecidableEq A] : V → ℕ → Finset (List A)
  | _, 0 => {[]}
  | v, n + 1 => Finset.univ.biUnion fun a =>
      (X.succ v a).biUnion fun u => (words u n).image (a :: ·)

variable (X) in
/-- The number of labelled paths of length `n` from `v` (arcs counted with their labels). -/
def npaths [Fintype A] : V → ℕ → ℕ
  | _, 0 => 1
  | v, n + 1 => ∑ a, ∑ u ∈ X.succ v a, npaths u n

section count

variable [Fintype A]

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem npaths_zero (v : V) : X.npaths v 0 = 1 := rfl

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem npaths_succ (v : V) (n : ℕ) : X.npaths v (n + 1) = ∑ a, ∑ u ∈ X.succ v a, X.npaths u n :=
  rfl

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem mem_words [DecidableEq A] : ∀ {v : V} {n : ℕ} {w : List A},
    w ∈ X.words v n ↔ w.length = n ∧ X.IsWord v w
  | v, 0, w => by
    simp only [words, Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, isWord_nil v⟩
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | v, n + 1, w => by
    simp only [words, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, mem_words]
    constructor
    · rintro ⟨a, u, hu, w', ⟨hl, hw'⟩, rfl⟩
      exact ⟨by simp [hl], isWord_cons.2 ⟨u, hu, hw'⟩⟩
    · rintro ⟨hl, hw⟩
      cases w with
      | nil => simp at hl
      | cons a w' =>
        obtain ⟨u, hu, hw'⟩ := isWord_cons.1 hw
        exact ⟨a, u, hu, w', ⟨by simpa using hl, hw'⟩, rfl⟩

/-- There are at most as many words as labelled paths. -/
@[category textbook, AMS 05, ref "LM95", group "carry_path"]
theorem card_words_le_npaths [DecidableEq A] : ∀ (v : V) (n : ℕ),
    (X.words v n).card ≤ X.npaths v n
  | v, 0 => by simp [words, npaths]
  | v, n + 1 => by
    rw [words, npaths_succ]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ => ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ => ?_)
    exact Finset.card_image_le.trans (card_words_le_npaths u n)

variable (X) in
/-- **Right-resolving** ([LM95] Def. 3.3.1): from each vertex, each label leads to at most one
vertex. -/
def RightResolving : Prop := ∀ v a, (X.succ v a).card ≤ 1

/-- In a right-resolving carry graph, distinct labelled paths from a vertex read distinct words
([LM95] Prop. 3.3.9, counting form). -/
@[category textbook, AMS 05, ref "LM95", group "carry_path"]
theorem card_words_eq_npaths [DecidableEq A] (h : X.RightResolving) : ∀ (v : V) (n : ℕ),
    (X.words v n).card = X.npaths v n
  | v, 0 => by simp [words, npaths]
  | v, n + 1 => by
    classical
    rw [words, npaths_succ, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.card_image_of_injective _ (List.cons_injective), card_words_eq_npaths h u n]
      · intro x hx y hy hxy
        exact absurd (Finset.card_le_one.1 (h v a) x hx y hy) hxy
    · intro a _ b _ hab
      refine Finset.disjoint_left.2 fun w hw hw' => hab ?_
      simp only [Finset.mem_biUnion, Finset.mem_image] at hw hw'
      obtain ⟨_, _, _, _, rfl⟩ := hw
      obtain ⟨_, _, _, _, h'⟩ := hw'
      exact (List.cons_eq_cons.1 h').1.symm

end count

variable (X) in
/-- **Functional**: at most one arc leaves each vertex. -/
def Functional : Prop := ∀ v a b u w, X.Adj v a u → X.Adj v b w → a = b ∧ u = w

@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem Functional.rightResolving (h : X.Functional) : X.RightResolving :=
  fun v a => Finset.card_le_one.2 fun _ hu _ hw => (h v a a _ _ hu hw).2

/-- A functional carry graph has at most one path of each length from each vertex. -/
@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem Functional.npaths_le_one [Fintype A] (h : X.Functional) : ∀ (v : V) (n : ℕ),
    X.npaths v n ≤ 1
  | v, 0 => le_rfl
  | v, n + 1 => by
    classical
    rw [npaths_succ]
    by_cases he : ∃ a u, X.Adj v a u
    · obtain ⟨a, u, hu⟩ := he
      have hs : ∀ b, b ≠ a → X.succ v b = ∅ := fun b hb =>
        Finset.eq_empty_of_forall_notMem fun w hw => hb (h v b a w u hw hu).1
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [hs b hb, Finset.sum_empty])
        (by simp)]
      have : X.succ v a = {u} := Finset.eq_singleton_iff_unique_mem.2
        ⟨hu, fun w hw => (h v a a w u hw hu).2⟩
      rw [this, Finset.sum_singleton]
      exact Functional.npaths_le_one h u n
    · push Not at he
      simp [Finset.sum_eq_zero, fun a => Finset.eq_empty_of_forall_notMem (he a)]

/-- In a functional carry graph an infinite labelled path is determined by its first vertex. -/
@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem Functional.iPath_eq (h : X.Functional) {s s' : ℕ → V} {ℓ ℓ' : ℕ → A}
    (hs : ∀ n, X.Adj (s n) (ℓ n) (s (n + 1))) (hs' : ∀ n, X.Adj (s' n) (ℓ' n) (s' (n + 1)))
    (h0 : s 0 = s' 0) : s = s' ∧ ℓ = ℓ' := by
  have key : ∀ n, s n = s' n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact (h _ _ _ _ _ (hs n) (by rw [ih]; exact hs' n)).2
  exact ⟨funext key, funext fun n => (h _ _ _ _ _ (hs n) (by rw [key n]; exact hs' n)).1⟩

/-! ### Kőnig's lemma -/

section konig

variable [Fintype A] [DecidableEq V]

variable (X) in
/-- Some walk of length `n` starts at `v`. -/
def HasWalk : V → ℕ → Prop
  | _, 0 => True
  | v, n + 1 => ∃ w ∈ X.out v, HasWalk w n

@[category API, AMS 05, ref "BJG09", group "carry_path"]
theorem HasWalk.mono : ∀ {v : V} {m n : ℕ}, m ≤ n → X.HasWalk v n → X.HasWalk v m
  | _, 0, _, _, _ => trivial
  | _, _ + 1, 0, h, _ => absurd h (by omega)
  | _, _ + 1, _ + 1, h, ⟨w, hw, h'⟩ => ⟨w, hw, HasWalk.mono (by omega) h'⟩

@[category API, AMS 05, ref "BJG09", group "carry_path"]
theorem hasWalk_iff : ∀ {v : V} {n : ℕ}, X.HasWalk v n ↔ ∃ g, g 0 = v ∧ X.IsWalk g n
  | v, 0 => ⟨fun _ => ⟨fun _ => v, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ => trivial⟩
  | v, n + 1 => by
    constructor
    · rintro ⟨w, hw, h⟩
      obtain ⟨g, hg0, hg⟩ := hasWalk_iff.1 h
      refine ⟨fun i => if i = 0 then v else g (i - 1), rfl, fun i hi => ?_⟩
      rcases i with _ | i
      · simpa [hg0] using mem_out.1 hw
      · simpa using hg i (by omega)
    · rintro ⟨g, rfl, hg⟩
      exact ⟨g 1, mem_out.2 (hg 0 (by omega)),
        hasWalk_iff.2 ⟨fun i => g (i + 1), rfl, fun i hi => hg (i + 1) (by omega)⟩⟩

@[category API, AMS 05, ref "BJG09", group "carry_path"]
theorem hasWalk_iff_exists_word : ∀ {v : V} {n : ℕ},
    X.HasWalk v n ↔ ∃ w : List A, w.length = n ∧ X.IsWord v w
  | v, 0 => ⟨fun _ => ⟨[], rfl, isWord_nil v⟩, fun _ => trivial⟩
  | v, n + 1 => by
    simp only [HasWalk, mem_out, hasWalk_iff_exists_word]
    constructor
    · rintro ⟨u, ⟨a, ha⟩, w, hl, hw⟩
      exact ⟨a :: w, by simp [hl], isWord_cons.2 ⟨u, ha, hw⟩⟩
    · rintro ⟨w, hl, hw⟩
      cases w with
      | nil => simp at hl
      | cons a w =>
        obtain ⟨u, ha, hw⟩ := isWord_cons.1 hw
        exact ⟨u, ⟨a, ha⟩, w, by simpa using hl, hw⟩

/-- The pigeonhole step: a vertex with walks of every length has a successor with walks of
every length. -/
@[category API, AMS 05, ref "BJG09", group "carry_path"]
theorem exists_succ_forall_hasWalk {v : V} (h : ∀ n, X.HasWalk v n) :
    ∃ w ∈ X.out v, ∀ n, X.HasWalk w n := by
  by_contra! hc
  choose N hN using hc
  obtain ⟨w, hw, hw'⟩ := h ((X.out v).attach.sup (fun w => N w.1 w.2) + 1)
  exact hN w hw (hw'.mono (Finset.le_sup (f := fun w : X.out v => N w.1 w.2)
    (Finset.mem_attach _ ⟨w, hw⟩)))

/-- **Kőnig's lemma** ([BJG09] §1.4; Mathlib's `Order/KonigLemma` in graph form): in a carry
graph over a finite alphabet, a vertex with walks of every length starts an infinite walk.  The
vertex set may be infinite. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_path"]
theorem exists_walk_of_forall_hasWalk {v : V} (h : ∀ n, X.HasWalk v n) :
    ∃ s : ℕ → V, s 0 = v ∧ ∀ n, X.under (s n) (s (n + 1)) := by
  let G := {u : V // ∀ n, X.HasWalk u n}
  have step : ∀ u : G, ∃ w : G, X.under u.1 w.1 := fun u =>
    let ⟨w, hw, hg⟩ := exists_succ_forall_hasWalk u.2
    ⟨⟨w, hg⟩, mem_out.1 hw⟩
  choose nxt hnxt using step
  let s : ℕ → G := fun n => Nat.rec ⟨v, h⟩ (fun _ u => nxt u) n
  exact ⟨fun n => (s n).1, rfl, fun n => hnxt (s n)⟩

/-- **Kőnig's lemma, labelled form**: words of every length from `v` give an infinite labelled
path from `v`. -/
@[category textbook, AMS 05, ref "BJG09" "LM95", group "carry_path"]
theorem exists_iPath_of_forall_isWord {v : V}
    (h : ∀ n, ∃ w : List A, w.length = n ∧ X.IsWord v w) :
    ∃ s ℓ, s 0 = v ∧ X.IsIPath s ℓ := by
  obtain ⟨s, hs0, hs⟩ := exists_walk_of_forall_hasWalk fun n => hasWalk_iff_exists_word.2 (h n)
  choose ℓ hℓ using hs
  exact ⟨s, ℓ, hs0, hℓ⟩

end konig

/-- The labels of an infinite path read a word of every length. -/
@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem IsIPath.reads {s : ℕ → V} {ℓ : ℕ → A} (h : X.IsIPath s ℓ) :
    ∀ (m n : ℕ), X.Reads (s m) ((List.range n).map fun i => ℓ (m + i)) (s (m + n))
  | m, 0 => by simp [reads_nil]
  | m, n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, reads_cons]
    refine ⟨s (m + 1), by simpa using h m, ?_⟩
    have := IsIPath.reads h (m + 1) n
    simp only [Function.comp_def, Nat.succ_eq_add_one] at this ⊢
    convert this using 2
    · funext i; congr 1; omega
    · omega

/-- An infinite path is a walk of every length. -/
@[category API, AMS 05, ref "LM95", group "carry_path"]
theorem IsIPath.isWalk {s : ℕ → V} {ℓ : ℕ → A} (h : X.IsIPath s ℓ) (n : ℕ) : X.IsWalk s n :=
  fun i _ => ⟨ℓ i, h i⟩

end CarryGraph
