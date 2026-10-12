/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Language
import ForMathlib.Dynamics.SymbolicDynamics.Duality
import ForMathlib.Dynamics.SymbolicDynamics.Rauzy

/-!
# The two-sided label shift and Rauzy graphs ([LM95] §§2.2, 3.1)

The one-sided theory of `Language.lean` and `Follower.lean` is about words read from a root. The
two-sided **label shift** of a carry graph is the subshift of `A^ℤ` whose words are the words read
on walks inside an essential set `S`, typically the core.  It is built with ForMathlib's
language–subshift duality:

* `blockWords X S n` — the words of length `n` read on walks inside `S`;
* `isLanguage_blockWords` — for a non-empty essential `S` this family is factorial and
  extendable (`SymbolicDynamics.FullShift.IsLanguage`);
* `labelShift X S := ofLanguage (blockWords X S)`, with `language_labelShift`: its language is
  exactly `blockWords X S` (finite alphabet, discrete topology);
* `mem_labelShift_of_path` — the label sequence of every bi-infinite path inside `S` lies in the
  shift.  For `S = core` the bi-infinite paths are automatically inside `S`
  (`mem_core_of_biPath`).

Taking `S = core` gives the sofic shift presented by `X` [LM95, Def. 3.1.3].  With `A = arcs` and
each arc labelled by itself, it is the edge shift [LM95, Def. 2.2.5].

The **Rauzy graph** `rauzy L n` of a factorial language `L` is the carry graph on words of length
`n`, with an arc `u →a v` when `u a = b v` is a word of length `n + 1` (`under_rauzy`: its
underlying relation is ForMathlib's `Step L n`).

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

open SymbolicDynamics.FullShift

variable {V A : Type*} {X : CarryGraph V A}

/-! ### Words read inside a set -/

section blocks

variable (S : Set V) [DecidablePred (· ∈ S)]

variable (X) in
/-- The words of length `n` read on walks inside `S`. -/
def blockWords (n : ℕ) : Set (Fin n → A) :=
  {w | ∃ v ∈ S, (X.restrict S).IsWord v (List.ofFn w)}

variable {S}

@[category API, AMS 05 37, group "carry_shift"]
theorem reads_restrict_mem : ∀ {v u : V} {w : List A}, (X.restrict S).Reads v w u → v ∈ S → u ∈ S
  | v, u, [], h, hv => by rw [reads_nil] at h; rw [h]; exact hv
  | v, u, a :: w, h, _ => by
    obtain ⟨t, ht, h⟩ := reads_cons.1 h
    exact reads_restrict_mem h (adj_restrict.1 ht).2.2

/-- **The words read inside a non-empty essential set form a factorial extendable language.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_shift"]
theorem isLanguage_blockWords (hS : X.Essential S) (hne : S.Nonempty) :
    IsLanguage (X.blockWords S) := by
  have right : ∀ {n} {w : Fin n → A}, w ∈ X.blockWords S n →
      ∃ w' ∈ X.blockWords S (n + 1), w' ∘ Fin.castSucc = w := by
    rintro n w ⟨x, hx, u, hr⟩
    obtain ⟨y, hy, a, hua⟩ := (hS u (reads_restrict_mem hr hx)).1
    refine ⟨Fin.snoc w a, ⟨x, hx, y, ?_⟩, funext fun i => Fin.snoc_castSucc ..⟩
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact reads_append.2 ⟨u, hr, reads_cons.2
      ⟨y, adj_restrict.2 ⟨reads_restrict_mem hr hx, hua, hy⟩, rfl⟩⟩
  refine
    { nonempty := fun n => ?_
      init := fun ⟨x, hx, h⟩ => ⟨x, hx, ?_⟩
      tail := fun ⟨x, hx, h⟩ => ?_
      extendRight := right
      extendLeft := fun ⟨x, hx, h⟩ => ?_ }
  · induction n with
    | zero => exact ⟨Fin.elim0, ⟨hne.some, hne.some_mem, by simpa using isWord_nil _⟩⟩
    | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw', -⟩ := right hw
      exact ⟨w', hw'⟩
  · rw [List.ofFn_succ', List.concat_eq_append] at h
    exact IsWord.of_append h
  · rw [List.ofFn_succ, isWord_cons] at h
    obtain ⟨t, ht, h⟩ := h
    exact ⟨t, (adj_restrict.1 ht).2.2, h⟩
  · obtain ⟨p, hp, b, hpx⟩ := (hS x hx).2
    refine ⟨Fin.cons b _, ⟨p, hp, ?_⟩, funext fun i => Fin.cons_succ ..⟩
    rw [List.ofFn_succ, isWord_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨x, adj_restrict.2 ⟨hp, hpx, hx⟩, h⟩

/-- The label words of a bi-infinite path inside `S` are read inside `S`. -/
@[category API, AMS 05 37, group "carry_shift"]
theorem reads_of_biPath {s : ℤ → V} {x : ℤ → A} (hpath : ∀ i, X.Adj (s i) (x i) (s (i + 1)))
    (hS : ∀ i, s i ∈ S) : ∀ (n : ℕ) (i : ℤ),
    (X.restrict S).Reads (s i) (List.ofFn fun k : Fin n => x (i + k)) (s (i + n))
  | 0, i => by simp [reads_nil]
  | n + 1, i => by
    rw [List.ofFn_succ, reads_cons]
    refine ⟨s (i + 1), adj_restrict.2 ⟨hS i, by simpa using hpath i, hS _⟩, ?_⟩
    have e : (List.ofFn fun k : Fin n => x (i + ((k.succ : ℕ) : ℤ))) =
        List.ofFn fun k : Fin n => x (i + 1 + (k : ℕ)) := by
      congr 1
      funext k
      simp only [Fin.val_succ]
      push_cast
      ring_nf
    rw [e, show i + ((n + 1 : ℕ) : ℤ) = i + 1 + n by push_cast; ring]
    exact reads_of_biPath hpath hS n (i + 1)

end blocks

/-! ### The label shift -/

section shift

variable [TopologicalSpace A] [DiscreteTopology A] (S : Set V) [DecidablePred (· ∈ S)]

variable (X) in
/-- **The label shift** of `X` inside `S`: the configurations all of whose blocks are read on
walks inside `S`. -/
def labelShift : Subshift A ℤ := ofLanguage (X.blockWords S)

variable {S}

/-- **The language of the label shift is the set of words read inside `S`.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_shift"]
theorem language_labelShift [Finite A] (hS : X.Essential S)
    (hne : S.Nonempty) (n : ℕ) : (X.labelShift S).language n = X.blockWords S n :=
  language_ofLanguage (isLanguage_blockWords hS hne) n

/-- **Bi-infinite paths inside `S` lie in the label shift.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_shift"]
theorem mem_labelShift_of_path {s : ℤ → V} {x : ℤ → A}
    (hpath : ∀ i, X.Adj (s i) (x i) (s (i + 1))) (hS : ∀ i, s i ∈ S) : x ∈ X.labelShift S :=
  fun n i => ⟨s i, hS i, _, reads_of_biPath hpath hS n i⟩

end shift

/-- Every vertex of a bi-infinite path lies in the core. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_shift"]
theorem mem_core_of_biPath {s : ℤ → V} (hpath : ∀ i, X.under (s i) (s (i + 1))) (i : ℤ) :
    s i ∈ X.core :=
  ⟨⟨fun n => s (i + n), by simp, fun n => by simpa [add_assoc] using hpath (i + n)⟩,
    ⟨fun n => s (i - n), by simp, fun _ => trivial, fun n => by
      have := hpath (i - (n + 1))
      simpa [sub_add_cancel, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using this⟩⟩

/-- **The sofic shift presented by `X`**: the label sequences of bi-infinite paths lie in the label
shift of the core. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_shift"]
theorem mem_labelShift_core_of_path [TopologicalSpace A] [DiscreteTopology A] [Fintype V]
    [Fintype A] [DecidableEq V]
    {s : ℤ → V} {x : ℤ → A} (hpath : ∀ i, X.Adj (s i) (x i) (s (i + 1))) :
    x ∈ X.labelShift X.core :=
  mem_labelShift_of_path hpath (mem_core_of_biPath fun i => ⟨x i, hpath i⟩)

/-! ### Rauzy graphs -/

section rauzy

variable [Fintype A] [DecidableEq A]

open Classical in
/-- **The Rauzy graph** of order `n` of a language `L`: vertices are words of length `n`, and
`u →a v` when a word `e` of length `n + 1` has `u` as its first `n` letters, `v` as its last `n`,
and ends in `a`. -/
noncomputable def rauzy (L : ∀ n, Set (Fin n → A)) (n : ℕ) : CarryGraph (Fin n → A) A where
  succ u a := Finset.univ.filter fun v =>
    ∃ e ∈ L (n + 1), edgeSrc e = u ∧ edgeTgt e = v ∧ e (Fin.last n) = a

@[category API, AMS 05 37 68, ref "LM95", group "carry_shift"]
theorem adj_rauzy {L : ∀ n, Set (Fin n → A)} {n : ℕ} {u v : Fin n → A} {a : A} :
    (rauzy L n).Adj u a v ↔
      ∃ e ∈ L (n + 1), edgeSrc e = u ∧ edgeTgt e = v ∧ e (Fin.last n) = a := by
  classical
  simp [rauzy, Adj]

/-- The underlying digraph of the Rauzy graph is ForMathlib's `Step L n`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_shift"]
theorem under_rauzy {L : ∀ n, Set (Fin n → A)} {n : ℕ} {u v : Fin n → A} :
    (rauzy L n).under u v ↔ Step L n u v := by
  simp only [under, adj_rauzy, Step]
  exact ⟨fun ⟨_, e, he, h1, h2, _⟩ => ⟨e, he, h1, h2⟩,
    fun ⟨e, he, h1, h2⟩ => ⟨_, e, he, h1, h2, rfl⟩⟩

@[category API, AMS 05 37 68, ref "LM95", group "carry_shift"]
theorem reach_rauzy {L : ∀ n, Set (Fin n → A)} {n : ℕ} {u v : Fin n → A} :
    (rauzy L n).Reach u v ↔ SymbolicDynamics.FullShift.Reach L n u v := by
  have : (rauzy L n).under = Step L n := by
    funext u v
    exact propext under_rauzy
  simp only [CarryGraph.Reach, SymbolicDynamics.FullShift.Reach, this]

end rauzy

end CarryGraph
