/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.ZeroEntropy

/-!
# Label sequences and the subset construction ([LM95] §§3.1–3.3)

A carry graph *presents* the label sequences of its infinite paths.  Two conditions are in play:

* the **state form** `LNoBranch` — no vertex has two distinct arcs inside its own strong
  component (Chapter 4: zero entropy of the graph itself);
* the **label form** `AllPer` — every infinite path has an eventually periodic *label*
  sequence.  This is a property of the label language alone.

The state form implies the label form for every finite graph, and on a right-resolving graph the
two agree (`lnoBranch_iff_allPer_of_rr`).  In general they differ: the `5/3`, `k = 3` tube of
`DubC2/` is a non-right-resolving presentation of one periodic orbit with a branching strong
component (`tube53_separates`).  The subset construction `det` [LM95, Thm 3.3.2] repairs this:

  `AllPer X  ⟺  AllPer X.det  ⟺  LNoBranch X.det`                 (`determinization`)

and its growth leg says that the label language grows polynomially
(`allPer_iff_wordGrowth`, the Lean meaning of "`λ_det = 1`" in `DubC2/README.md`).  The
construction is computable: `X.det : CarryGraph (Finset V) A`, so the det form of a small graph
is checked by `decide`.

## Contents

* `EvPer`, `AllPer`, `AllEvPer.allPer`, `allPer_of_hom` (quotient soundness).
* `lnoBranch_isLRank_ncard` (labelled rank from finite reach, any label type),
  `lnoBranch_iff_allEvPer`, `allPer_of_lnoBranch`.
* `RightResolving.eq`, `evPer_path_of_rr`, `lnoBranch_iff_allPer_of_rr`.
* `detStep`, `det`, `adj_det`, `det_rightResolving`, `isWord_det`, `isWord_det_singleton`,
  `words_det_singleton`, `det_iPath_of_iPath`, `exists_iPath_of_det` (Kőnig's lemma for the
  subset construction), `allPer_det_iff`.
* `determinization`, `allPer_iff_polyGrowth_det`, `allPer_iff_entropy_det`,
  `allPer_iff_wordGrowth`.
* `allPer_of_graded`, `tube`, `tube53_separates`, `diamond`, `diamond_separates`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005) 635–648.
* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor
  sequences*, Zenodo (2026).
-/

namespace CarryGraph

variable {V W A : Type*} {X : CarryGraph V A}

/-! ### Eventually periodic label sequences -/

/-- Eventual periodicity of a sequence. -/
def EvPer {α : Type*} (ℓ : ℕ → α) : Prop := ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → ℓ (m + L) = ℓ m

variable (X) in
/-- **The label form**: every infinite labelled path has an eventually periodic label
sequence. -/
def AllPer : Prop := ∀ s ℓ, X.IsIPath s ℓ → EvPer ℓ

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem AllEvPer.allPer (h : X.AllEvPer) : X.AllPer := fun s ℓ hs =>
  let ⟨n₀, L, hL, hp⟩ := h s ℓ hs
  ⟨n₀, L, hL, fun m hm => (hp m hm).2⟩

/-- **Quotient soundness**: a homomorphism sends infinite paths to infinite paths with the same
labels, so the label form of the image certifies the label form of the source.  Merging
follower-equivalent states [LM95, Lemma 3.3.8] is such a map (`Follower.lean`). -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_of_hom {Y : CarryGraph W A} (f : Hom X Y) (h : Y.AllPer) : X.AllPer :=
  fun s ℓ hs => h (f.toFun ∘ s) ℓ fun n => f.map_adj (hs n)

/-! ### The state form implies the label form, for any label type -/

@[category API, AMS 05 37, group "carry_labelled"]
theorem reach_of_ncard_eq (hfin : ∀ v, {w | X.Reach v w}.Finite) {s t : V} (hst : X.under s t)
    (he : {w | X.Reach t w}.ncard = {w | X.Reach s w}.ncard) : X.Reach t s := by
  have hsub : {w | X.Reach t w} ⊆ {w | X.Reach s w} := fun _ hw => (Reach.single hst).trans hw
  have := Set.eq_of_subset_of_ncard_le hsub he.ge (hfin s)
  have hs : s ∈ {w | X.Reach s w} := Reach.refl s
  rw [← this] at hs
  exact hs

/-- **Labelled completeness with finite reach**: without labelled branching, the number of
descendants is a labelled rank.  No finiteness of the label type is needed. -/
@[category textbook, AMS 05 37, ref "BJG09", group "carry_labelled"]
theorem lnoBranch_isLRank_ncard (hfin : ∀ v, {w | X.Reach v w}.Finite) (h : X.LNoBranch) :
    X.IsLRank fun v => {w | X.Reach v w}.ncard :=
  ⟨fun s a t hst => (noBranch_isRank_ncard hfin h.noBranch).1 s t ⟨a, hst⟩,
    fun s a b t u ht hu het heu => h s a b t u ht hu (reach_of_ncard_eq hfin ⟨a, ht⟩ het)
      (reach_of_ncard_eq hfin ⟨b, hu⟩ heu)⟩

/-- No labelled branching ⟺ every infinite path is eventually periodic (vertices and labels),
for a finite vertex set and an arbitrary label type. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem lnoBranch_iff_allEvPer [Finite V] : X.LNoBranch ↔ X.AllEvPer :=
  ⟨fun h _ _ hs => (lnoBranch_isLRank_ncard (fun _ => Set.toFinite _) h).evPer hs
    (Set.toFinite _), lnoBranch_of_allEvPer⟩

/-- **The state form is sound** for every finite presentation. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_of_lnoBranch [Finite V] (h : X.LNoBranch) : X.AllPer :=
  (lnoBranch_iff_allEvPer.1 h).allPer

/-! ### Right-resolving presentations -/

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem RightResolving.eq (h : X.RightResolving) {v w w' : V} {a : A} (hw : X.Adj v a w)
    (hw' : X.Adj v a w') : w = w' :=
  Finset.card_le_one.1 (h v a) w hw w' hw'

/-- On a right-resolving presentation, eventually periodic labels make the path eventually
periodic too: labels determine the path, and a repeated block start propagates. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem evPer_path_of_rr [Finite V] (hrr : X.RightResolving) {s : ℕ → V} {ℓ : ℕ → A}
    (hs : X.IsIPath s ℓ) (hl : EvPer ℓ) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m ∧ ℓ (m + L) = ℓ m := by
  obtain ⟨n₀, L, hL, hper⟩ := hl
  have lper : ∀ k i, ℓ (n₀ + k * L + i) = ℓ (n₀ + i) := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show n₀ + (k + 1) * L + i = (n₀ + k * L + i) + L by ring, hper _ (by omega), ih]
  have prop : ∀ k k', s (n₀ + k * L) = s (n₀ + k' * L) →
      ∀ i, s (n₀ + k * L + i) = s (n₀ + k' * L + i) := by
    intro k k' h0 i
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have e1 := hs (n₀ + k * L + i)
      have e2 := hs (n₀ + k' * L + i)
      rw [lper] at e1 e2
      rw [ih] at e1
      exact hrr.eq e1 e2
  obtain ⟨k, k', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun k : ℕ => s (n₀ + k * L)
  wlog hlt : k < k' generalizing k k'
  · exact this k' k hne.symm heq.symm (by omega)
  refine ⟨n₀ + k * L, (k' - k) * L, Nat.mul_pos (by omega) hL, fun m hm => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = n₀ + k * L + i := ⟨m - (n₀ + k * L), by omega⟩
  have hidx : n₀ + k * L + i + (k' - k) * L = n₀ + k' * L + i := by
    have : k' * L = k * L + (k' - k) * L := by rw [← add_mul]; congr 1; omega
    omega
  rw [hidx]
  exact ⟨(prop k k' heq i).symm, by rw [lper, lper]⟩

/-- **On a right-resolving presentation the two forms agree.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem lnoBranch_iff_allPer_of_rr [Finite V] (hrr : X.RightResolving) :
    X.LNoBranch ↔ X.AllPer :=
  ⟨allPer_of_lnoBranch, fun h =>
    lnoBranch_of_allEvPer fun _ _ hs => evPer_path_of_rr hrr hs (h _ _ hs)⟩

/-! ### The subset construction -/

section det

variable [DecidableEq V]

variable (X) in
/-- The `a`-successor set of `S`. -/
def detStep (S : Finset V) (a : A) : Finset V := S.biUnion fun v => X.succ v a

variable (X) in
/-- **The subset construction** [LM95, Thm 3.3.2] as a carry graph on `Finset V`: from `S`, the
letter `a` leads to the set of `a`-successors of `S`, if that set is non-empty. -/
def det : CarryGraph (Finset V) A where
  succ S a := if (X.detStep S a).Nonempty then {X.detStep S a} else ∅

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem mem_detStep {S : Finset V} {a : A} {w : V} :
    w ∈ X.detStep S a ↔ ∃ v ∈ S, X.Adj v a w := by
  simp [detStep, Adj]

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem detStep_empty (a : A) : X.detStep ∅ a = ∅ := by simp [detStep]

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem adj_det {S T : Finset V} {a : A} : X.det.Adj S a T ↔ T = X.detStep S a ∧ T.Nonempty := by
  simp only [Adj, det]
  split_ifs with h
  · rw [Finset.mem_singleton]
    exact ⟨fun e => ⟨e, e ▸ h⟩, And.left⟩
  · simp only [Finset.notMem_empty, false_iff]
    rintro ⟨rfl, h'⟩
    exact h h'

@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem det_rightResolving : X.det.RightResolving := fun S a => by
  simp only [det]
  split_ifs <;> simp

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem ends_empty : ∀ w : List A, X.ends ∅ w = ∅ := by
  intro w
  ext u
  simp [mem_ends]

/-- A word is read in the subset construction from a non-empty `S` iff it is read in `X` from
some vertex of `S`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem isWord_det : ∀ {w : List A} {S : Finset V}, S.Nonempty →
    (X.det.IsWord S w ↔ (X.ends S w).Nonempty)
  | [], S, hS => ⟨fun _ => hS, fun _ => isWord_nil S⟩
  | a :: w, S, _ => by
    rw [isWord_cons]
    constructor
    · rintro ⟨T, hT, hw⟩
      obtain ⟨rfl, hne⟩ := adj_det.1 hT
      exact (isWord_det hne).1 hw
    · intro h
      have hne : (X.detStep S a).Nonempty := by
        by_contra h0
        rw [Finset.not_nonempty_iff_eq_empty] at h0
        change (X.ends (X.detStep S a) w).Nonempty at h
        rw [h0, ends_empty] at h
        exact Finset.not_nonempty_empty h
      exact ⟨_, adj_det.2 ⟨rfl, hne⟩, (isWord_det hne).2 h⟩

/-- **The subset construction presents the same language** from `{v}` as `X` from `v`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem isWord_det_singleton {v : V} {w : List A} : X.det.IsWord {v} w ↔ X.IsWord v w := by
  rw [isWord_det (Finset.singleton_nonempty v), isWord_iff_ends_nonempty]

@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem words_det_singleton [Fintype A] [DecidableEq A] (v : V) (n : ℕ) :
    X.det.words {v} n = X.words v n := by
  ext w
  simp only [mem_words, isWord_det_singleton]

/-- The empty state reads only the empty word. -/
@[category API, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem isWord_det_empty {w : List A} : X.det.IsWord ∅ w ↔ w = [] := by
  cases w with
  | nil => exact ⟨fun _ => rfl, fun _ => isWord_nil _⟩
  | cons a w =>
    simp only [isWord_cons, reduceCtorEq, iff_false]
    rintro ⟨T, hT, -⟩
    obtain ⟨rfl, hne⟩ := adj_det.1 hT
    rw [detStep_empty] at hne
    exact Finset.not_nonempty_empty hne

/-- A path of `X` gives a path of `X.det` with the same labels, from any set containing its
start. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem det_iPath_of_iPath {s : ℕ → V} {ℓ : ℕ → A} (hs : X.IsIPath s ℓ) {S₀ : Finset V}
    (h0 : s 0 ∈ S₀) : ∃ S : ℕ → Finset V, S 0 = S₀ ∧ X.det.IsIPath S ℓ ∧ ∀ n, s n ∈ S n := by
  let S : ℕ → Finset V := fun n => Nat.rec S₀ (fun n T => X.detStep T (ℓ n)) n
  have hmem : ∀ n, s n ∈ S n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact mem_detStep.2 ⟨s n, ih, hs n⟩
  exact ⟨S, rfl, fun n => adj_det.2 ⟨rfl, ⟨s (n + 1), hmem (n + 1)⟩⟩, hmem⟩

omit [DecidableEq V] in
/-- Pigeonhole for a downward-closed predicate on a finite set. -/
@[category API, AMS 05 37, group "carry_labelled"]
theorem exists_forall_of_finset {P : V → ℕ → Prop} (F : Finset V)
    (hdown : ∀ x m m', m' ≤ m → P x m → P x m') (h : ∀ m, ∃ x ∈ F, P x m) :
    ∃ x ∈ F, ∀ m, P x m := by
  by_contra hcon
  push Not at hcon
  choose! M hM using hcon
  obtain ⟨x, hx, hP⟩ := h (F.sup M)
  exact hM x hx (hdown x _ _ (Finset.le_sup hx) hP)

/-- **Kőnig's lemma for the subset construction**: a path of `X.det` lifts to a path of `X` with
the same labels, starting in its first state.  The vertex and label types may be infinite. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem exists_iPath_of_det {S : ℕ → Finset V} {ℓ : ℕ → A} (hS : X.det.IsIPath S ℓ)
    (h0 : (S 0).Nonempty) : ∃ s : ℕ → V, s 0 ∈ S 0 ∧ X.IsIPath s ℓ := by
  -- `LW n v m`: a walk of length `m` from `v` reading `ℓ n, …, ℓ (n + m - 1)`
  let LW : ℕ → V → ℕ → Prop := fun n v m =>
    ∃ g : ℕ → V, g 0 = v ∧ ∀ i < m, X.Adj (g i) (ℓ (n + i)) (g (i + 1))
  have back : ∀ m, ∀ w ∈ S m, ∃ v ∈ S 0, ∃ g : ℕ → V, g 0 = v ∧ g m = w ∧
      ∀ i < m, X.Adj (g i) (ℓ i) (g (i + 1)) := by
    intro m
    induction m with
    | zero => exact fun w hw => ⟨w, hw, fun _ => w, rfl, rfl, fun i hi => absurd hi (by omega)⟩
    | succ m ih =>
      intro w hw
      rw [(adj_det.1 (hS m)).1] at hw
      obtain ⟨u, hu, huw⟩ := mem_detStep.1 hw
      obtain ⟨v, hv, g, hg0, hgm, hg⟩ := ih u hu
      refine ⟨v, hv, fun i => if i ≤ m then g i else w, by simpa using hg0, by simp, ?_⟩
      intro i hi
      by_cases him : i < m
      · simpa [him.le, show i + 1 ≤ m by omega] using hg i him
      · obtain rfl : i = m := by omega
        simpa [hgm] using huw
  have hne : ∀ m, (S m).Nonempty := fun m => by
    rcases m with _ | m
    · exact h0
    · exact (adj_det.1 (hS m)).2
  have hdown : ∀ n x m m', m' ≤ m → LW n x m → LW n x m' :=
    fun _ _ _ _ hle ⟨g, hg0, hg⟩ => ⟨g, hg0, fun i hi => hg i (by omega)⟩
  obtain ⟨v₀, hv₀, hgood₀⟩ : ∃ v ∈ S 0, ∀ m, LW 0 v m := by
    refine exists_forall_of_finset (S 0) (hdown 0) fun m => ?_
    obtain ⟨w, hw⟩ := hne m
    obtain ⟨v, hv, g, hg0, -, hg⟩ := back m w hw
    exact ⟨v, hv, g, hg0, fun i hi => by simpa using hg i hi⟩
  have extend : ∀ n v, (∀ m, LW n v m) → ∃ w, X.Adj v (ℓ n) w ∧ ∀ m, LW (n + 1) w m := by
    intro n v hv
    obtain ⟨w, hw, hgood⟩ := exists_forall_of_finset
      (P := fun w m => X.Adj v (ℓ n) w ∧ LW (n + 1) w m) (X.succ v (ℓ n))
      (fun x m m' hle ⟨h1, h2⟩ => ⟨h1, hdown _ _ _ _ hle h2⟩) fun m => by
        obtain ⟨g, hg0, hg⟩ := hv (m + 1)
        have h1 : X.Adj v (ℓ n) (g 1) := by simpa [hg0] using hg 0 (by omega)
        refine ⟨g 1, h1, h1, fun i => g (i + 1), rfl, fun i hi => ?_⟩
        have := hg (i + 1) (by omega)
        rwa [show n + (i + 1) = n + 1 + i by ring] at this
    exact ⟨w, hw, fun m => (hgood m).2⟩
  obtain ⟨p, hp0, -, hpR⟩ := exists_ray
    (R := fun x y : ℕ × V => y.1 = x.1 + 1 ∧ X.Adj x.2 (ℓ x.1) y.2)
    (S := {x | ∀ m, LW x.1 x.2 m})
    (fun x hx => by
      obtain ⟨w, hw, hgood⟩ := extend x.1 x.2 hx
      exact ⟨(x.1 + 1, w), hgood, rfl, hw⟩)
    (v := (0, v₀)) hgood₀
  have hfst : ∀ n, (p n).1 = n := by
    intro n
    induction n with
    | zero => rw [hp0]
    | succ n ih => rw [(hpR n).1, ih]
  refine ⟨fun n => (p n).2, by simpa [hp0] using hv₀, fun n => ?_⟩
  have := (hpR n).2
  rwa [hfst] at this

/-- **A label sequence all of whose prefixes are read lies on an infinite path** (finite vertex
set): iterate the subset construction from the whole vertex set along the sequence, and lift. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem exists_iPath_of_forall_reads [Fintype V] {ℓ : ℕ → A}
    (h : ∀ m, ∃ g : ℕ → V, ∀ i < m, X.Adj (g i) (ℓ i) (g (i + 1))) :
    ∃ s : ℕ → V, X.IsIPath s ℓ := by
  let S : ℕ → Finset V := fun n => Nat.rec Finset.univ (fun k T => X.detStep T (ℓ k)) n
  have hmem : ∀ m (g : ℕ → V), (∀ i < m, X.Adj (g i) (ℓ i) (g (i + 1))) → ∀ n ≤ m, g n ∈ S n := by
    intro m g hg n hn
    induction n with
    | zero => exact Finset.mem_univ _
    | succ n ih => exact mem_detStep.2 ⟨g n, ih (by omega), hg n (by omega)⟩
  have hne : ∀ n, (S n).Nonempty := fun n => by
    obtain ⟨g, hg⟩ := h n
    exact ⟨g n, hmem n g hg n le_rfl⟩
  have hS : X.det.IsIPath S ℓ := fun n => adj_det.2 ⟨rfl, hne (n + 1)⟩
  obtain ⟨s, -, hs⟩ := exists_iPath_of_det hS (hne 0)
  exact ⟨s, hs⟩

/-- The label form is a property of the label language: `X` and `X.det` agree. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_det_iff : X.det.AllPer ↔ X.AllPer := by
  constructor
  · intro h s ℓ hs
    obtain ⟨S, -, hS, -⟩ := det_iPath_of_iPath hs (Finset.mem_singleton_self (s 0))
    exact h S ℓ hS
  · intro h S ℓ hS
    have h0 : (S 0).Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty] at h0
      have := (adj_det.1 (hS 0)).2
      rw [(adj_det.1 (hS 0)).1, h0, detStep_empty] at this
      exact Finset.not_nonempty_empty this
    obtain ⟨s, -, hs⟩ := exists_iPath_of_det hS h0
    exact h s ℓ hs

/-- **The determinization theorem.**  Every infinite path of `X` has eventually periodic labels
iff the same holds for its subset construction iff the subset construction passes the state
form.  (The state form on `X` itself implies these, `allPer_of_lnoBranch`, but is not implied by
them, `tube53_separates`.) -/
@[category textbook, AMS 05 37, ref "LM95" "Oda26", group "carry_labelled"]
theorem determinization [Fintype V] : [X.AllPer, X.det.AllPer, X.det.LNoBranch].TFAE := by
  tfae_have 1 ↔ 2 := allPer_det_iff.symm
  tfae_have 2 ↔ 3 := (lnoBranch_iff_allPer_of_rr det_rightResolving).symm
  tfae_finish

/-- **Growth leg**: the label form holds iff the subset construction has polynomial path
growth. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_iff_polyGrowth_det [Fintype V] [Fintype A] : X.AllPer ↔ X.det.PolyGrowth :=
  (determinization.out 1 3).trans (zeroEntropy_tfae.out 2 4)

/-- **Entropy leg**: the label form holds iff the subset construction has entropy `≤ 0`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_iff_entropy_det [Fintype V] [Fintype A] : X.AllPer ↔ X.det.entropy ≤ 0 :=
  (determinization.out 1 3).trans (zeroEntropy_tfae.out 2 5)

/-- **The label language grows polynomially iff every infinite path has eventually periodic
labels**: the Lean meaning of "`λ_det = 1`", stated on the words of `X` itself and with no
Perron–Frobenius. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem allPer_iff_wordGrowth [Fintype V] [Fintype A] [DecidableEq A] :
    X.AllPer ↔ ∃ C d : ℕ, ∀ v n, (X.words v n).card ≤ C * (n + 1) ^ d := by
  rw [allPer_iff_polyGrowth_det]
  constructor
  · rintro ⟨C, d, h⟩
    refine ⟨C, d, fun v n => ?_⟩
    rw [← words_det_singleton, card_words_eq_npaths det_rightResolving]
    exact h _ _
  · rintro ⟨C, d, h⟩
    refine ⟨Fintype.card V * C + 1, d, fun S n => ?_⟩
    rw [← card_words_eq_npaths det_rightResolving]
    have hsub : X.det.words S n ⊆ insert [] (S.biUnion fun v => X.words v n) := by
      intro w hw
      rw [mem_words] at hw
      rw [Finset.mem_insert, Finset.mem_biUnion]
      rcases S.eq_empty_or_nonempty with rfl | hS
      · exact Or.inl (isWord_det_empty.1 hw.2)
      · obtain ⟨u, hu⟩ := (isWord_det hS).1 hw.2
        obtain ⟨v, hv, hr⟩ := mem_ends.1 hu
        exact Or.inr ⟨v, hv, mem_words.2 ⟨hw.1, u, hr⟩⟩
    have hpow : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    calc (X.det.words S n).card
        ≤ (S.biUnion fun v => X.words v n).card + 1 :=
          (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      _ ≤ ∑ v ∈ S, (X.words v n).card + 1 := by gcongr; exact Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ (Finset.univ : Finset V), C * (n + 1) ^ d + 1 := by
          gcongr
          exact (Finset.sum_le_sum fun v _ => h v n).trans
            (Finset.sum_le_sum_of_subset (Finset.subset_univ S))
      _ = Fintype.card V * C * (n + 1) ^ d + 1 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]
      _ ≤ (Fintype.card V * C + 1) * (n + 1) ^ d := by rw [add_mul, one_mul]; omega

end det

/-! ### The separating instance: the `5/3`, `k = 3` tube -/

/-- A graded carry graph (every arc raises a level mod `L`, and its label depends only on the
level) has periodic labels. -/
@[category API, AMS 05 37, group "carry_labelled"]
theorem allPer_of_graded {L : ℕ} (hL : 0 < L) (lev : V → ℕ) (f : ℕ → A)
    (h : ∀ v a w, X.Adj v a w → lev w = (lev v + 1) % L ∧ a = f (lev v % L)) : X.AllPer := by
  intro s ℓ hs
  have hlev : ∀ n, lev (s (n + 1)) % L = (lev (s 0) + (n + 1)) % L := by
    intro n
    induction n with
    | zero => rw [(h _ _ _ (hs 0)).1, Nat.mod_mod]
    | succ n ih =>
      rw [(h _ _ _ (hs (n + 1))).1, Nat.mod_mod, Nat.add_mod, ih, ← Nat.add_mod]
      congr 1
  have hl : ∀ n, ℓ n = f ((lev (s 0) + n) % L) := by
    intro n
    rw [(h _ _ _ (hs n)).2]
    rcases n with _ | n
    · rfl
    · rw [hlev n]
  refine ⟨0, L, hL, fun m _ => ?_⟩
  rw [hl, hl, ← add_assoc, Nat.add_mod_right]

/-- The arcs of the 8-vertex branching strong component of the `5/3`, `ν = 1/2`, `P = {2,3}`,
`K = 2`, `k = 3` joint graph (`CarryGraph/data/tube53_k3.txt`, engine ids `0 1 2 3 32 33 34 35 ↦
0 … 7`). -/
def tubeArcs : Finset (Fin 8 × ℤ × Fin 8) :=
  {(0, -2, 4), (0, -2, 5), (1, -2, 5), (4, -2, 6), (5, -2, 6), (5, -2, 7),
   (2, 2, 0), (2, 2, 1), (3, 2, 1), (6, 2, 2), (7, 2, 2), (7, 2, 3)}

/-- The tube as a carry graph. -/
def tube : CarryGraph (Fin 8) ℤ := ofFinset tubeArcs

/-- The level of a tube vertex: `{0,1} ↦ 0`, `{4,5} ↦ 1`, `{6,7} ↦ 2`, `{2,3} ↦ 3`. -/
def tubeLev (v : Fin 8) : ℕ := ![0, 0, 3, 3, 1, 1, 2, 2] v

/-- **The tube separates the two forms.**  Its strong component branches (vertex `0` has the
two `-2`-arcs to `4` and `5`, both returning to `0`), so the state form fails; yet every
infinite path reads the period-4 word `(-2, -2, 2, 2)`, so the label form holds, and with it, by
`determinization`, the det form. -/
@[category test, AMS 05 37, ref "LM95" "DN05", group "carry_labelled"]
theorem tube53_separates : ¬ tube.LNoBranch ∧ tube.AllPer ∧ tube.det.LNoBranch := by
  have hper : tube.AllPer := allPer_of_graded (L := 4) (by norm_num) tubeLev
    (fun n => if n < 2 then -2 else 2) (by
      intro v a w h
      have h' : (v, a, w) ∈ tubeArcs := adj_ofFinset.1 h
      simp only [tubeArcs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide)
  refine ⟨fun h => ?_, hper, (determinization.out 1 3).1 hper⟩
  have e : ∀ v a w, (v, a, w) ∈ tubeArcs → tube.Adj v a w := fun _ _ _ h => adj_ofFinset.2 h
  have r60 : tube.Reach 6 0 :=
    (Reach.single ⟨2, e 6 2 2 (by decide)⟩).trans (Reach.single ⟨2, e 2 2 0 (by decide)⟩)
  have := (h 0 (-2) (-2) 4 5 (e _ _ _ (by decide)) (e _ _ _ (by decide))
    ((Reach.single ⟨-2, e 4 (-2) 6 (by decide)⟩).trans r60)
    ((Reach.single ⟨-2, e 5 (-2) 6 (by decide)⟩).trans r60)).2
  exact absurd this (by decide)

/-- The smallest separating instance: `0 →a 1`, `0 →a 2`, `1 →b 0`, `2 →b 0`.  It presents the
single periodic sequence `(ab)^∞` with a branching strong component. -/
def diamond : CarryGraph (Fin 3) Bool :=
  ofFinset {(0, true, 1), (0, true, 2), (1, false, 0), (2, false, 0)}

/-- **Both forms checked by `decide`**: the state form fails on `diamond` and holds on its
subset construction (computed as a carry graph on `Finset (Fin 3)`). -/
@[category test, AMS 05 37, ref "LM95", group "carry_labelled"]
theorem diamond_separates : ¬ diamond.LNoBranch ∧ diamond.det.LNoBranch := by decide

end CarryGraph
