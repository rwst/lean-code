/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Rank
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.TFAE

/-!
# Peeling and the core ([LM95] §2.2; [BJG09] §1.4)

The **core** of a carry graph is the set of vertices lying on a bi-infinite walk; it is the
vertex set of the unique essential subgraph with the same edge shift [LM95, Def. 2.2.9,
Prop. 2.2.10].  It is reached by iterated removal of stranded vertices [LM95, Ex. 2.2.5]: first
the vertices without a surviving successor (the *forward peel*), then, inside what is left, the
vertices without a surviving predecessor.  `two_stage` says that a third stage removes nothing.

The forward peel is computable: `peel k` is the set of vertices from which a walk of length `k`
starts (`mem_peel`), it decreases, and it is stable after `|V|` rounds (`exists_peel_stable`).
This gives the **escape depth**: a vertex without an infinite forward walk has no walk of length
`|V|` (`hasWalk_card_iff`), and a vertex peeled in round `k` has no walk of length `k` — the
level bound that `Z32`'s funnel levels and `DubC2`'s peel rounds measure.

## Contents

* `fwd`, `bwdIn`, `core`, `Essential`.
* `core_essential`, `subset_core_of_essential` — the core is the largest essential set
  [LM95, Prop. 2.2.10].
* `fwd_greatest`, `bwdIn_greatest`, `two_stage` — the two peel stages and why a third is idle.
* `mem_core_of_cyc` — every cyclic vertex lies in the core.
* `core_eq_empty_iff` — empty core ⟺ acyclic ⟺ no walk of length `|V|` ⟺ nilpotent.
* `peel`, `mem_peel`, `exists_peel_stable`, `fwdSet`, `mem_fwdSet`, `hasWalk_card_iff` —
  the computable forward peel and the escape depth.
* `coreSet`, `mem_coreSet` — the core is computable (forward peel of `X` and of `X.reverse`).
* `lnoBranch_of_functional` — a core on which the carry graph is functional carries only simple
  cycles (the reading of `DubC.CoreDet`).

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
-/

namespace CarryGraph

variable {V A : Type*} (X : CarryGraph V A)

/-- Vertices with an infinite forward walk. -/
def fwd : Set V := {v | ∃ s : ℕ → V, s 0 = v ∧ ∀ n, X.under (s n) (s (n + 1))}

/-- Vertices with an infinite backward walk all of whose vertices lie in `S`. -/
def bwdIn (S : Set V) : Set V :=
  {v | ∃ s : ℕ → V, s 0 = v ∧ (∀ n, s n ∈ S) ∧ ∀ n, X.under (s (n + 1)) (s n)}

/-- **The core**: vertices with an infinite forward and an infinite backward walk, i.e. the
vertices of bi-infinite walks. -/
def core : Set V := X.fwd ∩ X.bwdIn Set.univ

/-- An essential set [LM95, Def. 2.2.9]: every vertex has a successor and a predecessor in it. -/
def Essential (S : Set V) : Prop := ∀ v ∈ S, (∃ w ∈ S, X.under v w) ∧ ∃ u ∈ S, X.under u v

variable {X}

/-- Dependent choice along a relation that never gets stuck inside `S`. -/
@[category API, AMS 05 37, group "carry_core"]
theorem exists_ray {R : V → V → Prop} {S : Set V} (h : ∀ v ∈ S, ∃ w ∈ S, R v w) {v : V}
    (hv : v ∈ S) : ∃ s : ℕ → V, s 0 = v ∧ (∀ n, s n ∈ S) ∧ ∀ n, R (s n) (s (n + 1)) := by
  choose f hfS hfR using h
  let step : S → S := fun x => ⟨f x.1 x.2, hfS x.1 x.2⟩
  refine ⟨fun n => (step^[n] ⟨v, hv⟩).1, rfl, fun n => (step^[n] ⟨v, hv⟩).2, fun n => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact hfR _ _

@[category API, AMS 05 37, group "carry_core"]
theorem fwd_of_under {v w : V} (h : X.under v w) (hw : w ∈ X.fwd) : v ∈ X.fwd := by
  obtain ⟨s, hs0, hs⟩ := hw
  refine ⟨fun n => if n = 0 then v else s (n - 1), by simp, fun n => ?_⟩
  rcases n with _ | n
  · simpa [hs0] using h
  · simpa using hs n

@[category API, AMS 05 37, group "carry_core"]
theorem bwdIn_of_under {S : Set V} {u v : V} (h : X.under u v) (hv : v ∈ S)
    (hu : u ∈ X.bwdIn S) : v ∈ X.bwdIn S := by
  obtain ⟨s, hs0, hsS, hs⟩ := hu
  refine ⟨fun n => if n = 0 then v else s (n - 1), by simp, fun n => ?_, fun n => ?_⟩
  · rcases n with _ | n
    · simpa using hv
    · simpa using hsS n
  · rcases n with _ | n
    · simpa [hs0] using h
    · simpa using hs n

@[category API, AMS 05 37, group "carry_core"]
theorem fwd_tail {v : V} (hv : v ∈ X.fwd) : ∃ w, X.under v w ∧ w ∈ X.fwd := by
  obtain ⟨s, rfl, hs⟩ := hv
  exact ⟨s 1, hs 0, fun n => s (n + 1), rfl, fun n => hs (n + 1)⟩

@[category API, AMS 05 37, group "carry_core"]
theorem bwdIn_tail {S : Set V} {v : V} (hv : v ∈ X.bwdIn S) :
    v ∈ S ∧ ∃ u, X.under u v ∧ u ∈ X.bwdIn S := by
  obtain ⟨s, rfl, hsS, hs⟩ := hv
  exact ⟨hsS 0, s 1, hs 0, fun n => s (n + 1), rfl, fun n => hsS (n + 1), fun n => hs (n + 1)⟩

@[category API, AMS 05 37, group "carry_core"]
theorem bwdIn_subset (S : Set V) : X.bwdIn S ⊆ S := fun _ hv => (bwdIn_tail hv).1

/-! ### The two peel stages -/

/-- **Stage 1** computes `fwd`: it is closed under "has a successor in the set", and every set
closed under that rule is contained in it. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem fwd_greatest :
    (∀ v ∈ X.fwd, ∃ w ∈ X.fwd, X.under v w) ∧
      ∀ S : Set V, (∀ v ∈ S, ∃ w ∈ S, X.under v w) → S ⊆ X.fwd := by
  refine ⟨fun v hv => ?_, fun S hS v hv => ?_⟩
  · obtain ⟨w, hvw, hw⟩ := fwd_tail hv
    exact ⟨w, hw, hvw⟩
  · obtain ⟨s, hs0, -, hs⟩ := exists_ray hS hv
    exact ⟨s, hs0, hs⟩

/-- **Stage 2** computes `bwdIn F`: it lies in `F`, is closed under "has a predecessor in the
set", and contains every subset of `F` closed under that rule. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem bwdIn_greatest (F : Set V) :
    X.bwdIn F ⊆ F ∧ (∀ v ∈ X.bwdIn F, ∃ u ∈ X.bwdIn F, X.under u v) ∧
      ∀ S ⊆ F, (∀ v ∈ S, ∃ u ∈ S, X.under u v) → S ⊆ X.bwdIn F := by
  refine ⟨bwdIn_subset F, fun v hv => ?_, fun S hSF hS v hv => ?_⟩
  · obtain ⟨-, u, huv, hu⟩ := bwdIn_tail hv
    exact ⟨u, hu, huv⟩
  · obtain ⟨s, hs0, hsS, hs⟩ := exists_ray (R := fun x y => X.under y x) hS hv
    exact ⟨s, hs0, fun n => hSF (hsS n), hs⟩

/-- **The two-stage theorem.**  After the forward peel (`F = fwd`) and the backward peel inside
it (`B = bwdIn F`), every survivor still has a surviving successor — a third stage removes
nothing — and the survivors are exactly the core.  The successor is the next vertex of `v`'s
forward ray: it is in `F`, and it inherits `v`'s backward ray, prefixed by `v`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem two_stage :
    (∀ v ∈ X.bwdIn X.fwd, ∃ w ∈ X.bwdIn X.fwd, X.under v w) ∧ X.bwdIn X.fwd = X.core := by
  have third : ∀ v ∈ X.bwdIn X.fwd, ∃ w ∈ X.bwdIn X.fwd, X.under v w := by
    intro v hv
    obtain ⟨w, hvw, hw⟩ := fwd_tail (bwdIn_subset _ hv)
    exact ⟨w, bwdIn_of_under hvw hw hv, hvw⟩
  refine ⟨third, Set.ext fun v => ⟨fun hv => ⟨bwdIn_subset _ hv, ?_⟩, fun hv => ?_⟩⟩
  · obtain ⟨s, hs0, -, hs⟩ := hv
    exact ⟨s, hs0, fun _ => trivial, hs⟩
  · -- a backward ray from a core vertex stays in `fwd`: each of its vertices reaches `v`
    obtain ⟨hf, s, hs0, -, hs⟩ := hv
    refine ⟨s, hs0, fun n => ?_, hs⟩
    induction n with
    | zero => exact hs0 ▸ hf
    | succ n ih => exact fwd_of_under (hs n) ih

/-! ### The core is the largest essential set -/

/-- [LM95, Prop. 2.2.10], first half: the core is essential. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem core_essential : X.Essential X.core := by
  intro v ⟨hf, hb⟩
  constructor
  · obtain ⟨w, hvw, hw⟩ := fwd_tail hf
    exact ⟨w, ⟨hw, bwdIn_of_under hvw trivial hb⟩, hvw⟩
  · obtain ⟨-, u, huv, hu⟩ := bwdIn_tail hb
    exact ⟨u, ⟨fwd_of_under huv hf, hu⟩, huv⟩

/-- [LM95, Prop. 2.2.10], second half: every essential set lies in the core. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem subset_core_of_essential {S : Set V} (hS : X.Essential S) : S ⊆ X.core := by
  intro v hv
  refine ⟨fwd_greatest.2 S (fun x hx => (hS x hx).1) hv, ?_⟩
  exact (bwdIn_greatest Set.univ).2.2 S (Set.subset_univ _) (fun x hx => (hS x hx).2) hv

/-- Every cyclic vertex lies in the core: its strong component is essential. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem mem_core_of_cyc {v : V} (hv : X.Cyc v) : v ∈ X.core := by
  refine subset_core_of_essential (S := {x | X.SameSCC v x}) ?_ (SameSCC.refl v)
  rintro x ⟨hvx, hxv⟩
  constructor
  · -- a successor of `x` on its way back to `v`
    rcases Relation.ReflTransGen.cases_head hxv with rfl | ⟨y, hxy, hyv⟩
    · obtain ⟨y, hxy, hyx⟩ := cyc_iff.1 hv
      exact ⟨y, ⟨Reach.single hxy, hyx⟩, hxy⟩
    · exact ⟨y, ⟨hvx.tail hxy, hyv⟩, hxy⟩
  · rcases Relation.ReflTransGen.cases_tail hvx with rfl | ⟨y, hvy, hyx⟩
    · obtain ⟨y, hvy, hyx⟩ := Relation.TransGen.tail'_iff.1 hv
      exact ⟨y, ⟨hvy, Reach.single hyx⟩, hyx⟩
    · exact ⟨y, ⟨hvy, Reach.head hyx hxv⟩, hyx⟩

/-! ### Empty core = acyclic = nilpotent -/

@[category API, AMS 05 37, group "carry_core"]
theorem transGen_of_walk {g : ℕ → V} {n : ℕ} (hg : X.IsWalk g n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) : Relation.TransGen X.under (g i) (g j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.TransGen.single (hg i (by omega))
  | succ j hij ih => exact (ih (by omega)).tail (hg j (by omega))

/-- In a finite carry graph a walk of length `|V|` passes a cyclic vertex. -/
@[category API, AMS 05 37, group "carry_core"]
theorem exists_cyc_of_walk [Fintype V] {g : ℕ → V} (hg : X.IsWalk g (Fintype.card V)) :
    ∃ i ≤ Fintype.card V, X.Cyc (g i) := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card V + 1) => g k) (by simp)
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with h' | h'
  · refine ⟨i, by omega, ?_⟩
    have := transGen_of_walk hg h' (by omega)
    rwa [← heq] at this
  · refine ⟨j, by omega, ?_⟩
    have := transGen_of_walk hg h' (by omega)
    rwa [heq] at this

section count

variable [Fintype A] [DecidableEq V]

/-- A walk of length `n` from `v` exists iff some labelled path of length `n` does. -/
@[category API, AMS 05 37, group "carry_core"]
theorem npaths_pos_iff : ∀ {v : V} {n : ℕ}, 0 < X.npaths v n ↔ X.HasWalk v n
  | v, 0 => by simp [npaths_zero, HasWalk]
  | v, n + 1 => by
    simp only [npaths_succ, Finset.sum_pos_iff, HasWalk, mem_out, npaths_pos_iff]
    constructor
    · rintro ⟨a, -, u, hu, h⟩
      exact ⟨u, ⟨a, hu⟩, h⟩
    · rintro ⟨u, ⟨a, hu⟩, h⟩
      exact ⟨a, Finset.mem_univ _, u, hu, h⟩

@[category API, AMS 05 37, group "carry_core"]
theorem hasWalk_of_fwd {v : V} (hv : v ∈ X.fwd) (n : ℕ) : X.HasWalk v n :=
  let ⟨s, hs0, hs⟩ := hv
  hasWalk_iff.2 ⟨s, hs0, fun i _ => hs i⟩

/-- **Empty core ⟺ acyclic ⟺ nilpotent** [LM95, Ex. 2.2.10]: the core is empty iff no vertex
lies on a cycle iff no labelled path has length `|V|` iff path counts vanish from some length
on.  In `DubC/` this is the *unavoidable divisor set* property of [DubOst06]. -/
@[category textbook, AMS 05 37, ref "LM95" "DubOst06", group "carry_core"]
theorem core_eq_empty_iff [Fintype V] :
    [X.core = ∅, ∀ v, ¬ X.Cyc v, ∀ v, X.npaths v (Fintype.card V) = 0,
      ∃ n, ∀ v, X.npaths v n = 0].TFAE := by
  tfae_have 1 → 2 := fun h v hv => by
    have := mem_core_of_cyc hv
    rw [h] at this
    exact this
  tfae_have 2 → 3 := fun h v => by
    by_contra hne
    obtain ⟨g, -, hg⟩ := hasWalk_iff.1 (npaths_pos_iff.1 (Nat.pos_of_ne_zero hne))
    obtain ⟨i, -, hi⟩ := exists_cyc_of_walk hg
    exact h _ hi
  tfae_have 3 → 4 := fun h => ⟨_, h⟩
  tfae_have 4 → 1 := fun ⟨n, h⟩ => by
    refine Set.eq_empty_of_forall_notMem fun v hv => ?_
    have := npaths_pos_iff.2 (hasWalk_of_fwd hv.1 n)
    rw [h v] at this
    exact Nat.lt_irrefl 0 this
  tfae_finish

end count

/-! ### The computable forward peel and the escape depth -/

section peel

variable [Fintype V] [Fintype A] [DecidableEq V]

variable (X) in
/-- **The forward peel**: `peel 0 = V`, and round `k + 1` keeps the vertices of `peel k` with a
successor in `peel k`. -/
def peel : ℕ → Finset V
  | 0 => Finset.univ
  | k + 1 => (peel k).filter fun v => (X.out v ∩ peel k).Nonempty

/-- **The peel computes walk lengths**: `peel k` is the set of vertices from which a walk of
length `k` starts. -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem mem_peel {v : V} : ∀ {k : ℕ}, v ∈ X.peel k ↔ X.HasWalk v k
  | 0 => by simp [peel, HasWalk]
  | k + 1 => by
    rw [peel, Finset.mem_filter, mem_peel]
    constructor
    · rintro ⟨-, w, hw⟩
      rw [Finset.mem_inter, mem_peel] at hw
      exact ⟨w, hw.1, hw.2⟩
    · intro h
      have h' : X.HasWalk v k := HasWalk.mono (Nat.le_succ k) h
      obtain ⟨w, hw, hwk⟩ := h
      exact ⟨h', w, Finset.mem_inter.2 ⟨hw, mem_peel.2 hwk⟩⟩

@[category API, AMS 05 37, group "carry_core"]
theorem peel_antitone {k l : ℕ} (h : k ≤ l) : X.peel l ⊆ X.peel k := fun _ hv =>
  mem_peel.2 ((mem_peel.1 hv).mono h)

@[category API, AMS 05 37, group "carry_core"]
theorem peel_stable_of {k : ℕ} (hk : X.peel (k + 1) = X.peel k) :
    ∀ m, k ≤ m → X.peel m = X.peel k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    calc X.peel (m + 1) = (X.peel m).filter (fun v => (X.out v ∩ X.peel m).Nonempty) := rfl
      _ = X.peel (k + 1) := by rw [ih]; rfl
      _ = X.peel k := hk

/-- **The peel stabilises within `|V|` rounds.** -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem exists_peel_stable : ∃ k ≤ Fintype.card V, X.peel (k + 1) = X.peel k := by
  by_contra! hc
  have hshrink : ∀ k ≤ Fintype.card V, (X.peel k).card + k ≤ Fintype.card V := by
    intro k hk
    induction k with
    | zero => simp [peel]
    | succ k ih =>
      have hss : X.peel (k + 1) ⊂ X.peel k :=
        Finset.ssubset_iff_subset_ne.2 ⟨peel_antitone (by omega), hc k (by omega)⟩
      have := Finset.card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hshrink _ le_rfl
  have h2 : X.peel (Fintype.card V + 1) ⊂ X.peel (Fintype.card V) :=
    Finset.ssubset_iff_subset_ne.2 ⟨peel_antitone (by omega), hc _ le_rfl⟩
  have := Finset.card_lt_card h2
  omega

@[category API, AMS 05 37, group "carry_core"]
theorem peel_eq_peel_card {m : ℕ} (hm : Fintype.card V ≤ m) :
    X.peel m = X.peel (Fintype.card V) := by
  obtain ⟨k, hk, hst⟩ := X.exists_peel_stable
  rw [peel_stable_of hst m (by omega), peel_stable_of hst _ hk]

/-- **Escape depth**: a vertex with a walk of length `|V|` has walks of every length, hence an
infinite forward walk (Kőnig); so a vertex without an infinite forward walk has no walk of
length `|V|`. -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem hasWalk_card_iff {v : V} : X.HasWalk v (Fintype.card V) ↔ v ∈ X.fwd := by
  refine ⟨fun h => ?_, fun h => hasWalk_of_fwd h _⟩
  have hall : ∀ n, X.HasWalk v n := by
    intro n
    rcases le_total n (Fintype.card V) with hn | hn
    · exact h.mono hn
    · rw [← mem_peel, peel_eq_peel_card hn, mem_peel]
      exact h
  exact exists_walk_of_forall_hasWalk hall

/-- **Escape depth, level form**: a vertex removed in round `k` of the peel has no walk of
length `k`; a vertex never removed has an infinite forward walk. -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem not_hasWalk_of_not_mem_peel {v : V} {k : ℕ} (h : v ∉ X.peel k) : ¬ X.HasWalk v k :=
  fun h' => h (mem_peel.2 h')

variable (X) in
/-- The vertices with an infinite forward walk, computed by the peel. -/
def fwdSet : Finset V := X.peel (Fintype.card V)

@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem mem_fwdSet {v : V} : v ∈ X.fwdSet ↔ v ∈ X.fwd := by
  rw [fwdSet, mem_peel, hasWalk_card_iff]

omit [Fintype A] in
/-- Infinite backward walks of `X` are infinite forward walks of `X.reverse`. -/
@[category API, AMS 05 37, ref "LM95", group "carry_core"]
theorem bwdIn_univ_eq : X.bwdIn Set.univ = X.reverse.fwd := by
  ext v
  constructor
  · rintro ⟨s, hs0, -, hs⟩
    exact ⟨s, hs0, fun n => under_reverse.2 (hs n)⟩
  · rintro ⟨s, hs0, hs⟩
    exact ⟨s, hs0, fun _ => trivial, fun n => under_reverse.1 (hs n)⟩

variable (X) in
/-- The core, computed as the forward peel of `X` intersected with that of `X.reverse`. -/
def coreSet : Finset V := X.fwdSet ∩ X.reverse.fwdSet

/-- **The core is computable.** -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_core"]
theorem mem_coreSet {v : V} : v ∈ X.coreSet ↔ v ∈ X.core := by
  rw [coreSet, Finset.mem_inter, mem_fwdSet, mem_fwdSet, core, bwdIn_univ_eq]
  rfl

instance decMemCore : DecidablePred (· ∈ X.core) := fun _ =>
  decidable_of_iff _ mem_coreSet

instance decMemFwd : DecidablePred (· ∈ X.fwd) := fun _ =>
  decidable_of_iff _ mem_fwdSet

@[category API, AMS 05 37, group "carry_core"]
theorem core_eq_empty_iff_coreSet : X.core = ∅ ↔ X.coreSet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_coreSet]

instance decCoreEmpty : Decidable (X.core = ∅) :=
  decidable_of_iff _ core_eq_empty_iff_coreSet.symm

end peel

/-! ### Peel chains -/

/-- A **peel chain** of length `J`: each round keeps every vertex of the previous set that has a
successor and a predecessor in it.  The rounds may keep more than the exact two-sided peel; this
is the form in which a certificate stores them. -/
def IsPeelChain (A : ℕ → Set V) (J : ℕ) : Prop :=
  ∀ j < J, ∀ v ∈ A j, (∃ w ∈ A j, X.under v w) → (∃ u ∈ A j, X.under u v) → v ∈ A (j + 1)

/-- **A walk lies in round `j` from step `j` on**, if round `0` is everything. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem IsPeelChain.walk_mem {A : ℕ → Set V} {J : ℕ} (h : X.IsPeelChain A J) (h0 : ∀ v, v ∈ A 0)
    {s : ℕ → V} (hs : ∀ n, X.under (s n) (s (n + 1))) : ∀ j ≤ J, ∀ n, j ≤ n → s n ∈ A j := by
  intro j
  induction j with
  | zero => intro _ n _; exact h0 _
  | succ j ih =>
    intro hj n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact h j (by omega) _ (ih (by omega) _ (by omega))
      ⟨_, ih (by omega) _ (by omega), hs (m + 1)⟩ ⟨_, ih (by omega) m (by omega), hs m⟩

/-- **The core lies in every round of a peel chain** that starts with everything. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem IsPeelChain.core_subset {A : ℕ → Set V} {J : ℕ} (h : X.IsPeelChain A J)
    (h0 : ∀ v, v ∈ A 0) : ∀ j ≤ J, X.core ⊆ A j := by
  intro j
  induction j with
  | zero => intro _ v _; exact h0 v
  | succ j ih =>
    intro hj v hv
    obtain ⟨⟨w, hw, hvw⟩, ⟨u, hu, huv⟩⟩ := core_essential v hv
    exact h j (by omega) v (ih (by omega) hv) ⟨w, ih (by omega) hw, hvw⟩
      ⟨u, ih (by omega) hu, huv⟩

/-! ### Functional graphs: periods within `|V|` -/

/-- **A walk in a finite functional graph repeats within `|V|` steps**: the labels of a walk of
length `N` are periodic from some time `t` with a period `P`, `t + P ≤ |V|`, as far as the walk
goes.  (Pigeonhole on the first `|V| + 1` vertices, then determinism.) -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem Functional.exists_period_of_walk [Fintype V] (h : X.Functional) {N : ℕ}
    {g : ℕ → V} {ℓ : ℕ → A}
    (hg : ∀ n, n + 1 ≤ N → X.Adj (g n) (ℓ n) (g (n + 1))) :
    ∃ t P, 1 ≤ P ∧ t + P ≤ Fintype.card V ∧
      ∀ n, t ≤ n → n + P + 1 ≤ N → ℓ (n + P) = ℓ n := by
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card V + 1) => g k) (by simp)
  have key : ∀ i j, i < j → j ≤ Fintype.card V → g i = g j →
      ∃ t P, 1 ≤ P ∧ t + P ≤ Fintype.card V ∧
        ∀ n, t ≤ n → n + P + 1 ≤ N → ℓ (n + P) = ℓ n := by
    intro i j hij hj hgij
    have hstep : ∀ k, j + k ≤ N → g (i + k) = g (j + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hgij
      | succ k ih =>
        intro hk
        have e := ih (by omega)
        have h1 := hg (i + k) (by omega)
        have h2 := hg (j + k) (by omega)
        rw [e] at h1
        exact (h _ _ _ _ _ h1 h2).2
    refine ⟨i, j - i, by omega, by omega, fun n hn hnN => ?_⟩
    have e := hstep (n - i) (by omega)
    rw [show i + (n - i) = n by omega, show j + (n - i) = n + (j - i) by omega] at e
    have h1 := hg n (by omega)
    have h2 := hg (n + (j - i)) (by omega)
    rw [← e] at h2
    exact (h _ _ _ _ _ h2 h1).1
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt
  · exact key a b hlt (by omega) he
  · exact key b a hlt (by omega) he.symm

/-! ### Functional cores -/

/-- **A functional core carries only simple cycles** (the reading of `DubC.CoreDet`): if `K`
contains the core and the restriction of `X` to `K` is functional, no vertex has two arcs
inside its strong component. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_core"]
theorem lnoBranch_of_functional (K : Set V) [DecidablePred (· ∈ K)] (hK : X.core ⊆ K)
    (hf : (X.restrict K).Functional) : X.LNoBranch := by
  intro v a b t u hvt hvu htv huv
  have cv : X.Cyc v := cyc_iff.2 ⟨t, ⟨a, hvt⟩, htv⟩
  have ct : X.Cyc t := cv.of_sameSCC ⟨Reach.single ⟨a, hvt⟩, htv⟩
  have cu : X.Cyc u := cv.of_sameSCC ⟨Reach.single ⟨b, hvu⟩, huv⟩
  have hv := hK (mem_core_of_cyc cv)
  exact hf v a b t u (adj_restrict.2 ⟨hv, hvt, hK (mem_core_of_cyc ct)⟩)
    (adj_restrict.2 ⟨hv, hvu, hK (mem_core_of_cyc cu)⟩)

end CarryGraph
