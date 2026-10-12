/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Reach
import Mathlib.Data.Set.Card

/-!
# Ranks ([BJG09] §1.5, §4.2; [LM95] §2.2, §4.4)

A **rank** of a carry graph is a function `ρ : V → ℕ` that never increases along an arc and
leaves every vertex at most one rank-keeping successor (`CarryGraph.IsRank`); the labelled
variant `IsLRank` asks for at most one rank-keeping *arc*.  Ranks are the witnesses of zero
entropy: they exist exactly when no vertex has two successors inside its own strong component
(`NoBranch`), and they force every infinite path that stays in a finite region to be eventually
periodic (`IsRank.evPer`), labels included (`IsLRank.evPer`).

A **peel rank** for `K` strictly decreases out of every vertex outside `K`; then every cycle
lies in `K` (`cyc_mem_of_peelRank`), and the same holds with all arcs reversed
(`cyc_mem_of_peelRank_rev`).

## Contents

* `IsRank`, `IsLRank`, `NoBranch`, `LNoBranch`.
* Soundness `IsRank.noBranch`, completeness `noBranch_isRank_desc` (finite `V`) and
  `noBranch_isRank_ncard` (infinite `V`, finite reach sets) — the canonical rank is the
  descendant count.
* `IsRank.evPer`, `IsLRank.evPer` — eventual periodicity of infinite paths.
* `cyc_mem_of_peelRank`, `cyc_mem_of_peelRank_rev`.
* `drops_add_le` — along a walk, the number of rank drops is at most the starting rank.

## References

* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

variable {V A : Type*} (X : CarryGraph V A)

/-- **Rank**: non-increasing along arcs, at most one rank-keeping successor. -/
def IsRank (ρ : V → ℕ) : Prop :=
  (∀ s t, X.under s t → ρ t ≤ ρ s) ∧
    ∀ s t u, X.under s t → X.under s u → ρ t = ρ s → ρ u = ρ s → t = u

/-- **Labelled rank**: non-increasing along arcs, at most one rank-keeping arc. -/
def IsLRank (ρ : V → ℕ) : Prop :=
  (∀ s a t, X.Adj s a t → ρ t ≤ ρ s) ∧
    ∀ s a b t u, X.Adj s a t → X.Adj s b u → ρ t = ρ s → ρ u = ρ s → a = b ∧ t = u

/-- No vertex has two distinct successors inside its own strong component; equivalently every
strong component with an arc is a simple cycle [LM95, Def. 2.2.13], [BJG09, §1.5]. -/
def NoBranch : Prop := ∀ v t u, X.under v t → X.under v u → X.Reach t v → X.Reach u v → t = u

/-- No vertex has two distinct arcs inside its own strong component. -/
def LNoBranch : Prop :=
  ∀ v a b t u, X.Adj v a t → X.Adj v b u → X.Reach t v → X.Reach u v → a = b ∧ t = u

variable {X}

@[category API, AMS 05, ref "LM95", group "carry_rank"]
theorem IsLRank.isRank {ρ : V → ℕ} (h : X.IsLRank ρ) : X.IsRank ρ :=
  ⟨fun _ _ ⟨_, ht⟩ => h.1 _ _ _ ht,
    fun _ _ _ ⟨_, ht⟩ ⟨_, hu⟩ h1 h2 => (h.2 _ _ _ _ _ ht hu h1 h2).2⟩

@[category API, AMS 05, ref "LM95", group "carry_rank"]
theorem LNoBranch.noBranch (h : X.LNoBranch) : X.NoBranch :=
  fun _ _ _ ⟨_, ht⟩ ⟨_, hu⟩ h1 h2 => (h _ _ _ _ _ ht hu h1 h2).2

/-! ### Soundness and completeness of the rank form -/

/-- A rank is constant on strong components. -/
@[category API, AMS 05, ref "BJG09", group "carry_rank"]
theorem IsRank.eq_of_reach {ρ : V → ℕ} (h : ∀ s t, X.under s t → ρ t ≤ ρ s) {s t : V}
    (hst : X.under s t) (hts : X.Reach t s) : ρ t = ρ s :=
  le_antisymm (h _ _ hst) (reach_rank_le ρ h hts)

/-- **Soundness**: a rank forbids branching inside a strong component. -/
@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem IsRank.noBranch {ρ : V → ℕ} (h : X.IsRank ρ) : X.NoBranch :=
  fun v _ _ hvt hvu htv huv =>
    h.2 v _ _ hvt hvu (IsRank.eq_of_reach h.1 hvt htv) (IsRank.eq_of_reach h.1 hvu huv)

@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem IsLRank.lnoBranch {ρ : V → ℕ} (h : X.IsLRank ρ) : X.LNoBranch := by
  have h1 : ∀ s t, X.under s t → ρ t ≤ ρ s := fun _ _ ⟨_, ht⟩ => h.1 _ _ _ ht
  exact fun v a b t u hvt hvu htv huv => h.2 v a b t u hvt hvu
    (IsRank.eq_of_reach h1 ⟨a, hvt⟩ htv) (IsRank.eq_of_reach h1 ⟨b, hvu⟩ huv)

section desc

variable [Fintype V] [Fintype A] [DecidableEq V]

/-- **Completeness** ([BJG09] Prop. 1.4.3, §1.5): without branching, the descendant count is a
rank.  Rank-keeping arcs are exactly the arcs inside a strong component (`desc_eq_iff`). -/
@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem noBranch_isRank_desc (h : X.NoBranch) : X.IsRank X.desc :=
  ⟨fun _ _ hst => desc_le_of_under hst, fun s _ _ hst hsu ht hu =>
    h s _ _ hst hsu ((desc_eq_iff hst).1 ht) ((desc_eq_iff hsu).1 hu)⟩

@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem lnoBranch_isLRank_desc (h : X.LNoBranch) : X.IsLRank X.desc :=
  ⟨fun _ a _ hst => desc_le_of_under ⟨a, hst⟩, fun s a b _ _ hst hsu ht hu =>
    h s a b _ _ hst hsu ((desc_eq_iff ⟨a, hst⟩).1 ht) ((desc_eq_iff ⟨b, hsu⟩).1 hu)⟩

@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem exists_isRank_iff_noBranch : (∃ ρ, X.IsRank ρ) ↔ X.NoBranch :=
  ⟨fun ⟨_, h⟩ => h.noBranch, fun h => ⟨_, noBranch_isRank_desc h⟩⟩

@[category textbook, AMS 05, ref "LM95" "BJG09", group "carry_rank"]
theorem exists_isLRank_iff_lnoBranch : (∃ ρ, X.IsLRank ρ) ↔ X.LNoBranch :=
  ⟨fun ⟨_, h⟩ => h.lnoBranch, fun h => ⟨_, lnoBranch_isLRank_desc h⟩⟩

end desc

/-- **Completeness for infinite vertex sets**: if every vertex reaches only finitely many
vertices, then without branching the number of descendants is a rank (generic half of
`DubC2.Gen.Follower.exists_checked`). -/
@[category research solved, AMS 05, ref "BJG09", group "carry_rank"]
theorem noBranch_isRank_ncard (hfin : ∀ v, {w | X.Reach v w}.Finite) (h : X.NoBranch) :
    X.IsRank fun v => {w | X.Reach v w}.ncard := by
  have hsub : ∀ {s t}, X.Reach s t → {w | X.Reach t w} ⊆ {w | X.Reach s w} :=
    fun hst _ hw => hst.trans hw
  have hle : ∀ s t, X.under s t → {w | X.Reach t w}.ncard ≤ {w | X.Reach s w}.ncard :=
    fun s _ hst => Set.ncard_le_ncard (hsub (Reach.single hst)) (hfin s)
  have heq : ∀ {s t}, X.under s t →
      {w | X.Reach t w}.ncard = {w | X.Reach s w}.ncard → X.Reach t s := by
    intro s t hst he
    have := Set.eq_of_subset_of_ncard_le (hsub (Reach.single hst)) he.ge (hfin s)
    have hs : s ∈ {w | X.Reach s w} := Reach.refl s
    rw [← this] at hs
    exact hs
  exact ⟨hle, fun s _ _ hst hsu ht hu => h s _ _ hst hsu (heq hst ht) (heq hsu hu)⟩

/-! ### Eventual periodicity -/

/-- **Rank ⇒ eventually periodic** (generic form of `DubC.eventually_periodic_of_rank`): along
an infinite walk in a finite region the rank is eventually constant, the walk is then forced,
and a repetition propagates.  The returned threshold is past the point where the rank settles. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_rank"]
theorem IsRank.evPer' {ρ : V → ℕ} (h : X.IsRank ρ) {s : ℕ → V}
    (hs : ∀ n, X.under (s n) (s (n + 1))) (hfin : {w | X.Reach (s 0) w}.Finite) :
    ∃ n₀ L, 0 < L ∧ (∀ m, n₀ ≤ m → s (m + L) = s m) ∧
      ∀ m, n₀ ≤ m → ρ (s (m + 1)) = ρ (s m) := by
  have hanti : ∀ p q : ℕ, p ≤ q → ρ (s q) ≤ ρ (s p) := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => exact le_rfl
    | succ q _ ih => exact (h.1 _ _ (hs q)).trans ih
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, ∀ m, n₁ ≤ m → ρ (s m) = ρ (s n₁) := by
    classical
    have hex : ∃ r, ∃ n, ρ (s n) = r := ⟨_, 0, rfl⟩
    obtain ⟨n₁, hn₁⟩ := Nat.find_spec hex
    refine ⟨n₁, fun m hm => le_antisymm (hanti _ _ hm) ?_⟩
    rw [hn₁]
    exact Nat.find_min' hex ⟨m, rfl⟩
  have main : ∀ p q : ℕ, n₁ ≤ p → p < q → s p = s q →
      ∃ n₀ L, 0 < L ∧ (∀ m, n₀ ≤ m → s (m + L) = s m) ∧
        ∀ m, n₀ ≤ m → ρ (s (m + 1)) = ρ (s m) := by
    intro p q hnp hpq heq
    obtain ⟨L, hL, rfl⟩ : ∃ L, 0 < L ∧ q = p + L := ⟨q - p, by omega, by omega⟩
    refine ⟨p, L, hL, fun m hm => ?_, fun m hm => by rw [hn₁ _ (by omega), hn₁ m (by omega)]⟩
    induction m, hm using Nat.le_induction with
    | base => exact heq.symm
    | succ m hpm ih =>
      have hadm2 : X.under (s m) (s (m + L + 1)) := by rw [← ih]; exact hs (m + L)
      have hr1 : ρ (s (m + 1)) = ρ (s m) := by rw [hn₁ (m + 1) (by omega), hn₁ m (by omega)]
      have hr2 : ρ (s (m + L + 1)) = ρ (s m) := by
        rw [hn₁ (m + L + 1) (by omega), hn₁ m (by omega)]
      have huq := h.2 (s m) (s (m + 1)) (s (m + L + 1)) (hs m) hadm2 hr1 hr2
      rw [show m + 1 + L = m + L + 1 by omega, ← huq]
  have hmaps : Set.MapsTo (fun j => s (n₁ + j)) Set.univ {w | X.Reach (s 0) w} := by
    intro j _
    have : ∀ n, X.Reach (s 0) (s n) := fun n => by
      induction n with
      | zero => exact Reach.refl _
      | succ n ih => exact ih.tail (hs n)
    exact this _
  obtain ⟨j₁, -, j₂, -, hjne, hjeq⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hfin
  rcases lt_or_gt_of_ne hjne with hlt | hlt
  · exact main (n₁ + j₁) (n₁ + j₂) (by omega) (by omega) hjeq
  · exact main (n₁ + j₂) (n₁ + j₁) (by omega) (by omega) hjeq.symm

/-- **Rank ⇒ every infinite walk in a finite region is eventually periodic.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_rank"]
theorem IsRank.evPer {ρ : V → ℕ} (h : X.IsRank ρ) {s : ℕ → V}
    (hs : ∀ n, X.under (s n) (s (n + 1))) (hfin : {w | X.Reach (s 0) w}.Finite) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m :=
  let ⟨n₀, L, hL, hper, _⟩ := h.evPer' hs hfin
  ⟨n₀, L, hL, hper⟩

/-- **Labelled rank ⇒ the vertex and the label sequence of an infinite path in a finite region
are eventually periodic, with one period.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_rank"]
theorem IsLRank.evPer {ρ : V → ℕ} (h : X.IsLRank ρ) {s : ℕ → V} {ℓ : ℕ → A}
    (hs : X.IsIPath s ℓ) (hfin : {w | X.Reach (s 0) w}.Finite) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m ∧ ℓ (m + L) = ℓ m := by
  obtain ⟨n₀, L, hL, hper, hρ⟩ := h.isRank.evPer' (fun n => ⟨ℓ n, hs n⟩) hfin
  refine ⟨n₀, L, hL, fun m hm => ⟨hper m hm, ?_⟩⟩
  have h2 : X.Adj (s m) (ℓ (m + L)) (s (m + 1)) := by
    have := hs (m + L)
    rwa [hper m hm, show m + L + 1 = m + 1 + L by omega, hper (m + 1) (by omega)] at this
  exact (h.2 (s m) _ _ _ _ h2 (hs m) (hρ m hm) (hρ m hm)).1

/-! ### Peel ranks -/

/-- The peel-rank argument for an arbitrary relation (generic form of
`DubC.transGen_self_of_rank`). -/
@[category API, AMS 05, ref "BJG09", group "carry_rank"]
theorem cyc_mem_of_peelRank_rel {adm : V → V → Prop} (C K : V → Prop) (ρ : V → ℕ)
    (hcyc : ∀ v, Relation.TransGen adm v v → C v)
    (hle : ∀ v t, C v → C t → adm v t → ρ t ≤ ρ v)
    (hlt : ∀ v t, C v → C t → adm v t → ¬ K v → ρ t < ρ v)
    {r : V} (hr : Relation.TransGen adm r r) : K r := by
  by_contra hK
  obtain ⟨t, hstep, hrest⟩ := Relation.TransGen.head'_iff.mp hr
  have hCr : C r := hcyc r hr
  have hmid : ∀ s, Relation.ReflTransGen adm t s → Relation.ReflTransGen adm s r → C s :=
    fun s h1 h2 => hcyc s (Relation.TransGen.trans_left (Relation.TransGen.tail' h2 hstep) h1)
  have walk : ∀ s, Relation.ReflTransGen adm t s → Relation.ReflTransGen adm s r →
      ρ s ≤ ρ t := by
    intro s h1
    induction h1 with
    | refl => intro _; exact le_rfl
    | @tail b c h1' hstep' ih =>
      intro h2
      have hb2 : Relation.ReflTransGen adm b r := Relation.ReflTransGen.head hstep' h2
      exact (hle b c (hmid b h1' hb2) (hmid c (h1'.tail hstep') h2) hstep').trans (ih hb2)
  have h1 : ρ r ≤ ρ t := walk r hrest Relation.ReflTransGen.refl
  have h2 : ρ t < ρ r := hlt r t hCr (hmid t Relation.ReflTransGen.refl hrest) hstep hK
  omega

/-- **Peel rank ⇒ every cycle lies in `K`.**  `C` contains every cyclic vertex; `ρ` never
increases along an arc inside `C` and strictly drops out of every vertex of `C` outside `K`. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_rank"]
theorem cyc_mem_of_peelRank (C K : V → Prop) (ρ : V → ℕ) (hcyc : ∀ v, X.Cyc v → C v)
    (hle : ∀ v t, C v → C t → X.under v t → ρ t ≤ ρ v)
    (hlt : ∀ v t, C v → C t → X.under v t → ¬ K v → ρ t < ρ v)
    {r : V} (hr : X.Cyc r) : K r :=
  cyc_mem_of_peelRank_rel C K ρ hcyc hle hlt hr

@[category API, AMS 05, ref "BJG09", group "carry_rank"]
theorem transGen_swap {r : V → V → Prop} {x y : V} (h : Relation.TransGen r x y) :
    Relation.TransGen (Function.swap r) y x := by
  induction h with
  | single hxy => exact Relation.TransGen.single hxy
  | tail _ hbc ih => exact Relation.TransGen.head hbc ih

/-- **Backward peel rank ⇒ every cycle lies in `K`**: the same argument with all arcs reversed;
`ρ` never decreases along an arc inside `C` and strictly increases into every vertex of `C`
outside `K`. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_rank"]
theorem cyc_mem_of_peelRank_rev (C K : V → Prop) (ρ : V → ℕ) (hcyc : ∀ v, X.Cyc v → C v)
    (hle : ∀ v t, C v → C t → X.under v t → ρ v ≤ ρ t)
    (hlt : ∀ v t, C v → C t → X.under v t → ¬ K t → ρ v < ρ t)
    {r : V} (hr : X.Cyc r) : K r :=
  cyc_mem_of_peelRank_rel (adm := Function.swap X.under) C K ρ
    (fun v h => hcyc v (transGen_swap h : Relation.TransGen X.under v v))
    (fun v t hv ht hst => hle t v ht hv hst)
    (fun v t hv ht hst hK => hlt t v ht hv hst hK) (transGen_swap hr)

/-- **Core form ⇒ no branching**: if every cyclic vertex lies in `K` and arcs inside `K` are
deterministic, no vertex branches inside its strong component. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_rank"]
theorem noBranch_of_cyc_det (K : V → Prop) (hcyc : ∀ v, X.Cyc v → K v)
    (hdet : ∀ v t u, K v → K t → K u → X.under v t → X.under v u → t = u) : X.NoBranch := by
  intro v t u hvt hvu htv huv
  have cv : X.Cyc v := cyc_iff.2 ⟨t, hvt, htv⟩
  have ct : X.Cyc t := cv.of_sameSCC ⟨Reach.single hvt, htv⟩
  have cu : X.Cyc u := cv.of_sameSCC ⟨Reach.single hvu, huv⟩
  exact hdet v t u (hcyc v cv) (hcyc t ct) (hcyc u cu) hvt hvu

/-! ### Rank depth -/

open Classical in
/-- **Rank depth**: along a walk of length `n` on which the rank never increases, the number of
strict drops plus the final rank is at most the initial rank.  So a walk drops at most `ρ (g 0)`
times. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_rank"]
theorem drops_add_le (ρ : V → ℕ) {g : ℕ → V} :
    ∀ n, (∀ i < n, ρ (g (i + 1)) ≤ ρ (g i)) →
      ((Finset.range n).filter fun i => ρ (g (i + 1)) < ρ (g i)).card + ρ (g n) ≤ ρ (g 0)
  | 0, _ => by simp
  | n + 1, h => by
    have ih := drops_add_le ρ n fun i hi => h i (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hd
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · have := h n (by omega)
      omega

end CarryGraph
