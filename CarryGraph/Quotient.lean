/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Splitting
import CarryGraph.Follower

/-!
# Homomorphisms, simulations and subdivision ([LM95] §§2.2, 3.1, 8.2; [BJG09] §§1.3, 4.5)

What survives passing to a coarser carry graph, and how word-labelled graphs become carry graphs.

* **Homomorphisms** (`Hom`, `Basic.lean`) map cycles to cycles (`Hom.cyc_map`, `Reach.lean`),
  the core into the core (`Hom.mem_core`), and the label form backwards (`allPer_of_hom`,
  `Labelled.lean`).  A **locally injective** homomorphism (injective on the `a`-successors of
  every vertex, the graph form of a right-resolving factor map [LM95, §8.2]) also bounds path
  counts, so growth and zero entropy pass backwards (`Hom.npaths_le`,
  `Hom.entropy_le_of_locInj`, `Hom.lnoBranch_of_locInj`).
* **Simulations** `IsSimulation X Y R`: a relation along which every arc of `X` is matched by an
  arc of `Y` with the same label.  Infinite paths, words and the label form transfer
  (`IsSimulation.exists_iPath`, `IsSimulation.langFrom_subset`, `allPer_of_simulation`).  A
  homomorphism is the functional case.
* **The rung** `cyc_mem_of_peelRank_of_hom`: if every cycle of `Y` lies in `K'`, a peel rank
  on the preimage of `K'` shrinks it to `K`.  This is one step of the `DubC/` ladder, with
  `Y` the graph modulo a divisor.
* **Subdivision** (gate G-2 of the plan).  A finite word-labelled graph
  `E : Finset (V × List A × V)` with non-empty words becomes the carry graph `subdivide E` on
  `V ⊕ (E × Fin N)`: an arc `u —w→ v` with `|w| = k` is replaced by a chain of `k` letter arcs
  through `k - 1` new interior vertices.  The four transfer lemmas:
  - `reads_subdivide_iff` — between old vertices the subdivision reads exactly the
    concatenations of word paths (`WReads`);
  - `allPer_subdivide_iff` — the label form of the subdivision is the word form `WAllPer`
    (the output of every infinite word path is eventually periodic);
  - `lnoBranch_subdivide_iff` — zero entropy of the subdivision is `WNoBranch` (no vertex has
    two distinct word arcs inside its strong component);
  - `mem_langFrom_subdivide`, `sofic_wordLang` — the prefixes of word-path outputs form a
    sofic language.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
-/

open Filter ENNReal ExpGrowth

namespace CarryGraph

variable {V W A : Type*} {X : CarryGraph V A} {Y : CarryGraph W A}

/-! ### Homomorphisms and cores -/

@[category API, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.mem_fwd (f : Hom X Y) {v : V} (hv : v ∈ X.fwd) : f.toFun v ∈ Y.fwd :=
  let ⟨s, hs0, hs⟩ := hv
  ⟨f.toFun ∘ s, congrArg f.toFun hs0, fun n => f.map_under (hs n)⟩

@[category API, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.mem_bwdIn_univ (f : Hom X Y) {v : V} (hv : v ∈ X.bwdIn Set.univ) :
    f.toFun v ∈ Y.bwdIn Set.univ :=
  let ⟨s, hs0, _, hs⟩ := hv
  ⟨f.toFun ∘ s, congrArg f.toFun hs0, fun _ => trivial, fun n => f.map_under (hs n)⟩

/-- **A homomorphism maps the core into the core.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.mem_core (f : Hom X Y) {v : V} (hv : v ∈ X.core) : f.toFun v ∈ Y.core :=
  ⟨f.mem_fwd hv.1, f.mem_bwdIn_univ hv.2⟩

@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem core_subset_preimage_core (f : Hom X Y) : X.core ⊆ f.toFun ⁻¹' Y.core :=
  fun _ => f.mem_core

/-- **Quotient soundness for `core = ∅`.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.core_eq_empty (f : Hom X Y) (h : Y.core = ∅) : X.core = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv => by
    have := f.mem_core hv
    rw [h] at this
    exact this

/-- **The rung**: if every cycle of `Y` lies in `K'` and a peel rank on the preimage of `K'`
strictly drops off `K`, every cycle of `X` lies in `K` (generic form of
`DubC.coreClosed_of_ladder`). -/
@[category textbook, AMS 05, ref "BJG09", group "carry_quotient"]
theorem cyc_mem_of_peelRank_of_hom (f : Hom X Y) (K' : W → Prop) (hK' : ∀ w, Y.Cyc w → K' w)
    (K : V → Prop) (ρ : V → ℕ)
    (hle : ∀ v t, K' (f.toFun v) → K' (f.toFun t) → X.under v t → ρ t ≤ ρ v)
    (hlt : ∀ v t, K' (f.toFun v) → K' (f.toFun t) → X.under v t → ¬ K v → ρ t < ρ v)
    {v : V} (hv : X.Cyc v) : K v :=
  cyc_mem_of_peelRank (fun v => K' (f.toFun v)) K ρ (fun _ hv => hK' _ (f.cyc_map hv)) hle hlt hv

/-! ### Locally injective homomorphisms -/

/-- `f` is **locally injective**: injective on the `a`-successors of every vertex. -/
def Hom.LocInj (f : Hom X Y) : Prop := ∀ v a, Set.InjOn f.toFun {w | X.Adj v a w}

/-- **A locally injective homomorphism does not increase path counts.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.npaths_le [Fintype A] [DecidableEq W] (f : Hom X Y) (hf : f.LocInj) :
    ∀ n v, X.npaths v n ≤ Y.npaths (f.toFun v) n := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    rw [npaths_succ, npaths_succ]
    refine Finset.sum_le_sum fun a _ => ?_
    calc ∑ u ∈ X.succ v a, X.npaths u n ≤ ∑ u ∈ X.succ v a, Y.npaths (f.toFun u) n :=
          Finset.sum_le_sum fun u _ => ih u
      _ = ∑ w ∈ (X.succ v a).image f.toFun, Y.npaths w n :=
          (Finset.sum_image (f := fun w => Y.npaths w n) fun u hu u' hu' h =>
            hf v a hu hu' h).symm
      _ ≤ ∑ w ∈ Y.succ (f.toFun v) a, Y.npaths w n := by
          refine Finset.sum_le_sum_of_subset fun w hw => ?_
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
          exact f.map_adj hu

section locInj

variable [Fintype V] [Fintype W] [Fintype A] [DecidableEq W]

omit [Fintype V] [Fintype W] in
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.polyGrowth_of_locInj (f : Hom X Y) (hf : f.LocInj) (h : Y.PolyGrowth) :
    X.PolyGrowth :=
  let ⟨C, d, hC⟩ := h
  ⟨C, d, fun v n => (f.npaths_le hf n v).trans (hC _ n)⟩

/-- **Entropy can only drop along a locally injective homomorphism.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.entropy_le_of_locInj (f : Hom X Y) (hf : f.LocInj) : X.entropy ≤ Y.entropy := by
  refine expGrowthSup_le_of_eventually_le (b := Fintype.card V) (natCast_ne_top _)
    (Eventually.of_forall fun n => ?_)
  have : X.ntot n ≤ Fintype.card V * Y.ntot n :=
    calc ∑ v, X.npaths v n ≤ ∑ _v : V, Y.ntot n :=
          Finset.sum_le_sum fun v _ => (f.npaths_le hf n v).trans (npaths_le_ntot _ n)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact_mod_cast this

/-- **Quotient soundness for zero entropy** along a locally injective homomorphism. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.lnoBranch_of_locInj [DecidableEq V] (f : Hom X Y) (hf : f.LocInj)
    (h : Y.LNoBranch) : X.LNoBranch :=
  entropy_le_zero_iff.1 ((f.entropy_le_of_locInj hf).trans (entropy_le_zero_iff.2 h))

end locInj

/-! ### Simulations -/

/-- `R` is a **simulation** of `X` by `Y`: from related vertices, every arc of `X` is matched by
an arc of `Y` with the same label, between related vertices. -/
def IsSimulation (X : CarryGraph V A) (Y : CarryGraph W A) (R : V → W → Prop) : Prop :=
  ∀ v w, R v w → ∀ a v', X.Adj v a v' → ∃ w', Y.Adj w a w' ∧ R v' w'

@[category API, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem Hom.isSimulation (f : Hom X Y) : IsSimulation X Y fun v w => f.toFun v = w := by
  rintro v _ rfl a v' h
  exact ⟨_, f.map_adj h, rfl⟩

@[category API, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem IsSimulation.reads {R : V → W → Prop} (hR : IsSimulation X Y R) :
    ∀ {v v' : V} {x : List A} {w : W}, R v w → X.Reads v x v' → ∃ w', Y.Reads w x w' ∧ R v' w'
  | v, v', [], w, h, hr => by
    rw [reads_nil] at hr
    subst hr
    exact ⟨w, reads_nil.2 rfl, h⟩
  | v, v', a :: x, w, h, hr => by
    obtain ⟨t, ht, hr⟩ := reads_cons.1 hr
    obtain ⟨w₁, hw₁, h₁⟩ := hR v w h a t ht
    obtain ⟨w', hw', h'⟩ := hR.reads h₁ hr
    exact ⟨w', reads_cons.2 ⟨w₁, hw₁, hw'⟩, h'⟩

/-- **A simulation can only enlarge the language.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_quotient"]
theorem IsSimulation.langFrom_subset {R : V → W → Prop} (hR : IsSimulation X Y R) {v : V} {w : W}
    (h : R v w) : ∀ x, x ∈ X.langFrom v → x ∈ Y.langFrom w :=
  fun _ ⟨_, hr⟩ => let ⟨w', hw', _⟩ := hR.reads h hr; ⟨w', hw'⟩

/-- **Infinite paths lift along a simulation.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem IsSimulation.exists_iPath {R : V → W → Prop} (hR : IsSimulation X Y R) {s : ℕ → V}
    {ℓ : ℕ → A} (hs : X.IsIPath s ℓ) {w : W} (h : R (s 0) w) :
    ∃ t : ℕ → W, t 0 = w ∧ Y.IsIPath t ℓ ∧ ∀ n, R (s n) (t n) := by
  classical
  let nxt : ℕ → W → W := fun n x =>
    if hx : ∃ x', Y.Adj x (ℓ n) x' ∧ R (s (n + 1)) x' then hx.choose else x
  let t : ℕ → W := fun n => Nat.rec w (fun n x => nxt n x) n
  have ht : ∀ n, t (n + 1) = nxt n (t n) := fun _ => rfl
  have key : ∀ n, R (s n) (t n) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      have hx := hR _ _ ih _ _ (hs n)
      rw [ht]
      simp only [nxt, dite_eq_left hx]
      exact hx.choose_spec.2
  refine ⟨t, rfl, fun n => ?_, key⟩
  have hx := hR _ _ (key n) _ _ (hs n)
  rw [ht]
  simp only [nxt, dite_eq_left hx]
  exact hx.choose_spec.1

/-- **Soundness along a total simulation**: the label form of `Y` gives that of `X`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem allPer_of_simulation {R : V → W → Prop} (hR : IsSimulation X Y R)
    (htot : ∀ v, ∃ w, R v w) (h : Y.AllPer) : X.AllPer := fun s ℓ hs =>
  let ⟨_, hw⟩ := htot (s 0)
  let ⟨t, _, ht, _⟩ := hR.exists_iPath hs hw
  h t ℓ ht

/-- **Peel, then simulate.**  If a peel chain of length `J` ends inside `K`, and the restriction
of `X` to `K` is simulated by a graph `Y` with the label form, from a state related to every
vertex of `K`, then `X` has the label form.  This is the shape of a two-part certificate: rounds
that push every infinite walk into `K`, then a deterministic automaton on `K`. -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_quotient"]
theorem allPer_of_peelChain {A : ℕ → Set V} {J : ℕ} (hA : X.IsPeelChain A J)
    (h0 : ∀ v, v ∈ A 0) {K : Set V} [DecidablePred (· ∈ K)] (hK : A J ⊆ K) {R : V → W → Prop}
    (hR : IsSimulation (X.restrict K) Y R) (htot : ∀ v ∈ K, ∃ w, R v w) (hY : Y.AllPer) :
    X.AllPer := by
  intro s ℓ hs
  have hmem : ∀ n, J ≤ n → s n ∈ K := fun n hn =>
    hK (hA.walk_mem h0 (fun n => ⟨ℓ n, hs n⟩) J le_rfl n hn)
  have hs' : (X.restrict K).IsIPath (fun n => s (n + J)) (fun n => ℓ (n + J)) := fun n =>
    adj_restrict.2 ⟨hmem _ (by omega), by simpa [Nat.add_right_comm] using hs (n + J),
      hmem _ (by omega)⟩
  obtain ⟨w, hw⟩ := htot _ (hmem J le_rfl)
  obtain ⟨t, -, ht, -⟩ := hR.exists_iPath hs' (by simpa using hw)
  obtain ⟨n₀, L, hL, hper⟩ := hY t _ ht
  refine ⟨n₀ + J, L, hL, fun m hm => ?_⟩
  have := hper (m - J) (by omega)
  simp only at this
  rwa [show m - J + L + J = m + L by omega, show m - J + J = m by omega] at this

/-! ### Word-labelled graphs -/

section words

variable (E : Finset (V × List A × V))

/-- Reading along a finite word path: `WReads E u x t` iff `x` is the concatenation of the words
of a path from `u` to `t` in the word graph `E`. -/
inductive WReads : V → List A → V → Prop
  | nil (u : V) : WReads u [] u
  | cons {u v t : V} {w x : List A} : (u, w, v) ∈ E → WReads v x t → WReads u (w ++ x) t

/-- Reachability in a word graph. -/
def WReach (v u : V) : Prop := ∃ x, WReads E v x u

/-- **Zero entropy of a word graph**: no vertex has two distinct word arcs that both return to
it. -/
def WNoBranch : Prop :=
  ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.1 = e₂.1 → WReach E e₁.2.2 e₁.1 → WReach E e₂.2.2 e₂.1 → e₁ = e₂

/-- An infinite word path `v` with words `w` and times `t`, whose output `ℓ` is the
concatenation of the words from `t 0` on (the shape of `Oda.WG.Covers`). -/
structure WCovers (ℓ : ℕ → A) (v : ℕ → V) (w : ℕ → List A) (t : ℕ → ℕ) : Prop where
  edge : ∀ i, (v i, w i, v (i + 1)) ∈ E
  time : ∀ i, t (i + 1) = t i + (w i).length
  word : ∀ i k, k < (w i).length → (w i)[k]? = some (ℓ (t i + k))

/-- **The word form of the label form**: every infinite word path has an eventually periodic
output. -/
def WAllPer : Prop := ∀ ℓ v w t, WCovers E ℓ v w t → EvPer ℓ

end words

/-! ### Subdivision -/

section subdivide

variable (E : Finset (V × List A × V))

/-- A bound for the word lengths of `E`. -/
def sdLen : ℕ := E.sup fun e => e.2.1.length

@[category API, AMS 05, group "carry_quotient"]
theorem length_le_sdLen (e : E) : e.1.2.1.length ≤ sdLen E :=
  Finset.le_sup (f := fun e => e.2.1.length) e.2

/-- The vertex of the subdivision reached after reading `i` letters of the arc `e`. -/
def sdPos (e : E) (i : ℕ) : V ⊕ (E × Fin (sdLen E)) :=
  if i = 0 then .inl e.1.1
  else if h : i < e.1.2.1.length then .inr (e, ⟨i, lt_of_lt_of_le h (length_le_sdLen E e)⟩)
  else .inl e.1.2.2

variable {E}

@[category API, AMS 05, group "carry_quotient"]
theorem sdPos_zero (e : E) : sdPos E e 0 = .inl e.1.1 := by simp [sdPos]

@[category API, AMS 05, group "carry_quotient"]
theorem sdPos_of_lt {e : E} {i : ℕ} (h0 : i ≠ 0) (h : i < e.1.2.1.length) :
    sdPos E e i = .inr (e, ⟨i, lt_of_lt_of_le h (length_le_sdLen E e)⟩) := by
  simp [sdPos, h0, h]

@[category API, AMS 05, group "carry_quotient"]
theorem sdPos_length {e : E} (h : e.1.2.1 ≠ []) : sdPos E e e.1.2.1.length = .inl e.1.2.2 := by
  have : e.1.2.1.length ≠ 0 := by simpa using h
  simp [sdPos, this]

@[category API, AMS 05, group "carry_quotient"]
theorem eq_zero_of_sdPos_eq_inl {e : E} {i : ℕ} {u : V} (hi : i < e.1.2.1.length)
    (h : sdPos E e i = .inl u) : i = 0 ∧ e.1.1 = u := by
  by_cases h0 : i = 0
  · subst h0
    rw [sdPos_zero] at h
    exact ⟨rfl, Sum.inl_injective h⟩
  · rw [sdPos_of_lt h0 hi] at h
    exact absurd h Sum.inr_ne_inl

@[category API, AMS 05, group "carry_quotient"]
theorem sdPos_inj {e e' : E} {i i' : ℕ} (h0 : i ≠ 0) (hi : i < e.1.2.1.length)
    (hi' : i' < e'.1.2.1.length) (h : sdPos E e i = sdPos E e' i') : e = e' ∧ i = i' := by
  rw [sdPos_of_lt h0 hi] at h
  by_cases h0' : i' = 0
  · subst h0'
    rw [sdPos_zero] at h
    exact absurd h Sum.inr_ne_inl
  · rw [sdPos_of_lt h0' hi'] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
    exact h

variable [DecidableEq V] [DecidableEq A]

instance sdDecEq : DecidableEq (V ⊕ (E × Fin (sdLen E))) := instDecidableEqSum

variable (E) in
/-- **The subdivision** of the word graph `E` ([LM95, §2.3], [BJG09, §4.5]): each arc
`u —w→ v` becomes a chain of `|w|` letter arcs through the interior vertices `(e, i)`,
`0 < i < |w|`.  Interior vertices `(e, i)` with `i = 0` or `i ≥ |w|` are isolated. -/
def subdivide : CarryGraph (V ⊕ (E × Fin (sdLen E))) A where
  succ z a := match z with
    | .inl u => (E.attach.filter fun e => e.1.1 = u ∧ e.1.2.1[0]? = some a).image
        fun e => sdPos E e 1
    | .inr (e, i) => if 0 < i.1 ∧ e.1.2.1[i.1]? = some a then {sdPos E e (i.1 + 1)} else ∅

/-- **The arcs of the subdivision**: one step along one word arc. -/
@[category API, AMS 05, ref "LM95", group "carry_quotient"]
theorem adj_subdivide {z z' : V ⊕ (E × Fin (sdLen E))} {a : A} :
    (subdivide E).Adj z a z' ↔
      ∃ (e : E) (i : ℕ), e.1.2.1[i]? = some a ∧ z = sdPos E e i ∧ z' = sdPos E e (i + 1) := by
  constructor
  · intro h
    rcases z with u | ⟨e, i⟩
    · simp only [Adj, subdivide, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
        true_and] at h
      obtain ⟨e, ⟨rfl, ha⟩, rfl⟩ := h
      exact ⟨e, 0, ha, (sdPos_zero e).symm, rfl⟩
    · simp only [Adj, subdivide] at h
      split_ifs at h with hc
      · rw [Finset.mem_singleton] at h
        obtain ⟨hi0, ha⟩ := hc
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ha
        exact ⟨e, i.1, ha, by rw [sdPos_of_lt (by omega) hlt], h⟩
      · simp at h
  · rintro ⟨e, i, ha, rfl, rfl⟩
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ha
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [sdPos_zero]
      simp only [Adj, subdivide, Finset.mem_image, Finset.mem_filter, Finset.mem_attach,
        true_and]
      exact ⟨e, ⟨rfl, ha⟩, rfl⟩
    · rw [sdPos_of_lt hi.ne' hlt]
      simp only [Adj, subdivide]
      rw [ite_eq_left ⟨hi, ha⟩]
      exact Finset.mem_singleton_self _

@[category API, AMS 05, group "carry_quotient"]
theorem sd_step_inr {e : E} {i : ℕ} (h0 : i ≠ 0) (hi : i < e.1.2.1.length) {a : A}
    {z : V ⊕ (E × Fin (sdLen E))} (h : (subdivide E).Adj (sdPos E e i) a z) :
    e.1.2.1[i]? = some a ∧ z = sdPos E e (i + 1) := by
  obtain ⟨e', i', ha, he, rfl⟩ := adj_subdivide.1 h
  obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨rfl, rfl⟩ := sdPos_inj h0 hi hlt' he
  exact ⟨ha, rfl⟩

@[category API, AMS 05, group "carry_quotient"]
theorem sd_step_inl {u : V} {a : A} {z : V ⊕ (E × Fin (sdLen E))}
    (h : (subdivide E).Adj (.inl u) a z) :
    ∃ e : E, e.1.1 = u ∧ e.1.2.1[0]? = some a ∧ z = sdPos E e 1 := by
  obtain ⟨e, i, ha, he, rfl⟩ := adj_subdivide.1 h
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨rfl, hu⟩ := eq_zero_of_sdPos_eq_inl hlt he.symm
  exact ⟨e, hu, ha, rfl⟩

/-- Reading the rest of a word arc from position `i`. -/
@[category API, AMS 05, group "carry_quotient"]
theorem reads_sdPos (e : E) : ∀ k i, i + k = e.1.2.1.length →
    (subdivide E).Reads (sdPos E e i) (e.1.2.1.drop i) (sdPos E e e.1.2.1.length)
  | 0, i, h => by
    have : i = e.1.2.1.length := by omega
    subst this
    rw [List.drop_length]
    exact reads_nil.2 rfl
  | k + 1, i, h => by
    have hi : i < e.1.2.1.length := by omega
    rw [List.drop_eq_getElem_cons hi, reads_cons]
    exact ⟨sdPos E e (i + 1), adj_subdivide.2 ⟨e, i, List.getElem?_eq_getElem hi, rfl, rfl⟩,
      reads_sdPos e k (i + 1) (by omega)⟩

variable (hE : ∀ e ∈ E, e.2.1 ≠ [])
include hE

@[category API, AMS 05, group "carry_quotient"]
theorem reads_of_wReads {u t : V} {x : List A} (h : WReads E u x t) :
    (subdivide E).Reads (.inl u) x (.inl t) := by
  induction h with
  | nil u => exact reads_nil.2 rfl
  | @cons u v t w x he _ ih =>
    refine reads_append.2 ⟨.inl v, ?_, ih⟩
    have := reads_sdPos (E := E) ⟨(u, w, v), he⟩ w.length 0 (by simp)
    rwa [sdPos_zero, sdPos_length (hE _ he), List.drop_zero] at this

omit hE in
variable (E) in
/-- The letters still to be read from a vertex of the subdivision before the next old vertex. -/
def sdRest : V ⊕ (E × Fin (sdLen E)) → List A
  | .inl _ => []
  | .inr (e, i) => e.1.2.1.drop i.1

omit hE in
variable (E) in
/-- The next old vertex. -/
def sdExit : V ⊕ (E × Fin (sdLen E)) → V
  | .inl u => u
  | .inr (e, _) => e.1.2.2

omit [DecidableEq V] [DecidableEq A] in
@[category API, AMS 05, group "carry_quotient"]
theorem sdRest_sdPos {e : E} {i : ℕ} (h0 : i ≠ 0) (hi : i ≤ e.1.2.1.length) :
    sdRest E (sdPos E e i) = e.1.2.1.drop i ∧ sdExit E (sdPos E e i) = e.1.2.2 := by
  rcases hi.lt_or_eq with hi | rfl
  · rw [sdPos_of_lt h0 hi]
    exact ⟨rfl, rfl⟩
  · rw [sdPos_length (hE _ e.2), List.drop_length]
    exact ⟨rfl, rfl⟩

/-- Every walk into an old vertex reads the rest of the current word arc, then a word path. -/
@[category API, AMS 05, group "carry_quotient"]
theorem wReads_of_reads : ∀ {x : List A} {z : V ⊕ (E × Fin (sdLen E))} {t : V},
    (subdivide E).Reads z x (.inl t) → ∃ y, x = sdRest E z ++ y ∧ WReads E (sdExit E z) y t
  | [], z, t, h => by
    rw [reads_nil] at h
    subst h
    exact ⟨[], rfl, .nil t⟩
  | a :: x, z, t, h => by
    obtain ⟨z', hz', hr⟩ := reads_cons.1 h
    obtain ⟨y, hxy, hy⟩ := wReads_of_reads hr
    obtain ⟨e, i, ha, rfl, rfl⟩ := adj_subdivide.1 hz'
    obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hr1, hr2⟩ := sdRest_sdPos hE (e := e) (i := i + 1) (by omega) (by omega)
    rw [hr1] at hxy
    rw [hr2] at hy
    subst hxy
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [sdPos_zero]
      refine ⟨e.1.2.1 ++ y, ?_, .cons e.2 hy⟩
      show a :: (e.1.2.1.drop 1 ++ y) = [] ++ (e.1.2.1 ++ y)
      rw [List.nil_append, ← hai, ← List.cons_append, ← List.drop_eq_getElem_cons hi,
        List.drop_zero]
    · rw [sdPos_of_lt hi0.ne' hi]
      refine ⟨y, ?_, hy⟩
      show a :: (e.1.2.1.drop (i + 1) ++ y) = e.1.2.1.drop i ++ y
      rw [← hai, ← List.cons_append, ← List.drop_eq_getElem_cons hi]

/-- **G-2 (i): the subdivision reads exactly the word-path concatenations** between old
vertices. -/
@[category textbook, AMS 05 68, ref "LM95" "BJG09", group "carry_quotient"]
theorem reads_subdivide_iff {u t : V} {x : List A} :
    (subdivide E).Reads (.inl u) x (.inl t) ↔ WReads E u x t :=
  ⟨fun h => by
    obtain ⟨y, rfl, hy⟩ := wReads_of_reads hE h
    exact hy, reads_of_wReads hE⟩

omit hE in
theorem reads_eq_or_adj : ∀ {x : List A} {z z' : V ⊕ (E × Fin (sdLen E))},
    (subdivide E).Reads z x z' → z' = z ∨ ∃ z₀ a, (subdivide E).Adj z₀ a z'
  | [], _, _, h => .inl (reads_nil.1 h)
  | a :: x, z, _, h => by
    obtain ⟨z₁, hz₁, hr⟩ := reads_cons.1 h
    rcases reads_eq_or_adj hr with rfl | h'
    · exact .inr ⟨z, a, hz₁⟩
    · exact .inr h'

/-- From every vertex reached from an old vertex, the rest of the current word arc can be
read. -/
@[category API, AMS 05, group "carry_quotient"]
theorem reads_sdRest {u : V} {x : List A} {z : V ⊕ (E × Fin (sdLen E))}
    (h : (subdivide E).Reads (.inl u) x z) :
    (subdivide E).Reads z (sdRest E z) (.inl (sdExit E z)) := by
  rcases reads_eq_or_adj h with rfl | ⟨z₀, a, hz⟩
  · exact reads_nil.2 rfl
  · obtain ⟨e, i, ha, -, rfl⟩ := adj_subdivide.1 hz
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hr1, hr2⟩ := sdRest_sdPos hE (e := e) (i := i + 1) (by omega) (by omega)
    rw [hr1, hr2, ← sdPos_length (hE _ e.2)]
    exact reads_sdPos e (e.1.2.1.length - (i + 1)) (i + 1) (by omega)

/-- **G-2 (iv), languages**: the language of the subdivision at an old vertex is the set of
prefixes of word-path outputs. -/
@[category textbook, AMS 05 68, ref "LM95", group "carry_quotient"]
theorem mem_langFrom_subdivide {u : V} {x : List A} :
    x ∈ (subdivide E).langFrom (.inl u) ↔ ∃ y t, WReads E u (x ++ y) t := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨sdRest E z, sdExit E z,
      (reads_subdivide_iff hE).1 (reads_append.2 ⟨z, hz, reads_sdRest hE hz⟩)⟩
  · rintro ⟨y, t, h⟩
    exact IsWord.of_append ⟨_, (reads_subdivide_iff hE).2 h⟩

/-- **The prefixes of the outputs of a finite word graph form a sofic language.** -/
@[category textbook, AMS 05 68, ref "LM95", group "carry_quotient"]
theorem sofic_wordLang [Finite V] (u : V) : Sofic {x | ∃ y t, WReads E u (x ++ y) t} := by
  have : (subdivide E).langFrom (.inl u) = {x | ∃ y t, WReads E u (x ++ y) t} :=
    Set.ext fun _ => mem_langFrom_subdivide hE
  rw [← this]
  exact sofic_of_finite _ _

omit [DecidableEq V] [DecidableEq A] in
/-- Distinct word arcs out of one vertex leave it along distinct letter arcs. -/
@[category API, AMS 05, group "carry_quotient"]
theorem eq_of_sdPos_one {e₁ e₂ : E} (h1 : e₁.1.1 = e₂.1.1)
    (ha : e₁.1.2.1[0]? = e₂.1.2.1[0]?) (h : sdPos E e₁ 1 = sdPos E e₂ 1) : e₁ = e₂ := by
  have p₁ := List.length_pos_of_ne_nil (hE _ e₁.2)
  have p₂ := List.length_pos_of_ne_nil (hE _ e₂.2)
  have one : ∀ e : E, e.1.2.1.length = 1 → sdPos E e 1 = .inl e.1.2.2 := by
    intro e he
    rw [← he]
    exact sdPos_length (hE _ e.2)
  rcases (Nat.succ_le_of_lt p₁).lt_or_eq with l₁ | l₁ <;>
    rcases (Nat.succ_le_of_lt p₂).lt_or_eq with l₂ | l₂
  · exact (sdPos_inj one_ne_zero l₁ l₂ h).1
  · rw [sdPos_of_lt one_ne_zero l₁, one e₂ l₂.symm] at h
    exact absurd h Sum.inr_ne_inl
  · rw [sdPos_of_lt one_ne_zero l₂, one e₁ l₁.symm] at h
    exact absurd h.symm Sum.inr_ne_inl
  · rw [one e₁ l₁.symm, one e₂ l₂.symm] at h
    obtain ⟨b₁, hb₁⟩ := List.length_eq_one_iff.1 l₁.symm
    obtain ⟨b₂, hb₂⟩ := List.length_eq_one_iff.1 l₂.symm
    rw [hb₁, hb₂] at ha
    have hw : e₁.1.2.1 = e₂.1.2.1 := by
      rw [hb₁, hb₂]
      simpa using ha
    exact Subtype.ext (Prod.ext h1 (Prod.ext hw (Sum.inl_injective h)))

/-- **G-2 (iii): zero entropy of the subdivision is `WNoBranch`.** -/
@[category textbook, AMS 05 37, ref "LM95" "BJG09", group "carry_quotient"]
theorem lnoBranch_subdivide_iff : (subdivide E).LNoBranch ↔ WNoBranch E := by
  have back : ∀ (e : E) {u : V}, (subdivide E).Reach (sdPos E e 1) (.inl u) →
      WReach E e.1.2.2 u := by
    intro e u h
    obtain ⟨x, hx⟩ := reach_iff_exists_reads.1 h
    obtain ⟨y, -, hy⟩ := wReads_of_reads hE hx
    have hp := List.length_pos_of_ne_nil (hE _ e.2)
    rw [(sdRest_sdPos hE (e := e) one_ne_zero (by omega)).2] at hy
    exact ⟨y, hy⟩
  have fwd : ∀ (e : E) {u : V}, WReach E e.1.2.2 u →
      (subdivide E).Reach (sdPos E e 1) (.inl u) := by
    intro e u ⟨y, hy⟩
    have hp := List.length_pos_of_ne_nil (hE _ e.2)
    have h1 := reads_sdPos e (e.1.2.1.length - 1) 1 (by omega)
    rw [sdPos_length (hE _ e.2)] at h1
    exact reach_iff_exists_reads.2 ⟨_, reads_append.2 ⟨_, h1, reads_of_wReads hE hy⟩⟩
  constructor
  · intro h e₁ he₁ e₂ he₂ hsrc r₁ r₂
    have hp₁ := List.length_pos_of_ne_nil (hE _ he₁)
    have hp₂ := List.length_pos_of_ne_nil (hE _ he₂)
    have a₁ : (subdivide E).Adj (.inl e₁.1) e₁.2.1[0] (sdPos E ⟨e₁, he₁⟩ 1) := by
      rw [← sdPos_zero ⟨e₁, he₁⟩]
      exact adj_subdivide.2 ⟨⟨e₁, he₁⟩, 0, List.getElem?_eq_getElem hp₁, rfl, rfl⟩
    have a₂ : (subdivide E).Adj (.inl e₁.1) e₂.2.1[0] (sdPos E ⟨e₂, he₂⟩ 1) := by
      rw [hsrc, ← sdPos_zero ⟨e₂, he₂⟩]
      exact adj_subdivide.2 ⟨⟨e₂, he₂⟩, 0, List.getElem?_eq_getElem hp₂, rfl, rfl⟩
    obtain ⟨hab, hz⟩ := h _ _ _ _ _ a₁ a₂ (fwd ⟨e₁, he₁⟩ r₁) (by rw [hsrc]; exact fwd ⟨e₂, he₂⟩ r₂)
    have := eq_of_sdPos_one hE (e₁ := ⟨e₁, he₁⟩) (e₂ := ⟨e₂, he₂⟩) hsrc
      (by rw [List.getElem?_eq_getElem hp₁, List.getElem?_eq_getElem hp₂, hab]) hz
    exact congrArg Subtype.val this
  · intro h z a b z₁ z₂ h₁ h₂ r₁ r₂
    obtain ⟨e, i, ha, rfl, rfl⟩ := adj_subdivide.1 h₁
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 ha
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [sdPos_zero] at h₂ r₂ r₁
      obtain ⟨e₂, hsrc, hb, rfl⟩ := sd_step_inl h₂
      have r₁' := back e r₁
      have r₂' := back e₂ (u := e₂.1.1) (by rw [hsrc]; exact r₂)
      have he : e = e₂ := Subtype.ext (h e.1 e.2 e₂.1 e₂.2 hsrc.symm r₁' r₂')
      subst he
      rw [ha] at hb
      exact ⟨Option.some_injective _ hb, rfl⟩
    · obtain ⟨hb, rfl⟩ := sd_step_inr hi0.ne' hi h₂
      rw [ha] at hb
      exact ⟨Option.some_injective _ hb, rfl⟩

omit hE in
/-- Following the interior of a word arc along an infinite path. -/
@[category API, AMS 05, group "carry_quotient"]
theorem sd_follow {s : ℕ → V ⊕ (E × Fin (sdLen E))} {ℓ : ℕ → A}
    (hs : (subdivide E).IsIPath s ℓ) (e : E) :
    ∀ j n i, i ≠ 0 → i + j ≤ e.1.2.1.length → s n = sdPos E e i →
      s (n + j) = sdPos E e (i + j) ∧ ∀ m < j, e.1.2.1[i + m]? = some (ℓ (n + m))
  | 0, n, i, _, _, h => ⟨h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | j + 1, n, i, h0, hj, h => by
    obtain ⟨h1, h2⟩ := sd_follow hs e j n i h0 (by omega) h
    have hstep := hs (n + j)
    rw [h1] at hstep
    obtain ⟨hl, hnext⟩ := sd_step_inr (by omega) (by omega) hstep
    refine ⟨by rw [← add_assoc, hnext, add_assoc], fun m hm => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact h2 m hm
    · exact hl

/-- From an old vertex an infinite path runs through one whole word arc. -/
@[category API, AMS 05, group "carry_quotient"]
theorem sd_arc {s : ℕ → V ⊕ (E × Fin (sdLen E))} {ℓ : ℕ → A}
    (hs : (subdivide E).IsIPath s ℓ) {n : ℕ} {u : V} (h : s n = .inl u) :
    ∃ e : E, e.1.1 = u ∧ s (n + e.1.2.1.length) = .inl e.1.2.2 ∧
      ∀ m < e.1.2.1.length, e.1.2.1[m]? = some (ℓ (n + m)) := by
  have hstep := hs n
  rw [h] at hstep
  obtain ⟨e, hu, h0, h1⟩ := sd_step_inl hstep
  have hp := List.length_pos_of_ne_nil (hE _ e.2)
  obtain ⟨hf1, hf2⟩ := sd_follow hs e (e.1.2.1.length - 1) (n + 1) 1 one_ne_zero (by omega) h1
  refine ⟨e, hu, ?_, fun m hm => ?_⟩
  · rw [show n + e.1.2.1.length = n + 1 + (e.1.2.1.length - 1) by omega, hf1,
      show 1 + (e.1.2.1.length - 1) = e.1.2.1.length by omega, sdPos_length (hE _ e.2)]
  · rcases m with _ | m
    · simpa using h0
    · have := hf2 m (by omega)
      rwa [show 1 + m = m + 1 by omega, show n + 1 + m = n + (m + 1) by omega] at this

/-- **G-2 (ii): the label form of the subdivision is the word form.** -/
@[category textbook, AMS 05 37, ref "LM95" "Oda26", group "carry_quotient"]
theorem allPer_subdivide_iff : (subdivide E).AllPer ↔ WAllPer E := by
  classical
  constructor
  · -- a word path gives a path of the subdivision
    intro h ℓ v w t hc
    have hpos : ∀ i, 0 < (w i).length := fun i => List.length_pos_of_ne_nil (hE _ (hc.edge i))
    let e : ℕ → E := fun i => ⟨(v i, w i, v (i + 1)), hc.edge i⟩
    let nx : ℕ × ℕ → ℕ × ℕ := fun p =>
      if p.2 + 1 < (w p.1).length then (p.1, p.2 + 1) else (p.1 + 1, 0)
    let st : ℕ → ℕ × ℕ := fun n => nx^[n] (0, 0)
    have hst : ∀ n, st (n + 1) = nx (st n) := fun n => Function.iterate_succ_apply' nx n (0, 0)
    have inv : ∀ n, (st n).2 < (w (st n).1).length ∧ t (st n).1 + (st n).2 = t 0 + n := by
      intro n
      induction n with
      | zero => exact ⟨hpos 0, rfl⟩
      | succ n ih =>
        rw [hst]
        simp only [nx]
        split_ifs with hk
        · exact ⟨hk, by simp only; omega⟩
        · refine ⟨hpos _, ?_⟩
          simp only
          rw [hc.time]
          omega
    let s : ℕ → V ⊕ (E × Fin (sdLen E)) := fun n => sdPos E (e (st n).1) (st n).2
    have hpath : (subdivide E).IsIPath s fun n => ℓ (t 0 + n) := by
      intro n
      obtain ⟨hk, ht⟩ := inv n
      have hnext : s (n + 1) = sdPos E (e (st n).1) ((st n).2 + 1) := by
        simp only [s]
        rw [hst]
        simp only [nx]
        split_ifs with hk'
        · rfl
        · have hl : (st n).2 + 1 = (w (st n).1).length := by omega
          rw [sdPos_zero, hl]
          exact (sdPos_length (hE _ (e _).2)).symm
      rw [hnext]
      refine adj_subdivide.2 ⟨e (st n).1, (st n).2, ?_, rfl, rfl⟩
      have := hc.word _ _ hk
      rw [ht] at this
      exact this
    obtain ⟨n₀, L, hL, hper⟩ := h s _ hpath
    refine ⟨t 0 + n₀, L, hL, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = t 0 + k := ⟨m - t 0, by omega⟩
    have := hper k (by omega)
    simp only at this
    rwa [← add_assoc] at this
  · -- a path of the subdivision gives a word path
    intro h s ℓ hs
    -- reach an old vertex
    obtain ⟨τ, u₀, hτ⟩ : ∃ τ u, s τ = .inl u := by
      obtain ⟨e, i, ha, he, -⟩ := adj_subdivide.1 (hs 0)
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 ha
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨0, _, by rw [he, sdPos_zero]⟩
      · obtain ⟨hf, -⟩ := sd_follow hs e (e.1.2.1.length - i) 0 i hi0.ne' (by omega) he
        refine ⟨0 + (e.1.2.1.length - i), e.1.2.2, ?_⟩
        rw [hf, show i + (e.1.2.1.length - i) = e.1.2.1.length by omega,
          sdPos_length (hE _ e.2)]
    obtain ⟨e₀, -⟩ := sd_arc hE hs hτ
    let P : ℕ → E → Prop := fun n e => s n = .inl e.1.1 ∧
      s (n + e.1.2.1.length) = .inl e.1.2.2 ∧
        ∀ m < e.1.2.1.length, e.1.2.1[m]? = some (ℓ (n + m))
    let ch : ℕ → E := fun n => if hx : ∃ e, P n e then hx.choose else e₀
    have hch : ∀ n u, s n = .inl u → P n (ch n) := by
      intro n u hn
      have hx : ∃ e, P n e := by
        obtain ⟨e, he, h1, h2⟩ := sd_arc hE hs hn
        exact ⟨e, by rw [hn, he], h1, h2⟩
      simp only [ch, dite_eq_left hx]
      exact hx.choose_spec
    let T : ℕ → ℕ := fun i => Nat.rec τ (fun _ n => n + (ch n).1.2.1.length) i
    have hT : ∀ i, T (i + 1) = T i + (ch (T i)).1.2.1.length := fun _ => rfl
    have hP : ∀ i, P (T i) (ch (T i)) := by
      intro i
      induction i with
      | zero => exact hch τ u₀ hτ
      | succ i ih => exact hch _ _ (by rw [hT]; exact ih.2.1)
    refine h ℓ (fun i => (ch (T i)).1.1) (fun i => (ch (T i)).1.2.1) T ⟨fun i => ?_, hT,
      fun i k hk => (hP i).2.2 k hk⟩
    have h1 := (hP (i + 1)).1
    rw [hT, (hP i).2.1] at h1
    have h2 : (ch (T i)).1.2.2 = (ch (T (i + 1))).1.1 := Sum.inl_injective h1
    rw [← h2]
    exact (ch (T i)).2

/-- **[Oda26] Theorem 21 for finite word graphs**: the word form of the label form holds iff the
subset construction of the subdivision has no branching inside a strong component. -/
@[category textbook, AMS 05 37, ref "LM95" "Oda26", group "carry_quotient"]
theorem wAllPer_iff_det [Fintype V] : WAllPer E ↔ (subdivide E).det.LNoBranch :=
  (allPer_subdivide_iff hE).symm.trans (determinization.out 1 3)

end subdivide

end CarryGraph
