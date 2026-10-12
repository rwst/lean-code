/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Product

/-!
# Covers of dynamical systems ([LM95] §§1.5, 6.5)

A **system** is a state space `S` with maps `f a : S → S` indexed by the letters and an
admissibility predicate `adm : S → A → Prop` ("the step `a` may be taken at `x`").  A carry graph
`X` **covers** the system through `ρ : V → Set S` if every admissible step from `ρ v` is
shadowed by an arc out of `v`:

  `x ∈ ρ v`, `adm x a`  ⟹  `f a x ∈ ρ w` for some `w ∈ succ v a`.

This is the shape of every "the real orbit is a path" lemma in the corpus.  The converse,
**realisability** (`Realizes`), says that every word of `X` from `v` is the itinerary of some
point of `ρ v`; it is what lower bounds need.

## Main results

* **Shadowing** (`Cover.follows`, `Cover.exists_iPath`): a finite admissible run is read by a
  path of `X`; an orbit admissible forever is an infinite labelled path of `X` (no compactness
  is needed: the path is built step by step).
* **Transfer theorems**, the generic forms of what each corpus root proves per certificate:
  - `Cover.evPer_of_allPer`: if `X` has the label form, every admissible-forever label sequence
    is eventually periodic (and so if `X.LNoBranch`, or `X.det.LNoBranch`);
  - `Cover.escape_of_core_empty`, `Cover.escape_of_peel`: if the core is empty, no point of
    `⋃ ρ` survives `|V|` admissible steps, and a point of `ρ v` with `v ∉ peel k` does not
    survive `k`;
  - `Cover.ncard_orbitWords_le`, `Cover.ncard_orbitLang_le`, `Cover.orbitEntropy_le`: the
    itineraries of length `n` number at most the paths, so their growth rate is at most
    `X.entropy`;
  - `Cover.orbitEntropy_eq` (exact covers): with `Realizes` and a right-resolving `X`, the growth
    rate of the itineraries *is* `X.entropy`;
  - `Cover.not_allPer_of_horseshoe`: a horseshoe of a right-resolving graph `Y` that is realised
    forever (`RealizesInf`) inside `⋃ ρ` rules out the label form for **every** cover `X` of the
    same system.  This is the DubC2 obstruction principle and the shape of [Oda26] Thm 42.
* **Constructions** (`Cover.mono`, `Cover.comap`, `Cover.map`, `Cover.labelProduct`,
  `Cover.piProduct`, `Cover.det`): a supergraph, a pull-back along a semiconjugacy, a
  homomorphic image, the label product of two covers (the
  residue × cell principle of Chapter 8) and the subset construction are covers again.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [Oda26] Odagiri, floor certificates for `⌊ξ(p/q)ⁿ⌋`, 2026.
-/

open Filter ENNReal ExpGrowth

namespace CarryGraph

variable {V W S A : Type*} {X : CarryGraph V A} {Y : CarryGraph W A}
  {f : A → S → S} {adm : S → A → Prop} {ρ : V → Set S}

/-! ### Runs, itineraries and orbits -/

variable (f) in
/-- The point reached from `x` along the word `w`. -/
def run : S → List A → S
  | x, [] => x
  | x, a :: w => run (f a x) w

variable (f adm) in
/-- `x` **follows** `w`: every step of the run of `w` from `x` is admissible. -/
def Follows : S → List A → Prop
  | _, [] => True
  | x, a :: w => adm x a ∧ Follows (f a x) w

variable (f) in
/-- The orbit of `x` along the label sequence `ℓ`. -/
def orbit (x : S) (ℓ : ℕ → A) : ℕ → S
  | 0 => x
  | n + 1 => f (ℓ n) (orbit x ℓ n)

variable (f adm) in
/-- The orbit of `x` along `ℓ` is admissible at every step. -/
def AdmForever (x : S) (ℓ : ℕ → A) : Prop := ∀ n, adm (orbit f x ℓ n) (ℓ n)

@[category API, AMS 37, group "carry_cover"]
theorem orbit_succ' (x : S) (ℓ : ℕ → A) : ∀ n,
    orbit f x ℓ (n + 1) = orbit f (f (ℓ 0) x) (fun i => ℓ (i + 1)) n
  | 0 => rfl
  | n + 1 => by rw [orbit, orbit_succ' x ℓ n]; rfl

@[category API, AMS 37, group "carry_cover"]
theorem AdmForever.tail {x : S} {ℓ : ℕ → A} (h : AdmForever f adm x ℓ) :
    AdmForever f adm (f (ℓ 0) x) (fun i => ℓ (i + 1)) := fun n => by
  rw [← orbit_succ']; exact h (n + 1)

/-- The first `n` letters of a sequence. -/
def pre (ℓ : ℕ → A) (n : ℕ) : List A := List.ofFn fun i : Fin n => ℓ i

@[category API, AMS 37, group "carry_cover"]
theorem length_pre (ℓ : ℕ → A) (n : ℕ) : (pre ℓ n).length = n := List.length_ofFn

@[category API, AMS 37, group "carry_cover"]
theorem pre_succ (ℓ : ℕ → A) (n : ℕ) : pre ℓ (n + 1) = ℓ 0 :: pre (fun i => ℓ (i + 1)) n := by
  simp [pre, List.ofFn_succ]

/-- An admissible-forever orbit follows every prefix of its label sequence. -/
@[category API, AMS 37, group "carry_cover"]
theorem AdmForever.follows : ∀ {x : S} {ℓ : ℕ → A} (_ : AdmForever f adm x ℓ) (n : ℕ),
    Follows f adm x (pre ℓ n)
  | _, _, _, 0 => trivial
  | _, _, h, n + 1 => by
    rw [pre_succ]
    exact ⟨h 0, h.tail.follows n⟩

/-! ### Covers -/

variable (X f adm ρ) in
/-- `X` **covers** the system `(S, f, adm)` through `ρ`: an admissible step from `ρ v` is
shadowed by an arc out of `v`. -/
structure Cover : Prop where
  step : ∀ v a x, x ∈ ρ v → adm x a → ∃ w ∈ X.succ v a, f a x ∈ ρ w

variable (X f adm ρ) in
/-- **Realisability**: every word of `X` from `v` is followed by some point of `ρ v`. -/
def Realizes : Prop := ∀ v (w : List A), X.IsWord v w → ∃ x ∈ ρ v, Follows f adm x w

variable (X f adm ρ) in
/-- **Realisability forever**: every infinite labelled path of `X` is the itinerary of an orbit
admissible forever that starts in `ρ` of its first vertex. -/
def RealizesInf : Prop := ∀ s ℓ, X.IsIPath s ℓ → ∃ x ∈ ρ (s 0), AdmForever f adm x ℓ

/-- **Finite shadowing**: a run that follows `w` from `ρ v` is read by a path from `v`, ending at
a vertex whose `ρ` contains the end of the run. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.follows (h : Cover X f adm ρ) :
    ∀ {v : V} {x : S} {w : List A}, x ∈ ρ v → Follows f adm x w →
      ∃ u, X.Reads v w u ∧ run f x w ∈ ρ u
  | v, _, [], hx, _ => ⟨v, rfl, hx⟩
  | v, x, a :: w, hx, ⟨ha, hw⟩ => by
    obtain ⟨t, ht, hft⟩ := h.step v a x hx ha
    obtain ⟨u, hu, hru⟩ := h.follows hft hw
    exact ⟨u, ⟨t, ht, hu⟩, hru⟩

@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.isWord (h : Cover X f adm ρ) {v : V} {x : S} {w : List A} (hx : x ∈ ρ v)
    (hw : Follows f adm x w) : X.IsWord v w :=
  let ⟨u, hu, _⟩ := h.follows hx hw
  ⟨u, hu⟩

/-- **Shadowing**: an orbit admissible forever from `ρ v` is an infinite labelled path of `X`
from `v`, which stays in `ρ` along the orbit. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.exists_iPath (h : Cover X f adm ρ) {v : V} {x : S} {ℓ : ℕ → A} (hx : x ∈ ρ v)
    (hadm : AdmForever f adm x ℓ) :
    ∃ s : ℕ → V, s 0 = v ∧ X.IsIPath s ℓ ∧ ∀ n, orbit f x ℓ n ∈ ρ (s n) := by
  classical
  let F : ∀ n, {u // orbit f x ℓ n ∈ ρ u} → {u // orbit f x ℓ (n + 1) ∈ ρ u} := fun n u =>
    ⟨Classical.choose (h.step u.1 (ℓ n) _ u.2 (hadm n)),
      (Classical.choose_spec (h.step u.1 (ℓ n) _ u.2 (hadm n))).2⟩
  let t : ∀ n, {u // orbit f x ℓ n ∈ ρ u} := fun n =>
    Nat.rec (motive := fun n => {u // orbit f x ℓ n ∈ ρ u}) ⟨v, hx⟩ F n
  refine ⟨fun n => (t n).1, rfl, fun n => ?_, fun n => (t n).2⟩
  exact (Classical.choose_spec (h.step (t n).1 (ℓ n) _ (t n).2 (hadm n))).1

/-! ### Constructions of covers -/

/-- A supergraph of a cover is a cover. -/
@[category API, AMS 37 05, group "carry_cover"]
theorem Cover.mono {X' : CarryGraph V A} (h : Cover X f adm ρ)
    (hX : ∀ v a, X.succ v a ⊆ X'.succ v a) : Cover X' f adm ρ :=
  ⟨fun v a x hx ha =>
    let ⟨w, hw, hfw⟩ := h.step v a x hx ha
    ⟨w, hX v a hw, hfw⟩⟩

/-- A cover stays a cover when fewer steps are admissible. -/
@[category API, AMS 37 05, group "carry_cover"]
theorem Cover.mono_adm {adm' : S → A → Prop} (h : Cover X f adm ρ)
    (had : ∀ x a, adm' x a → adm x a) : Cover X f adm' ρ :=
  ⟨fun v a x hx ha => h.step v a x hx (had x a ha)⟩

/-- **Pull-back along a semiconjugacy**: if `π` maps admissible steps of `(S', f', adm')` to
admissible steps of `(S, f, adm)`, a cover of the second system covers the first through the
preimages. -/
@[category API, AMS 37 05, group "carry_cover"]
theorem Cover.comap {S' : Type*} {f' : A → S' → S'} {adm' : S' → A → Prop}
    (h : Cover X f adm ρ) (π : S' → S)
    (hπ : ∀ a x, adm' x a → adm (π x) a ∧ π (f' a x) = f a (π x)) :
    Cover X f' adm' (fun v => π ⁻¹' ρ v) :=
  ⟨fun v a x hx ha =>
    let ⟨w, hw, hfw⟩ := h.step v a (π x) hx (hπ a x ha).1
    ⟨w, hw, show π (f' a x) ∈ ρ w from (hπ a x ha).2 ▸ hfw⟩⟩

/-- The image of a cover under a homomorphism is a cover, through the union of the fibres. -/
@[category API, AMS 37 05, group "carry_cover"]
theorem Cover.map (h : Cover X f adm ρ) (g : Hom X Y) :
    Cover Y f adm (fun u => {x | ∃ v, g.toFun v = u ∧ x ∈ ρ v}) :=
  ⟨fun _ a x ⟨v, hv, hx⟩ ha =>
    let ⟨w, hw, hfw⟩ := h.step v a x hx ha
    ⟨g.toFun w, hv ▸ g.map_adj hw, w, rfl, hfw⟩⟩

/-- **Covers pass along simulations**: if `R` simulates `X` by `Y`, then `Y` covers the same
system through `σ w = ⋃ {ρ v | R v w}`.  (`Cover.map` is the case of a homomorphism; the
subset automata of entropy certificates are the case `R v S ↔ v ∈ S`.) -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.ofSimulation {R : V → W → Prop} (h : Cover X f adm ρ) (hR : IsSimulation X Y R) :
    Cover Y f adm (fun w => {x | ∃ v, R v w ∧ x ∈ ρ v}) :=
  ⟨fun w a x ⟨v, hvw, hx⟩ ha =>
    let ⟨v', hv', hfx⟩ := h.step v a x hx ha
    let ⟨w', hw', hR'⟩ := hR v w hvw a v' hv'
    ⟨w', hw', v', hR', hfx⟩⟩

/-- **Covers lift to the line graph** (and, by iteration, to every higher block graph
[LM95, §2.3]): a vertex of `X.lineGraph` is an arc `u →a v`, and it covers the points of `ρ v`.
Points of `ρ v` are covered as soon as `v` has an incoming arc. -/
@[category textbook, AMS 37 05, ref "LM95" "BJG09", group "carry_cover"]
theorem Cover.lineGraph [DecidableEq V] [DecidableEq A] (h : Cover X f adm ρ) :
    Cover X.lineGraph f adm (fun t => {x | X.Adj t.1 t.2.1 t.2.2 ∧ x ∈ ρ t.2.2}) := by
  refine ⟨fun ⟨u, b, v⟩ a x ⟨huv, hx⟩ ha => ?_⟩
  obtain ⟨w, hw, hfx⟩ := h.step v a x hx ha
  exact ⟨(v, a, w), adj_lineGraph.2 ⟨huv, rfl, rfl, hw⟩, hw, hfx⟩

/-- **The product principle**: covers of the same system by `X` and by `Y` give a cover by the
label product, through the intersections.  In Chapter 8 this is residue × cell. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.labelProduct {σ : W → Set S} (hX : Cover X f adm ρ) (hY : Cover Y f adm σ) :
    Cover (X.labelProduct Y) f adm (fun p => ρ p.1 ∩ σ p.2) :=
  ⟨fun p a x hx ha =>
    let ⟨w₁, hw₁, hf₁⟩ := hX.step p.1 a x hx.1 ha
    let ⟨w₂, hw₂, hf₂⟩ := hY.step p.2 a x hx.2 ha
    ⟨(w₁, w₂), Finset.mem_product.2 ⟨hw₁, hw₂⟩, hf₁, hf₂⟩⟩

/-- The indexed version of `Cover.labelProduct`. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.piProduct {ι : Type*} [Fintype ι] [DecidableEq ι] {Vs : ι → Type*}
    [∀ i, DecidableEq (Vs i)] {G : ∀ i, CarryGraph (Vs i) A} {σ : ∀ i, Vs i → Set S}
    (hG : ∀ i, Cover (G i) f adm (σ i)) :
    Cover (CarryGraph.piProduct G) f adm (fun p => {x | ∀ i, x ∈ σ i (p i)}) := by
  refine ⟨fun p a x hx ha => ?_⟩
  choose w hw hfw using fun i => (hG i).step (p i) a x (hx i) ha
  exact ⟨w, Fintype.mem_piFinset.2 hw, hfw⟩

/-- **Covers determinize**: the subset construction covers the system through the unions. -/
@[category textbook, AMS 37 05 68, ref "LM95", group "carry_cover"]
theorem Cover.det [DecidableEq V] (h : Cover X f adm ρ) :
    Cover X.det f adm (fun T => {x | ∃ v ∈ T, x ∈ ρ v}) := by
  refine ⟨fun T a x ⟨v, hv, hx⟩ ha => ?_⟩
  obtain ⟨w, hw, hfw⟩ := h.step v a x hx ha
  have hwT : w ∈ X.detStep T a := mem_detStep.2 ⟨v, hv, hw⟩
  exact ⟨X.detStep T a, adj_det.2 ⟨rfl, ⟨w, hwT⟩⟩, w, hwT, hfw⟩

/-! ### Transfer: periodicity -/

/-- **Transfer of the label form**: if `X` has the label form, every admissible-forever label
sequence from `⋃ ρ` is eventually periodic. -/
@[category textbook, AMS 37 05 11, ref "LM95", group "carry_cover"]
theorem Cover.evPer_of_allPer (h : Cover X f adm ρ) (hX : X.AllPer) {v : V} {x : S}
    {ℓ : ℕ → A} (hx : x ∈ ρ v) (hadm : AdmForever f adm x ℓ) : EvPer ℓ :=
  let ⟨_, _, hs, _⟩ := h.exists_iPath hx hadm
  hX _ _ hs

/-- **Transfer of zero entropy**: on a finite cover with no labelled branching, every
admissible-forever label sequence is eventually periodic. -/
@[category textbook, AMS 37 05 11, ref "LM95", group "carry_cover"]
theorem Cover.evPer_of_lnoBranch [Finite V] (h : Cover X f adm ρ) (hX : X.LNoBranch) {v : V}
    {x : S} {ℓ : ℕ → A} (hx : x ∈ ρ v) (hadm : AdmForever f adm x ℓ) : EvPer ℓ :=
  h.evPer_of_allPer (allPer_of_lnoBranch hX) hx hadm

/-- **Transfer through the subset construction**: zero entropy of `det X` suffices. -/
@[category textbook, AMS 37 05 11, ref "LM95", group "carry_cover"]
theorem Cover.evPer_of_det [Fintype V] [DecidableEq V] (h : Cover X f adm ρ)
    (hX : X.det.LNoBranch) {v : V} {x : S} {ℓ : ℕ → A} (hx : x ∈ ρ v)
    (hadm : AdmForever f adm x ℓ) : EvPer ℓ :=
  h.evPer_of_allPer ((determinization (X := X)).out 3 1 |>.1 hX) hx hadm

/-- **The obstruction**: one admissible-forever orbit from `⋃ ρ` with a label sequence that is
not eventually periodic rules out the label form of `X`. -/
@[category textbook, AMS 37 05 11, ref "LM95", group "carry_cover"]
theorem Cover.not_allPer (h : Cover X f adm ρ) {v : V} {x : S} {ℓ : ℕ → A} (hx : x ∈ ρ v)
    (hadm : AdmForever f adm x ℓ) (hℓ : ¬ EvPer ℓ) : ¬ X.AllPer :=
  fun hX => hℓ (h.evPer_of_allPer hX hx hadm)

/-- **A realised horseshoe kills the label form of every cover.**  Let `Y` be a right-resolving
finite carry graph that realises its infinite paths inside `⋃ ρ` (`RealizesInf`).  Two distinct
petals of a horseshoe of `Y` give an admissible-forever orbit whose label sequence is not
eventually periodic, so no cover `X` of the same system has the label form.  This is the DubC2
obstruction principle; [Oda26] Thm 42 has this shape. -/
@[category textbook, AMS 37 05 11, ref "LM95" "Oda26", group "carry_cover"]
theorem Cover.not_allPer_of_horseshoe [Finite W] {σ : W → Set S} (h : Cover X f adm ρ)
    (hY : RealizesInf Y f adm σ) (hrr : Y.RightResolving) {u : W}
    (hσ : ∀ x ∈ σ u, ∃ v, x ∈ ρ v) {ι : Type*} (H : Y.Horseshoe u ι) {i j : ι} (hij : i ≠ j) :
    ¬ X.AllPer := by
  obtain ⟨s, ℓ, hs0, hs, hne⟩ := H.exists_not_evPer hij
  obtain ⟨x, hx, hadm⟩ := hY s ℓ hs
  obtain ⟨v, hv⟩ := hσ x (hs0 ▸ hx)
  exact h.not_allPer hv hadm fun hl => hne (evPer_path_of_rr hrr hs hl)

/-- The obstruction in its zero-entropy form. -/
@[category textbook, AMS 37 05 11, ref "LM95" "Oda26", group "carry_cover"]
theorem Cover.not_lnoBranch_of_horseshoe [Finite V] [Finite W] {σ : W → Set S}
    (h : Cover X f adm ρ) (hY : RealizesInf Y f adm σ) (hrr : Y.RightResolving) {u : W}
    (hσ : ∀ x ∈ σ u, ∃ v, x ∈ ρ v) {ι : Type*} (H : Y.Horseshoe u ι) {i j : ι} (hij : i ≠ j) :
    ¬ X.LNoBranch :=
  fun hX => h.not_allPer_of_horseshoe hY hrr hσ H hij (allPer_of_lnoBranch hX)

/-! ### Transfer: escape -/

section escape

variable [Fintype A] [DecidableEq V]

/-- A point of `ρ v` follows no word longer than the longest walk from `v`. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.not_follows_of_not_hasWalk (h : Cover X f adm ρ) {v : V} {x : S} {n : ℕ}
    (hx : x ∈ ρ v) (hv : ¬ X.HasWalk v n) {w : List A} (hw : w.length = n) :
    ¬ Follows f adm x w :=
  fun hf => hv (hasWalk_iff_exists_word.2 ⟨w, hw, h.isWord hx hf⟩)

/-- **Escape from the peel**: if `v ∉ peel k`, no point of `ρ v` survives `k` admissible steps
(the escape-time bound behind the Z32 funnels). -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.escape_of_peel [Fintype V] (h : Cover X f adm ρ) {v : V} {x : S} {k : ℕ}
    (hx : x ∈ ρ v) (hv : v ∉ X.peel k) {w : List A} (hw : w.length = k) :
    ¬ Follows f adm x w :=
  h.not_follows_of_not_hasWalk hx (fun hk => hv (mem_peel.2 hk)) hw

/-- **Escape**: if the core of `X` is empty, no point of `⋃ ρ` survives `|V|` admissible
steps.  In `DubC/` this is the unavoidable-divisor-set theorem. -/
@[category textbook, AMS 37 05 11, ref "DubOst06", group "carry_cover"]
theorem Cover.escape_of_core_empty [Fintype V] (h : Cover X f adm ρ) (hX : X.core = ∅)
    {v : V} {x : S} (hx : x ∈ ρ v) {w : List A} (hw : w.length = Fintype.card V) :
    ¬ Follows f adm x w := by
  have h0 : ∀ v, X.npaths v (Fintype.card V) = 0 := by
    have h := (core_eq_empty_iff (X := X)).out 1 3
    exact h.1 hX
  refine h.not_follows_of_not_hasWalk hx (fun hk => ?_) hw
  have := npaths_pos_iff.2 hk
  rw [h0 v] at this
  exact Nat.lt_irrefl 0 this

/-- With an empty core, no orbit from `⋃ ρ` is admissible forever. -/
@[category textbook, AMS 37 05 11, ref "DubOst06", group "carry_cover"]
theorem Cover.not_admForever_of_core_empty [Fintype V] (h : Cover X f adm ρ) (hX : X.core = ∅)
    {v : V} {x : S} (hx : x ∈ ρ v) (ℓ : ℕ → A) : ¬ AdmForever f adm x ℓ := fun hadm =>
  h.escape_of_core_empty hX hx (length_pre ℓ _) (hadm.follows _)

end escape

/-! ### Transfer: counting itineraries -/

variable (f adm ρ) in
/-- The **itineraries** of length `n` from `ρ v`. -/
def orbitWords (v : V) (n : ℕ) : Set (List A) :=
  {w | w.length = n ∧ ∃ x ∈ ρ v, Follows f adm x w}

variable (f adm) in
/-- The itineraries of length `n` from a set `T` of states. -/
def orbitLang (T : Set S) (n : ℕ) : Set (List A) :=
  {w | w.length = n ∧ ∃ x ∈ T, Follows f adm x w}

section count

variable [Fintype A] [DecidableEq A]

/-- Itineraries are words of the cover. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.orbitWords_subset (h : Cover X f adm ρ) (v : V) (n : ℕ) :
    orbitWords f adm ρ v n ⊆ ↑(X.words v n) := fun _ ⟨hl, _, hx, hf⟩ =>
  mem_words.2 ⟨hl, h.isWord hx hf⟩

/-- **The itinerary count**: there are at most `npaths v n` itineraries of length `n` from
`ρ v`. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.ncard_orbitWords_le (h : Cover X f adm ρ) (v : V) (n : ℕ) :
    (orbitWords f adm ρ v n).ncard ≤ X.npaths v n :=
  (Set.ncard_le_ncard (h.orbitWords_subset v n) (Finset.finite_toSet _)).trans
    ((Set.ncard_coe_finset _).le.trans (card_words_le_npaths v n))

/-- The words of an exact cover are itineraries. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Realizes.words_subset (h : Realizes X f adm ρ) (v : V) (n : ℕ) :
    ↑(X.words v n) ⊆ orbitWords f adm ρ v n := fun w hw =>
  let ⟨hl, hw⟩ := mem_words.1 hw
  ⟨hl, h v w hw⟩

/-- **Exact covers**: for a cover that realises its words, the itineraries from `ρ v` are
exactly the words from `v` (the Z32 type certificate is of this kind). -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.orbitWords_eq (h : Cover X f adm ρ) (hr : Realizes X f adm ρ) (v : V) (n : ℕ) :
    orbitWords f adm ρ v n = ↑(X.words v n) :=
  (h.orbitWords_subset v n).antisymm (hr.words_subset v n)

variable [Fintype V]

/-- The itineraries from `T ⊆ ⋃ ρ` lie in the union of the word sets. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.orbitLang_subset (h : Cover X f adm ρ) {T : Set S}
    (hT : ∀ x ∈ T, ∃ v, x ∈ ρ v) (n : ℕ) :
    orbitLang f adm T n ⊆ ↑(Finset.univ.biUnion fun v => X.words v n) := by
  rintro w ⟨hl, x, hx, hf⟩
  obtain ⟨v, hv⟩ := hT x hx
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
    Set.mem_iUnion, Finset.mem_coe]
  exact ⟨v, mem_words.2 ⟨hl, h.isWord hv hf⟩⟩

/-- **The itinerary count**, total form: at most `ntot n` itineraries of length `n`. -/
@[category textbook, AMS 37 05, group "carry_cover"]
theorem Cover.ncard_orbitLang_le (h : Cover X f adm ρ) {T : Set S}
    (hT : ∀ x ∈ T, ∃ v, x ∈ ρ v) (n : ℕ) : (orbitLang f adm T n).ncard ≤ X.ntot n :=
  (Set.ncard_le_ncard (h.orbitLang_subset hT n) (Finset.finite_toSet _)).trans <|
    (Set.ncard_coe_finset _).le.trans <| Finset.card_biUnion_le.trans <|
      Finset.sum_le_sum fun v _ => card_words_le_npaths v n

/-- **The entropy inequality**: the itineraries of a system grow at most like the paths of any
cover. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.orbitEntropy_le (h : Cover X f adm ρ) {T : Set S}
    (hT : ∀ x ∈ T, ∃ v, x ∈ ρ v) :
    expGrowthSup (fun n => ((orbitLang f adm T n).ncard : ℝ≥0∞)) ≤ X.entropy :=
  expGrowthSup_monotone fun n => by exact_mod_cast h.ncard_orbitLang_le hT n

/-- **Exact covers compute the entropy**: if `X` is right-resolving and realises its words, the
itineraries from `⋃ ρ` grow exactly like the paths of `X`. -/
@[category textbook, AMS 37 05, ref "LM95", group "carry_cover"]
theorem Cover.orbitEntropy_eq (h : Cover X f adm ρ) (hr : Realizes X f adm ρ)
    (hrr : X.RightResolving) :
    expGrowthSup (fun n => ((orbitLang f adm {x | ∃ v, x ∈ ρ v} n).ncard : ℝ≥0∞))
      = X.entropy := by
  refine le_antisymm (h.orbitEntropy_le fun _ hx => hx) ?_
  refine expGrowthSup_le_of_eventually_le (b := Fintype.card V) (natCast_ne_top _)
    (Eventually.of_forall fun n => ?_)
  have hsub : ∀ v, ↑(X.words v n) ⊆ orbitLang f adm {x | ∃ v, x ∈ ρ v} n := fun v w hw =>
    let ⟨hl, _, hx, hf⟩ := hr.words_subset v n hw
    ⟨hl, _, ⟨v, hx⟩, hf⟩
  have hfin : (orbitLang f adm {x | ∃ v, x ∈ ρ v} n).Finite :=
    (Finset.finite_toSet _).subset (h.orbitLang_subset (fun _ hx => hx) n)
  have : X.ntot n ≤ Fintype.card V * (orbitLang f adm {x | ∃ v, x ∈ ρ v} n).ncard :=
    calc X.ntot n = ∑ v, (X.words v n).card :=
          Finset.sum_congr rfl fun v _ => (card_words_eq_npaths hrr v n).symm
      _ ≤ ∑ _v : V, (orbitLang f adm {x | ∃ v, x ∈ ρ v} n).ncard :=
          Finset.sum_le_sum fun v _ =>
            (Set.ncard_coe_finset _).symm.le.trans (Set.ncard_le_ncard (hsub v) hfin)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact_mod_cast this

end count

end CarryGraph
