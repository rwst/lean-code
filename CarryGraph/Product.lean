/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Quotient

/-!
# Label products ([LM95] §3.4)

The **label product** `X.labelProduct Y` of two carry graphs over one alphabet [LM95, Def. 3.4.8]
has the pairs of vertices as vertices and an `a`-arc where both factors have one.  Its walks are
pairs of walks reading the same word (`reads_labelProduct`), so it presents the intersection of
the two languages (`mem_langFrom_labelProduct`, [LM95, Prop. 3.4.10]), and sofic languages are
closed under intersection (`Sofic.inter`).  The indexed version `piProduct` does the same for a
finite family of factors.

What the affine carry graphs of Chapter 8 need from products:

* **soundness**: the two projections are homomorphisms, so the label form or an empty core of
  one factor passes to the product (`allPer_labelProduct_left`, `core_labelProduct_left`, …);
* **zero entropy**: the product of zero-entropy graphs has zero entropy
  (`lnoBranch_labelProduct`), and in general `entropy (X ⊗ Y) ≤ entropy X + entropy Y`
  (`entropy_labelProduct_le`).  The bound `≤ min` holds for the *words*
  (`card_words_labelProduct_le`), and for paths when the other factor is right-resolving
  (`entropy_labelProduct_le_left`).  It fails for paths in general: the one-letter loop times
  the two-vertex complete graph has entropy `log 2`;
* **the subset construction factorises**: `detStep (S ×ˢ T) a = detStep S a ×ˢ detStep T a`
  (`detStep_labelProduct`, `detStep_piProduct`).  This is the content of
  `DubC2.Gen.Follower.rstep_prodR` (the CRT bridge), stated for graphs;
* **monotonicity in the index set**: more factors, smaller language, and every certificate
  survives (`allPer_piProduct_mono`, `langFrom_piProduct_antitone`), also next to a shared
  factor (`Hom.prodMap`; the cell coordinate of a `DubC2/` cell).

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

open Filter ENNReal ExpGrowth

namespace CarryGraph

variable {V W V' W' A : Type*} {X : CarryGraph V A} {Y : CarryGraph W A}

/-! ### The label product -/

variable (X Y) in
/-- **The label product** [LM95, Def. 3.4.8]. -/
def labelProduct : CarryGraph (V × W) A := ⟨fun x a => X.succ x.1 a ×ˢ Y.succ x.2 a⟩

@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem adj_labelProduct {x y : V × W} {a : A} :
    (X.labelProduct Y).Adj x a y ↔ X.Adj x.1 a y.1 ∧ Y.Adj x.2 a y.2 :=
  Finset.mem_product

variable (X Y) in
/-- The first projection. -/
def fstHom : Hom (X.labelProduct Y) X := ⟨Prod.fst, fun h => (adj_labelProduct.1 h).1⟩

variable (X Y) in
/-- The second projection. -/
def sndHom : Hom (X.labelProduct Y) Y := ⟨Prod.snd, fun h => (adj_labelProduct.1 h).2⟩

/-- The product of two homomorphisms. -/
def Hom.prodMap {X' : CarryGraph V' A} {Y' : CarryGraph W' A} (f : Hom X X') (g : Hom Y Y') :
    Hom (X.labelProduct Y) (X'.labelProduct Y') :=
  ⟨Prod.map f.toFun g.toFun, fun h =>
    adj_labelProduct.2 ⟨f.map_adj (adj_labelProduct.1 h).1, g.map_adj (adj_labelProduct.1 h).2⟩⟩

/-- Walks of the label product are pairs of walks reading the same word. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem reads_labelProduct : ∀ {v₁ v₁' : V} {v₂ v₂' : W} {w : List A},
    (X.labelProduct Y).Reads (v₁, v₂) w (v₁', v₂') ↔ X.Reads v₁ w v₁' ∧ Y.Reads v₂ w v₂'
  | v₁, v₁', v₂, v₂', [] => by simp [reads_nil]
  | v₁, v₁', v₂, v₂', a :: w => by
    simp only [reads_cons]
    constructor
    · rintro ⟨⟨u₁, u₂⟩, h, hr⟩
      obtain ⟨h₁, h₂⟩ := reads_labelProduct.1 hr
      exact ⟨⟨u₁, (adj_labelProduct.1 h).1, h₁⟩, ⟨u₂, (adj_labelProduct.1 h).2, h₂⟩⟩
    · rintro ⟨⟨u₁, h₁, hr₁⟩, ⟨u₂, h₂, hr₂⟩⟩
      exact ⟨(u₁, u₂), adj_labelProduct.2 ⟨h₁, h₂⟩, reads_labelProduct.2 ⟨hr₁, hr₂⟩⟩

/-- **[LM95, Prop. 3.4.10]**: the label product presents the intersection of the languages. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem mem_langFrom_labelProduct {v₁ : V} {v₂ : W} {w : List A} :
    w ∈ (X.labelProduct Y).langFrom (v₁, v₂) ↔ w ∈ X.langFrom v₁ ∧ w ∈ Y.langFrom v₂ := by
  constructor
  · rintro ⟨⟨u₁, u₂⟩, h⟩
    obtain ⟨h₁, h₂⟩ := reads_labelProduct.1 h
    exact ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩
  · rintro ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩
    exact ⟨(u₁, u₂), reads_labelProduct.2 ⟨h₁, h₂⟩⟩

@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem langFrom_labelProduct (v₁ : V) (v₂ : W) :
    (X.labelProduct Y).langFrom (v₁, v₂) = X.langFrom v₁ ⊓ Y.langFrom v₂ :=
  Language.ext fun _ => mem_langFrom_labelProduct

/-- **Sofic languages are closed under intersection** [LM95, Prop. 3.4.10]. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem Sofic.inter {L₁ L₂ : Language A} (h₁ : Sofic L₁) (h₂ : Sofic L₂) : Sofic (L₁ ⊓ L₂) := by
  obtain ⟨n, X₁, v₁, rfl⟩ := h₁
  obtain ⟨m, X₂, v₂, rfl⟩ := h₂
  rw [← langFrom_labelProduct]
  exact sofic_of_finite _ _

/-- **[LM95, Prop. 3.4.10]**: the label product of right-resolving graphs is right-resolving. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem rightResolving_labelProduct (hX : X.RightResolving) (hY : Y.RightResolving) :
    (X.labelProduct Y).RightResolving := fun x a => by
  show (X.succ x.1 a ×ˢ Y.succ x.2 a).card ≤ 1
  rw [Finset.card_product]
  exact Nat.mul_le_mul (hX _ _) (hY _ _)

/-! ### Soundness: one factor certifies the product -/

/-- The label form of the first factor gives that of the product. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem allPer_labelProduct_left (h : X.AllPer) : (X.labelProduct Y).AllPer :=
  allPer_of_hom (fstHom X Y) h

@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem allPer_labelProduct_right (h : Y.AllPer) : (X.labelProduct Y).AllPer :=
  allPer_of_hom (sndHom X Y) h

@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem core_labelProduct_left (h : X.core = ∅) : (X.labelProduct Y).core = ∅ :=
  (fstHom X Y).core_eq_empty h

@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem core_labelProduct_right (h : Y.core = ∅) : (X.labelProduct Y).core = ∅ :=
  (sndHom X Y).core_eq_empty h

/-! ### The subset construction factorises -/

/-- **One step of the subset construction on a product set is the product of the steps.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem detStep_labelProduct [DecidableEq V] [DecidableEq W] (S : Finset V) (T : Finset W)
    (a : A) : (X.labelProduct Y).detStep (S ×ˢ T) a = X.detStep S a ×ˢ Y.detStep T a := by
  ext ⟨u₁, u₂⟩
  simp only [mem_detStep, Finset.mem_product, adj_labelProduct, Prod.exists]
  constructor
  · rintro ⟨v₁, v₂, ⟨hv₁, hv₂⟩, h₁, h₂⟩
    exact ⟨⟨v₁, hv₁, h₁⟩, ⟨v₂, hv₂, h₂⟩⟩
  · rintro ⟨⟨v₁, hv₁, h₁⟩, ⟨v₂, hv₂, h₂⟩⟩
    exact ⟨v₁, v₂, ⟨hv₁, hv₂⟩, h₁, h₂⟩

/-! ### Growth -/

section growth

variable [Fintype A]

@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem npaths_labelProduct_le : ∀ (n : ℕ) (v : V) (w : W),
    (X.labelProduct Y).npaths (v, w) n ≤ X.npaths v n * Y.npaths w n
  | 0, _, _ => by simp [npaths_zero]
  | n + 1, v, w => by
    rw [npaths_succ, npaths_succ, npaths_succ]
    calc ∑ a, ∑ u ∈ (X.labelProduct Y).succ (v, w) a, (X.labelProduct Y).npaths u n
        ≤ ∑ a, (∑ u ∈ X.succ v a, X.npaths u n) * ∑ u ∈ Y.succ w a, Y.npaths u n := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Finset.sum_mul_sum]
          show ∑ u ∈ X.succ v a ×ˢ Y.succ w a, _ ≤ _
          rw [Finset.sum_product]
          exact Finset.sum_le_sum fun u₁ _ => Finset.sum_le_sum fun u₂ _ =>
            npaths_labelProduct_le n u₁ u₂
      _ ≤ ∑ a, (∑ u ∈ X.succ v a, X.npaths u n) * ∑ b, ∑ u ∈ Y.succ w b, Y.npaths u n :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _
            (Finset.single_le_sum (f := fun b => ∑ u ∈ Y.succ w b, Y.npaths u n)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
      _ = _ := (Finset.sum_mul ..).symm

omit [Fintype A] in
/-- If the second factor is right-resolving, the first projection is locally injective. -/
@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem fstHom_locInj (hY : Y.RightResolving) : (fstHom X Y).LocInj := by
  rintro ⟨v, w⟩ a ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy (h : x₁ = y₁)
  have hx' := (adj_labelProduct.1 hx).2
  have hy' := (adj_labelProduct.1 hy).2
  exact Prod.ext h (Finset.card_le_one.1 (hY w a) _ hx' _ hy')

variable [Fintype V] [Fintype W]

@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem ntot_labelProduct_le (n : ℕ) :
    (X.labelProduct Y).ntot n ≤ X.ntot n * Y.ntot n := by
  rw [ntot, ntot, ntot, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => npaths_labelProduct_le n v w

/-- The entropy of a finite carry graph is finite. -/
@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem entropy_ne_top : X.entropy ≠ ⊤ := by
  have hw : X.IsSuperEigen (fun _ => 1) (Fintype.card A * Fintype.card V) 1 := by
    refine ⟨fun _ => le_rfl, fun v => ?_⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one, one_mul]
    exact card_arcsFrom_le v
  refine ne_top_of_le_ne_top ?_ (entropy_le_of_superEigen one_pos hw)
  rw [Nat.cast_one, div_one, Ne, ENNReal.log_eq_top_iff]
  exact natCast_ne_top _

/-- **The entropy of a label product is at most the sum of the entropies.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem entropy_labelProduct_le : (X.labelProduct Y).entropy ≤ X.entropy + Y.entropy := by
  refine (expGrowthSup_monotone (b := (fun n => (X.ntot n : ℝ≥0∞)) * fun n => (Y.ntot n : ℝ≥0∞))
    fun n => ?_).trans (expGrowthSup_mul_le (.inr entropy_ne_top) (.inl entropy_ne_top))
  show ((X.labelProduct Y).ntot n : ℝ≥0∞) ≤ (X.ntot n : ℝ≥0∞) * (Y.ntot n : ℝ≥0∞)
  exact_mod_cast ntot_labelProduct_le (X := X) (Y := Y) n

/-- **Right-resolving second factor: the product has at most the entropy of the first.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem entropy_labelProduct_le_left [DecidableEq V] [DecidableEq W] (hY : Y.RightResolving) :
    (X.labelProduct Y).entropy ≤ X.entropy :=
  (fstHom X Y).entropy_le_of_locInj (fstHom_locInj hY)

/-- **The label product of zero-entropy graphs has zero entropy.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem lnoBranch_labelProduct [DecidableEq V] [DecidableEq W] (hX : X.LNoBranch)
    (hY : Y.LNoBranch) : (X.labelProduct Y).LNoBranch := by
  obtain ⟨C₁, d₁, h₁⟩ := polyGrowth_of_lnoBranch hX
  obtain ⟨C₂, d₂, h₂⟩ := polyGrowth_of_lnoBranch hY
  refine polyGrowth_lnoBranch ⟨C₁ * C₂, d₁ + d₂, fun x n => ?_⟩
  calc (X.labelProduct Y).npaths x n ≤ X.npaths x.1 n * Y.npaths x.2 n :=
        npaths_labelProduct_le n x.1 x.2
    _ ≤ C₁ * (n + 1) ^ d₁ * (C₂ * (n + 1) ^ d₂) := Nat.mul_le_mul (h₁ _ n) (h₂ _ n)
    _ = C₁ * C₂ * (n + 1) ^ (d₁ + d₂) := by ring

omit [Fintype V] [Fintype W] in
/-- **Word counts of a label product are bounded by those of either factor.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem card_words_labelProduct_le [DecidableEq A] (v : V) (w : W) (n : ℕ) :
    ((X.labelProduct Y).words (v, w) n).card ≤ min (X.words v n).card (Y.words w n).card := by
  refine le_min (Finset.card_le_card fun x hx => ?_) (Finset.card_le_card fun x hx => ?_) <;>
    rw [mem_words] at hx ⊢ <;>
    obtain ⟨hl, hw⟩ := hx
  · exact ⟨hl, (mem_langFrom_labelProduct.1 hw).1⟩
  · exact ⟨hl, (mem_langFrom_labelProduct.1 hw).2⟩

end growth

/-! ### Indexed label products -/

section pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vs : ι → Type*}

/-- **The indexed label product** of a finite family of carry graphs over one alphabet. -/
def piProduct (G : ∀ i, CarryGraph (Vs i) A) : CarryGraph (∀ i, Vs i) A :=
  ⟨fun x a => Fintype.piFinset fun i => (G i).succ (x i) a⟩

variable {G : ∀ i, CarryGraph (Vs i) A}

@[category API, AMS 05 37, ref "LM95", group "carry_product"]
theorem adj_piProduct {x y : ∀ i, Vs i} {a : A} :
    (piProduct G).Adj x a y ↔ ∀ i, (G i).Adj (x i) a (y i) :=
  Fintype.mem_piFinset

variable (G) in
/-- The projection to one factor. -/
def projHom (i : ι) : Hom (piProduct G) (G i) := ⟨fun x => x i, fun h => adj_piProduct.1 h i⟩

/-- Walks of an indexed label product are families of walks reading the same word. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem reads_piProduct : ∀ {x y : ∀ i, Vs i} {w : List A},
    (piProduct G).Reads x w y ↔ ∀ i, (G i).Reads (x i) w (y i)
  | x, y, [] => by
    simp only [reads_nil]
    exact ⟨fun h i => by rw [h], fun h => funext h⟩
  | x, y, a :: w => by
    simp only [reads_cons]
    constructor
    · rintro ⟨u, h, hr⟩ i
      exact ⟨u i, adj_piProduct.1 h i, reads_piProduct.1 hr i⟩
    · intro h
      choose u hu hr using h
      exact ⟨u, adj_piProduct.2 hu, reads_piProduct.2 hr⟩

/-- **An indexed label product presents the intersection of the languages.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem mem_langFrom_piProduct {x : ∀ i, Vs i} {w : List A} :
    w ∈ (piProduct G).langFrom x ↔ ∀ i, w ∈ (G i).langFrom (x i) := by
  constructor
  · rintro ⟨y, h⟩ i
    exact ⟨y i, reads_piProduct.1 h i⟩
  · intro h
    choose y hy using h
    exact ⟨y, reads_piProduct.2 hy⟩

@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem rightResolving_piProduct (h : ∀ i, (G i).RightResolving) :
    (piProduct G).RightResolving := fun x a => by
  refine Finset.card_le_one.2 fun y hy z hz => funext fun i => ?_
  exact Finset.card_le_one.1 (h i (x i) a) _ (adj_piProduct.1 hy i) _ (adj_piProduct.1 hz i)

/-- **One factor certifies the indexed product.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem allPer_piProduct (i : ι) (h : (G i).AllPer) : (piProduct G).AllPer :=
  allPer_of_hom (projHom G i) h

/-- **The subset construction factorises over an indexed product** — the content of
`DubC2.Gen.Follower.rstep_prodR`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem detStep_piProduct [∀ i, DecidableEq (Vs i)] (S : ∀ i, Finset (Vs i)) (a : A) :
    (piProduct G).detStep (Fintype.piFinset S) a =
      Fintype.piFinset fun i => (G i).detStep (S i) a := by
  ext y
  simp only [mem_detStep, Fintype.mem_piFinset, adj_piProduct]
  constructor
  · rintro ⟨x, hx, h⟩ i
    exact ⟨x i, hx i, h i⟩
  · intro h
    choose x hx h using h
    exact ⟨x, hx, h⟩

/-! ### Monotonicity in the index set -/

/-- Restricting to a smaller index set is a homomorphism. -/
def restrictHom {I J : Finset ι} (hIJ : I ⊆ J) :
    Hom (piProduct fun j : J => G j) (piProduct fun i : I => G i) :=
  ⟨fun x i => x ⟨i, hIJ i.2⟩, fun h => adj_piProduct.2 fun i => adj_piProduct.1 h ⟨i, hIJ i.2⟩⟩

omit [Fintype ι] in
/-- **Monotonicity, certificates**: a certificate for the product over `I` certifies the
product over every `J ⊇ I`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem allPer_piProduct_mono {I J : Finset ι} (hIJ : I ⊆ J)
    (h : (piProduct fun i : I => G i).AllPer) : (piProduct fun j : J => G j).AllPer :=
  allPer_of_hom (restrictHom hIJ) h

omit [Fintype ι] in
/-- **Monotonicity, languages**: more factors, smaller language. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_product"]
theorem langFrom_piProduct_antitone {I J : Finset ι} (hIJ : I ⊆ J) (x : ∀ j : J, Vs j) :
    ∀ w, w ∈ (piProduct fun j : J => G j).langFrom x →
      w ∈ (piProduct fun i : I => G i).langFrom fun i => x ⟨i, hIJ i.2⟩ :=
  langFrom_subset_of_hom (restrictHom hIJ) x

omit [Fintype ι] in
/-- **Monotonicity next to a shared factor** (the cell coordinate of a `DubC2/` cell). -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_product"]
theorem allPer_labelProduct_piProduct_mono {I J : Finset ι} (hIJ : I ⊆ J)
    (h : (X.labelProduct (piProduct fun i : I => G i)).AllPer) :
    (X.labelProduct (piProduct fun j : J => G j)).AllPer :=
  allPer_of_hom ((Hom.id X).prodMap (restrictHom hIJ)) h

end pi

end CarryGraph
