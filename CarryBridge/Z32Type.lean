/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.Z32
import Z32.«entropy-certificates».EntropyCert

/-!
# Bridge: the type certificates of `Z32/` as exact carry graphs

A type certificate `c : Z32.EntropyCert.TypeCert` for an anchored window `[0, ℓ)` of the base
`3/2` lists states (scaled cylinder-image endpoints), edges `(source, carry, target)` with carries
in `{0, 1}`, and two weight vectors.  Read as a carry graph — `typeGraph c` on the states, letters
`Fin 2` — it is the plan's model of an **exact** cover:

* it is right-resolving (`typeGraph_rightResolving`);
* the weight checks are a super- and a sub-eigenvector (`typeGraph_isSuperEigen`,
  `typeGraph_isSubEigen`), so the generic brackets bound its entropy
  (`entropy_typeGraph_le`, `le_entropy_typeGraph`);
* a confined model orbit walks it from the root (`exists_iPath_of_modelOrbit`: soundness), and
  every word read from the root is the carry word of a confined model orbit
  (`exists_modelOrbit_of_isWord`: realizability);
* hence the language of the window is the label language of the root:
  `card_modelLang_eq_words`, the carry-graph form of `TypeCert.card_modelLang_eq`.

## References

* [Fla92] L. Flatto, *Z-numbers and β-transformations*, Contemp. Math. 135 (1992).
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryBridge

open CarryGraph Z32 Z32.EntropyCert

variable (c : TypeCert)

/-- The states of a type certificate, as a finite vertex type. -/
abbrev TState : Type := {x : ℤ // x ∈ c.states}

instance tstateFintype : Fintype (TState c) :=
  Fintype.subtype c.states.toFinset fun _ => List.mem_toFinset

/-- **The type graph**: `x →t y` iff `(x, t, y)` is an edge of the certificate. -/
def typeGraph : CarryGraph (TState c) (Fin 2) :=
  ⟨fun x t => Finset.univ.filter fun y => ((x : ℤ), ((t : ℕ) : ℤ), (y : ℤ)) ∈ c.ed⟩

variable {c}

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem adj_typeGraph {x y : TState c} {t : Fin 2} :
    (typeGraph c).Adj x t y ↔ ((x : ℤ), ((t : ℕ) : ℤ), (y : ℤ)) ∈ c.ed := by
  simp [typeGraph, Adj]

/-- The root: the state `L` (the window itself). -/
def troot (h : c.ok = true) : TState c := ⟨c.L, TypeCert.L_mem h⟩

/-- The letter of a carry `0` or `1`. -/
def tlet (s : ℤ) : Fin 2 := if s = 0 then 0 else 1

theorem tlet_cast {s : ℤ} (hs : s = 0 ∨ s = 1) : (((tlet s : Fin 2) : ℕ) : ℤ) = s := by
  rcases hs with rfl | rfl <;> rfl

/-- **The type graph is right-resolving**: the transition identity determines the target. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem typeGraph_rightResolving (h : c.ok = true) : (typeGraph c).RightResolving := by
  intro x t
  refine Finset.card_le_one.2 fun y hy z hz => ?_
  have hy' := (TypeCert.edge_parts h (adj_typeGraph.1 hy)).2.2.2.2
  have hz' := (TypeCert.edge_parts h (adj_typeGraph.1 hz)).2.2.2.2
  exact Subtype.ext (by simp only at hy' hz'; omega)

/-- The arcs out of a state are the certificate's out-edge list. -/
theorem sum_arcsFrom (h : c.ok = true) (f : ℤ → ℕ) (x : TState c) :
    ∑ a ∈ (typeGraph c).arcsFrom x, f a.2 = ((c.outL x).map fun e => f e.2.2).sum := by
  classical
  rw [← TypeCert.sum_outEdges h f x.2]
  refine Finset.sum_bij (fun a _ => ((x : ℤ), (((a.1 : Fin 2) : ℕ) : ℤ), (a.2 : ℤ)))
    (fun a ha => ?_) (fun a ha b hb e => ?_) (fun e he => ?_) (fun a _ => rfl)
  · simp only [PathGrowth.outEdges, Finset.mem_filter]
    exact ⟨TypeCert.mem_E_of_mem_ed (adj_typeGraph.1 (mem_arcsFrom.1 ha)), trivial⟩
  · simp only [Prod.mk.injEq] at e
    obtain ⟨-, e1, e2⟩ := e
    have h1 : a.1 = b.1 := Fin.ext (by exact_mod_cast e1)
    have h2 : a.2 = b.2 := Subtype.ext e2
    exact Sigma.ext h1 (heq_of_eq h2)
  · simp only [PathGrowth.outEdges, Finset.mem_filter] at he
    obtain ⟨heE, hsrc⟩ := he
    have hed := TypeCert.mem_ed_of_mem_E heE
    obtain ⟨-, htgt, -, hlab, -⟩ := TypeCert.edge_parts h hed
    refine ⟨⟨tlet e.2.1, ⟨e.2.2, htgt⟩⟩, mem_arcsFrom.2 (adj_typeGraph.2 ?_), ?_⟩
    · rw [tlet_cast hlab, ← hsrc]; exact hed
    · simp only [tlet_cast hlab, ← hsrc]

/-- **The upper weight check is a super-eigenvector** of the type graph. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem typeGraph_isSuperEigen (h : c.ok = true) :
    (typeGraph c).IsSuperEigen (fun x => c.wt x) c.a c.b := by
  refine ⟨fun x => (TypeCert.m_pos h).trans_le (TypeCert.m_le_wt h x), fun x => ?_⟩
  rw [sum_arcsFrom h (fun z => c.wt z) x]
  exact (TypeCert.weight_parts h x.2).2.1

/-- **The lower weight check is a sub-eigenvector** of the type graph. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem typeGraph_isSubEigen (h : c.ok = true) :
    (typeGraph c).IsSubEigen (fun x => c.wt0 x) c.a' c.b' := by
  intro x
  rw [sum_arcsFrom h (fun z => c.wt0 z) x]
  exact (TypeCert.weight_parts h x.2).2.2

/-- The entropy of the type graph is at most `log (a/b)`. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem entropy_typeGraph_le (h : c.ok = true) :
    (typeGraph c).entropy ≤ ENNReal.log ((c.a : ENNReal) / c.b) :=
  entropy_le_of_superEigen (TypeCert.b_pos h) (typeGraph_isSuperEigen h)

/-- The entropy of the type graph is at least `log (a'/b')`. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem le_entropy_typeGraph (h : c.ok = true) :
    ENNReal.log ((c.a' : ENNReal) / c.b') ≤ (typeGraph c).entropy :=
  log_le_entropy_of_subEigen (TypeCert.b'_pos h) (typeGraph_isSubEigen h)
    (v₀ := troot h) (TypeCert.wt0_pos_of_mem h (TypeCert.L_mem h))

/-! ### Exactness -/

/-- **Soundness**: a confined model orbit walks the type graph from the root, reading its carry
word. -/
@[category research solved, AMS 11 37 05, ref "Fla92", group "carry_bridge_z32"]
theorem exists_iPath_of_modelOrbit (h : c.ok = true) {y : ℕ → ℝ} {s : ℕ → ℤ}
    (horb : IsModelOrbit 3 2 c.window y s) :
    ∃ A : ℕ → TState c, A 0 = troot h ∧ (typeGraph c).IsIPath A fun n => tlet (s n) := by
  obtain ⟨A, hA0, hAmem, -, hpath⟩ := TypeCert.exists_state_path h horb
  refine ⟨fun n => ⟨A n, hAmem n⟩, Subtype.ext hA0, fun n => adj_typeGraph.2 ?_⟩
  rw [tlet_cast (TypeCert.carry_eq h horb n)]
  exact hpath n

/-- A word read in the type graph is a word of the certificate's edge set. -/
theorem map_mem_words_of_reads :
    ∀ (w : List (Fin 2)) (x u : TState c), (typeGraph c).Reads x w u →
      w.map (fun t : Fin 2 => ((t : ℕ) : ℤ)) ∈ PathGrowth.words c.E (x : ℤ) w.length
  | [], _, _, _ => by simp [PathGrowth.words_zero]
  | a :: w, x, u, hr => by
    obtain ⟨t, hxt, htu⟩ := reads_cons.1 hr
    rw [List.length_cons, PathGrowth.words_succ, Finset.mem_biUnion]
    refine ⟨((x : ℤ), ((a : ℕ) : ℤ), (t : ℤ)), ?_, ?_⟩
    · simp only [PathGrowth.outEdges, Finset.mem_filter]
      exact ⟨TypeCert.mem_E_of_mem_ed (adj_typeGraph.1 hxt), trivial⟩
    · exact Finset.mem_image.2 ⟨_, map_mem_words_of_reads w t u htu, by simp⟩

/-- **Realizability**: every word read from the root is the carry word of a confined model
orbit. -/
@[category research solved, AMS 11 37 05, ref "Fla92", group "carry_bridge_z32"]
theorem exists_modelOrbit_of_isWord (h : c.ok = true) {w : List (Fin 2)}
    (hw : (typeGraph c).IsWord (troot h) w) :
    ∃ (y : ℕ → ℝ) (s : ℕ → ℤ), IsModelOrbit 3 2 c.window y s ∧
      w.map (fun t : Fin 2 => ((t : ℕ) : ℤ)) = List.ofFn fun i : Fin w.length => s i := by
  obtain ⟨u, hu⟩ := hw
  have hm := map_mem_words_of_reads w (troot h) u hu
  obtain ⟨y, s, horb, -, hword⟩ :=
    TypeCert.exists_orbit_of_mem_words h w.length c.L (TypeCert.L_mem h) _ hm
  exact ⟨y, s, horb, hword⟩

/-- **The window's language is the type graph's label language from the root**
(`TypeCert.card_modelLang_eq` in carry-graph form): soundness and realizability are inverse
injections. -/
@[category research solved, AMS 11 37 05, ref "Fla92" "LM95", group "carry_bridge_z32"]
theorem card_modelLang_eq_words (h : c.ok = true) (k : ℕ) :
    Nat.card (modelLang 3 2 c.window k) = ((typeGraph c).words (troot h) k).card := by
  classical
  have hcoe : Function.Injective fun t : Fin 2 => ((t : ℕ) : ℤ) := fun a b e =>
    Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) from e))
  -- model words to graph words
  have hto : ∀ v : modelLang 3 2 c.window k,
      (List.ofFn fun i : Fin k => tlet (v.1 i)) ∈ (typeGraph c).words (troot h) k := by
    rintro ⟨v, y, s, horb, hval⟩
    obtain ⟨A, hA0, hA⟩ := exists_iPath_of_modelOrbit h horb
    refine mem_words.2 ⟨by simp, ?_⟩
    have key : ∀ m n, (typeGraph c).Reads (A n) (List.ofFn fun i : Fin m => tlet (s (n + i)))
        (A (n + m)) := by
      intro m
      induction m with
      | zero => intro n; simp [reads_nil]
      | succ m ih =>
        intro n
        rw [List.ofFn_succ, reads_cons]
        refine ⟨A (n + 1), by simpa using hA n, ?_⟩
        have e : (fun i : Fin m => tlet (s (n + ((i.succ : Fin (m + 1)) : ℕ))))
            = fun i : Fin m => tlet (s (n + 1 + i)) := by
          funext i; congr 2; simp [Fin.val_succ]; omega
        rw [e, show n + (m + 1) = n + 1 + m by omega]
        exact ih (n + 1)
    refine ⟨A k, ?_⟩
    have := key k 0
    simp only [Nat.zero_add] at this
    rw [hA0] at this
    have e : (fun i : Fin k => tlet (v i)) = fun i : Fin k => tlet (s i) := by
      funext i; rw [hval i]
    rw [e]
    exact this
  have hinj1 : Function.Injective fun v : modelLang 3 2 c.window k =>
      (⟨_, hto v⟩ : {x // x ∈ (typeGraph c).words (troot h) k}) := by
    rintro ⟨v, y, s, horb, hval⟩ ⟨v', y', s', horb', hval'⟩ e
    have e' := List.ofFn_injective (congrArg Subtype.val e)
    refine Subtype.ext (funext fun i => ?_)
    have := congrFun e' i
    simp only at this
    have c1 := TypeCert.carry_eq h horb i
    have c2 := TypeCert.carry_eq h horb' i
    show v i = v' i
    rw [← hval i, ← hval' i] at this ⊢
    rw [← tlet_cast c1, ← tlet_cast c2, this]
  -- graph words to model words
  have hback : ∀ w : {x // x ∈ (typeGraph c).words (troot h) k},
      ∃ v : Fin k → ℤ, v ∈ modelLang 3 2 c.window k ∧
        w.1.map (fun t : Fin 2 => ((t : ℕ) : ℤ)) = List.ofFn v := by
    rintro ⟨w, hw⟩
    obtain ⟨hlen, hword⟩ := mem_words.1 hw
    obtain ⟨y, s, horb, hmap⟩ := exists_modelOrbit_of_isWord h hword
    subst hlen
    exact ⟨fun i => s i, ⟨y, s, horb, fun _ => rfl⟩, hmap⟩
  choose f hf1 hf2 using hback
  have hfin : Finite (modelLang 3 2 c.window k) :=
    (modelLang_finite (p := 3) (q := 2) (by norm_num) (by norm_num) c.window k).to_subtype
  have hinj2 : Function.Injective fun w => (⟨f w, hf1 w⟩ : modelLang 3 2 c.window k) := by
    intro w w' e
    have hf : f w = f w' := congrArg Subtype.val e
    have hm : w.1.map (fun t : Fin 2 => ((t : ℕ) : ℤ))
        = w'.1.map (fun t : Fin 2 => ((t : ℕ) : ℤ)) := by
      rw [hf2 w, hf2 w', hf]
    exact Subtype.ext (List.map_injective_iff.2 hcoe hm)
  refine le_antisymm ?_ ?_
  · calc Nat.card (modelLang 3 2 c.window k)
        ≤ Nat.card {x // x ∈ (typeGraph c).words (troot h) k} :=
          Nat.card_le_card_of_injective _ hinj1
      _ = ((typeGraph c).words (troot h) k).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  · calc ((typeGraph c).words (troot h) k).card
        = Nat.card {x // x ∈ (typeGraph c).words (troot h) k} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Nat.card (modelLang 3 2 c.window k) := Nat.card_le_card_of_injective _ hinj2

end CarryBridge
