/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.Z32
import CarryGraph.Flow
import Z32.BalanceVectors

/-!
# Bridge: the balance vectors of the `3/2` density problem as circulations

| `Z32/BalanceVectors.lean` | `CarryGraph/` |
|---|---|
| `edgeOk w` | `edgeGraph w` on `Fin (2 ^ w)` (`under_edgeGraph`) |
| `BalanceVec w` | a circulation of `edgeGraph w` (`isCirculation_balanceFlow`) |
| `IsTrap w S` | `S` nonempty and essential (`isTrap_map_iff`) |
| `exists_balanceVec` | `exists_circulation_of_walk` (`exists_balanceVec'`) |

`BalanceVec.isTrap_supp'` and `exists_balanceVec'` re-derive the support lemma and the balance
lemma from the generic ones; `BalanceVec.reach_of_pos` is new: every edge carrying balance flow
lies on a cycle of the level-`w` carry graph.  (A separate file because `Z32.BalanceVectors` and
`Z32.CertComplete` cannot be imported together: both declare `Z32.cycleDenom_cast`.)
-/

namespace CarryBridge

open CarryGraph Z32

/-! ### Balance vectors as circulations -/

section Balance

open Filter Topology

variable {w : ℕ}

/-- The level-`w` carry graph of `Z32/BalanceVectors.lean` on the `2 ^ w` dyadic cells. -/
def edgeGraph (w : ℕ) : CarryGraph (Fin (2 ^ w)) Unit :=
  ofRel fun b _ b' => edgeOk w b b' = true

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem under_edgeGraph {b b' : Fin (2 ^ w)} :
    (edgeGraph w).under b b' ↔ edgeOk w b b' = true := by
  simp [CarryGraph.under, edgeGraph, adj_ofRel]

/-- A balance vector as a flow on the cells. -/
def balanceFlow (B : BalanceVec w) : Fin (2 ^ w) → Fin (2 ^ w) → ℝ := fun b b' => B.ν b b'

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem outflow_balanceFlow (B : BalanceVec w) (b : Fin (2 ^ w)) :
    outflow (balanceFlow B) b = B.μ b := by
  rw [outflow, ← B.out b b.2]
  exact Fin.sum_univ_eq_sum_range (fun b' => B.ν b b') _

/-- **A balance vector is a circulation** of the level-`w` carry graph. -/
@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem isCirculation_balanceFlow (B : BalanceVec w) :
    (edgeGraph w).IsCirculation (balanceFlow B) where
  nonneg _ _ := B.ν_nonneg _ _
  adm b b' h := under_edgeGraph.2 (B.adm b b' h)
  cons b := by
    rw [outflow_balanceFlow, inflow, ← B.inn b b.2]
    exact (Fin.sum_univ_eq_sum_range (fun c => B.ν c b) _).symm

/-- **A trap is a nonempty essential set.** -/
@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem isTrap_map_iff (S : Finset (Fin (2 ^ w))) :
    IsTrap w (S.map Fin.valEmbedding) ↔ S.Nonempty ∧ (edgeGraph w).Essential (S : Set _) := by
  simp only [IsTrap, Finset.map_nonempty, Finset.mem_map, Fin.valEmbedding_apply,
    CarryGraph.Essential, Finset.mem_coe, under_edgeGraph]
  constructor
  · rintro ⟨hne, hs, hp⟩
    refine ⟨hne, fun v hv => ⟨?_, ?_⟩⟩
    · obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := hs v ⟨v, hv, rfl⟩
      exact ⟨u, hu, he⟩
    · obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := hp v ⟨v, hv, rfl⟩
      exact ⟨u, hu, he⟩
  · rintro ⟨hne, hS⟩
    refine ⟨hne, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨u, hu, he⟩ := (hS v hv).1
      exact ⟨u, ⟨u, hu, rfl⟩, he⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨u, hu, he⟩ := (hS v hv).2
      exact ⟨u, ⟨u, hu, rfl⟩, he⟩

/-- **The support of a balance vector is a trap** (`BalanceVec.isTrap_supp`), re-derived: the
support of a circulation is essential (`IsCirculation.essential`). -/
@[category research solved, AMS 11 37 05, group "carry_bridge_z32"]
theorem BalanceVec.isTrap_supp' (B : BalanceVec w) : IsTrap w B.supp := by
  classical
  have hS : B.supp = (Finset.univ.filter (· ∈ flowSupp (balanceFlow B))).map Fin.valEmbedding := by
    ext b
    simp only [B.mem_supp, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, flowSupp, Set.mem_ofPred_eq, outflow_balanceFlow]
    exact ⟨fun ⟨hb, hpos⟩ => ⟨⟨b, hb⟩, hpos, rfl⟩, fun ⟨c, hc, hcb⟩ => hcb ▸ ⟨c.2, hc⟩⟩
  have hne := B.supp_nonempty
  rw [hS] at hne ⊢
  refine (isTrap_map_iff _).2 ⟨Finset.map_nonempty.1 hne, ?_⟩
  simpa using (isCirculation_balanceFlow B).essential

/-- **Every edge carrying balance flow lies on a cycle** of the level-`w` carry graph: its head
leads back to its tail. -/
@[category research solved, AMS 11 37 05, group "carry_bridge_z32"]
theorem BalanceVec.reach_of_pos (B : BalanceVec w) {b b' : Fin (2 ^ w)} (h : 0 < B.ν b b') :
    (edgeGraph w).Reach b' b :=
  (isCirculation_balanceFlow B).reach_of_pos h

/-- The cells carrying balance mass lie in the core of the level-`w` carry graph. -/
@[category research solved, AMS 11 37 05, group "carry_bridge_z32"]
theorem BalanceVec.mem_core (B : BalanceVec w) {b : Fin (2 ^ w)} (h : 0 < B.μ b) :
    b ∈ (edgeGraph w).core :=
  (isCirculation_balanceFlow B).supp_subset_core (by simpa [flowSupp, outflow_balanceFlow] using h)

/-- A flow on the cells, extended by `0` to all of `ℕ × ℕ`. -/
noncomputable def extFlow (ν : Fin (2 ^ w) → Fin (2 ^ w) → ℝ) (b b' : ℕ) : ℝ :=
  if h : b < 2 ^ w then if h' : b' < 2 ^ w then ν ⟨b, h⟩ ⟨b', h'⟩ else 0 else 0

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem extFlow_fin (ν : Fin (2 ^ w) → Fin (2 ^ w) → ℝ) (b b' : Fin (2 ^ w)) :
    extFlow ν b b' = ν b b' := by
  simp [extFlow]

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem extFlow_pos {ν : Fin (2 ^ w) → Fin (2 ^ w) → ℝ} {b b' : ℕ} (h : 0 < extFlow ν b b') :
    ∃ (hb : b < 2 ^ w) (hb' : b' < 2 ^ w), 0 < ν ⟨b, hb⟩ ⟨b', hb'⟩ := by
  unfold extFlow at h
  split_ifs at h with hb hb'
  · exact ⟨hb, hb', h⟩
  all_goals exact absurd h (lt_irrefl 0)

/-- A circulation of mass `1` on the level-`w` carry graph, read as a balance vector. -/
noncomputable def toBalanceVec {ν : Fin (2 ^ w) → Fin (2 ^ w) → ℝ}
    (hc : (edgeGraph w).IsCirculation ν) (hm : ∑ v, outflow ν v = 1) : BalanceVec w where
  μ b := ∑ b' ∈ Finset.range (2 ^ w), extFlow ν b b'
  ν := extFlow ν
  ν_nonneg b b' := by
    unfold extFlow
    split_ifs
    · exact hc.nonneg _ _
    all_goals exact le_rfl
  sum_μ := by
    rw [← hm, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Fin.sum_univ_eq_sum_range, outflow]
    exact Finset.sum_congr rfl fun c _ => extFlow_fin ν b c
  out _ _ := rfl
  inn b' hb' := by
    rw [← Fin.sum_univ_eq_sum_range (fun b => extFlow ν b b'),
      ← Fin.sum_univ_eq_sum_range (fun c => extFlow ν b' c)]
    have h1 := hc.cons ⟨b', hb'⟩
    rw [outflow, inflow] at h1
    rw [Finset.sum_congr rfl fun c _ => extFlow_fin ν c ⟨b', hb'⟩,
      Finset.sum_congr rfl fun c _ => extFlow_fin ν ⟨b', hb'⟩ c, h1]
  adm b b' hpos := by
    obtain ⟨hb, hb', hp⟩ := extFlow_pos hpos
    have := under_edgeGraph.1 (hc.adm _ _ hp)
    simpa only [Fin.val_mk] using this

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem toBalanceVec_μ {ν : Fin (2 ^ w) → Fin (2 ^ w) → ℝ}
    (hc : (edgeGraph w).IsCirculation ν) (hm : ∑ v, outflow ν v = 1) (b : Fin (2 ^ w)) :
    (toBalanceVec hc hm).μ b = outflow ν b := by
  change ∑ b' ∈ Finset.range (2 ^ w), extFlow ν b b' = _
  rw [← Fin.sum_univ_eq_sum_range (fun c => extFlow ν b c), outflow]
  exact Finset.sum_congr rfl fun c _ => extFlow_fin ν b c

/-- **The balance lemma** (`Z32.exists_balanceVec`), re-derived from the generic
`exists_circulation_of_walk`: the cells of the orbit form an infinite walk of the level-`w`
carry graph. -/
@[category research solved, AMS 11 37 05, group "carry_bridge_z32"]
theorem exists_balanceVec' (β ξ : ℝ) (w : ℕ)
    (hadm : ∀ n, edgeOk w (cell w (ξ * β ^ n)) (cell w (ξ * β ^ (n + 1))) = true)
    (Nseq : ℕ → ℕ) (hNseq : Tendsto Nseq atTop atTop) :
    ∃ (B : BalanceVec w) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ b < 2 ^ w, Tendsto (fun k => freqVec β ξ w (Nseq (φ k)) b) atTop (𝓝 (B.μ b)) := by
  classical
  let x : ℕ → Fin (2 ^ w) := fun n => ⟨cell w (ξ * β ^ n), cell_lt _ _⟩
  obtain ⟨ν, φ, hc, hm, hφ, -, hf⟩ :=
    exists_circulation_of_walk x (fun n => under_edgeGraph.2 (hadm n)) Nseq hNseq
  refine ⟨toBalanceVec hc hm, φ, hφ, fun b hb => ?_⟩
  have hfr : ∀ N, freqVec β ξ w N b = empFreq x N ⟨b, hb⟩ := fun N => by
    have hcongr : ((Finset.range N).filter fun n => cell w (ξ * β ^ n) = b)
        = (Finset.range N).filter fun n => x n = ⟨b, hb⟩ :=
      Finset.filter_congr fun n _ => by simp [x, Fin.ext_iff]
    rw [freqVec, CarryGraph.empFreq, CarryGraph.visits, winCount_eq_card β ξ hb N, hcongr]
  have := hf ⟨b, hb⟩
  rw [← toBalanceVec_μ hc hm ⟨b, hb⟩] at this
  simpa only [hfr] using this

end Balance

end CarryBridge
