/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.NFGraphs
import Oda26.WaitingTime

/-!
# Rank certificates from certified graphs

[Oda26] §6.2 turns a finished word-graph certificate into a *rank certificate* (`Oda.RankCert`) and
then into an explicit waiting time (Theorem 27, `Oda.waiting_time`).  This file does the first step
once and for all: **every finite single-letter graph all of whose strongly connected components
pass the phase test (`AllCert`) carries a rank certificate**, with

* blocks = the strongly connected components (`Oda.WG.SCC`),
* rank `ρ` = the number of vertices reaching the block (strictly increasing along inter-block
  edges),
* `η` = the number of vertices on cyclic components reaching the block,
* phase, period and labelling = those of the phase test of the block.

Hence `ρ, η ≤ |V|`, and Theorem 27 gives a waiting time for every orbit segment inside the graph,
for every shift `ν` (`Oda.WG.waiting_time_of_allCert`): `T ≤ G(|V|, |V| − 1)` with
`G(e, r) = γ^e·r + (A + γD)·∑_{j<e} γ^j`, so `T = O(log ξ)` with constants depending only on the
graph.  By `Oda.WG.allCert_iff_allPer` the hypothesis is equivalent to "every infinite walk has
eventually periodic output", which is what a `DubC2.Gen.Checked` certificate proves
(`DubC2/OdaBridge.lean`).

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open Finset
open scoped Classical

variable {V : Type*}

/-- Being in the same strongly connected component, as a setoid. -/
def sccSetoid (E : Graph V ℤ) : Setoid V where
  r := SameSCC E
  iseqv := ⟨fun _ => ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
    fun h => h.symm, fun h h' => h.trans h'⟩

/-- The strongly connected components. -/
abbrev SCC (E : Graph V ℤ) := Quotient (sccSetoid E)

/-- The component of `u`. -/
abbrev scc (E : Graph V ℤ) (u : V) : SCC E := Quotient.mk (sccSetoid E) u

theorem out_scc (E : Graph V ℤ) (u : V) : SameSCC E (scc E u).out u :=
  Quotient.exact (Quotient.out_eq (scc E u))

theorem scc_eq_iff {E : Graph V ℤ} {u v : V} : scc E u = scc E v ↔ SameSCC E u v :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem reach_of_edge {E : Graph V ℤ} {u v : V} {w : List ℤ} (h : E u w v) : Reach E u v :=
  Relation.ReflTransGen.single ⟨w, h⟩

/-- The vertices reaching `x`. -/
noncomputable def preds [Fintype V] (E : Graph V ℤ) (x : V) : Finset V := univ.filter fun y => Reach E y x

/-- `x` lies on a cyclic component: its component has an internal edge. -/
def Cyc (E : Graph V ℤ) (x : V) : Prop :=
  ∃ u c v, E u [c] v ∧ SameSCC E x u ∧ SameSCC E x v

/-- The vertices on cyclic components reaching `x`. -/
noncomputable def cpreds [Fintype V] (E : Graph V ℤ) (x : V) : Finset V :=
  univ.filter fun y => Reach E y x ∧ Cyc E y

theorem preds_eq [Fintype V] {E : Graph V ℤ} {x y : V} (h : SameSCC E x y) : preds E x = preds E y := by
  ext z; simp only [preds, mem_filter, mem_univ, true_and]
  exact ⟨fun hz => hz.trans h.1, fun hz => hz.trans h.2⟩

theorem cpreds_eq [Fintype V] {E : Graph V ℤ} {x y : V} (h : SameSCC E x y) : cpreds E x = cpreds E y := by
  ext z; simp only [cpreds, mem_filter, mem_univ, true_and]
  exact ⟨fun hz => ⟨hz.1.trans h.1, hz.2⟩, fun hz => ⟨hz.1.trans h.2, hz.2⟩⟩

theorem cyc_of_sameSCC {E : Graph V ℤ} {x y : V} (h : SameSCC E x y) (hx : Cyc E x) : Cyc E y := by
  obtain ⟨u, c, v, he, hu, hv⟩ := hx
  exact ⟨u, c, v, he, h.symm.trans hu, h.symm.trans hv⟩

/-- Across an inter-component edge `u → v`, `preds u ⊊ preds v`. -/
theorem preds_ssubset [Fintype V] {E : Graph V ℤ} {u v : V} {w : List ℤ} (he : E u w v)
    (hne : ¬ SameSCC E u v) : preds E u ⊂ preds E v := by
  refine Finset.ssubset_iff_of_subset (fun z hz => ?_) |>.2 ⟨v, ?_, ?_⟩
  · simp only [preds, mem_filter, mem_univ, true_and] at hz ⊢
    exact hz.trans (reach_of_edge he)
  · simp only [preds, mem_filter, mem_univ, true_and]; exact Relation.ReflTransGen.refl
  · simp only [preds, mem_filter, mem_univ, true_and]
    exact fun hvu => hne ⟨reach_of_edge he, hvu⟩

section Data

variable {E : Graph V ℤ} (hc : AllCert E)
include hc

/-- The phase of the test passed by the component of `x`. -/
noncomputable def phH (x : V) : V → ℤ := Classical.choose (hc x)

/-- The period of the test passed by the component of `x`. -/
noncomputable def phD (x : V) : ℕ := Classical.choose (Classical.choose_spec (hc x))

/-- The labelling of the test passed by the component of `x`. -/
noncomputable def phL (x : V) : ℤ → ℤ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (hc x)))

theorem ph_spec (x : V) : 0 < phD hc x ∧ ∀ u w v, E u w v → SameSCC E x u → SameSCC E x v →
    phH hc x v ≡ phH hc x u + w.length [ZMOD phD hc x] ∧
      ∀ i (hi : i < w.length), w[i] = phL hc x ((phH hc x u + i) % phD hc x) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hc x)))

end Data

/-- **The rank certificate of a certified graph.** -/
noncomputable def rankCertOf [Fintype V] (E : Graph V ℤ) (hc : AllCert E) : RankCert V (SCC E) where
  E u c v := E u [c] v
  blk := scc E
  ρ B := (preds E B.out).card
  per B := decide (Cyc E B.out)
  d B := phD hc B.out
  h v := phH hc (scc E v).out v
  lam B := phL hc B.out
  η B := (cpreds E B.out).card
  rank_step u c v he hne := by
    rw [preds_eq (out_scc E u), preds_eq (out_scc E v)]
    exact Finset.card_lt_card (preds_ssubset he fun h => hne (scc_eq_iff.2 h))
  internal_per u c v he hb := by
    simp only [decide_eq_true_eq]
    have hv : SameSCC E (scc E u).out v := by rw [hb]; exact out_scc E v
    exact ⟨u, c, v, he, out_scc E u, hv⟩
  d_pos B _ := (ph_spec hc B.out).1
  internal u c v he hb := by
    have hv : SameSCC E (scc E u).out v := by rw [hb]; exact out_scc E v
    have := (ph_spec hc (scc E u).out).2 u [c] v he (out_scc E u) hv
    refine ⟨?_, ?_⟩
    · show phH hc (scc E v).out v ≡ _ [ZMOD _]
      rw [← hb]; simpa using this.1
    · have h2 := this.2 0 (by simp)
      simpa using h2
  eta_per B hB := by
    simp only [decide_eq_true_eq] at hB
    refine Finset.card_pos.2 ⟨B.out, ?_⟩
    simp only [cpreds, mem_filter, mem_univ, true_and]
    exact ⟨Relation.ReflTransGen.refl, hB⟩
  eta_step u c v he hne := by
    have hns : ¬ SameSCC E u v := fun h => hne (scc_eq_iff.2 h)
    rw [cpreds_eq (out_scc E u), cpreds_eq (out_scc E v)]
    have hsub : cpreds E u ⊆ cpreds E v := fun z hz => by
      simp only [cpreds, mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨hz.1.trans (reach_of_edge he), hz.2⟩
    split_ifs with hp
    · simp only [decide_eq_true_eq] at hp
      have hcv : Cyc E v := cyc_of_sameSCC (out_scc E v) hp
      refine Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨v, ?_, ?_⟩)
      · simp only [cpreds, mem_filter, mem_univ, true_and]
        exact ⟨Relation.ReflTransGen.refl, hcv⟩
      · simp only [cpreds, mem_filter, mem_univ, true_and]
        exact fun h => hns ⟨reach_of_edge he, h.1⟩
    · simpa using Finset.card_le_card hsub

/-- **Waiting time for certified graphs** (Theorem 27 applied to `rankCertOf`).  If every
component of the finite single-letter graph `E` passes the phase test, there is a constant `D`
such that, for every shift `ν` and every `ξ` with `P = ⌊ξ + ν⌋ ≥ b/(a−b) + |ν|`, an orbit segment
of `⌊ξ(a/b)ⁿ + ν⌋` of length `T` whose carries label a walk of `E` has
`T ≤ γ^{|V|}(|V| − 1) + (A + γD)·∑_{j<|V|} γ^j`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_waiting"]
theorem waiting_time_of_allCert [Fintype V] {E : Graph V ℤ} (hc : AllCert E) :
    ∃ D : ℕ, ∀ {a b : ℕ} {ξ ν : ℝ}, 1 < b → b < a → Nat.Coprime a b → ∀ {P : ℤ},
      (P : ℝ) ≤ ξ + ν → ξ + ν < P + 1 → (b : ℝ) / (a - b) + |ν| ≤ P → ∀ {γ A : ℝ},
      1 + Real.logb b ((a : ℝ) / b) ≤ γ → Real.logb b (P + 2 + 2 * |ν|) ≤ A →
      ∀ {σ : ℕ → V} {T : ℕ}, (∀ n < T, E (σ n) [cf a b ξ ν n] (σ (n + 1))) →
      (T : ℝ) ≤ Gpot γ (A + γ * D) (Fintype.card V) (Fintype.card V - 1 : ℕ) := by
  refine ⟨univ.sup fun x : V => phD hc (scc E x).out, ?_⟩
  intro a b ξ ν hb hab hcop P hξ0 hξ1 hP γ A hγ hA σ T hwalk
  set H := rankCertOf E hc
  refine waiting_time H hb hab hcop hξ0 hξ1 hP hγ hA (ρmax := Fintype.card V)
    (m := Fintype.card V) (fun B => ?_) (fun B => Finset.card_le_univ _) (fun B _ => ?_)
    (fun B => Finset.card_le_univ _) hwalk
  · refine Finset.card_pos.2 ⟨B.out, ?_⟩
    simp only [preds, mem_filter, mem_univ, true_and]; exact Relation.ReflTransGen.refl
  · show phD hc B.out ≤ _
    have : B = scc E B.out := (Quotient.out_eq B).symm
    conv_lhs => rw [this]
    exact Finset.le_sup (f := fun x : V => phD hc (scc E x).out) (mem_univ B.out)

end Oda.WG
