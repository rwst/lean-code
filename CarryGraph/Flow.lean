/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Circulations ([BJG09] ch. 3)

A **circulation** on a finite carry graph is a nonnegative real weight on the arcs of the
underlying digraph that is conserved at every vertex: what flows out of `v` equals what flows
in.  Circulations are the finite-resolution form of invariant measures: the transition
frequencies of an infinite walk converge, along a subsequence, to a circulation of total mass `1`
(`exists_circulation_of_walk`).  This is the balance lemma of the `3/2` density problem, stated
for every carry graph.

The structure of a circulation is read off the graph:

* `IsCirculation.essential` — the vertices carrying flow form an essential set, so they lie in
  the core (`IsCirculation.supp_subset_core`);
* `IsCirculation.reach_of_pos` — every arc carrying flow lies on a cycle: the flow cannot leave
  the set of vertices reachable from the head of the arc without coming back.  Hence a graph
  without cycles carries no circulation but `0` (`IsCirculation.eq_zero_of_not_cyc`);
* `IsCirculation.noBranch_perm` — on a graph without branching inside its strong components
  (zero entropy, Chapter 4) a circulation is a weighted sum of simple cycles: the support carries
  an injective successor map `σ`, all flow out of `v` goes to `σ v`, and the mass is constant
  along `σ`.
* `exists_circulation_avoiding` — a vertex visited with lower frequency `0` is avoided by some
  circulation of mass `1`, whose support is then an essential set without that vertex.

Flows live on the underlying digraph (`under`), not on labelled arcs.

## References

* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009, ch. 3.
-/

open Filter Topology

namespace CarryGraph

variable {V A : Type*} [Fintype V] (X : CarryGraph V A)

/-! ### Circulations -/

/-- The flow leaving `v`. -/
def outflow (ν : V → V → ℝ) (v : V) : ℝ := ∑ w, ν v w

/-- The flow entering `v`. -/
def inflow (ν : V → V → ℝ) (v : V) : ℝ := ∑ u, ν u v

/-- A **circulation**: a nonnegative flow on the arcs of the underlying digraph, conserved at
every vertex. -/
structure IsCirculation (ν : V → V → ℝ) : Prop where
  /-- Flows are nonnegative. -/
  nonneg : ∀ v w, 0 ≤ ν v w
  /-- Flow runs along arcs only. -/
  adm : ∀ v w, 0 < ν v w → X.under v w
  /-- Conservation. -/
  cons : ∀ v, outflow ν v = inflow ν v

/-- The **support** of a flow: the vertices with positive outflow. -/
def flowSupp (ν : V → V → ℝ) : Set V := {v | 0 < outflow ν v}

variable {X} {ν : V → V → ℝ}

omit [Fintype V] in
private theorem exists_pos_of_sum_pos {s : Finset V} {f : V → ℝ} (h : 0 < ∑ x ∈ s, f x) :
    ∃ x ∈ s, 0 < f x := by
  by_contra hc
  push Not at hc
  exact absurd (Finset.sum_nonpos hc) (not_le.2 h)

namespace IsCirculation

variable (h : X.IsCirculation ν)
include h

@[category API, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem outflow_nonneg (v : V) : 0 ≤ outflow ν v :=
  Finset.sum_nonneg fun w _ => h.nonneg v w

@[category API, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem le_outflow (v w : V) : ν v w ≤ outflow ν v :=
  Finset.single_le_sum (f := ν v) (fun x _ => h.nonneg v x) (Finset.mem_univ w)

@[category API, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem le_inflow (v w : V) : ν v w ≤ inflow ν w :=
  Finset.single_le_sum (f := fun u => ν u w) (fun x _ => h.nonneg x w) (Finset.mem_univ v)

@[category API, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem mem_flowSupp_of_pos {v w : V} (hp : 0 < ν v w) : v ∈ flowSupp ν ∧ w ∈ flowSupp ν :=
  ⟨hp.trans_le (h.le_outflow v w), hp.trans_le ((h.le_inflow v w).trans_eq (h.cons w).symm)⟩

/-- **The support is essential**: every vertex carrying flow sends flow to, and receives flow
from, a vertex carrying flow. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem essential : X.Essential (flowSupp ν) := by
  intro v hv
  refine ⟨?_, ?_⟩
  · obtain ⟨w, -, hw⟩ := exists_pos_of_sum_pos (s := Finset.univ) (f := ν v) hv
    exact ⟨w, (h.mem_flowSupp_of_pos hw).2, h.adm v w hw⟩
  · have hin : 0 < inflow ν v := (h.cons v) ▸ hv
    obtain ⟨u, -, hu⟩ := exists_pos_of_sum_pos (s := Finset.univ) (f := fun u => ν u v) hin
    exact ⟨u, (h.mem_flowSupp_of_pos hu).1, h.adm u v hu⟩

/-- The support of a circulation lies in the core. -/
@[category textbook, AMS 05 90, ref "BJG09" "LM95", group "carry_flow"]
theorem supp_subset_core : flowSupp ν ⊆ X.core :=
  subset_core_of_essential h.essential

/-- **Every arc carrying flow lies on a cycle.**  Let `R` be the set of vertices reachable from
`w`.  No flow leaves `R`, so by conservation summed over `R` no flow enters `R` either; the arc
`v → w` enters `R` unless `v ∈ R`. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem reach_of_pos {v w : V} (hp : 0 < ν v w) : X.Reach w v := by
  classical
  by_contra hn
  set R := Finset.univ.filter (X.Reach w) with hR
  set Rc := Finset.univ.filter fun x => ¬ X.Reach w x with hRc
  have hout : ∀ u ∈ R, outflow ν u = ∑ x ∈ R, ν u x := by
    intro u hu
    have hu' : X.Reach w u := (Finset.mem_filter.1 hu).2
    rw [outflow, ← Finset.sum_filter_add_sum_filter_not Finset.univ (X.Reach w)]
    refine add_eq_left.2 (Finset.sum_eq_zero fun x hx => ?_)
    refine le_antisymm (not_lt.1 fun hpos => ?_) (h.nonneg u x)
    exact (Finset.mem_filter.1 hx).2 (hu'.tail (h.adm u x hpos))
  have hin : ∀ u, inflow ν u = ∑ x ∈ R, ν x u + ∑ x ∈ Rc, ν x u := fun u => by
    rw [inflow, ← Finset.sum_filter_add_sum_filter_not Finset.univ (X.Reach w)]
  have htot : ∑ u ∈ R, outflow ν u = ∑ u ∈ R, inflow ν u :=
    Finset.sum_congr rfl fun u _ => h.cons u
  rw [Finset.sum_congr rfl hout, Finset.sum_congr rfl fun u _ => hin u, Finset.sum_add_distrib,
    Finset.sum_comm (s := R) (t := R)] at htot
  have hzero : ∑ u ∈ R, ∑ x ∈ Rc, ν x u = 0 := by linarith
  have hwR : w ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ _, Reach.refl w⟩
  have hvRc : v ∈ Rc := Finset.mem_filter.2 ⟨Finset.mem_univ _, hn⟩
  have h1 : ν v w ≤ ∑ x ∈ Rc, ν x w :=
    Finset.single_le_sum (f := fun x => ν x w) (fun x _ => h.nonneg x w) hvRc
  have h2 : ∑ x ∈ Rc, ν x w ≤ ∑ u ∈ R, ∑ x ∈ Rc, ν x u :=
    Finset.single_le_sum (f := fun u => ∑ x ∈ Rc, ν x u)
      (fun u _ => Finset.sum_nonneg fun x _ => h.nonneg x u) hwR
  linarith

/-- The tail of an arc carrying flow is cyclic. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem cyc_of_pos {v w : V} (hp : 0 < ν v w) : X.Cyc v :=
  cyc_iff.2 ⟨w, h.adm v w hp, h.reach_of_pos hp⟩

/-- Both ends of an arc carrying flow lie in one strong component. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem sameSCC_of_pos {v w : V} (hp : 0 < ν v w) : X.SameSCC v w :=
  ⟨Reach.single (h.adm v w hp), h.reach_of_pos hp⟩

/-- A graph without cycles carries only the zero circulation. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem eq_zero_of_not_cyc (hX : ∀ v, ¬ X.Cyc v) (v w : V) : ν v w = 0 :=
  le_antisymm (not_lt.1 fun hp => hX v (h.cyc_of_pos hp)) (h.nonneg v w)

/-! ### Zero entropy: circulations are sums of simple cycles -/

/-- Without branching inside strong components, at most one arc out of each vertex carries
flow. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem eq_of_pos_of_noBranch (hX : X.NoBranch) {v w u : V} (hw : 0 < ν v w) (hu : 0 < ν v u) :
    w = u :=
  hX v w u (h.adm v w hw) (h.adm v u hu) (h.reach_of_pos hw) (h.reach_of_pos hu)

/-- Without branching, all flow out of `v` runs along the one arc that carries any. -/
@[category textbook, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem outflow_eq_of_noBranch (hX : X.NoBranch) {v w : V} (hw : 0 < ν v w) :
    outflow ν v = ν v w := by
  refine Finset.sum_eq_single w (fun u _ hu => ?_) (fun hw' => absurd (Finset.mem_univ w) hw')
  exact le_antisymm (not_lt.1 fun hp => hu (h.eq_of_pos_of_noBranch hX hw hp).symm)
    (h.nonneg v u)

/-- **Circulations on a zero-entropy graph** (the zero-entropy case of the decomposition of a
circulation into cycles, [BJG09] ch. 3).  If no vertex branches inside its strong component,
there is a successor map `σ` that is injective on the support of `ν`, maps it into itself,
carries all the flow (`ν v w` is the outflow of `v` when `w = σ v`, and `0` otherwise), and
keeps the outflow constant.  So `σ`
permutes the support, its cycles are simple cycles of the graph, and `ν` is the sum over these
cycles of a constant weight times the cycle's indicator. -/
@[category research solved, AMS 05 90, ref "BJG09", group "carry_flow"]
theorem noBranch_perm [DecidableEq V] (hX : X.NoBranch) :
    ∃ σ : V → V, Set.MapsTo σ (flowSupp ν) (flowSupp ν) ∧ Set.InjOn σ (flowSupp ν) ∧
      (∀ v ∈ flowSupp ν, ∀ w, ν v w = if w = σ v then outflow ν v else 0) ∧
      ∀ v ∈ flowSupp ν, outflow ν (σ v) = outflow ν v := by
  classical
  have hex : ∀ v ∈ flowSupp ν, ∃ w, 0 < ν v w := fun v hv => by
    obtain ⟨w, -, hw⟩ := exists_pos_of_sum_pos (s := Finset.univ) (f := ν v) hv
    exact ⟨w, hw⟩
  choose! σ hσ using hex
  have hσeq : ∀ {v w}, 0 < ν v w → σ v = w := fun {v w} hw =>
    h.eq_of_pos_of_noBranch hX (hσ v (h.mem_flowSupp_of_pos hw).1) hw
  have hmaps : Set.MapsTo σ (flowSupp ν) (flowSupp ν) := fun v hv =>
    (h.mem_flowSupp_of_pos (hσ v hv)).2
  -- σ is onto the support, hence injective on it
  set S := Finset.univ.filter (· ∈ flowSupp ν) with hS
  have hmemS : ∀ {v}, v ∈ S ↔ v ∈ flowSupp ν := by simp [hS]
  have hsurj : ∀ w ∈ S, ∃ v, ∃ (_ : v ∈ S), σ v = w := by
    intro w hw
    have hin : 0 < inflow ν w := (h.cons w) ▸ hmemS.1 hw
    obtain ⟨u, -, hu⟩ := exists_pos_of_sum_pos (s := Finset.univ) (f := fun u => ν u w) hin
    exact ⟨u, hmemS.2 (h.mem_flowSupp_of_pos hu).1, hσeq hu⟩
  have hinj : Set.InjOn σ (flowSupp ν) := fun a ha b hb hab =>
    Finset.inj_on_of_surj_on_of_card_le (s := S) (t := S) (fun v _ => σ v)
      (fun v hv => hmemS.2 (hmaps (hmemS.1 hv))) hsurj le_rfl (hmemS.2 ha) (hmemS.2 hb) hab
  refine ⟨σ, hmaps, hinj, fun v hv w => ?_, fun v hv => ?_⟩
  · rw [h.outflow_eq_of_noBranch hX (hσ v hv)]
    split_ifs with hw
    · rw [hw]
    · exact le_antisymm (not_lt.1 fun hp => hw (hσeq hp).symm) (h.nonneg v w)
  · rw [h.cons, inflow, h.outflow_eq_of_noBranch hX (hσ v hv)]
    refine Finset.sum_eq_single v (fun u _ hu => ?_) (fun hv' => absurd (Finset.mem_univ v) hv')
    refine le_antisymm (not_lt.1 fun hp => hu ?_) (h.nonneg u _)
    exact hinj (h.mem_flowSupp_of_pos hp).1 hv (hσeq hp)

end IsCirculation

/-! ### Empirical flows of a walk -/

section Empirical

variable [DecidableEq V] (x : ℕ → V)

/-- The number of dates `n < N` at which the walk `x` visits `v`. -/
def visits (N : ℕ) (v : V) : ℕ := ((Finset.range N).filter fun n => x n = v).card

/-- The number of dates `n < N` at which the walk `x` steps from `v` to `w`. -/
def transits (N : ℕ) (v w : V) : ℕ :=
  ((Finset.range N).filter fun n => x n = v ∧ x (n + 1) = w).card

/-- The empirical frequency of `v` among the first `N` dates. -/
noncomputable def empFreq (N : ℕ) (v : V) : ℝ := (visits x N v : ℝ) / N

/-- The empirical flow: the frequency of the step `v → w` among the first `N` steps. -/
noncomputable def empFlow (N : ℕ) (v w : V) : ℝ := (transits x N v w : ℝ) / N

/-- The out-marginal of the transition counts is the visit count, exactly. -/
@[category API, AMS 05 37, group "carry_flow"]
theorem sum_transits_out (N : ℕ) (v : V) : ∑ w, transits x N v w = visits x N v := by
  rw [visits, Finset.card_eq_sum_card_fiberwise (f := fun n => x (n + 1)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [transits, Finset.filter_filter]

/-- The in-marginal of the transition counts: the dates whose successor visits `w`. -/
@[category API, AMS 05 37, group "carry_flow"]
theorem sum_transits_in (N : ℕ) (w : V) :
    ∑ v, transits x N v w = ((Finset.range N).filter fun n => x (n + 1) = w).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := x) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [transits, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun n _ => by tauto)

private theorem card_filter_range_succ (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    ((Finset.range (N + 1)).filter Q).card
      = ((Finset.range N).filter Q).card + (if Q N then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hq : Q N
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hq), ite_eq_left_of_eq_true _ _ (eq_true hq),
      Finset.card_insert_of_notMem (by simp)]
  · simp [hq]

private theorem card_filter_shift (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    ((Finset.range N).filter fun n => Q (n + 1)).card + (if Q 0 then 1 else 0)
      = ((Finset.range (N + 1)).filter Q).card := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.zero_add,
      Finset.range_one, Finset.filter_singleton]
    split <;> simp
  | succ N ih =>
    rw [card_filter_range_succ (fun n => Q (n + 1)) N, card_filter_range_succ Q (N + 1)]
    omega

/-- **The in-marginal is exact up to the boundary**: the steps into `w` and the visits to `w`
differ by at most one. -/
@[category API, AMS 05 37, group "carry_flow"]
theorem abs_sum_transits_in_sub (N : ℕ) (w : V) :
    |((∑ v, transits x N v w : ℕ) : ℝ) - (visits x N w : ℝ)| ≤ 1 := by
  set Q : ℕ → Prop := fun n => x n = w
  have key : (∑ v, transits x N v w) + (if Q 0 then 1 else 0)
      = visits x N w + (if Q N then 1 else 0) := by
    rw [sum_transits_in, card_filter_shift Q N, card_filter_range_succ Q N]
    rfl
  have hz : -1 ≤ ((∑ v, transits x N v w : ℕ) : ℤ) - ((visits x N w : ℕ) : ℤ) ∧
      ((∑ v, transits x N v w : ℕ) : ℤ) - ((visits x N w : ℕ) : ℤ) ≤ 1 := by
    by_cases h0 : Q 0 <;> by_cases hN : Q N <;> simp only [h0, hN, ite_true, ite_false] at key <;>
      omega
  rw [abs_le]
  exact ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2⟩

/-- The visits partition the dates. -/
@[category API, AMS 05 37, group "carry_flow"]
theorem sum_visits (N : ℕ) : ∑ v, visits x N v = N := by
  conv_rhs => rw [← Finset.card_range N, Finset.card_eq_sum_card_fiberwise (f := x)
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rfl

omit [Fintype V] in
@[category API, AMS 05 37, group "carry_flow"]
theorem empFlow_nonneg (N : ℕ) (v w : V) : 0 ≤ empFlow x N v w := by unfold empFlow; positivity

omit [Fintype V] in
@[category API, AMS 05 37, group "carry_flow"]
theorem empFlow_le_one (N : ℕ) (v w : V) : empFlow x N v w ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [empFlow, hN]
  · rw [empFlow, div_le_one (by exact_mod_cast hN)]
    have := Finset.card_le_card (Finset.filter_subset
      (fun n => x n = v ∧ x (n + 1) = w) (Finset.range N))
    rw [Finset.card_range] at this
    exact_mod_cast this

/-- **The balance lemma.**  Along any sequence of horizons tending to infinity, the empirical
flows of an infinite walk have a convergent subsequence; the limit is a circulation of total
mass `1`, and the empirical frequencies converge along the same subsequence to its outflows.
(Bolzano–Weierstrass on the cube `[0,1]^{V × V}`: the out-marginal is exact, the in-marginal
costs `1/N`.) -/
@[category research solved, AMS 05 37, ref "BJG09", group "carry_flow"]
theorem exists_circulation_of_walk (hx : ∀ n, X.under (x n) (x (n + 1))) (Nseq : ℕ → ℕ)
    (hN : Tendsto Nseq atTop atTop) :
    ∃ (ν : V → V → ℝ) (φ : ℕ → ℕ), X.IsCirculation ν ∧ ∑ v, outflow ν v = 1 ∧ StrictMono φ ∧
      (∀ v w, Tendsto (fun k => empFlow x (Nseq (φ k)) v w) atTop (𝓝 (ν v w))) ∧
      ∀ v, Tendsto (fun k => empFreq x (Nseq (φ k)) v) atTop (𝓝 (outflow ν v)) := by
  have hcpt : IsCompact (Set.univ.pi fun _ : V × V => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq
    (x := fun k (q : V × V) => empFlow x (Nseq k) q.1 q.2)
    (fun k => Set.mem_univ_pi.2 fun q => ⟨empFlow_nonneg x _ _ _, empFlow_le_one x _ _ _⟩)
  set M : ℕ → ℕ := fun k => Nseq (φ k)
  have hM : Tendsto M atTop atTop := hN.comp hφ.tendsto_atTop
  set ν : V → V → ℝ := fun v w => a (v, w)
  have hν : ∀ v w, Tendsto (fun k => empFlow x (M k) v w) atTop (𝓝 (ν v w)) := fun v w =>
    (tendsto_pi_nhds.1 hlim) (v, w)
  have hnonneg : ∀ v w, 0 ≤ ν v w := fun v w =>
    ge_of_tendsto' (hν v w) fun k => empFlow_nonneg x _ _ _
  have hfreq : ∀ v, Tendsto (fun k => empFreq x (M k) v) atTop (𝓝 (outflow ν v)) := by
    intro v
    refine (tendsto_finsetSum _ fun w _ => hν v w).congr fun k => ?_
    simp only [empFlow, empFreq, ← Finset.sum_div, ← Nat.cast_sum, sum_transits_out]
  have hzero : Tendsto (fun k => 1 / (M k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hM
  have hcons : ∀ w, outflow ν w = inflow ν w := by
    intro w
    have h1 : Tendsto (fun k => ∑ v, empFlow x (M k) v w) atTop (𝓝 (inflow ν w)) :=
      tendsto_finsetSum _ fun v _ => hν v w
    have hdiff : Tendsto (fun k => (∑ v, empFlow x (M k) v w) - empFreq x (M k) w) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm
        (f := fun k => (∑ v, empFlow x (M k) v w) - empFreq x (M k) w) (fun k => ?_) hzero
      rcases Nat.eq_zero_or_pos (M k) with h0 | hpos
      · simp [empFlow, empFreq, h0]
      · have hNR : (0 : ℝ) < M k := by exact_mod_cast hpos
        simp only [empFlow, empFreq, ← Finset.sum_div, Real.norm_eq_abs]
        rw [← Nat.cast_sum, div_sub_div_same, abs_div, abs_of_pos hNR]
        gcongr
        exact abs_sum_transits_in_sub x (M k) w
    have h2 := (hfreq w).add hdiff
    rw [add_zero] at h2
    exact tendsto_nhds_unique (h2.congr fun k => by ring) h1
  have hmass : ∑ v, outflow ν v = 1 := by
    have h1 : Tendsto (fun k => ∑ v, empFreq x (M k) v) atTop (𝓝 (∑ v, outflow ν v)) :=
      tendsto_finsetSum _ fun v _ => hfreq v
    refine tendsto_nhds_unique h1 (Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [hM.eventually_ge_atTop 1] with k hk
    have hNR : (M k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < M k := by exact_mod_cast hk
      exact this.ne'
    simp only [empFreq, ← Finset.sum_div, ← Nat.cast_sum, sum_visits, div_self hNR]
  have hadm : ∀ v w, 0 < ν v w → X.under v w := by
    intro v w hpos
    obtain ⟨k, hk⟩ := ((hν v w).eventually (lt_mem_nhds hpos)).exists
    have hcard : transits x (M k) v w ≠ 0 := by
      intro h0
      simp [empFlow, h0] at hk
    obtain ⟨n, hn⟩ := Finset.card_ne_zero.1 hcard
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hn
    rw [← h1, ← h2]
    exact hx n
  exact ⟨ν, φ, ⟨hnonneg, hadm, hcons⟩, hmass, hφ, hν, hfreq⟩

/-- **A vertex of lower frequency `0` is avoided by a circulation.**  If the walk visits `v` with
frequency tending to `0` along some horizons, there is a circulation of mass `1` with no flow
through `v`; its support is an essential set (`IsCirculation.essential`) that avoids `v`. -/
@[category research solved, AMS 05 37, ref "BJG09", group "carry_flow"]
theorem exists_circulation_avoiding (hx : ∀ n, X.under (x n) (x (n + 1))) {v : V}
    (Nseq : ℕ → ℕ) (hN : Tendsto Nseq atTop atTop)
    (hv : Tendsto (fun k => empFreq x (Nseq k) v) atTop (𝓝 0)) :
    ∃ ν : V → V → ℝ, X.IsCirculation ν ∧ ∑ u, outflow ν u = 1 ∧ outflow ν v = 0 := by
  obtain ⟨ν, φ, hc, hm, hφ, -, hf⟩ := exists_circulation_of_walk x hx Nseq hN
  exact ⟨ν, hc, hm, tendsto_nhds_unique (hf v) (hv.comp hφ.tendsto_atTop)⟩

end Empirical

end CarryGraph
