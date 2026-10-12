/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.ZeroEntropy

/-!
# Right covers, state splitting and line graphs ([LM95] §§2.3, 2.4; [BJG09] §4.5)

Three re-encodings of the state space of a carry graph that change the vertex count but not the
growth of the number of paths.

* **Right covers.**  `RightCover X Y p U`: on a set `U` closed under successors, `p : W → V`
  maps the `a`-successors of `y` bijectively onto the `a`-successors of `p y`.  Path counts
  agree on `U` (`npaths_eq_of_rightCover`).  If moreover every vertex outside `U` is a sink and
  every vertex of `X` is a sink or lifts into `U`, the total path counts agree up to a constant
  factor, so the entropy, zero entropy and the emptiness of the core are the same
  (`entropy_eq_of_rightCover`, `lnoBranch_iff_of_rightCover`, `core_eq_empty_iff_of_rightCover`).
* **In-splitting** [LM95, Def. 2.4.7] `inSplit X π`: the copy `(u, c)` of `u` has an arc
  `(u, c) →a (v, π u a v)` for every arc `u →a v`; the class `π u a v` partitions the arcs
  *into* `v`.  The first projection is a right cover (`inSplit_rightCover`).
* **Out-splitting** [LM95, Def. 2.4.3] `outSplit X π`: the copy `(u, c)` keeps the arcs out of
  `u` of class `c`, into every copy of their target.  The copies of `u` together carry
  `|C|` times the paths of `u` (`sum_npaths_outSplit`).
* **The line graph** [BJG09, §4.5], the edge graph `X^{[2]}` of [LM95, Def. 2.3.4] (as a carry
  graph: arcs labelled by the second letter): vertices are arcs, and `(u, a, v) →b (v, b, w)`.
  It counts the paths of `X` shifted by one (`ntot_lineGraph`).  Iterating it gives the higher
  block graphs `X^{[n]}`.

Entropy (`entropy_inSplit`, `entropy_outSplit`, `entropy_lineGraph`), zero entropy
(`lnoBranch_*_iff`) and `core = ∅` (`core_*`) are invariant under all of them.  The one analytic
input is the shift invariance of the exponential growth rate of a sequence with
`u (n + 1) ≤ c · u n` (`expGrowthSup_shift`).

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
-/

open Filter ENNReal ExpGrowth

namespace CarryGraph

variable {V W A C : Type*} {X : CarryGraph V A} {Y : CarryGraph W A}

/-! ### Two facts about exponential growth rates -/

@[category API, AMS 26 40, group "carry_splitting"]
theorem ereal_div_succ_le {x : EReal} (hx : 0 ≤ x ∨ x = ⊥) {n : ℕ} (hn : 1 ≤ n) :
    x / ((n + 1 : ℕ) : EReal) ≤ x / (n : EReal) := by
  rcases hx with hx | rfl
  · induction x using EReal.rec with
    | bot => simp at hx
    | top =>
      rw [EReal.top_div_of_pos_ne_top (by exact_mod_cast (by omega : 0 < n + 1))
          (EReal.natCast_ne_top _),
        EReal.top_div_of_pos_ne_top (by exact_mod_cast (by omega : 0 < n)) (EReal.natCast_ne_top _)]
    | coe x =>
      have hx' : 0 ≤ x := by exact_mod_cast hx
      rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_coe_eq_natCast, ← EReal.coe_div,
        ← EReal.coe_div, EReal.coe_le_coe_iff]
      exact div_le_div_of_nonneg_left hx' (by exact_mod_cast hn) (by push_cast; linarith)
  · rw [EReal.bot_div_of_pos_ne_top (by exact_mod_cast (by omega : 0 < n + 1))
      (EReal.natCast_ne_top _)]
    exact bot_le

/-- **Shift invariance of the growth rate**: for a sequence of naturals with
`u (n + 1) ≤ c · u n`, dropping the first term does not change `expGrowthSup`. -/
@[category API, AMS 26 40, group "carry_splitting"]
theorem expGrowthSup_shift {u : ℕ → ℕ} {c : ℕ} (hc : ∀ n, u (n + 1) ≤ c * u n) :
    expGrowthSup (fun n => (u (n + 1) : ℝ≥0∞)) = expGrowthSup (fun n => (u n : ℝ≥0∞)) := by
  apply le_antisymm
  · exact expGrowthSup_le_of_eventually_le (b := c) (natCast_ne_top c)
      (Eventually.of_forall fun n => by exact_mod_cast hc n)
  · unfold expGrowthSup
    rw [← limsup_nat_add _ 1]
    refine limsup_le_limsup (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hx : 0 ≤ ENNReal.log (u (n + 1) : ℝ≥0∞) ∨ ENNReal.log (u (n + 1) : ℝ≥0∞) = ⊥ := by
      rcases Nat.eq_zero_or_pos (u (n + 1)) with h | h
      · right; simp [h]
      · left; rw [ENNReal.zero_le_log_iff]; exact_mod_cast h
    simpa using ereal_div_succ_le hx hn

/-! ### Sinks and the total path count -/

section count

variable [Fintype A]

variable (X) in
/-- `v` is a **sink**: no arc leaves it. -/
def IsSink (v : V) : Prop := ∀ a w, ¬ X.Adj v a w

@[category API, AMS 05, group "carry_splitting"]
theorem npaths_sink {v : V} (h : X.IsSink v) (n : ℕ) : X.npaths v (n + 1) = 0 := by
  rw [npaths_succ]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun u hu => (h a u hu).elim

variable [Fintype V]

@[category API, AMS 05, group "carry_splitting"]
theorem npaths_succ_le_ntot (v : V) (n : ℕ) :
    X.npaths v (n + 1) ≤ Fintype.card A * Fintype.card V * X.ntot n := by
  rw [npaths_succ]
  calc ∑ a, ∑ u ∈ X.succ v a, X.npaths u n ≤ ∑ _a : A, Fintype.card V * X.ntot n := by
        refine Finset.sum_le_sum fun a _ => ?_
        calc ∑ u ∈ X.succ v a, X.npaths u n ≤ ∑ _u ∈ X.succ v a, X.ntot n :=
              Finset.sum_le_sum fun u _ => npaths_le_ntot u n
          _ = (X.succ v a).card * X.ntot n := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ Fintype.card V * X.ntot n := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]

/-- One more step multiplies the total path count by at most `|V| · |A| · |V|`. -/
@[category API, AMS 05, group "carry_splitting"]
theorem ntot_succ_le (n : ℕ) :
    X.ntot (n + 1) ≤ Fintype.card V * (Fintype.card A * Fintype.card V) * X.ntot n :=
  calc ∑ v, X.npaths v (n + 1) ≤ ∑ _v : V, Fintype.card A * Fintype.card V * X.ntot n :=
        Finset.sum_le_sum fun v _ => npaths_succ_le_ntot v n
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

@[category API, AMS 05, group "carry_splitting"]
theorem ntot_eq_zero_of_le {n m : ℕ} (h : X.ntot n = 0) (hnm : n ≤ m) : X.ntot m = 0 := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    have := ntot_succ_le (X := X) m
    rw [ih, mul_zero] at this
    exact Nat.eq_zero_of_le_zero this

/-- The core is empty iff the total path count vanishes at some length. -/
@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem core_eq_empty_iff_ntot [DecidableEq V] : X.core = ∅ ↔ ∃ n, X.ntot n = 0 := by
  have h := (core_eq_empty_iff (X := X)).out 1 4
  rw [h]
  simp only [ntot, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]

end count

/-! ### Comparing two graphs through their total path counts -/

section compare

variable [Fintype V] [Fintype W] [Fintype A]

/-- Total path counts comparable up to constants from length `1` on give equal entropy. -/
@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem entropy_eq_of_ntot {b c : ℕ} (h₁ : ∀ n, X.ntot (n + 1) ≤ b * Y.ntot (n + 1))
    (h₂ : ∀ n, Y.ntot (n + 1) ≤ c * X.ntot (n + 1)) : X.entropy = Y.entropy := by
  refine le_antisymm (expGrowthSup_le_of_eventually_le (natCast_ne_top b)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)) (expGrowthSup_le_of_eventually_le (natCast_ne_top c)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)) <;>
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  · exact_mod_cast h₁ m
  · exact_mod_cast h₂ m

/-- Total path counts comparable up to constants from length `1` on give the same verdict
`core = ∅`. -/
@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem core_eq_empty_iff_of_ntot [DecidableEq V] [DecidableEq W] {b c : ℕ}
    (h₁ : ∀ n, X.ntot (n + 1) ≤ b * Y.ntot (n + 1))
    (h₂ : ∀ n, Y.ntot (n + 1) ≤ c * X.ntot (n + 1)) : X.core = ∅ ↔ Y.core = ∅ := by
  rw [core_eq_empty_iff_ntot, core_eq_empty_iff_ntot]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.eq_zero_of_le_zero ((h₂ n).trans (by
      rw [ntot_eq_zero_of_le hn (Nat.le_succ n), mul_zero]))⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.eq_zero_of_le_zero ((h₁ n).trans (by
      rw [ntot_eq_zero_of_le hn (Nat.le_succ n), mul_zero]))⟩

end compare

/-! ### Right covers -/

/-- `p : W → V` is a **right cover** of `X` by `Y` on `U ⊆ W`: `U` is closed under successors,
and for `y ∈ U` and every label `a`, `p` maps the `a`-successors of `y` bijectively onto the
`a`-successors of `p y` ([LM95, §8.2], right-resolving factor codes, at the level of graphs). -/
structure RightCover (X : CarryGraph V A) (Y : CarryGraph W A) (p : W → V) (U : Set W) :
    Prop where
  closed : ∀ y ∈ U, ∀ a z, Y.Adj y a z → z ∈ U
  bij : ∀ y ∈ U, ∀ a, Set.BijOn p {z | Y.Adj y a z} {v | X.Adj (p y) a v}

/-- A right cover on all of `W` is a homomorphism `Y → X`. -/
def RightCover.toHom {p : W → V} (h : RightCover X Y p Set.univ) : Hom Y X :=
  ⟨p, fun hz => (h.bij _ trivial _).mapsTo hz⟩

/-- **A right cover preserves path counts** from every vertex of `U`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem npaths_eq_of_rightCover [Fintype A] {p : W → V} {U : Set W} (hc : RightCover X Y p U) :
    ∀ n, ∀ y ∈ U, Y.npaths y n = X.npaths (p y) n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro y hy
    rw [npaths_succ, npaths_succ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hb := hc.bij y hy a
    refine Finset.sum_nbij p (fun z hz => hb.mapsTo hz)
      (fun z₁ hz₁ z₂ hz₂ h => hb.injOn hz₁ hz₂ h) (fun v hv => ?_)
      (fun z hz => ih z (hc.closed y hy a z hz))
    obtain ⟨z, hz, rfl⟩ := hb.surjOn hv
    exact ⟨z, hz, rfl⟩

section cover

variable [Fintype V] [Fintype W] [Fintype A] {p : W → V} {U : Set W}

@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem ntot_le_of_rightCover (hc : RightCover X Y p U)
    (hX : ∀ v, (∃ y ∈ U, p y = v) ∨ X.IsSink v) (n : ℕ) :
    X.ntot (n + 1) ≤ 1 * Y.ntot (n + 1) := by
  classical
  rw [one_mul]
  calc ∑ v, X.npaths v (n + 1)
      ≤ ∑ v, ∑ y ∈ (Finset.univ.filter (· ∈ U)).filter (fun y => p y = v), Y.npaths y (n + 1) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rcases hX v with ⟨y, hy, rfl⟩ | hs
        · rw [← npaths_eq_of_rightCover hc _ y hy]
          exact Finset.single_le_sum (f := fun y => Y.npaths y (n + 1))
            (fun _ _ => Nat.zero_le _) (by simp [hy])
        · rw [npaths_sink hs]
          exact Nat.zero_le _
    _ = ∑ y ∈ Finset.univ.filter (· ∈ U), Y.npaths y (n + 1) :=
        Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ ≤ ∑ y, Y.npaths y (n + 1) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem ntot_rightCover_le (hc : RightCover X Y p U) (hU : ∀ y ∉ U, Y.IsSink y) (n : ℕ) :
    Y.ntot (n + 1) ≤ Fintype.card W * X.ntot (n + 1) :=
  calc ∑ y, Y.npaths y (n + 1) ≤ ∑ _y : W, X.ntot (n + 1) := Finset.sum_le_sum fun y _ => by
        by_cases hy : y ∈ U
        · rw [npaths_eq_of_rightCover hc _ y hy]
          exact npaths_le_ntot _ _
        · rw [npaths_sink (hU y hy)]
          exact Nat.zero_le _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **A right cover preserves entropy** when the vertices off `U` are sinks and every vertex of
`X` is a sink or has a lift in `U`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem entropy_eq_of_rightCover (hc : RightCover X Y p U) (hU : ∀ y ∉ U, Y.IsSink y)
    (hX : ∀ v, (∃ y ∈ U, p y = v) ∨ X.IsSink v) : X.entropy = Y.entropy :=
  entropy_eq_of_ntot (ntot_le_of_rightCover hc hX) (ntot_rightCover_le hc hU)

/-- **A right cover preserves zero entropy** (same hypotheses). -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem lnoBranch_iff_of_rightCover [DecidableEq V] [DecidableEq W] (hc : RightCover X Y p U)
    (hU : ∀ y ∉ U, Y.IsSink y) (hX : ∀ v, (∃ y ∈ U, p y = v) ∨ X.IsSink v) :
    Y.LNoBranch ↔ X.LNoBranch := by
  rw [← entropy_le_zero_iff, ← entropy_le_zero_iff, entropy_eq_of_rightCover hc hU hX]

@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem polyGrowth_iff_of_rightCover [DecidableEq V] [DecidableEq W] (hc : RightCover X Y p U)
    (hU : ∀ y ∉ U, Y.IsSink y) (hX : ∀ v, (∃ y ∈ U, p y = v) ∨ X.IsSink v) :
    Y.PolyGrowth ↔ X.PolyGrowth :=
  ((zeroEntropy_tfae (X := Y)).out 4 2).trans
    ((lnoBranch_iff_of_rightCover hc hU hX).trans ((zeroEntropy_tfae (X := X)).out 2 4))

@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem core_eq_empty_iff_of_rightCover [DecidableEq V] [DecidableEq W]
    (hc : RightCover X Y p U) (hU : ∀ y ∉ U, Y.IsSink y)
    (hX : ∀ v, (∃ y ∈ U, p y = v) ∨ X.IsSink v) : X.core = ∅ ↔ Y.core = ∅ :=
  core_eq_empty_iff_of_ntot (ntot_le_of_rightCover hc hX) (ntot_rightCover_le hc hU)

end cover

/-! ### In-splitting -/

section inSplit

variable [DecidableEq V] [DecidableEq C]

variable (X) in
/-- **The in-splitting** [LM95, Def. 2.4.7] of `X` by the arc classes `π : V → A → V → C`:
the copy `(u, c)` has an arc `(u, c) →a (v, π u a v)` for every arc `u →a v`. -/
def inSplit (π : V → A → V → C) : CarryGraph (V × C) A :=
  ⟨fun x a => (X.succ x.1 a).image fun v => (v, π x.1 a v)⟩

@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem adj_inSplit {π : V → A → V → C} {x y : V × C} {a : A} :
    (X.inSplit π).Adj x a y ↔ X.Adj x.1 a y.1 ∧ y.2 = π x.1 a y.1 := by
  obtain ⟨y₁, y₂⟩ := y
  simp only [inSplit, Adj, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, rfl, rfl⟩
    exact ⟨hv, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨y₁, hv, rfl, rfl⟩

variable (X) in
/-- **In-splitting is a right cover** of the original graph by the first projection. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem inSplit_rightCover (π : V → A → V → C) :
    RightCover X (X.inSplit π) Prod.fst Set.univ where
  closed _ _ _ _ _ := trivial
  bij x _ a := by
    refine ⟨fun y hy => (adj_inSplit.1 hy).1, fun y₁ hy₁ y₂ hy₂ h => ?_,
      fun v hv => ⟨(v, π x.1 a v), adj_inSplit.2 ⟨hv, rfl⟩, rfl⟩⟩
    have e₁ := (adj_inSplit.1 hy₁).2
    have e₂ := (adj_inSplit.1 hy₂).2
    exact Prod.ext h (by rw [e₁, e₂, h])

@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem npaths_inSplit [Fintype A] (π : V → A → V → C) (x : V × C) (n : ℕ) :
    (X.inSplit π).npaths x n = X.npaths x.1 n :=
  npaths_eq_of_rightCover (inSplit_rightCover X π) n x trivial

variable [Fintype V] [Fintype A] [Fintype C] [Nonempty C]

/-- **In-splitting preserves entropy** [LM95, Thm. 4.1.10 with Thm. 2.4.10]. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem entropy_inSplit (π : V → A → V → C) : (X.inSplit π).entropy = X.entropy :=
  (entropy_eq_of_rightCover (inSplit_rightCover X π) (fun _ h => (h trivial).elim)
    fun v => .inl ⟨(v, Classical.arbitrary C), trivial, rfl⟩).symm

/-- **The zero-entropy verdict is invariant under in-splitting** (the vertex count is not). -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem lnoBranch_inSplit_iff (π : V → A → V → C) : (X.inSplit π).LNoBranch ↔ X.LNoBranch :=
  lnoBranch_iff_of_rightCover (inSplit_rightCover X π) (fun _ h => (h trivial).elim)
    fun v => .inl ⟨(v, Classical.arbitrary C), trivial, rfl⟩

@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem core_inSplit (π : V → A → V → C) : (X.inSplit π).core = ∅ ↔ X.core = ∅ :=
  (core_eq_empty_iff_of_rightCover (inSplit_rightCover X π) (fun _ h => (h trivial).elim)
    fun v => .inl ⟨(v, Classical.arbitrary C), trivial, rfl⟩).symm

end inSplit

/-! ### Out-splitting -/

section outSplit

variable [DecidableEq C] [Fintype C]

variable (X) in
/-- **The out-splitting** [LM95, Def. 2.4.3] of `X` by the arc classes `π : V → A → V → C`: the
copy `(u, c)` keeps the arcs `u →a v` of class `π u a v = c`, into every copy of `v`. -/
def outSplit (π : V → A → V → C) : CarryGraph (V × C) A :=
  ⟨fun x a => ((X.succ x.1 a).filter fun v => π x.1 a v = x.2) ×ˢ Finset.univ⟩

@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem adj_outSplit {π : V → A → V → C} {x y : V × C} {a : A} :
    (X.outSplit π).Adj x a y ↔ X.Adj x.1 a y.1 ∧ π x.1 a y.1 = x.2 := by
  simp [outSplit, Adj]

/-- **The copies of `u` together carry `|C|` times the paths of `u`.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem sum_npaths_outSplit [Fintype A] (π : V → A → V → C) :
    ∀ (n : ℕ) (u : V), ∑ c, (X.outSplit π).npaths (u, c) n = Fintype.card C * X.npaths u n := by
  intro n
  induction n with
  | zero => intro u; simp [npaths_zero]
  | succ n ih =>
    intro u
    have step : ∀ c a, ∑ y ∈ (X.outSplit π).succ (u, c) a, (X.outSplit π).npaths y n =
        ∑ v ∈ (X.succ u a).filter (fun v => π u a v = c), Fintype.card C * X.npaths v n := by
      intro c a
      show ∑ y ∈ ((X.succ u a).filter fun v => π u a v = c) ×ˢ Finset.univ, _ = _
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun v _ => ih v
    simp only [npaths_succ]
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => step c a,
      Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_fiberwise (X.succ u a) (π u a) fun v => Fintype.card C * X.npaths v n,
      Finset.mul_sum]

variable [Fintype V] [Fintype A]

@[category API, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem ntot_outSplit (π : V → A → V → C) (n : ℕ) :
    (X.outSplit π).ntot n = Fintype.card C * X.ntot n := by
  simp only [ntot, Fintype.sum_prod_type, sum_npaths_outSplit, Finset.mul_sum]

variable [Nonempty C]

/-- **Out-splitting preserves entropy** [LM95, Thm. 4.1.10 with Thm. 2.4.10]. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem entropy_outSplit (π : V → A → V → C) : (X.outSplit π).entropy = X.entropy :=
  entropy_eq_of_ntot (b := Fintype.card C) (c := 1) (fun n => by rw [ntot_outSplit])
    fun n => by
      rw [ntot_outSplit, one_mul]
      exact Nat.le_mul_of_pos_left _ Fintype.card_pos

/-- **The zero-entropy verdict is invariant under out-splitting.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem lnoBranch_outSplit_iff [DecidableEq V] [DecidableEq A] (π : V → A → V → C) :
    (X.outSplit π).LNoBranch ↔ X.LNoBranch := by
  rw [← entropy_le_zero_iff, ← entropy_le_zero_iff, entropy_outSplit]

@[category textbook, AMS 05 37, ref "LM95", group "carry_splitting"]
theorem core_outSplit [DecidableEq V] (π : V → A → V → C) : (X.outSplit π).core = ∅ ↔ X.core = ∅ :=
  core_eq_empty_iff_of_ntot (b := Fintype.card C) (c := 1) (fun n => by rw [ntot_outSplit])
    fun n => by
      rw [ntot_outSplit, one_mul]
      exact Nat.le_mul_of_pos_left _ Fintype.card_pos

end outSplit

/-! ### The line graph -/

section line

variable [DecidableEq V] [DecidableEq A]

variable (X) in
/-- **The line graph** [BJG09, §4.5] (edge graph [LM95, Def. 2.3.4]): the vertices are the arcs
`(u, a, v)` of `X`, and `(u, a, v) →b (v, b, w)` for every arc `v →b w`.  Triples that are not
arcs are isolated. -/
def lineGraph : CarryGraph (V × A × V) A :=
  ⟨fun t b => if X.Adj t.1 t.2.1 t.2.2 then (X.succ t.2.2 b).image fun w => (t.2.2, b, w) else ∅⟩

@[category API, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem adj_lineGraph {u v v' w : V} {a b b' : A} :
    X.lineGraph.Adj (u, a, v) b (v', b', w) ↔ X.Adj u a v ∧ v' = v ∧ b' = b ∧ X.Adj v b w := by
  by_cases h : X.Adj u a v
  · have e : X.lineGraph.succ (u, a, v) b = (X.succ v b).image fun w => (v, b, w) := by
      simp [lineGraph, h]
    rw [Adj, e, Finset.mem_image]
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨w, hw, rfl, rfl, rfl⟩
      exact ⟨h, rfl, rfl, hw⟩
    · rintro ⟨-, rfl, rfl, hw⟩
      exact ⟨w, hw, rfl, rfl, rfl⟩
  · have e : X.lineGraph.succ (u, a, v) b = ∅ := by
      simp [lineGraph, h]
    rw [Adj, e]
    simp [h]

variable (X) in
/-- **The line graph right-covers `X`** on the arcs, by the target map. -/
@[category textbook, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem lineGraph_rightCover :
    RightCover X X.lineGraph (fun t => t.2.2) {t | X.Adj t.1 t.2.1 t.2.2} where
  closed := by
    rintro ⟨u, a, v⟩ - b ⟨v', b', w⟩ h
    obtain ⟨-, rfl, rfl, hw⟩ := adj_lineGraph.1 h
    exact hw
  bij := by
    rintro ⟨u, a, v⟩ ht b
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨v', b', w⟩ h
      obtain ⟨-, rfl, rfl, hw⟩ := adj_lineGraph.1 h
      exact hw
    · rintro ⟨v₁, b₁, w₁⟩ h₁ ⟨v₂, b₂, w₂⟩ h₂ (e : w₁ = w₂)
      obtain ⟨-, rfl, rfl, -⟩ := adj_lineGraph.1 h₁
      obtain ⟨-, rfl, rfl, -⟩ := adj_lineGraph.1 h₂
      rw [e]
    · intro w hw
      exact ⟨(v, b, w), adj_lineGraph.2 ⟨ht, rfl, rfl, hw⟩, rfl⟩

@[category API, AMS 05 37, ref "BJG09", group "carry_splitting"]
theorem npaths_lineGraph [Fintype A] {t : V × A × V} (ht : X.Adj t.1 t.2.1 t.2.2) (n : ℕ) :
    X.lineGraph.npaths t n = X.npaths t.2.2 n :=
  npaths_eq_of_rightCover (lineGraph_rightCover X) n t ht

@[category API, AMS 05 37, ref "BJG09", group "carry_splitting"]
theorem isSink_lineGraph {t : V × A × V} (ht : ¬ X.Adj t.1 t.2.1 t.2.2) : X.lineGraph.IsSink t := by
  obtain ⟨u, a, v⟩ := t
  rintro b ⟨v', b', w⟩ h
  exact ht (adj_lineGraph.1 h).1

variable [Fintype V] [Fintype A]

/-- **The line graph counts the paths of `X` shifted by one.** -/
@[category textbook, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem ntot_lineGraph (n : ℕ) : X.lineGraph.ntot (n + 1) = X.ntot (n + 2) := by
  classical
  have h : ∀ t : V × A × V, X.lineGraph.npaths t (n + 1) =
      if X.Adj t.1 t.2.1 t.2.2 then X.npaths t.2.2 (n + 1) else 0 := by
    intro t
    split_ifs with ht
    · exact npaths_lineGraph ht _
    · exact npaths_sink (isSink_lineGraph ht) n
  simp only [ntot, h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [npaths_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext x
  exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

/-- **The line graph has the entropy of `X`.** -/
@[category textbook, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem entropy_lineGraph : X.lineGraph.entropy = X.entropy := by
  unfold entropy
  rw [expGrowthSup_congr (v := fun n => (X.ntot (n + 1) : ℝ≥0∞))
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩), expGrowthSup_shift ntot_succ_le]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [ntot_lineGraph]

/-- **The zero-entropy verdict is invariant under passing to the line graph.** -/
@[category textbook, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem lnoBranch_lineGraph_iff : X.lineGraph.LNoBranch ↔ X.LNoBranch := by
  rw [← entropy_le_zero_iff, ← entropy_le_zero_iff, entropy_lineGraph]

@[category textbook, AMS 05 37, ref "BJG09" "LM95", group "carry_splitting"]
theorem core_lineGraph : X.lineGraph.core = ∅ ↔ X.core = ∅ := by
  rw [core_eq_empty_iff_ntot, core_eq_empty_iff_ntot]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 2, by rw [← ntot_lineGraph, ntot_eq_zero_of_le hn (by omega)]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [ntot_lineGraph, ntot_eq_zero_of_le hn (by omega)]⟩

end line

end CarryGraph
