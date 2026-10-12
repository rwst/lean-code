/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.Z32
import Z32.CycleTransversal
import Z32.EscapeBound

/-!
# Bridge: escape bounds, schemas and cycle transversals of `Z32/` as carry-graph facts

Three further `Z32/` results are statements about a finite **functional** carry graph, plus
arithmetic:

* **Escape bounds** (`Z32/EscapeBound.lean`).  The combinatorial budget `A = |blocks|` of
  `Cert.exists_carry_period_le` is the generic fact that a walk in a finite functional graph
  repeats within `|V|` steps (`CarryGraph.Functional.exists_period_of_walk`).
  `Cert.exists_carry_period_le'` and `Cert.exists_escape_le'` re-derive the two theorems from it.
* **The depth-`K` schema** (`Z32/DepthKSchema.lean`).  The rank rotation on the `K + 2` arcs of
  the marked orbit is a functional carry graph, `rotGraph`, with two letters (low and high
  branch).  A confined orbit's ranks are an infinite path of it (`isIPath_ranks`), so the carry
  word is eventually periodic by the generic label form of functional graphs:
  `isEventuallyPeriodic_carry_of_certifiedK'`, `not_confined_of_certifiedK'`.
* **Cycle transversals** (`Z32/CertComplete.lean`, `Z32/CycleTransversal.lean`).  Two confined
  orbits in one block have the same block itinerary and carry word because a path of a
  functional graph is determined by its start (`CarryGraph.Functional.iPath_eq`); the rest is the
  expansion `(p/q)ⁿ`.  `Cert.eq_of_memI_block'`, `Cert.ok_eq_false_of_infinite_hold'` and
  `Cert.ok_eq_false_of_infinite_cycles'` re-derive the chain.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. **251** (2005) 635–648.
* [Dub09AA] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. (2009).
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryBridge

open CarryGraph Z32 Z32.BlockCert ForMathlib.SubwordComplexity

/-! ### The block graph is small -/

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem card_blk_le (c : Cert) : Fintype.card (Blk c) ≤ c.blocks.length := by
  rw [Fintype.card_of_subtype c.blocks.toFinset (fun _ => List.mem_toFinset)]
  exact List.toFinset_card_le _

/-! ### Escape bounds -/

/-- **The combinatorial budget of a block certificate** (`Cert.exists_carry_period_le`),
re-derived: the funnel puts a confined orbit on a walk of the block graph, and a walk of a finite
functional graph repeats within `|V| ≤ |blocks|` steps. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem Cert.exists_carry_period_le' {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    {ξ : ℝ} {N : ℕ} (_hLN : c.blocks.length ≤ N)
    (hmem : ∀ n, n ≤ N + c.levels.length →
      memL c.D c.closed c.U (yFract c.p c.q ξ 0 n)) :
    ∃ t P, 1 ≤ P ∧ t + P ≤ c.blocks.length ∧
      ∀ n, t ≤ n → n + P + 1 ≤ N →
        Z32.carry c.p c.q ξ 0 (n + P) = Z32.carry c.p c.q ξ 0 n := by
  obtain ⟨-, hq1, -, -, -, -⟩ := Cert.parts hc
  have hq0' : 0 < c.q := by omega
  set y : ℕ → ℝ := yFract c.p c.q ξ 0 with hydef
  set w : ℕ → ℤ := Z32.carry c.p c.q ξ 0 with hwdef
  have hy0 : ∀ n, 0 ≤ y n := fun n => yFract_nonneg n
  have hy1 : ∀ n, y n < 1 := fun n => yFract_lt_one n
  have hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ) := by
    intro n
    have h := carry_eq (p := c.p) (q := c.q) (ξ := ξ) (ν := 0) hq0' n
    simp only [mul_zero, sub_zero] at h
    rw [hwdef, hydef]
    linarith
  have hchoice : ∀ n, n ≤ N → ∃ I : Blk c, memI c.D c.closed I.1 (y n) := by
    intro n hn
    obtain ⟨I, hI, hIm⟩ := Cert.memL_blocks_of_le hc hy0 hy1 hrec hmem (n := n) (by omega)
    exact ⟨⟨I, hI⟩, hIm⟩
  obtain ⟨I₀, -⟩ := hchoice 0 (Nat.zero_le _)
  have : Nonempty (Blk c) := ⟨I₀⟩
  choose! Bl hBl using hchoice
  let g : ℕ → Blk c := fun n => if n ≤ N then Bl n else I₀
  have hg : ∀ n, n ≤ N → memI c.D c.closed (g n).1 (y n) := fun n hn => by
    simp only [g, hn, ↓reduceIte]
    exact hBl n hn
  obtain ⟨t, P, hP, htP, hper⟩ := (functional_blkGraph hc hst).exists_period_of_walk (N := N)
    (g := g) (ℓ := w) fun n hn => by
      obtain ⟨hs, -, hh⟩ := mem_outEdges_iff.1 (Cert.mem_outEdges_of_memI hc hy0 hy1 hrec
        (g (n + 1)).2 (hg n (by omega)) (hg (n + 1) hn))
      exact adj_blkGraph.2 ⟨hs, hh⟩
  exact ⟨t, P, hP, htP.trans (card_blk_le c), hper⟩

/-- **`Cert.escape_bound`** (`Cert.exists_escape_le`), re-derived through
`Cert.exists_carry_period_le'`. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "DN05", group "carry_bridge_z32"]
theorem Cert.exists_escape_le' {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    {ξ X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ c.levels.length + escapeSteps c.p c.q c.blocks.length X Lo,
      ¬ memL c.D c.closed c.U (yFract c.p c.q ξ 0 n) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hq1, hqp, hgcd, -, -⟩ := Cert.parts hc
  have hcop : Nat.Coprime c.p c.q := hgcd
  have hLN : c.blocks.length ≤ escapeSteps c.p c.q c.blocks.length X Lo := by
    simp only [escapeSteps]; omega
  obtain ⟨t, P, hP, htP, hper⟩ :=
    Cert.exists_carry_period_le' hc hst (N := escapeSteps c.p c.q c.blocks.length X Lo) hLN
      (fun n hn => hcon n (by omega))
  have habs : |ξ| = ξ := abs_of_pos (lt_of_lt_of_le hLo hLξ)
  exact not_period_of_escapeSteps (ν := 0) hq1 hqp hcop hLo (by rw [habs]; exact hLξ)
    (by rw [habs]; exact hξX) hP htP le_rfl hper

/-! ### The depth-`K` schema as a rotation graph -/

/-- **The rank rotation of the depth-`K` schema**: `K + 2` ranks; from a rank `r ≤ N_L` the low
letter (`false`) leads to `r + N_R + 1`, from a larger rank the high letter (`true`) leads to
`r − N_L`. -/
def rotGraph (NL NR K : ℕ) : CarryGraph (Fin (K + 2)) Bool :=
  ofRel fun r b r' => if (r : ℕ) ≤ NL then b = false ∧ (r' : ℕ) = r + NR + 1
    else b = true ∧ (r' : ℕ) + NL = r

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem adj_rotGraph {NL NR K : ℕ} {r r' : Fin (K + 2)} {b : Bool} :
    (rotGraph NL NR K).Adj r b r' ↔
      ((r : ℕ) ≤ NL ∧ b = false ∧ (r' : ℕ) = r + NR + 1) ∨
        (¬ (r : ℕ) ≤ NL ∧ b = true ∧ (r' : ℕ) + NL = r) := by
  rw [rotGraph, adj_ofRel]
  split_ifs with h <;> simp [h]

/-- The rotation graph is functional. -/
@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem rotGraph_functional (NL NR K : ℕ) : (rotGraph NL NR K).Functional := by
  intro r a b t u ht hu
  have ht' := adj_ofRel.1 ht
  have hu' := adj_ofRel.1 hu
  split_ifs at ht' hu' with h
  · exact ⟨ht'.1.trans hu'.1.symm, Fin.ext (by omega)⟩
  · exact ⟨ht'.1.trans hu'.1.symm, Fin.ext (by omega)⟩

/-- A functional finite carry graph has the label form. -/
@[category API, AMS 05 37, ref "LM95", group "carry_bridge_z32"]
theorem allPer_of_functional {V A : Type*} [Finite V] {X : CarryGraph V A} (h : X.Functional) :
    X.AllPer :=
  allPer_of_lnoBranch (IsLRank.lnoBranch (ρ := fun _ => 0)
    ⟨fun _ _ _ _ => le_rfl, fun s a b t u ht hu _ _ => h s a b t u ht hu⟩)

section Schema

variable {p q K : ℕ} {s ξ : ℝ}

theorem blockRank_le (w : ℕ → ℝ) (K : ℕ) (x : ℝ) : blockRank w K x ≤ K + 1 := by
  simp only [blockRank]
  calc (∑ i ∈ Finset.range (K + 1), if w i ≤ x then (1 : ℕ) else 0)
      ≤ ∑ _i ∈ Finset.range (K + 1), (1 : ℕ) := Finset.sum_le_sum fun i _ => by split <;> simp
    _ = K + 1 := by simp

/-- The rank of time `n`. -/
noncomputable def rankAt (p q K : ℕ) (w : ℕ → ℝ) (ξ s : ℝ) (n : ℕ) : Fin (K + 2) :=
  ⟨blockRank w K ((p : ℝ) * yFract p q ξ (-s) n), Nat.lt_succ_of_le (blockRank_le w K _)⟩

/-- The branch of time `n`: `true` iff the carry is `⌊θ⌋ + 1`. -/
noncomputable def branchAt (p q : ℕ) (ξ s : ℝ) (n : ℕ) : Bool :=
  decide (Z32.carry p q ξ (-s) n ≠ schemaBase p q s)

/-- **One step of a confined orbit is an arc of the rotation graph** (only the window
memberships at `n` and `n + 1` are used). -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem adj_rankAt (hq : 0 < q) (hqp : q < p) {w : ℕ → ℝ}
    (hw : Escape p q (schemaEps p q s) K w) {n : ℕ}
    (hyn : yFract p q ξ (-s) n < 1 / (p : ℝ)) (hyn1 : yFract p q ξ (-s) (n + 1) < 1 / (p : ℝ)) :
    (rotGraph (lowCount p q (schemaEps p q s) w K) (highCount p q (schemaEps p q s) w K) K).Adj
      (rankAt p q K w ξ s n) (branchAt p q ξ s n) (rankAt p q K w ξ s (n + 1)) := by
  set e := schemaEps p q s with he
  have he0 : 0 ≤ e := schemaEps_nonneg p q s
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le hq hqp.le
  set v : ℕ → ℝ := fun n => (p : ℝ) * yFract p q ξ (-s) n with hv
  have hv0 : 0 ≤ v n := mul_nonneg hp0.le (yFract_nonneg (p := p) (q := q) (ξ := ξ) (ν := -s) n)
  have hv1 : v n < 1 := by
    have := mul_lt_mul_of_pos_left hyn hp0
    rwa [mul_one_div, div_self hp0.ne'] at this
  obtain ⟨hb, hr⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp hyn hyn1
  have hstep : ((p : ℝ) * (v n + e) < q) ∨ (1 ≤ v n + e) := by
    rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  have hlow := low_iff_blockRank_le hq hqp hw hstep
  refine adj_rotGraph.2 ?_
  rcases hb with ⟨hL, hc⟩ | ⟨hH, hc⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), sub_zero] at hr
    exact Or.inl ⟨hlow.1 hL, by simp [branchAt, hc],
      blockRank_step_low hq hqp he0 hw hv0 hL hr⟩
  · have hne : Z32.carry p q ξ (-s) n ≠ schemaBase p q s := by rw [hc]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at hr
    exact Or.inr ⟨fun hle => not_low_of_one_le hqp hH (hlow.2 hle), by simp [branchAt, hne],
      blockRank_step_high hq hqp hw hv1 hH hr⟩

/-- **A confined orbit walks the rotation graph**: its ranks form an infinite path labelled by
the branch taken. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem isIPath_ranks (hq : 0 < q) (hqp : q < p) {w : ℕ → ℝ}
    (hw : Escape p q (schemaEps p q s) K w)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) :
    (rotGraph (lowCount p q (schemaEps p q s) w K) (highCount p q (schemaEps p q s) w K) K).IsIPath
      (rankAt p q K w ξ s) (branchAt p q ξ s) :=
  fun n => adj_rankAt hq hqp hw (hy n) (hy (n + 1))

/-- The carry is the base plus the branch bit (where the orbit is confined at `n` and `n + 1`). -/
theorem carry_eq_branch (hq : 0 < q) (hqp : q < p) {n : ℕ}
    (hyn : yFract p q ξ (-s) n < 1 / (p : ℝ)) (hyn1 : yFract p q ξ (-s) (n + 1) < 1 / (p : ℝ)) :
    Z32.carry p q ξ (-s) n = schemaBase p q s + if branchAt p q ξ s n then 1 else 0 := by
  obtain ⟨hb, -⟩ := step_of_confined_at (ξ := ξ) (s := s) hq hqp hyn hyn1
  rcases hb with ⟨-, hc⟩ | ⟨-, hc⟩
  · simp [branchAt, hc]
  · simp [branchAt, hc]

/-- **The depth-`K` schema forces an eventually periodic carry word**
(`isEventuallyPeriodic_carry_of_certifiedK`), re-derived: the ranks walk the functional rotation
graph, whose labels are eventually periodic. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem isEventuallyPeriodic_carry_of_certifiedK' (hq : 0 < q) (hqp : q < p)
    (hy : ∀ n, yFract p q ξ (-s) n < 1 / (p : ℝ)) (hcert : SchemaCertifiedK p q s K) :
    IsEventuallyPeriodic (Z32.carry p q ξ (-s)) := by
  obtain ⟨w, hw⟩ := hcert
  obtain ⟨n₀, L, hL, hper⟩ := allPer_of_functional (rotGraph_functional _ _ K) _ _
    (isIPath_ranks hq hqp hw hy)
  refine ⟨n₀, L, hL, fun k hk => ?_⟩
  rw [carry_eq_branch hq hqp (hy (k + L)) (hy (k + L + 1)),
    carry_eq_branch hq hqp (hy k) (hy (k + 1)), hper k hk]

/-- **The budget `K + 2` of the depth-`K` schema** (`exists_carry_period_of_certifiedK`),
re-derived: a walk of the rotation graph, which has `K + 2` vertices, repeats within `K + 2`
steps. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem exists_carry_period_of_certifiedK' (hq : 0 < q) (hqp : q < p) {N : ℕ}
    (hy : ∀ n, n ≤ N → yFract p q ξ (-s) n < 1 / (p : ℝ))
    (hcert : SchemaCertifiedK p q s K) :
    ∃ t P, 1 ≤ P ∧ t + P ≤ K + 2 ∧
      ∀ n, t ≤ n → n + P + 1 ≤ N → Z32.carry p q ξ (-s) (n + P) = Z32.carry p q ξ (-s) n := by
  obtain ⟨w, hw⟩ := hcert
  obtain ⟨t, P, hP, htP, hper⟩ := (rotGraph_functional _ _ K).exists_period_of_walk (N := N)
    (g := rankAt p q K w ξ s) (ℓ := branchAt p q ξ s)
    fun n hn => adj_rankAt hq hqp hw (hy n (by omega)) (hy (n + 1) hn)
  refine ⟨t, P, hP, by simpa using htP, fun n hn hnN => ?_⟩
  rw [carry_eq_branch hq hqp (hy (n + P) (by omega)) (hy (n + P + 1) hnN),
    carry_eq_branch hq hqp (hy n (by omega)) (hy (n + 1) (by omega)), hper n hn hnN]

/-- **The escape bound for the depth-`K` schema** (`exists_escape_le_of_certifiedK`),
re-derived through `exists_carry_period_of_certifiedK'`. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "DN05", group "carry_bridge_z32"]
theorem exists_escape_le_of_certifiedK' (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hcert : SchemaCertifiedK p q s K)
    {X Lo : ℝ} (hLo : 0 < Lo) (hLξ : Lo ≤ ξ) (hξX : ξ ≤ X) :
    ∃ n ≤ escapeSteps p q (K + 2) X Lo, 1 / (p : ℝ) ≤ yFract p q ξ (-s) n := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, P, hP, htP, hper⟩ :=
    exists_carry_period_of_certifiedK' (p := p) (q := q) (ξ := ξ) (s := s) (K := K)
      (by omega) hqp (N := escapeSteps p q (K + 2) X Lo) hcon hcert
  have habs : |ξ| = ξ := abs_of_pos (lt_of_lt_of_le hLo hLξ)
  exact not_period_of_escapeSteps (ν := -s) hq hqp hcop hLo (by rw [habs]; exact hLξ)
    (by rw [habs]; exact hξX) hP htP le_rfl hper

/-- **The depth-`K` schema theorem, core form** (`not_confined_of_certifiedK`), re-derived. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "DN05", group "carry_bridge_z32"]
theorem not_confined_of_certifiedK' (hq : 1 < q) (hqp : q < p) (hcop : Nat.Coprime p q)
    (hξ : ξ ≠ 0) (hcert : SchemaCertifiedK p q s K) :
    ∃ n : ℕ, 1 / (p : ℝ) ≤ yFract p q ξ (-s) n := by
  by_contra hcon
  push Not at hcon
  exact not_isEventuallyPeriodic_carry hq hqp hcop hξ
    (isEventuallyPeriodic_carry_of_certifiedK' (by omega) hqp hcon hcert)

end Schema

/-! ### Cycle transversals -/

/-- **Distinct confined orbits occupy distinct blocks** (`Cert.eq_of_memI_block`), re-derived:
both orbits walk the functional block graph from the same block, so they read the same carry
word (`Functional.iPath_eq`), and equal carry words separate at the rate `(p/q)ⁿ`. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "Dub08", group "carry_bridge_z32"]
theorem Cert.eq_of_memI_block' {c : Cert} (hc : c.ok = true) (hst : c.strata = [])
    {y y' : ℕ → ℝ} {w w' : ℕ → ℤ}
    (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n < 1) (hmem : ∀ n, memL c.D c.closed c.U (y n))
    (hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ))
    (hy0' : ∀ n, 0 ≤ y' n) (hy1' : ∀ n, y' n < 1) (hmem' : ∀ n, memL c.D c.closed c.U (y' n))
    (hrec' : ∀ n, (c.q : ℝ) * y' (n + 1) = (c.p : ℝ) * y' n - (w' n : ℝ))
    {I : Ivl} (hI : I ∈ c.blocks)
    (h0 : memI c.D c.closed I (y 0)) (h0' : memI c.D c.closed I (y' 0)) : y 0 = y' 0 := by
  obtain ⟨-, hq1, hqp, -, -, -⟩ := Cert.parts hc
  have hq0 : 0 < c.q := by omega
  have hp0 : 0 < c.p := by omega
  -- a block path started at `I`, for any confined orbit through `I`
  have path : ∀ {z : ℕ → ℝ} {u : ℕ → ℤ}, (∀ n, 0 ≤ z n) → (∀ n, z n < 1) →
      (∀ n, memL c.D c.closed c.U (z n)) →
      (∀ n, (c.q : ℝ) * z (n + 1) = (c.p : ℝ) * z n - (u n : ℝ)) →
      memI c.D c.closed I (z 0) →
      ∃ B : ℕ → Blk c, B 0 = ⟨I, hI⟩ ∧ (blkGraph c).IsIPath B u := by
    intro z u hz0 hz1 hzm hzr hz
    have hH : ∀ n, ∃ J : Blk c, memI c.D c.closed J.1 (z n) := fun n => by
      obtain ⟨J, hJ, hJm⟩ := Cert.memL_blocks_of_le hc hz0 hz1 hzr
        (N := n + c.levels.length) (fun m _ => hzm m) le_rfl
      exact ⟨⟨J, hJ⟩, hJm⟩
    choose Bl hBl using hH
    let B : ℕ → Blk c := fun n => if n = 0 then ⟨I, hI⟩ else Bl n
    have hBm : ∀ n, memI c.D c.closed (B n).1 (z n) := fun n => by
      by_cases hn : n = 0
      · subst hn; simpa [B] using hz
      · simpa [B, hn] using hBl n
    refine ⟨B, by simp [B], fun n => ?_⟩
    obtain ⟨hs, -, hh⟩ := mem_outEdges_iff.1 (Cert.mem_outEdges_of_memI hc hz0 hz1 hzr
      (B (n + 1)).2 (hBm n) (hBm (n + 1)))
    exact adj_blkGraph.2 ⟨hs, hh⟩
  obtain ⟨B, hB0, hB⟩ := path hy0 hy1 hmem hrec h0
  obtain ⟨B', hB0', hB'⟩ := path hy0' hy1' hmem' hrec' h0'
  have hww : w = w' := ((functional_blkGraph hc hst).iPath_eq hB hB' (hB0.trans hB0'.symm)).2
  subst hww
  -- equal carry words separate the two orbits at the rate `(p/q)ⁿ`
  have hgap : ∀ n, (c.q : ℝ) ^ n * (y n - y' n) = (c.p : ℝ) ^ n * (y 0 - y' 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 := hrec n
      have e2 := hrec' n
      have : (c.q : ℝ) ^ (n + 1) * (y (n + 1) - y' (n + 1))
          = (c.q : ℝ) ^ n * ((c.q : ℝ) * y (n + 1) - (c.q : ℝ) * y' (n + 1)) := by ring
      rw [this, e1, e2]
      have hpow : (c.p : ℝ) ^ (n + 1) = (c.p : ℝ) * (c.p : ℝ) ^ n := by ring
      rw [hpow]
      linear_combination (c.p : ℝ) * ih
  by_contra hne
  have hd0 : 0 < |y 0 - y' 0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hqR : (0 : ℝ) < c.q := by exact_mod_cast hq0
  have hpR : (0 : ℝ) < c.p := by exact_mod_cast hp0
  have hratio : (c.q : ℝ) / c.p < 1 := by
    rw [div_lt_one hpR]; exact_mod_cast hqp
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd0 hratio
  have h1 : |(c.q : ℝ) ^ n * (y n - y' n)| < (c.q : ℝ) ^ n := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.q : ℝ) ^ n)]
    have : |y n - y' n| < 1 := by
      rw [abs_lt]; constructor <;> [linarith [hy0 n, hy1' n]; linarith [hy0' n, hy1 n]]
    nlinarith [pow_pos hqR n]
  rw [hgap n, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.p : ℝ) ^ n)] at h1
  have h2 : |y 0 - y' 0| < ((c.q : ℝ) / c.p) ^ n := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **An unranked certificate cannot hold infinitely many points**
(`Cert.ok_eq_false_of_infinite_hold`), re-derived through `Cert.eq_of_memI_block'`. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "Dub08", group "carry_bridge_z32"]
theorem Cert.ok_eq_false_of_infinite_hold' {c : Cert} (hst : c.strata = [])
    {z : ℕ → ℝ} (hz : Function.Injective z)
    (hhold : ∀ j, ∃ (y : ℕ → ℝ) (w : ℕ → ℤ), y 0 = z j ∧ (∀ n, 0 ≤ y n) ∧ (∀ n, y n < 1) ∧
      (∀ n, memL c.D c.closed c.U (y n)) ∧
      (∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ))) :
    c.ok = false := by
  rcases Bool.eq_false_or_eq_true c.ok with hc | h
  swap
  · exact h
  exfalso
  choose Y W hY0 hYnn hY1 hYmem hYrec using hhold
  have hblk : ∀ j, ∃ I ∈ c.blocks, memI c.D c.closed I (z j) := by
    intro j
    have := Cert.memL_blocks_of_le hc (hYnn j) (hY1 j) (hYrec j)
      (N := c.levels.length) (fun m _ => hYmem j m) (n := 0) (by omega)
    rw [hY0 j] at this
    exact this
  choose F hFmem hFi using hblk
  have hFinj : Function.Injective F := by
    intro i j hij
    refine hz ?_
    rw [← hY0 i, ← hY0 j]
    refine Cert.eq_of_memI_block' hc hst (hYnn i) (hY1 i) (hYmem i) (hYrec i)
      (hYnn j) (hY1 j) (hYmem j) (hYrec j) (hFmem i) ?_ ?_
    · rw [hY0 i]; exact hFi i
    · rw [hY0 j, hij]; exact hFi j
  exact (Set.infinite_range_of_injective hFinj)
    ((c.blocks.finite_toSet).subset fun x ⟨j, hj⟩ => hj ▸ hFmem j)

/-- **The removed set must be a transversal of the cycles**
(`Cert.ok_eq_false_of_infinite_cycles`), re-derived. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "Dub08", group "carry_bridge_z32"]
theorem Cert.ok_eq_false_of_infinite_cycles' {c : Cert} (hst : c.strata = [])
    {D A : ℕ → ℕ} (hD : ∀ j, 0 < D j) (hcop : ∀ j, Nat.Coprime (D j) (c.p * c.q))
    (hA : ∀ j, A j < D j)
    (hinj : Function.Injective fun j => ((A j : ℝ) / (D j : ℝ)))
    (hmem : ∀ j n, memL c.D c.closed c.U (cycOrbit c.p c.q (D j) (A j) n)) :
    c.ok = false := by
  refine Cert.ok_eq_false_of_infinite_hold' hst (z := fun j => (A j : ℝ) / (D j : ℝ)) hinj ?_
  intro j
  obtain ⟨w, hw⟩ := cycOrbit_rec (hD j) (hcop j) (A j)
  exact ⟨cycOrbit c.p c.q (D j) (A j), w, cycOrbit_zero (hD j) (hA j) c.p c.q,
    fun n => cycOrbit_nonneg _ _ _ _ n, fun n => cycOrbit_lt_one (hD j) _ _ _ n,
    hmem j, hw⟩

end CarryBridge
