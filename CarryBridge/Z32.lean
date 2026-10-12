/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Labelled
import Z32.ModelEntropy

/-!
# Bridge: `Z32/` block certificates as carry graphs

A block certificate `c : Z32.BlockCert.Cert` (base `p/q`, shift `ν = 0`, a set `U ⊆ [0, 1)`, a
funnel of levels ending in the **blocks**, and a rank stratification) is read as the carry graph

`blkGraph c` — vertices the distinct blocks, letters the carries `s ∈ carries p q`, an arc
`I →s J` iff the branch-`s` image of `I` hits `J` (`Z32.BlockCert.hits`).

| `Z32/` | `CarryGraph/` |
|---|---|
| `outEdges … I` | the arcs out of `I` (`mem_outEdges_iff`) |
| `funcOk … strata` | `IsLRank (blkGraph c) (rank strata)` (`isLRank_blkGraph`) |
| `funcOk` with `strata = []` | `Functional (blkGraph c)` (`functional_blkGraph`) |
| `Cert.exists_block_path` | an infinite labelled path of `blkGraph c` (`isIPath_blocks`) |
| the rank/pigeonhole half of `Cert.not_confined` | `IsLRank.evPer` |

`Cert.not_confined'` re-derives the headline soundness theorem of `Z32/BlockCert.lean`: the funnel
(Z32's arithmetic) puts a confined orbit on an infinite path of `blkGraph c`; the generic
rank theorem makes its labels eventually periodic; [DN05] Lemma 2 says the carry word is not.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. **251** (2005) 635–648.
* [Dub09AA] A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math. Nachr. (2009).
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryBridge

open CarryGraph Z32 Z32.BlockCert ForMathlib.SubwordComplexity

variable {c : Cert}

/-- The blocks of a certificate, as a finite vertex type. -/
abbrev Blk (c : Cert) : Type := {J : Ivl // J ∈ c.blocks}

instance blkFintype (c : Cert) : Fintype (Blk c) :=
  Fintype.subtype c.blocks.toFinset fun _ => List.mem_toFinset

/-- **The block graph of a block certificate**: an arc `I →s J` iff `s` is a carry and the
branch-`s` image of `I` hits `J`. -/
def blkGraph (c : Cert) : CarryGraph (Blk c) ℤ :=
  ⟨fun I s => if s ∈ carries c.p c.q then
    Finset.univ.filter fun J => hits c.D c.p c.q c.closed I.1 J.1 s = true else ∅⟩

@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem adj_blkGraph {I J : Blk c} {s : ℤ} :
    (blkGraph c).Adj I s J ↔ s ∈ carries c.p c.q ∧ hits c.D c.p c.q c.closed I.1 J.1 s = true := by
  simp only [blkGraph, Adj]
  split_ifs with h <;> simp [h]

/-- The `(carry, block)` list `outEdges` lists exactly the arcs. -/
@[category API, AMS 11 37 05, group "carry_bridge_z32"]
theorem mem_outEdges_iff {D : ℤ} {p q : ℕ} {cl : Bool} {H : List Ivl} {I J : Ivl} {s : ℤ} :
    (s, J) ∈ outEdges D p q cl H I ↔ s ∈ carries p q ∧ J ∈ H ∧ hits D p q cl I J s = true := by
  simp only [outEdges, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', J', ⟨hJ', hh⟩, rfl, rfl⟩
    exact ⟨hs', hJ', hh⟩
  · rintro ⟨hs, hJ, hh⟩
    exact ⟨s, hs, J, ⟨hJ, hh⟩, rfl, rfl⟩

private theorem eq_of_mem_of_length_le_one' {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l with
  | [] => exact absurd ha (by simp)
  | [_] => rw [List.mem_singleton] at ha hb; rw [ha, hb]

/-- **`funcOk` is a labelled rank**: the rank of the strata never increases along an arc, and at
most one arc keeps it. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem isLRank_blkGraph (hc : c.ok = true) :
    (blkGraph c).IsLRank fun I => rank c.strata I.1 := by
  obtain ⟨-, -, -, -, -, hfunc⟩ := Cert.parts hc
  simp only [funcOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfunc
  refine ⟨fun I s J h => ?_, fun I a b J K hJ hK hJr hKr => ?_⟩
  · obtain ⟨hs, hh⟩ := adj_blkGraph.1 h
    exact (hfunc I.1 I.2).1 (s, J.1) (mem_outEdges_iff.2 ⟨hs, J.2, hh⟩)
  · obtain ⟨ha, hha⟩ := adj_blkGraph.1 hJ
    obtain ⟨hb, hhb⟩ := adj_blkGraph.1 hK
    have m1 : (a, J.1) ∈ (outEdges c.D c.p c.q c.closed c.blocks I.1).filter
        fun e => decide (rank c.strata e.2 = rank c.strata I.1) :=
      List.mem_filter.2 ⟨mem_outEdges_iff.2 ⟨ha, J.2, hha⟩, by simpa using hJr⟩
    have m2 : (b, K.1) ∈ (outEdges c.D c.p c.q c.closed c.blocks I.1).filter
        fun e => decide (rank c.strata e.2 = rank c.strata I.1) :=
      List.mem_filter.2 ⟨mem_outEdges_iff.2 ⟨hb, K.2, hhb⟩, by simpa using hKr⟩
    have := eq_of_mem_of_length_le_one' ((hfunc I.1 I.2).2) m1 m2
    exact ⟨congrArg Prod.fst this, Subtype.ext (congrArg Prod.snd this)⟩

/-- **With `strata = []` the block graph is functional**: at most one arc out of every block. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem functional_blkGraph (hc : c.ok = true) (hs : c.strata = []) : (blkGraph c).Functional :=
  fun I a b J K hJ hK =>
    (isLRank_blkGraph hc).2 I a b J K hJ hK (by rw [hs]; rfl) (by rw [hs]; rfl)

/-- A certified block graph has no labelled branching. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem lnoBranch_blkGraph (hc : c.ok = true) : (blkGraph c).LNoBranch :=
  (isLRank_blkGraph hc).lnoBranch

/-- A certified block graph has the label form. -/
@[category research solved, AMS 11 37 05, ref "Dub09AA" "LM95", group "carry_bridge_z32"]
theorem allPer_blkGraph (hc : c.ok = true) : (blkGraph c).AllPer :=
  allPer_of_lnoBranch (lnoBranch_blkGraph hc)

/-- **The funnel, read as a path**: an orbit confined to `U` forever runs along an infinite
labelled path of the block graph, labelled by its carries. -/
@[category API, AMS 11 37 05, ref "Dub09AA", group "carry_bridge_z32"]
theorem isIPath_blocks (hc : c.ok = true) {y : ℕ → ℝ} {w : ℕ → ℤ}
    (hy0 : ∀ n, 0 ≤ y n) (hy1 : ∀ n, y n < 1) (hmem : ∀ n, memL c.D c.closed c.U (y n))
    (hrec : ∀ n, (c.q : ℝ) * y (n + 1) = (c.p : ℝ) * y n - (w n : ℝ)) :
    ∃ B : ℕ → Blk c, (∀ n, memI c.D c.closed (B n).1 (y n)) ∧ (blkGraph c).IsIPath B w := by
  obtain ⟨Bl, hBmem, hBm, hedge⟩ := Cert.exists_block_path hc hy0 hy1 hmem hrec
  refine ⟨fun n => ⟨Bl n, hBmem n⟩, hBm, fun n => ?_⟩
  obtain ⟨hs, -, hh⟩ := mem_outEdges_iff.1 (hedge n)
  exact adj_blkGraph.2 ⟨hs, hh⟩

/-- **`Z32.BlockCert.Cert.not_confined`, re-derived**: the funnel gives a path of the block graph
(`isIPath_blocks`), the labelled rank makes its labels eventually periodic (`IsLRank.evPer`),
and [DN05] Lemma 2 says the carry word is not. -/
@[category research solved, AMS 11 37, ref "Dub09AA" "DN05", group "carry_bridge_z32"]
theorem Cert.not_confined' {ξ : ℝ} (hc : c.ok = true) (hξ : ξ ≠ 0) :
    ¬ ∀ n, memL c.D c.closed c.U (yFract c.p c.q ξ 0 n) := by
  intro hy
  obtain ⟨-, hq1, hqp, hcop, -, -⟩ := Cert.parts hc
  have hq0' : 0 < c.q := by omega
  have hrec : ∀ n, (c.q : ℝ) * yFract c.p c.q ξ 0 (n + 1)
      = (c.p : ℝ) * yFract c.p c.q ξ 0 n - (carry c.p c.q ξ 0 n : ℝ) := by
    intro n
    have h := carry_eq (p := c.p) (q := c.q) (ξ := ξ) (ν := 0) hq0' n
    simp only [mul_zero, sub_zero] at h
    linarith
  obtain ⟨B, -, hB⟩ := isIPath_blocks hc (fun n => yFract_nonneg n) (fun n => yFract_lt_one n)
    hy hrec
  obtain ⟨n₀, L, hL, hper⟩ := (isLRank_blkGraph hc).evPer hB (Set.toFinite _)
  exact not_isEventuallyPeriodic_carry hq1 hqp hcop hξ ⟨n₀, L, hL, fun m hm => (hper m hm).2⟩

/-- **`Z32.card_modelLang_le_of_cert`, re-derived**: on a functional block graph a model orbit is
an infinite path determined by its first block (`Functional.iPath_eq`), so each length carries at
most one word per block. -/
@[category research solved, AMS 11 37, ref "Dub09AA", group "carry_bridge_z32"]
theorem card_modelLang_le_of_cert' (hc : c.ok = true) (hs : c.strata = []) (n : ℕ) :
    Nat.card (modelLang c.p c.q (certSet c) n) ≤ c.blocks.length := by
  classical
  have hex : ∀ v : modelLang c.p c.q (certSet c) n, ∃ (w : ℕ → ℤ) (B : ℕ → Blk c),
      (∀ i : Fin n, w i = v.1 i) ∧ (blkGraph c).IsIPath B w := by
    rintro ⟨v, y, w, horb, hval⟩
    obtain ⟨B, -, hB⟩ := isIPath_blocks hc (fun m => (horb.2.1 m).1) (fun m => (horb.2.1 m).2)
      horb.1 horb.2.2
    exact ⟨w, B, hval, hB⟩
  choose wf Bf hval hpath using hex
  have hinj : Function.Injective fun v => Bf v 0 := by
    intro v v' h0
    obtain ⟨-, hw⟩ := (functional_blkGraph hc hs).iPath_eq (hpath v) (hpath v') h0
    refine Subtype.ext (funext fun i => ?_)
    rw [← hval v i, ← hval v' i, hw]
  calc Nat.card (modelLang c.p c.q (certSet c) n)
      ≤ Nat.card (Blk c) := Nat.card_le_card_of_injective _ hinj
    _ = c.blocks.toFinset.card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_of_subtype _ fun _ => List.mem_toFinset
    _ ≤ c.blocks.length := c.blocks.toFinset_card_le

/-- **`Z32.not_cert_and_horse`, re-derived by counting alone**: a horseshoe certificate
realises `N^k ≥ 2^k` model words of length `k·L` (`Horse.card_modelLang_ge`, the intermediate
value theorem), while a functional block graph allows at most one per block
(`card_modelLang_le_of_cert'`); no growth rates are needed. -/
@[category research solved, AMS 11 37, ref "Dub09AA", group "carry_bridge_z32"]
theorem not_cert_and_horse' {h : Horse} (hc : c.ok = true) (hs : c.strata = [])
    (hok : h.ok = true) (hp : h.p = c.p) (hq : h.q = c.q) (hU : h.uSet = certSet c) : False := by
  have hN2 : 2 ≤ h.words.length := by
    have hok' := hok
    simp only [Horse.ok, Bool.and_eq_true, decide_eq_true_eq] at hok'
    exact hok'.1.1.1.2
  have h1 := Horse.card_modelLang_ge hok (k := c.blocks.length + 1) (by omega)
  rw [hU, hp, hq] at h1
  have h2 := card_modelLang_le_of_cert' hc hs ((c.blocks.length + 1) * h.len)
  have h3 : c.blocks.length + 1 < 2 ^ (c.blocks.length + 1) := Nat.lt_two_pow_self
  have h4 : 2 ^ (c.blocks.length + 1) ≤ h.words.length ^ (c.blocks.length + 1) :=
    Nat.pow_le_pow_left hN2 _
  omega


end CarryBridge
