/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.Solenoid.LimitMeasures
import CITED.EinsiedlerLindenstrauss
import CITED.LindWard
import Z32.VisitDensity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The bridge: from transverse invariance and entropy to visit density (plan-A1+ L7–L8, W6)

W1–W5 built the unconditional infrastructure: the solenoid `Σ₆`, its Haar measure, the character
dictionary, the limit measures of the orbit of `wind ξ`, and Kolmogorov–Sinai entropy.  Every limit
measure is `T = ×(3/2)`-invariant (`limitMeasures_T32_invariant`) and **nothing else is known about
it**.  This file states exactly what is missing and what it would buy.

## The two open inputs (defs, never axioms — house precedent `RB.EAll`)

* `TransverseRecovery ξ` (**H-inv**) — every limit measure of positive `σ₂`-entropy is
  `σ₂`-invariant.  This is the transverse direction the orbit does not supply; `T` alone is one
  algebraic direction, and `σ₃ = σ₂ ∘ T` (`σ2_T32`), so recovering *either* of `σ₂, σ₃` recovers
  the full `ℤ²`-action.  Formal content of plan-A12 barrier 5(i).
* `EntropyProduction ξ ε` (**H-ent**) — every limit measure carries at least `ε` of
  `σ₂`-entropy.  W5 proves no lower entropy bound for any system, so this is open at every `ε > 0`.

## What they buy (the two-tier conversion)

* `haar_component_of_bridge` — `ε` of entropy gives every limit measure a Haar component of mass
  at least `ε / log 2` (`EL.rigidity_decomposition`, the one cited axiom of this lane).
* `le_lowerDensity_of_bridge` / `M6_of_bridge` — that component converts to a **quantitative** rung:
  every arc of length `t ≤ 1` is visited with lower density at least `(ε / log 2) · (t/2)`, hence
  `Z32.M6 (3/2) ξ`.  A linear conversion of a quantitative open input into a quantitative
  conclusion.  (The factor `1/2` is wrap-around loss, sharp for a single cell — see
  `exists_fract_window`.)
* `M7_of_bridge` — the full `log 2` forces `c = 1`, so every limit measure *is* Haar, the orbit
  equidistributes in `Σ₆`, and `(ξ (3/2)ⁿ)` is u.d. mod 1 (target **T**).
* `M7_iff_bridge` — the terminal conditional: equidistribution is **equivalent** to the two open
  inputs at `ε = log 2`.  The forward direction is what makes the pair non-circular *as a
  factorization*: they are necessary, not merely sufficient.

## The unconditional trichotomy

`trichotomy`: for every limit measure, at least one of
(i) zero `σ₂`-entropy, (ii) failure of `σ₂`-invariance, (iii) a Haar component of mass
`h_ν(σ₂)/log 2`.  No open input is consumed — only the cited axiom.  This is the compiled form of
"the wall is exactly (H-inv, H-ent)": the plan's exhaustiveness claim, machine-checked.

## The measure-to-counting step

`exists_mem_limitMeasures_measure_le` is the only genuinely analytic lemma here: if the empirical
measures give an open set `U` mass `≤ b` along *any* nontrivial filter of times, then **some** limit
measure gives `U` mass `≤ b`.  Compactness of `ProbabilityMeasure Σ₆` supplies a cluster point,
`MapClusterPt.mono` keeps it a limit measure, and portmanteau
(`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) transfers the bound.  Composed with the
window lemma `exists_fract_window` and the level-`(0,0)` cells of W2 — whose Haar mass is the arc
length — it turns "every limit measure charges this cell" into "the orbit visits this arc with
positive lower density".

## Axiom footprint

`EL.rigidity_decomposition` (bridge lane, quarantined to `CITED/EinsiedlerLindenstrauss.lean`) is
used by `haar_component_of_bridge`, `trichotomy`, `M6_of_bridge`, `M7_of_bridge` and both
directions of `M7_iff_bridge`.  `LindWard.kolmogorovSinai_σ2_haar` is used **only** by the forward
direction of `M7_iff_bridge` (and by `entropyProduction_of_equidistributed`), where the value
`h_Haar(σ₂) = log 2` is unavoidable.  Everything else in the file is std3.

## References

Plan A1+ §4 L7–L8 and §7.2 W6; gate-G1 verdict box (§4 L7) for the pinning of the cited statement.
-/

namespace TH.S6

open Filter MeasureTheory Set

open scoped Topology ENNReal NNReal

/-! ### The third invariance is free -/

/-- `σ₂ ∘ T = σ₃`: multiplication by `2` followed by multiplication by `3/2` is multiplication
by `3`.  Hence a `T`-invariant measure that is `σ₂`-invariant is automatically `σ₃`-invariant, and
the whole `ℤ²`-action is recovered from one transverse direction. -/
@[category API, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem σ2_T32 (x : S6) : σ2 (T32 x) = σ3 x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [T32_mk, σ2_mk, σ3_mk, smul_smul]
  norm_num

@[category API, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem measurable_σ2 : Measurable (σ2 : S6 → S6) := measurable_solAut isZ16Unit_two

@[category API, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem measurable_σ3 : Measurable (σ3 : S6 → S6) := measurable_solAut isZ16Unit_three

/-- **`σ₃`-invariance is free.**  A limit measure is `T`-invariant by W4, so `σ₂`-invariance
upgrades it to invariance under the whole `ℤ²`-action generated by `σ₂` and `σ₃`. -/
@[category research solved, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem map_σ3_of_map_σ2 {ξ : ℝ} {ν : ProbabilityMeasure S6} (hν : ν ∈ limitMeasures ξ)
    (h2 : Measure.map σ2 (ν : Measure S6) = (ν : Measure S6)) :
    Measure.map σ3 (ν : Measure S6) = (ν : Measure S6) := by
  have hT : Measure.map T32 (ν : Measure S6) = (ν : Measure S6) := map_T32_of_mem_limitMeasures hν
  have hfun : ((σ2 : S6 → S6) ∘ (T32 : S6 → S6)) = (σ3 : S6 → S6) := funext σ2_T32
  calc Measure.map σ3 (ν : Measure S6)
      = Measure.map ((σ2 : S6 → S6) ∘ (T32 : S6 → S6)) (ν : Measure S6) := by rw [hfun]
    _ = Measure.map σ2 (Measure.map T32 (ν : Measure S6)) :=
        (Measure.map_map measurable_σ2 measurable_T32).symm
    _ = (ν : Measure S6) := by rw [hT, h2]

/-! ### The conclusion of the rigidity axiom, packaged -/

/-- **A Haar splitting of `μ` of weight `c`**: the conclusion of `EL.rigidity_decomposition`.
`μ = c · Haar + (1 - c) · ν₀` with `ν₀` invariant of zero `σ₂`-entropy, and the entropy-mass link
`h_μ(σ₂) = c log 2`. -/
structure HaarSplit (μ : Measure S6) (c : ℝ) (ν₀ : Measure S6) : Prop where
  /-- the complementary part is a probability measure -/
  isProbabilityMeasure : IsProbabilityMeasure ν₀
  /-- the Haar weight is nonnegative -/
  nonneg : 0 ≤ c
  /-- the Haar weight is at most one -/
  le_one : c ≤ 1
  /-- the complementary part is `σ₂`-invariant -/
  map_σ2 : Measure.map σ2 ν₀ = ν₀
  /-- the complementary part is `σ₃`-invariant -/
  map_σ3 : Measure.map σ3 ν₀ = ν₀
  /-- the convex decomposition itself -/
  decomp : μ = ENNReal.ofReal c • haar + ENNReal.ofReal (1 - c) • ν₀
  /-- the complementary part carries no `σ₂`-entropy -/
  entropy_zero : kolmogorovSinai σ2 ν₀ = 0
  /-- **the entropy-mass link**: the Haar weight is `h_μ(σ₂)/log 2` -/
  entropy_mass : kolmogorovSinai σ2 μ = ENNReal.ofReal (c * Real.log 2)

/-- The cited axiom, in packaged form. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03", group "th_solenoid_bridge"]
theorem exists_haarSplit (μ : Measure S6) [IsProbabilityMeasure μ]
    (h2 : Measure.map σ2 μ = μ) (h3 : Measure.map σ3 μ = μ) :
    ∃ (c : ℝ) (ν₀ : Measure S6), HaarSplit μ c ν₀ := by
  obtain ⟨c, ν₀, hprob, hc0, hc1, hm2, hm3, hdec, hz, hmass⟩ :=
    EL.rigidity_decomposition μ h2 h3
  exact ⟨c, ν₀, ⟨hprob, hc0, hc1, hm2, hm3, hdec, hz, hmass⟩⟩

/-- Every set gets at least its Haar share, scaled by the weight. -/
@[category API, AMS 37 28, ref "A1plus", group "th_solenoid_bridge"]
theorem HaarSplit.le_measure {μ : Measure S6} {c : ℝ} {ν₀ : Measure S6} (h : HaarSplit μ c ν₀)
    (A : Set S6) : ENNReal.ofReal c * haar A ≤ μ A := by
  rw [h.decomp, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]
  exact le_self_add

/-- Weight one means the measure *is* Haar. -/
@[category API, AMS 37 28, ref "A1plus", group "th_solenoid_bridge"]
theorem HaarSplit.eq_haar {μ : Measure S6} {ν₀ : Measure S6} (h : HaarSplit μ 1 ν₀) :
    μ = haar := by
  rw [h.decomp]
  simp

/-! ### The two open inputs -/

/-- **H-inv, transverse-invariance recovery** (OPEN).  Every limit measure of the `T`-orbit of
`wind ξ` that carries positive `σ₂`-entropy is `σ₂`-invariant.

This is a `def`, never an axiom: it is the open input, and the point of the file is to display
which theorems rest on it. -/
def TransverseRecovery (ξ : ℝ) : Prop :=
  ∀ ν ∈ limitMeasures ξ, 0 < kolmogorovSinai σ2 (ν : Measure S6) →
    Measure.map σ2 (ν : Measure S6) = (ν : Measure S6)

/-- **H-ent(ε), uniform entropy production** (OPEN).  Every limit measure of the `T`-orbit of
`wind ξ` carries at least `ε` of `σ₂`-entropy. -/
def EntropyProduction (ξ ε : ℝ) : Prop :=
  ∀ ν ∈ limitMeasures ξ, ENNReal.ofReal ε ≤ kolmogorovSinai σ2 (ν : Measure S6)

/-- H-ent is monotone in `ε`, downwards. -/
@[category API, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem EntropyProduction.mono {ξ ε ε' : ℝ} (h : EntropyProduction ξ ε) (hle : ε' ≤ ε) :
    EntropyProduction ξ ε' := fun ν hν => (ENNReal.ofReal_le_ofReal hle).trans (h ν hν)

/-! ### The unconditional trichotomy -/

/-- **The trichotomy** (no open input consumed).  For every limit measure of the orbit of
`wind ξ`, at least one of:

* (i) it carries **no `σ₂`-entropy** — the zero-entropy escape;
* (ii) it fails to be **`σ₂`-invariant** — the bridge gap;
* (iii) it has a **Haar component** of mass `h_ν(σ₂)/log 2`.

This is the formal content of "the wall is exactly (H-inv, H-ent)": ruling out (i) and (ii) is
precisely `EntropyProduction` and `TransverseRecovery`, and nothing else stands in the way. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem trichotomy {ξ : ℝ} {ν : ProbabilityMeasure S6} (hν : ν ∈ limitMeasures ξ) :
    kolmogorovSinai σ2 (ν : Measure S6) = 0 ∨
      Measure.map σ2 (ν : Measure S6) ≠ (ν : Measure S6) ∨
      ∃ (c : ℝ) (ν₀ : Measure S6), HaarSplit (ν : Measure S6) c ν₀ := by
  by_cases hzero : kolmogorovSinai σ2 (ν : Measure S6) = 0
  · exact Or.inl hzero
  by_cases hinv : Measure.map σ2 (ν : Measure S6) = (ν : Measure S6)
  · exact Or.inr (Or.inr (exists_haarSplit _ hinv (map_σ3_of_map_σ2 hν hinv)))
  · exact Or.inr (Or.inl hinv)

/-! ### Tier one: a proportional Haar component -/

/-- **The bridge, quantitative tier.**  Under H-inv and H-ent(ε) with `ε > 0`, every limit measure
has a Haar component whose mass is at least `ε / log 2` — *linear* in the entropy input. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem haar_component_of_bridge {ξ ε : ℝ} (hε : 0 < ε) (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ ε) {ν : ProbabilityMeasure S6} (hν : ν ∈ limitMeasures ξ) :
    ∃ (c : ℝ) (ν₀ : Measure S6), HaarSplit (ν : Measure S6) c ν₀ ∧ ε / Real.log 2 ≤ c := by
  have hpos : 0 < kolmogorovSinai σ2 (ν : Measure S6) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hε) (hent ν hν)
  have h2 : Measure.map σ2 (ν : Measure S6) = (ν : Measure S6) := hinv ν hν hpos
  obtain ⟨c, ν₀, hsplit⟩ := exists_haarSplit (ν : Measure S6) h2 (map_σ3_of_map_σ2 hν h2)
  refine ⟨c, ν₀, hsplit, ?_⟩
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hle : ENNReal.ofReal ε ≤ ENNReal.ofReal (c * Real.log 2) := by
    rw [← hsplit.entropy_mass]
    exact hent ν hν
  have : ε ≤ c * Real.log 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hsplit.nonneg hlog.le)).mp hle
  rwa [div_le_iff₀ hlog]

/-! ### Tier two: equidistribution -/

/-- Under H-inv and H-ent(log 2) every limit measure **is** Haar: the weight is forced to `1`. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem eq_haar_of_bridge {ξ : ℝ} (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ (Real.log 2)) {ν : ProbabilityMeasure S6}
    (hν : ν ∈ limitMeasures ξ) : (ν : Measure S6) = haar := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨c, ν₀, hsplit, hc⟩ := haar_component_of_bridge hlog hinv hent hν
  rw [div_self hlog.ne'] at hc
  have : c = 1 := le_antisymm hsplit.le_one hc
  subst this
  exact hsplit.eq_haar

/-- Under the bridge the limit set collapses to `{Haar}`. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem limitMeasures_eq_of_bridge {ξ : ℝ} (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ (Real.log 2)) : limitMeasures ξ = {haarProb} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  obtain ⟨ν, hν⟩ := limitMeasures_nonempty ξ
  have hhaar : ν = haarProb :=
    ProbabilityMeasure.toMeasure_injective (by rw [eq_haar_of_bridge hinv hent hν,
      haarProb_toMeasure])
  refine ⟨hhaar ▸ hν, fun μ hμ => ?_⟩
  exact ProbabilityMeasure.toMeasure_injective
    (by rw [eq_haar_of_bridge hinv hent hμ, haarProb_toMeasure])

/-- **The bridge implies equidistribution in `Σ₆`** — the whole master family at once. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem equidistributed_of_bridge {ξ : ℝ} (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ (Real.log 2)) : Equidistributed ξ :=
  (equidistributed_iff_limitMeasures ξ).mpr (limitMeasures_eq_of_bridge hinv hent)

/-- **M7 from the bridge**: the target statement **T**, u.d. mod 1 of `(ξ (3/2)ⁿ)`. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem M7_of_bridge {ξ : ℝ} (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ (Real.log 2)) :
    Bertin.UniformlyDistributedModOne (fun n => ξ * (3 / 2) ^ n) :=
  ud_of_limitMeasures_eq (limitMeasures_eq_of_bridge hinv hent)

/-! ### The converse: the open inputs are necessary -/

/-- If the orbit equidistributes then H-inv holds — trivially, because Haar is `σ₂`-invariant. -/
@[category research solved, AMS 37 28 11, ref "A1plus", group "th_solenoid_bridge"]
theorem transverseRecovery_of_equidistributed {ξ : ℝ} (h : Equidistributed ξ) :
    TransverseRecovery ξ := by
  intro ν hν _
  have : ν = haarProb := by
    rw [(equidistributed_iff_limitMeasures ξ).mp h] at hν
    exact hν
  rw [this, haarProb_toMeasure]
  exact map_σ2_haar

/-- If the orbit equidistributes then H-ent(log 2) holds.  **This is the one place the value
`h_Haar(σ₂) = log 2` is needed** ([LW88], `CITED/LindWard.lean`); everything else in the file uses
only the rigidity axiom. -/
@[category research solved, AMS 37 28 11, ref "LW88" "A1plus", group "th_solenoid_bridge"]
theorem entropyProduction_of_equidistributed {ξ : ℝ} (h : Equidistributed ξ) :
    EntropyProduction ξ (Real.log 2) := by
  intro ν hν
  have : ν = haarProb := by
    rw [(equidistributed_iff_limitMeasures ξ).mp h] at hν
    exact hν
  rw [this, haarProb_toMeasure]
  exact LindWard.le_kolmogorovSinai_σ2_haar

/-- **The terminal conditional (L15).**  Equidistribution of the `T`-orbit of `wind ξ` is
*equivalent* to the conjunction of the two open inputs at `ε = log 2`.  The forward direction says
the pair is **necessary**, so the factorization is not a repackaging of the conclusion: any proof
of equidistribution must in particular establish both. -/
@[category research solved, AMS 37 28 11, ref "Rud90" "EL03" "LW88" "A1plus",
  group "th_solenoid_bridge"]
theorem M7_iff_bridge (ξ : ℝ) :
    Equidistributed ξ ↔ TransverseRecovery ξ ∧ EntropyProduction ξ (Real.log 2) :=
  ⟨fun h => ⟨transverseRecovery_of_equidistributed h, entropyProduction_of_equidistributed h⟩,
    fun h => equidistributed_of_bridge h.1 h.2⟩

/-! ### From measures back to counting -/

/-- **The cluster-point transfer.**  If the empirical measures give the open set `U` mass at most
`b` along *any* nontrivial filter of times, then some limit measure gives `U` mass at most `b`.

Compactness of `ProbabilityMeasure Σ₆` (Prokhorov, W4) supplies a cluster point of the empirical
measures along that filter; `MapClusterPt.mono` keeps it a limit measure of the full sequence; and
portmanteau transfers the bound, `U` being open. -/
@[category research solved, AMS 37 28 60, ref "A1plus", group "th_solenoid_bridge"]
theorem exists_mem_limitMeasures_measure_le {ξ : ℝ} {F : Filter ℕ} [F.NeBot] (hF : F ≤ atTop)
    {U : Set S6} (hU : IsOpen U) {b : ℝ≥0∞}
    (hb : ∀ᶠ N in F, (empirical ξ N : Measure S6) U ≤ b) :
    ∃ ν ∈ limitMeasures ξ, (ν : Measure S6) U ≤ b := by
  obtain ⟨ν, hclust⟩ := exists_clusterPt_of_compactSpace (Filter.map (empirical ξ) F)
  have hmap : MapClusterPt ν F (empirical ξ) := hclust
  refine ⟨ν, hmap.mono hF, ?_⟩
  haveI hne : (𝓝 ν ⊓ Filter.map (empirical ξ) F).NeBot := hclust
  have htend : Tendsto (id : ProbabilityMeasure S6 → ProbabilityMeasure S6)
      (𝓝 ν ⊓ Filter.map (empirical ξ) F) (𝓝 ν) := tendsto_id.mono_left inf_le_left
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto htend hU).trans ?_
  exact liminf_le_of_frequently_le' (Filter.Eventually.frequently
    (Filter.Eventually.filter_mono inf_le_right (Filter.eventually_map.mpr hb)))

/-! ### The window lemma and the level-`(0,0)` cells -/

/-- **The window lemma.**  For a base point `s` and an arc length `t ∈ (0, 1]` there is an interval
`(a, b) ⊆ [0, 1]` of length **at least `t/2`** such that every real whose *fractional part* lies in
`(a, b)` lies in the arc `[s, s + t)` in the sense of `Z32.inArc`.

`Z32.inArc` measures `⟨x - s⟩` while a level-`(0,0)` cell constrains `⟨x⟩`, so the window has to be
placed relative to `⟨s⟩`.  Three cases: the arc does not wrap (window of the full length `t`), or it
wraps and the longer of its two pieces — `(⟨s⟩, 1)` and `(0, ⟨s⟩ + t - 1)`, of total length `t` — is
taken.  **The factor `1/2` is sharp for a single cell**: a wrapped arc is two fract-intervals, and
at `⟨s⟩ = 1 - t/2` both pieces have length exactly `t/2`. -/
@[category API, AMS 11 37, ref "A1plus", group "th_solenoid_bridge"]
theorem exists_fract_window (s : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ t / 2 ≤ b - a ∧ b ≤ 1 ∧
      ∀ η : ℝ, Int.fract η ∈ Set.Ioo a b → Z32.inArc s t η := by
  have hs0 : 0 ≤ Int.fract s := Int.fract_nonneg s
  have hs1 : Int.fract s < 1 := Int.fract_lt_one s
  have key : ∀ η : ℝ, Int.fract (η - s) = Int.fract (Int.fract η - Int.fract s) := by
    intro η
    have hrw : η - s = (Int.fract η - Int.fract s) + (((⌊η⌋ - ⌊s⌋ : ℤ) : ℝ)) := by
      simp only [Int.fract]
      push_cast
      ring
    rw [hrw, Int.fract_add_intCast]
  by_cases hcase : Int.fract s + t ≤ 1
  · refine ⟨Int.fract s, Int.fract s + t, hs0, by linarith, hcase, ?_⟩
    rintro η ⟨h1, h2⟩
    have hmem : Int.fract η - Int.fract s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    show Int.fract (η - s) < t
    rw [key, Int.fract_eq_self.mpr hmem]
    linarith
  · have hcase' : 1 < Int.fract s + t := lt_of_not_ge hcase
    by_cases hbig : t / 2 ≤ 1 - Int.fract s
    · refine ⟨Int.fract s, 1, hs0, by linarith, le_rfl, ?_⟩
      rintro η ⟨h1, h2⟩
      have hmem : Int.fract η - Int.fract s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      show Int.fract (η - s) < t
      rw [key, Int.fract_eq_self.mpr hmem]
      linarith
    · have hbig' : 1 - Int.fract s < t / 2 := lt_of_not_ge hbig
      refine ⟨0, Int.fract s + t - 1, le_rfl, by linarith, by linarith, ?_⟩
      rintro η ⟨h1, h2⟩
      have hmem : Int.fract η - Int.fract s + 1 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      show Int.fract (η - s) < t
      rw [key, show Int.fract η - Int.fract s
            = (Int.fract η - Int.fract s + 1) + (((-1 : ℤ) : ℝ)) by push_cast; ring,
        Int.fract_add_intCast, Int.fract_eq_self.mpr hmem]
      linarith

/-- Level-`(0,0)` cells are open. -/
@[category API, AMS 37 11, ref "A1plus", group "th_solenoid_bridge"]
theorem isOpen_cell (a b : ℝ) (k : ℕ) (c : ℚ_[2]) (j : ℕ) (d : ℚ_[3]) :
    IsOpen (cell a b k c j d) :=
  QuotientAddGroup.isOpenMap_coe _
    (isOpen_Ioo.prod ((Padic.isOpen_residueBall k c).prod (Padic.isOpen_residueBall j d)))

/-- At level `(0, 0)` the cell over `(a, b)` is exactly the fractional-part window: no residue
condition survives. -/
@[category API, AMS 11 37, ref "A1plus", group "th_solenoid_bridge"]
theorem wind_mem_cell_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (η : ℝ) :
    wind η ∈ cell a b 0 0 0 0 ↔ Int.fract η ∈ Set.Ioo a b := by
  have h := level_bridge ha hb 0 0 0 0 η
  simpa using h

/-- The Haar mass of a level-`(0,0)` cell is the length of its interval (W2's `haar_cell`). -/
@[category API, AMS 37 28, ref "A1plus", group "th_solenoid_bridge"]
theorem haar_cell_zero {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    haar (cell a b 0 0 0 0) = ENNReal.ofReal (b - a) := by
  rw [haar_cell ha hb 0 (by simp) 0 (by simp)]
  simp

/-- **The counting step.**  The empirical measure of a level-`(0,0)` cell whose window sits inside
the arc `[s, s + t)` is at most the visit ratio of that arc. -/
@[category research solved, AMS 11 37 28, ref "A1plus", group "th_solenoid_bridge"]
theorem empirical_cell_le_visitRatio {ξ s t a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hwin : ∀ η : ℝ, Int.fract η ∈ Set.Ioo a b → Z32.inArc s t η) (N : ℕ) :
    (empirical ξ N : Measure S6) (cell a b 0 0 0 0)
      ≤ ENNReal.ofReal (Z32.visitRatio (3 / 2) ξ s t (N + 1)) := by
  classical
  have hsub : (Finset.range (N + 1)).filter
      (fun n => T32^[n] (wind ξ) ∈ cell a b 0 0 0 0) ⊆ Z32.visits (3 / 2) ξ s t (N + 1) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Z32.mem_visits]
    refine ⟨hn.1, hwin _ ?_⟩
    have hmem := hn.2
    rw [T32_iter_wind] at hmem
    exact (wind_mem_cell_iff ha hb _).mp hmem
  have hcard : ((Finset.range (N + 1)).filter
      (fun n => T32^[n] (wind ξ) ∈ cell a b 0 0 0 0)).card
      ≤ Z32.visitCount (3 / 2) ξ s t (N + 1) := Finset.card_le_card hsub
  have hsum : (empirical ξ N : Measure S6) (cell a b 0 0 0 0)
      = ((N : ℝ≥0∞) + 1)⁻¹ * (((Finset.range (N + 1)).filter
        (fun n => T32^[n] (wind ξ) ∈ cell a b 0 0 0 0)).card : ℝ≥0∞) := by
    rw [empirical_toMeasure, empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      smul_eq_mul]
    congr 1
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Measure.dirac_apply, Set.indicator_apply]
    simp
  have hstep : (empirical ξ N : Measure S6) (cell a b 0 0 0 0)
      ≤ ((N : ℝ≥0∞) + 1)⁻¹ * ((Z32.visitCount (3 / 2) ξ s t (N + 1) : ℕ) : ℝ≥0∞) := by
    rw [hsum]
    gcongr
  refine hstep.trans (le_of_eq ?_)
  rw [Z32.visitRatio, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
  push_cast
  rw [ENNReal.div_eq_inv_mul]

/-! ### Tier one, concluded: positive visit density -/

/-- **The quantitative rung.**  Under H-inv and H-ent(ε), every arc of length `t ∈ (0, 1]` is
visited with lower density at least `(ε / log 2) · (t / 2)` — *linear* in the entropy input.

Proof shape: the Haar component of mass `ε / log 2` (tier one) gives every limit measure at least
that share of the window cell, whose Haar mass is the window length; if the visit ratio dipped below
the bound along any sequence of times, `exists_mem_limitMeasures_measure_le` would manufacture a
limit measure starving that cell.

The factor `1/2` comes from the wrap-around of the arc, and is sharp for a single cell
(`exists_fract_window`); recovering the full `|I|` would need a two-cell covering. -/
@[category research solved, AMS 11 37 28, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem le_lowerDensity_of_bridge {ξ ε : ℝ} (hε : 0 < ε) (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ ε) (s : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ε / Real.log 2 * (t / 2) ≤ Z32.lowerDensity (3 / 2) ξ s t := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 < ε / Real.log 2 := div_pos hε hlog
  obtain ⟨a, b, ha, hlen, hb, hwin⟩ := exists_fract_window s ht ht1
  set m : ℝ := ε / Real.log 2 * (b - a) with hm
  have hm0 : 0 < m := mul_pos hc0 (by linarith)
  -- every limit measure charges the window cell by at least `m`
  have hlow : ∀ ν ∈ limitMeasures ξ,
      ENNReal.ofReal m ≤ (ν : Measure S6) (cell a b 0 0 0 0) := by
    intro ν hν
    obtain ⟨c, ν₀, hsplit, hc⟩ := haar_component_of_bridge hε hinv hent hν
    refine le_trans ?_ (hsplit.le_measure _)
    rw [haar_cell_zero ha hb, ← ENNReal.ofReal_mul (le_trans hc0.le hc)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  -- if the density dipped below `m`, some limit measure would starve the cell
  have hmain : m ≤ Z32.lowerDensity (3 / 2) ξ s t := by
    by_contra hcon
    obtain ⟨m', hm'1, hm'2⟩ := exists_between (lt_of_not_ge hcon)
    have hm'0 : 0 ≤ m' := le_trans (Z32.lowerDensity_nonneg _ _ _ _) hm'1.le
    have hfreq : ∃ᶠ N in atTop, Z32.visitRatio (3 / 2) ξ s t N < m' :=
      Filter.frequently_lt_of_liminf_lt (Z32.isCoboundedUnder_ge_visitRatio _ _ _ _) hm'1
    have hfreq' : ∃ᶠ N in atTop, Z32.visitRatio (3 / 2) ξ s t (N + 1) < m' := by
      rw [Filter.frequently_atTop] at hfreq ⊢
      intro n
      obtain ⟨k, hk, hkp⟩ := hfreq (n + 1)
      exact ⟨k - 1, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩
    set F : Filter ℕ := atTop ⊓ 𝓟 {N | Z32.visitRatio (3 / 2) ξ s t (N + 1) < m'} with hF
    haveI : F.NeBot := Filter.frequently_iff_neBot.mp hfreq'
    have hbnd : ∀ᶠ N in F, (empirical ξ N : Measure S6) (cell a b 0 0 0 0)
        ≤ ENNReal.ofReal m' := by
      filter_upwards [Filter.eventually_inf_principal.mpr (Eventually.of_forall fun N h => h)] with
        N hN
      exact (empirical_cell_le_visitRatio ha hb hwin N).trans (ENNReal.ofReal_le_ofReal hN.le)
    obtain ⟨ν, hν, hνle⟩ :=
      exists_mem_limitMeasures_measure_le (ξ := ξ) inf_le_left (isOpen_cell a b 0 0 0 0) hbnd
    have hcontra := (hlow ν hν).trans hνle
    rw [ENNReal.ofReal_le_ofReal_iff hm'0] at hcontra
    linarith
  refine le_trans ?_ hmain
  rw [hm]
  exact mul_le_mul_of_nonneg_left hlen hc0.le

/-- **M6 from the bridge.**  Under H-inv and H-ent(ε) with `ε > 0` the orbit `(ξ (3/2)ⁿ)` visits
every arc with positive lower density: milestone `Z32.M6` at base `3/2`, the quantitative rung of
plan-A6+ reached from a quantitative open input. -/
@[category research solved, AMS 11 37 28, ref "Rud90" "EL03" "A1plus", group "th_solenoid_bridge"]
theorem M6_of_bridge {ξ ε : ℝ} (hε : 0 < ε) (hinv : TransverseRecovery ξ)
    (hent : EntropyProduction ξ ε) : Z32.M6 (3 / 2) ξ := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ s t' : ℝ, 0 < t' → t' ≤ 1 → Z32.V4 (3 / 2) ξ s t' := fun s t' ht' ht1' =>
    lt_of_lt_of_le (mul_pos (div_pos hε hlog) (by linarith))
      (le_lowerDensity_of_bridge hε hinv hent s ht' ht1')
  intro s t ht
  by_cases h1 : t ≤ 1
  · exact key s t ht h1
  · exact lt_of_lt_of_le (key s 1 one_pos le_rfl) (Z32.lowerDensity_mono_arc (not_le.mp h1).le)

end TH.S6
