/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Splitting
import Mathlib.Tactic.IntervalCases
import DubC.Verdict

/-!
# Bridge: `DubC/` as a carry graph

The base-`a` coprimality subshift modulo `M` of `DubC/` is the **digit graph**
`CarryBridge.digitGraph a M`: vertices `ZMod M`, labels the digits `d < a`, and an arc
`r →[d] a·r + d` between units.  Its underlying digraph is `DubC.Step a M`
(`under_digitGraph`).  Through this dictionary every `DubC` certificate is a witness for a
`CarryGraph` property, and the `DubC` soundness theorems follow from the generic ones:

| `DubC/` | `CarryGraph/` |
|---|---|
| `CertOK a M ρ` | `IsRank (digitGraph a M) ρ` (`certOK_iff_isRank`), also `IsLRank` for `a ≤ M` |
| `C(𝒫)` (prose) | `NoBranch (digitGraph a M)` (`certOK_iff_noBranch`, completeness) |
| `eventually_periodic_of_rank` | `IsRank.evPer` |
| `CoreClosed a M K` | every cyclic vertex lies in `K` (`coreClosed_iff`) |
| `transGen_self_of_rank`, `coreClosed_of_rankOn` | `cyc_mem_of_peelRank` |
| `onCycle_proj`, the ladder rung | `Hom.cyc_map` along `projHom`, then `cyc_mem_of_peelRank` |
| the engine's two-stage peel | `core (digitGraph a M)`, computable (`coreClosed_core`) |
| zero entropy | `certOK_iff_polyGrowth`, `certOK_iff_allEvPer`, `certOK_iff_entropy` |
| full vs reduced model (X-SPLIT) | `digitGraph_rightCover`, `certOK_full_iff_reduced'` |

Re-derived (primed names, same statements): `digits_eventually_periodic_of_certOK'`,
`infinite_composites_floorPow_of_certOK'`, `coreClosed_of_rankOn'`,
`coreClosed_of_rankRevOn'`, `coreClosed_of_ladder'`.  The core form `CoreClosed` + `CoreDet`
implies `C(𝒫)` (`noBranch_of_coreCert`), so by completeness a rank certificate exists whenever a
core certificate does (`exists_certOK_of_coreCert`).  Through `zeroEntropy_tfae` a certificate
exists iff residue walks grow polynomially, iff every admissible residue walk is eventually
periodic, iff the coprimality subshift has entropy `≤ 0` (and, for `a ≤ M`, the same for the
labelled digit sequences).

## References

* [Dub09] A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs*, 2nd ed., 2009.
-/

namespace CarryBridge

open CarryGraph DubC

variable {a M : ℕ}

/-- **The digit graph** of base `a` modulo `M`: `r →[d] a·r + d` between units. -/
def digitGraph (a M : ℕ) [NeZero M] : CarryGraph (ZMod M) (Fin a) :=
  CarryGraph.ofRel fun r d t => Cop M r ∧ Cop M t ∧ t = (a : ZMod M) * r + ((d : ℕ) : ZMod M)

@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem adj_digitGraph [NeZero M] {r t : ZMod M} {d : Fin a} :
    (digitGraph a M).Adj r d t ↔ Cop M r ∧ Cop M t ∧ t = (a : ZMod M) * r + ((d : ℕ) : ZMod M) :=
  adj_ofRel

/-- The underlying digraph of the digit graph is `DubC.Step`. -/
@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem under_digitGraph [NeZero M] {r t : ZMod M} : (digitGraph a M).under r t ↔ Step a M r t := by
  simp only [under, adj_digitGraph, Step]
  constructor
  · rintro ⟨d, hr, ht, rfl⟩
    exact ⟨hr, ht, d, d.2, rfl⟩
  · rintro ⟨hr, ht, d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, hr, ht, rfl⟩

@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem under_digitGraph_eq [NeZero M] : (digitGraph a M).under = Step a M := by
  funext r t
  exact propext under_digitGraph

@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem cyc_digitGraph [NeZero M] {r : ZMod M} :
    (digitGraph a M).Cyc r ↔ Relation.TransGen (Step a M) r r := by
  rw [Cyc, under_digitGraph_eq]

/-- `DubC.CoreClosed` says that every cyclic vertex of the digit graph lies in `K`. -/
@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem coreClosed_iff [NeZero M] {K : ZMod M → Prop} :
    CoreClosed a M K ↔ ∀ r, (digitGraph a M).Cyc r → K r := by
  simp only [CoreClosed, cyc_digitGraph]

/-! ### The rank certificate -/

/-- **`DubC.CertOK` is `IsRank` on the digit graph.** -/
@[category API, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_isRank [NeZero M] {ρ : ZMod M → ℕ} :
    CertOK a M ρ ↔ (digitGraph a M).IsRank ρ := by
  simp only [IsRank, under_digitGraph_eq]
  refine ⟨fun h => ⟨rank_le_of_certOK h, unique_of_certOK h⟩, fun h => ?_⟩
  intro r hr d₁ hd₁ d₂ hd₂
  exact ⟨fun ht => h.1 _ _ ⟨hr, ht, d₁, hd₁, rfl⟩, fun ht hu h1 h2 =>
    h.2 _ _ _ ⟨hr, ht, d₁, hd₁, rfl⟩ ⟨hr, hu, d₂, hd₂, rfl⟩ h1 h2⟩

/-- Digits below `M` are recovered from the target residue. -/
@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem digit_eq_of_target [NeZero M] (haM : a ≤ M) {r : ZMod M} {d₁ d₂ : Fin a}
    (h : (a : ZMod M) * r + ((d₁ : ℕ) : ZMod M) = (a : ZMod M) * r + ((d₂ : ℕ) : ZMod M)) :
    d₁ = d₂ := by
  have h' : ((d₁ : ℕ) : ZMod M) = ((d₂ : ℕ) : ZMod M) := add_left_cancel h
  have := congrArg ZMod.val h'
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext this

/-- For `a ≤ M` the certificate is even a **labelled** rank: digits are pinned down by residues.
-/
@[category API, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_isLRank [NeZero M] (haM : a ≤ M) {ρ : ZMod M → ℕ} :
    CertOK a M ρ ↔ (digitGraph a M).IsLRank ρ := by
  rw [certOK_iff_isRank]
  refine ⟨fun h => ⟨fun s d t hst => h.1 s t ⟨d, hst⟩, fun s d₁ d₂ t u ht hu h1 h2 => ?_⟩,
    IsLRank.isRank⟩
  have htu := h.2 s t u ⟨d₁, ht⟩ ⟨d₂, hu⟩ h1 h2
  subst htu
  obtain ⟨-, -, e1⟩ := adj_digitGraph.1 ht
  obtain ⟨-, -, e2⟩ := adj_digitGraph.1 hu
  exact ⟨digit_eq_of_target haM (e1.symm.trans e2), rfl⟩

/-- **Completeness of the rank form of `C(𝒫)`** (from `CarryGraph.exists_isRank_iff_noBranch`). -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95" "BJG09", group "carry_bridge_dubc"]
theorem certOK_iff_noBranch [NeZero M] : (∃ ρ, CertOK a M ρ) ↔ (digitGraph a M).NoBranch := by
  simp_rw [certOK_iff_isRank]
  exact exists_isRank_iff_noBranch

/-! ### Re-derived soundness -/

/-- `DubC.digits_eventually_periodic_of_certOK`, re-derived from `CarryGraph.IsRank.evPer`. -/
@[category research solved, AMS 11 37, ref "Dub09", group "carry_bridge_dubc"]
theorem digits_eventually_periodic_of_certOK' (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank)
    {ξ : ℝ} {N : ℕ} (hunit : ∀ n, N ≤ n → Cop M ((floorPow ξ a n : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m := by
  obtain ⟨j₀, L, hL, hjper⟩ := (certOK_iff_isRank.1 hcert).evPer
    (s := fun j => ((floorPow ξ a (N + j) : ZMod M)))
    (fun j => under_digitGraph.2 (step_floorPow (by omega) hunit j)) (Set.toFinite _)
  refine ⟨N + j₀, L, hL, digits_periodic_of_residues_periodic ha haM ?_⟩
  intro p hp
  have h1 := hjper (p - N) (by omega)
  rw [show N + (p - N + L) = p + L by omega, show N + (p - N) = p by omega] at h1
  exact h1

/-- **One finite certificate settles the base** (`DubC.infinite_composites_floorPow_of_certOK`,
re-derived). -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "carry_bridge_dubc"]
theorem infinite_composites_floorPow_of_certOK' (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank) {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite :=
  infinite_composites_floorPow_of_digits ha hξ fun _ hunit =>
    digits_eventually_periodic_of_certOK' ha haM rank hcert hunit

/-! ### Peel ranks and the ladder -/

/-- `DubC.coreClosed_of_rankOn`, re-derived from `CarryGraph.cyc_mem_of_peelRank`. -/
@[category research solved, AMS 11 37, ref "Dub09", group "carry_bridge_dubc"]
theorem coreClosed_of_rankOn' [NeZero M] (C K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hcyc : ∀ r, Relation.TransGen (Step a M) r r → C r)
    (hle : ∀ r t, C r → C t → Step a M r t → ρ t ≤ ρ r)
    (hlt : ∀ r t, C r → C t → Step a M r t → ¬ K r → ρ t < ρ r) :
    CoreClosed a M K :=
  coreClosed_iff.2 fun _ hr => cyc_mem_of_peelRank (X := digitGraph a M) C K ρ
    (fun v hv => hcyc v (cyc_digitGraph.1 hv))
    (fun v t hv ht h => hle v t hv ht (under_digitGraph.1 h))
    (fun v t hv ht h hK => hlt v t hv ht (under_digitGraph.1 h) hK) hr

/-- `DubC.coreClosed_of_rankRevOn`, re-derived from `CarryGraph.cyc_mem_of_peelRank_rev`. -/
@[category research solved, AMS 11 37, ref "Dub09", group "carry_bridge_dubc"]
theorem coreClosed_of_rankRevOn' [NeZero M] (C K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hcyc : ∀ r, Relation.TransGen (Step a M) r r → C r)
    (hle : ∀ r t, C r → C t → Step a M r t → ρ r ≤ ρ t)
    (hlt : ∀ r t, C r → C t → Step a M r t → ¬ K t → ρ r < ρ t) :
    CoreClosed a M K :=
  coreClosed_iff.2 fun _ hr => cyc_mem_of_peelRank_rev (X := digitGraph a M) C K ρ
    (fun v hv => hcyc v (cyc_digitGraph.1 hv))
    (fun v t hv ht h => hle v t hv ht (under_digitGraph.1 h))
    (fun v t hv ht h hK => hlt v t hv ht (under_digitGraph.1 h) hK) hr

/-- **Reduction modulo `M' ∣ M` is a homomorphism of digit graphs** (the digit is kept). -/
def projHom [NeZero M] {M' : ℕ} [NeZero M'] (hdvd : M' ∣ M) :
    Hom (digitGraph a M) (digitGraph a M') where
  toFun := ZMod.castHom hdvd (ZMod M')
  map_adj := by
    intro r d t h
    obtain ⟨hr, ht, rfl⟩ := adj_digitGraph.1 h
    refine adj_digitGraph.2
      ⟨(cop_iff_isUnit _).mpr (RingHom.isUnit_map _ ((cop_iff_isUnit r).mp hr)),
      (cop_iff_isUnit _).mpr (RingHom.isUnit_map _ ((cop_iff_isUnit _).mp ht)), ?_⟩
    simp only [map_add, map_mul, map_natCast]

/-- **One rung of the ladder** (`DubC.coreClosed_of_ladder`), re-derived: cycles map to cycles
along `projHom` (`CarryGraph.Hom.cyc_map`), so the preimage of `K'` contains every cycle, and a
peel rank on it shrinks it to `K`. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "carry_bridge_dubc"]
theorem coreClosed_of_ladder' [NeZero M] {M' : ℕ} [NeZero M'] (hdvd : M' ∣ M)
    (K' : ZMod M' → Prop) (hK' : CoreClosed a M' K')
    (K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hle : ∀ r t, K' (ZMod.castHom hdvd (ZMod M') r) → K' (ZMod.castHom hdvd (ZMod M') t) →
      Step a M r t → ρ t ≤ ρ r)
    (hlt : ∀ r t, K' (ZMod.castHom hdvd (ZMod M') r) → K' (ZMod.castHom hdvd (ZMod M') t) →
      Step a M r t → ¬ K r → ρ t < ρ r) :
    CoreClosed a M K :=
  coreClosed_iff.2 fun _ hr => cyc_mem_of_peelRank (X := digitGraph a M)
    (fun r => K' (ZMod.castHom hdvd (ZMod M') r)) K ρ
    (fun _ hv => coreClosed_iff.1 hK' _ ((projHom (a := a) hdvd).cyc_map hv))
    (fun v t hv ht h => hle v t hv ht (under_digitGraph.1 h))
    (fun v t hv ht h hK => hlt v t hv ht (under_digitGraph.1 h) hK) hr

/-! ### Core certificates imply rank certificates -/

/-- **The core form implies `C(𝒫)`**: `CoreClosed` + `CoreDet` give `NoBranch`. -/
@[category research solved, AMS 05 11 37, ref "Dub09" "BJG09", group "carry_bridge_dubc"]
theorem noBranch_of_coreCert [NeZero M] {K : ZMod M → Prop} (hc : CoreClosed a M K)
    (hd : CoreDet a M K) : (digitGraph a M).NoBranch :=
  noBranch_of_cyc_det K (coreClosed_iff.1 hc) fun r t u hr ht hu hrt hru => by
    obtain ⟨-, -, d₁, hd₁, rfl⟩ := under_digitGraph.1 hrt
    obtain ⟨-, -, d₂, hd₂, rfl⟩ := under_digitGraph.1 hru
    exact hd r hr d₁ hd₁ d₂ hd₂ ht hu

/-- **A core certificate yields a rank certificate** (the converse fails, see
`DubC/Verdict.lean`: base `4`, modulus `6`). -/
@[category research solved, AMS 05 11 37, ref "Dub09" "BJG09", group "carry_bridge_dubc"]
theorem exists_certOK_of_coreCert [NeZero M] {K : ZMod M → Prop} (hc : CoreClosed a M K)
    (hd : CoreDet a M K) : ∃ ρ, CertOK a M ρ :=
  certOK_iff_noBranch.2 (noBranch_of_coreCert hc hd)

/-! ### Zero entropy of the coprimality subshift -/

/-- **A certificate exists iff residue walks grow polynomially.** -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_polyGrowth [NeZero M] :
    (∃ ρ, CertOK a M ρ) ↔ (digitGraph a M).forget.PolyGrowth := by
  classical
  rw [certOK_iff_noBranch]
  exact (digitGraph a M).noBranch_tfae.out 2 4

/-- **A certificate exists iff the coprimality subshift has entropy `≤ 0`.** -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_entropy [NeZero M] :
    (∃ ρ, CertOK a M ρ) ↔ (digitGraph a M).forget.entropy ≤ 0 := by
  classical
  rw [certOK_iff_noBranch]
  exact (digitGraph a M).noBranch_tfae.out 2 5

/-- **A certificate exists iff every admissible residue walk is eventually periodic.**  The
"only if" half is `DubC.eventually_periodic_of_rank`; the "if" half is the horseshoe. -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_allEvPer [NeZero M] :
    (∃ ρ, CertOK a M ρ) ↔ ∀ s : ℕ → ZMod M, (∀ n, Step a M (s n) (s (n + 1))) →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m := by
  classical
  rw [certOK_iff_noBranch, ← under_digitGraph_eq]
  exact (digitGraph a M).noBranch_tfae.out 2 3

/-- **With `a ≤ M`, a certificate exists iff the digit sequences have zero entropy**: the
labelled digit graph has entropy `≤ 0`. -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem certOK_iff_entropy_labelled [NeZero M] (haM : a ≤ M) :
    (∃ ρ, CertOK a M ρ) ↔ (digitGraph a M).entropy ≤ 0 := by
  classical
  simp_rw [certOK_iff_isLRank haM]
  exact (digitGraph a M).zeroEntropy_tfae.out 1 5

/-! ### The engine's core -/

/-- **The core of the digit graph is a valid `CoreClosed` set**: every cyclic unit lies in the
bi-infinite core, which `two_stage` identifies with the output of the engine's
forward-then-backward peel and `mem_coreSet` computes. -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem coreClosed_core [NeZero M] : CoreClosed a M (· ∈ (digitGraph a M).core) :=
  coreClosed_iff.2 fun _ hr => mem_core_of_cyc hr

/-- Any superset of the core is `CoreClosed`. -/
@[category research solved, AMS 05 11 37, ref "Dub09" "LM95", group "carry_bridge_dubc"]
theorem coreClosed_of_core_subset [NeZero M] {K : ZMod M → Prop}
    (h : (digitGraph a M).core ⊆ {r | K r}) : CoreClosed a M K :=
  coreClosed_iff.2 fun _ hr => h (mem_core_of_cyc hr)

/-! ### Instances (the `DubC/Verdict.lean` bases) -/

@[category test, AMS 05 11 37, ref "Dub09", group "carry_bridge_dubc"]
theorem noBranch_six_thirty : (digitGraph 6 30).NoBranch :=
  certOK_iff_noBranch.1 ⟨_, certOK_six⟩

/-- The rank form is strictly weaker than `CoreDet` on the units: at base `4`, modulus `6`, a
rank certificate exists but the units are not a deterministic core. -/
@[category test, AMS 05 11 37, ref "Dub09", group "carry_bridge_dubc"]
theorem noBranch_not_coreDet_four : (digitGraph 4 6).NoBranch ∧ ¬ CoreDet 4 6 (Cop 6) :=
  ⟨certOK_iff_noBranch.1 ⟨_, certOK_four⟩, not_coreDet_four_six⟩

/-! ### Full versus reduced model: a right cover -/

/-- **The reduced model** of `DubC/README.md`: the units mod `M'` with the digits `2, 4, 6` that
survive coprimality to `2` and `7`, labelled by the base-`7` digit. -/
def reducedGraph (M' : ℕ) [NeZero M'] : CarryGraph (ZMod M') (Fin 7) :=
  CarryGraph.ofRel fun ρ d σ => Cop M' ρ ∧ Cop M' σ ∧ ((d : ℕ) = 2 ∨ (d : ℕ) = 4 ∨ (d : ℕ) = 6) ∧
    σ = 7 * ρ + ((d : ℕ) : ZMod M')

@[category API, AMS 05 11, ref "Dub09", group "carry_bridge_dubc"]
theorem adj_reducedGraph {M' : ℕ} [NeZero M'] {ρ σ : ZMod M'} {d : Fin 7} :
    (reducedGraph M').Adj ρ d σ ↔ Cop M' ρ ∧ Cop M' σ ∧
      ((d : ℕ) = 2 ∨ (d : ℕ) = 4 ∨ (d : ℕ) = 6) ∧ σ = 7 * ρ + ((d : ℕ) : ZMod M') :=
  adj_ofRel

@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem cop_natCast {M k : ℕ} [NeZero M] : Cop M (k : ZMod M) ↔ Nat.Coprime k M := by
  rw [Cop, ZMod.val_natCast, Nat.Coprime, Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]

/-- Coprimality to `14 M'` splits into oddness, `7 ∤ ·` and coprimality to `M'`. -/
@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem coprime_fourteen_mul {k M' : ℕ} :
    Nat.Coprime k (14 * M') ↔ k % 2 = 1 ∧ k % 7 ≠ 0 ∧ Nat.Coprime k M' := by
  rw [Nat.coprime_mul_iff_right, show (14 : ℕ) = 2 * 7 by norm_num, Nat.coprime_mul_iff_right,
    Nat.coprime_two_right, Nat.odd_iff, and_assoc]
  have h7 : Nat.Coprime k 7 ↔ k % 7 ≠ 0 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide), Nat.dvd_iff_mod_eq_zero]
  rw [h7]

section full

variable {M' : ℕ} [NeZero M']

/-- Reduction mod `M'`. -/
abbrev red (M' : ℕ) : ZMod (14 * M') →+* ZMod M' := ZMod.castHom (dvd_mul_left M' 14) (ZMod M')

@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem red_eq_val (x : ZMod (14 * M')) : red M' x = (x.val : ZMod M') := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem cop_red {x : ZMod (14 * M')} : Cop M' (red M' x) ↔ Nat.Coprime x.val M' := by
  rw [red_eq_val, cop_natCast]

@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem step_val {x : ZMod (14 * M')} (d : ℕ) :
    ((7 : ℕ) : ZMod (14 * M')) * x + (d : ZMod (14 * M')) =
      ((7 * x.val + d : ℕ) : ZMod (14 * M')) := by
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- Every unit mod `M'` lifts to a unit mod `14 M'` (Chinese remainder theorem). -/
@[category API, AMS 05 11, group "carry_bridge_dubc"]
theorem exists_unit_lift (hc : Nat.Coprime M' 14) {ρ : ZMod M'} (hρ : Cop M' ρ) :
    ∃ x : ZMod (14 * M'), Cop (14 * M') x ∧ red M' x = ρ := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.symm hc) 1 ρ.val
  refine ⟨(k : ZMod (14 * M')), ?_, ?_⟩
  · rw [cop_natCast, coprime_fourteen_mul]
    have h14 : k % 14 = 1 := hk1
    refine ⟨by omega, by omega, ?_⟩
    have : Nat.Coprime (k % M') M' := by
      rw [show k % M' = ρ.val % M' from hk2, Nat.mod_eq_of_lt (ZMod.val_lt ρ)]; exact hρ
    rwa [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm] at this
  · rw [map_natCast, ← ZMod.natCast_mod, show k % M' = ρ.val % M' from hk2,
      Nat.mod_eq_of_lt (ZMod.val_lt ρ), ZMod.natCast_zmod_val]

/-- **The full model right-covers the reduced model** on the units: reduction mod `M'` maps the
`d`-successor of a unit mod `14 M'` to the `d`-successor of its reduction, and both exist
together.  The labels make the covering a bijection without a digit-collision argument, and
no hypothesis on `M'` is needed (coprimality to `14` enters only through the lifting of units,
`exists_unit_lift`). -/
@[category research solved, AMS 05 11 37, ref "LM95" "Dub09", group "carry_bridge_dubc"]
theorem digitGraph_rightCover :
    RightCover (reducedGraph M') (digitGraph 7 (14 * M')) (red M') {x | Cop (14 * M') x} where
  closed _ _ _ _ h := (adj_digitGraph.1 h).2.1
  bij x hx' d := by
    have hx : Cop (14 * M') x := hx'
    have hv : Nat.Coprime x.val (14 * M') := hx
    rw [coprime_fourteen_mul] at hv
    obtain ⟨hx2, hx7, hxM⟩ := hv
    have full : ∀ d : ℕ, d < 7 → (Cop (14 * M') (((7 : ℕ) : ZMod (14 * M')) * x + d) ↔
        (d = 2 ∨ d = 4 ∨ d = 6) ∧ Nat.Coprime (7 * x.val + d) M') := by
      intro d hd
      rw [step_val, cop_natCast, coprime_fourteen_mul]
      constructor
      · rintro ⟨h2, h7, hM⟩
        refine ⟨?_, hM⟩
        interval_cases d <;> omega
      · rintro ⟨hd, hM⟩
        exact ⟨by omega, by omega, hM⟩
    have redstep : ∀ d : ℕ,
        red M' (((7 : ℕ) : ZMod (14 * M')) * x + d) = 7 * red M' x + d := by
      intro d
      rw [map_add, map_mul, map_natCast, map_natCast, Nat.cast_ofNat]
    have copred : ∀ d : ℕ, Cop M' (7 * red M' x + d) ↔ Nat.Coprime (7 * x.val + d) M' := by
      intro d
      rw [red_eq_val, show (7 : ZMod M') * (x.val : ZMod M') + (d : ZMod M') =
        ((7 * x.val + d : ℕ) : ZMod M') by push_cast; ring, cop_natCast]
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨-, hy', rfl⟩ := adj_digitGraph.1 hy
      obtain ⟨hd', hM⟩ := (full d d.2).1 hy'
      exact adj_reducedGraph.2 ⟨cop_red.2 hxM, by rw [redstep]; exact (copred d).2 hM, hd',
        redstep d⟩
    · intro y₁ hy₁ y₂ hy₂ _
      rw [(adj_digitGraph.1 hy₁).2.2, (adj_digitGraph.1 hy₂).2.2]
    · intro σ hσ
      obtain ⟨-, hσ', hd, rfl⟩ := adj_reducedGraph.1 hσ
      exact ⟨_, adj_digitGraph.2 ⟨hx, (full d d.2).2 ⟨hd, (copred d).1 hσ'⟩, rfl⟩, redstep d⟩

/-- Path counts of a unit in the full model equal those of its reduction. -/
@[category research solved, AMS 05 11 37, ref "LM95" "Dub09", group "carry_bridge_dubc"]
theorem npaths_full_eq_reduced {x : ZMod (14 * M')}
    (hx : Cop (14 * M') x) (n : ℕ) :
    (digitGraph 7 (14 * M')).npaths x n = (reducedGraph M').npaths (red M' x) n :=
  npaths_eq_of_rightCover digitGraph_rightCover n x hx

/-- **Full and reduced model have the same verdict** (re-derived
from the generic right-cover theorem): a rank certificate exists for base `7` modulo `14 M'`
iff the reduced model modulo `M'` has no branching inside a strong component, although the two
cores differ in size. -/
@[category research solved, AMS 05 11 37, ref "LM95" "Dub09", group "carry_bridge_dubc"]
theorem certOK_full_iff_reduced' (hM : 1 ≤ M') (hc : Nat.Coprime M' 14) :
    (∃ ρ, CertOK 7 (14 * M') ρ) ↔ (reducedGraph M').LNoBranch := by
  classical
  simp_rw [certOK_iff_isLRank (show 7 ≤ 14 * M' by omega)]
  rw [exists_isLRank_iff_lnoBranch]
  refine lnoBranch_iff_of_rightCover digitGraph_rightCover
    (fun y hy d z h => hy (adj_digitGraph.1 h).1) fun ρ => ?_
  by_cases hρ : Cop M' ρ
  · obtain ⟨x, hx, rfl⟩ := exists_unit_lift hc hρ
    exact .inl ⟨x, hx, rfl⟩
  · exact .inr fun d σ h => hρ (adj_reducedGraph.1 h).1

end full

end CarryBridge
