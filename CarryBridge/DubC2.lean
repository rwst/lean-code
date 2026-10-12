/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Interval
import CarryGraph.Mirror
import DubC2.NuInterval
import DubC2.EntropyBound
import DubC2.FollowerInfinite
import DubC2.FollowerCheck
import DubC2.GenBlocks
import DubC2.Obstruction

/-!
# Bridge: `DubC2/` as a carry graph

A `DubC2.Gen` cell `P` (`p/q`, shift `ν = a/b`, residues mod `M`, `D` cells, divisor lists
`PM`, `Pq`, letters `sLo + t`, `t < nA`) is the affine carry graph of Chapter 8,

`genGraph P = affine p q (a/b) sLo nA M D PM Pq` (residue graph ⊗ cell graph),

and the certificate's vertex numbering `k = r·D + c` is the encoding `enc`.  Every arc listed by
`Params.succList` is an arc of `genGraph P` and conversely (`mem_succList_iff`), so the
certificate graph `certGraph P` (on `Fin nV`, arcs from `succList`) is isomorphic to `genGraph P`.

| `DubC2/` | `CarryGraph/` |
|---|---|
| `Params.succList` | `genGraph P = affine …` (`mem_succList_iff`) |
| `Checked P C` (peel + det + rank) | `(genGraph P).AllPer` (`checked_allPer`) |
| `C_det`, `λ_det = 1` | `checked_lnoBranch_det`, `checked_polyGrowth_det` |
| `sound` | `cover_affine` |
| `divisor_set_of_checked` | `frequently_not_avoid_of_allPer` (any cover) |
| `hullOK P a₀ a₁` | `Hom (affineHull …) (genGraph P)` (`hullHom`) |
| `divisor_set_of_checked_hull` | the same generic theorem with `cover_affineHull` |
| `EntCert.check` | a cover by `entGraph E` with a super-eigenvector (`entGraph_superEigen`) |
| `dimH_eventually_avoids_le` | `dimH_avoiders_le` for that cover |

Re-derived (primed names, same statements): `divisor_set_of_checked'`,
`divisor_set_of_checked_hull'`, `dimH_eventually_avoids_le'`.  The only arithmetic input taken
from the roots is [DN05] Lemma 2 (`Z32.not_isEventuallyPeriodic_carry`): the carry word of
`ξ(p/q)ⁿ + ν` is not eventually periodic for `ξ ≠ 0`.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. **251** (2005) 635–648.
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryBridge

open CarryGraph Filter ForMathlib.SubwordComplexity

/-! ### The generic divisor theorem -/

section Generic

variable {p q : ℕ} {ν : ℝ} {s₀ : ℤ} {nA : ℕ} {P : List ℕ} {V : Type*}
  {X : CarryGraph V (Fin nA)} {ρ : V → Set ℝ}

/-- The carry of the affine orbit is the carry word of [DN05]. -/
@[category API, AMS 11 37, ref "DN05", group "carry_bridge_dubc2"]
theorem carry_orb (ξ : ℝ) (n : ℕ) :
    carry p q ν (Z32.orb p q ξ ν n) = Z32.carry p q ξ ν n := by
  simp only [carry, Z32.carry, Z32.xInt, Z32.orb, affStep_orbit]

/-- **The generic divisor theorem**: if *some* cover of the affine system has the label form,
then for every `ξ ≠ 0` infinitely many of `⌊ξ(p/q)ⁿ + ν⌋` meet `P`.  ([DN05] Lemma 2 is the
only arithmetic input: the carry word is not eventually periodic.) -/
@[category research solved, AMS 11 37 05, ref "DN05" "LM95", group "carry_bridge_dubc2"]
theorem frequently_not_avoid_of_allPer (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (h : Cover X (fun _ => affStep p q ν) (affAdm p q ν s₀ P) ρ) (hρ : ∀ z, ∃ v, z ∈ ρ v)
    (hwin : ∀ z, s₀ ≤ carry p q ν z ∧ carry p q ν z < s₀ + nA) (hX : X.AllPer) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ¬ Avoid P (Z32.xInt p q ξ ν n) := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  let tl : ℕ → Fin nA := fun m =>
    ⟨(carry p q ν (Z32.orb p q ξ ν (N + m)) - s₀).toNat, by
      have := hwin (Z32.orb p q ξ ν (N + m)); omega⟩
  have htl : ∀ m, carry p q ν (Z32.orb p q ξ ν (N + m)) = s₀ + (tl m : ℕ) := fun m => by
    have := hwin (Z32.orb p q ξ ν (N + m)); simp only [tl]; omega
  have horb : ∀ m, orbit (fun _ => affStep p q ν) (Z32.orb p q ξ ν N) tl m
      = Z32.orb p q ξ ν (N + m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [orbit, ih]; exact affStep_orbit ξ (N + m)
  have hadm : AdmForever (fun _ => affStep p q ν) (affAdm p q ν s₀ P) (Z32.orb p q ξ ν N) tl := by
    intro m
    rw [horb]
    refine ⟨by rw [htl], hcon _ (by omega), ?_⟩
    show Avoid P ⌊affStep p q ν (ξ * ((p : ℝ) / q) ^ (N + m) + ν)⌋
    rw [affStep_orbit]
    exact hcon _ (by omega)
  obtain ⟨v, hv⟩ := hρ (Z32.orb p q ξ ν N)
  obtain ⟨n₀, L, hL, hper⟩ := h.evPer_of_allPer hX hv hadm
  apply Z32.not_isEventuallyPeriodic_carry (p := p) (q := q) (ξ := ξ) (ν := ν) hq hpq hcop hξ
  refine ⟨N + n₀, L, hL, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
  rw [← carry_orb, ← carry_orb, show N + m + L = N + (m + L) by ring, htl, htl,
    hper m (by omega)]

end Generic

/-! ### The certificate graph -/

open DubC2.Gen

variable {P : Params}

/-- The shift `ν = a/b` of a cell, as a rational. -/
def nuQ (P : Params) : ℚ := (P.a : ℚ) / P.b

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem nuQ_cast (P : Params) : ((nuQ P : ℚ) : ℝ) = (P.a : ℝ) / P.b := by
  simp [nuQ]

/-- **The carry graph of a `DubC2` cell**: the affine graph at `ν = a/b`. -/
def genGraph (P : Params) [NeZero P.M] : CarryGraph (ZMod P.M × Fin P.D) (Fin P.nA) :=
  affine P.p P.q (nuQ P) P.sLo P.nA P.M P.D P.PM P.Pq

/-- **The certificate graph**: vertex numbers `k < nV`, arcs listed by `succList`. -/
def certGraph (P : Params) : CarryGraph (Fin P.nV) (Fin P.nA) :=
  ofRel fun k t k' => (k' : ℕ) ∈ P.succList k (P.letter t)

/-- The vertex number `r·D + c` of a vertex `(r, c)`. -/
def enc (P : Params) [NeZero P.M] (v : ZMod P.M × Fin P.D) : Fin P.nV :=
  ⟨v.1.val * P.D + v.2, by
    have h1 := ZMod.val_lt v.1
    have h2 := v.2.2
    calc v.1.val * P.D + v.2 < v.1.val * P.D + P.D := by omega
      _ = (v.1.val + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ h1⟩

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem enc_div (P : Params) [NeZero P.M] (v : ZMod P.M × Fin P.D) :
    (enc P v : ℕ) / P.D = v.1.val := by
  have h2 := v.2.2
  simp only [enc]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2, zero_add]

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem enc_mod (P : Params) [NeZero P.M] (v : ZMod P.M × Fin P.D) :
    (enc P v : ℕ) % P.D = v.2 := by
  simp only [enc]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.2.2]

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem enc_injective (P : Params) [NeZero P.M] : Function.Injective (enc P) := by
  intro v w h
  have h1 := enc_div P v
  have h2 := enc_mod P v
  rw [h] at h1 h2
  rw [enc_div] at h1
  rw [enc_mod] at h2
  exact Prod.ext (ZMod.val_injective _ h1.symm) (Fin.ext h2.symm)

/-- The residue step of the certificate is the residue graph's. -/
@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem rnext_val (hF : ParamFacts P) [NeZero P.M] {r r' : ZMod P.M} {s : ℤ}
    (h : (P.q : ZMod P.M) * r' = P.p * r + (s : ZMod P.M)) : P.rnext r.val s = r'.val := by
  have hinv : ((P.q : ZMod P.M) * P.qinv) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (P.q * P.qinv) 1 P.M).2 hF.inv
    push_cast at this
    exact this
  have hx : ((((P.p : ℤ) * r.val + s) * P.qinv : ℤ) : ZMod P.M) = r' := by
    push_cast
    rw [ZMod.natCast_zmod_val, ← h]
    linear_combination r' * hinv
  have hv := ZMod.val_intCast (n := P.M) (((P.p : ℤ) * r.val + s) * P.qinv)
  rw [hx] at hv
  simp only [Params.rnext]
  rw [← hv, Int.toNat_natCast]

/-- The cell arc of `genGraph`, in the certificate's integer form. -/
@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem cellArc_iff (hF : ParamFacts P) {c c₂ : Fin P.D} {t : Fin P.nA} :
    (cellGraph P.p P.q (nuQ P) P.sLo P.nA P.D).Adj c t c₂ ↔
      (P.q : ℤ) * P.b * (c₂ : ℕ) < P.hi c (P.letter t) ∧
        P.lo c (P.letter t) < (P.q : ℤ) * P.b * ((c₂ : ℕ) + 1) := by
  have hb : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  have hD : (0 : ℚ) < P.D := by exact_mod_cast hF.D0
  have hbD : (0 : ℚ) < P.b * P.D := by positivity
  simp only [cellGraph, blockGraph, Adj, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [cells, nuQ]
  have d1 : (P.p : ℚ) * ((((c : ℕ) : ℚ) + 1) / P.D) - ((P.p : ℚ) - P.q) * ((P.a : ℚ) / P.b)
      - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ) - P.q * (((c₂ : ℕ) : ℚ) / P.D)
      = ((P.hi c (P.letter t) - P.q * P.b * (c₂ : ℕ) : ℤ) : ℚ) / (P.b * P.D) := by
    simp only [Params.hi, Params.shiftK, Params.letter]
    push_cast
    field_simp
    ring
  have d2 : (P.q : ℚ) * ((((c₂ : ℕ) : ℚ) + 1) / P.D) - ((P.p : ℚ) * (((c : ℕ) : ℚ) / P.D)
      - ((P.p : ℚ) - P.q) * ((P.a : ℚ) / P.b) - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ))
      = ((P.q * P.b * ((c₂ : ℕ) + 1) - P.lo c (P.letter t) : ℤ) : ℚ) / (P.b * P.D) := by
    simp only [Params.lo, Params.shiftK, Params.letter]
    push_cast
    field_simp
    ring
  have k1 : (P.q : ℚ) * (((c₂ : ℕ) : ℚ) / P.D) < P.p * ((((c : ℕ) : ℚ) + 1) / P.D)
      - ((P.p : ℚ) - P.q) * ((P.a : ℚ) / P.b) - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ) ↔
      (P.q : ℤ) * P.b * (c₂ : ℕ) < P.hi c (P.letter t) := by
    rw [← sub_pos, d1, div_pos_iff_of_pos_right hbD, Int.cast_pos, sub_pos]
  have k2 : (P.p : ℚ) * (((c : ℕ) : ℚ) / P.D) - ((P.p : ℚ) - P.q) * ((P.a : ℚ) / P.b)
      - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ) < P.q * ((((c₂ : ℕ) : ℚ) + 1) / P.D) ↔
      P.lo c (P.letter t) < (P.q : ℤ) * P.b * ((c₂ : ℕ) + 1) := by
    rw [← sub_pos, d2, div_pos_iff_of_pos_right hbD, Int.cast_pos, sub_pos]
  rw [k1, k2]

/-- **Every arc of `genGraph P` is listed by `succList`** (the converse is
`adj_of_mem_succList`). -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem mem_succList (hF : ParamFacts P) [NeZero P.M] {v v' : ZMod P.M × Fin P.D}
    {t : Fin P.nA} (h : (genGraph P).Adj v t v') :
    (enc P v' : ℕ) ∈ P.succList (enc P v) (P.letter t) := by
  obtain ⟨hr, hc⟩ := adj_labelProduct.1 h
  obtain ⟨h1, h2, h3, h4⟩ := adj_residueGraph.1 hr
  obtain ⟨hhi, hlo⟩ := (cellArc_iff hF).1 hc
  have hrn : P.rnext v.1.val (P.letter t) = v'.1.val := rnext_val hF h3
  have hw : (0 : ℤ) < (P.q : ℤ) * P.b := by
    have := hF.q1; have := hF.b0; positivity
  have hcond : ((P.PM.all fun l => v.1.val % l != 0) &&
      (P.Pq.all fun l => P.letter t % (l : ℤ) != 0) &&
      (P.PM.all fun l => P.rnext v.1.val (P.letter t) % l != 0)) = true := by
    rw [hrn]
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨fun l hl hm => h1 l hl ?_, fun l hl hm => h2 l hl ?_⟩, fun l hl hm => h4 l hl ?_⟩
    · exact Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hm)
    · exact Int.dvd_of_emod_eq_zero hm
    · exact Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hm)
  simp only [Params.succList]
  rw [enc_div, enc_mod, ite_eq_left_of_eq_true _ _ (eq_true hcond)]
  simp only [List.mem_map, List.mem_filter, List.mem_range'_1, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨v'.2, ⟨⟨?_, ?_⟩, hhi, hlo⟩, ?_⟩
  · simp only [Params.cLo]
    rw [Int.toNat_le]
    have : P.lo v.2 (P.letter t) / ((P.q : ℤ) * P.b) < ((v'.2 : ℕ) : ℤ) + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hw]; linarith
    omega
  · have h2' : (v'.2 : ℕ) < P.cHi v.2 (P.letter t) := by
      simp only [Params.cHi]
      refine lt_min v'.2.2 ?_
      rw [Int.lt_toNat]
      have : ((v'.2 : ℕ) : ℤ) ≤ (P.hi v.2 (P.letter t) - 1) / ((P.q : ℤ) * P.b) := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      omega
    omega
  · rw [hrn]; rfl

/-- **The encoding is a homomorphism** `genGraph P → certGraph P`. -/
def encHom (hF : ParamFacts P) [NeZero P.M] : Hom (genGraph P) (certGraph P) :=
  ⟨enc P, fun h => adj_ofRel.2 (mem_succList hF h)⟩

/-- **A checked certificate gives the label form of its certificate graph.** -/
@[category research solved, AMS 11 05 37, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem certGraph_allPer {C : Cert} (hc : Checked P C) : (certGraph P).AllPer := by
  intro s ℓ hs
  have hp : IsPath P 0 (fun n => s n) (fun n => ℓ n) :=
    ⟨fun n _ => (s n).2, fun n _ => (ℓ n).2, fun n _ => adj_ofRel.1 (hs n)⟩
  obtain ⟨N, L, hL, hper⟩ := isEventuallyPeriodic_of_path hc hp
  exact ⟨N, L, hL, fun m hm => Fin.ext (hper m hm)⟩

/-- The side conditions of a checked certificate. -/
@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem paramFacts_of_checked {C : Cert} (hc : Checked P C) : ParamFacts P := by
  have hh := hc.head
  simp only [checkHead, Bool.and_eq_true] at hh
  exact paramFacts hh.1.1.1.1.1

/-- **A checked certificate gives the label form of the affine carry graph** of its cell. -/
@[category research solved, AMS 11 05 37, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem checked_allPer [NeZero P.M] {C : Cert} (hc : Checked P C) : (genGraph P).AllPer :=
  allPer_of_hom (encHom (paramFacts_of_checked hc)) (certGraph_allPer hc)

/-- **`C_det`**: the subset construction of the affine graph of a checked cell has no labelled
branching. -/
@[category research solved, AMS 11 05 37, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem checked_lnoBranch_det [NeZero P.M] {C : Cert} (hc : Checked P C) :
    (genGraph P).det.LNoBranch :=
  ((determinization (X := genGraph P)).out 1 3).1 (checked_allPer hc)

/-- **`λ_det = 1`**: the subset construction of the affine graph of a checked cell has
polynomial path growth. -/
@[category research solved, AMS 11 05 37, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem checked_polyGrowth_det [NeZero P.M] {C : Cert} (hc : Checked P C) :
    (genGraph P).det.PolyGrowth :=
  allPer_iff_polyGrowth_det.1 (checked_allPer hc)

/-! ### The certificate's own structure: peel rounds and the det automaton

`Checked` is two certificates in one.  The rounds are a peel chain of the certificate graph
that ends inside the listed core (`checked_isPeelChain`, `checked_round_core`).  The det table is
a carry graph on det-state numbers with a labelled rank (`checked_isLRank_det`), and it
simulates the certificate graph on the core (`checked_detSim`).  The generic theorem
`allPer_of_peelChain` then gives the label form, without `Gen.isEventuallyPeriodic_of_path`. -/

/-- Round `j` of the peel, as a vertex set. -/
def roundSet (P : Params) (C : Cert) (j : ℕ) : Set (Fin P.nV) := {k | C.memA P j k = true}

/-- The listed core, as a vertex set. -/
def coreSet (C : Cert) (P : Params) : Set (Fin P.nV) := {k | (k : ℕ) ∈ C.core}

instance (C : Cert) (P : Params) : DecidablePred (· ∈ coreSet C P) := fun k =>
  inferInstanceAs (Decidable ((k : ℕ) ∈ C.core))

@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem mem_roundSet_zero (C : Cert) (k : Fin P.nV) : k ∈ roundSet P C 0 := by
  simp [roundSet, Cert.memA]

/-- **The peel rounds form a peel chain** of the certificate graph. -/
@[category research solved, AMS 11 05 37, ref "LM95", group "carry_bridge_dubc2"]
theorem checked_isPeelChain {C : Cert} (hc : Checked P C) :
    (certGraph P).IsPeelChain (roundSet P C) C.J := by
  rintro j hj k hk ⟨w, hw, t, hkw⟩ ⟨u, hu, t', huk⟩
  have hkw' := adj_ofRel.1 hkw
  have huk' := adj_ofRel.1 huk
  exact (round_at hc hj hk k.2).2 ⟨t, t.2, w, hkw', hw⟩
    ((round_at hc hj hu u.2).1 t' t'.2 k huk')

/-- **The last round lies in the listed core.** -/
@[category research solved, AMS 11 05 37, group "carry_bridge_dubc2"]
theorem checked_round_core {C : Cert} (hc : Checked P C) :
    roundSet P C C.J ⊆ coreSet C P := by
  intro k hA
  obtain ⟨-, hZ, hcov, hcore, -⟩ := head_facts hc
  have hi : (k : ℕ) / C.Z < C.nB := (Nat.div_lt_iff_lt_mul hZ).2 (by have := k.2; linarith)
  have h := List.all_eq_true.1 (hcore _ hi) ((k : ℕ) % C.Z) (mem_blk_scan hZ hA)
  rw [Nat.div_add_mod' (k : ℕ) C.Z] at h
  simp only [roundSet, Set.mem_ofPred_eq] at hA
  rw [hA] at h
  simpa [coreSet] using h

/-- **The det automaton as a carry graph**: an arc `i →t j` iff the table sends state `i` under
letter `t` to state `j`. -/
def detGraph (P : Params) (C : Cert) : CarryGraph (Fin C.sets.length) (Fin P.nA) :=
  ofRel fun i t j => (C.trans.getD i []).getD t none = some (j : ℕ)

private theorem det_row {C : Cert} (hc : Checked P C) (i : Fin C.sets.length) :
    (∀ t < P.nA, (match (C.trans.getD i []).getD t none with
      | none => detSucc P C (C.sets.getD i 0) (P.letter t) == 0
      | some j => decide (j < C.sets.length) &&
          subset (detSucc P C (C.sets.getD i 0) (P.letter t)) (C.sets.getD j 0) &&
          decide (C.rank.getD j 0 ≤ C.rank.getD i 0)) = true) ∧
      (keep C P.nA i).length ≤ 1 := by
  have hdet := List.all_eq_true.1 hc.det i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  simp only [detOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hdet
  exact ⟨fun t ht => hdet.1 t ht, hdet.2⟩

/-- **The det rank is a labelled rank** of the det automaton. -/
@[category research solved, AMS 11 05 37, ref "LM95", group "carry_bridge_dubc2"]
theorem checked_isLRank_det {C : Cert} (hc : Checked P C) :
    (detGraph P C).IsLRank fun i => C.rank.getD i 0 := by
  have hstep : ∀ (i : Fin C.sets.length) (t : Fin P.nA) (j : Fin C.sets.length),
      (detGraph P C).Adj i t j → C.rank.getD j 0 ≤ C.rank.getD i 0 := by
    intro i t j h
    have hrow := (det_row hc i).1 t t.2
    rw [adj_ofRel.1 h] at hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact hrow.2
  have hkeep : ∀ (i : Fin C.sets.length) (t : Fin P.nA) (j : Fin C.sets.length),
      (detGraph P C).Adj i t j → C.rank.getD j 0 = C.rank.getD i 0 → (t : ℕ) ∈ keep C P.nA i := by
    intro i t j h hr
    simp only [keep, List.mem_filter, List.mem_range, adj_ofRel.1 h, hr, beq_self_eq_true,
      and_true]
    exact t.2
  refine ⟨hstep, fun i a b t u ht hu h1 h2 => ?_⟩
  have hab : a = b := Fin.ext <| (eq_headD_of_mem (det_row hc i).2 (hkeep _ _ _ ht h1)).trans
    (eq_headD_of_mem (det_row hc i).2 (hkeep _ _ _ hu h2)).symm
  subst hab
  have e := (adj_ofRel.1 ht).symm.trans (adj_ofRel.1 hu)
  exact ⟨rfl, Fin.ext (Option.some_injective _ e)⟩

/-- The relation between a core vertex and a det state containing it. -/
def detRel (C : Cert) (k : Fin P.nV) (i : Fin C.sets.length) : Prop :=
  (k : ℕ) ∈ C.core ∧ (C.sets.getD i 0).testBit (C.core.idxOf (k : ℕ)) = true

/-- **The det automaton simulates the certificate graph on the core.** -/
@[category research solved, AMS 11 05 37, ref "LM95", group "carry_bridge_dubc2"]
theorem checked_detSim {C : Cert} (hc : Checked P C) :
    IsSimulation ((certGraph P).restrict (coreSet C P)) (detGraph P C) (detRel C) := by
  rintro k i ⟨hk, hb⟩ t k' hadj
  obtain ⟨-, hkk', hk'⟩ := adj_restrict.1 hadj
  have hmem := adj_ofRel.1 hkk'
  have hT :
      (detSucc P C (C.sets.getD i 0) (P.letter t)).testBit (C.core.idxOf (k' : ℕ)) = true := by
    rw [detSucc, testBit_orFold]
    refine ⟨C.core.idxOf (k : ℕ), mem_bits hb, rfl, ?_⟩
    rw [getD_idxOf hk]
    exact testBit_succIdx hmem hk'
  have hrow := (det_row hc i).1 t t.2
  revert hrow
  cases e : (C.trans.getD i []).getD t none with
  | none =>
    intro hrow
    simp only [beq_iff_eq] at hrow
    exact absurd hrow (ne_zero_of_testBit hT)
  | some j =>
    intro hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact ⟨⟨j, hrow.1.1⟩, adj_ofRel.2 e, hk', testBit_of_subset hrow.1.2 hT⟩

/-- Det state `0` contains the whole core. -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem checked_detTot {C : Cert} (hc : Checked P C) :
    ∀ k ∈ coreSet C P, ∃ i, detRel C k i := by
  intro k hk
  obtain ⟨hlen, -, -, -, h0⟩ := head_facts hc
  refine ⟨⟨0, hlen⟩, hk, testBit_of_subset h0 ?_⟩
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact List.idxOf_lt_length_of_mem hk

/-- **The label form of the certificate graph, from the certificate's structure**
(`certGraph_allPer` re-derived): peel chain into the core, det simulation, labelled rank. -/
@[category research solved, AMS 11 05 37, ref "LM95", group "carry_bridge_dubc2"]
theorem certGraph_allPer' {C : Cert} (hc : Checked P C) : (certGraph P).AllPer :=
  allPer_of_peelChain (checked_isPeelChain hc) (mem_roundSet_zero C) (checked_round_core hc)
    (checked_detSim hc) (checked_detTot hc)
    (allPer_of_lnoBranch (checked_isLRank_det hc).lnoBranch)

/-! ### The cycle certificate as a peel rank -/

/-- **The rank-keeping part of the det automaton**: the arcs that keep the det rank. -/
def keepGraph (P : Params) (C : Cert) : CarryGraph (Fin C.sets.length) (Fin P.nA) :=
  ofRel fun i t j => (C.trans.getD i []).getD t none = some (j : ℕ) ∧
    C.rank.getD j 0 = C.rank.getD i 0

/-- The rank-keeping part is functional: one arc out of each state at most. -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem checked_keepGraph_functional {C : Cert} (hc : Checked P C) :
    (keepGraph P C).Functional := by
  intro i a b t u ht hu
  obtain ⟨ht1, ht2⟩ := adj_ofRel.1 ht
  obtain ⟨hu1, hu2⟩ := adj_ofRel.1 hu
  exact (checked_isLRank_det hc).2 i a b t u (adj_ofRel.2 ht1) (adj_ofRel.2 hu1) ht2 hu2

/-- An arc of the rank-keeping part is the `fstep` of its tail. -/
private theorem keep_arc {C : Cert} (hc : Checked P C) {i j : Fin C.sets.length} {t : Fin P.nA}
    (h : (keepGraph P C).Adj i t j) :
    ¬ (keep C P.nA i).isEmpty ∧ fstep C P.nA i = j := by
  obtain ⟨h1, h2⟩ := adj_ofRel.1 h
  have hmem : (t : ℕ) ∈ keep C P.nA i := by
    simp only [keep, List.mem_filter, List.mem_range, h1, h2, beq_self_eq_true, and_true]
    exact t.2
  have hkf : kf C P.nA i = t := (eq_headD_of_mem (det_row hc i).2 hmem).symm
  refine ⟨fun he => by rw [List.isEmpty_iff] at he; simp [he] at hmem, ?_⟩
  simp only [fstep, hkf, next, h1, Option.getD_some]

private theorem listed_iff {cyc : List (List ℕ × ℕ × ℕ)} {i : ℕ} :
    listed cyc i = true ↔ ∃ c ∈ cyc, i ∈ c.1 := by
  simp [listed, List.any_eq_true]

/-- **Every cycle of the rank-keeping part is listed** (`CycChecked` read as a peel rank: rank `0`
on the listed states, potential `+ 1` elsewhere, strictly dropping off the listed states). -/
@[category research solved, AMS 11 05 37, ref "BJG09", group "carry_bridge_dubc2"]
theorem cycChecked_cyc_listed {C : Cert} (hc : Checked P C) {W : List (List ℤ)}
    {cyc : List (List ℕ × ℕ × ℕ)} {pot : List ℕ} (hcc : CycChecked P C W cyc pot)
    {i : Fin C.sets.length} (hi : (keepGraph P C).Cyc i) : listed cyc i = true := by
  classical
  let ρ : Fin C.sets.length → ℕ := fun x => if listed cyc x then 0 else pot.getD x 0 + 1
  -- listed states step to listed states
  have hclosed : ∀ {x y : Fin C.sets.length} {t : Fin P.nA}, (keepGraph P C).Adj x t y →
      listed cyc x = true → listed cyc y = true := by
    intro x y t h hx
    obtain ⟨c, hc', hxc⟩ := listed_iff.1 hx
    obtain ⟨hlen, -, -, -, hstep⟩ := cycOK_spec (List.all_eq_true.1 hcc.cycles c hc')
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.1 hxc
    have hg : c.1.getD j 0 = x := by simp [List.getD_eq_getElem?_getD, hj, hjx]
    have := (hstep j hj).1
    rw [hg, (keep_arc hc h).2] at this
    refine listed_iff.2 ⟨c, hc', ?_⟩
    rw [this]
    have hl : (j + 1) % c.1.length < c.1.length := Nat.mod_lt _ hlen
    simp [List.getD_eq_getElem?_getD, hl, List.getElem_mem]
  have hle : ∀ x y : Fin C.sets.length, True → True → (keepGraph P C).under x y → ρ y ≤ ρ x := by
    rintro x y - - ⟨t, h⟩
    by_cases hx : listed cyc x
    · simp [ρ, hx, hclosed h hx]
    · by_cases hy : listed cyc y
      · simp [ρ, hx, hy]
      · have hp := List.all_eq_true.1 hcc.pot x (List.mem_range.2 x.2)
        obtain ⟨hne, hf⟩ := keep_arc hc h
        have hr := (adj_ofRel.1 h).2
        simp only [potOK, Bool.or_eq_true, hx, hne, hf, hy, bne_iff_ne, ne_eq, hr,
          not_true_eq_false, decide_eq_true_eq, false_or, Bool.false_eq_true] at hp
        simp only [ρ, hx, hy, Bool.false_eq_true, ite_false]
        omega
  have hlt : ∀ x y : Fin C.sets.length, True → True → (keepGraph P C).under x y →
      ¬ (listed cyc x = true) → ρ y < ρ x := by
    rintro x y - - ⟨t, h⟩ hx
    by_cases hy : listed cyc y
    · simp [ρ, hx, hy]
    · have hp := List.all_eq_true.1 hcc.pot x (List.mem_range.2 x.2)
      obtain ⟨hne, hf⟩ := keep_arc hc h
      have hr := (adj_ofRel.1 h).2
      simp only [potOK, Bool.or_eq_true, hx, hne, hf, hy, bne_iff_ne, ne_eq, hr,
        not_true_eq_false, decide_eq_true_eq, false_or, Bool.false_eq_true] at hp
      simp only [ρ, hx, hy, Bool.false_eq_true, ite_false]
      omega
  exact cyc_mem_of_peelRank (X := keepGraph P C) (fun _ => True)
    (fun x : Fin C.sets.length => listed cyc x = true) ρ (fun _ _ => trivial) hle hlt hi

/-- The vertex `(r, c)` of a vertex number `k = r·D + c`. -/
def dec (hF : ParamFacts P) [NeZero P.M] (k : Fin P.nV) : ZMod P.M × Fin P.D :=
  ((((k : ℕ) / P.D : ℕ) : ZMod P.M), ⟨(k : ℕ) % P.D, Nat.mod_lt _ hF.D0⟩)

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem div_lt_M (hF : ParamFacts P) (k : Fin P.nV) : (k : ℕ) / P.D < P.M :=
  (Nat.div_lt_iff_lt_mul hF.D0).2 k.2

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem enc_dec (hF : ParamFacts P) [NeZero P.M] (k : Fin P.nV) : enc P (dec hF k) = k := by
  apply Fin.ext
  simp only [enc, dec, ZMod.val_natCast, Nat.mod_eq_of_lt (div_lt_M hF k)]
  exact Nat.div_add_mod' _ _

/-- **Every arc listed by `succList` is an arc of `genGraph P`.** -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem adj_of_mem_succList (hF : ParamFacts P) [NeZero P.M] {k k' : Fin P.nV} {t : Fin P.nA}
    (h : (k' : ℕ) ∈ P.succList k (P.letter t)) : (genGraph P).Adj (dec hF k) t (dec hF k') := by
  have hinv : ((P.q : ZMod P.M) * P.qinv) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (P.q * P.qinv) 1 P.M).2 hF.inv
    push_cast at this
    exact this
  simp only [Params.succList] at h
  split_ifs at h with hc
  · obtain ⟨c₂, hc₂, hk'⟩ := List.mem_map.1 h
    rw [List.mem_filter, List.mem_range'_1] at hc₂
    obtain ⟨⟨hc₂lo, hc₂D⟩, hcond⟩ := hc₂
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hD : c₂ < P.D := by
      have : P.cHi ((k : ℕ) % P.D) (P.letter t) ≤ P.D := min_le_left _ _
      omega
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have hrn := rnext_lt hF ((k : ℕ) / P.D) (P.letter t)
    have hdk : dec hF k' = (((P.rnext ((k : ℕ) / P.D) (P.letter t) : ℕ) : ZMod P.M), ⟨c₂, hD⟩) := by
      simp only [dec, ← hk']
      refine Prod.ext ?_ (Fin.ext ?_)
      · simp only
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hF.D0, Nat.div_eq_of_lt hD, zero_add]
      · simp only
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hD]
    rw [hdk]
    refine adj_labelProduct.2 ⟨adj_residueGraph.2 ⟨?_, ?_, ?_, ?_⟩, (cellArc_iff hF).2 hcond⟩
    · intro l hl hdvd
      simp only [dec, ZMod.val_natCast, Nat.mod_eq_of_lt (div_lt_M hF k)] at hdvd
      exact h1 l hl (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 hdvd))
    · intro l hl hdvd
      exact h2 l hl (Int.emod_eq_zero_of_dvd hdvd)
    · simp only [dec, Params.rnext]
      have hx : (((((P.p : ℤ) * ((k : ℕ) / P.D : ℕ) + P.letter t) * P.qinv % P.M).toNat : ℕ)
          : ZMod P.M)
          = ((((P.p : ℤ) * ((k : ℕ) / P.D : ℕ) + P.letter t) * P.qinv : ℤ) : ZMod P.M) := by
        rw [← Int.cast_natCast,
          Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hF.M0.ne')), ZMod.intCast_mod]
      rw [hx]
      simp only [Params.letter, Int.cast_mul, Int.cast_add, Int.cast_natCast]
      linear_combination ((P.p : ZMod P.M) * (((k : ℕ) / P.D : ℕ) : ZMod P.M)
        + (P.sLo : ZMod P.M) + ((t : ℕ) : ZMod P.M)) * hinv
    · intro l hl hdvd
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrn] at hdvd
      exact h3 l hl (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 hdvd))
  · simp at h

/-- **Decoding is a homomorphism** `certGraph P → genGraph P`; with `encHom` the two graphs are
isomorphic. -/
def decHom (hF : ParamFacts P) [NeZero P.M] : Hom (certGraph P) (genGraph P) :=
  ⟨dec hF, fun h => adj_of_mem_succList hF (adj_ofRel.1 h)⟩

/-- The certificate graph and the affine graph have the same label form. -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem allPer_certGraph_iff (hF : ParamFacts P) [NeZero P.M] :
    (certGraph P).AllPer ↔ (genGraph P).AllPer :=
  ⟨allPer_of_hom (encHom hF), allPer_of_hom (decHom hF)⟩

/-- **The obstruction, through the carry graph**: a pseudo-orbit whose letters are not
eventually periodic rules out the label form of the affine graph, for every `M` and `D`
([Oda26] Lemma 38 read backwards; the witnesses of `not_checked_of_horseOK`,
`not_checked_of_branchOK` and `not_checked_of_two_letters` are such pseudo-orbits). -/
@[category research solved, AMS 11 37 05, ref "Oda26", group "carry_bridge_dubc2"]
theorem not_allPer_of_pseudoOrbit (hF : ParamFacts P) [NeZero P.M] {r : ℕ → ℕ} {y : ℕ → ℝ}
    {s : ℕ → ℤ} (h : PseudoOrbit P r y s) (hs : ¬ IsEventuallyPeriodic s) :
    ¬ (genGraph P).AllPer := by
  intro hX
  have hc := (allPer_certGraph_iff hF).2 hX
  let v : ℕ → Fin P.nV := fun n => ⟨PseudoOrbit.pvtx P r y n, (PseudoOrbit.step hF h n).1⟩
  let ℓ : ℕ → Fin P.nA := fun n => ⟨PseudoOrbit.ptix P s n, (PseudoOrbit.step hF h n).2.1⟩
  have hp : (certGraph P).IsIPath v ℓ := fun n => adj_ofRel.2 (PseudoOrbit.step hF h n).2.2.2
  obtain ⟨N, L, hL, hper⟩ := hc v ℓ hp
  refine hs ⟨N, L, hL, fun k hk => ?_⟩
  have e := congrArg Fin.val (hper k hk)
  simp only [ℓ] at e
  rw [← (PseudoOrbit.step hF h k).2.2.1, ← (PseudoOrbit.step hF h (k + L)).2.2.1, e]

/-! ### The affine cover of a cell -/

/-- The carry window of a cell. -/
@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem window (hF : ParamFacts P) {ν : ℝ} {a₀ a₁ : ℤ} (h₀ : (a₀ : ℝ) ≤ P.b * ν)
    (h₁ : (P.b : ℝ) * ν ≤ a₁)
    (hlo : (P.b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * a₁)
    (hhi : (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * a₀ ≤ (P.b : ℤ) * (P.sLo + P.nA)) (z : ℝ) :
    P.sLo ≤ carry P.p P.q ν z ∧ carry P.p P.q ν z < P.sLo + P.nA := by
  have hq : P.q ≠ 0 := by have := hF.q1; omega
  have hp : 0 < P.p := by have := hF.q1; have := hF.pq; omega
  obtain ⟨c1, c2⟩ := carry_bounds (p := P.p) (ν := ν) hq hp z
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hK : (0 : ℝ) ≤ (P.p : ℝ) - P.q := by
    have : (P.q : ℝ) ≤ P.p := by exact_mod_cast hF.pq.le
    linarith
  have hlo' : (P.b : ℝ) * (P.sLo - 1) ≤ -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * a₁ := by
    exact_mod_cast hlo
  have hhi' : (P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * a₀ ≤ (P.b : ℝ) * (P.sLo + P.nA) := by
    exact_mod_cast hhi
  have e0 := mul_le_mul_of_nonneg_left h₀ hK
  have e1 := mul_le_mul_of_nonneg_left h₁ hK
  constructor
  · have : ((P.sLo - 1 : ℤ) : ℝ) < carry P.p P.q ν z := by
      push_cast
      have : (P.b : ℝ) * (P.sLo - 1) < P.b * carry P.p P.q ν z := by nlinarith
      exact lt_of_mul_lt_mul_left this hb.le
    have := Int.cast_lt.1 this
    omega
  · have : (carry P.p P.q ν z : ℝ) < ((P.sLo + P.nA : ℤ) : ℝ) := by
      push_cast
      have : (P.b : ℝ) * carry P.p P.q ν z < P.b * (P.sLo + P.nA) := by nlinarith
      exact lt_of_mul_lt_mul_left this hb.le
    exact_mod_cast this

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem hPM_of (hF : ParamFacts P) : ∀ ℓ ∈ P.PM, ℓ ∣ P.M ∧ ℓ ∈ P.PM ++ P.Pq :=
  fun l hl => ⟨Nat.dvd_of_mod_eq_zero (hF.PM l hl), List.mem_append_left _ hl⟩

@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem hPq_of (hF : ParamFacts P) : ∀ ℓ ∈ P.Pq, ℓ ∣ P.q ∧ Nat.Coprime ℓ P.p ∧ ℓ ∈ P.PM ++ P.Pq :=
  fun l hl => ⟨Nat.dvd_of_mod_eq_zero (hF.Pq l hl).1, (hF.Pq l hl).2, List.mem_append_right _ hl⟩

/-- **The affine cover of a cell** at every real shift `ν`, with the divisor set
`PM ++ Pq`. -/
@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem cover_genGraph (hF : ParamFacts P) [NeZero P.M] :
    Cover (genGraph P) (fun _ => affStep P.p P.q (nuQ P))
      (affAdm P.p P.q (nuQ P) P.sLo (P.PM ++ P.Pq))
      (fun v => {z | ((⌊z⌋ : ℤ) : ZMod P.M) = v.1} ∩ Int.fract ⁻¹' ival (cells P.D v.2)) :=
  cover_affine (by have := hF.q1; omega) (by have := hF.q1; have := hF.pq; omega) hF.D0
    (hPM_of hF) (hPq_of hF)

/-- **`divisor_set_of_checked`, re-derived**: through `checked_allPer`, the affine cover and the
generic divisor theorem. -/
@[category research solved, AMS 11 37, ref "DN05", group "carry_bridge_dubc2"]
theorem divisor_set_of_checked' {C : Cert} (hc : Checked P C) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ ((P.a : ℝ) / P.b) n := by
  have hF := paramFacts_of_checked hc
  have : NeZero P.M := ⟨hF.M0.ne'⟩
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hν : (P.b : ℝ) * ((nuQ P : ℚ) : ℝ) = P.a := by rw [nuQ_cast]; field_simp
  have h := frequently_not_avoid_of_allPer hF.q1 hF.pq hF.cop (cover_genGraph hF)
    (fun z => affine_rho_cover hF.D0 z) (window hF hν.ge hν.le hF.sLo hF.sHi)
    (checked_allPer hc) hξ
  rw [nuQ_cast] at h
  refine h.mono fun n hn => ?_
  simp only [Avoid] at hn
  push Not at hn
  exact hn

/-! ### The mirror `ν ↦ 1 − ν` -/

/-- The carry window at the mirror shift `1 − a/b` is the reversed window. -/
@[category API, AMS 11, group "carry_bridge_dubc2"]
theorem window_mirror (hF : ParamFacts P) (z : ℝ) :
    -(P.sLo + P.nA - 1) ≤ carry P.p P.q (1 - (P.a : ℝ) / P.b) z ∧
      carry P.p P.q (1 - (P.a : ℝ) / P.b) z < -(P.sLo + P.nA - 1) + P.nA := by
  have hq : P.q ≠ 0 := by have := hF.q1; omega
  have hp : 0 < P.p := by have := hF.q1; have := hF.pq; omega
  obtain ⟨c1, c2⟩ := carry_bounds (p := P.p) (ν := 1 - (P.a : ℝ) / P.b) hq hp z
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hlo : (P.b : ℝ) * (P.sLo - 1) ≤ -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * P.a := by
    exact_mod_cast hF.sLo
  have hhi : (P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * P.a ≤ (P.b : ℝ) * (P.sLo + P.nA) := by
    exact_mod_cast hF.sHi
  have e1 : (P.b : ℝ) * (-(P.q : ℝ) - ((P.p : ℝ) - P.q) * (1 - (P.a : ℝ) / P.b))
      = -(P.p : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a := by field_simp; ring
  have e2 : (P.b : ℝ) * ((P.p : ℝ) - ((P.p : ℝ) - P.q) * (1 - (P.a : ℝ) / P.b))
      = (P.q : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a := by field_simp; ring
  set c := carry P.p P.q (1 - (P.a : ℝ) / P.b) z
  constructor
  · have h1 : (P.b : ℝ) * (-(P.sLo + P.nA : ℤ) : ℤ) < P.b * c := by
      push_cast; nlinarith [mul_lt_mul_of_pos_left c1 hb]
    have := Int.cast_lt.1 (lt_of_mul_lt_mul_left h1 hb.le)
    omega
  · have h1 : (P.b : ℝ) * c < P.b * ((1 - P.sLo : ℤ) : ℝ) := by
      push_cast; nlinarith [mul_lt_mul_of_pos_left c2 hb]
    have := Int.cast_lt.1 (lt_of_mul_lt_mul_left h1 hb.le)
    omega

/-- **A checked certificate is also a theorem at the mirror shift `1 − a/b`**
(`DubC2.Mirror.divisor_set_mirror_of_checked`), re-derived from carry graphs alone: the affine
graph at `1 − a/b` with the reversed letter window is the mirror image of the certified one
(`allPer_affine_mirror_iff`), it covers the system at `1 − a/b` (`cover_affine`), and the generic
divisor theorem applies.  No orbit-level mirror and no count of integer hits is needed. -/
@[category research solved, AMS 11 37, ref "DN05", group "carry_bridge_dubc2"]
theorem divisor_set_mirror_of_checked' {C : Cert} (hc : Checked P C) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ (1 - (P.a : ℝ) / P.b) n := by
  have hF := paramFacts_of_checked hc
  have : NeZero P.M := ⟨hF.M0.ne'⟩
  have hX : (affine P.p P.q (1 - nuQ P) (-(P.sLo + P.nA - 1)) P.nA P.M P.D P.PM P.Pq).AllPer :=
    (allPer_affine_mirror_iff fun l hl => (hPM_of hF l hl).1).2 (checked_allPer hc)
  have hcov := cover_affine (p := P.p) (q := P.q) (νq := 1 - nuQ P) (s₀ := -(P.sLo + P.nA - 1))
    (nA := P.nA) (by have := hF.q1; omega) (by have := hF.q1; have := hF.pq; omega) hF.D0
    (hPM_of hF) (hPq_of hF)
  have hcast : (((1 - nuQ P : ℚ)) : ℝ) = 1 - (P.a : ℝ) / P.b := by
    push_cast [nuQ_cast]; rfl
  rw [hcast] at hcov
  have h := frequently_not_avoid_of_allPer hF.q1 hF.pq hF.cop hcov
    (fun z => affine_rho_cover hF.D0 z) (window_mirror hF) hX hξ
  refine h.mono fun n hn => ?_
  simp only [Avoid] at hn
  push Not at hn
  exact hn

/-! ### Parameter intervals -/

/-- **The hull check is a homomorphism**: `hullOK P a₀ a₁` says that the cell hull over
`[a₀/b, a₁/b]` maps into the cell graph at `a/b` by the identity. -/
def cellHullHom (hF : ParamFacts P) {a₀ a₁ : ℤ} (hh : hullOK P a₀ a₁ = true) :
    Hom (cellHull P.p P.q ((a₀ : ℚ) / P.b) ((a₁ : ℚ) / P.b) P.sLo P.nA P.D)
      (cellGraph P.p P.q (nuQ P) P.sLo P.nA P.D) :=
  ⟨id, fun {c t c₂} h => by
    have hq : 0 < P.q := by have := hF.q1; omega
    obtain ⟨-, -, hs⟩ := hullOK_spec hq hF.b0 hh
    refine (cellArc_iff hF).2 (hs c c.2 t t.2 c₂ c₂.2 ?_)
    obtain ⟨h1, h2, -⟩ := adj_blockHull.1 h
    simp only [cells] at h1 h2
    have hb : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
    have hD : (0 : ℚ) < P.D := by exact_mod_cast hF.D0
    have hbD : (0 : ℚ) < P.b * P.D := by positivity
    have d1 : (P.p : ℚ) * ((((c : ℕ) : ℚ) + 1) / P.D) - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ)
        - P.q * (((c₂ : ℕ) : ℚ) / P.D) - ((P.p : ℚ) - P.q) * ((a₀ : ℚ) / P.b)
        = ((P.hiAt a₀ c (P.letter t) - P.q * P.b * (c₂ : ℕ) : ℤ) : ℚ) / (P.b * P.D) := by
      simp only [Params.hiAt, Params.letter]
      push_cast
      field_simp
      ring
    have d2 : ((P.p : ℚ) - P.q) * ((a₁ : ℚ) / P.b) - ((P.p : ℚ) * (((c : ℕ) : ℚ) / P.D)
        - ((P.sLo + ((t : ℕ) : ℤ) : ℤ) : ℚ) - P.q * ((((c₂ : ℕ) : ℚ) + 1) / P.D))
        = ((P.q * P.b * ((c₂ : ℕ) + 1) - P.loAt a₁ c (P.letter t) : ℤ) : ℚ) / (P.b * P.D) := by
      simp only [Params.loAt, Params.letter]
      push_cast
      field_simp
      ring
    have k1 := sub_pos.2 h1
    have k2 := sub_pos.2 h2
    rw [d1, div_pos_iff_of_pos_right hbD, Int.cast_pos, sub_pos] at k1
    rw [d2, div_pos_iff_of_pos_right hbD, Int.cast_pos, sub_pos] at k2
    simp only [Params.hullEdge, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨k1, k2⟩⟩

/-- The affine hull over `[a₀/b, a₁/b]` maps into `genGraph P` when the hull check passes. -/
def hullHom (hF : ParamFacts P) [NeZero P.M] {a₀ a₁ : ℤ} (hh : hullOK P a₀ a₁ = true) :
    Hom (affineHull P.p P.q ((a₀ : ℚ) / P.b) ((a₁ : ℚ) / P.b) P.sLo P.nA P.M P.D P.PM P.Pq)
      (genGraph P) :=
  (Hom.id _).prodMap (cellHullHom hF hh)

/-- **`divisor_set_of_checked_hull`, re-derived**: a checked cell with a passing hull check
proves the divisor statement for every real shift in `[a₀/b, a₁/b]`. -/
@[category research solved, AMS 11 37, ref "DN05", group "carry_bridge_dubc2"]
theorem divisor_set_of_checked_hull' {C : Cert} (hc : Checked P C) {a₀ a₁ : ℤ}
    (hh : hullOK P a₀ a₁ = true) {ν : ℝ} (hν₀ : (a₀ : ℝ) / P.b ≤ ν) (hν₁ : ν ≤ (a₁ : ℝ) / P.b)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ ν n := by
  have hF := paramFacts_of_checked hc
  have : NeZero P.M := ⟨hF.M0.ne'⟩
  have hq : 0 < P.q := by have := hF.q1; omega
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  obtain ⟨hlo, hhi, -⟩ := hullOK_spec hq hF.b0 hh
  have h₀ : (a₀ : ℝ) ≤ P.b * ν := by rw [div_le_iff₀ hb] at hν₀; linarith
  have h₁ : (P.b : ℝ) * ν ≤ a₁ := by rw [le_div_iff₀ hb] at hν₁; linarith
  have hcov := cover_affineHull (ν₀ := (a₀ : ℚ) / P.b) (ν₁ := (a₁ : ℚ) / P.b) (s₀ := P.sLo)
    (nA := P.nA) hq.ne' hF.pq.le (hq.trans hF.pq) (by push_cast; exact hν₀)
    (by push_cast; exact hν₁) hF.D0 (hPM_of hF) (hPq_of hF)
  have h := frequently_not_avoid_of_allPer hF.q1 hF.pq hF.cop hcov
    (fun z => affine_rho_cover hF.D0 z) (window hF h₀ h₁ hlo hhi)
    (allPer_of_hom (hullHom hF hh) (checked_allPer hc)) hξ
  refine h.mono fun n hn => ?_
  simp only [Avoid] at hn
  push Not at hn
  exact hn

/-! ### Entropy certificates -/

/-- **The automaton of an entropy certificate**, as a carry graph on its states. -/
def entGraph (E : EntCert) (P : Params) : CarryGraph (Fin E.sets.length) (Fin P.nA) :=
  ofRel fun i t j => E.tr i t = some (j : ℕ)

/-- The states of an entropy certificate simulate the affine graph of its cell. -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem entGraph_simulation {E : EntCert} (hE : E.Facts P) [NeZero P.M] :
    IsSimulation (genGraph P) (entGraph E P) fun v i => E.mem i (enc P v) = true := by
  have hF : ParamFacts P := paramFacts hE.par
  intro v i hv t v' h
  obtain ⟨j, hj, hm⟩ := hE.close i i.2 t t.2 _ (enc P v).2 hv _ (mem_succList hF h)
  exact ⟨⟨j, hE.trans i i.2 t t.2 j hj⟩, adj_ofRel.2 hj, hm⟩

/-- **The weights of an entropy certificate are a super-eigenvector** of its automaton. -/
@[category API, AMS 11 05, group "carry_bridge_dubc2"]
theorem entGraph_superEigen {E : EntCert} (hE : E.Facts P) :
    (entGraph E P).IsSuperEigen (fun i => E.wt i) E.a E.b := by
  refine ⟨fun i => hE.w0 i i.2, fun i => ?_⟩
  have hsum : ∑ x ∈ (entGraph E P).arcsFrom i, E.wt x.2 = E.wsum P i := by
    rw [arcsFrom, Finset.sum_sigma, EntCert.wsum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [EntCert.wopt]
    rcases ht : E.tr i t with _ | j
    · refine Finset.sum_eq_zero fun k hk => ?_
      have := adj_ofRel.1 hk
      rw [ht] at this
      exact absurd this (by simp)
    · have hj : j < E.sets.length := hE.trans i i.2 t t.2 j ht
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · rfl
      · intro k hk hne
        have := adj_ofRel.1 hk
        rw [ht, Option.some.injEq] at this
        exact absurd (Fin.ext this.symm) hne
      · intro hn
        exact absurd (adj_ofRel.2 (by rw [ht])) hn
  rw [hsum]
  exact hE.cw i i.2

/-! ### The follower automaton (gate G-3) -/

section Follower

open DubC2.Gen.Follower

/-- **The follower automaton as a carry graph**: states `FState` (infinitely many in general,
`DubC2.Gen.Follower.triv32_infinite`), letters `Fin nA`, one arc per live step. -/
def folGraph (P : Params) : CarryGraph FState (Fin P.nA) :=
  ⟨fun X t => (step P X (P.letter t)).toFinset⟩

@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem adj_folGraph {X Y : FState} {t : Fin P.nA} :
    (folGraph P).Adj X t Y ↔ step P X (P.letter t) = some Y := by
  simp [folGraph, Adj, Option.mem_def]

/-- The follower automaton is right-resolving. -/
@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem folGraph_rightResolving : (folGraph P).RightResolving := fun X t => by
  simp only [folGraph]
  cases step P X (P.letter t) <;> simp

/-- From a valid state every live letter lies in the window: this is the only arithmetic input
of the dictionary. -/
@[category API, AMS 11 37, group "carry_bridge_dubc2"]
theorem exists_letter (hF : ParamFacts P) {X Y : FState} (hX : Valid X) {s : ℤ}
    (h : step P X s = some Y) : ∃ t : Fin P.nA, P.letter t = s := by
  have hsa := letter_mem hF hX h
  simp only [alph, Finset.mem_image, Finset.mem_range] at hsa
  obtain ⟨t, ht, rfl⟩ := hsa
  exact ⟨⟨t, ht⟩, rfl⟩

/-- **Reachability is the follower automaton's** (from a valid state). -/
@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem reach_folGraph_iff (hF : ParamFacts P) {X Y : FState} (hX : Valid X) :
    (folGraph P).Reach X Y ↔ Follower.Reach P X Y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      obtain ⟨t, ht⟩ := hbc
      exact ih.tail ⟨_, adj_folGraph.1 ht⟩
  · intro h
    have key : ∀ Y, Follower.Reach P X Y → (folGraph P).Reach X Y ∧ Valid Y := by
      intro Y h
      induction h with
      | refl => exact ⟨Relation.ReflTransGen.refl, hX⟩
      | tail _ hbc ih =>
        obtain ⟨s, hs⟩ := hbc
        obtain ⟨t, rfl⟩ := exists_letter hF ih.2 hs
        exact ⟨ih.1.tail ⟨t, adj_folGraph.2 hs⟩, valid_of_step hs⟩
    exact (key Y h).1

/-- **A branching state is labelled branching** in the follower carry graph. -/
@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem branching_iff (hF : ParamFacts P) {X : FState} (hX : Valid X) :
    Branching P X ↔ ∃ a b Y Z, (folGraph P).Adj X a Y ∧ (folGraph P).Adj X b Z ∧
      (folGraph P).Reach Y X ∧ (folGraph P).Reach Z X ∧ a ≠ b := by
  constructor
  · rintro ⟨s₁, s₂, Y₁, Y₂, hne, h1, h2, r1, r2⟩
    obtain ⟨a, rfl⟩ := exists_letter hF hX h1
    obtain ⟨b, rfl⟩ := exists_letter hF hX h2
    exact ⟨a, b, Y₁, Y₂, adj_folGraph.2 h1, adj_folGraph.2 h2,
      (reach_folGraph_iff hF (valid_of_step h1)).2 r1,
      (reach_folGraph_iff hF (valid_of_step h2)).2 r2, fun h => hne (h ▸ rfl)⟩
  · rintro ⟨a, b, Y, Z, h1, h2, r1, r2, hne⟩
    have h1' := adj_folGraph.1 h1
    have h2' := adj_folGraph.1 h2
    refine ⟨_, _, Y, Z, fun h => hne (Fin.ext ?_), h1', h2',
      (reach_folGraph_iff hF (valid_of_step h1')).1 r1,
      (reach_folGraph_iff hF (valid_of_step h2')).1 r2⟩
    simpa [Params.letter] using h

/-- **`exists_injective_path`, re-derived** from the generic geodesic Kőnig lemma
`exists_injective_walk_of_infinite_reach`: no arithmetic beyond the letter window. -/
@[category research solved, AMS 11 37 05, ref "BJG09", group "carry_bridge_dubc2"]
theorem exists_injective_path' (hF : ParamFacts P)
    (hinf : ¬ {X | Follower.Reach P (root P) X}.Finite) :
    ∃ (s : ℕ → ℤ) (X : ℕ → FState), X 0 = root P ∧
      (∀ n, step P (X n) (s n) = some (X (n + 1))) ∧ Function.Injective X := by
  classical
  have hinf' : {Y | (folGraph P).Reach (root P) Y}.Infinite := by
    have : {Y | (folGraph P).Reach (root P) Y} = {X | Follower.Reach P (root P) X} := by
      ext Y
      exact reach_folGraph_iff hF valid_root
    rw [this]
    exact hinf
  obtain ⟨X, hX0, hX, -, hinj⟩ := exists_injective_walk_of_infinite_reach hinf'
  choose t ht using hX
  exact ⟨fun n => P.letter (t n), X, hX0, fun n => adj_folGraph.1 (ht n), hinj⟩

/-- **`finite_of_checked`, re-derived**: the generic Kőnig half (`exists_injective_path'`) and
the one arithmetic lemma `not_injective_of_periodic` (a periodic letter sequence cannot drive an
injective follower path). -/
@[category research solved, AMS 11 37, ref "Oda26", group "carry_bridge_dubc2"]
theorem finite_of_checked' {C : Cert} (hc : Checked P C) :
    {X | Follower.Reach P (root P) X}.Finite := by
  have hF := paramFacts_of_checked hc
  by_contra hinf
  obtain ⟨s, X, h0, hX, hinj⟩ := exists_injective_path' hF hinf
  have hs : ∀ m, stepw P (root P) (DubC2.Gen.Follower.pre s m) = some (X m) := by
    intro m
    induction m with
    | zero => rw [h0]; rfl
    | succ m ih => rw [stepw_pre_succ, ih]; exact hX m
  exact not_injective_of_periodic hF h0 hX
    (eventuallyPeriodic_of_checked hc s fun m => by rw [hs]; rfl) hinj

/-- **T5(iv) in carry-graph form**: some cell count certifies iff the follower carry graph has
finitely many vertices reachable from the root and no labelled branching among them. -/
@[category research solved, AMS 11 37 05, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem checked_iff_finite' (hP : checkParams P = true) :
    (∃ D C, Checked { P with D := D } C) ↔
      {Y | (folGraph P).Reach (root P) Y}.Finite ∧
        ∀ X, (folGraph P).Reach (root P) X → ∀ a b Y Z, (folGraph P).Adj X a Y →
          (folGraph P).Adj X b Z → (folGraph P).Reach Y X → (folGraph P).Reach Z X →
            a = b ∧ Y = Z := by
  have hF := paramFacts hP
  have hset : {Y | (folGraph P).Reach (root P) Y} = {X | Follower.Reach P (root P) X} := by
    ext Y
    exact reach_folGraph_iff hF valid_root
  rw [hset]
  constructor
  · rintro ⟨D, C, hc⟩
    refine ⟨finite_of_checked' (P := { P with D := D }) hc, fun X hX a b Y Z h1 h2 r1 r2 => ?_⟩
    have hX' := (reach_folGraph_iff hF valid_root).1 hX
    by_cases hab : a = b
    · subst hab
      exact ⟨rfl, folGraph_rightResolving.eq h1 h2⟩
    · exact absurd hc (not_checked_of_branching (P := { P with D := D })
        ((branching_iff hF (valid_of_reach hX')).2 ⟨a, b, Y, Z, h1, h2, r1, r2, hab⟩))
  · rintro ⟨hfin, hnb⟩
    refine ⟨_, exists_checked_DF hP hfin fun X hX hb => ?_⟩
    obtain ⟨a, b, Y, Z, h1, h2, r1, r2, hab⟩ := (branching_iff hF (valid_of_reach hX)).1 hb
    exact hab (hnb X ((reach_folGraph_iff hF valid_root).2 hX) a b Y Z h1 h2 r1 r2).1

/-! #### The follower check as a labelled rank -/

/-- The states reachable from the root. -/
def reachSetF (P : Params) : Set FState := {X | Follower.Reach P (root P) X}

open Classical in
/-- **The follower check is a labelled rank** (`checkF_imp_isRank`): the least tree label of a
state is a labelled rank of the follower automaton on the states reachable from the root. -/
@[category research solved, AMS 11 37 05, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem checkF_isLRank {Q : ℕ} {T : LTree} (hc : checkF P Q T = true) :
    ((folGraph P).restrict (reachSetF P)).IsLRank (labF P Q T) := by
  obtain ⟨hP, -, -, -, hall⟩ := checkF_facts hc
  have hF := paramFacts hP
  refine ⟨fun X a Y h => ?_, fun X a b Y Z hY hZ h1 h2 => ?_⟩
  · obtain ⟨hX, hXY, -⟩ := adj_restrict.1 h
    exact labF_step hc hX (adj_folGraph.1 hXY)
  · obtain ⟨hX, hXY, hYr⟩ := adj_restrict.1 hY
    obtain ⟨-, hXZ, hZr⟩ := adj_restrict.1 hZ
    obtain ⟨k, hk, hkX⟩ := labF_mem hc hX
    have key : ∀ {t : Fin P.nA} {W : FState}, step P X (P.letter t) = some W →
        W ∈ reachSetF P → labF P Q T W = labF P Q T X →
        aedge P Q T k (P.letter t) = some (some (labF P Q T X)) := by
      intro t W hs hW hl
      obtain ⟨t', -, ht', k', lab', he, hk', hW', hle⟩ :=
        edge_rep hc hk hkX (valid_of_reach hX) hs
      have h2 := labF_le hk' hW'
      rw [he]
      congr
      omega
    have e1 := key (adj_folGraph.1 hXY) hYr h1
    have e2 := key (adj_folGraph.1 hXZ) hZr h2
    have hn := (LTree.find_spec hk).2 _ hall
    simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at hn
    have hm : ∀ t : Fin P.nA, aedge P Q T k (P.letter t) = some (some (labF P Q T X)) →
        (t : ℕ) ∈ (List.range P.nA).filter fun t =>
          aedge P Q T k (P.letter t) == some (some (labF P Q T X)) := fun t he => by
      simp [t.2, he]
    have hab : a = b := Fin.ext (eq_of_length_le_one hn.2 (hm a e1) (hm b e2))
    subst hab
    exact ⟨rfl, folGraph_rightResolving.eq hXY hXZ⟩

/-- **No reachable state branches** (`not_branching_of_checkF`), re-derived from the labelled
rank (`IsLRank.lnoBranch`). -/
@[category research solved, AMS 11 37 05, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem not_branching_of_checkF' {Q : ℕ} {T : LTree} (hc : checkF P Q T = true) {X : FState}
    (hX : Follower.Reach P (root P) X) : ¬ Branching P X := by
  classical
  obtain ⟨hP, -, -, -, -⟩ := checkF_facts hc
  have hF := paramFacts hP
  intro hb
  obtain ⟨a, b, Y, Z, h1, h2, r1, r2, hab⟩ := (branching_iff hF (valid_of_reach hX)).1 hb
  have hclosed : ∀ U ∈ reachSetF P, ∀ W, (folGraph P).under U W → W ∈ reachSetF P := by
    rintro U hU W ⟨t, ht⟩
    exact Relation.ReflTransGen.tail hU ⟨_, adj_folGraph.1 ht⟩
  have hY : Y ∈ reachSetF P := hclosed X hX Y ⟨a, h1⟩
  have hZ : Z ∈ reachSetF P := hclosed X hX Z ⟨b, h2⟩
  have hl := (checkF_isLRank hc).lnoBranch X a b Y Z (adj_restrict.2 ⟨hX, h1, hY⟩)
    (adj_restrict.2 ⟨hX, h2, hZ⟩) (r1.restrict hclosed hY) (r2.restrict hclosed hZ)
  exact hab hl.1

/-- **A passed follower check gives a certificate at some cell count**
(`exists_checked_of_checkF` without fixing `D = Q`), re-derived: finiteness from the tree, no
branching from the labelled rank, then `checked_iff_finite'`. -/
@[category research solved, AMS 11 37 05, ref "Oda26", group "carry_bridge_dubc2"]
theorem exists_checked_of_checkF' {Q : ℕ} {T : LTree} (hc : checkF P Q T = true) :
    ∃ D C, Checked { P with D := D } C := by
  obtain ⟨hP, -, -, -, -⟩ := checkF_facts hc
  have hF := paramFacts hP
  have hset : {Y | (folGraph P).Reach (root P) Y} = {X | Follower.Reach P (root P) X} := by
    ext Y
    exact reach_folGraph_iff hF valid_root
  refine (checked_iff_finite' hP).2 ⟨hset ▸ (checkF_sound hc).1, fun X hX a b Y Z h1 h2 r1 r2 => ?_⟩
  have hX' := (reach_folGraph_iff hF valid_root).1 hX
  by_cases hab : a = b
  · subst hab
    exact ⟨rfl, folGraph_rightResolving.eq h1 h2⟩
  · exact absurd ((branching_iff hF (valid_of_reach hX')).2 ⟨a, b, Y, Z, h1, h2, r1, r2, hab⟩)
      (not_branching_of_checkF' hc hX')

end Follower

/-! ### The avoiding language -/

section Avoid

open DubC2.Gen.Follower DubC2.Gen.Horse

/-- The follower automaton with integer letters (no window). -/
def folGraphZ (P : Params) : CarryGraph FState ℤ := ⟨fun X s => (step P X s).toFinset⟩

@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem adj_folGraphZ {X Y : FState} {s : ℤ} : (folGraphZ P).Adj X s Y ↔ step P X s = some Y := by
  simp [folGraphZ, Adj, Option.mem_def]

@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem reach_folGraphZ_iff {X Y : FState} : (folGraphZ P).Reach X Y ↔ Follower.Reach P X Y := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨s, hs⟩ := hbc
      exact ih.tail ⟨s, adj_folGraphZ.1 hs⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨s, hs⟩ := hbc
      exact ih.tail ⟨s, adj_folGraphZ.2 hs⟩

/-- **The avoiding pseudo-orbit language** of a cell: the language of the follower carry graph
from the root. -/
def avoidLang (P : Params) : Language ℤ := (folGraphZ P).langFrom (root P)

@[category API, AMS 11 37 05, group "carry_bridge_dubc2"]
theorem mem_avoidLang {w : List ℤ} : w ∈ avoidLang P ↔ (stepw P (root P) w).isSome := by
  have key : ∀ (w : List ℤ) (X : FState), (folGraphZ P).IsWord X w ↔ (stepw P X w).isSome := by
    intro w
    induction w with
    | nil => exact fun X => ⟨fun _ => rfl, fun _ => isWord_nil _⟩
    | cons s w ih =>
      intro X
      rw [isWord_cons]
      simp only [stepw]
      constructor
      · rintro ⟨Y, hY, hw⟩
        rw [adj_folGraphZ.1 hY]
        exact (ih Y).1 hw
      · intro h
        cases hs : step P X s with
        | none => rw [hs] at h; simp at h
        | some Y =>
          rw [hs] at h
          exact ⟨Y, adj_folGraphZ.2 hs, (ih Y).2 (by simpa using h)⟩
  exact key w _

/-- **A certified cell has a sofic avoiding language** (`finite_of_checked'` and the generic
`sofic_of_finite_reach`). -/
@[category research solved, AMS 11 37 05, ref "LM95" "Oda26", group "carry_bridge_dubc2"]
theorem sofic_of_checked {C : Cert} (hc : Checked P C) : Sofic (avoidLang P) := by
  refine sofic_of_finite_reach ?_
  have : {Y | (folGraphZ P).Reach (root P) Y} = {X | Follower.Reach P (root P) X} := by
    ext Y
    exact reach_folGraphZ_iff
  rw [this]
  exact finite_of_checked' hc

/-! #### Monotonicity in the divisor set: a simulation -/

section Mono

variable {P' : Params}

/-- The residue steps of two parameter records with the same `p, q` agree mod every common prime
of their `PM`s, from residues that agree mod it. -/
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem rnext_mod_eq (hF : ParamFacts P) (hF' : ParamFacts P') (hp : P'.p = P.p) (hq : P'.q = P.q)
    {l : ℕ} (hl : l ∈ P.PM) (hl' : l ∈ P'.PM) {r r' : ℕ} (h : r % l = r' % l) (s : ℤ) :
    P.rnext r s % l = P'.rnext r' s % l := by
  have hlM : l ∣ P.M := Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have hlM' : l ∣ P'.M := Nat.dvd_of_mod_eq_zero (hF'.PM l hl')
  rcases Nat.lt_or_ge l 2 with hl2 | hl2
  · obtain _ | _ | l := l
    · have := hF.M0
      rw [Nat.zero_dvd] at hlM
      omega
    · simp only [zero_add, Nat.mod_one]
    · omega
  have A := rnext_modEq hF hl2 (by exact_mod_cast hlM) (invMod_spec hF hl2 hlM) (x := r)
    (ρ := r % l) s (by rw [Int.ModEq]; push_cast; rw [Int.emod_emod])
  have B := rnext_modEq hF' hl2 (by exact_mod_cast hlM') (invMod_spec hF' hl2 hlM') (x := r')
    (ρ := r % l) s (by rw [Int.ModEq, h]; push_cast; rw [Int.emod_emod])
  rw [hp, hq] at B
  have := A.trans B.symm
  rw [Int.ModEq] at this
  exact_mod_cast this

/-- `X` shadows `X'`: same interval, and every residue of `X'` has a partner in `X` agreeing
mod every prime of `P.PM`. -/
def Shadow (P : Params) (X' X : FState) : Prop :=
  X'.lo = X.lo ∧ X'.hi = X.hi ∧ ∀ r' ∈ X'.R, ∃ r ∈ X.R, ∀ l ∈ P.PM, r % l = r' % l

variable (hF : ParamFacts P) (hF' : ParamFacts P') (hp : P'.p = P.p) (hq : P'.q = P.q)
  (ha : P'.a = P.a) (hb : P'.b = P.b) (hPM : ∀ l ∈ P.PM, l ∈ P'.PM)
  (hPq : ∀ l ∈ P.Pq, l ∈ P'.Pq)
include hF hF' hp hq hPM

omit hF' hp hq hPM in
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem shadow_root : Shadow P (root P') (root P) := by
  refine ⟨rfl, rfl, fun r' _ => ⟨r' % P.M, Finset.mem_range.2 (Nat.mod_lt _ hF.M0), fun l hl => ?_⟩⟩
  exact Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero (hF.PM l hl))

include ha hb hPq in
/-- **Shadowing is a simulation** of the follower carry graph of `P'` by that of `P`. -/
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem shadow_isSimulation :
    IsSimulation (folGraphZ P') (folGraphZ P) (fun X' X => Shadow P X' X) := by
  intro X' X hX s Y' h
  rw [adj_folGraphZ] at h
  obtain ⟨hlo, hhi, hR⟩ := hX
  have hres : ∀ y' ∈ rstep P' X'.R s, ∃ y ∈ rstep P X.R s, ∀ l ∈ P.PM, y % l = y' % l := by
    intro y' hy'
    simp only [rstep, Finset.mem_image, Finset.mem_filter] at hy' ⊢
    obtain ⟨r', ⟨hr', hok'⟩, rfl⟩ := hy'
    obtain ⟨r, hr, hrl⟩ := hR r' hr'
    simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hok'
    have hnext : ∀ l ∈ P.PM, P.rnext r s % l = P'.rnext r' s % l := fun l hl =>
      rnext_mod_eq hF hF' hp hq hl (hPM l hl) (hrl l hl) s
    refine ⟨P.rnext r s, ⟨r, ⟨hr, ?_⟩, rfl⟩, hnext⟩
    simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun l hl => hrl l hl ▸ hok'.1 l (hPM l hl),
      fun l hl => hnext l hl ▸ hok'.2 l (hPM l hl)⟩
  have hI : istepX P' X' s = istepX P X s := by
    simp only [istepX, hp, hq, ha, hb, hlo, hhi]
  unfold step at h
  split_ifs at h with hc
  obtain ⟨hs, ⟨y', hy'⟩, hint⟩ := hc
  cases h
  obtain ⟨y, hy, -⟩ := hres y' hy'
  have hs' : sOK P s = true := by
    simp only [sOK, List.all_eq_true, bne_iff_ne, ne_eq] at hs ⊢
    exact fun l hl => hs l (hPq l hl)
  refine ⟨_, adj_folGraphZ.2 (ite_eq_left ⟨hs', ⟨y, hy⟩, hI ▸ hint⟩), ?_⟩
  exact ⟨congrArg Prod.fst hI, congrArg Prod.snd hI, hres⟩

include ha hb hPq in
/-- **`avoidLang_mono`, re-derived from the simulation**: more primes, same map, smaller avoiding
language; no relation between the moduli is needed. -/
@[category research solved, AMS 05 11 37, ref "LM95", group "carry_bridge_dubc2"]
theorem avoidLang_mono' : ∀ w, w ∈ avoidLang P' → w ∈ avoidLang P :=
  fun w hw => (shadow_isSimulation hF hF' hp hq ha hb hPM hPq).langFrom_subset
    (shadow_root (P' := P') hF) w hw

end Mono

end Avoid

/-! ### The residue automaton as an indexed label product -/

section Residue

open DubC2.Gen.Follower DubC2.Gen.Horse

/-- The primes of `PM`, as a finite index type. -/
instance pmFintype (P : Params) : Fintype {l // l ∈ P.PM} :=
  Fintype.subtype P.PM.toFinset fun _ => List.mem_toFinset

/-- The residue part of the follower automaton: `r → rnext r s` when `r < M` survives `s`. -/
def resGraph (P : Params) : CarryGraph ℕ ℤ :=
  ⟨fun r s => if r < P.M ∧ rOK P r s = true then {P.rnext r s} else ∅⟩

/-- The per-prime residue automaton mod `l` (`DubC2/xfrontier.py`, `Follower.mstep`). -/
def primeGraph (P : Params) (l : ℕ) : CarryGraph ℕ ℤ :=
  ⟨fun ρ s => if ρ < l ∧ ρ ≠ 0 ∧ stepMod P.p l (invMod P.q l) ρ s ≠ 0 then
    {stepMod P.p l (invMod P.q l) ρ s} else ∅⟩

@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem adj_resGraph {r r' : ℕ} {s : ℤ} :
    (resGraph P).Adj r s r' ↔ r < P.M ∧ rOK P r s = true ∧ r' = P.rnext r s := by
  simp only [resGraph, Adj]
  split_ifs with h <;> simp_all

@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem adj_primeGraph {l ρ ρ' : ℕ} {s : ℤ} :
    (primeGraph P l).Adj ρ s ρ' ↔ ρ < l ∧ ρ ≠ 0 ∧ stepMod P.p l (invMod P.q l) ρ s ≠ 0 ∧
      ρ' = stepMod P.p l (invMod P.q l) ρ s := by
  simp only [primeGraph, Adj]
  split_ifs with h <;> simp_all

/-- The Chinese remainder map `r ↦ (r mod l)_{l ∈ PM}`. -/
def crt (P : Params) (r : ℕ) : ∀ _ : {l // l ∈ P.PM}, ℕ := fun l => r % l

/-- **The residue automaton is the indexed label product of the per-prime automata**, read
through the Chinese remainder map. -/
@[category research solved, AMS 05 11 37, ref "LM95", group "carry_bridge_dubc2"]
theorem adj_resGraph_iff_piProduct (hF : ParamFacts P) (hC : CRTFacts P) {r r' : ℕ}
    (hr : r < P.M) (hr' : r' < P.M) (s : ℤ) :
    (resGraph P).Adj r s r' ↔
      (piProduct fun l : {l // l ∈ P.PM} => primeGraph P l).Adj (crt P r) s (crt P r') := by
  rw [adj_resGraph, adj_piProduct]
  simp only [adj_primeGraph, rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, crt,
    Subtype.forall]
  constructor
  · rintro ⟨-, ⟨h0, h1⟩, rfl⟩ l hl
    have hl2 := hC.two l hl
    refine ⟨Nat.mod_lt _ (by omega), h0 l hl, ?_, rnext_mod hF hC hl r s⟩
    rw [← rnext_mod hF hC hl]
    exact h1 l hl
  · intro h
    refine ⟨hr, ⟨fun l hl => (h l hl).2.1, fun l hl => ?_⟩,
      eq_of_mod_eq hC hr' (rnext_lt hF r s) fun l hl => ?_⟩
    · rw [rnext_mod hF hC hl]; exact (h l hl).2.2.1
    · rw [rnext_mod hF hC hl]; exact (h l hl).2.2.2

/-- The residue step of the follower automaton is the subset step of `resGraph`. -/
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem rstep_eq_detStep (R : Finset ℕ) (hR : ∀ r ∈ R, r < P.M) (s : ℤ) :
    rstep P R s = (resGraph P).detStep R s := by
  ext r'
  simp only [rstep, Finset.mem_image, Finset.mem_filter, mem_detStep, adj_resGraph]
  constructor
  · rintro ⟨r, ⟨hr, hok⟩, rfl⟩
    exact ⟨r, hr, hR r hr, hok, rfl⟩
  · rintro ⟨r, hr, -, hok, rfl⟩
    exact ⟨r, ⟨hr, hok⟩, rfl⟩

/-- The product of per-prime residue sets, as a set of residues mod `M`. -/
def prodSet (P : Params) (S : {l // l ∈ P.PM} → Set ℕ) : Set ℕ :=
  {r | r < P.M ∧ ∀ l, r % l.1 ∈ S l}

/-- **A residue step maps product sets to product sets**, factor by factor: the subset step of
the indexed product (`detStep_piProduct`) transported along the Chinese remainder map. -/
@[category research solved, AMS 05 11 37, ref "LM95", group "carry_bridge_dubc2"]
theorem rstep_prodSet (hF : ParamFacts P) (hC : CRTFacts P) (R : Finset ℕ)
    {S : {l // l ∈ P.PM} → Set ℕ} (hR : (↑R : Set ℕ) = prodSet P S) (s : ℤ) :
    (↑(rstep P R s) : Set ℕ) =
      prodSet P fun l => {y | ∃ x ∈ S l, (primeGraph P l).Adj x s y} := by
  classical
  have hR' : ∀ r ∈ R, r < P.M := fun r h => by
    have : r ∈ (↑R : Set ℕ) := h
    rw [hR] at this
    exact this.1
  rw [rstep_eq_detStep R hR' s]
  ext r'
  simp only [Finset.mem_coe, mem_detStep]
  constructor
  · rintro ⟨r, hr, hE⟩
    have hrM := hR' r hr
    have hr'M : r' < P.M := (adj_resGraph.1 hE).2.2 ▸ rnext_lt hF r s
    have hrS : r ∈ prodSet P S := hR ▸ hr
    have hπ := adj_piProduct.1 ((adj_resGraph_iff_piProduct hF hC hrM hr'M s).1 hE)
    exact ⟨hr'M, fun l => ⟨r % l.1, hrS.2 l, hπ l⟩⟩
  · rintro ⟨hr'M, h⟩
    choose ρ hρS hρE using h
    obtain ⟨r, hrM, hcrt⟩ := exists_crt hC fun l => if h : l ∈ P.PM then ρ ⟨l, h⟩ else 0
    have hρl : ∀ l : {l // l ∈ P.PM}, r % l.1 = ρ l := fun l => by
      rw [hcrt l.1 l.2]
      simp only [l.2, dite_true]
      exact Nat.mod_eq_of_lt (adj_primeGraph.1 (hρE l)).1
    have hrS : r ∈ prodSet P S := ⟨hrM, fun l => by rw [hρl]; exact hρS l⟩
    refine ⟨r, (hR ▸ hrS : r ∈ (↑R : Set ℕ)), (adj_resGraph_iff_piProduct hF hC hrM hr'M s).2 ?_⟩
    exact adj_piProduct.2 fun l => by simp only [crt]; rw [hρl]; exact hρE l

/-- `prodR` is the product set of the masks' bit sets. -/
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem coe_prodR (ms : List ℕ) :
    (↑(prodR P ms) : Set ℕ) = prodSet P fun l => {ρ | (mk P ms l).testBit ρ = true} := by
  ext r
  simp only [prodR, Finset.coe_filter, Finset.mem_range, List.all_eq_true, prodSet,
    Subtype.forall]
  rfl

/-- `mstep` is the per-prime successor set, on bit sets. -/
@[category API, AMS 05 11 37, group "carry_bridge_dubc2"]
theorem testBit_mstep_eq (l m : ℕ) (s : ℤ) :
    {j | (mstep P l m s).testBit j = true} =
      {y | ∃ x ∈ {ρ | m.testBit ρ = true}, (primeGraph P l).Adj x s y} := by
  ext j
  change (mstep P l m s).testBit j = true ↔ _
  rw [testBit_mstep]
  simp only [Set.mem_ofPred_eq, adj_primeGraph]
  constructor
  · rintro ⟨r, hr, hm, h0, h1, rfl⟩
    exact ⟨r, hm, hr, h0, h1, rfl⟩
  · rintro ⟨r, hm, hr, h0, h1, rfl⟩
    exact ⟨r, hr, hm, h0, h1, rfl⟩

/-- **`DubC2.Gen.Follower.rstep_prodR`, re-derived** from the label-product step
`rstep_prodSet`. -/
@[category research solved, AMS 05 11 37, ref "LM95", group "carry_bridge_dubc2"]
theorem rstep_prodR' (hF : ParamFacts P) (hC : CRTFacts P) (ms : List ℕ) (s : ℤ) :
    rstep P (prodR P ms) s = prodR P (mstepAll P ms s) := by
  apply Finset.coe_injective
  rw [rstep_prodSet hF hC _ (coe_prodR ms) s, coe_prodR]
  congr 1
  funext l
  rw [mstepAll, mk_map _ l.2, testBit_mstep_eq]

end Residue

end CarryBridge

namespace DubC2.Gen

open CarryGraph CarryBridge Filter

/-- **`dimH_eventually_avoids_le`, re-derived**: the automaton of an entropy certificate covers
the affine system (`entGraph_simulation`, `Cover.ofSimulation`), its weights bound its entropy
by `log (a/b)` (`entGraph_superEigen`), and the generic `dimH_avoiders_le` does the rest. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "carry_bridge_dubc2"]
theorem dimH_eventually_avoids_le' {E : EntCert} {P : Params} (hc : E.check P = true) :
    dimH {ξ : ℝ | ∀ᶠ n in atTop, Avoids P ξ n}
      ≤ ENNReal.ofReal (Real.log ((E.a : ℝ) / E.b) / Real.log ((P.p : ℝ) / P.q)) := by
  have hE := E.facts P hc
  have hF : ParamFacts P := paramFacts hE.par
  have : NeZero P.M := ⟨hF.M0.ne'⟩
  have hq : 0 < P.q := by have := hF.q1; omega
  have hcov := (cover_genGraph hF).ofSimulation (entGraph_simulation hE)
  have hρ : ∀ z, ∃ i : Fin E.sets.length, z ∈ {x | ∃ v, E.mem i (enc P v) = true ∧
      x ∈ {z | ((⌊z⌋ : ℤ) : ZMod P.M) = v.1} ∩ Int.fract ⁻¹' ival (cells P.D v.2)} := by
    intro z
    obtain ⟨v, hv⟩ := affine_rho_cover (M := P.M) hF.D0 z
    exact ⟨⟨0, hE.len⟩, v, hE.init _ (enc P v).2, hv⟩
  have hν : (P.b : ℝ) * ((nuQ P : ℚ) : ℝ) = P.a := by
    rw [nuQ_cast, mul_div_cancel₀ _ (by exact_mod_cast hF.b0.ne')]
  have h := dimH_avoiders_le hq hF.pq hcov hρ (window hF hν.ge hν.le hF.sLo hF.sHi)
  have hent := entropy_le_of_superEigen (by exact_mod_cast hE.b0) (entGraph_superEigen hE)
  have hb : (0 : ℝ) < E.b := by exact_mod_cast hE.b0
  have ha : (0 : ℝ) < E.a := by have := hE.ba; have := hE.b0; exact_mod_cast (by omega : 0 < E.a)
  have hlog : ENNReal.log ((E.a : ENNReal) / E.b) = ((Real.log ((E.a : ℝ) / E.b) : ℝ) : EReal) := by
    rw [← ENNReal.log_ofReal_of_pos (by positivity), ENNReal.ofReal_div_of_pos hb]
    simp
  have hL : (0 : EReal) ≤ ((Real.log ((P.p : ℝ) / P.q) : ℝ) : EReal) := by
    have : (0 : ℝ) ≤ Real.log ((P.p : ℝ) / P.q) := by
      have hq' : (0 : ℝ) < P.q := by exact_mod_cast hq
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hq', one_mul]
      exact_mod_cast hF.pq.le
    exact_mod_cast this
  refine (le_of_eq ?_).trans (h.trans ?_)
  · congr 1
    ext ξ
    simp only [Set.mem_ofPred_eq, Avoids, Avoid, xs, Z32.xInt, Z32.orb, Params.nu, nuQ_cast]
  · rw [← EReal.real_coe_toENNReal]
    refine EReal.toENNReal_le_toENNReal ?_
    rw [EReal.coe_div, ← hlog]
    exact EReal.div_le_div_right_of_nonneg hL hent

end DubC2.Gen
