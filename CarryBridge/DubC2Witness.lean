/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.DubC2

/-!
# Bridge: the `DubC2` obstruction witnesses as carry-graph facts

`DubC2/Horseshoe.lean` and `DubC2/Branch.lean` prove `¬ Checked` from a witness, building the
witness's pseudo-orbit (resp. its finite pseudo-orbit segments) inside the proof.  This file
builds the same objects as stand-alone statements and reads them in `CarryGraph` terms:

* `horseOK` gives an avoiding pseudo-orbit with aperiodic letters
  (`exists_pseudoOrbit_of_horseOK`), hence no label form for any `D`, `M`
  (`not_allPer_of_horseOK`);
* `branchOK` makes every prefix of an aperiodic word a word of the certificate graph, hence an
  infinite path with aperiodic labels (`exists_iPath_of_branchOK`, via the generic
  `exists_iPath_of_forall_reads`), hence no label form (`not_allPer_of_branchOK`).

`not_checked_of_horseOK'` and `not_checked_of_branchOK'` re-derive the two soundness theorems: a
checked certificate gives the label form (`checked_allPer`, `certGraph_allPer'`), which the
witnesses contradict.  The constructions are repeated here, not factored out of the `DubC2/`
files, so that the kernel-checked atlases importing those files are not rebuilt.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace CarryBridge

open CarryGraph DubC2.Gen DubC2.Gen.Horse DubC2.Gen.Branch Filter
  ForMathlib.SubwordComplexity

variable {P : Params}

/-! ### Horseshoe witnesses -/

/-- **A horseshoe witness gives an avoiding pseudo-orbit with aperiodic letters**, for every
parameter set with the same base and shift whose prime lists lie inside the witness's. -/
@[category research solved, AMS 11 37, ref "Oda26", group "carry_bridge_dubc2"]
theorem exists_pseudoOrbit_of_horseOK (hF : ParamFacts P) (H : HorseWitness)
    (h : horseOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) :
    ∃ (r : ℕ → ℕ) (y : ℕ → ℝ) (s : ℕ → ℤ), PseudoOrbit P r y s ∧ ¬ IsEventuallyPeriodic s := by
  classical
  simp only [horseOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hL, hlen⟩, hne⟩, hPMw⟩, hw₁⟩, hw₂⟩ := h
  have hW : ∀ k, WordFacts P.p P.q P.a P.b H (hblk H.w₁ H.w₂ k) := fun k => by
    rcases hblk_cases (w₁ := H.w₁) (w₂ := H.w₂) k with e | e <;> rw [e]
    · exact wordFacts hw₁
    · exact wordFacts hw₂
  set L := H.w₁.length with hLdef
  have hbl : ∀ k, (hblk H.w₁ H.w₂ k).length = L := hblk_length hlen
  set s := hseq H.w₁ H.w₂ with hsdef
  have hsat : ∀ k i, i < L → s (k * L + i) = (hblk H.w₁ H.w₂ k).getD i 0 :=
    fun k i hi => hseq_at hL k hi
  -- real parameters
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hp0 : (0 : ℝ) < P.p := by linarith
  have hb0 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  set ρ : ℝ := (P.q : ℝ) / P.p with hρ
  have hρ0 : 0 ≤ ρ := (div_pos hq0 hp0).le
  have hρ1 : ρ < 1 := (div_lt_one hp0).2 hpq
  -- the letter bound and the series point
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ n, |(s n : ℝ)| ≤ S := by
    refine ⟨((H.w₁ ++ H.w₂).map (fun x : ℤ => |(x : ℝ)|)).sum, fun n => ?_⟩
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem ?_)
    · obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    · rcases hseq_mem hL hlen n with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h
  set c : ℝ := ((P.p : ℝ) - P.q) * P.a / P.b with hcdef
  set u : ℕ → ℝ := fun n => ((s n : ℝ) + c) / P.p with hu
  have hub : ∀ n, |u n| ≤ (S + |c|) / P.p := fun n => by
    simp only [hu, abs_div, abs_of_pos hp0]
    exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (by linarith [hS n])) hp0.le
  set y : ℕ → ℝ := gs ρ u with hy
  have hrec : ∀ n, y n = hb P.p P.q P.a P.b (s n) (y (n + 1)) := fun n => by
    simp only [hy]
    rw [gs_rec hρ0 hρ1 hub n]
    simp only [hu, hb, hρ, hcdef]
    field_simp
    ring
  have hyb : ∀ n, |y n| ≤ (S + |c|) / P.p / (1 - ρ) := gs_abs_le hρ0 hρ1 hub
  -- the boundary points lie in `K`
  set lo : ℝ := (H.lo : ℝ)
  set hi : ℝ := (H.hi : ℝ)
  set E : ℝ := (S + |c|) / P.p / (1 - ρ) + |lo| + |hi| with hE
  have hE0 : 0 ≤ E := by
    have := (abs_nonneg (y 0)).trans (hyb 0)
    simp only [hE]
    linarith [abs_nonneg lo, abs_nonneg hi]
  set lam : ℝ := ρ ^ L with hlam
  have hlam0 : 0 ≤ lam := pow_nonneg hρ0 _
  have hlam1 : lam < 1 := pow_lt_one₀ hρ0 hρ1 hL.ne'
  have hblock : ∀ k (ε : ℝ), lo - ε ≤ y (k * L + L) → y (k * L + L) ≤ hi + ε →
      ∀ i ≤ L, back P.p P.q P.a P.b ((hblk H.w₁ H.w₂ k).drop i) lo - ρ ^ (L - i) * ε ≤
          y (k * L + i) ∧
        y (k * L + i) ≤ back P.p P.q P.a P.b ((hblk H.w₁ H.w₂ k).drop i) hi + ρ ^ (L - i) * ε := by
    intro k ε h1 h2 i hi'
    have := block_bounds (w := hblk H.w₁ H.w₂ k) (n₀ := k * L) hp0 hrec
      (fun i hi => hsat k i (by rw [← hbl k]; exact hi)) (by rwa [hbl k]) (by rwa [hbl k]) i
      (by rw [hbl k]; exact hi')
    rwa [hbl k] at this
  have hbnd : ∀ m k, lo - lam ^ m * E ≤ y (k * L) ∧ y (k * L) ≤ hi + lam ^ m * E := by
    intro m
    induction m with
    | zero =>
      intro k
      obtain ⟨h1, h2⟩ := abs_le.1 (hyb (k * L))
      simp only [pow_zero, one_mul, hE]
      constructor <;> linarith [neg_abs_le lo, le_abs_self hi, le_abs_self lo, neg_abs_le hi]
    | succ m ih =>
      intro k
      obtain ⟨h1, h2⟩ := ih (k + 1)
      rw [show (k + 1) * L = k * L + L by ring] at h1 h2
      have := hblock k _ h1 h2 0 (Nat.zero_le _)
      simp only [List.drop_zero, Nat.sub_zero, Nat.add_zero] at this
      have hlo := (hW k).lo
      have hhi := (hW k).hi
      have hlo' : lo ≤ back P.p P.q P.a P.b (hblk H.w₁ H.w₂ k) lo := by
        have := (Rat.cast_le (K := ℝ)).2 hlo
        rwa [cast_back] at this
      have hhi' : back P.p P.q P.a P.b (hblk H.w₁ H.w₂ k) hi ≤ hi := by
        have := (Rat.cast_le (K := ℝ)).2 hhi
        rwa [cast_back] at this
      rw [pow_succ', mul_assoc]
      constructor <;> linarith [this.1, this.2]
  have hK : ∀ k, lo ≤ y (k * L) ∧ y (k * L) ≤ hi := by
    intro k
    constructor
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < (lo - y (k * L)) / (E + 1) by
        apply div_pos <;> linarith) hlam1
      have h1 := (hbnd m k).1
      have : lam ^ m * E < lo - y (k * L) := by
        rw [lt_div_iff₀ (by linarith)] at hm
        nlinarith [pow_nonneg hlam0 m]
      linarith
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < (y (k * L) - hi) / (E + 1) by
        apply div_pos <;> linarith) hlam1
      have h1 := (hbnd m k).2
      have : lam ^ m * E < y (k * L) - hi := by
        rw [lt_div_iff₀ (by linarith)] at hm
        nlinarith [pow_nonneg hlam0 m]
      linarith
  -- every point lies in `[0, 1)`
  have hy01 : ∀ n, 0 ≤ y n ∧ y n < 1 := by
    intro n
    obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < L ∧ n = k * L + i :=
      ⟨n / L, n % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']⟩
    obtain ⟨h1, h2⟩ := hK (k + 1)
    rw [show (k + 1) * L = k * L + L by ring] at h1 h2
    have := hblock k 0 (by simpa using h1) (by simpa using h2) i hi.le
    simp only [mul_zero, sub_zero, add_zero] at this
    have hi' : i < (hblk H.w₁ H.w₂ k).length := by rw [hbl k]; exact hi
    have g0 := (Rat.cast_le (K := ℝ)).2 ((hW k).img0 i hi')
    have g1 := (Rat.cast_lt (K := ℝ)).2 ((hW k).img1 i hi')
    rw [cast_back] at g0 g1
    push_cast at g0 g1
    exact ⟨g0.trans this.1, this.2.trans_lt g1⟩
  -- the carry identity
  have hident : ∀ n, (s n : ℝ) * P.b =
      P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a := by
    intro n
    have e := hrec n
    simp only [hb] at e
    rw [eq_div_iff hp0.ne'] at e
    field_simp at e
    linear_combination -e
  -- residues
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (H.R % P.M).toNat with hr₀
  have hr₀c : (r₀ : ℤ) = H.R % P.M := Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne')
  have hr₀M : r₀ < P.M := by
    have := Int.emod_lt_of_pos H.R hM0
    omega
  set r := rs P r₀ s with hr
  have hrlt : ∀ n, r n < P.M := by
    intro n; cases n with
    | zero => exact hr₀M
    | succ n => exact rnext_lt hF _ _
  have hrav : ∀ n, ∀ l ∈ P.PM, r n % l ≠ 0 :=
    rs_av_of_blocks hF hL hlen hPM hPMw
      (fun k l hl => by have h := (hW k).ret l hl; rw [hbl k] at h; exact h)
      (fun k l hl i hi => (hW k).av l hl i (by rw [hbl k]; exact hi))
  have hpo : PseudoOrbit P r y s := by
    refine ⟨hrlt, fun n => (hy01 n).1, fun n => (hy01 n).2, hident, fun n => rfl, hrav, ?_⟩
    intro n l hl
    have hlH := hPq l hl
    rcases hseq_mem hL hlen n with hm | hm
    · exact (wordFacts hw₁).sav l hlH _ hm
    · exact (wordFacts hw₂).sav l hlH _ hm
  exact ⟨r, y, s, hpo, hseq_not_periodic hL hlen hne⟩


/-- **A horseshoe witness rules out the label form** of the affine carry graph, for every cell
count and modulus. -/
@[category research solved, AMS 11 37 05, ref "Oda26", group "carry_bridge_dubc2"]
theorem not_allPer_of_horseOK (hF : ParamFacts P) [NeZero P.M] (H : HorseWitness)
    (h : horseOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ (genGraph P).AllPer := by
  obtain ⟨r, y, s, hpo, hs⟩ := exists_pseudoOrbit_of_horseOK hF H h hPM hPq
  exact not_allPer_of_pseudoOrbit hF hpo hs

/-- **`not_checked_of_horseOK`, re-derived**: a checked certificate gives the label form. -/
@[category research solved, AMS 11 37, ref "Oda26", group "carry_bridge_dubc2"]
theorem not_checked_of_horseOK' {C : Cert} (H : HorseWitness)
    (h : horseOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ Checked P C := by
  intro hc
  have hF := paramFacts_of_checked hc
  have : NeZero P.M := ⟨hF.M0.ne'⟩
  exact not_allPer_of_horseOK hF H h hPM hPq (checked_allPer hc)

/-! ### Branching witnesses -/

/-- **A branching witness gives an infinite path of the certificate graph with aperiodic labels**,
for every cell count and modulus: every prefix of the coded concatenation is read (finite
pseudo-orbit segments), and the generic `exists_iPath_of_forall_reads` does the rest. -/
@[category research solved, AMS 11 37 05, ref "Oda26" "LM95", group "carry_bridge_dubc2"]
theorem exists_iPath_of_branchOK (hF : ParamFacts P) (H : BranchWitness)
    (h : branchOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) :
    ∃ (v : ℕ → Fin P.nV) (ℓ : ℕ → Fin P.nA), (certGraph P).IsIPath v ℓ ∧ ¬ EvPer ℓ := by
  classical
  simp only [branchOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hL', hlen⟩, hne⟩, hPMw⟩, hlo0⟩, hlohi⟩, hhi1⟩, hw₁⟩, hw₂⟩ := h
  have hW : ∀ k, BWordFacts P.p P.q P.a P.b H (hblk H.w₁ H.w₂ k) := fun k => by
    rcases hblk_cases (w₁ := H.w₁) (w₂ := H.w₂) k with e | e <;> rw [e]
    · exact bwordFacts hw₁
    · exact bwordFacts hw₂
  set L := H.w₁.length with hLdef
  have hbl : ∀ k, (hblk H.w₁ H.w₂ k).length = L := hblk_length hlen
  set s := hseq H.w₁ H.w₂ with hsdef
  have hsat : ∀ k i, i < L → s (k * L + i) = (hblk H.w₁ H.w₂ k).getD i 0 :=
    fun k i hi => hseq_at hL' k hi
  have hp0 : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb0 : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  set I : ℚ × ℚ := (H.lo, H.hi) with hI
  -- the word of the first `k` blocks keeps `I` inside its follower interval
  set W : ℕ → List ℤ := fun k => (List.range (k * L)).map s with hW'
  have hWsucc : ∀ k, W (k + 1) = W k ++ hblk H.w₁ H.w₂ k := by
    intro k
    simp only [hW', show (k + 1) * L = k * L + L by ring, List.range_add, List.map_append,
      List.map_map]
    congr 1
    refine List.ext_getElem (by simp [hbl k]) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [hsat k i h1, List.getD_eq_getElem _ _ (by rw [hbl k]; exact h1)]
  have hWin : ∀ k, Within I (ifold P.p P.q P.a P.b (W k) I) := by
    intro k
    induction k with
    | zero =>
      simp only [hW', zero_mul, List.range_zero, List.map_nil]
      exact ⟨le_rfl, le_rfl⟩
    | succ k ih =>
      rw [hWsucc, ifold_append]
      exact (hW k).within.trans (ifold_mono hp0.le hq0 _ ih)
  have hWget : ∀ k i, i < k * L → (W k).getD i 0 = s i := by
    intro k i hi
    rw [List.getD_eq_getElem _ _ (by simp [hW']; exact hi)]
    simp [hW']
  have hWlen : ∀ k, (W k).length = k * L := fun k => by simp [hW']
  -- residues
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (H.R % P.M).toNat with hr₀
  have hr₀M : r₀ < P.M := by
    have := Int.emod_lt_of_pos H.R hM0
    have := Int.emod_nonneg H.R hM0.ne'
    omega
  set r := rs P r₀ s with hr
  have hrlt : ∀ n, r n < P.M := by
    intro n; cases n with
    | zero => exact hr₀M
    | succ n => exact rnext_lt hF _ _
  have hrav : ∀ n, ∀ l ∈ P.PM, r n % l ≠ 0 :=
    rs_av_of_blocks hF hL' hlen hPM hPMw
      (fun k l hl => by have h := (hW k).ret l hl; rw [hbl k] at h; exact h)
      (fun k l hl i hi => (hW k).av l hl i (by rw [hbl k]; exact hi))
  have hsav : ∀ n, ∀ l ∈ P.Pq, s n % (l : ℤ) ≠ 0 := by
    intro n l hl
    have hlH := hPq l hl
    rcases hseq_mem hL' hlen n with hm | hm
    · exact (bwordFacts hw₁).sav l hlH _ hm
    · exact (bwordFacts hw₂).sav l hlH _ hm
  -- finite paths of every length
  have hfin : ∀ m, ∃ v : ℕ → ℕ, (∀ i ≤ m, v i < P.nV) ∧ ∀ i < m,
      PseudoOrbit.ptix P s i < P.nA ∧ P.letter (PseudoOrbit.ptix P s i) = s i ∧
        v (i + 1) ∈ P.succList (v i) (P.letter (PseudoOrbit.ptix P s i)) := by
    intro m
    have hmL : m + 1 ≤ (m + 1) * L := Nat.le_mul_of_pos_right _ hL'
    obtain ⟨ys, -, -, -, hys, hrec⟩ := realize (a := P.a) (b := P.b) hp0 hq0 (W (m + 1)) I hlo0
      hhi1 H.lo (hWin (m + 1)).1 (hlohi.trans_le (hWin (m + 1)).2)
    rw [hWlen] at hys hrec
    set y : ℕ → ℝ := fun i => (ys i : ℝ)
    have hst : ∀ i, i < (m + 1) * L →
        PseudoOrbit.pvtx P r y i < P.nV ∧ PseudoOrbit.ptix P s i < P.nA ∧
        P.letter (PseudoOrbit.ptix P s i) = s i ∧
          PseudoOrbit.pvtx P r y (i + 1) ∈ P.succList (PseudoOrbit.pvtx P r y i)
            (P.letter (PseudoOrbit.ptix P s i)) := by
      intro i hi
      obtain ⟨a0, a1⟩ := hys i hi.le
      obtain ⟨b0, b1⟩ := hys (i + 1) hi
      have e := hrec i hi
      rw [hWget _ _ hi] at e
      refine PseudoOrbit.step_of hF i (hrlt i) (show (0 : ℝ) ≤ (ys i : ℝ) by exact_mod_cast a0)
        (show (ys i : ℝ) < 1 by exact_mod_cast a1)
        (show (0 : ℝ) ≤ (ys (i + 1) : ℝ) by exact_mod_cast b0)
        (show (ys (i + 1) : ℝ) < 1 by exact_mod_cast b1) ?_ rfl (hrav i) (hrav (i + 1)) (hsav i)
      have e' : ((ys (i + 1) : ℚ) : ℝ) = ((fw P.p P.q P.a P.b (s i) (ys i) : ℚ) : ℝ) := by rw [e]
      simp only [fw] at e'
      push_cast at e'
      simp only [y]
      have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hb' : (P.b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
      rw [e']
      field_simp
      ring
    exact ⟨PseudoOrbit.pvtx P r y, fun i hi => (hst i (by omega)).1,
      fun i hi => (hst i (by omega)).2⟩
  have hlet : ∀ n, PseudoOrbit.ptix P s n < P.nA ∧ P.letter (PseudoOrbit.ptix P s n) = s n := by
    intro n
    obtain ⟨v, -, hv⟩ := hfin (n + 1)
    exact ⟨(hv n (by omega)).1, (hv n (by omega)).2.1⟩
  have hnV : 0 < P.nV := Nat.mul_pos hF.M0 hF.D0
  let ℓ : ℕ → Fin P.nA := fun n => ⟨PseudoOrbit.ptix P s n, (hlet n).1⟩
  obtain ⟨v, hv⟩ := exists_iPath_of_forall_reads (X := certGraph P) (ℓ := ℓ) fun m => by
    obtain ⟨g, hg1, hg2⟩ := hfin m
    refine ⟨fun i => if hi : g i < P.nV then ⟨g i, hi⟩ else ⟨0, hnV⟩, fun i hi => ?_⟩
    refine adj_ofRel.2 ?_
    simp only [hg1 i (by omega), hg1 (i + 1) (by omega), ↓reduceDIte]
    exact (hg2 i hi).2.2
  refine ⟨v, ℓ, hv, fun ⟨n₀, L, hL, hper⟩ =>
    hseq_not_periodic hL' hlen hne ⟨n₀, L, hL, fun k hk => ?_⟩⟩
  have e := congrArg (fun t : Fin P.nA => P.letter t) (hper k hk)
  simp only [ℓ] at e
  rw [(hlet k).2, (hlet (k + L)).2] at e
  exact e

/-- **A branching witness rules out the label form** of the affine carry graph. -/
@[category research solved, AMS 11 37 05, ref "Oda26", group "carry_bridge_dubc2"]
theorem not_allPer_of_branchOK (hF : ParamFacts P) [NeZero P.M] (H : BranchWitness)
    (h : branchOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ (genGraph P).AllPer := by
  intro hX
  obtain ⟨v, ℓ, hp, hn⟩ := exists_iPath_of_branchOK hF H h hPM hPq
  exact hn ((allPer_certGraph_iff hF).2 hX v ℓ hp)

/-- **`not_checked_of_branchOK`, re-derived** from the certificate's own structure
(`certGraph_allPer'`). -/
@[category research solved, AMS 11 37, ref "Oda26", group "carry_bridge_dubc2"]
theorem not_checked_of_branchOK' {C : Cert} (H : BranchWitness)
    (h : branchOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ Checked P C := by
  intro hc
  obtain ⟨v, ℓ, hp, hn⟩ := exists_iPath_of_branchOK (paramFacts_of_checked hc) H h hPM hPq
  exact hn (certGraph_allPer' hc v ℓ hp)

end CarryBridge
