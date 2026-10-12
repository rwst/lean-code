/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Core
import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Growth and entropy ([LM95] §4.1, §4.3, §5.3)

The number `npaths v n` of labelled paths of length `n` from `v` either grows polynomially or
at least like `2^(n/N)` (`polyGrowth_or_exp`): a labelled rank gives the polynomial bound
(`isLRank_polyGrowth`), and a vertex with two arcs inside its strong component doubles its path
count every `N` steps (`pow_le_npaths_of_branch`).

The **entropy** of a finite carry graph is the exponential growth rate of the total path count,
`expGrowthSup (n ↦ ∑ v, npaths v n)`, an `EReal` (it is `⊥` when the graph has no infinite path).
It is the topological entropy of the edge shift [LM95, Def. 4.1.1, Prop. 4.1.13]; it equals
`log λ_A` for the Perron eigenvalue of the adjacency matrix [LM95, Thm. 4.3.1], which is not
proved here.  The proved substitutes are the eigenvector brackets of [LM95, §5.3]: a
*super-eigenvector* `b·(A w) ≤ a·w`, `w ≥ 1` bounds the entropy by `log (a/b)`
(`entropy_le_of_superEigen`), a *sub-eigenvector* `a·w ≤ b·(A w)`, `w ≠ 0` bounds it from below
(`log_le_entropy_of_subEigen`).

## Contents

* `arcsFrom`, `npaths_succ'`, `npaths_le_succ`, `npaths_mono_of_reach`.
* `PolyGrowth`, `npaths_le_of_isLRank`, `isLRank_polyGrowth`.
* `pow_le_npaths_of_branch`, `polyGrowth_lnoBranch`, `polyGrowth_or_exp` — the dichotomy.
* `ntot`, `entropy`, `entropy_le_zero_of_polyGrowth`, `entropy_pos_of_branch`,
  `entropy_le_zero_iff`, `entropy_pos_iff`.
* `IsSuperEigen`, `IsSubEigen`, `pow_mul_npaths_le`, `pow_mul_le_npaths`,
  `entropy_le_of_superEigen`, `log_le_entropy_of_subEigen`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

open Filter ENNReal ExpGrowth

namespace CarryGraph

variable {V A : Type*} {X : CarryGraph V A}

/-! ### Path counts -/

section count

variable [Fintype A]

variable (X) in
/-- The arcs leaving `v`, as pairs (label, target). -/
def arcsFrom (v : V) : Finset (Σ _ : A, V) := Finset.univ.sigma (X.succ v)

@[category API, AMS 05 37, group "carry_growth"]
theorem mem_arcsFrom {v : V} {x : Σ _ : A, V} : x ∈ X.arcsFrom v ↔ X.Adj v x.1 x.2 := by
  simp [arcsFrom, Adj]

@[category API, AMS 05 37, group "carry_growth"]
theorem npaths_succ' (v : V) (n : ℕ) :
    X.npaths v (n + 1) = ∑ x ∈ X.arcsFrom v, X.npaths x.2 n := by
  rw [npaths_succ, arcsFrom, Finset.sum_sigma]

@[category API, AMS 05 37, group "carry_growth"]
theorem npaths_le_succ {v w : V} {a : A} (h : X.Adj v a w) (n : ℕ) :
    X.npaths w n ≤ X.npaths v (n + 1) := by
  rw [npaths_succ']
  exact Finset.single_le_sum (f := fun x : Σ _ : A, V => X.npaths x.2 n)
    (fun _ _ => Nat.zero_le _) ((mem_arcsFrom (x := ⟨a, w⟩)).2 h)

@[category API, AMS 05 37, group "carry_growth"]
theorem npaths_add_le_succ {v t u : V} {a b : A} (ht : X.Adj v a t) (hu : X.Adj v b u)
    (hne : ¬ (a = b ∧ t = u)) (n : ℕ) :
    X.npaths t n + X.npaths u n ≤ X.npaths v (n + 1) := by
  classical
  have hne' : (⟨a, t⟩ : Σ _ : A, V) ≠ ⟨b, u⟩ := fun h => hne ⟨congrArg Sigma.fst h,
    by simpa using (Sigma.mk.inj_iff.1 h).2⟩
  rw [npaths_succ', ← Finset.sum_pair (f := fun x : Σ _ : A, V => X.npaths x.2 n) hne']
  refine Finset.sum_le_sum_of_subset fun x hx => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mem_arcsFrom.2 ht
  · exact mem_arcsFrom.2 hu

@[category API, AMS 05 37, group "carry_growth"]
theorem npaths_mono_of_reach {x y : V} (h : X.Reach x y) :
    ∃ j, ∀ m, X.npaths y m ≤ X.npaths x (j + m) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun m => by simp⟩
  | head hxz _ ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨a, ha⟩ := hxz
    refine ⟨j + 1, fun m => (hj m).trans ?_⟩
    rw [show j + 1 + m = (j + m) + 1 by ring]
    exact npaths_le_succ ha _

end count

/-! ### Polynomial growth from a labelled rank -/

section poly

variable [Fintype V] [Fintype A]

variable (X) in
/-- Polynomial path growth, uniformly in the start vertex. -/
def PolyGrowth : Prop := ∃ C d : ℕ, ∀ v n, X.npaths v n ≤ C * (n + 1) ^ d

@[category API, AMS 05 37, group "carry_growth"]
theorem card_arcsFrom_le (v : V) : (X.arcsFrom v).card ≤ Fintype.card A * Fintype.card V := by
  calc (X.arcsFrom v).card ≤ (Finset.univ : Finset (Σ _ : A, V)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card A * Fintype.card V := by simp [Fintype.card_sigma]

/-- **The counting step.**  With `B = |A||V|` and `Y = B N + 1`, a vertex of rank `r` has at
most `Y ^ r` labelled paths of each length `n ≤ N`: along the unique rank-keeping arc the count
grows by at most `B · Y^(r-1)` per step, the rank-dropping arcs being bounded by induction. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem npaths_le_of_isLRank {ρ : V → ℕ} (h : X.IsLRank ρ) (N : ℕ) :
    ∀ r v, ρ v = r → ∀ n ≤ N,
      X.npaths v n ≤ (Fintype.card A * Fintype.card V * N + 1) ^ r := by
  classical
  set B := Fintype.card A * Fintype.card V with hB
  set Y := B * N + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    set D := if r = 0 then 0 else B * Y ^ (r - 1) with hD
    have inner : ∀ n ≤ N, ∀ v, ρ v = r → X.npaths v n ≤ 1 + n * D := by
      intro n
      induction n with
      | zero => intro _ v _; simp [npaths_zero]
      | succ n ihn =>
        intro hn v hv
        rw [npaths_succ', ← Finset.sum_filter_add_sum_filter_not _ (fun x => ρ x.2 = r)]
        have hkeep : ∑ x ∈ (X.arcsFrom v).filter (fun x => ρ x.2 = r), X.npaths x.2 n ≤
            1 + n * D := by
          have hcard : ((X.arcsFrom v).filter (fun x => ρ x.2 = r)).card ≤ 1 := by
            refine Finset.card_le_one.2 fun x hx y hy => ?_
            simp only [Finset.mem_filter, mem_arcsFrom] at hx hy
            obtain ⟨h1, h2⟩ := h.2 v _ _ _ _ hx.1 hy.1 (hx.2.trans hv.symm) (hy.2.trans hv.symm)
            obtain ⟨x1, x2⟩ := x
            obtain ⟨y1, y2⟩ := y
            simp only at h1 h2
            subst h1 h2
            rfl
          calc _ ≤ ((X.arcsFrom v).filter (fun x => ρ x.2 = r)).card • (1 + n * D) :=
                Finset.sum_le_card_nsmul _ _ _ fun x hx => by
                  simp only [Finset.mem_filter] at hx
                  exact ihn (by omega) x.2 hx.2
            _ ≤ 1 • (1 + n * D) := Nat.mul_le_mul_right _ hcard
            _ = 1 + n * D := one_smul _ _
        have hdrop : ∑ x ∈ (X.arcsFrom v).filter (fun x => ¬ ρ x.2 = r), X.npaths x.2 n ≤ D := by
          rcases Nat.eq_zero_or_pos r with hr | hr
          · have : (X.arcsFrom v).filter (fun x => ¬ ρ x.2 = r) = ∅ := by
              refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
              simp only [Finset.mem_filter, mem_arcsFrom] at hx
              have := h.1 v _ _ hx.1
              omega
            simp [this]
          · have hDr : D = B * Y ^ (r - 1) := by simp [hD, hr.ne']
            calc _ ≤ ((X.arcsFrom v).filter (fun x => ¬ ρ x.2 = r)).card • Y ^ (r - 1) :=
                  Finset.sum_le_card_nsmul _ _ _ fun x hx => by
                    simp only [Finset.mem_filter, mem_arcsFrom] at hx
                    have hlt : ρ x.2 < r := by have := h.1 v _ _ hx.1; omega
                    exact (ih (ρ x.2) hlt x.2 rfl n (by omega)).trans
                      (Nat.pow_le_pow_right hY1 (by omega))
              _ ≤ B • Y ^ (r - 1) := Nat.mul_le_mul_right _
                  ((Finset.card_filter_le _ _).trans (card_arcsFrom_le v))
              _ = D := by rw [hDr, smul_eq_mul]
        calc _ ≤ (1 + n * D) + D := Nat.add_le_add hkeep hdrop
          _ = 1 + (n + 1) * D := by ring
    intro v hv n hn
    refine (inner n hn v hv).trans ?_
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hD, hr]
    · have hDr : D = B * Y ^ (r - 1) := by simp [hD, hr.ne']
      calc 1 + n * D ≤ Y ^ (r - 1) + n * (B * Y ^ (r - 1)) := by
            rw [hDr]; exact Nat.add_le_add_right (Nat.one_le_pow _ _ hY1) _
        _ = Y ^ (r - 1) * (1 + B * n) := by ring
        _ ≤ Y ^ (r - 1) * Y := Nat.mul_le_mul_left _ (by rw [hY]; nlinarith)
        _ = Y ^ r := by rw [← pow_succ, Nat.sub_add_cancel hr]

/-- **A labelled rank gives polynomial growth**: a rank bounded by `R` gives at most
`(|A||V| + 1)^R (n+1)^R` labelled paths of length `n`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem isLRank_polyGrowth {ρ : V → ℕ} (h : X.IsLRank ρ) {R : ℕ} (hR : ∀ v, ρ v ≤ R) :
    ∀ v n, X.npaths v n ≤ (Fintype.card A * Fintype.card V + 1) ^ R * (n + 1) ^ R := by
  intro v n
  calc X.npaths v n ≤ (Fintype.card A * Fintype.card V * n + 1) ^ ρ v :=
        npaths_le_of_isLRank h n _ v rfl n le_rfl
    _ ≤ (Fintype.card A * Fintype.card V * n + 1) ^ R := Nat.pow_le_pow_right (by omega) (hR v)
    _ ≤ ((Fintype.card A * Fintype.card V + 1) * (n + 1)) ^ R :=
      Nat.pow_le_pow_left (by nlinarith) _
    _ = _ := mul_pow _ _ _

@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem polyGrowth_of_lnoBranch [DecidableEq V] (h : X.LNoBranch) : X.PolyGrowth :=
  ⟨_, _, isLRank_polyGrowth (lnoBranch_isLRank_desc h) desc_le_card⟩

end poly

/-! ### Branching forces exponential growth -/

section branch

variable [Fintype A]

/-- **Doubling**: a vertex with two distinct arcs inside its strong component has at least
`2^k` labelled paths of length `k N`, for some `N > 0`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem pow_le_npaths_of_branch {v t u : V} {a b : A} (hvt : X.Adj v a t) (hvu : X.Adj v b u)
    (hne : ¬ (a = b ∧ t = u)) (htv : X.Reach t v) (huv : X.Reach u v) :
    ∃ N, 0 < N ∧ ∀ k, 2 ^ k ≤ X.npaths v (k * N) := by
  obtain ⟨j₁, h₁⟩ := npaths_mono_of_reach htv
  obtain ⟨j₂, h₂⟩ := npaths_mono_of_reach huv
  have step : ∀ m, 2 * X.npaths v m ≤ X.npaths v (j₁ + j₂ + 2 + m) := by
    intro m
    have a1 : X.npaths v m ≤ X.npaths t (j₁ + j₂ + 1 + m) := by
      calc X.npaths v m ≤ X.npaths u (j₂ + m) := h₂ m
        _ ≤ X.npaths v (j₂ + m + 1) := npaths_le_succ hvu _
        _ ≤ X.npaths t (j₁ + (j₂ + m + 1)) := h₁ _
        _ = _ := by ring_nf
    have a2 : X.npaths v m ≤ X.npaths u (j₁ + j₂ + 1 + m) := by
      calc X.npaths v m ≤ X.npaths t (j₁ + m) := h₁ m
        _ ≤ X.npaths v (j₁ + m + 1) := npaths_le_succ hvt _
        _ ≤ X.npaths u (j₂ + (j₁ + m + 1)) := h₂ _
        _ = _ := by ring_nf
    calc 2 * X.npaths v m ≤ X.npaths t (j₁ + j₂ + 1 + m) + X.npaths u (j₁ + j₂ + 1 + m) := by
          omega
      _ ≤ X.npaths v (j₁ + j₂ + 1 + m + 1) := npaths_add_le_succ hvt hvu hne _
      _ = _ := by ring_nf
  refine ⟨j₁ + j₂ + 2, by omega, fun k => ?_⟩
  induction k with
  | zero => simp [npaths_zero]
  | succ k ih =>
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * X.npaths v (k * (j₁ + j₂ + 2)) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := step _
      _ = _ := by ring_nf

/-- Exponential beats polynomial. -/
@[category API, AMS 05, group "carry_growth"]
theorem exists_pow_lt (C d a L : ℕ) (hL : 0 < L) : ∃ m, C * (a + m * L + 1) ^ d < 2 ^ m := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · exact ⟨0, by simp⟩
  set E := a + (d + 1) * L + 1 with hE
  set j := C * E ^ d with hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
  refine ⟨(d + 1) * j, ?_⟩
  have h1 : a + (d + 1) * j * L + 1 ≤ E * j := by
    have : a ≤ a * j := Nat.le_mul_of_pos_right _ hj1
    have : (d + 1) * j * L = (d + 1) * L * j := by ring
    nlinarith
  have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
  calc C * (a + (d + 1) * j * L + 1) ^ d ≤ C * (E * j) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = j * j ^ d := by rw [hj, mul_pow]; ring
    _ ≤ j * (2 ^ j) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjlt.le _)
    _ < 2 ^ j * (2 ^ j) ^ d := mul_lt_mul_of_pos_right hjlt (by positivity)
    _ = 2 ^ ((d + 1) * j) := by rw [← pow_succ', ← pow_mul, Nat.mul_comm]

end branch

section dichotomy

variable [Fintype V] [Fintype A]

omit [Fintype V] in
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem polyGrowth_lnoBranch (h : X.PolyGrowth) : X.LNoBranch := by
  intro v a b t u hvt hvu htv huv
  by_contra hne
  obtain ⟨N, hN, hk⟩ := pow_le_npaths_of_branch hvt hvu hne htv huv
  obtain ⟨C, d, hCd⟩ := h
  obtain ⟨m, hm⟩ := exists_pow_lt C d 0 N hN
  have := (hk m).trans (hCd v (m * N))
  rw [zero_add] at hm
  omega

/-- **The growth dichotomy**: path counts grow polynomially, or some vertex doubles its count
every `N` steps. -/
@[category research solved, AMS 05 37, ref "LM95", group "carry_growth"]
theorem polyGrowth_or_exp [DecidableEq V] :
    X.PolyGrowth ∨ ∃ v N, 0 < N ∧ ∀ k, 2 ^ k ≤ X.npaths v (k * N) := by
  by_cases h : X.LNoBranch
  · exact .inl (polyGrowth_of_lnoBranch h)
  · right
    simp only [LNoBranch, not_forall] at h
    obtain ⟨v, a, b, t, u, hvt, hvu, htv, huv, hne⟩ := h
    obtain ⟨N, hN, hk⟩ := pow_le_npaths_of_branch hvt hvu hne htv huv
    exact ⟨v, N, hN, hk⟩

end dichotomy

/-! ### Entropy -/

section entropy

variable [Fintype V] [Fintype A]

variable (X) in
/-- The total number of labelled paths of length `n`. -/
def ntot (n : ℕ) : ℕ := ∑ v, X.npaths v n

variable (X) in
/-- **The entropy** of a finite carry graph: the exponential growth rate of the number of
labelled paths, i.e. the topological entropy of its edge shift [LM95, §4.1]. -/
noncomputable def entropy : EReal := expGrowthSup fun n => (X.ntot n : ℝ≥0∞)

@[category API, AMS 05 37, group "carry_growth"]
theorem npaths_le_ntot (v : V) (n : ℕ) : X.npaths v n ≤ X.ntot n :=
  Finset.single_le_sum (f := fun v => X.npaths v n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

/-- Polynomials have exponential growth rate at most `0`. -/
@[category API, AMS 05 37, group "carry_growth"]
theorem expGrowthSup_poly_le (C d : ℕ) :
    expGrowthSup (fun n => ((C * (n + 1) ^ d : ℕ) : ℝ≥0∞)) ≤ 0 := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨ε, hε0, hεc⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hε : 0 < ε := by exact_mod_cast hε0
  refine le_trans ?_ hεc.le
  set r := Real.exp ε with hr
  have hr1 : 1 < r := lt_trans (by linarith) (Real.add_one_lt_exp hε.ne')
  set K : ℝ := C * 2 ^ d + 1 with hK
  have hKpos : 0 < K := by positivity
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt d hr1).eventually
    (gt_mem_nhds (inv_pos.2 hKpos))
  have hev : ∀ᶠ n : ℕ in atTop, ((C * (n + 1) ^ d : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal r ^ n := by
    filter_upwards [ht, eventually_ge_atTop 1] with n hn hn1
    have hrn : 0 < r ^ n := pow_pos (Real.exp_pos ε) n
    rw [div_lt_iff₀ hrn] at hn
    have h1 : ((n : ℝ) + 1) ^ d ≤ (2 * n) ^ d := by
      gcongr
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have h2 : (C : ℝ) * ((n : ℝ) + 1) ^ d ≤ r ^ n := by
      calc (C : ℝ) * ((n : ℝ) + 1) ^ d ≤ C * (2 * n) ^ d := by gcongr
        _ = C * 2 ^ d * n ^ d := by ring
        _ ≤ K * n ^ d := by gcongr; linarith
        _ ≤ r ^ n := by
          have := mul_lt_mul_of_pos_left hn hKpos
          rw [mul_inv_cancel_left₀ hKpos.ne'] at this
          linarith
    rw [← ENNReal.ofReal_pow (Real.exp_pos ε).le, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact h2)
  calc expGrowthSup (fun n => ((C * (n + 1) ^ d : ℕ) : ℝ≥0∞))
      ≤ expGrowthSup (fun n => ENNReal.ofReal r ^ n) := expGrowthSup_eventually_monotone hev
    _ = ENNReal.log (ENNReal.ofReal r) := expGrowthSup_pow
    _ = ε := by rw [ENNReal.log_ofReal_of_pos (Real.exp_pos ε), Real.log_exp]

/-- **Polynomial growth ⇒ entropy `≤ 0`.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem entropy_le_zero_of_polyGrowth (h : X.PolyGrowth) : X.entropy ≤ 0 := by
  obtain ⟨C, d, hCd⟩ := h
  refine le_trans (expGrowthSup_monotone fun n => ?_) (expGrowthSup_poly_le (Fintype.card V * C) d)
  have : X.ntot n ≤ Fintype.card V * C * (n + 1) ^ d := by
    calc X.ntot n ≤ ∑ _v : V, C * (n + 1) ^ d := Finset.sum_le_sum fun v _ => hCd v n
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
  exact_mod_cast this

/-- **A lower bound from a growing subsequence**: `c^k ≤ npaths v (k N)` with `c ≥ 1` gives
entropy `≥ log c / N`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem log_div_le_entropy {v : V} {c N : ℕ} (hc : 0 < c) (hN : 0 < N)
    (h : ∀ k, c ^ k ≤ X.npaths v (k * N)) :
    ((Real.log c / N : ℝ) : EReal) ≤ X.entropy := by
  refine Frequently.le_expGrowthSup (frequently_atTop.2 fun m => ⟨m * N, ?_, ?_⟩)
  · exact Nat.le_mul_of_pos_right m hN
  · have he : ((Real.log c / N : ℝ) : EReal) * ((m * N : ℕ) : EReal) = ((m * Real.log c : ℝ)) := by
      rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_mul]
      congr 1
      push_cast
      field_simp
    have h2 : Real.exp (m * Real.log c) = ((c ^ m : ℕ) : ℝ) := by
      rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hc)]
      push_cast
      rfl
    rw [he, EReal.exp_coe, h2, ENNReal.ofReal_natCast]
    exact_mod_cast (h m).trans (npaths_le_ntot v _)

/-- **Branching ⇒ positive entropy**: `2^k ≤ npaths v (k N)` gives entropy `≥ log 2 / N`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem log_two_div_le_entropy {v : V} {N : ℕ} (hN : 0 < N)
    (h : ∀ k, 2 ^ k ≤ X.npaths v (k * N)) :
    ((Real.log 2 / N : ℝ) : EReal) ≤ X.entropy := by
  exact_mod_cast log_div_le_entropy (c := 2) two_pos hN h

/-- **Entropy `≤ 0` ⟺ no labelled branching** [LM95, §4.1, Thm. 4.4.4 in counting form]. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem entropy_le_zero_iff [DecidableEq V] : X.entropy ≤ 0 ↔ X.LNoBranch := by
  refine ⟨fun h => ?_, fun h => entropy_le_zero_of_polyGrowth (polyGrowth_of_lnoBranch h)⟩
  intro v a b t u hvt hvu htv huv
  by_contra hne
  obtain ⟨N, hN, hk⟩ := pow_le_npaths_of_branch hvt hvu hne htv huv
  have h1 := (log_two_div_le_entropy hN hk).trans h
  have h2 : (0 : ℝ) < Real.log 2 / N := div_pos (Real.log_pos one_lt_two) (by exact_mod_cast hN)
  exact absurd h1 (not_le.2 (by exact_mod_cast h2))

@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem entropy_pos_iff [DecidableEq V] : 0 < X.entropy ↔ ¬ X.LNoBranch := by
  rw [← entropy_le_zero_iff, not_le]

/-! ### Eigenvector brackets -/

variable (X) in
/-- A **super-eigenvector** for the ratio `a / b` [LM95, §5.3]: `w ≥ 1` and
`b · (A w)(v) ≤ a · w(v)` at every vertex. -/
def IsSuperEigen (w : V → ℕ) (a b : ℕ) : Prop :=
  (∀ v, 1 ≤ w v) ∧ ∀ v, b * ∑ x ∈ X.arcsFrom v, w x.2 ≤ a * w v

variable (X) in
/-- A **sub-eigenvector** for the ratio `a / b`: `a · w(v) ≤ b · (A w)(v)` at every vertex. -/
def IsSubEigen (w : V → ℕ) (a b : ℕ) : Prop := ∀ v, a * w v ≤ b * ∑ x ∈ X.arcsFrom v, w x.2

omit [Fintype V] in
/-- The super-eigenvector bound on path counts: `b^n · npaths v n ≤ a^n · w v`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem pow_mul_npaths_le {w : V → ℕ} {a b : ℕ} (hw : X.IsSuperEigen w a b) :
    ∀ n v, b ^ n * X.npaths v n ≤ a ^ n * w v
  | 0, v => by simpa [npaths_zero] using hw.1 v
  | n + 1, v => by
    have ih := pow_mul_npaths_le hw n
    calc b ^ (n + 1) * X.npaths v (n + 1)
        = b * ∑ x ∈ X.arcsFrom v, b ^ n * X.npaths x.2 n := by
          rw [npaths_succ', Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ b * ∑ x ∈ X.arcsFrom v, a ^ n * w x.2 :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun x _ => ih x.2)
      _ = a ^ n * (b * ∑ x ∈ X.arcsFrom v, w x.2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ a ^ n * (a * w v) := Nat.mul_le_mul_left _ (hw.2 v)
      _ = a ^ (n + 1) * w v := by ring

omit [Fintype V] in
/-- The sub-eigenvector bound on path counts: `a^n · w v ≤ b^n · M · npaths v n` when
`w ≤ M`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem pow_mul_le_npaths {w : V → ℕ} {a b M : ℕ} (hw : X.IsSubEigen w a b)
    (hM : ∀ u, w u ≤ M) : ∀ n v, a ^ n * w v ≤ b ^ n * M * X.npaths v n
  | 0, v => by simpa [npaths_zero] using hM v
  | n + 1, v => by
    have ih := pow_mul_le_npaths hw hM n
    calc a ^ (n + 1) * w v = a ^ n * (a * w v) := by ring
      _ ≤ a ^ n * (b * ∑ x ∈ X.arcsFrom v, w x.2) := Nat.mul_le_mul_left _ (hw v)
      _ = b * ∑ x ∈ X.arcsFrom v, a ^ n * w x.2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ b * ∑ x ∈ X.arcsFrom v, b ^ n * M * X.npaths x.2 n :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun x _ => ih x.2)
      _ = b ^ (n + 1) * M * X.npaths v (n + 1) := by
          rw [npaths_succ', Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Super-eigenvector bound on the entropy** [LM95, §5.3]: `entropy ≤ log (a / b)`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem entropy_le_of_superEigen {w : V → ℕ} {a b : ℕ} (hb : 0 < b)
    (hw : X.IsSuperEigen w a b) : X.entropy ≤ ENNReal.log ((a : ℝ≥0∞) / b) := by
  set W := ∑ v, w v
  have hnat : ∀ n, b ^ n * X.ntot n ≤ a ^ n * W := fun n => by
    rw [ntot, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => pow_mul_npaths_le hw n v
  have hle : ∀ n, (X.ntot n : ℝ≥0∞) ≤ (W : ℝ≥0∞) * ((a : ℝ≥0∞) / b) ^ n := fun n => by
    rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv, ← mul_div_assoc,
      ENNReal.le_div_iff_mul_le
      (.inl (pow_ne_zero _ (by exact_mod_cast hb.ne'))) (.inl (pow_ne_top (natCast_ne_top b)))]
    have := hnat n
    exact_mod_cast (by rw [mul_comm]; exact this.trans_eq (mul_comm _ _))
  calc X.entropy ≤ expGrowthSup (fun n => ((a : ℝ≥0∞) / b) ^ n) :=
        expGrowthSup_le_of_eventually_le (natCast_ne_top W) (Eventually.of_forall hle)
    _ = _ := expGrowthSup_pow

/-- **Sub-eigenvector bound on the entropy**: `log (a / b) ≤ entropy` when `w ≠ 0`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_growth"]
theorem log_le_entropy_of_subEigen {w : V → ℕ} {a b : ℕ} (hb : 0 < b)
    (hw : X.IsSubEigen w a b) {v₀ : V} (hv₀ : 0 < w v₀) :
    ENNReal.log ((a : ℝ≥0∞) / b) ≤ X.entropy := by
  set M := Finset.univ.sup w
  have hM : ∀ u, w u ≤ M := fun u => Finset.le_sup (Finset.mem_univ u)
  have hge : ∀ n, (w v₀ : ℝ≥0∞) * ((a : ℝ≥0∞) / b) ^ n ≤ (M : ℝ≥0∞) * X.ntot n := fun n => by
    rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv, ← mul_div_assoc,
      ENNReal.div_le_iff_le_mul
      (.inl (pow_ne_zero _ (by exact_mod_cast hb.ne'))) (.inl (pow_ne_top (natCast_ne_top b)))]
    have h1 := pow_mul_le_npaths hw hM n v₀
    have h2 : a ^ n * w v₀ ≤ M * X.ntot n * b ^ n :=
      h1.trans (by
        calc b ^ n * M * X.npaths v₀ n ≤ b ^ n * M * X.ntot n :=
              Nat.mul_le_mul_left _ (npaths_le_ntot v₀ n)
          _ = M * X.ntot n * b ^ n := by ring)
    exact_mod_cast (by rw [mul_comm]; exact h2)
  calc ENNReal.log ((a : ℝ≥0∞) / b) = expGrowthSup (fun n => ((a : ℝ≥0∞) / b) ^ n) :=
        expGrowthSup_pow.symm
    _ ≤ expGrowthSup (fun n => (M : ℝ≥0∞) * X.ntot n) :=
        expGrowthSup_of_eventually_ge (by exact_mod_cast hv₀.ne') (Eventually.of_forall hge)
    _ ≤ X.entropy := expGrowthSup_le_of_eventually_le (natCast_ne_top M)
        (Eventually.of_forall fun n => le_rfl)

end entropy

end CarryGraph
