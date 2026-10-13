/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound
import Z32.EscapeBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The rank-depth first-hit bound (plans/plan-dubC2-transform.html, T4(a))

The soundness chain of a checked certificate (`DubC2/GenCert.lean`, `DubC2/GenSound.lean`) made
quantitative.  An avoiding stretch of the orbit `xₙ = ⌊ξ(p/q)ⁿ + a/b⌋` is a path of the
certificate graph; after `J` peeling steps at either end it runs in the core and drives the det
path, whose rank drops at most `R` times (`R` = rank of the root det state).  On each
constant-rank stretch the letters are forced, so after at most `|det|` steps the carry word is
periodic, and `Z32.escape_endgame` (the quantitative [DN05] Lemma 2) bounds how long it can stay
periodic: a stretch starting at time `u` ends by `γ·u + K`, where

* `γ = 1 + log_q(p/q)` is [Oda26] Thm 27's growth factor, and
* `K = log_q(|ξ| + 1) + max(0, −log_{p/q}(|ξ|(p/q − 1)))` carries the size of `ξ` (the second
  logarithm is the small-`|ξ|` end; it vanishes once `|ξ|(p/q − 1) ≥ 1`).

Compounding over the `R + 1` stretches gives

  `N + L ≤ γ^(R+1) · (N + J + (R+1)(|det| + K + 1)) + J + 1`

for every window `[N, N + L]` on which the orbit avoids the divisor set (`Gen.window_bound`),
hence a hit in `[N, γ^(R+1)(N + J + (R+1)(|det| + K + 1)) + J + 2]` (`Gen.first_hit_rank`).
This replaces [Oda26] Thm 27's exponent `V` (the vertex count) by the rank depth `R` of the
determinized core.

* `Gen.rank_bound` — the compounding, as a statement about any rank-monotone, rank-deterministic
  sequence (no orbit, no certificate).
* `Gen.le_of_escape` — `Z32.escape_endgame`'s dichotomy in logarithmic form.
* `Gen.WinPath`, `Gen.win_mem_core`, `Gen.win_detPath_spec` — the peel/det half of
  `GenCert.lean` on a finite window.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. 251
  (2005) 635–648.
* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor
  sequences*, Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

/-! ## The compounding over constant-rank stretches -/

section Stretch

variable {S T : ℕ} {d ρ τ f g : ℕ → ℕ} {γ K o : ℝ}

theorem rank_antitone (hmono : ∀ i < T, ρ (d (i + 1)) ≤ ρ (d i)) {j k : ℕ} (hjk : j ≤ k)
    (hk : k ≤ T) : ρ (d k) ≤ ρ (d j) := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (hmono k (by omega)).trans (ih (by omega))

/-- **One constant-rank stretch.**  If the letters are forced by the det state on `[i, e]`, the
det states repeat within `S` steps, the letter word is periodic from there to `e`, and the
escape hypothesis bounds `e`. -/
theorem stretch_bound (hS : ∀ i ≤ T, d i < S)
    (hforce : ∀ i < T, ρ (d (i + 1)) = ρ (d i) → τ i = f (d i) ∧ d (i + 1) = g (d i))
    (hγ : 1 ≤ γ) (hK : 0 ≤ K) (ho : 0 ≤ o)
    (hesc : ∀ t P e : ℕ, 1 ≤ P → t + P ≤ e → e ≤ T →
      (∀ n, t ≤ n → n + P + 1 ≤ e → τ (n + P) = τ n) →
        (e : ℝ) + o ≤ γ * (((t + P : ℕ) : ℝ) + o) + K)
    {i e : ℕ} (heT : e ≤ T) (hconst : ∀ j, i ≤ j → j ≤ e → ρ (d j) = ρ (d i)) :
    (e : ℝ) + o ≤ γ * ((i : ℝ) + o + S) + K := by
  have hpos : (0 : ℝ) ≤ (i : ℝ) + o + S := by
    have : (0 : ℝ) ≤ i := i.cast_nonneg; have : (0 : ℝ) ≤ S := S.cast_nonneg; linarith
  by_cases hsmall : e < i + S
  · have : (e : ℝ) < i + S := by exact_mod_cast hsmall
    nlinarith
  push Not at hsmall
  obtain ⟨m₁, m₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (S + 1) => (⟨d (i + m), hS _ (by omega)⟩ : Fin S)) (by simp)
  simp only [Fin.mk.injEq] at heq
  wlog hlt : (m₁ : ℕ) < m₂ generalizing m₁ m₂
  · exact this m₂ m₁ hne.symm heq.symm (by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact absurd h hlt
      · exact h)
  have hm₂ : (m₂ : ℕ) ≤ S := Nat.lt_succ_iff.1 m₂.2
  have hstep : ∀ x, i ≤ x → x < e → τ x = f (d x) ∧ d (x + 1) = g (d x) := fun x hx hxe =>
    hforce x (by omega) (by rw [hconst (x + 1) (by omega) (by omega), hconst x hx (by omega)])
  have hshift : ∀ k, i + m₂ + k ≤ e → d (i + m₁ + k) = d (i + m₂ + k) := by
    intro k
    induction k with
    | zero => intro _; simpa using heq
    | succ k ih =>
      intro hk
      have e1 := (hstep (i + m₁ + k) (by omega) (by omega)).2
      have e2 := (hstep (i + m₂ + k) (by omega) (by omega)).2
      rw [show i + m₁ + (k + 1) = (i + m₁ + k) + 1 by omega,
        show i + m₂ + (k + 1) = (i + m₂ + k) + 1 by omega, e1, e2, ih (by omega)]
  have h := hesc (i + m₁) (m₂ - m₁) e (by omega) (by omega) heT (by
    intro n hn hne'
    obtain ⟨k, rfl⟩ : ∃ k, n = i + m₁ + k := ⟨n - (i + m₁), by omega⟩
    have e1 := (hstep (i + m₁ + k) (by omega) (by omega)).1
    have e2 := (hstep (i + m₂ + k) (by omega) (by omega)).1
    rw [show i + m₁ + k + (m₂ - m₁) = i + m₂ + k by omega, e1, e2, hshift k (by omega)])
  have hc : ((i + m₁ + (m₂ - m₁) : ℕ) : ℝ) ≤ (i : ℝ) + S := by
    rw [show i + m₁ + (m₂ - m₁) = i + m₂ by omega]; push_cast
    have : ((m₂ : ℕ) : ℝ) ≤ S := by exact_mod_cast hm₂
    linarith
  nlinarith

theorem aux_le (hγ : 1 ≤ γ) {X A : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (r : ℕ) :
    γ * (X + A) ≤ γ ^ (r + 1) * (X + (r + 1) * A) := by
  have h1 : γ ≤ γ ^ (r + 1) := le_self_pow₀ hγ (by omega)
  have h2 : X + A ≤ X + (r + 1) * A := by
    have : (1 : ℝ) ≤ r + 1 := by have := r.cast_nonneg (α := ℝ); linarith
    nlinarith
  exact mul_le_mul h1 h2 (by linarith) (le_trans zero_le_one (le_trans hγ h1))

/-- **The compounding.**  A det path whose rank never increases and whose letters (and next
states) are forced while the rank is kept, run on `[i, T]` with rank `≤ r` at `i`: the escape
hypothesis on each stretch gives `T + o ≤ γ^(r+1) (i + o + (r+1)(S + K + 1))`. -/
@[category API, AMS 11 37 68, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem rank_bound (hS : ∀ i ≤ T, d i < S) (hmono : ∀ i < T, ρ (d (i + 1)) ≤ ρ (d i))
    (hforce : ∀ i < T, ρ (d (i + 1)) = ρ (d i) → τ i = f (d i) ∧ d (i + 1) = g (d i))
    (hγ : 1 ≤ γ) (hK : 0 ≤ K) (ho : 0 ≤ o)
    (hesc : ∀ t P e : ℕ, 1 ≤ P → t + P ≤ e → e ≤ T →
      (∀ n, t ≤ n → n + P + 1 ≤ e → τ (n + P) = τ n) →
        (e : ℝ) + o ≤ γ * (((t + P : ℕ) : ℝ) + o) + K) :
    ∀ r i, i ≤ T → ρ (d i) ≤ r →
      (T : ℝ) + o ≤ γ ^ (r + 1) * ((i : ℝ) + o + (r + 1) * (S + K + 1)) := by
  have hA : (0 : ℝ) ≤ S + K + 1 := by have : (0 : ℝ) ≤ S := S.cast_nonneg; linarith
  -- no rank drop after `i`: one stretch up to `T`
  have nodrop : ∀ (r : ℕ) i, i ≤ T → (¬ ∃ j, i < j ∧ j ≤ T ∧ ρ (d j) < ρ (d i)) →
      (T : ℝ) + o ≤ γ ^ (r + 1) * ((i : ℝ) + o + (r + 1) * (S + K + 1)) := by
    intro r i hi hnd
    push Not at hnd
    have h := stretch_bound hS hforce hγ hK ho hesc le_rfl (i := i) fun j hj hjT =>
      le_antisymm (rank_antitone hmono hj hjT)
        (by rcases hj.lt_or_eq with h | h
            · exact hnd j h hjT
            · rw [h])
    have h2 := aux_le hγ (X := (i : ℝ) + o) (by have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith) hA r
    nlinarith
  intro r
  induction r with
  | zero =>
    intro i hi hr
    refine nodrop 0 i hi ?_
    rintro ⟨j, -, -, hj⟩
    omega
  | succ r ih =>
    intro i hi hr
    by_cases hdrop : ∃ j, i < j ∧ j ≤ T ∧ ρ (d j) < ρ (d i)
    · classical
      obtain ⟨i', hi'⟩ : ∃ i', i' = Nat.find hdrop := ⟨_, rfl⟩
      have hspec := Nat.find_spec hdrop
      rw [← hi'] at hspec
      obtain ⟨hii', hi'T, hρ⟩ := hspec
      obtain ⟨k, hk⟩ : ∃ k, i' = k + 1 := ⟨i' - 1, by omega⟩
      have hst := stretch_bound hS hforce hγ hK ho hesc (i := i) (e := k) (by omega)
        fun j hj hjk => le_antisymm (rank_antitone hmono hj (by omega)) (by
          by_contra hlt
          push Not at hlt
          rcases hj.lt_or_eq with h | h
          · exact Nat.find_min hdrop (show j < Nat.find hdrop by rw [← hi']; omega)
              ⟨h, by omega, hlt⟩
          · rw [h] at hlt; exact lt_irrefl _ hlt)
      have hIH := ih i' hi'T (by omega)
      have hk' : (i' : ℝ) = k + 1 := by exact_mod_cast hk
      have hI : (i' : ℝ) + o ≤ γ * ((i : ℝ) + o + (S + K + 1)) := by nlinarith
      have hγr : (0 : ℝ) ≤ γ ^ (r + 1) := pow_nonneg (by linarith) _
      have hrA : ((r : ℝ) + 1) * (S + K + 1) ≤ γ * (((r : ℝ) + 1) * (S + K + 1)) := by
        have : (0 : ℝ) ≤ ((r : ℝ) + 1) * (S + K + 1) := mul_nonneg (by positivity) hA
        nlinarith
      calc (T : ℝ) + o ≤ γ ^ (r + 1) * ((i' : ℝ) + o + (r + 1) * (S + K + 1)) := by
            exact hIH
        _ ≤ γ ^ (r + 1) * (γ * ((i : ℝ) + o + (S + K + 1)) +
              γ * (((r : ℝ) + 1) * (S + K + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hγr; linarith
        _ = γ ^ (r + 1 + 1) * ((i : ℝ) + o + ((r + 1 : ℕ) + 1) * (S + K + 1)) := by
            push_cast; ring
    · exact nodrop (r + 1) i hi hdrop

end Stretch

/-! ## The escape dichotomy in logarithmic form -/

section Escape

variable {p q : ℕ} {ξ : ℝ}

/-- `Z32.escape_endgame`'s two branches, at `u = t + P`, give one linear bound
`e ≤ (1 + log_q(p/q))·u + K(ξ)`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_first_hit"]
theorem le_of_escape (hq : 1 < q) (hqp : q < p) (hξ : ξ ≠ 0) {u P e : ℕ} (hPu : P ≤ u)
    (hue : u ≤ e)
    (h : ((q : ℝ) ^ (e - u) ≤ |ξ| * ((p : ℝ) / q) ^ u + 1) ∨
      (|ξ| * ((p : ℝ) / q) ^ (e - P) * ((p : ℝ) / q - 1) < 1)) :
    (e : ℝ) ≤ (1 + Real.logb q ((p : ℝ) / q)) * u +
      (Real.logb q (|ξ| + 1) + max 0 (-Real.logb ((p : ℝ) / q) (|ξ| * ((p : ℝ) / q - 1)))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
  have hb1 : (1 : ℝ) < (p : ℝ) / q := by rw [lt_div_iff₀ hq0]; linarith
  have hb0 : (0 : ℝ) < (p : ℝ) / q := by linarith
  have hξ0 : 0 < |ξ| := abs_pos.2 hξ
  have hlam : 0 ≤ Real.logb q ((p : ℝ) / q) := Real.logb_nonneg hq1 hb1.le
  have hΛ : 0 ≤ Real.logb q (|ξ| + 1) := Real.logb_nonneg hq1 (by linarith)
  have hmax := le_max_left 0 (-Real.logb ((p : ℝ) / q) (|ξ| * ((p : ℝ) / q - 1)))
  have hu0 : (0 : ℝ) ≤ u := u.cast_nonneg
  rcases h with hA | hB
  · have hbu : (1 : ℝ) ≤ ((p : ℝ) / q) ^ u := one_le_pow₀ hb1.le
    have hle : (q : ℝ) ^ (e - u) ≤ (|ξ| + 1) * ((p : ℝ) / q) ^ u := by nlinarith
    have hlog := Real.logb_le_logb_of_le hq1 (pow_pos hq0 _) hle
    rw [Real.logb_pow, Real.logb_self_eq_one hq1,
      Real.logb_mul (by positivity) (pow_pos hb0 _).ne', Real.logb_pow] at hlog
    rw [Nat.cast_sub hue] at hlog
    nlinarith
  · have hc : 0 < |ξ| * ((p : ℝ) / q - 1) := mul_pos hξ0 (by linarith)
    have hlt : ((p : ℝ) / q) ^ (e - P) < (|ξ| * ((p : ℝ) / q - 1))⁻¹ := by
      rw [lt_inv_comm₀ (pow_pos hb0 _) hc]
      rw [inv_eq_one_div, lt_div_iff₀ (pow_pos hb0 _)]
      nlinarith
    have hlog := Real.logb_lt_logb hb1 (pow_pos hb0 _) hlt
    rw [Real.logb_pow, Real.logb_self_eq_one hb1, Real.logb_inv,
      Nat.cast_sub (by omega : P ≤ e)] at hlog
    have hP : (P : ℝ) ≤ u := by exact_mod_cast hPu
    have := le_max_right 0 (-Real.logb ((p : ℝ) / q) (|ξ| * ((p : ℝ) / q - 1)))
    have := mul_nonneg hlam hu0
    nlinarith

end Escape

/-! ## The peel and the det path on a finite window -/

/-- A path of the graph on the window `[N, N + L)`. -/
structure WinPath (P : Params) (N L : ℕ) (v t : ℕ → ℕ) : Prop where
  lt : ∀ n, N ≤ n → n < N + L → v n < P.nV
  letter_lt : ∀ n, N ≤ n → n < N + L → t n < P.nA
  edge : ∀ n, N ≤ n → n + 1 < N + L → v (n + 1) ∈ P.succList (v n) (P.letter (t n))

section Window

variable {P : Params} {C : Cert} {N L : ℕ} {v t : ℕ → ℕ}

/-- `Gen.mem_A` on a window: `J` peeling rounds cost `J` steps at each end. -/
theorem win_mem_A (hc : Checked P C) (hp : WinPath P N L v t) :
    ∀ j, j ≤ C.J → ∀ n, N + j ≤ n → n + j < N + L → C.memA P j (v n) = true := by
  intro j
  induction j with
  | zero =>
    intro _ n hn hn'
    simp only [Cert.memA, ite_true, decide_eq_true_eq]
    exact hp.lt n (by omega) (by omega)
  | succ j ih =>
    intro hj n hn hn'
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (round_at hc (by omega) (ih (by omega) (m + 1) (by omega) (by omega))
      (hp.lt _ (by omega) (by omega))).2
      ⟨t (m + 1), hp.letter_lt _ (by omega) (by omega), v (m + 1 + 1),
        hp.edge _ (by omega) (by omega), ih (by omega) _ (by omega) (by omega)⟩ ?_
    exact (round_at hc (by omega) (ih (by omega) m (by omega) (by omega))
      (hp.lt _ (by omega) (by omega))).1 (t m) (hp.letter_lt m (by omega) (by omega)) _
      (hp.edge m (by omega) (by omega))

theorem win_mem_core (hc : Checked P C) (hp : WinPath P N L v t) {n : ℕ} (hn : N + C.J ≤ n)
    (hn' : n + C.J < N + L) : v n ∈ C.core := by
  obtain ⟨-, hZ, hcov, hcore, -⟩ := head_facts hc
  have hA := win_mem_A hc hp C.J le_rfl n hn hn'
  have hi : v n / C.Z < C.nB :=
    (Nat.div_lt_iff_lt_mul hZ).2 (by have := hp.lt n (by omega) (by omega); linarith)
  have h := List.all_eq_true.1 (hcore _ hi) (v n % C.Z) (mem_blk_scan hZ hA)
  rw [Nat.div_add_mod' (v n) C.Z, hA] at h
  simpa using h

theorem win_step_entry (hc : Checked P C) (hp : WinPath P N L v t) {d n : ℕ}
    (hn : N + C.J ≤ n) (hn' : n + 1 + C.J < N + L) (hd : d < C.sets.length)
    (hbit : (C.sets.getD d 0).testBit (C.core.idxOf (v n)) = true) :
    ∃ j, (C.trans.getD d []).getD (t n) none = some j ∧ j < C.sets.length ∧
      (C.sets.getD j 0).testBit (C.core.idxOf (v (n + 1))) = true ∧
        C.rank.getD j 0 ≤ C.rank.getD d 0 := by
  have hdet := List.all_eq_true.1 hc.det d (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  simp only [detOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hdet
  have hrow := hdet.1 (t n) (hp.letter_lt n (by omega) (by omega))
  have hT : (detSucc P C (C.sets.getD d 0) (P.letter (t n))).testBit (C.core.idxOf (v (n + 1)))
      = true := by
    rw [detSucc, testBit_orFold]
    refine ⟨C.core.idxOf (v n), mem_bits hbit, rfl, ?_⟩
    rw [getD_idxOf (win_mem_core hc hp hn (by omega))]
    exact testBit_succIdx (hp.edge n (by omega) (by omega))
      (win_mem_core hc hp (by omega) (by omega))
  revert hrow
  cases (C.trans.getD d []).getD (t n) none with
  | none =>
    intro hrow
    simp only [beq_iff_eq] at hrow
    exact absurd hrow (ne_zero_of_testBit hT)
  | some j =>
    intro hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact ⟨j, rfl, hrow.1.1, testBit_of_subset hrow.1.2 hT, hrow.2⟩

theorem win_detPath_spec (hc : Checked P C) (hp : WinPath P N L v t) (i : ℕ)
    (hi : N + C.J + i + C.J < N + L) :
    detPath C t (N + C.J) i < C.sets.length ∧
      (C.sets.getD (detPath C t (N + C.J) i) 0).testBit (C.core.idxOf (v (N + C.J + i))) = true := by
  induction i with
  | zero =>
    obtain ⟨hlen, -, -, -, h0⟩ := head_facts hc
    refine ⟨hlen, testBit_of_subset h0 ?_⟩
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact List.idxOf_lt_length_of_mem (win_mem_core hc hp (by omega) (by omega))
  | succ i ih =>
    have ih := ih (by omega)
    obtain ⟨j, he, hj, hb, -⟩ := win_step_entry hc hp (by omega) (by omega) ih.1 ih.2
    have hdp : detPath C t (N + C.J) (i + 1) = next C (detPath C t (N + C.J) i)
        (t (N + C.J + i)) := rfl
    rw [hdp, show N + C.J + (i + 1) = N + C.J + i + 1 by omega]
    unfold next
    rw [he]
    exact ⟨hj, hb⟩

theorem win_detPath_rank (hc : Checked P C) (hp : WinPath P N L v t) (i : ℕ)
    (hi : N + C.J + (i + 1) + C.J < N + L) :
    C.rank.getD (detPath C t (N + C.J) (i + 1)) 0 ≤ C.rank.getD (detPath C t (N + C.J) i) 0 ∧
      (C.rank.getD (detPath C t (N + C.J) (i + 1)) 0 = C.rank.getD (detPath C t (N + C.J) i) 0 →
        t (N + C.J + i) ∈ keep C P.nA (detPath C t (N + C.J) i)) := by
  obtain ⟨hi', hbit⟩ := win_detPath_spec hc hp i (by omega)
  obtain ⟨j, he, -, -, hr⟩ := win_step_entry hc hp (by omega) (by omega) hi' hbit
  have hdp : detPath C t (N + C.J) (i + 1) = next C (detPath C t (N + C.J) i)
      (t (N + C.J + i)) := rfl
  rw [hdp]
  unfold next keep
  rw [he]
  refine ⟨hr, fun h => ?_⟩
  simp only [Option.getD_some] at h
  simp only [List.mem_filter, List.mem_range, he, h, beq_self_eq_true, and_true]
  exact hp.letter_lt _ (by omega) (by omega)

end Window

/-! ## The bound -/

/-- The growth factor `γ = 1 + log_q(p/q)` of [Oda26] Thm 27. -/
noncomputable def Params.gamma (P : Params) : ℝ := 1 + Real.logb P.q ((P.p : ℝ) / P.q)

/-- The size term `K(ξ) = log_q(|ξ| + 1) + max(0, −log_{p/q}(|ξ|(p/q − 1)))`. -/
noncomputable def Params.kξ (P : Params) (ξ : ℝ) : ℝ :=
  Real.logb P.q (|ξ| + 1) +
    max 0 (-Real.logb ((P.p : ℝ) / P.q) (|ξ| * ((P.p : ℝ) / P.q - 1)))

/-- The rank depth: the rank of the root det state (every det path starts there). -/
def Cert.depth (C : Cert) : ℕ := C.rank.getD 0 0

/-- The bound of `Gen.window_bound`. -/
noncomputable def firstHitBound (P : Params) (C : Cert) (ξ : ℝ) (N : ℕ) : ℝ :=
  P.gamma ^ (C.depth + 1) * ((N : ℝ) + C.J + (C.depth + 1) * (C.sets.length + P.kξ ξ + 1)) +
    C.J + 1

variable {P : Params} {C : Cert} {ξ : ℝ}

theorem paramFacts_of_checked (hc : Checked P C) : ParamFacts P := by
  have hh := hc.head
  simp only [checkHead, Bool.and_eq_true] at hh
  exact paramFacts hh.1.1.1.1.1

theorem one_le_gamma (hF : ParamFacts P) : 1 ≤ P.gamma := by
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hq1 : (1 : ℝ) < P.q := by exact_mod_cast hF.q1
  have hqp : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hb1 : (1 : ℝ) < (P.p : ℝ) / P.q := by rw [lt_div_iff₀ hq0]; linarith
  have := Real.logb_nonneg hq1 hb1.le
  simp only [Params.gamma]; linarith

theorem kξ_nonneg (hF : ParamFacts P) : 0 ≤ P.kξ ξ := by
  have hq1 : (1 : ℝ) < P.q := by exact_mod_cast hF.q1
  have := Real.logb_nonneg hq1 (by linarith [abs_nonneg ξ] : (1 : ℝ) ≤ |ξ| + 1)
  have := le_max_left 0 (-Real.logb ((P.p : ℝ) / P.q) (|ξ| * ((P.p : ℝ) / P.q - 1)))
  simp only [Params.kξ]; linarith

theorem le_firstHitBound {N : ℕ} (hF : ParamFacts P) :
    (N : ℝ) + C.J + C.J + 1 ≤ firstHitBound P C ξ N := by
  have h1 : (1 : ℝ) ≤ P.gamma ^ (C.depth + 1) := one_le_pow₀ (one_le_gamma hF)
  have h2 : (0 : ℝ) ≤ (C.depth + 1) * (C.sets.length + P.kξ ξ + 1) := by
    have hk := kξ_nonneg (ξ := ξ) hF
    have hl : (0 : ℝ) ≤ C.sets.length := Nat.cast_nonneg _
    exact mul_nonneg (by positivity) (by linarith)
  have h3 : (0 : ℝ) ≤ (N : ℝ) + C.J := by positivity
  simp only [firstHitBound]
  nlinarith

/-- **The rank-depth window bound.**  If `xₙ = ⌊ξ(p/q)ⁿ + a/b⌋` avoids the divisor set for all
`n ∈ [N, N + L]`, then `N + L ≤ γ^(R+1)(N + J + (R+1)(|det| + K(ξ) + 1)) + J + 1`, with `R` the
rank depth of the certificate. -/
@[category research solved, AMS 11 37 68, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem window_bound (hc : Checked P C) (hξ : ξ ≠ 0) {N L : ℕ}
    (hav : ∀ n, N ≤ n → n ≤ N + L → Avoids P ξ n) :
    ((N + L : ℕ) : ℝ) ≤ firstHitBound P C ξ N := by
  have hF := paramFacts_of_checked hc
  have hγ := one_le_gamma hF
  have hK := kξ_nonneg (ξ := ξ) hF
  have hRHS := le_firstHitBound (C := C) (ξ := ξ) (N := N) hF
  -- short windows: nothing to do
  by_cases hshort : L < 2 * C.J + 1
  · have : ((N + L : ℕ) : ℝ) ≤ (N : ℝ) + C.J + C.J := by push_cast; exact_mod_cast (by omega)
    linarith
  push Not at hshort
  -- the orbit is a path on the window
  have hp : WinPath P N L (vtx P ξ) (tix P ξ) :=
    ⟨fun n hn hn' => (sound hF (hav n hn (by omega)) (hav (n + 1) (by omega) (by omega))).1,
     fun n hn hn' => (sound hF (hav n hn (by omega)) (hav (n + 1) (by omega) (by omega))).2.1,
     fun n hn hn' => (sound hF (hav n hn (by omega)) (hav (n + 1) (by omega) (by omega))).2.2.2⟩
  have hlet : ∀ n, N ≤ n → n < N + L → P.letter (tix P ξ n) = cs P ξ n := fun n hn hn' =>
    (sound hF (hav n hn (by omega)) (hav (n + 1) (by omega) (by omega))).2.2.1
  set T := L - 2 * C.J - 1 with hT
  have hspec : ∀ i ≤ T, detPath C (tix P ξ) (N + C.J) i < C.sets.length := fun i hi =>
    (win_detPath_spec hc hp i (by omega)).1
  have hkeep : ∀ i ≤ T, (keep C P.nA (detPath C (tix P ξ) (N + C.J) i)).length ≤ 1 := by
    intro i hi
    have hdet := List.all_eq_true.1 hc.det (detPath C (tix P ξ) (N + C.J) i)
      (List.mem_range'_1.2 ⟨by omega, by have := hspec i hi; omega⟩)
    simp only [detOK, Bool.and_eq_true, decide_eq_true_eq] at hdet
    exact hdet.2
  have hmain := rank_bound (S := C.sets.length) (T := T) (d := detPath C (tix P ξ) (N + C.J))
    (ρ := fun s => C.rank.getD s 0) (τ := fun i => tix P ξ (N + C.J + i))
    (f := fun s => (keep C P.nA s).headD 0)
    (g := fun s => next C s ((keep C P.nA s).headD 0))
    (γ := P.gamma) (K := P.kξ ξ) (o := (N : ℝ) + C.J) hspec
    (fun i hi => (win_detPath_rank hc hp i (by omega)).1)
    (fun i hi hr => by
      have hmem := (win_detPath_rank hc hp i (by omega)).2 hr
      have he := eq_headD_of_mem (hkeep i (by omega)) hmem
      exact ⟨he, by
        show next C (detPath C (tix P ξ) (N + C.J) i) (tix P ξ (N + C.J + i)) =
          next C (detPath C (tix P ξ) (N + C.J) i)
            ((keep C P.nA (detPath C (tix P ξ) (N + C.J) i)).headD 0)
        rw [← he]⟩)
    hγ hK (by positivity)
    (fun t₀ Pd e hP hte heT hper => by
      have hper' : ∀ n, N + C.J + t₀ ≤ n → n + Pd + 1 ≤ N + C.J + e →
          Z32.carry P.p P.q ξ P.nu (n + Pd) = Z32.carry P.p P.q ξ P.nu n := by
        intro n hn hn'
        obtain ⟨k, rfl⟩ : ∃ k, n = N + C.J + k := ⟨n - (N + C.J), by omega⟩
        have h : tix P ξ (N + C.J + (k + Pd)) = tix P ξ (N + C.J + k) :=
          hper k (by omega) (by omega)
        change cs P ξ (N + C.J + k + Pd) = cs P ξ (N + C.J + k)
        rw [← hlet (N + C.J + k + Pd) (by omega) (by omega), ← hlet (N + C.J + k) (by omega)
          (by omega), show N + C.J + k + Pd = N + C.J + (k + Pd) by omega, h]
      have hesc := Z32.escape_endgame (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu)
        (by have := hF.q1; omega) hF.pq hF.cop hP (by omega) hper'
      have hle := le_of_escape (p := P.p) (q := P.q) (ξ := ξ) hF.q1 hF.pq hξ
        (u := N + C.J + t₀ + Pd) (P := Pd) (e := N + C.J + e) (by omega) (by omega)
        (by rwa [show N + C.J + e - (N + C.J + t₀ + Pd) = N + C.J + e - (N + C.J + t₀) - Pd
          by omega])
      simp only [Params.gamma, Params.kξ]
      push_cast at hle ⊢
      linarith)
    C.depth 0 (by omega) (by
      show C.rank.getD (detPath C (tix P ξ) (N + C.J) 0) 0 ≤ C.rank.getD 0 0
      exact le_rfl)
  have hTc : ((T : ℕ) : ℝ) = (L : ℝ) - 2 * C.J - 1 := by
    have h1 : 2 * C.J ≤ L := by omega
    have h2 : 1 ≤ L - 2 * C.J := by omega
    rw [hT, Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; ring
  simp only [firstHitBound]
  push_cast at hmain ⊢
  rw [hTc] at hmain
  linarith

/-- **The rank-depth first-hit bound** (T4(a)).  For every `ξ ≠ 0` and every start `N`, some
`n ∈ [N, firstHitBound + 1]` has `xₙ = ⌊ξ(p/q)ⁿ + a/b⌋` divisible by a member of the divisor
set.  The bound is `γ^(R+1)(N + J + (R+1)(|det| + K(ξ) + 1)) + J + 2`: exponential in the rank
depth `R` of the determinized core, not in the vertex count. -/
@[category research solved, AMS 11 37 68, ref "Oda26" "DN05", group "dubc2_first_hit"]
theorem first_hit_rank (hc : Checked P C) (hξ : ξ ≠ 0) (N : ℕ) :
    ∃ n, N ≤ n ∧ (n : ℝ) ≤ firstHitBound P C ξ N + 1 ∧
      ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ ((P.a : ℝ) / P.b) n := by
  have hB := le_firstHitBound (C := C) (ξ := ξ) (N := N) (paramFacts_of_checked hc)
  set B := firstHitBound P C ξ N
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  by_contra hcon
  push Not at hcon
  have hm : B < ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one B
  have hmB : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ B + 1 := by push_cast; linarith [Nat.floor_le hB0]
  have hNm : N ≤ ⌊B⌋₊ + 1 := by
    have : (N : ℝ) < ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ C.J := C.J.cast_nonneg
      linarith
    exact_mod_cast this.le
  have h := window_bound hc hξ (N := N) (L := ⌊B⌋₊ + 1 - N) fun n hn hn' ℓ hℓ =>
    hcon n hn (le_trans (by exact_mod_cast (by omega : n ≤ ⌊B⌋₊ + 1)) hmB) ℓ hℓ
  rw [show N + (⌊B⌋₊ + 1 - N) = ⌊B⌋₊ + 1 by omega] at h
  linarith

end DubC2.Gen
