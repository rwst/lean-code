/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.OrbitBasics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# From a rank certificate to a waiting time ([Oda26] §6.2, Theorem 27)

A *rank certificate* is a finite labelled graph `H` whose vertices are partitioned into blocks,
with an integer rank `ρ` strictly increasing along edges between distinct blocks (`Q-rank`), every
block with an internal edge *periodic* — its internal edges advance a phase `h` modulo `d_B ≤ D`
and read their label off the phase (`Q-block`) — and a count `η ≤ m` of periodic blocks increasing
along inter-block edges by one at each periodic block entered (`Q-cyc`).

If an orbit segment of `⌊ξ(a/b)ⁿ + ν⌋` of length `T` lies in `H`, then
`T ≤ R·γ^m + (A + γD)·∑_{j<m} γ^j` with `R = ρ_max − 1`, `γ ≥ 1 + log_b(a/b)`,
`A ≥ log_b(P + 2 + 2|ν|)`, `P = ⌊ξ + ν⌋ ≥ b/(a−b) + |ν|`.  ([Oda26] is `ν = 0`.)

* `Oda.RankCert` — the data and conditions (Q-rank), (Q-block), (Q-cyc).
* `Oda.periodic_stay` — **Step 1**: a stay of length `ℓ` in a periodic block entered at time `u`
  ends before `γu + A + γD` (via Lemma 25 and Lemma 26).
* `Oda.waiting_time` — **[Oda26] Theorem 27**, (24).

The proof replaces the paper's bookkeeping (Steps 2–3) by the invariant
`n ≤ G(η(B), ρ(B) − 1)` with `G(e, r) = γ^e·r + (A + γD)·∑_{j<e} γ^j`, which satisfies
`G(e+1, r) = γ·G(e, r) + A + γD`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

open Finset

/-- **A rank certificate** ([Oda26] §6.2) on vertices `V` with blocks `β`; `E u c v` is an edge
`u → v` labelled by the carry `c`. -/
structure RankCert (V β : Type*) where
  E : V → ℤ → V → Prop
  blk : V → β
  ρ : β → ℕ
  per : β → Bool
  d : β → ℕ
  h : V → ℤ
  lam : β → ℤ → ℤ
  η : β → ℕ
  /-- (Q-rank) -/
  rank_step : ∀ u c v, E u c v → blk u ≠ blk v → ρ (blk u) + 1 ≤ ρ (blk v)
  /-- (Q-block): a block with an internal edge is periodic … -/
  internal_per : ∀ u c v, E u c v → blk u = blk v → per (blk u) = true
  d_pos : ∀ B, per B = true → 1 ≤ d B
  /-- … and its internal edges advance the phase and read their label from it. -/
  internal : ∀ u c v, E u c v → blk u = blk v →
    h v ≡ h u + 1 [ZMOD d (blk u)] ∧ c = lam (blk u) (h u % d (blk u))
  /-- (Q-cyc) -/
  eta_per : ∀ B, per B = true → 1 ≤ η B
  eta_step : ∀ u c v, E u c v → blk u ≠ blk v →
    η (blk u) + (if per (blk v) then 1 else 0) ≤ η (blk v)

variable {a b : ℕ} {ξ ν : ℝ}

/-- `Qₙ` is strictly increasing once `ξ ≥ b/(a−b)`. -/
theorem Qf_add_ge (hb : 0 < b) (hab : b < a) (hξ : (b : ℝ) / (a - b) ≤ ξ) (u k : ℕ) :
    Qf a b ξ ν u + k ≤ Qf a b ξ ν (u + k) := by
  have hr : (1 : ℝ) ≤ (a : ℝ) / b := by
    rw [le_div_iff₀ (by exact_mod_cast hb)]; simp only [one_mul]; exact_mod_cast hab.le
  have h0 : (0 : ℝ) ≤ ξ := le_trans (div_nonneg (by positivity)
    (by have : (b : ℝ) < a := by exact_mod_cast hab
        linarith)) hξ
  induction k with
  | zero => simp
  | succ k ih =>
    have := Qf_succ_gt (ξ := ξ) (ν := ν) hb hab (n := u + k)
      (le_trans hξ (le_mul_of_one_le_right h0 (one_le_pow₀ hr)))
    push_cast
    rw [show u + (k + 1) = u + k + 1 by ring]
    linarith

/-- **[Oda26] Theorem 27, Step 1.**  If the carries on `[u, u+ℓ)` are `d`-periodic
(`1 ≤ d ≤ D`), then `u + ℓ < γu + A + γD`. -/
theorem periodic_stay (hb : 1 < b) (hab : b < a) (hcop : Nat.Coprime a b) {P : ℤ}
    (hξ0 : (P : ℝ) ≤ ξ + ν) (hξ1 : ξ + ν < P + 1) (hP : (b : ℝ) / (a - b) + |ν| ≤ P) {γ A : ℝ}
    (hγ : 1 + Real.logb b ((a : ℝ) / b) ≤ γ) (hA : Real.logb b (P + 2 + 2 * |ν|) ≤ A)
    {D u ℓ d : ℕ}
    (hd1 : 1 ≤ d) (hdD : d ≤ D)
    (hper : ∀ i, i < ℓ - d → cf a b ξ ν (u + i + d) = cf a b ξ ν (u + i)) :
    (u : ℝ) + ℓ < γ * u + A + γ * D := by
  have hb0 : (1 : ℝ) < b := by exact_mod_cast hb
  have hab' : (b : ℝ) < a := by exact_mod_cast hab
  have hr : (1 : ℝ) < (a : ℝ) / b := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hκ : 0 < Real.logb b ((a : ℝ) / b) := Real.logb_pos hb0 hr
  have hν0 := abs_nonneg ν
  have hP0 : (0 : ℝ) < P :=
    lt_of_lt_of_le (by have := div_pos (by linarith : (0 : ℝ) < b) (by linarith : (0 : ℝ) < a - b)
                       linarith) hP
  have hA0 : 0 < A := lt_of_lt_of_le (Real.logb_pos hb0 (by linarith)) hA
  have hγ1 : 1 ≤ γ := by linarith
  have hu0 : (0 : ℝ) ≤ u := by positivity
  have hD : (d : ℝ) ≤ D := by exact_mod_cast hdD
  by_cases hdl : d ≤ ℓ
  · have hdiv := pow_dvd_of_carry_period hcop hdl hper
    have hinc := Qf_add_ge (a := a) (b := b) (ξ := ξ) (ν := ν) (by omega) hab
      (by linarith [neg_abs_le ν, le_abs_self ν])
    have h1 := hinc u d
    have h2 := hinc 0 u
    have hQ0 : Qf a b ξ ν 0 = P := by
      simp only [Qf, Z32.xInt, Z32.orb, pow_zero, mul_one]
      rw [Int.floor_eq_iff]; exact ⟨hξ0, hξ1⟩
    rw [zero_add, hQ0] at h2
    have hpos : 0 < Qf a b ξ ν (u + d) - Qf a b ξ ν u := by omega
    have hle := Int.le_of_dvd hpos hdiv
    -- `Q_{u+d} ≤ x_{u+d} + ν < (P+1+|ν|)·r^{u+d} + ν`
    have hx : (Qf a b ξ ν (u + d) : ℝ) ≤ ξ * ((a : ℝ) / b) ^ (u + d) + ν := by
      have := Int.floor_le (Z32.orb a b ξ ν (u + d))
      simpa only [Qf, Z32.xInt, Z32.orb] using this
    have hrpow : (0 : ℝ) < ((a : ℝ) / b) ^ (u + d) := by positivity
    have hrge : (1 : ℝ) ≤ ((a : ℝ) / b) ^ (u + d) := one_le_pow₀ hr.le
    have hQu : (P : ℝ) ≤ Qf a b ξ ν u := by
      have : P ≤ Qf a b ξ ν u := by omega
      exact_mod_cast this
    have hmain : (b : ℝ) ^ (ℓ - d) < (P + 2 + 2 * |ν|) * ((a : ℝ) / b) ^ (u + d) := by
      have h3 : ((b : ℤ) ^ (ℓ - d) : ℤ) ≤ Qf a b ξ ν (u + d) - Qf a b ξ ν u := hle
      have h3' : (b : ℝ) ^ (ℓ - d) ≤ (Qf a b ξ ν (u + d) : ℝ) - Qf a b ξ ν u := by exact_mod_cast h3
      have : ξ * ((a : ℝ) / b) ^ (u + d) ≤ (P + 1 + |ν|) * ((a : ℝ) / b) ^ (u + d) :=
        mul_le_mul_of_nonneg_right (by linarith [neg_abs_le ν]) hrpow.le
      have h4 : |ν| ≤ |ν| * ((a : ℝ) / b) ^ (u + d) := le_mul_of_one_le_right hν0 hrge
      nlinarith [le_abs_self ν]
    have hlog := Real.logb_lt_logb hb0 (by positivity) hmain
    rw [Real.logb_pow, Real.logb_self_eq_one hb0, Real.logb_mul (by linarith) hrpow.ne',
      Real.logb_pow] at hlog
    have hcast : ((ℓ - d : ℕ) : ℝ) = (ℓ : ℝ) - d := by rw [Nat.cast_sub hdl]
    rw [hcast] at hlog
    push_cast at hlog
    -- `ℓ − d < A + (u + d)κ`, then `κ ≤ γ − 1`, `d(1+κ) ≤ γD`
    have k1 : (u : ℝ) * Real.logb b ((a : ℝ) / b) ≤ u * (γ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hu0
    have k2 : (d : ℝ) * (1 + Real.logb b ((a : ℝ) / b)) ≤ D * γ :=
      mul_le_mul hD hγ (by linarith) (by positivity)
    nlinarith
  · push Not at hdl
    have : (ℓ : ℝ) < d := by exact_mod_cast hdl
    have k1 : (u : ℝ) ≤ γ * u := le_mul_of_one_le_left hu0 hγ1
    have k2 : (D : ℝ) ≤ γ * D := le_mul_of_one_le_left (by positivity) hγ1
    linarith

/-! ## The potential `G` -/

/-- `G(e, r) = γ^e·r + K·∑_{j<e} γ^j`. -/
noncomputable def Gpot (γ K : ℝ) (e : ℕ) (r : ℝ) : ℝ := γ ^ e * r + K * ∑ j ∈ range e, γ ^ j

theorem Gpot_succ (γ K : ℝ) (e : ℕ) (r : ℝ) :
    Gpot γ K (e + 1) r = γ * Gpot γ K e r + K := by
  simp only [Gpot, sum_range_succ', pow_succ, pow_zero, mul_add, mul_sum]
  ring_nf

theorem Gpot_nonneg {γ K : ℝ} (hγ : 1 ≤ γ) (hK : 0 ≤ K) (e : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ Gpot γ K e r := by
  unfold Gpot
  have : 0 ≤ ∑ j ∈ range e, γ ^ j := sum_nonneg fun j _ => by positivity
  positivity

theorem Gpot_mono {γ K : ℝ} (hγ : 1 ≤ γ) (hK : 0 ≤ K) {e e' : ℕ} (he : e ≤ e') {r r' : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ r') : Gpot γ K e r ≤ Gpot γ K e' r' := by
  have hstep : ∀ k, Gpot γ K k r ≤ Gpot γ K (k + 1) r := by
    intro k
    rw [Gpot_succ]
    have := Gpot_nonneg hγ hK k hr0
    nlinarith
  calc Gpot γ K e r ≤ Gpot γ K e' r := monotone_nat_of_le_succ hstep he
    _ ≤ Gpot γ K e' r' := by
      unfold Gpot
      have : 0 ≤ γ ^ e' := by positivity
      nlinarith

theorem Gpot_add_one {γ K : ℝ} (hγ : 1 ≤ γ) (e : ℕ) (r : ℝ) :
    Gpot γ K e r + 1 ≤ Gpot γ K e (r + 1) := by
  unfold Gpot
  have := one_le_pow₀ (n := e) hγ
  nlinarith

/-- **[Oda26] Theorem 27 (waiting time from a rank certificate).**  Let `a > b > 1` be coprime,
`P = ⌊ξ⌋ ≥ b/(a−b)`, `γ ≥ 1 + log_b(a/b)`, `A ≥ log_b(P+2)`, and let `H` be a rank certificate with
`ρ ∈ [1, ρ_max]`, `d_B ≤ D` and `η ≤ m`.  If an orbit segment of length `T` lies in `H`
(states `σ 0, …, σ T`, the `n`-th edge labelled by the carry `cₙ`), then
`T ≤ (ρ_max − 1)·γ^m + (A + γD)·∑_{j<m} γ^j`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_waiting"]
theorem waiting_time {V β : Type*} [DecidableEq β] (H : RankCert V β) (hb : 1 < b) (hab : b < a)
    (hcop : Nat.Coprime a b) {P : ℤ} (hξ0 : (P : ℝ) ≤ ξ + ν) (hξ1 : ξ + ν < P + 1)
    (hP : (b : ℝ) / (a - b) + |ν| ≤ P) {γ A : ℝ} (hγ : 1 + Real.logb b ((a : ℝ) / b) ≤ γ)
    (hA : Real.logb b (P + 2 + 2 * |ν|) ≤ A) {ρmax D m : ℕ} (hρ1 : ∀ B, 1 ≤ H.ρ B)
    (hρ : ∀ B, H.ρ B ≤ ρmax) (hD : ∀ B, H.per B = true → H.d B ≤ D) (hm : ∀ B, H.η B ≤ m)
    {σ : ℕ → V} {T : ℕ} (hwalk : ∀ n < T, H.E (σ n) (cf a b ξ ν n) (σ (n + 1))) :
    (T : ℝ) ≤ Gpot γ (A + γ * D) m (ρmax - 1 : ℕ) := by
  have hb0 : (1 : ℝ) < b := by exact_mod_cast hb
  have hab' : (b : ℝ) < a := by exact_mod_cast hab
  have hr : (1 : ℝ) < (a : ℝ) / b := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hκ : 0 < Real.logb b ((a : ℝ) / b) := Real.logb_pos hb0 hr
  have hν0 := abs_nonneg ν
  have hP0 : (0 : ℝ) < P :=
    lt_of_lt_of_le (by have := div_pos (by linarith : (0 : ℝ) < b) (by linarith : (0 : ℝ) < a - b)
                       linarith) hP
  have hA0 : 0 < A := lt_of_lt_of_le (Real.logb_pos hb0 (by linarith)) hA
  have hγ1 : 1 ≤ γ := by linarith
  have hK : 0 ≤ A + γ * D := by positivity
  set G := Gpot γ (A + γ * D) with hG
  let B : ℕ → β := fun n => H.blk (σ n)
  let pr : β → ℕ := fun B => if H.per B then 1 else 0
  -- the stay bound: from an entry `u` into a block, the time `n` obeys `n ≤ G(η, ρ−1)`
  have hderive : ∀ n u, n ≤ T → u ≤ n → (∀ k, u ≤ k → k ≤ n → B k = B n) →
      (u : ℝ) ≤ G (H.η (B n) - pr (B n)) (H.ρ (B n) - 1 : ℕ) →
      (n : ℝ) ≤ G (H.η (B n)) (H.ρ (B n) - 1 : ℕ) := by
    intro n u hnT hun hblk hu
    by_cases hper : H.per (B n) = true
    · have hη := H.eta_per _ hper
      have hpr : pr (B n) = 1 := by simp [pr, hper]
      rw [hpr] at hu
      set Bn := B n
      -- the carries on `[u, n)` read off the phase, hence are `d`-periodic
      have hint : ∀ k, u ≤ k → k < n → H.E (σ k) (cf a b ξ ν k) (σ (k + 1)) ∧
          H.blk (σ k) = H.blk (σ (k + 1)) := fun k h1 h2 =>
        ⟨hwalk k (by omega), by
          have e1 := hblk k h1 (by omega); have e2 := hblk (k + 1) (by omega) (by omega)
          simp only [B] at e1 e2; rw [e1, e2]⟩
      set dd := H.d Bn
      have hphase : ∀ i, u + i ≤ n → H.h (σ (u + i)) ≡ H.h (σ u) + i [ZMOD dd] := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ih =>
          intro hi
          obtain ⟨hE, hbk⟩ := hint (u + i) (by omega) (by omega)
          have h1 := (H.internal _ _ _ hE hbk).1
          have hb' : H.blk (σ (u + i)) = Bn := hblk (u + i) (by omega) (by omega)
          rw [hb'] at h1
          rw [← add_assoc]
          push_cast
          exact h1.trans ((ih (by omega)).add_right 1) |>.trans (by rw [add_assoc])
      have hcarry : ∀ i, u + i < n → cf a b ξ ν (u + i) = H.lam Bn ((H.h (σ u) + i) % dd) := by
        intro i hi
        obtain ⟨hE, hbk⟩ := hint (u + i) (by omega) hi
        have h2 := (H.internal _ _ _ hE hbk).2
        have hb' : H.blk (σ (u + i)) = Bn := hblk (u + i) (by omega) (by omega)
        rw [hb'] at h2
        rw [h2, hphase i hi.le]
      have hd1 := H.d_pos _ hper
      have hstay := periodic_stay (ℓ := n - u) (u := u) (d := dd) hb hab hcop hξ0 hξ1 hP hγ hA
        hd1 (hD _ hper) (fun i hi => by
          rw [hcarry i (by omega), show u + i + dd = u + (i + dd) by ring, hcarry (i + dd) (by omega)]
          congr 1
          push_cast
          rw [show H.h (σ u) + ((i : ℤ) + dd) = H.h (σ u) + i + dd * 1 by ring, Int.add_mul_emod_self_left])
      have hcast : ((u : ℕ) : ℝ) + ((n - u : ℕ) : ℝ) = n := by
        rw [Nat.cast_sub hun]; ring
      rw [hcast] at hstay
      have hη' : H.η Bn = (H.η Bn - 1) + 1 := by omega
      rw [hη', show G (H.η Bn - 1 + 1) (H.ρ Bn - 1 : ℕ) =
        γ * G (H.η Bn - 1) (H.ρ Bn - 1 : ℕ) + (A + γ * D) from Gpot_succ _ _ _ _]
      have : γ * u ≤ γ * G (H.η Bn - 1) (H.ρ Bn - 1 : ℕ) := mul_le_mul_of_nonneg_left hu (by linarith)
      linarith
    · have hn : n = u := by
        by_contra hne
        obtain hlt : u < n := lt_of_le_of_ne hun (Ne.symm hne)
        have e1 := hblk u le_rfl hun
        have e2 := hblk (u + 1) (by omega) (by omega)
        have := H.internal_per _ _ _ (hwalk u (by omega)) (by simp only [B] at e1 e2; rw [e1, e2])
        simp only [B] at e1
        rw [e1] at this
        exact hper this
      have hpr : pr (B n) = 0 := by simp [pr, hper]
      rw [hpr, Nat.sub_zero] at hu
      have : (n : ℝ) = u := by rw [hn]
      rw [this]; exact hu
  -- the invariant
  have hinv : ∀ n ≤ T, ∃ u ≤ n, (∀ k, u ≤ k → k ≤ n → B k = B n) ∧
      (u : ℝ) ≤ G (H.η (B n) - pr (B n)) (H.ρ (B n) - 1 : ℕ) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, le_rfl, fun k h1 h2 => by rw [show k = 0 by omega], ?_⟩
      simpa using Gpot_nonneg hγ1 hK _ (Nat.cast_nonneg _)
    | succ n ih =>
      intro hn
      obtain ⟨u, hun, hblk, hu⟩ := ih (by omega)
      have hE := hwalk n (by omega)
      by_cases hsame : B (n + 1) = B n
      · refine ⟨u, by omega, fun k h1 h2 => ?_, by rw [hsame]; exact hu⟩
        rcases (show k ≤ n ∨ k = n + 1 by omega) with hk | hk
        · rw [hblk k h1 hk, hsame]
        · rw [hk]
      · refine ⟨n + 1, le_rfl, fun k h1 h2 => by rw [show k = n + 1 by omega], ?_⟩
        have hbound := hderive n u (by omega) hun hblk hu
        have hne : H.blk (σ n) ≠ H.blk (σ (n + 1)) := fun h => hsame (by simp only [B]; rw [h])
        have hρs := H.rank_step _ _ _ hE hne
        have hηs := H.eta_step _ _ _ hE hne
        have hρn := hρ1 (B n)
        simp only [B] at hρs hηs hρn hbound ⊢
        calc ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
          _ ≤ G (H.η (H.blk (σ n))) ((H.ρ (H.blk (σ n)) - 1 : ℕ) + 1) := by
            have := Gpot_add_one (K := A + γ * D) hγ1 (H.η (H.blk (σ n)))
              ((H.ρ (H.blk (σ n)) - 1 : ℕ) : ℝ)
            linarith
          _ ≤ _ := by
            refine Gpot_mono hγ1 hK ?_ (by positivity) ?_
            · simp only [pr]; split_ifs at hηs ⊢ <;> omega
            · have : (H.ρ (H.blk (σ n)) - 1 : ℕ) + 1 ≤ (H.ρ (H.blk (σ (n + 1))) - 1 : ℕ) := by
                omega
              exact_mod_cast this
  obtain ⟨u, hun, hblk, hu⟩ := hinv T le_rfl
  have hfin := hderive T u le_rfl hun hblk hu
  refine le_trans hfin (Gpot_mono hγ1 hK (hm _) (Nat.cast_nonneg _) ?_)
  have : H.ρ (B T) - 1 ≤ ρmax - 1 := by have := hρ (B T); omega
  exact_mod_cast this

end Oda
