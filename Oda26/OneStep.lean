/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.WordGraph
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# One-step outer graphs and finite certification ([Oda26] §3)

States `(q, j)`: a residue `q` mod `M` and a cell `j < K`.  The one-step graph `G_K(W)` on a set
`W` of states has an edge `(q, j) —e→ (z, k)` iff, with `δ = (a − b)ν` for the shift `ν`,
(E1) `−b < e + δ < a`, (E2) `bz ≡ aq + e (mod M)`, (E3) `aj − b(k+1) < (e + δ)K < a(j+1) − bk`.
The orbit state is `σ_K(n) = (Qₙ mod M, ⌊Kθₙ⌋)` with `Qₙ = ⌊ξ(a/b)ⁿ + ν⌋`.  At `ν = 0` these are
the integer conditions `1 − b ≤ e ≤ a − 1`, `aj − b(k+1) < eK < a(j+1) − bk` of [Oda26]
(`Oda.WG.oneStep_zero`); all results below hold for every shift.

* `Oda.WG.oneStep_edge` — **[Oda26] Proposition 5 (orbit inclusion)**.
* `Oda.WG.eventually_removal`, `Oda.WG.retained_tail` — **Lemma 8 (retained tail)**: a tail in `W`
  eventually lies in `R_K(W)`, the union of the cyclic components failing the phase test.
* `Oda.WG.cell_refine` — **Lemma 9 (refinement)**: `⌊fKθ⌋ = f⌊Kθ⌋ + i` with `0 ≤ i < f`.
* `Oda.WG.joint_enlargement` — **Lemma 11 (joint enlargement)**.
* `Oda.WG.finite_certification` — **Theorem 10 (finite certification)**: if the stage sets
  `U_t = R_{K_t}(W_t)`, `W_{t+1} = Refine_f(U_t)` become empty, then `gcd(Qₙ, M) > 1` infinitely
  often, for every `ξ > 0`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity

variable {V α : Type*}

/-! ## Lemma 8, abstractly -/

/-- Along a covering walk of a non-eventually-periodic word, the edges are eventually edges of the
removal `R(G)`. -/
theorem eventually_removal [Finite V] {E : Graph V α} {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α}
    {t : ℕ → ℕ} (hc : Covers E y v w t) (hy : ¬ IsEventuallyPeriodic y) :
    ∃ i₁, ∀ i, i₁ ≤ i → removal E (v i) (w i) (v (i + 1)) := by
  obtain ⟨i₁, hi₁⟩ := eventually_sameSCC hc.edge
  set S := SameSCC E (v i₁)
  have hSeq : ∀ i, i₁ ≤ i → SameSCC E (v i) = S := by
    intro i hi
    funext x
    exact propext ⟨fun hx => (hi₁ i hi).trans hx, fun hx => (hi₁ i hi).symm.trans hx⟩
  have hnc : ¬ Certified E S := fun hcert =>
    hy ((hc.shift i₁).periodic_of_certified hcert fun i => hi₁ (i₁ + i) (by omega))
  refine ⟨i₁, fun i hi => ⟨hc.edge i, (hi₁ i hi).symm.trans (hi₁ (i + 1) (by omega)), ?_⟩⟩
  rw [hSeq i hi]; exact hnc

/-- `R(W)`: the vertices with an out-edge in the removal (= the union of the uncertified cyclic
components). -/
def Rset (E : Graph V α) (x : V) : Prop := ∃ w x', removal E x w x'

/-! ## The one-step graph -/

variable {a b : ℕ} {ξ ν : ℝ}

/-- **The one-step graph** `G_K(W)` ([Oda26] (10)), for the shift `ν`. -/
def oneStep (a b : ℕ) (ν : ℝ) (M K : ℕ) (W : Fin M × Fin K → Prop) : Graph (Fin M × Fin K) ℤ :=
  fun x w x' => W x ∧ W x' ∧ ∃ e : ℤ, w = [e] ∧ -(b : ℝ) < e + ((a : ℝ) - b) * ν ∧
    (e : ℝ) + ((a : ℝ) - b) * ν < a ∧
    (b : ℤ) * (x'.1 : ℕ) ≡ (a : ℤ) * (x.1 : ℕ) + e [ZMOD M] ∧
    (a : ℝ) * (x.2 : ℕ) - b * ((x'.2 : ℕ) + 1) < (e + ((a : ℝ) - b) * ν) * K ∧
    (e + ((a : ℝ) - b) * ν) * K < (a : ℝ) * ((x.2 : ℕ) + 1) - b * (x'.2 : ℕ)

/-- The unshifted one-step graph in the integer form of [Oda26] (10). -/
theorem oneStep_zero {M K : ℕ} {W : Fin M × Fin K → Prop} {x x' : Fin M × Fin K} {w : List ℤ} :
    oneStep a b 0 M K W x w x' ↔ W x ∧ W x' ∧ ∃ e : ℤ, w = [e] ∧ 1 - (b : ℤ) ≤ e ∧
      e ≤ (a : ℤ) - 1 ∧ (b : ℤ) * (x'.1 : ℕ) ≡ (a : ℤ) * (x.1 : ℕ) + e [ZMOD M] ∧
      (a : ℤ) * (x.2 : ℕ) - b * ((x'.2 : ℕ) + 1) < e * K ∧
      e * K < (a : ℤ) * ((x.2 : ℕ) + 1) - b * (x'.2 : ℕ) := by
  simp only [oneStep, mul_zero, add_zero]
  refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun e =>
    and_congr_right fun _ => ?_
  have c1 : -(b : ℝ) < e ↔ 1 - (b : ℤ) ≤ e := by
    rw [show (1 - (b : ℤ) ≤ e) ↔ (-(b : ℤ) < e) by omega]; exact_mod_cast Iff.rfl
  have c2 : (e : ℝ) < a ↔ e ≤ (a : ℤ) - 1 := by
    rw [show (e ≤ (a : ℤ) - 1) ↔ (e < (a : ℤ)) by omega]; exact_mod_cast Iff.rfl
  rw [c1, c2]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The residue `Q mod M` as an element of `Fin M`. -/
def res (M : ℕ) (hM : 0 < M) (Q : ℤ) : Fin M :=
  ⟨(Q % M).toNat, by
    have h1 := Int.emod_nonneg Q (show (M : ℤ) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos Q (show (0 : ℤ) < M by omega)
    omega⟩

theorem res_val (M : ℕ) (hM : 0 < M) (Q : ℤ) : ((res M hM Q : ℕ) : ℤ) = Q % M := by
  simp only [res]
  exact Int.toNat_of_nonneg (Int.emod_nonneg Q (show (M : ℤ) ≠ 0 by omega))

/-- **The orbit state** `σ_K(n) = (Qₙ mod M, ⌊Kθₙ⌋)`. -/
noncomputable def state (a b M K : ℕ) (hM : 0 < M) (hK : 0 < K) (ξ ν : ℝ) (n : ℕ) : Fin M × Fin K :=
  (res M hM (Qf a b ξ ν n), cell a b K hK ξ ν n)

theorem cell_val (K : ℕ) (hK : 0 < K) (n : ℕ) :
    ((cell a b K hK ξ ν n : ℕ) : ℝ) ≤ K * θf a b ξ ν n ∧
      K * θf a b ξ ν n < (cell a b K hK ξ ν n : ℕ) + 1 := by
  have h0 := Int.fract_nonneg (Z32.orb a b ξ ν n)
  have hnn : 0 ≤ ⌊(K : ℝ) * θf a b ξ ν n⌋ := Int.floor_nonneg.2 (by positivity)
  have hcast : (((cell a b K hK ξ ν n : ℕ) : ℤ) : ℝ) = (⌊(K : ℝ) * θf a b ξ ν n⌋ : ℝ) := by
    simp only [cell]; rw [Int.toNat_of_nonneg hnn]
  push_cast at hcast
  rw [hcast]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- **[Oda26] Proposition 5 (orbit inclusion).**  If `σ_K(n), σ_K(n+1) ∈ W`, then
`σ_K(n) —cₙ→ σ_K(n+1)` is an edge of `G_K(W)`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_onestep"]
theorem oneStep_edge (ha : 0 < a) (hb : 0 < b) {M K : ℕ} (hM : 0 < M) (hK : 0 < K)
    {W : Fin M × Fin K → Prop} (n : ℕ) (hW : W (state a b M K hM hK ξ ν n))
    (hW' : W (state a b M K hM hK ξ ν (n + 1))) :
    oneStep a b ν M K W (state a b M K hM hK ξ ν n) [cf a b ξ ν n]
      (state a b M K hM hK ξ ν (n + 1)) := by
  have hcf := cf_eq (a := a) (b := b) (ξ := ξ) (ν := ν) hb n
  have hcd : (cf a b ξ ν n : ℝ) + ((a : ℝ) - b) * ν = a * θf a b ξ ν n - b * θf a b ξ ν (n + 1) := by
    rw [hcf]; ring
  have hθ0 := Int.fract_nonneg (Z32.orb a b ξ ν n)
  have hθ1 := Int.fract_lt_one (Z32.orb a b ξ ν n)
  have hθ0' := Int.fract_nonneg (Z32.orb a b ξ ν (n + 1))
  have hθ1' := Int.fract_lt_one (Z32.orb a b ξ ν (n + 1))
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  change 0 ≤ θf a b ξ ν n at hθ0
  change θf a b ξ ν n < 1 at hθ1
  change 0 ≤ θf a b ξ ν (n + 1) at hθ0'
  change θf a b ξ ν (n + 1) < 1 at hθ1'
  refine ⟨hW, hW', cf a b ξ ν n, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcd]; nlinarith
  · rw [hcd]; nlinarith
  · simp only [state, res_val]
    have h := b_mul_Qf_succ (a := a) (b := b) (ξ := ξ) (ν := ν) n
    have e1 := (Int.mod_modEq (Qf a b ξ ν (n + 1)) M).mul_left (b : ℤ)
    have e2 := ((Int.mod_modEq (Qf a b ξ ν n) M).mul_left (a : ℤ)).add_right (cf a b ξ ν n)
    rw [h] at e1
    exact e1.trans e2.symm
  · have h1 := cell_val (a := a) (b := b) (ξ := ξ) (ν := ν) K hK n
    have h2 := cell_val (a := a) (b := b) (ξ := ξ) (ν := ν) K hK (n + 1)
    simp only [state]; rw [hcd]
    nlinarith [mul_nonneg ha'.le (sub_nonneg.2 h1.1), mul_pos hb' (sub_pos.2 h2.2)]
  · have h1 := cell_val (a := a) (b := b) (ξ := ξ) (ν := ν) K hK n
    have h2 := cell_val (a := a) (b := b) (ξ := ξ) (ν := ν) K hK (n + 1)
    simp only [state]; rw [hcd]
    nlinarith [mul_pos ha' (sub_pos.2 h1.2), mul_nonneg hb'.le (sub_nonneg.2 h2.1)]

/-- **[Oda26] Lemma 8 (retained tail).**  If `σ_K(n) ∈ W` for all large `n`, then
`σ_K(n) ∈ R_K(W)` for all large `n`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_onestep"]
theorem retained_tail (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) (hξ : ξ ≠ 0)
    {M K : ℕ} (hM : 0 < M) (hK : 0 < K) {W : Fin M × Fin K → Prop} {n₀ : ℕ}
    (hW : ∀ n, n₀ ≤ n → W (state a b M K hM hK ξ ν n)) :
    ∃ n₁, ∀ n, n₁ ≤ n → Rset (oneStep a b ν M K W) (state a b M K hM hK ξ ν n) := by
  have hc : Covers (oneStep a b ν M K W) (cf a b ξ ν) (fun i => state a b M K hM hK ξ ν (n₀ + i))
      (fun i => [cf a b ξ ν (n₀ + i)]) (fun i => n₀ + i) :=
    ⟨fun i => oneStep_edge (by omega) (by omega) hM hK _ (hW _ (by omega)) (hW _ (by omega)),
      fun i => by simp, fun i => by simp; ring, fun i => by simp [List.range'_succ]⟩
  obtain ⟨i₁, hi₁⟩ := eventually_removal hc
    (Z32.not_isEventuallyPeriodic_carry (p := a) (q := b) (ν := ν) (by omega) hab hcop hξ)
  refine ⟨n₀ + i₁, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = n₀ + i := ⟨n - n₀, by omega⟩
  exact ⟨_, _, hi₁ i (by omega)⟩

/-- **[Oda26] Lemma 9 (refinement).**  `⌊fKθ⌋ = f·⌊Kθ⌋ + i` with `0 ≤ i < f`: the refined cell
divided by `f` is the coarse cell. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_onestep"]
theorem cell_refine {K K' f : ℕ} (hK : 0 < K) (hK' : 0 < K') (hf : 0 < f) (hKK : K' = f * K)
    (n : ℕ) : (cell a b K' hK' ξ ν n : ℕ) / f = (cell a b K hK ξ ν n : ℕ) := by
  have h0 := Int.fract_nonneg (Z32.orb a b ξ ν n)
  change 0 ≤ θf a b ξ ν n at h0
  have e : ∀ L (hL : 0 < L), (cell a b L hL ξ ν n : ℕ) = ⌊(L : ℝ) * θf a b ξ ν n⌋₊ := by
    intro L hL
    simp only [cell]
    exact Int.floor_toNat _
  rw [e, e, ← Nat.floor_div_natCast, hKK]
  congr 1
  push_cast
  field_simp

/-- **[Oda26] Lemma 11 (joint enlargement).**  With `M' = hM`, `K' = fK`: if `σ_K(n) = (q, j)`
mod `M` and `gcd(Qₙ, hM) = 1`, then `σ_{K'}(n) = (q + ℓM, fj + i)` with `0 ≤ ℓ < h`, `0 ≤ i < f`,
and `gcd(q + ℓM, hM) = 1`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_onestep"]
theorem joint_enlargement {M K h f : ℕ} (hM : 0 < M) (hK : 0 < K) (hh : 0 < h) (hf : 0 < f)
    (n : ℕ) (hcop : Int.gcd (Qf a b ξ ν n) (h * M) = 1) :
    ((state a b (h * M) (f * K) (Nat.mul_pos hh hM) (Nat.mul_pos hf hK) ξ ν n).1 : ℕ) % M =
        (state a b M K hM hK ξ ν n).1 ∧
      ((state a b (h * M) (f * K) (Nat.mul_pos hh hM) (Nat.mul_pos hf hK) ξ ν n).2 : ℕ) / f =
        (state a b M K hM hK ξ ν n).2 ∧
      Nat.Coprime ((state a b (h * M) (f * K) (Nat.mul_pos hh hM) (Nat.mul_pos hf hK) ξ ν n).1)
        (h * M) := by
  refine ⟨?_, cell_refine hK (Nat.mul_pos hf hK) hf rfl n, ?_⟩
  · have e1 := res_val (h * M) (Nat.mul_pos hh hM) (Qf a b ξ ν n)
    have e2 := res_val M hM (Qf a b ξ ν n)
    simp only [state]
    have : (((res (h * M) (Nat.mul_pos hh hM) (Qf a b ξ ν n) : ℕ) % M : ℕ) : ℤ) =
        ((res M hM (Qf a b ξ ν n) : ℕ) : ℤ) := by
      push_cast
      rw [e1, e2, Nat.cast_mul, Int.emod_emod_of_dvd _ (dvd_mul_left _ _)]
    exact_mod_cast this
  · simp only [state]
    have e1 := res_val (h * M) (Nat.mul_pos hh hM) (Qf a b ξ ν n)
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 hcop
    have hco : IsCoprime ((res (h * M) (Nat.mul_pos hh hM) (Qf a b ξ ν n) : ℕ) : ℤ)
        ((h * M : ℕ) : ℤ) := by
      refine ⟨u, v + u * (Qf a b ξ ν n / ((h * M : ℕ) : ℤ)), ?_⟩
      rw [e1]
      have := Int.emod_def (Qf a b ξ ν n) ((h * M : ℕ) : ℤ)
      push_cast at this huv ⊢
      linear_combination u * this + huv
    exact Nat.isCoprime_iff_coprime.1 hco

theorem coprime_res {M : ℕ} (hM : 0 < M) {Q : ℤ} (hcop : Int.gcd Q M = 1) :
    Nat.Coprime (res M hM Q) M := by
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 hcop
  have hco : IsCoprime ((res M hM Q : ℕ) : ℤ) (M : ℤ) := by
    refine ⟨u, v + u * (Q / M), ?_⟩
    rw [res_val]
    have := Int.emod_def Q M
    linear_combination u * this + huv
  exact Nat.isCoprime_iff_coprime.1 hco

/-- The stage sets of the one-step method (modulus `M`, initial cell count `K₀`, refinement
factor `f`): `W₀ = V(M, K₀)` (residues prime to `M`), `W_{t+1} = Refine_f(R_{K_t}(W_t))`. -/
def stageW (a b : ℕ) (ν : ℝ) (M K₀ f : ℕ) : (t : ℕ) → (Fin M × Fin (K₀ * f ^ t) → Prop)
  | 0 => fun x => Nat.Coprime x.1 M
  | t + 1 => fun x => Rset (oneStep a b ν M (K₀ * f ^ t) (stageW a b ν M K₀ f t))
      (x.1, ⟨(x.2 : ℕ) / f, Nat.div_lt_of_lt_mul
        (lt_of_lt_of_eq x.2.2 (by ring : K₀ * f ^ (t + 1) = f * (K₀ * f ^ t)))⟩)

/-- `U_t = R_{K_t}(W_t)`. -/
def stageU (a b : ℕ) (ν : ℝ) (M K₀ f t : ℕ) : Fin M × Fin (K₀ * f ^ t) → Prop :=
  Rset (oneStep a b ν M (K₀ * f ^ t) (stageW a b ν M K₀ f t))

/-- **[Oda26] Theorem 10 (finite certification)**, for any shift `ν`.  If `U_s = ∅` for some `s`,
then for every `ξ > 0` and every `N` there is `n ≥ max(N, 1)` with `gcd(⌊ξ(a/b)ⁿ + ν⌋, M) > 1`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_onestep"]
theorem finite_certification (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) {M K₀ f s : ℕ}
    (hM : 0 < M) (hK₀ : 0 < K₀) (hf : 0 < f) (hU : ∀ x, ¬ stageU a b ν M K₀ f s x) :
    ∀ ξ : ℝ, 0 < ξ → ∀ N : ℕ, ∃ n, max N 1 ≤ n ∧ 1 < Int.gcd (Qf a b ξ ν n) M := by
  intro ξ hξ N
  by_contra hcon
  push Not at hcon
  have hK : ∀ t, 0 < K₀ * f ^ t := fun t => Nat.mul_pos hK₀ (pow_pos hf t)
  have hg : ∀ n, max N 1 ≤ n → Int.gcd (Qf a b ξ ν n) M = 1 := by
    intro n hn
    have h1 := hcon n hn
    have h0 : Int.gcd (Qf a b ξ ν n) M ≠ 0 := by
      rw [Ne, Int.gcd_eq_zero_iff]; intro h; have := h.2; omega
    omega
  have key : ∀ t, ∃ n₁, ∀ n, n₁ ≤ n →
      stageU a b ν M K₀ f t (state a b M (K₀ * f ^ t) hM (hK t) ξ ν n) := by
    intro t
    induction t with
    | zero =>
      exact retained_tail hb hab hcop hξ.ne' hM (hK 0) (n₀ := max N 1) fun n hn =>
        coprime_res hM (hg n hn)
    | succ t ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine retained_tail hb hab hcop hξ.ne' hM (hK (t + 1)) (n₀ := n₁) fun n hn => ?_
      simp only [stageW]
      have h := hn₁ n hn
      unfold stageU at h
      convert h using 2 <;>
        first | rfl | exact Fin.ext (cell_refine (hK t) (hK (t + 1)) hf (by ring) n)
  obtain ⟨n₁, hn₁⟩ := key s
  exact hU _ (hn₁ n₁ le_rfl)

end Oda.WG
