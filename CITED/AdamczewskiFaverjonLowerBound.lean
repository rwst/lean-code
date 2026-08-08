/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.NumberTheory.HeightTuple
import ForMathlib.NumberTheory.HeightLiouville
import CITED.AdamczewskiFaverjonRelationMatrix
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3 Step (LB): the Liouville lower bound

The arithmetic half of plan-formalize-AF17's **WP10**.  Step (UB)
(`CITED/AdamczewskiFaverjonUpperBound.lean`) shows that `E(A_k(α), α^{q^k})` is *small*; this file
shows it cannot be *too* small unless it vanishes, which is [AF22]'s (2.35):

  `|E(A_k(α), α^{q^k})| ≥ e^{-c₃ q^k δ₂}`.

Everything rests on the claim of their Appendix A.2, that the height of every coordinate of
`A_k(α)` is `O(q^k)`.

## The route, and why the obvious one fails

The recursion is `A_{k+1}(α) = A(α) · A(α^{q^k}) · ⋯`, so the coordinates of `A_k(α)` are sums of
`m` products.  Mathlib's `Height.logHeight₁_sum_le` is sharp, and applying it entry by entry
multiplies the bound by `m` at every step: `k` steps cost `m^k`, not `O(q^k)`.  [AF22] avoid this
by working place by place over the `S`-integers of a number field, where `log⁺|∑_ℓ z_ℓ|_ν` is
bounded by `log m + max_ℓ log⁺|z_ℓ|_ν` — a **maximum**, not a sum.

The Lean-native form of that maximum is the *affine height of a tuple*,
`Height.mulHeightAff`, whose local factor at a place is `max (⨆ entries) 1`
(`ForMathlib/NumberTheory/HeightTuple.lean`).  It dominates the height of every single coordinate
and it obeys `h(AB) ≤ w log m + h(A) + h(B)` — an **additive** cost per multiplication.  No
`S`-integer theory is needed, and the constant is explicit.

## Contents

* `AF.evalMatrix`, `AF.evalMatrix_iterMatrix_succ` — `A_k(α)`, and the recursion it satisfies;
* `AF.logHeightAff_evalMatrix_iterMatrix_le` — the `k`-fold product bound,
  `h(A_k(α)) ≤ k·w·log m + ∑_{j<k} h(A(α^{q^j}))`;
* `AF.exists_logHeightAff_evalMatrix_le` — the height of `A(z)` in terms of that of `z`, with the
  degree entering *linearly* (this is where `Height.mulHeight_pow_le` is used);
* **`AF.exists_logHeight₁_iterMatrix_eval_le`** — [AF22] Lemma A.1: `h(A_k(α)_{i,j}) ≤ γ q^k`;
* **`AF.logHeight₁_eval_evalPoint_le`** — [AF22] (2.33) at the point `(A_k(α), α^{q^k})`, with the
  `q^k`-coefficient *linear* in the two degrees, which is what the final contradiction needs;
* **`AF.exp_le_norm_eval_evalPoint`** — [AF22] (2.35), by Liouville's inequality;
* `AF.le_of_frequently_exp_le` — the shape of the contradiction that closes Lemma 2.11: if the
  (UB) and (LB) exponentials are compatible for infinitely many `k`, the (LB) rate dominates.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3 Step (LB), (2.32)–(2.35) and Appendix A.2 (Lemma A.1).
* [Wal00] M. Waldschmidt. *Diophantine approximation on linear algebraic groups.*  Grundlehren
  326, Springer 2000; Lemma 3.7 (= (2.33)) and p. 82 (Liouville's inequality).
* [AF17f] `plans/plan-formalize-AF17.html`: WP10, risk R15, milestone M4 (Stage 2).
-/

open Height Finset
open scoped Polynomial

namespace AF

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The matrix `A_k(α)` -/

/-- `A_k(α)`: a matrix of polynomials evaluated at a point. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def evalMatrix (z : K) (M : Matrix ι ι K[X]) : Matrix ι ι K :=
  M.map (Polynomial.evalRingHom z)

omit [NumberField K] [Fintype ι] [DecidableEq ι] in
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalMatrix_apply (z : K) (M : Matrix ι ι K[X]) (i j : ι) :
    evalMatrix z M i j = (M i j).eval z := rfl

omit [NumberField K] [Fintype ι] in
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalMatrix_one (z : K) : evalMatrix z (1 : Matrix ι ι K[X]) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [evalMatrix_apply, Matrix.one_apply, h]

omit [NumberField K] in
/-- **The recursion**: `A_{k+1}(α) = A(α) · A_k(α^q)`, read off from
`AF.iterMatrix_succ` and `AF.substPow_eval`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalMatrix_iterMatrix_succ (q : ℕ) (A : Matrix ι ι K[X]) (α : K) (k : ℕ) :
    evalMatrix α (iterMatrix q A (k + 1))
      = evalMatrix α A * evalMatrix (α ^ q) (iterMatrix q A k) := by
  ext i j
  rw [iterMatrix_succ, evalMatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Polynomial.eval_mul, Matrix.map_apply]
  simp only [evalMatrix_apply, substPow_eval]

/-! ## The height of `A_k(α)` -/

/-- The `k`-fold product bound: each multiplication costs one additive
`totalWeight K * log m`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem logHeightAff_evalMatrix_iterMatrix_le [Nonempty ι] (q : ℕ) (A : Matrix ι ι K[X]) (k : ℕ) :
    ∀ α : K, Matrix.logHeightAff (evalMatrix α (iterMatrix q A k))
      ≤ k * (totalWeight K * Real.log (Fintype.card ι))
        + ∑ j ∈ Finset.range k, Matrix.logHeightAff (evalMatrix (α ^ q ^ j) A) := by
  induction k with
  | zero => intro α; simp [iterMatrix_zero, evalMatrix_one]
  | succ n ih =>
    intro α
    have hpow : ∀ j : ℕ, (α ^ q) ^ q ^ j = α ^ q ^ (j + 1) := by
      intro j; rw [← pow_mul, pow_succ']
    have h := ih (α ^ q)
    simp only [hpow] at h
    rw [evalMatrix_iterMatrix_succ]
    refine (Matrix.logHeightAff_mul_le _ _).trans ?_
    rw [Finset.sum_range_succ' (fun j ↦ Matrix.logHeightAff (evalMatrix (α ^ q ^ j) A)) n]
    simp only [pow_zero, pow_one]
    push_cast
    linarith

omit [DecidableEq ι] in
/-- The affine height of `A(z)` in terms of that of `z`: the degree enters **linearly**, with a
constant depending on `A` alone.  The proof is Mathlib's linear-map height bound applied to the
tuple of powers `(1, z, …, z^D)`, whose height is `mulHeight₁ z ^ D`
(`Height.mulHeight_pow_le`). -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_logHeightAff_evalMatrix_le (A : Matrix ι ι K[X]) {D : ℕ}
    (hD : ∀ i j, (A i j).natDegree ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : K,
      Matrix.logHeightAff (evalMatrix z A) ≤ C + D * logHeight₁ z := by
  classical
  set Cmat : Option (ι × ι) × Fin (D + 1) → K :=
    fun p ↦ p.1.elim (if (p.2 : ℕ) = 0 then 1 else 0) fun s ↦ (A s.1 s.2).coeff (p.2 : ℕ)
    with hCdef
  have hpos : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) ^ totalWeight K * mulHeight Cmat := by
    have := mulHeight_pos Cmat
    positivity
  have hone : (1 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) ^ totalWeight K * mulHeight Cmat :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 D))
      (one_le_mulHeight _)
  refine ⟨Real.log (((D + 1 : ℕ) : ℝ) ^ totalWeight K * mulHeight Cmat), Real.log_nonneg hone,
    fun z ↦ ?_⟩
  set x : Fin (D + 1) → K := fun n ↦ z ^ (n : ℕ) with hxdef
  have hval : (fun o : Option (ι × ι) ↦ ∑ n : Fin (D + 1), Cmat (o, n) * x n)
      = fun o : Option (ι × ι) ↦ o.elim 1 fun s ↦ evalMatrix z A s.1 s.2 := by
    ext o
    cases o with
    | none =>
      simp only [hCdef, hxdef, Option.elim_none]
      rw [Finset.sum_eq_single (0 : Fin (D + 1))]
      · simp
      · intro b _ hb
        simp [Fin.val_eq_zero_iff.not.mpr hb]
      · simp
    | some s =>
      simp only [hCdef, hxdef, Option.elim_some, evalMatrix_apply]
      rw [Fin.sum_univ_eq_sum_range fun n ↦ (A s.1 s.2).coeff n * z ^ n]
      exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hD s.1 s.2)) z).symm
  have hlin := mulHeight_linearMap_apply_le Cmat x
  rw [hval] at hlin
  have hx : mulHeight x ≤ mulHeight₁ z ^ D := mulHeight_pow_le z D
  have hcard : (Nat.card (Fin (D + 1)) : ℝ) = ((D + 1 : ℕ) : ℝ) := by simp
  rw [hcard] at hlin
  have hmain : Matrix.mulHeightAff (evalMatrix z A)
      ≤ (((D + 1 : ℕ) : ℝ) ^ totalWeight K * mulHeight Cmat) * mulHeight₁ z ^ D := by
    exact hlin.trans (mul_le_mul_of_nonneg_left hx hpos.le)
  rw [Matrix.logHeightAff_eq_log_mulHeightAff, logHeight₁_eq_log_mulHeight₁]
  refine (Real.log_le_log (Matrix.mulHeightAff_pos _) hmain).trans_eq ?_
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow]

/-- **[AF22] Lemma A.1**: the height of every coordinate of `A_k(α)` is `O(q^k)`, with a constant
independent of `k`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exists_logHeight₁_iterMatrix_eval_le [Nonempty ι] {q : ℕ} (hq : 2 ≤ q)
    (A : Matrix ι ι K[X]) {D : ℕ} (hD : ∀ i j, (A i j).natDegree ≤ D) (α : K) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (k : ℕ) (i j : ι),
      logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_logHeightAff_evalMatrix_le A hD
  set L : ℝ := totalWeight K * Real.log (Fintype.card ι) with hL
  have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos.nat_succ_le
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hcard1)
  -- the geometric sum
  have hgeom : ∀ k : ℕ, ∑ j ∈ Finset.range k, ((q : ℝ) ^ j) ≤ (q : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ihn =>
      rw [Finset.sum_range_succ]
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hqn : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
      calc ∑ j ∈ Finset.range n, ((q : ℝ) ^ j) + (q : ℝ) ^ n
          ≤ (q : ℝ) ^ n + (q : ℝ) ^ n := by linarith
        _ = 2 * (q : ℝ) ^ n := by ring
        _ ≤ (q : ℝ) * (q : ℝ) ^ n := by nlinarith
        _ = (q : ℝ) ^ (n + 1) := by rw [pow_succ']
  have hklt : ∀ k : ℕ, (k : ℝ) ≤ (q : ℝ) ^ k := by
    intro k
    have h1 : (k : ℕ) < 2 ^ k := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    exact_mod_cast (h1.le.trans h2)
  refine ⟨L + C + D * logHeight₁ α,
    add_nonneg (add_nonneg hL0 hC0) (mul_nonneg (Nat.cast_nonneg D) (zero_le_logHeight₁ α)),
    fun k i j ↦ ?_⟩
  have hentry : logHeight₁ ((iterMatrix q A k i j).eval α)
      ≤ Matrix.logHeightAff (evalMatrix α (iterMatrix q A k)) := by
    rw [← evalMatrix_apply α (iterMatrix q A k) i j]
    exact Matrix.logHeight₁_le_logHeightAff (evalMatrix α (iterMatrix q A k)) i j
  refine hentry.trans ((logHeightAff_evalMatrix_iterMatrix_le q A k α).trans ?_)
  have hterm : ∀ j ∈ Finset.range k,
      Matrix.logHeightAff (evalMatrix (α ^ q ^ j) A) ≤ C + D * logHeight₁ α * (q : ℝ) ^ j := by
    intro j _
    refine (hC (α ^ q ^ j)).trans (le_of_eq ?_)
    rw [logHeight₁_pow]
    push_cast
    ring
  have hD0 : (0 : ℝ) ≤ D * logHeight₁ α :=
    mul_nonneg (Nat.cast_nonneg D) (zero_le_logHeight₁ α)
  calc (k : ℝ) * L + ∑ j ∈ Finset.range k, Matrix.logHeightAff (evalMatrix (α ^ q ^ j) A)
      ≤ (k : ℝ) * L + ∑ j ∈ Finset.range k, (C + D * logHeight₁ α * (q : ℝ) ^ j) := by
        have := Finset.sum_le_sum hterm
        linarith
    _ = (k : ℝ) * (L + C) + D * logHeight₁ α * ∑ j ∈ Finset.range k, (q : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
        ring
    _ ≤ (q : ℝ) ^ k * (L + C) + D * logHeight₁ α * (q : ℝ) ^ k :=
        add_le_add (mul_le_mul_of_nonneg_right (hklt k) (add_nonneg hL0 hC0))
          (mul_le_mul_of_nonneg_left (hgeom k) hD0)
    _ = (L + C + D * logHeight₁ α) * (q : ℝ) ^ k := by ring

/-! ## The height of `E(A_k(α), α^{q^k})`, and Liouville -/

/-- The point `(A_k(α), α^{q^k})` at which the auxiliary polynomial is evaluated: the `y`-variables
are indexed by `ι × ι` and the `z`-variable by `none`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def evalPoint (q : ℕ) (A : Matrix ι ι K[X]) (α : K) (k : ℕ) :
    Option (ι × ι) → K :=
  fun o ↦ o.elim (α ^ q ^ k) fun s ↦ (iterMatrix q A k s.1 s.2).eval α

/-- **[AF22] (2.33) at the point `(A_k(α), α^{q^k})`.**  The bound splits into a part depending on
the polynomial alone and a part proportional to `q^k` whose coefficient is **linear in the two
degrees** `dY` and `dZ` — which is exactly what the contradiction at the end of [AF22]'s Lemma 2.11
needs, since there `dY ≈ δ₁ ≤ δ₂ ≈ dZ`. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem logHeight₁_eval_evalPoint_le {q : ℕ} {A : Matrix ι ι K[X]} {α : K}
    (Q : MvPolynomial (Option (ι × ι)) K) {dY dZ : ℕ}
    (hdY : ∀ s, Q.degreeOf (some s) ≤ dY) (hdZ : Q.degreeOf none ≤ dZ)
    {γ : ℝ} (hγ : ∀ (k : ℕ) (i j : ι), logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k)
    (k : ℕ) :
    logHeight₁ (MvPolynomial.eval (evalPoint q A α k) Q)
      ≤ (totalWeight K * Real.log ((#Q.support + 1 : ℕ) : ℝ)
            + ∑ ν ∈ Q.support, logHeight₁ (Q.coeff ν))
        + ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k := by
  classical
  set d : Option (ι × ι) → ℕ := fun o ↦ o.elim dZ fun _ ↦ dY with hd
  have hdle : ∀ o, Q.degreeOf o ≤ d o := by
    intro o; cases o with
    | none => exact hdZ
    | some s => exact hdY s
  refine (logHeight₁_eval_le_of_degreeOf (evalPoint q A α k) Q hdle).trans ?_
  have hsum : ∑ o : Option (ι × ι), (d o : ℝ) * logHeight₁ (evalPoint q A α k o)
      ≤ ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k := by
    rw [Fintype.sum_option]
    have hnone : (d none : ℝ) * logHeight₁ (evalPoint q A α k none)
        = dZ * ((q : ℝ) ^ k * logHeight₁ α) := by
      simp only [hd, Option.elim_none, evalPoint, logHeight₁_pow]
      push_cast
      ring
    have hsome : ∀ s : ι × ι, (d (some s) : ℝ) * logHeight₁ (evalPoint q A α k (some s))
        ≤ dY * (γ * (q : ℝ) ^ k) := by
      intro s
      simp only [hd, Option.elim_some, evalPoint]
      exact mul_le_mul_of_nonneg_left (hγ k s.1 s.2) (by positivity)
    calc (d none : ℝ) * logHeight₁ (evalPoint q A α k none)
          + ∑ s : ι × ι, (d (some s) : ℝ) * logHeight₁ (evalPoint q A α k (some s))
        ≤ dZ * ((q : ℝ) ^ k * logHeight₁ α)
            + ∑ _s : ι × ι, (dY : ℝ) * (γ * (q : ℝ) ^ k) := by
          rw [hnone]
          have hs := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ι × ι))) ↦ hsome s
          linarith
      _ = ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  linarith

/-- If a nonzero algebraic number has logarithmic height at most `B`, then `e^{-B}` is a lower
bound for its absolute value at any complex embedding — Liouville's inequality
([Wal00] p. 82, `NumberField.neg_logHeight₁_le_log_norm`) in exponential form. -/
@[category API, AMS 11, ref "Wal00", group "af_mahler_alternative"]
theorem exp_neg_le_norm (φ : K →+* ℂ) {x : K} (hx : x ≠ 0) {B : ℝ} (hB : logHeight₁ x ≤ B) :
    Real.exp (-B) ≤ ‖φ x‖ := by
  have hxpos : 0 < ‖φ x‖ := by
    simpa using fun h ↦ hx (φ.injective (by simpa using h))
  calc Real.exp (-B) ≤ Real.exp (-logHeight₁ x) := Real.exp_le_exp.2 (by linarith)
    _ ≤ Real.exp (Real.log ‖φ x‖) :=
        Real.exp_le_exp.2 (NumberField.neg_logHeight₁_le_log_norm φ hx)
    _ = ‖φ x‖ := Real.exp_log hxpos

/-- **[AF22] (2.35)**: the lower bound of Step (LB).  The exponent is `C(Q) + c·q^k` with `c`
linear in the degrees of `Q`; combined with Step (UB)'s `e^{-c₂ q^k δ₁ δ₂}` this is what forces
`c₃ ≥ c₂ δ₁` and hence the contradiction of [AF22]'s Lemma 2.11. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem exp_le_norm_eval_evalPoint {q : ℕ} {A : Matrix ι ι K[X]} {α : K} (φ : K →+* ℂ)
    (Q : MvPolynomial (Option (ι × ι)) K) {dY dZ : ℕ}
    (hdY : ∀ s, Q.degreeOf (some s) ≤ dY) (hdZ : Q.degreeOf none ≤ dZ)
    {γ : ℝ} (hγ : ∀ (k : ℕ) (i j : ι), logHeight₁ ((iterMatrix q A k i j).eval α) ≤ γ * q ^ k)
    (k : ℕ) (hne : MvPolynomial.eval (evalPoint q A α k) Q ≠ 0) :
    Real.exp (-((totalWeight K * Real.log ((#Q.support + 1 : ℕ) : ℝ)
          + ∑ ν ∈ Q.support, logHeight₁ (Q.coeff ν))
        + ((Fintype.card (ι × ι) : ℝ) * dY * γ + dZ * logHeight₁ α) * q ^ k))
      ≤ ‖φ (MvPolynomial.eval (evalPoint q A α k) Q)‖ :=
  exp_neg_le_norm φ hne (logHeight₁_eval_evalPoint_le Q hdY hdZ hγ k)

/-- **The shape of the contradiction** at the end of [AF22]'s Lemma 2.11.  If the lower bound
`e^{-(C + a q^k)}` of Step (LB) and the upper bound `e^{-b q^k}` of Step (UB) are compatible for
infinitely many `k`, then `b ≤ a`: the `k`-free constant `C` is washed out by `q^k → ∞`.

In [AF22] this is applied with `a = c₃δ₂` and `b = c₂δ₁δ₂`, giving `c₂δ₁ ≤ c₃` with `c₂, c₃`
independent of `δ₁` — impossible once `δ₁` is large. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem le_of_frequently_exp_le {q : ℕ} (hq : 2 ≤ q) {C a b : ℝ}
    (h : ∃ᶠ k in Filter.atTop, Real.exp (-(C + a * q ^ k)) ≤ Real.exp (-(b * q ^ k))) :
    b ≤ a := by
  by_contra hba
  push Not at hba
  have hab : 0 < b - a := by linarith
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hq
  have htend : Filter.Tendsto (fun k : ℕ ↦ (q : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq1
  obtain ⟨k, hk, hkC⟩ := (h.and_eventually (htend.eventually_gt_atTop (C / (b - a)))).exists
  have hle : b * (q : ℝ) ^ k ≤ C + a * (q : ℝ) ^ k := by
    have := Real.exp_le_exp.1 hk
    linarith
  have hlt : C / (b - a) * (b - a) < (q : ℝ) ^ k * (b - a) :=
    mul_lt_mul_of_pos_right hkC hab
  rw [div_mul_cancel₀ _ hab.ne'] at hlt
  have hexp : (q : ℝ) ^ k * (b - a) = b * (q : ℝ) ^ k - a * (q : ℝ) ^ k := by ring
  rw [hexp] at hlt
  linarith

end AF
