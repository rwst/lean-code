/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.TopologicalPressure
import ForMathlib.Combinatorics.PathGrowth

/-!
# Bounding the pressure by a finite-state transfer operator

`ForMathlib/Dynamics/TopologicalPressure.lean` defines the pressure `P(T, φ, P)` of a potential
along a finite partition, and `ForMathlib/Combinatorics/PathGrowth.lean` bounds the growth of the
weighted path sums of a finite labelled digraph by an elementary vector (Collatz–Wielandt)
certificate.  This file joins the two: **a potential dominated by a finite-state transfer operator
has pressure at most the growth rate of that operator.**

That is exactly the shape of every computed pressure bound.  One never evaluates
`sup_A S_n φ` cell by cell; one exhibits a finite window, reads off a transfer matrix whose entries
dominate `exp φ` on each window, and bounds its spectral radius.  The step from "the matrix has
growth rate `λ`" to "the pressure is at most `log λ`" is the content here, and it is purely
combinatorial: no analysis, no compactness, no continuity of `φ`.

## Main definitions

* `Dynamics.TransferBound T φ P V` — the data that makes the bound work: a **state observable**
  `state : α → V` into a finite set, a successor map `tgt : V → ι → V` with
  `state (T x) = tgt (state x) (P x)` (the state is driven by the partition symbol), and integer
  **edge weights** `weight : V → ι → ℕ` with `exp (φ x) ≤ weight (state x) (P x)`.
* `Dynamics.stateSum T φ P st q n` — the partition sum refined by the value of the state
  observable.  It is the intermediate object the induction runs on: `partitionSum` is recovered by
  summing over states, and each `stateSum` obeys the transfer recursion.

## Main results

* `Dynamics.partitionSum_le_of_transferBound` — `Z_n(φ, P) ≤ ∑_q psum (detE tgt) weight 1 q n`,
  the partition function is dominated by the total weight of the length-`n` paths.
* `Dynamics.partitionPressure_le_of_transferBound` — combining it with the vector certificate
  `b · (M v) ≤ a · v` of `PathGrowth`, `P(T, φ, P) ≤ log (a / b)`.  This is the statement a
  computed certificate discharges.

## References

* Bowen, R. *Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms*, LNM 470, 1975.
* Walters, P. *An Introduction to Ergodic Theory*, GTM 79, Springer 1982, Chapter 9.
-/

open Filter MeasureTheory PathGrowth ExpGrowth
open scoped ENNReal

namespace Dynamics

variable {α ι V : Type*} [MeasurableSpace α]

/-! ### The dynamical join, one step at a time -/

omit [MeasurableSpace α] in
/-- The dynamical join of length `n + 1` is the symbol read now, followed by the join of length `n`
read from the next point. -/
theorem joinIter_succ (T : α → α) (f : α → ι) (n : ℕ) (x : α) :
    joinIter T f (n + 1) x = Fin.cons (f x) (joinIter T f n (T x)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [joinIter]
  · simp only [joinIter, Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply]

/-- Reindexing a sum over words of length `n + 1` as first symbol, then the rest. -/
theorem sum_pi_fin_succ {M : Type*} [AddCommMonoid M] [Fintype ι] (n : ℕ)
    (F : (Fin (n + 1) → ι) → M) :
    ∑ w : Fin (n + 1) → ι, F w = ∑ c : ι, ∑ w' : Fin n → ι, F (Fin.cons c w') :=
  (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => ι)
      (fun p => F (Fin.cons p.1 p.2)) F fun _ => rfl).symm.trans
    (Fintype.sum_prod_type' fun c w' => F (Fin.cons c w'))

/-! ### Transfer bounds -/

/-- A **transfer bound** for `(T, φ, P)` on the finite state set `V`: a state observable driven by
the partition symbol, together with integer edge weights dominating `exp φ`.

The two axioms are exactly what a window machine provides: the window slides deterministically as
the next symbol is read, and the potential on a window is bounded by the weight recorded for that
window. -/
structure TransferBound (T : α → α) (φ : α → ℝ) (f : α → ι) (V : Type*) where
  /-- The finite-state observable. -/
  state : α → V
  /-- The successor map: reading a symbol moves the state. -/
  tgt : V → ι → V
  /-- The edge weights. -/
  weight : V → ι → ℕ
  /-- The state is driven by the partition symbol. -/
  state_apply : ∀ x, state (T x) = tgt (state x) (f x)
  /-- The weight of an edge dominates `exp` of the potential. -/
  exp_le : ∀ x, Real.exp (φ x) ≤ weight (state x) (f x)

/-- The `n`-th partition sum, refined by the value of the state observable `st`.  Summing over `q`
recovers an upper bound for `partitionSum` (`partitionSum_le_sum_stateSum`), and each refined sum
obeys the transfer recursion (`stateSum_le_psum`). -/
noncomputable def stateSum [Fintype ι] (T : α → α) (φ : α → ℝ) (f : α → ι) (st : α → V) (q : V)
    (n : ℕ) : ℝ≥0∞ :=
  ∑ w : Fin n → ι, ⨆ x ∈ {x : α | joinIter T f n x = w ∧ st x = q},
    ENNReal.ofReal (Real.exp (birkhoffSum T φ n x))

variable [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

omit [MeasurableSpace α] [DecidableEq ι] [DecidableEq V] in
/-- Refining the cells by the state can only lose: the cell supremum is at most the sum over states
of the refined suprema. -/
theorem partitionSum_le_sum_stateSum (T : α → α) (φ : α → ℝ) (f : α → ι) (st : α → V) (n : ℕ) :
    partitionSum T φ f n ≤ ∑ q : V, stateSum T φ f st q n := by
  have hcomm : ∑ q : V, stateSum T φ f st q n
      = ∑ w : Fin n → ι, ∑ q : V, ⨆ x ∈ {x : α | joinIter T f n x = w ∧ st x = q},
        ENNReal.ofReal (Real.exp (birkhoffSum T φ n x)) := by
    simp only [stateSum]
    exact Finset.sum_comm
  rw [partitionSum, hcomm]
  refine Finset.sum_le_sum fun w _ => ?_
  refine iSup₂_le fun x hx => ?_
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun q : V => ⨆ y ∈ {y : α | joinIter T f n y = w ∧ st y = q},
      ENNReal.ofReal (Real.exp (birkhoffSum T φ n y)))
    (fun _ _ => zero_le) (Finset.mem_univ (st x)))
  exact le_iSup₂ (f := fun y (_ : y ∈ {y : α | joinIter T f n y = w ∧ st y = st x}) =>
    ENNReal.ofReal (Real.exp (birkhoffSum T φ n y))) x ⟨hx, rfl⟩

omit [MeasurableSpace α] in
/-- **The transfer recursion.**  The state-refined partition sum is dominated by the total weight
of the length-`n` paths of the transfer operator out of that state. -/
theorem stateSum_le_psum {T : α → α} {φ : α → ℝ} {f : α → ι} (B : TransferBound T φ f V)
    (n : ℕ) (q : V) :
    stateSum T φ f B.state q n
      ≤ ((psum (detE B.tgt) (fun e => B.weight e.1 e.2.1) (fun _ => 1) q n : ℕ) : ℝ≥0∞) := by
  induction n generalizing q with
  | zero =>
    have hone : ∀ w : Fin 0 → ι,
        (⨆ x ∈ {x : α | joinIter T f 0 x = w ∧ B.state x = q},
          ENNReal.ofReal (Real.exp (birkhoffSum T φ 0 x))) ≤ 1 := by
      intro w
      exact iSup₂_le fun x _ => by simp [birkhoffSum]
    calc stateSum T φ f B.state q 0 ≤ ∑ _w : Fin 0 → ι, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun w _ => hone w
      _ = 1 := by simp
      _ = _ := by simp [psum]
  | succ n ih =>
    set F : (Fin (n + 1) → ι) → ℝ≥0∞ := fun w =>
      ⨆ x ∈ {x : α | joinIter T f (n + 1) x = w ∧ B.state x = q},
        ENNReal.ofReal (Real.exp (birkhoffSum T φ (n + 1) x)) with hF
    have hre : stateSum T φ f B.state q (n + 1)
        = ∑ c : ι, ∑ w' : Fin n → ι, F (Fin.cons c w') := by
      rw [stateSum]
      exact sum_pi_fin_succ n F
    have key : ∀ (c : ι) (w' : Fin n → ι), F (Fin.cons c w')
        ≤ (B.weight q c : ℝ≥0∞) * ⨆ y ∈ {y : α | joinIter T f n y = w' ∧ B.state y = B.tgt q c},
            ENNReal.ofReal (Real.exp (birkhoffSum T φ n y)) := by
      intro c w'
      refine iSup₂_le fun x hx => ?_
      obtain ⟨hj, hs⟩ := hx
      rw [joinIter_succ] at hj
      have hfx : f x = c := by simpa using congrArg (fun u => u 0) hj
      have hw' : joinIter T f n (T x) = w' := by
        funext j
        simpa using congrArg (fun u => u j.succ) hj
      have hmem : T x ∈ {y : α | joinIter T f n y = w' ∧ B.state y = B.tgt q c} :=
        ⟨hw', by rw [B.state_apply, hs, hfx]⟩
      have h1 : ENNReal.ofReal (Real.exp (φ x)) ≤ (B.weight q c : ℝ≥0∞) := by
        have := ENNReal.ofReal_le_ofReal (B.exp_le x)
        rwa [ENNReal.ofReal_natCast, hs, hfx] at this
      have h2 : ENNReal.ofReal (Real.exp (birkhoffSum T φ n (T x)))
          ≤ ⨆ y ∈ {y : α | joinIter T f n y = w' ∧ B.state y = B.tgt q c},
              ENNReal.ofReal (Real.exp (birkhoffSum T φ n y)) :=
        le_iSup₂ (f := fun y (_ : y ∈ {y : α | joinIter T f n y = w' ∧ B.state y = B.tgt q c}) =>
          ENNReal.ofReal (Real.exp (birkhoffSum T φ n y))) (T x) hmem
      rw [birkhoffSum_succ_apply', Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact mul_le_mul' h1 h2
    calc stateSum T φ f B.state q (n + 1) = ∑ c : ι, ∑ w' : Fin n → ι, F (Fin.cons c w') := hre
      _ ≤ ∑ c : ι, ∑ w' : Fin n → ι, (B.weight q c : ℝ≥0∞) *
            ⨆ y ∈ {y : α | joinIter T f n y = w' ∧ B.state y = B.tgt q c},
              ENNReal.ofReal (Real.exp (birkhoffSum T φ n y)) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun w' _ => key c w'
      _ = ∑ c : ι, (B.weight q c : ℝ≥0∞) * stateSum T φ f B.state (B.tgt q c) n := by
          simp only [stateSum, Finset.mul_sum]
      _ ≤ ∑ c : ι, (B.weight q c : ℝ≥0∞) *
            ((psum (detE B.tgt) (fun e => B.weight e.1 e.2.1) (fun _ => 1) (B.tgt q c) n : ℕ)
              : ℝ≥0∞) := by
          exact Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl (ih (B.tgt q c))
      _ = _ := by rw [psum_detE_succ]; push_cast; rfl

omit [MeasurableSpace α] in
/-- **The partition function is dominated by the path sums of the transfer operator.** -/
theorem partitionSum_le_of_transferBound {T : α → α} {φ : α → ℝ} {f : α → ι}
    (B : TransferBound T φ f V) (n : ℕ) :
    partitionSum T φ f n
      ≤ ∑ q : V, ((psum (detE B.tgt) (fun e => B.weight e.1 e.2.1) (fun _ => 1) q n : ℕ)
          : ℝ≥0∞) :=
  (partitionSum_le_sum_stateSum T φ f B.state n).trans
    (Finset.sum_le_sum fun q _ => stateSum_le_psum B n q)

omit [MeasurableSpace α] in
/-- **A vector certificate for the transfer operator bounds the pressure.**  If `v` is a positive
integer vector with `b · (M v) ≤ a · v` entrywise, then `P(T, φ, P) ≤ log (a / b)`. -/
theorem partitionPressure_le_of_transferBound {T : α → α} {φ : α → ℝ} {f : α → ι}
    (B : TransferBound T φ f V) {a b : ℕ} (hb : 0 < b) (ha : 0 < a) (v : V → ℕ)
    (hv : ∀ q, 1 ≤ v q)
    (hcert : ∀ q, b * ∑ e ∈ outEdges (detE B.tgt) q, B.weight e.1 e.2.1 * v e.2.2 ≤ a * v q) :
    partitionPressure T φ f ≤ (Real.log ((a : ℝ) / b) : EReal) := by
  set r : ℝ := (a : ℝ) / b with hr
  have hrpos : 0 < r := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  set K : ℝ := ∑ q : V, (v q : ℝ) with hK
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hstep : ∀ n : ℕ,
      partitionSum T φ f n ≤ ENNReal.ofReal K * ENNReal.ofReal r ^ n := by
    intro n
    have hpsum : ∀ q : V,
        ((psum (detE B.tgt) (fun e => B.weight e.1 e.2.1) (fun _ => 1) q n : ℕ) : ℝ)
          ≤ r ^ n * v q :=
      fun q => psum_le_pow _ _ _ v a b hb (fun s => hv s) hcert n q
    refine (partitionSum_le_of_transferBound B n).trans ?_
    calc ∑ q : V, ((psum (detE B.tgt) (fun e => B.weight e.1 e.2.1) (fun _ => 1) q n : ℕ) : ℝ≥0∞)
        ≤ ∑ q : V, ENNReal.ofReal (r ^ n * v q) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (hpsum q)
      _ = ENNReal.ofReal (∑ q : V, r ^ n * v q) :=
          (ENNReal.ofReal_sum_of_nonneg fun q _ => by positivity).symm
      _ = ENNReal.ofReal K * ENNReal.ofReal r ^ n := by
          rw [← Finset.mul_sum, ← hK, ENNReal.ofReal_mul (by positivity), mul_comm,
            ENNReal.ofReal_pow hrpos.le]
  calc partitionPressure T φ f
      ≤ expGrowthSup (fun n : ℕ => ENNReal.ofReal r ^ n) :=
        expGrowthSup_le_of_eventually_le ENNReal.ofReal_ne_top
          (Filter.Eventually.of_forall hstep)
    _ = (Real.log r : EReal) := by
        rw [expGrowthSup_pow, ENNReal.log_ofReal_of_pos hrpos]

end Dynamics
