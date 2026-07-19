/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.Rigidity
import CITED.Stanley
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The eventual-periodicity engine, and the transcendence of `f(z) = Σ wⱼzʲ` (plan-B1E2, WP6)

**A P-recursive sequence with finitely many values is eventually periodic** — proved, elementary,
no analysis.  With `RB.not_eventually_periodic` (WP1) and the one Stanley axiom this yields the
capstone

  **`RB.not_isAlgebraic_wminSeries`** : `Σⱼ wⱼzʲ` is *not algebraic* over `ℚ(z)`.

[AF17] §8.1 treat exactly this inference as routine — *«Comme la suite `(aₙ)` ne prend qu'un
nombre fini de valeurs entières et qu'elle n'est pas ultimement périodique, on obtient facilement
que `f(z)` est transcendante»* — and this file is that "facilement", spelled out.

## The chain (three steps, one axiom)

1. **Stanley** (`Stanley.pRecursive_of_isAlgebraic`, the only axiom): algebraic ⇒ D-finite ⇒
   the coefficients satisfy `∑ⱼ Qⱼ(n)·w(n+j) = 0` with `Qⱼ ∈ ℚ[t]` not all `0`.
2. **Pigeonhole ⇒ constant coefficients** (`exists_constant_recurrence`, *proved*). Let
   `e = maxⱼ deg Qⱼ` and `qⱼ = [tᵉ]Qⱼ`. Windows `(w n, …, w (n+s))` live in a finite set, so only
   finitely many `m` carry a window that occurs finitely often; past that `N`, the window at `m`
   recurs infinitely often, making `∑ⱼ Qⱼ(t)·w(m+j)` a polynomial with infinitely many roots,
   hence `0`.  Its `[tᵉ]` coefficient is the constant-coefficient recurrence `∑ⱼ qⱼ·w(m+j) = 0`,
   nontrivial because `[tᵉ]` of a maximal-degree `Qⱼ` is its leading coefficient.
3. **Finite state ⇒ eventually periodic** (`eventuallyPeriodic_of_constant_recurrence`, *proved*).
   With `b = max{j : qⱼ ≠ 0}`, the window `(w m, …, w (m+b))` determines its successor (solve the
   recurrence for the top term, `q_b ≠ 0`), so it evolves deterministically on a finite set;
   pigeonhole gives a repeat, and determinism propagates it forever.

## Two architectural bonuses (why this beats the Carlson route rev. 1 proposed)

* **Rationality is never an intermediate.** Step 3 yields eventual periodicity *directly*, so
  Fatou's lemma, pole structure and Skolem–Mahler–Lech are all bypassed — and rev. 1's separate
  "rational + `{0,1}` coefficients ⇒ eventually periodic" glue disappears.
* **The axiom footprint says nothing about finite coefficient sets.** All of that lives in the
  *proved* half. See `CITED.Stanley`'s module doc for why Carlson was deleted.

## Generality

Steps 2 and 3 are stated for an arbitrary `w : ℕ → ℚ` with `(Set.range w).Finite` — nothing about
`RB` enters until `not_isAlgebraic_wminSeries`.  They are ForMathlib candidates (the only reason
they live here is that `Stanley.IsPRecursive` does).

## Contents

* `RB.exists_constant_recurrence` — step 2.
* `RB.eventuallyPeriodic_of_constant_recurrence` — step 3.
* **`RB.eventuallyPeriodic_of_isPRecursive`** — steps 2+3: P-recursive + finite range ⇒
  eventually periodic.
* **`RB.eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs`** — the plan's WP6 deliverable.
* **`RB.not_isAlgebraic_wminSeries`** — the capstone: `Σⱼ wⱼzʲ` is transcendental over `ℚ(z)`.

## References

* [Sta80] Stanley. *Differentiably finite power series.* European J. Combin. **1** (1980),
  175–188.  (Thm 2.1 + Thm 1.5 = the axiom.)
* [AF17] Adamczewski, Faverjon. Proc. LMS **115** (2017), 55–90.  (§8.1: this inference,
  "facilement".)
* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91.  (Prop 26 = the
  non-periodicity this consumes, proved in `RB.Rigidity`.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 G0.c (the three steps), WP6.
-/

namespace RB

open Stanley

/-! ## Step 2: pigeonhole ⇒ constant coefficients -/

/-- The top coefficients `[tᵉ]Qⱼ` at `e = maxⱼ deg Qⱼ` are not all zero: the `j` attaining the
max contributes its leading coefficient. -/
@[category API, AMS 11 68 05, ref "B1E2", group "stanley_closure"]
lemma top_coeff_ne_zero {s : ℕ} {Q : Fin (s + 1) → Polynomial ℚ} {j₀ : Fin (s + 1)}
    (hj₀ : Q j₀ ≠ 0) : ∃ j, (Q j).coeff (Finset.univ.sup (fun j => (Q j).natDegree)) ≠ 0 := by
  classical
  set F : Finset (Fin (s + 1)) := Finset.univ.filter (fun j => Q j ≠ 0) with hF
  have hFne : F.Nonempty := ⟨j₀, by simp [hF, hj₀]⟩
  obtain ⟨j₁, hj₁F, hj₁max⟩ := F.exists_max_image (fun j => (Q j).natDegree) hFne
  have hQ1 : Q j₁ ≠ 0 := by simpa [hF] using hj₁F
  have hsup : Finset.univ.sup (fun j => (Q j).natDegree) = (Q j₁).natDegree := by
    refine le_antisymm (Finset.sup_le fun j _ => ?_)
      (Finset.le_sup (f := fun j => (Q j).natDegree) (Finset.mem_univ j₁))
    by_cases hj : Q j = 0
    · simp [hj]
    · exact hj₁max j (by simp [hF, hj])
  exact ⟨j₁, by rw [hsup]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ1⟩

/-- A polynomial vanishing at infinitely many *naturals* is zero. -/
@[category API, AMS 11 68 05, ref "B1E2", group "stanley_closure"]
lemma poly_eq_zero_of_infinite_nat_roots {P : Polynomial ℚ} {T : Set ℕ} (hT : T.Infinite)
    (h : ∀ m ∈ T, P.eval (m : ℚ) = 0) : P = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot P ?_
  refine Set.Infinite.mono (s := (fun m : ℕ => (m : ℚ)) '' T) ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩; exact h m hm
  · exact hT.image (Set.injOn_of_injective fun a b hab => by exact_mod_cast hab)

/-- **The pigeonhole**: past some `N`, every window of `w` recurs infinitely often.  Only
finitely many positions can carry a window that occurs only finitely often. -/
@[category research solved, AMS 11 68 05, ref "B1E2", group "stanley_closure"]
lemma exists_N_recurrent {w : ℕ → ℚ} (hfin : (Set.range w).Finite) (s : ℕ) :
    ∃ N : ℕ, ∀ m, N < m →
      ((fun m' => (fun j : Fin (s + 1) => w (m' + j))) ⁻¹'
        {(fun j : Fin (s + 1) => w (m + j))}).Infinite := by
  classical
  set V : ℕ → (Fin (s + 1) → ℚ) := fun m j => w (m + j) with hV
  have hrangeV : (Set.range V).Finite := by
    refine Set.Finite.subset
      (Set.Finite.pi' (t := fun _ : Fin (s + 1) => Set.range w) fun _ => hfin) ?_
    rintro f ⟨m, rfl⟩ j
    exact ⟨m + j, rfl⟩
  set B : Set (Fin (s + 1) → ℚ) := {v ∈ Set.range V | (V ⁻¹' {v}).Finite} with hB
  have hBfin : B.Finite := hrangeV.subset fun v hv => hv.1
  have hbad : {m | (V ⁻¹' {V m}).Finite} ⊆ ⋃ v ∈ B, V ⁻¹' {v} := fun m hm =>
    Set.mem_biUnion ⟨⟨m, rfl⟩, hm⟩ rfl
  have hbadfin : {m | (V ⁻¹' {V m}).Finite}.Finite :=
    Set.Finite.subset (hBfin.biUnion fun v hv => hv.2) hbad
  obtain ⟨N, hN⟩ := hbadfin.bddAbove
  refine ⟨N, fun m hm => ?_⟩
  by_contra hcon
  exact absurd (hN (Set.not_infinite.mp hcon)) (by omega)

/-- **Step 2** ([B1E2] §0.1): a P-recursive sequence with finitely many values satisfies a
nontrivial *constant-coefficient* recurrence from some point on. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "B1E2", group "stanley_closure"]
theorem exists_constant_recurrence {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    (hrec : IsPRecursive w) :
    ∃ (s : ℕ) (q : Fin (s + 1) → ℚ) (N : ℕ), (∃ j, q j ≠ 0) ∧
      ∀ m, N < m → ∑ j : Fin (s + 1), q j * w (m + j) = 0 := by
  obtain ⟨s, Q, ⟨j₀, hj₀⟩, hQ⟩ := hrec
  classical
  set e : ℕ := Finset.univ.sup (fun j => (Q j).natDegree) with he
  obtain ⟨N, hN⟩ := exists_N_recurrent hfin s
  refine ⟨s, fun j => (Q j).coeff e, N, top_coeff_ne_zero hj₀, fun m hm => ?_⟩
  set P : Polynomial ℚ := ∑ j : Fin (s + 1), Q j * Polynomial.C (w (m + j)) with hP
  have hroots : ∀ m' ∈ ((fun m' => (fun j : Fin (s + 1) => w (m' + j))) ⁻¹'
      {(fun j : Fin (s + 1) => w (m + j))}), P.eval (m' : ℚ) = 0 := by
    intro m' hm'
    have hval : ∀ j : Fin (s + 1), w (m' + j) = w (m + j) := fun j => congrFun hm' j
    rw [hP]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    rw [← hQ m']
    exact Finset.sum_congr rfl fun j _ => by rw [hval j]
  have hPzero : P = 0 := poly_eq_zero_of_infinite_nat_roots (hN m hm) hroots
  have hc := congrArg (fun p => Polynomial.coeff p e) hPzero
  simpa only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_zero] using hc

/-! ## Step 3: finite state ⇒ eventually periodic -/

/-- **Step 3** ([B1E2] §0.1): a nontrivial constant-coefficient recurrence, plus finitely many
values, forces eventual periodicity.

The window `(w m, …, w (m+b))` with `b = max{j : qⱼ ≠ 0}` determines its own successor — solve
the recurrence for the top term, legitimate since `q_b ≠ 0` — so it evolves *deterministically*
on a finite set.  Pigeonhole gives a repeat; determinism propagates it forever. -/
@[category research solved, AMS 11 68 05, ref "B1E2", group "stanley_closure"]
theorem eventuallyPeriodic_of_constant_recurrence {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    {s : ℕ} {q : Fin (s + 1) → ℚ} {N : ℕ} (hq : ∃ j, q j ≠ 0)
    (hrec : ∀ m, N < m → ∑ j : Fin (s + 1), q j * w (m + j) = 0) :
    ∃ N' p, 0 < p ∧ ∀ n, N' ≤ n → w (n + p) = w n := by
  classical
  obtain ⟨j₀, hj₀⟩ := hq
  set F : Finset (Fin (s + 1)) := Finset.univ.filter (fun j => q j ≠ 0) with hF
  have hFne : F.Nonempty := ⟨j₀, by simp [hF, hj₀]⟩
  obtain ⟨jb, hjbF, hjbmax⟩ := F.exists_max_image (fun j => (j : ℕ)) hFne
  have hqb : q jb ≠ 0 := by simpa [hF] using hjbF
  set b : ℕ := (jb : ℕ) with hb
  set Agree : ℕ → ℕ → Prop := fun m₁ m₂ => ∀ i ≤ b, w (m₁ + i) = w (m₂ + i) with hAg
  -- the window determines its successor
  have hdet : ∀ m₁ m₂, N ≤ m₁ → N ≤ m₂ → Agree m₁ m₂ → Agree (m₁ + 1) (m₂ + 1) := by
    intro m₁ m₂ h1 h2 heq i hi
    rcases Nat.lt_or_ge i b with hib | hib
    · -- inside the window: the entry is inherited
      have h := heq (1 + i) (by omega)
      have e1 : m₁ + (1 + i) = m₁ + 1 + i := by omega
      have e2 : m₂ + (1 + i) = m₂ + 1 + i := by omega
      rwa [e1, e2] at h
    · -- the new top entry: solve the recurrence at `m+1`
      have hieq : i = b := by omega
      subst hieq
      have hers : ∑ j ∈ Finset.univ.erase jb, q j * w (m₁ + 1 + j)
          = ∑ j ∈ Finset.univ.erase jb, q j * w (m₂ + 1 + j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases hqj : q j = 0
        · simp [hqj]
        · have hjne : j ≠ jb := Finset.ne_of_mem_erase hj
          have hjle : (j : ℕ) ≤ b := hjbmax j (by simp [hF, hqj])
          have hjlt : (j : ℕ) < b := lt_of_le_of_ne hjle fun h => hjne (Fin.ext h)
          have h := heq (1 + (j : ℕ)) (by omega)
          have e1 : m₁ + (1 + (j : ℕ)) = m₁ + 1 + (j : ℕ) := by omega
          have e2 : m₂ + (1 + (j : ℕ)) = m₂ + 1 + (j : ℕ) := by omega
          rw [e1, e2] at h
          rw [h]
      have r1 := hrec (m₁ + 1) (by omega)
      have r2 := hrec (m₂ + 1) (by omega)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jb)] at r1 r2
      rw [hers] at r1
      have hcan : q jb * w (m₁ + 1 + jb) = q jb * w (m₂ + 1 + jb) := by linarith [r1, r2]
      exact mul_left_cancel₀ hqb hcan
  have hiter : ∀ m₁ m₂, N ≤ m₁ → N ≤ m₂ → Agree m₁ m₂ → ∀ k, Agree (m₁ + k) (m₂ + k) := by
    intro m₁ m₂ h1 h2 heq k
    induction k with
    | zero => simpa using heq
    | succ k ih =>
      have h := hdet (m₁ + k) (m₂ + k) (by omega) (by omega) ih
      have e1 : m₁ + (k + 1) = m₁ + k + 1 := by omega
      have e2 : m₂ + (k + 1) = m₂ + k + 1 := by omega
      rw [e1, e2]; exact h
  -- pigeonhole: the state space is finite, the positions are not
  haveI : Finite ↥(Set.range w) := hfin
  obtain ⟨k₁, k₂, hne, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (fun i : Fin (b + 1) => (⟨w (N + k + i), ⟨N + k + i, rfl⟩⟩ : ↥(Set.range w))))
  have hagree : ∀ a c : ℕ,
      (fun i : Fin (b + 1) => (⟨w (N + a + i), ⟨N + a + i, rfl⟩⟩ : ↥(Set.range w)))
        = (fun i : Fin (b + 1) => (⟨w (N + c + i), ⟨N + c + i, rfl⟩⟩ : ↥(Set.range w))) →
      Agree (N + a) (N + c) := fun a c h i hi =>
    congrArg Subtype.val (congrFun h ⟨i, by omega⟩)
  rcases Nat.lt_or_ge k₁ k₂ with hlt | hge
  · refine ⟨N + k₁, k₂ - k₁, by omega, fun n hn => ?_⟩
    have hA := hiter (N + k₁) (N + k₂) (by omega) (by omega) (hagree k₁ k₂ hfeq)
      (n - (N + k₁)) 0 (by omega)
    have e1 : N + k₁ + (n - (N + k₁)) + 0 = n := by omega
    have e2 : N + k₂ + (n - (N + k₁)) + 0 = n + (k₂ - k₁) := by omega
    rw [e1, e2] at hA
    exact hA.symm
  · have hlt' : k₂ < k₁ := lt_of_le_of_ne hge (Ne.symm hne)
    refine ⟨N + k₂, k₁ - k₂, by omega, fun n hn => ?_⟩
    have hA := hiter (N + k₂) (N + k₁) (by omega) (by omega) (hagree k₂ k₁ hfeq.symm)
      (n - (N + k₂)) 0 (by omega)
    have e1 : N + k₂ + (n - (N + k₂)) + 0 = n := by omega
    have e2 : N + k₁ + (n - (N + k₂)) + 0 = n + (k₁ - k₂) := by omega
    rw [e1, e2] at hA
    exact hA.symm

/-! ## The engine, and the capstone -/

/-- **Steps 2+3**: a P-recursive sequence with finitely many values is eventually periodic.
Fully proved; no axiom. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "B1E2", group "stanley_closure"]
theorem eventuallyPeriodic_of_isPRecursive {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    (hrec : IsPRecursive w) : ∃ N p, 0 < p ∧ ∀ n, N ≤ n → w (n + p) = w n := by
  obtain ⟨s, q, N, hq, hqrec⟩ := exists_constant_recurrence hfin hrec
  exact eventuallyPeriodic_of_constant_recurrence hfin hq hqrec

/-- **WP6's deliverable** ([B1E2]): an *algebraic* power series with finitely many coefficient
values has an eventually periodic coefficient sequence.

Footprint: `std3 + Stanley.pRecursive_of_isAlgebraic`.  Zero Carlson, zero Fatou, zero analytic
infrastructure, and **no rationality intermediate**. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "B1E2", group "stanley_closure"]
theorem eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs {w : ℕ → ℚ}
    (hfin : (Set.range w).Finite) (halg : IsAlgebraic (Polynomial ℚ) (PowerSeries.mk w)) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → w (n + p) = w n := by
  refine eventuallyPeriodic_of_isPRecursive hfin ?_
  simpa using pRecursive_of_isAlgebraic halg

/-- **The capstone**: the generating function `f(z) = Σⱼ wⱼzʲ` of the minimal word is **not
algebraic** over `ℚ(z)`.

This is [AF17] §8.1's "on obtient facilement que `f(z)` est transcendante", spelled out: the
word takes finitely many values (`{0,1}`) and is not eventually periodic (`not_eventually_periodic`
= [AFS08] Prop 26), and an algebraic series with finitely many coefficient values *would* be
eventually periodic.

Footprint: `std3 + Stanley.pRecursive_of_isAlgebraic`.  In particular this is **independent of
the AF axiom** — a second, unrelated transcendence statement about the same word. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "AFS08" "AF17", group "rb_rational_base"]
theorem not_isAlgebraic_wminSeries {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsAlgebraic (Polynomial ℚ) (PowerSeries.mk fun j => (wmin x₀ j : ℚ)) := by
  intro halg
  -- the alphabet is literally `{0,1}`
  have hfin : (Set.range fun j => (wmin x₀ j : ℚ)).Finite := by
    refine Set.Finite.subset ((Set.finite_singleton (1 : ℚ)).insert 0) ?_
    rintro _ ⟨j, rfl⟩
    have h : wmin x₀ j = 0 ∨ wmin x₀ j = 1 := by have := wmin_le_one x₀ j; omega
    rcases h with h | h <;> simp [h]
  obtain ⟨N, p, hp, hper⟩ := eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs hfin halg
  refine not_eventually_periodic hx₀ ⟨N, p, hp, fun n hn => ?_⟩
  exact_mod_cast hper n hn

end RB
