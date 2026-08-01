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
# The eventual-periodicity engine, and the non-holonomy of the minimal word (plan-B1E2b, WP1)

**A P-recursive sequence with finitely many values is eventually periodic** — proved, elementary,
no analysis.  With `RB.not_eventually_periodic` this yields the headline of the file, which costs
**no axiom at all**:

  **`RB.not_isPRecursive_wmin`** : the minimal word `w` of base `3/2` is *not P-recursive*
  (not holonomic).

Transcendence of the generating function is a *corollary* of that, and is the only statement in
the file that pays for the [Sta80] axiom:

  **`RB.not_isAlgebraic_wminSeries`** : `f(z) = Σⱼ wⱼzʲ` is not algebraic over `ℚ(z)`
  — because algebraic ⇒ P-recursive coefficients (Stanley) ⇒ `not_isPRecursive_wmin`.

This ordering is deliberate ([B1E2b] WP1 / review item F2).  Non-holonomy is *strictly stronger*
than non-algebraicity — the class of holonomic series contains the algebraic ones properly — and
the strictly stronger statement is the one that is axiom-free.  Stating the weaker corollary as
the headline, and paying an axiom for it, was the ordering of rev. 1.

By Stanley Thm 1.5 (`P`-recursive coefficients ⟺ D-finite series) the flagship also says that
`f` is **not D-finite**; that reading is prose only until a `Stanley.IsDFinite` predicate exists
([B1E2b] WP18), since the "⟸" direction of Thm 1.5 is not currently formalized.

[AF17] §8.1 treat the algebraicity inference as routine — *«Comme la suite `(aₙ)` ne prend qu'un
nombre fini de valeurs entières et qu'elle n'est pas ultimement périodique, on obtient facilement
que `f(z)` est transcendante»* — and this file is that "facilement", spelled out.

## The chain (two proved steps; the axiom only in the last corollary)

1. **Pigeonhole ⇒ constant coefficients** (`exists_constant_recurrence`, *proved*). Let
   `e = maxⱼ deg Qⱼ` and `qⱼ = [tᵉ]Qⱼ`. Windows `(w n, …, w (n+s))` live in a finite set, so only
   finitely many `m` carry a window that occurs finitely often; past that `N`, the window at `m`
   recurs infinitely often, making `∑ⱼ Qⱼ(t)·w(m+j)` a polynomial with infinitely many roots,
   hence `0`.  Its `[tᵉ]` coefficient is the constant-coefficient recurrence `∑ⱼ qⱼ·w(m+j) = 0`,
   nontrivial because `[tᵉ]` of a maximal-degree `Qⱼ` is its leading coefficient.
2. **Finite state ⇒ eventually periodic** (`eventuallyPeriodic_of_constant_recurrence`, *proved*).
   With `b = max{j : qⱼ ≠ 0}`, the window `(w m, …, w (m+b))` determines its successor (solve the
   recurrence for the top term, `q_b ≠ 0`), so it evolves deterministically on a finite set;
   pigeonhole gives a repeat, and determinism propagates it forever.

Contraposed (`not_isPRecursive_of_not_eventuallyPeriodic`), steps 1+2 are the whole flagship:
a finite-valued sequence that is *not* eventually periodic is not P-recursive.  Instantiating at
`wmin` with [AFS08] Prop 26 (`RB.not_eventually_periodic`, proved in `RB.Rigidity`) gives
`not_isPRecursive_wmin` on `std3`.

Step 2 alone already handles **rational** `f` ([B1E2b] WP2, review item F7a): `f·Q = P` *is* a
constant-coefficient recurrence on the coefficients, read off the `zⁿ`-coefficient for `n > deg P`
after reversing the index (`qⱼ = Q_{s−j}`, `s = deg Q`).  So `not_rational_wminSeries` is also
`std3` — and is *cheaper* than the transcendence statement rather than a consequence of it.

3. **Stanley** (`Stanley.pRecursive_of_isAlgebraic`, the only axiom, used *only* here): algebraic
   ⇒ D-finite ⇒ the coefficients satisfy `∑ⱼ Qⱼ(n)·w(n+j) = 0` with `Qⱼ ∈ ℚ[t]` not all `0`.
   Composed with step 1+2 it turns the flagship into non-algebraicity of `f`.

## Two architectural bonuses (why this beats the Carlson route rev. 1 proposed)

* **Rationality is never an intermediate.** Step 2 yields eventual periodicity *directly*, so
  Fatou's lemma, pole structure and Skolem–Mahler–Lech are all bypassed — and rev. 1's separate
  "rational + `{0,1}` coefficients ⇒ eventually periodic" glue disappears.
* **The axiom footprint says nothing about finite coefficient sets.** All of that lives in the
  *proved* half. See `CITED.Stanley`'s module doc for why Carlson was deleted.

## Generality

Steps 1 and 2 are stated for an arbitrary `w : ℕ → ℚ` with `(Set.range w).Finite` — nothing about
`RB` enters until `not_isPRecursive_wmin`.  They are ForMathlib candidates (the only reason
they live here is that `Stanley.IsPRecursive` does).  In particular
`not_isPRecursive_of_not_eventuallyPeriodic` is the interface for the *family* of ceiling-orbit
words of other bases ([B1E2b] WP4/WP5): supply a finite alphabet and aperiodicity, get
non-holonomy.

## Contents

* `RB.exists_constant_recurrence` — step 1.
* `RB.eventuallyPeriodic_of_constant_recurrence` — step 2.
* **`RB.eventuallyPeriodic_of_isPRecursive`** — steps 1+2: P-recursive + finite range ⇒
  eventually periodic.
* **`RB.not_isPRecursive_of_not_eventuallyPeriodic`** — its contrapositive; the reusable interface.
* `RB.finite_range_wmin` — the alphabet of the minimal word is `{0,1}`.
* **`RB.not_isPRecursive_wmin`** — the flagship: the minimal word is not holonomic.  `std3`.
* `RB.eventuallyPeriodic_of_rational_of_finite_coeffs` — the rational case, no axiom.
* **`RB.not_rational_wminSeries`** — `Σⱼ wⱼzʲ` is not a rational function.  `std3`.
* `RB.eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs` — steps 1+2+3, general form.
* **`RB.not_isAlgebraic_wminSeries`** — the corollary: `Σⱼ wⱼzʲ` is transcendental over `ℚ(z)`.

## References

* [Sta80] Stanley. *Differentiably finite power series.* European J. Combin. **1** (1980),
  175–188.  (Thm 2.1 + Thm 1.5 = the axiom.)
* [AF17] Adamczewski, Faverjon. Proc. LMS **115** (2017), 55–90.  (§8.1: this inference,
  "facilement".)
* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91.  (Prop 26 = the
  non-periodicity this consumes, proved in `RB.Rigidity`.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.1 G0.c (the three steps), WP6.
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP1 (this reordering), item F2.
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

/-- **The reusable interface** ([B1E2b] WP1): a finite-valued sequence that is *not* eventually
periodic is **not P-recursive**.  The contrapositive of `eventuallyPeriodic_of_isPRecursive`, and
the form every consumer wants: aperiodicity is what the rigidity theorems produce.

Fully proved; no axiom.  Nothing here is specific to base `3/2` — this is the entry point for the
ceiling-orbit words of other bases ([B1E2b] WP4/WP5). -/
@[category research solved, AMS 11 68 05, ref "Sta80" "B1E2b", group "stanley_closure"]
theorem not_isPRecursive_of_not_eventuallyPeriodic {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    (hper : ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → w (n + p) = w n) : ¬ IsPRecursive w :=
  fun hrec => hper (eventuallyPeriodic_of_isPRecursive hfin hrec)

/-! ## The flagship: the minimal word is not holonomic -/

/-- The minimal word takes only the values `0` and `1`, so its range is finite. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_rational_base"]
lemma finite_range_wmin (x₀ : ℕ) : (Set.range fun j => (wmin x₀ j : ℚ)).Finite := by
  refine Set.Finite.subset ((Set.finite_singleton (1 : ℚ)).insert 0) ?_
  rintro _ ⟨j, rfl⟩
  have h : wmin x₀ j = 0 ∨ wmin x₀ j = 1 := by have := wmin_le_one x₀ j; omega
  rcases h with h | h <;> simp [h]

/-- **The flagship** ([B1E2b] WP1): the minimal word `w` of base `3/2` is **not P-recursive** —
it satisfies *no* nontrivial linear recurrence with polynomial coefficients.

Footprint: `std3`.  **No cited axiom**: the engine (steps 1+2) is proved, and the aperiodicity it
consumes is `RB.not_eventually_periodic` = [AFS08] Prop 26, also proved (2-adic descent, in
`RB.Rigidity`).

By [Sta80] Thm 1.5 this is equivalent to saying that the generating function `f(z) = Σⱼ wⱼzʲ` is
**not D-finite**, which is strictly stronger than `not_isAlgebraic_wminSeries` below: algebraic
series are D-finite, but not conversely (`exp` is D-finite and transcendental).  The strictly
stronger statement is the one that costs nothing. -/
@[category research solved, AMS 11 68, ref "AFS08" "Sta80" "B1E2b", group "rb_rational_base"]
theorem not_isPRecursive_wmin {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsPRecursive (fun j => (wmin x₀ j : ℚ)) :=
  not_isPRecursive_of_not_eventuallyPeriodic (finite_range_wmin x₀) (by
    rintro ⟨N, p, hp, hper⟩
    exact not_eventually_periodic hx₀ ⟨N, p, hp, fun n hn => by exact_mod_cast hper n hn⟩)

/-! ## The rational case, without the axiom -/

/-- **[B1E2b] WP2** (review item F7a): a power series with finitely many coefficient values which
is a **rational function** — `f·Q = P` with `Q ≠ 0` — has an eventually periodic coefficient
sequence.

This is the "Fatou half" of the classical story, and here it costs **no axiom at all**: clearing
denominators makes the `zⁿ`-coefficient of `f·Q = P` read `∑ᵢ Qᵢ·w(n−i) = 0` for `n > deg P`,
which after the index reversal `qⱼ = Q_{s−j}` (`s = deg Q`) is *literally* the hypothesis of
`eventuallyPeriodic_of_constant_recurrence`.  Do **not** route this through Stanley: rationality
implies algebraicity, but taking that route would pay an axiom for a strictly weaker input.

No hypothesis on `Q(0)` is needed.  Step 2 solves its recurrence forward at the *largest* index
with `qⱼ ≠ 0`, which under the reversal is the *lowest* nonvanishing coefficient of `Q`, so a
factor `Xᵐ ∣ Q` is harmless (it just shortens the window). -/
@[category research solved, AMS 11 68 05, ref "B1E2b", group "stanley_closure"]
theorem eventuallyPeriodic_of_rational_of_finite_coeffs {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    {P Q : Polynomial ℚ} (hQ : Q ≠ 0)
    (h : PowerSeries.mk w * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → w (n + p) = w n := by
  classical
  refine eventuallyPeriodic_of_constant_recurrence hfin
    (q := fun j : Fin (Q.natDegree + 1) => Q.coeff (Q.natDegree - j)) (N := P.natDegree)
    ⟨0, ?_⟩ (fun m hm => ?_)
  · -- nontrivial: `j = 0` reads off the leading coefficient of `Q`
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hQ
  · -- past `deg P`, the coefficient of `z^{m+s}` in `f·Q = P` vanishes
    have hc : PowerSeries.coeff (m + Q.natDegree)
        (PowerSeries.mk w * (Q : PowerSeries ℚ)) = 0 := by
      rw [h, Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Polynomial.coeff_coe,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one] at hc
    -- split off the first `m` terms, which vanish: their `Q`-index exceeds `deg Q`
    rw [show m + Q.natDegree + 1 = m + (Q.natDegree + 1) by omega, Finset.sum_range_add] at hc
    have hzero : ∑ k ∈ Finset.range m, w k * Q.coeff (m + Q.natDegree - k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hk' : k < m := Finset.mem_range.mp hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    rw [hzero, zero_add] at hc
    rw [Fin.sum_univ_eq_sum_range
      (fun j => Q.coeff (Q.natDegree - j) * w (m + j)) (Q.natDegree + 1)]
    calc ∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff (Q.natDegree - j) * w (m + j)
        = ∑ j ∈ Finset.range (Q.natDegree + 1),
            w (m + j) * Q.coeff (m + Q.natDegree - (m + j)) :=
          Finset.sum_congr rfl fun j _ => by
            have hidx : m + Q.natDegree - (m + j) = Q.natDegree - j := by omega
            rw [hidx, mul_comm]
      _ = 0 := hc

/-- **[B1E2b] WP2**: the generating function `f(z) = Σⱼ wⱼzʲ` of the minimal word is **not a
rational function**: `f·Q = P` is impossible for polynomials `P, Q` with `Q ≠ 0`.

Footprint: `std3`.  This is the statement the paper's rev. 1 asserted "by Thm 1.1" through an
unstated lemma (review item F7a); it is in fact *cheaper* than the transcendence statement, not
a consequence of it — the Stanley axiom never enters. -/
@[category research solved, AMS 11 68, ref "AFS08" "B1E2b", group "rb_rational_base"]
theorem not_rational_wminSeries {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      PowerSeries.mk (fun j => (wmin x₀ j : ℚ)) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  rintro ⟨P, Q, hQ, h⟩
  obtain ⟨N, p, hp, hper⟩ :=
    eventuallyPeriodic_of_rational_of_finite_coeffs (finite_range_wmin x₀) hQ h
  exact not_eventually_periodic hx₀ ⟨N, p, hp, fun n hn => by exact_mod_cast hper n hn⟩

/-! ## The algebraic case: the one place the axiom is used -/

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

/-- **The corollary** ([AF17] §8.1): the generating function `f(z) = Σⱼ wⱼzʲ` of the minimal word
is **not algebraic** over `ℚ(z)`.

This is "on obtient facilement que `f(z)` est transcendante", spelled out — but note the route:
the work is entirely in the flagship `not_isPRecursive_wmin`, and the Stanley axiom is consumed
*here and only here*, to weaken non-holonomy to non-algebraicity ([B1E2b] WP1).

Footprint: `std3 + Stanley.pRecursive_of_isAlgebraic`.  In particular this is **independent of
the AF axiom** — a second, unrelated transcendence statement about the same word. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "AFS08" "AF17", group "rb_rational_base"]
theorem not_isAlgebraic_wminSeries {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsAlgebraic (Polynomial ℚ) (PowerSeries.mk fun j => (wmin x₀ j : ℚ)) := fun halg =>
  not_isPRecursive_wmin hx₀ (by simpa using pRecursive_of_isAlgebraic halg)

end RB
