/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.Rigidity
import CITED.Stanley
import ForMathlib.RingTheory.PowerSeries.EventuallyPeriodic
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
   pigeonhole gives a repeat, and determinism propagates it forever.  **Since [AF17] WP6 the engine
   itself is `isEventuallyPeriodic_of_recurrence` in
   `ForMathlib.RingTheory.PowerSeries.EventuallyPeriodic`** — over an arbitrary integral domain,
   and reusing the Morse–Hedlund determinism pigeonhole of
   `ForMathlib.Combinatorics.InfiniteComplexity`.  What remains here is the index reversal.

Contraposed (`not_isPRecursive_of_not_eventuallyPeriodic`), steps 1+2 are the whole flagship:
a finite-valued sequence that is *not* eventually periodic is not P-recursive.  Instantiating at
`wmin` with [AFS08] Prop 26 (`RB.not_eventually_periodic`, proved in `RB.Rigidity`) gives
`not_isPRecursive_wmin` on `std3`.

Step 2 alone already handles **rational** `f` ([B1E2b] WP2, review item F7a): `f·Q = P` *is* a
constant-coefficient recurrence on the coefficients.  That reading off is Bertin's Proposition 1.1
(`IsRationalSeries.exists_recurrence`), so since [AF17] WP6 this file no longer re-derives it: the
rational case is `IsRationalSeries.isEventuallyPeriodic_coeff`, applied through `mul_comm`.  So
`not_rational_wminSeries` is also `std3` — and is *cheaper* than the transcendence statement
rather than a consequence of it.

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
`RB` enters until `not_isPRecursive_wmin`.  Step 2 **has** moved to ForMathlib ([AF17] WP6), in
the stronger form `isEventuallyPeriodic_of_recurrence` (any integral domain); step 1 stays here
because `Stanley.IsPRecursive` does.  In particular
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
* **`RB.not_isRationalSeries_wminSeries`** — the same, as `¬ IsRationalSeries`.  `std3`.
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
on a finite set.  Pigeonhole gives a repeat; determinism propagates it forever.

Since [AF17] WP6 that engine lives in `ForMathlib.RingTheory.PowerSeries.EventuallyPeriodic`
(`isEventuallyPeriodic_of_recurrence`, over an arbitrary integral domain), and all that is left
here is the index reversal: the ForMathlib form solves for the *lowest*-index coefficient `q 0`
of `∑_{i ≤ s} qᵢ·w(n−i)`, this one for the *highest* index `q_b` of `∑_j qⱼ·w(m+j)`. -/
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
  have hbs : b ≤ s := by have := jb.isLt; omega
  -- `q` as a function on `ℕ`, and its reversal `i ↦ q (b − i)`
  set qn : ℕ → ℚ := fun k => if h : k < s + 1 then q ⟨k, h⟩ else 0 with hqn
  have hqn_zero : ∀ x, b < x → qn x = 0 := by
    intro x hx
    by_cases hxs : x < s + 1
    · rw [hqn]
      simp only [dite_eq_left hxs]
      by_contra hne
      have hle : x ≤ b := hjbmax ⟨x, hxs⟩ (by simp [hF, hne])
      omega
    · rw [hqn]
      exact dite_eq_right hxs
  have hqn_b : qn b ≠ 0 := by
    rw [hqn]
    simp only [dite_eq_left (show b < s + 1 by omega)]
    simpa using hqb
  refine isEventuallyPeriodic_of_recurrence hfin (q := fun i => qn (b - i)) (s := b)
    (n₀ := N + 1 + b) (by simpa using hqn_b) (fun n hn => ?_)
  set m : ℕ := n - b with hm
  calc ∑ i ∈ Finset.range (b + 1), qn (b - i) * w (n - i)
      = ∑ i ∈ Finset.range (b + 1), (fun k => qn k * w (m + k)) (b + 1 - 1 - i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [Finset.mem_range] at hi
          show qn (b - i) * w (n - i) = qn (b - i) * w (m + (b - i))
          rw [show m + (b - i) = n - i from by omega]
    _ = ∑ i ∈ Finset.range (b + 1), qn i * w (m + i) :=
        Finset.sum_range_reflect (fun k => qn k * w (m + k)) (b + 1)
    _ = ∑ i ∈ Finset.range (s + 1), qn i * w (m + i) :=
        Finset.sum_subset (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hbs))) fun x _ hx => by
          rw [Finset.mem_range, not_lt] at hx
          rw [hqn_zero x hx, zero_mul]
    _ = ∑ j : Fin (s + 1), q j * w (m + j) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => qn k * w (m + k)) (s + 1)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hqn]
        simp only [dite_eq_left j.isLt, Fin.eta]
    _ = 0 := hrec m (by omega)

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

No hypothesis on `Q(0)` is needed: the recurrence `IsRationalSeries.exists_recurrence` reads off
`Q·f = P` has its leading coefficient at `Q`'s *trailing* degree, so a factor `Xᵐ ∣ Q` is harmless
(it just shortens the window). -/
@[category research solved, AMS 11 68 05, ref "B1E2b", group "stanley_closure"]
theorem eventuallyPeriodic_of_rational_of_finite_coeffs {w : ℕ → ℚ} (hfin : (Set.range w).Finite)
    {P Q : Polynomial ℚ} (hQ : Q ≠ 0)
    (h : PowerSeries.mk w * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → w (n + p) = w n := by
  have hrat : IsRationalSeries (PowerSeries.mk w) := ⟨P, Q, hQ, by rw [mul_comm]; exact h⟩
  obtain ⟨N, p, hp, hper⟩ :=
    hrat.isEventuallyPeriodic_coeff (by simpa using hfin)
  exact ⟨N, p, hp, fun n hn => by simpa using hper n hn⟩

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

/-- The same statement in the vocabulary of `ForMathlib.RingTheory.PowerSeries.Rationality`:
`f(z) = Σⱼ wⱼzʲ` is **not a rational series** ([AF17] WP6).  `IsRationalSeries` orders the product
the other way (`Q·f = P`), which over a commutative ring is the same hypothesis.

Footprint: `std3`. -/
@[category research solved, AMS 11 68, ref "AFS08" "B1E2b", group "rb_rational_base"]
theorem not_isRationalSeries_wminSeries {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsRationalSeries (PowerSeries.mk fun j => (wmin x₀ j : ℚ)) := by
  rintro ⟨P, Q, hQ, h⟩
  exact not_rational_wminSeries hx₀ ⟨P, Q, hQ, by rw [mul_comm]; exact h⟩

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
