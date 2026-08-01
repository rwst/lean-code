/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.MahlerExamples
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The representation question: can the `0`-decimation always be made a permutation?
(plan-B1E2b WP10)

Theorem C (`RB.regular_of_not_isIntegral_inv`) needs `σ(·,0)` to be a permutation of the state set.
The Thue–Morse and Cantor systems have that; the parity system does not (`RB/MahlerExamples.lean`).
Since a `k`-automatic sequence has *many* finite presentations — the `k`-kernel is only the minimal
one — it is natural to ask whether the hypothesis can always be arranged by choosing a different
presentation.  This file states that question and fences it in.

## Presentations

`RB.IsPresentation k a φ σ` drops both extra conditions of `RB.IsKernelModel`: `φ` need not be
injective and its range need not be the whole kernel; all that is asked is that some state carries
`a` and that `φ (σ i r) n = φ i (k·n + r)`.  That is exactly a DFAO for `a` with the automaton
written as a function, and every kernel model is one (`IsKernelModel.isPresentation`).  The extra
freedom is the point: the question is whether *some* presentation has a bijective `0`-decimation.

## What is proved here, and what is left open

**A necessary condition** (`invariant_of_bijective_zero`).  If a finite presentation has
`σ(·,0)` bijective then it has finite order `T ≥ 1`, and reading the intertwining relation `T` times
gives, for the state carrying `a`,

  `a(k^T·n) = a(n)` for all `n`.

So a sequence that is not invariant under `n ↦ k^T·n` for any `T ≥ 1` has **no** permutation
presentation at all — not merely none whose states are the kernel.  Thue–Morse and the Cantor
sequence pass the test (`thueMorse_two_pow_mul`, `cantorSeq_three_pow_mul`) and do have one; the
parity sequence `n % 2` fails it at `n = 1`, so `paritySeq_not_hasPermutationPresentation` upgrades
WP9's collapsing example from "its kernel model collapses" to "**every** finite presentation of it
collapses".  This is more than the plan asked for and it is what makes the question interesting
rather than open-ended.

**Two obstructions to the obvious constructions.**

* *Base change does not help*: the `0`-decimation in base `k^t` is the `t`-fold composite of the
  one in base `k`, and on a finite state set a composite power is bijective exactly when the map is
  (`RB.sigma_pow_zero_perm_iff`, built in `RB/MahlerExamples.lean` — item (i) of the plan's WP10).
* *Restricting to the eventual image does not help*.  The **eventual image**
  `ι^∞ = ⋂_m Im σ(·,0)^m` does carry a bijective `0`-decimation (`bijOn_eventualImage`) and is
  nonempty, but it is not a presentation of `a`: it need not contain a state carrying `a`
  (`paritySeq_notMem_eventualImage`, the parity system again), and it need not be closed under
  `σ(·,r)` for `r > 0` (`eventualImage_not_closed_example`).  Either failure alone destroys the
  Mahler system.

**The question** (`RepresentationQuestion`) is whether the necessary condition is also sufficient
for a `k`-automatic sequence.  It is recorded as a `def : Prop`, never an axiom and with no
conjectured answer — the corpus policy on open problems, and the plan's instruction not to claim a
program.

## Contents

* **`RB.IsPresentation`**, `RB.IsKernelModel.isPresentation`.
* `RB.eventualImage`, `RB.mapsTo_eventualImage`, `RB.mem_eventualImage_of_isPeriodicPt`,
  `RB.notMem_eventualImage_of_notMem_range`, `RB.exists_iterate_add_eq`,
  `RB.exists_iterate_eq_self_on_eventualImage`, **`RB.bijOn_eventualImage`**,
  `RB.eventualImage_nonempty`.
* `RB.exists_iterate_eq_id`, `RB.phi_iterate_zero`, **`RB.invariant_of_bijective_zero`**.
* `RB.thueMorse_two_pow_mul`, `RB.cantorSeq_three_pow_mul`,
  **`RB.thueMorse_hasPermutationPresentation`**, `RB.cantorSeq_hasPermutationPresentation`,
  **`RB.paritySeq_not_hasPermutationPresentation`**.
* `RB.paritySeq_notMem_eventualImage`, `RB.notClosedSigma`,
  **`RB.eventualImage_not_closed_example`**.
* **`RB.HasPermutationPresentation`**, **`RB.RepresentationQuestion`** — the question, stated.

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90.
* [AS03] Allouche, Shallit. *Automatic Sequences.* CUP 2003.  (DFAOs and the kernel, Thm 6.6.2.)
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP10 = review item B9; (i) is in
  `RB/MahlerExamples.lean`, (ii) and (iii) are here.
-/

namespace RB

open AS

/-! ## Presentations: kernel models without the minimality -/

/-- **A finite presentation** ([B1E2b] WP10): a state set `ι`, a decimation `σ`, and a reading map
`φ` with `φ (σ i r) n = φ i (k·n + r)`, one of whose states carries `a`.

This is a DFAO for `a` written without automata: `φ i` is the sequence read from state `i`, and the
output function is `i ↦ φ i 0`.  Unlike `RB.IsKernelModel` neither injectivity nor exhaustion of
the kernel is required, so a sequence has many presentations — which is exactly what the
representation question exploits. -/
@[category API, AMS 11 68, ref "AS03" "B1E2b", group "rb_representation"]
def IsPresentation (k : ℕ) (a : ℕ → ℕ) {ι : Type*} (φ : ι → ℕ → ℕ) (σ : ι → Fin k → ι) : Prop :=
  (∃ i₀, φ i₀ = a) ∧ ∀ i r n, φ (σ i r) n = φ i (k * n + r)

/-- Every kernel model is a presentation: `a` itself lies in its own `k`-kernel. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_representation"]
lemma IsKernelModel.isPresentation {k : ℕ} {a : ℕ → ℕ} {ι : Type*} {φ : ι → ℕ → ℕ}
    {σ : ι → Fin k → ι} (h : IsKernelModel k a φ σ) : IsPresentation k a φ σ := by
  refine ⟨?_, h.2.2⟩
  have ha : a ∈ Set.range φ := by
    rw [h.2.1]
    exact ⟨0, 0, by norm_num, by funext n; norm_num⟩
  exact ha

/-! ## The eventual image of the `0`-decimation -/

/-- **The eventual image** `ι^∞ = ⋂_m Im f^m` of a self-map ([B1E2b] WP10(ii)). -/
@[category API, AMS 68, ref "B1E2b", group "rb_representation"]
def eventualImage {ι : Type*} (f : ι → ι) : Set ι := ⋂ m, Set.range f^[m]

/-- Periodic points lie in the eventual image. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
lemma mem_eventualImage_of_isPeriodicPt {ι : Type*} {f : ι → ι} {y : ι} {q : ℕ} (hq : 0 < q)
    (h : f^[q] y = y) : y ∈ eventualImage f := by
  have hper : ∀ t, f^[q * t] y = y := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [show q * (t + 1) = q * t + q by ring, Function.iterate_add_apply, h, ih]
  simp only [eventualImage, Set.mem_iInter]
  intro m
  obtain ⟨t, ht⟩ : ∃ t, m ≤ q * t := ⟨m, by nlinarith⟩
  exact ⟨f^[q * t - m] y, by rw [← Function.iterate_add_apply, Nat.add_sub_cancel' ht, hper]⟩

/-- Anything outside the image of `f` is outside the eventual image. -/
@[category API, AMS 68, ref "B1E2b", group "rb_representation"]
lemma notMem_eventualImage_of_notMem_range {ι : Type*} {f : ι → ι} {y : ι}
    (h : y ∉ Set.range f) : y ∉ eventualImage f := by
  intro hy
  simp only [eventualImage, Set.mem_iInter] at hy
  exact h (by simpa using hy 1)

/-- The eventual image is `f`-stable. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
lemma mapsTo_eventualImage {ι : Type*} (f : ι → ι) :
    Set.MapsTo f (eventualImage f) (eventualImage f) := by
  intro x hx
  simp only [eventualImage, Set.mem_iInter] at hx ⊢
  intro m
  obtain ⟨y, hy⟩ := hx m
  exact ⟨f y, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hy]⟩

/-- On a finite type the iterates of a self-map are eventually periodic. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
lemma exists_iterate_add_eq {ι : Type*} [Finite ι] (f : ι → ι) :
    ∃ N p, 0 < p ∧ f^[N + p] = f^[N] := by
  obtain ⟨m₁, m₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => f^[m])
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨m₁, m₂ - m₁, by omega, by rw [show m₁ + (m₂ - m₁) = m₂ by omega]; exact heq.symm⟩
  · exact ⟨m₂, m₁ - m₂, by omega, by rw [show m₂ + (m₁ - m₂) = m₁ by omega]; exact heq⟩

/-- On the eventual image, `f` has finite order. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
lemma exists_iterate_eq_self_on_eventualImage {ι : Type*} [Finite ι] (f : ι → ι) :
    ∃ p, 0 < p ∧ ∀ y ∈ eventualImage f, f^[p] y = y := by
  obtain ⟨N, p, hp, hNp⟩ := exists_iterate_add_eq f
  refine ⟨p, hp, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ : y ∈ Set.range f^[N] := by
    simp only [eventualImage, Set.mem_iInter] at hy; exact hy N
  rw [← hz, ← Function.iterate_add_apply, add_comm p N, hNp]

/-- **The eventual image carries a bijective `0`-decimation** ([B1E2b] WP10(ii)): on `ι^∞` the map
`f` is a permutation.  This is the half of the eventual-image observation that works. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
theorem bijOn_eventualImage {ι : Type*} [Finite ι] (f : ι → ι) :
    Set.BijOn f (eventualImage f) (eventualImage f) := by
  obtain ⟨p, hp, hfix⟩ := exists_iterate_eq_self_on_eventualImage f
  refine (Set.toFinite _).surjOn_iff_bijOn_of_mapsTo (mapsTo_eventualImage f) |>.mp ?_
  intro y hy
  refine ⟨f^[p - 1] y, Set.MapsTo.iterate (mapsTo_eventualImage f) (p - 1) hy, ?_⟩
  calc f (f^[p - 1] y) = f^[p - 1 + 1] y := (Function.iterate_succ_apply' f (p - 1) y).symm
    _ = f^[p] y := by rw [show p - 1 + 1 = p by omega]
    _ = y := hfix y hy

/-- The eventual image of a self-map of a nonempty finite type is nonempty. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
theorem eventualImage_nonempty {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ι) :
    (eventualImage f).Nonempty := by
  obtain ⟨N, p, hp, hNp⟩ := exists_iterate_add_eq f
  obtain ⟨x⟩ := ‹Nonempty ι›
  refine ⟨f^[N] x, mem_eventualImage_of_isPeriodicPt hp ?_⟩
  rw [← Function.iterate_add_apply, add_comm p N, hNp]

/-! ## The necessary condition -/

/-- An injective self-map of a finite type has finite order. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_representation"]
lemma exists_iterate_eq_id {ι : Type*} [Finite ι] {f : ι → ι} (hf : Function.Injective f) :
    ∃ T, 0 < T ∧ f^[T] = id := by
  obtain ⟨N, p, hp, hNp⟩ := exists_iterate_add_eq f
  refine ⟨p, hp, funext fun x => ?_⟩
  refine (hf.iterate N) ?_
  show f^[N] (f^[p] x) = f^[N] (id x)
  rw [← Function.iterate_add_apply, hNp, id_eq]

/-- Reading the intertwining relation `T` times at residue `0`:
`φ (σ(·,0)^T i) n = φ i (k^T·n)`. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_representation"]
lemma phi_iterate_zero {k : ℕ} (hk : 0 < k) {a : ℕ → ℕ} {ι : Type*} {φ : ι → ℕ → ℕ}
    {σ : ι → Fin k → ι} (hpres : IsPresentation k a φ σ) :
    ∀ (T : ℕ) (i : ι) (n : ℕ), φ ((fun i => σ i ⟨0, hk⟩)^[T] i) n = φ i (k ^ T * n) := by
  intro T
  induction T with
  | zero => intro i n; simp
  | succ T ih =>
    intro i n
    rw [Function.iterate_succ_apply, ih (σ i ⟨0, hk⟩) n, hpres.2 i ⟨0, hk⟩ (k ^ T * n)]
    congr 1
    simp [pow_succ]
    ring

/-- **The necessary condition** ([B1E2b] WP10): a finite presentation with bijective `0`-decimation
forces the represented sequence to be invariant under `n ↦ k^T·n` for some `T ≥ 1`.

`σ(·,0)` bijective on a finite state set has finite order `T`; iterating the intertwining relation
`T` times sends every state's sequence to itself along `n ↦ k^T·n`, and one of those states carries
`a`.  Contrapositive: a sequence failing this test has no permutation presentation whatsoever. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem invariant_of_bijective_zero {k : ℕ} (hk : 0 < k) {a : ℕ → ℕ} {ι : Type*} [Finite ι]
    {φ : ι → ℕ → ℕ} {σ : ι → Fin k → ι} (hpres : IsPresentation k a φ σ)
    (hbij : Function.Bijective fun i => σ i ⟨0, hk⟩) :
    ∃ T, 0 < T ∧ ∀ n, a (k ^ T * n) = a n := by
  obtain ⟨T, hT, hid⟩ := exists_iterate_eq_id hbij.injective
  obtain ⟨i₀, hi₀⟩ := hpres.1
  refine ⟨T, hT, fun n => ?_⟩
  have h := phi_iterate_zero hk hpres T i₀ n
  rw [hid] at h
  simp only [id_eq] at h
  rw [hi₀] at h
  exact h.symm

/-! ## The question, and its two known instances -/

/-- **The representation question, as a property** ([B1E2b] WP10, review item B9): does *some*
finite presentation of `a` have a bijective `0`-decimation? -/
@[category API, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
def HasPermutationPresentation (k : ℕ) (hk : 0 < k) (a : ℕ → ℕ) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (φ : ι → ℕ → ℕ) (σ : ι → Fin k → ι),
    IsPresentation k a φ σ ∧ Function.Bijective fun i => σ i ⟨0, hk⟩

/-- The necessary condition, restated for `HasPermutationPresentation`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem invariant_of_hasPermutationPresentation {k : ℕ} (hk : 0 < k) {a : ℕ → ℕ}
    (h : HasPermutationPresentation k hk a) : ∃ T, 0 < T ∧ ∀ n, a (k ^ T * n) = a n := by
  obtain ⟨ι, hfin, φ, σ, hpres, hbij⟩ := h
  exact invariant_of_bijective_zero hk hpres hbij

/-- Appending binary zeros does not change the digit sum: `t(2^T·n) = t(n)`. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_representation"]
lemma thueMorse_two_pow_mul (T n : ℕ) : thueMorse (2 ^ T * n) = thueMorse n := by
  induction T with
  | zero => simp
  | succ T ih => rw [show 2 ^ (T + 1) * n = 2 * (2 ^ T * n) by ring, thueMorse_two_mul, ih]

/-- The same for the Cantor sequence in base `3`. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_representation"]
lemma cantorSeq_three_pow_mul (T n : ℕ) : cantorSeq (3 ^ T * n) = cantorSeq n := by
  induction T with
  | zero => simp
  | succ T ih => rw [show 3 ^ (T + 1) * n = 3 * (3 ^ T * n) by ring, cantorSeq_three_mul, ih]

/-- **Positive instance**: Thue–Morse has a permutation presentation — its own kernel model, whose
`0`-decimation is the identity. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem thueMorse_hasPermutationPresentation :
    HasPermutationPresentation 2 (by norm_num) thueMorse :=
  ⟨Fin 2, inferInstance, tmPhi, tmSigma, thueMorse_isKernelModel.isPresentation, by decide⟩

/-- **Positive instance, base `3`**: the Cantor sequence. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem cantorSeq_hasPermutationPresentation :
    HasPermutationPresentation 3 (by norm_num) cantorSeq :=
  ⟨Fin 2, inferInstance, cantorPhi, cantorSigma, cantorSeq_isKernelModel.isPresentation, by decide⟩

/-- **Negative instance, for every presentation at once** ([B1E2b] WP10): no finite presentation of
the parity sequence has a bijective `0`-decimation, because `p(2^T·n) = p(n)` fails at `n = 1`
(`2^T` is even for `T ≥ 1`, while `1` is odd).

This is strictly stronger than WP9's `paritySigma_zero_not_injective`, which only says the *kernel*
model collapses. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem paritySeq_no_bijective_zero {ι : Type*} [Finite ι] {φ : ι → ℕ → ℕ}
    {σ : ι → Fin 2 → ι} (hpres : IsPresentation 2 paritySeq φ σ) :
    ¬ Function.Bijective fun i => σ i ⟨0, by norm_num⟩ := by
  intro hbij
  obtain ⟨T, hT, hinv⟩ := invariant_of_bijective_zero (by norm_num) hpres hbij
  have h1 := hinv 1
  have h2 : (2 : ℕ) ∣ 2 ^ T := dvd_pow_self 2 hT.ne'
  rw [show paritySeq (2 ^ T * 1) = (2 ^ T * 1) % 2 from rfl,
    show paritySeq 1 = 1 % 2 from rfl] at h1
  omega

/-- **The parity sequence has no permutation presentation** ([B1E2b] WP10). -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem paritySeq_not_hasPermutationPresentation :
    ¬ HasPermutationPresentation 2 (by norm_num) paritySeq := by
  rintro ⟨ι, hfin, φ, σ, hpres, hbij⟩
  exact paritySeq_no_bijective_zero hpres hbij

/-! ## Why the eventual image does not settle the question ([B1E2b] WP10(ii)) -/

/-- **First failure: the eventual image can lose the sequence.** In the parity system no state of
`ι^∞` carries `paritySeq` — the state that does is in the image of no decimation.  So restricting
to `ι^∞` produces a permutation system that represents something else. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem paritySeq_notMem_eventualImage :
    ∀ i ∈ eventualImage (fun i => paritySigma i ⟨0, by norm_num⟩), parityPhi i ≠ paritySeq := by
  intro i hi hcon
  have h0 : (0 : Fin 3) ∉ eventualImage (fun i => paritySigma i ⟨0, by norm_num⟩) :=
    notMem_eventualImage_of_notMem_range (by decide)
  have : i = 0 := paritySeq_isKernelModel.1 (by rw [hcon]; rfl)
  exact h0 (this ▸ hi)

/-- A decimation whose eventual image is not closed under `σ(·,1)`: `k = 2`,
`σ(0,·) = (1,0)`, `σ(1,·) = (1,0)`, `σ(2,·) = (2,2)`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_representation"]
def notClosedSigma : Fin 3 → Fin 2 → Fin 3 := ![![1, 0], ![1, 0], ![2, 2]]

/-- **Second failure: the eventual image need not be a subsystem.** State `1` is a fixed point of
`σ(·,0)`, hence lies in `ι^∞`, but `σ(1,1) = 0` is in the image of no `σ(·,0)`-iterate.  So `ι^∞`
is not closed under the other decimations and carries no Mahler system by itself. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
theorem eventualImage_not_closed_example :
    ∃ i ∈ eventualImage (fun i => notClosedSigma i ⟨0, by norm_num⟩),
      notClosedSigma i ⟨1, by norm_num⟩ ∉
        eventualImage (fun i => notClosedSigma i ⟨0, by norm_num⟩) := by
  refine ⟨1, mem_eventualImage_of_isPeriodicPt Nat.one_pos (by decide), ?_⟩
  have h : notClosedSigma 1 ⟨1, by norm_num⟩ = 0 := by decide
  rw [h]
  exact notMem_eventualImage_of_notMem_range (by decide)

/-! ## The question, stated -/

/-- **The representation question** ([B1E2b] WP10, review item B9) — *stated, not answered*.

> Is a `k`-automatic sequence invariant under `n ↦ k^T·n` for some `T ≥ 1` necessarily one with a
> permutation presentation?

The forward implication is `invariant_of_hasPermutationPresentation`, so this asks exactly whether
the necessary condition found here is sufficient.  What is known against the two obvious
constructions: base change cannot repair a collapse (`RB.sigma_pow_zero_perm_iff`), and the
eventual image, although it does carry a permutation, need not contain the sequence
(`paritySeq_notMem_eventualImage`) and need not be closed under the other decimations
(`eventualImage_not_closed_example`).

**Open.**  Recorded as a `def : Prop`, never an axiom and with no conjectured answer — the corpus
policy on open problems, and the plan's instruction not to promise a program. -/
@[category API, AMS 11 68, ref "AF17" "B1E2b", group "rb_representation"]
def RepresentationQuestion (k : ℕ) (hk : 0 < k) : Prop :=
  ∀ a : ℕ → ℕ, (kKernel k a).Finite → (∃ T, 0 < T ∧ ∀ n, a (k ^ T * n) = a n) →
    HasPermutationPresentation k hk a

end RB
