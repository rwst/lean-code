/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.RingTheory.PowerSeries.Rationality
import ForMathlib.Combinatorics.InfiniteComplexity

/-!
# Rational series with finitely many coefficient values

Over an integral domain, a formal power series whose coefficient sequence takes only **finitely
many values** is a rational series *if and only if* that sequence is **eventually periodic**:

`isRationalSeries_iff_isEventuallyPeriodic_coeff`.

Both directions are cheap, because both halves already exist:

* **(⇒)** `IsRationalSeries.exists_recurrence` (Bertin's Proposition 1.1, in
  `ForMathlib.RingTheory.PowerSeries.Rationality`) turns `Q · F = P` into a linear recurrence
  `q₀ aₙ + q₁ aₙ₋₁ + ⋯ + q_s aₙ₋ₛ = 0` valid for `n ≥ n₀`, with `q₀ ≠ 0`.  In a domain `q₀`
  cancels, so the length-`s` window `(aₙ₋ₛ, …, aₙ₋₁)` *determines* `aₙ`; that is exactly
  `ForMathlib.SubwordComplexity.RightDeterministic` for the shifted sequence, and
  `isEventuallyPeriodic_of_rightDeterministic` (the Morse–Hedlund pigeonhole) does the rest.
  Finiteness of the coefficient *set* — not of the ambient ring — is what makes the state space
  finite, so the sequence is passed through the subtype `↥(Set.range a)`.
* **(⇐)** eventual periodicity *is* the recurrence `aₙ − aₙ₋ₚ = 0`, so
  `exists_recurrence.isRationalSeries` applies verbatim.  No finiteness and no domain hypothesis
  is needed here, only `Nontrivial` (in the zero ring no `Q ≠ 0` exists, so *nothing* is rational).

Note the asymmetry: the forward direction needs no divisibility or normalization of the
denominator — a factor `Xᵐ ∣ Q` is harmless, since the recurrence produced by Proposition 1.1
already has its leading coefficient at `Q`'s *trailing* degree.

## Main results

* `rightDeterministic_of_recurrence` — a linear recurrence with `q₀ ≠ 0` makes the length-`s`
  window right-deterministic (from index `n₀` on).
* `isEventuallyPeriodic_of_recurrence` — recurrence + finitely many values ⇒ eventually periodic.
* `IsRationalSeries.isEventuallyPeriodic_coeff` — rational + finitely many values ⇒ eventually
  periodic.
* `isRationalSeries_of_isEventuallyPeriodic_coeff` — the converse.
* `isRationalSeries_iff_isEventuallyPeriodic_coeff` — the characterization.
* `not_isRationalSeries_of_not_isEventuallyPeriodic` — the contrapositive interface: a
  finite-valued coefficient sequence that is *not* eventually periodic has a non-rational
  generating series.
* `finite_range_of_abs_le`, `IsRationalSeries.isEventuallyPeriodic_coeff_of_abs_le` — the
  *bounded integer coefficients* form, which is how the literature states the hypothesis.

## Scope

This is the elementary half of the classical circle of ideas.  **Fatou's theorem** — an integer
power series with radius of convergence `≥ 1` that is algebraic over `ℚ(z)` is rational — is *not*
proved here, and none of the above is a step towards it: everything here is coefficient
combinatorics, with no analysis.  A statement of the form "finitely many integer values and not
ultimately periodic ⇒ the generating function is transcendental over `ℚ(z)`" ([AF17] §8.1) needs
that analytic input, or some other route from algebraicity to a recurrence.

## References

* [Ber92] M. J. Bertin, *Pisot and Salem Numbers*, Birkhäuser, 1992: Proposition 1.1 (the
  rationality ⟺ recurrence dictionary consumed here).
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866
  (the determinism ⇒ eventual periodicity pigeonhole, in
  `ForMathlib.Combinatorics.InfiniteComplexity`).
* [AF17] B. Adamczewski, C. Faverjon, *Méthode de Mahler : relations linéaires, transcendance et
  applications aux nombres automatiques*, Proc. LMS **115** (2017), 55–90: §8.1 uses the
  finite-values/not-ultimately-periodic hypothesis in exactly this way.
-/

open ForMathlib.SubwordComplexity
open scoped Polynomial PowerSeries

variable {K : Type*}

section Domain

variable [CommRing K] [IsDomain K]

/-- **A linear recurrence is a deterministic rule.**  If `∑_{i ≤ s} qᵢ aₙ₋ᵢ = 0` for all `n ≥ n₀`
and `q₀ ≠ 0`, then in a domain the length-`s` window determines the next term: the shifted
sequence `m ↦ a (m + n₀)` is right-deterministic at level `s`. -/
theorem rightDeterministic_of_recurrence {a : ℕ → K} {s n₀ : ℕ} {q : ℕ → K} (hq0 : q 0 ≠ 0)
    (hrec : ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * a (n - i) = 0) :
    RightDeterministic (fun m => a (m + n₀)) s := by
  intro i j hij
  show a (i + s + n₀) = a (j + s + n₀)
  refine mul_left_cancel₀ hq0 ?_
  -- Solve the recurrence at index `m + s + n₀` for its top term.
  have key : ∀ m : ℕ, q 0 * a (m + s + n₀)
      = -∑ l ∈ Finset.range s, q (l + 1) * a (m + (s - l - 1) + n₀) := by
    intro m
    have h := hrec (m + s + n₀) (by omega)
    rw [Finset.sum_range_succ'] at h
    have hsum : ∑ l ∈ Finset.range s, q (l + 1) * a (m + s + n₀ - (l + 1))
        = ∑ l ∈ Finset.range s, q (l + 1) * a (m + (s - l - 1) + n₀) :=
      Finset.sum_congr rfl fun l hl => by
        rw [Finset.mem_range] at hl
        rw [show m + s + n₀ - (l + 1) = m + (s - l - 1) + n₀ from by omega]
    rw [hsum, Nat.sub_zero] at h
    linear_combination h
  rw [key i, key j]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  have hw : a (i + (s - l - 1) + n₀) = a (j + (s - l - 1) + n₀) := hij (s - l - 1) (by omega)
  rw [hw]

/-- **Recurrence + finitely many values ⇒ eventually periodic.**  The window evolves
deterministically (`rightDeterministic_of_recurrence`) on the finite state space
`↥(Set.range a)`, so the Morse–Hedlund pigeonhole applies. -/
theorem isEventuallyPeriodic_of_recurrence {a : ℕ → K} (hfin : (Set.range a).Finite)
    {s n₀ : ℕ} {q : ℕ → K} (hq0 : q 0 ≠ 0)
    (hrec : ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * a (n - i) = 0) :
    IsEventuallyPeriodic a := by
  haveI : Finite ↥(Set.range a) := hfin.to_subtype
  have hdet := rightDeterministic_of_recurrence hq0 hrec
  have hdet' : RightDeterministic
      (fun m => (⟨a (m + n₀), Set.mem_range_self _⟩ : ↥(Set.range a))) s := fun i j hij =>
    Subtype.ext (hdet i j fun t ht => congrArg Subtype.val (hij t ht))
  obtain ⟨N, p, hp, hper⟩ := isEventuallyPeriodic_of_rightDeterministic _ hdet'
  refine ⟨N + n₀, p, hp, fun k hk => ?_⟩
  have h := congrArg Subtype.val (hper (k - n₀) (by omega))
  simp only at h
  rwa [show k - n₀ + p + n₀ = k + p from by omega, show k - n₀ + n₀ = k from by omega] at h

/-- **A rational series with finitely many coefficient values has an eventually periodic
coefficient sequence.**  Bertin's Proposition 1.1 supplies the recurrence; the pigeonhole does the
rest.  No analysis, and no hypothesis on the denominator beyond `Q ≠ 0`. -/
theorem IsRationalSeries.isEventuallyPeriodic_coeff {F : K⟦X⟧} (hF : IsRationalSeries F)
    (hfin : (Set.range fun n => PowerSeries.coeff n F).Finite) :
    IsEventuallyPeriodic fun n => PowerSeries.coeff n F := by
  obtain ⟨s, n₀, q, hq0, -, hrec⟩ := hF.exists_recurrence
  exact isEventuallyPeriodic_of_recurrence hfin hq0 hrec

/-- **The contrapositive**, and the form every consumer wants: a coefficient sequence that takes
finitely many values and is *not* eventually periodic has a **non-rational** generating series. -/
theorem not_isRationalSeries_of_not_isEventuallyPeriodic {F : K⟦X⟧}
    (hfin : (Set.range fun n => PowerSeries.coeff n F).Finite)
    (hper : ¬ IsEventuallyPeriodic fun n => PowerSeries.coeff n F) : ¬ IsRationalSeries F :=
  fun hF => hper (hF.isEventuallyPeriodic_coeff hfin)

end Domain

section Converse

variable [CommRing K] [Nontrivial K]

/-- **The converse**: an eventually periodic coefficient sequence makes the series rational —
`aₙ − aₙ₋ₚ = 0` *is* a linear recurrence with leading coefficient `1`.  Neither finiteness of the
coefficient set nor a domain hypothesis is needed; `Nontrivial` is, since in the zero ring no
denominator `Q ≠ 0` exists. -/
theorem isRationalSeries_of_isEventuallyPeriodic_coeff {F : K⟦X⟧}
    (h : IsEventuallyPeriodic fun n => PowerSeries.coeff n F) : IsRationalSeries F := by
  classical
  obtain ⟨N, p, hp, hper⟩ := h
  refine exists_recurrence.isRationalSeries
    ⟨p, N + p, fun i => if i = 0 then 1 else if i = p then -1 else 0, by simp,
      by omega, fun n hn => ?_⟩
  have hsplit : ∀ i ∈ Finset.range (p + 1),
      (if i = 0 then (1 : K) else if i = p then -1 else 0) * PowerSeries.coeff (n - i) F
        = (if i = 0 then PowerSeries.coeff n F else 0)
          - (if i = p then PowerSeries.coeff (n - p) F else 0) := by
    intro i _
    rcases eq_or_ne i 0 with rfl | h0
    · simp [hp.ne]
    · rcases eq_or_ne i p with rfl | hip
      · simp [h0]
      · simp [h0, hip]
  have h1 : ∑ i ∈ Finset.range (p + 1), (if i = 0 then PowerSeries.coeff n F else 0)
      = PowerSeries.coeff n F := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => if_neg hb)
      (fun hb => absurd (Finset.mem_range.mpr (by omega)) hb), if_pos rfl]
  have h2 : ∑ i ∈ Finset.range (p + 1), (if i = p then PowerSeries.coeff (n - p) F else 0)
      = PowerSeries.coeff (n - p) F := by
    rw [Finset.sum_eq_single p (fun b _ hb => if_neg hb)
      (fun hb => absurd (Finset.mem_range.mpr (by omega)) hb), if_pos rfl]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, h1, h2, sub_eq_zero]
  have := hper (n - p) (by omega)
  rwa [show n - p + p = n from by omega] at this

end Converse

section Characterization

variable [CommRing K] [IsDomain K]

/-- **The characterization.**  Over an integral domain, a power series whose coefficients take
finitely many values is rational **iff** its coefficient sequence is eventually periodic. -/
theorem isRationalSeries_iff_isEventuallyPeriodic_coeff {F : K⟦X⟧}
    (hfin : (Set.range fun n => PowerSeries.coeff n F).Finite) :
    IsRationalSeries F ↔ IsEventuallyPeriodic fun n => PowerSeries.coeff n F :=
  ⟨fun hF => hF.isEventuallyPeriodic_coeff hfin, isRationalSeries_of_isEventuallyPeriodic_coeff⟩

end Characterization

section Integer

/-- A bounded integer sequence has finite range. -/
theorem finite_range_of_abs_le {a : ℕ → ℤ} {B : ℤ} (h : ∀ n, |a n| ≤ B) : (Set.range a).Finite := by
  refine (Set.finite_Icc (-B) B).subset ?_
  rintro _ ⟨n, rfl⟩
  exact Set.mem_Icc.mpr (abs_le.mp (h n))

/-- **The bounded-integer form**, as the hypothesis is usually stated: an integer power series with
bounded coefficients which is a rational series has an eventually periodic coefficient
sequence. -/
theorem IsRationalSeries.isEventuallyPeriodic_coeff_of_abs_le {F : ℤ⟦X⟧} {B : ℤ}
    (hF : IsRationalSeries F) (hB : ∀ n, |PowerSeries.coeff n F| ≤ B) :
    IsEventuallyPeriodic fun n => PowerSeries.coeff n F :=
  hF.isEventuallyPeriodic_coeff (finite_range_of_abs_le hB)

end Integer
