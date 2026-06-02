/-
# Rational formal power series and linear recurrences (Bertin, Proposition 1.1)

A formal series `F = ∑ aₙ Xⁿ`, an element of `K⟦X⟧` over a field `K`, is a *rational
series* if and only if its coefficients eventually satisfy a linear recurrence

`q₀ aₙ + q₁ aₙ₋₁ + ⋯ + q_s aₙ₋ₛ = 0`   for all `n ≥ n₀`,   with `q₀ ≠ 0`.   (∗)

Reference: M.-J. Bertin et al., *Pisot and Salem Numbers*, Proposition 1.1
(statement and proof transcribed from the source).

Proof (transcribed from the source):
* If `F` is a rational series it can be written `F = P/Q` with `P Q : K[X]`, `Q(0) ≠ 0`,
  `deg Q = r`. From the formal identity `Q F = P`, equating the coefficient of `Xⁿ` for
  `n ≥ n₀ := max (r + 1) s` yields exactly the relation (∗).
* Conversely set `Q := ∑_{0 ≤ i ≤ s} qᵢ Xⁱ` (so `Q(0) = q₀ ≠ 0`). The relations (∗) say
  every coefficient of `Q F` of index `≥ n₀` vanishes, hence `Q F = P` with `deg P ≤ n₀ - 1`,
  so `F = P/Q` is a rational series.

We work over a field and do not assume the chosen denominator has nonzero constant term:
the forward direction reads the recurrence off `Q F = P` after shifting indices by
`Q.natTrailingDegree`, which makes the leading coefficient `Q`'s trailing coefficient (`≠ 0`).
-/
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Basic

open scoped Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- `F ∈ K⟦X⟧` is a **rational series** when it is the power-series expansion of a ratio
`P/Q` of polynomials, i.e. the formal identity `Q * F = P` holds for some `P Q : K[X]`
with `Q ≠ 0`. (Equivalently `F` lies in the image of `K(X)` inside `K⟦X⟧`.) -/
def IsRationalSeries (F : K⟦X⟧) : Prop :=
  ∃ P Q : K[X], Q ≠ 0 ∧ (Q : K⟦X⟧) * F = (P : K⟦X⟧)

/-- The `n`-th coefficient of `Q * F` for a polynomial `Q` is the finite convolution
`∑_{i ≤ n} Q.coeff i * a_{n-i}`. This is the bridge between the formal identity `Q * F = P`
and the coefficient relation (∗). -/
theorem coeff_coe_mul (Q : K[X]) (G : K⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m ((Q : K⟦X⟧) * G)
      = ∑ i ∈ Finset.range (m + 1), Q.coeff i * PowerSeries.coeff (m - i) G := by
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe]

/-- **Proposition 1.1, forward direction.** The coefficients of a rational series eventually
satisfy a linear recurrence (∗) with nonzero leading coefficient. -/
theorem IsRationalSeries.exists_recurrence {F : K⟦X⟧} (hF : IsRationalSeries F) :
    ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
      ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0 := by
  obtain ⟨P, Q, hQ, hQF⟩ := hF
  have hk : Q.natTrailingDegree ≤ Q.natDegree := Q.natTrailingDegree_le_natDegree
  refine ⟨Q.natDegree - Q.natTrailingDegree, max Q.natDegree (P.natDegree + 1),
    fun j => Q.coeff (Q.natTrailingDegree + j), ?_, ?_, ?_⟩
  · -- `q 0 = Q`'s trailing coefficient, nonzero since `Q ≠ 0`.
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQ
  · -- `s ≤ n₀`.
    exact (Nat.sub_le _ _).trans (le_max_left _ _)
  · -- the recurrence, read off `Q * F = P` at index `n + Q.natTrailingDegree`.
    intro n hn
    show ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
        Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F = 0
    obtain ⟨hnQ, hnP⟩ := max_le_iff.mp hn
    have key : PowerSeries.coeff (n + Q.natTrailingDegree) ((Q : K⟦X⟧) * F)
        = ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
            Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F :=
      calc PowerSeries.coeff (n + Q.natTrailingDegree) ((Q : K⟦X⟧) * F)
          = ∑ i ∈ Finset.range (n + Q.natTrailingDegree + 1),
              Q.coeff i * PowerSeries.coeff (n + Q.natTrailingDegree - i) F :=
            coeff_coe_mul Q F _
        _ = ∑ i ∈ Finset.Ico Q.natTrailingDegree (Q.natDegree + 1),
              Q.coeff i * PowerSeries.coeff (n + Q.natTrailingDegree - i) F :=
            (Finset.sum_subset
              (fun x hx => by simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega)
              (fun x _ hx => by
                simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
                obtain h | h := hx
                · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree h, zero_mul]
                · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])).symm
        _ = ∑ i ∈ Finset.range (Q.natDegree - Q.natTrailingDegree + 1),
              Q.coeff (Q.natTrailingDegree + i) * PowerSeries.coeff (n - i) F := by
            rw [Finset.sum_Ico_eq_sum_range, show Q.natDegree + 1 - Q.natTrailingDegree
                = Q.natDegree - Q.natTrailingDegree + 1 from by omega]
            exact Finset.sum_congr rfl fun i _ => by
              rw [show n + Q.natTrailingDegree - (Q.natTrailingDegree + i) = n - i from by omega]
    rw [← key, hQF, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Proposition 1.1, converse direction.** A formal series whose coefficients eventually
satisfy a linear recurrence (∗) with nonzero leading coefficient is a rational series. -/
theorem exists_recurrence.isRationalSeries {F : K⟦X⟧}
    (h : ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
        ∀ n, n₀ ≤ n → ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0) :
    IsRationalSeries F := by
  obtain ⟨s, n₀, q, hq0, hsn, hrec⟩ := h
  set Q : K[X] := ∑ i ∈ Finset.range (s + 1), Polynomial.monomial i (q i) with hQdef
  have hQcoeff : ∀ j, Q.coeff j = if j < s + 1 then q j else 0 := by
    intro j
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', Finset.mem_range]
  -- Every coefficient of `Q * F` of index `≥ n₀` vanishes, by the recurrence.
  have hvanish : ∀ m, n₀ ≤ m → PowerSeries.coeff m ((Q : K⟦X⟧) * F) = 0 := by
    intro m hm
    have hsplit : ∑ i ∈ Finset.range (m + 1), Q.coeff i * PowerSeries.coeff (m - i) F
        = ∑ i ∈ Finset.range (s + 1), Q.coeff i * PowerSeries.coeff (m - i) F :=
      (Finset.sum_subset
        (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
        (fun x _ hx => by
          rw [Finset.mem_range, not_lt] at hx
          rw [hQcoeff, if_neg (show ¬ x < s + 1 by omega), zero_mul])).symm
    rw [coeff_coe_mul, hsplit,
      Finset.sum_congr rfl fun i hi => by rw [hQcoeff, if_pos (Finset.mem_range.mp hi)]]
    exact hrec m hm
  refine ⟨PowerSeries.trunc n₀ ((Q : K⟦X⟧) * F), Q, ?_, ?_⟩
  · -- `Q ≠ 0`, since `Q.coeff 0 = q 0 ≠ 0`.
    refine fun hQ0 => hq0 ?_
    have h0 := hQcoeff 0
    rw [hQ0, Polynomial.coeff_zero, if_pos (Nat.succ_pos s)] at h0
    exact h0.symm
  · -- `Q * F` agrees with its truncation, as all higher coefficients vanish.
    ext m
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hm
    exacts [rfl, hvanish m (by omega)]

/-- **Proposition 1.1.** A formal power series `F = ∑ aₙ Xⁿ ∈ K⟦X⟧` over a field is a
rational series if and only if there exist `s n₀ : ℕ` and coefficients `q : ℕ → K` with
`q 0 ≠ 0` such that the coefficients `aₙ = PowerSeries.coeff n F` satisfy

`q 0 * aₙ + q 1 * aₙ₋₁ + ⋯ + q s * aₙ₋ₛ = 0`   for every `n ≥ n₀`.

The side hypothesis `s ≤ n₀` records that the recurrence is read at indices `n ≥ n₀ ≥ s`,
so the lowest index `n - s` is a genuine (non-truncated) natural number; it is automatically
satisfiable, since both directions produce such witnesses. -/
theorem isRationalSeries_iff_exists_recurrence (F : K⟦X⟧) :
    IsRationalSeries F ↔
      ∃ (s n₀ : ℕ) (q : ℕ → K), q 0 ≠ 0 ∧ s ≤ n₀ ∧
        ∀ n, n₀ ≤ n →
          ∑ i ∈ Finset.range (s + 1), q i * PowerSeries.coeff (n - i) F = 0 :=
  ⟨IsRationalSeries.exists_recurrence, exists_recurrence.isRationalSeries⟩
