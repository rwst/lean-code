/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.NumberTheory.ConjugatePowerSum
import ForMathlib.NumberTheory.PisotNumber

/-!
# The fractional parts of the powers of a Pisot number

The defining property of a Pisot–Vijayaraghavan number `θ` is that its non-dominant conjugates
lie strictly inside the unit disc.  Combined with the integrality of the conjugate power sums
(`conj_powerSum_isInt`) this gives the classical statement that motivates the definition:

  **`θⁿ` approaches the rational integers exponentially fast**, `‖θⁿ‖ ≤ C ρⁿ` with `ρ < 1`.

The same argument applies verbatim to `(θ-1)θᵐ` — or to `P(θ)θᵐ` for any `P ∈ ℤ[X]` — because
the only inputs are that the full conjugate sum is a rational integer and that the non-dominant
conjugate contributions are geometrically small.  The `(θ-1)` variant is the one that governs
the Cantor set `C(θ) = (θ-1)·{∑ εₖθ^{-k}}` and its Erdős products.

## Main results

* `exists_bound_of_forall_norm_lt_one` — a finite multiset of complex numbers of modulus `< 1`
  has a uniform bound `ρ < 1`;
* `IsPisot.exists_int_pow_close` — `∃ C ρ < 1, ∀ n, dist(θⁿ, ℤ) ≤ C ρⁿ`;
* `IsPisot.exists_int_sub_one_mul_pow_close` — the same for `(θ-1)θᵐ`.

## Implementation notes

The bound `ρ` is produced by a multiset induction rather than by `Finset.sup'`, so that the
empty case (a rational integer `θ`, whose minimal polynomial is linear) needs no separate
treatment: there `ρ = 0` and the distance is exactly `0`.
-/

open Polynomial

/-- A finite multiset of complex numbers all of modulus `< 1` admits a uniform bound `ρ < 1`. -/
theorem exists_bound_of_forall_norm_lt_one {s : Multiset ℂ} (h : ∀ z ∈ s, ‖z‖ < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ s, ‖z‖ ≤ ρ := by
  induction s using Multiset.induction with
  | empty => exact ⟨0, le_refl 0, by norm_num, by simp⟩
  | cons a s ih =>
      obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ih (fun z hz => h z (Multiset.mem_cons_of_mem hz))
      refine ⟨max ρ ‖a‖, le_trans hρ0 (le_max_left _ _),
        max_lt hρ1 (h a (Multiset.mem_cons_self a s)), ?_⟩
      intro z hz
      rcases Multiset.mem_cons.mp hz with rfl | hz
      · exact le_max_right _ _
      · exact le_trans (hρ z hz) (le_max_left _ _)

/-- The non-dominant conjugates of a Pisot number all have modulus `< 1`.  (The conjugates are
distinct, so erasing one copy of `θ` leaves no other copy behind.) -/
theorem IsPisot.norm_lt_one_of_mem_erase {θ : ℝ} (hθ : IsPisot θ) :
    ∀ z ∈ ((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ), ‖z‖ < 1 := by
  intro z hz
  rw [(nodup_aroots_minpoly θ hθ.2.1).mem_erase_iff] at hz
  exact hθ.2.2 z hz.2 hz.1

/-- A uniform geometric ratio for the non-dominant conjugates of a Pisot number. -/
theorem IsPisot.exists_ratio {θ : ℝ} (hθ : IsPisot θ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ ((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ), ‖z‖ ≤ ρ :=
  exists_bound_of_forall_norm_lt_one hθ.norm_lt_one_of_mem_erase

/-- **The powers of a Pisot number approach the integers geometrically.**  There are `C ≥ 0` and
`ρ < 1` with `|θⁿ - Tₙ| ≤ C ρⁿ` for suitable integers `Tₙ`; one may take `ρ = max_{j≥2}|θ_j|`
and `C = d - 1`. -/
theorem IsPisot.exists_int_pow_close {θ : ℝ} (hθ : IsPisot θ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ, ∃ T : ℤ, |θ ^ n - (T : ℝ)| ≤ C * ρ ^ n := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := hθ.exists_ratio
  refine ⟨(Multiset.card (((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ)) : ℝ), ρ, by positivity,
    hρ0, hρ1, ?_⟩
  intro n
  obtain ⟨T, hT⟩ := conj_powerSum_isInt θ hθ.2.1 n
  refine ⟨T, ?_⟩
  refine exists_int_sub_le_of_conj θ hθ.2.1 hT (by push_cast; ring) ?_
  intro z hz
  calc ‖z ^ n‖ = ‖z‖ ^ n := by rw [norm_pow]
    _ ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg _) (hρ z hz) n

/-- **The `(θ-1)`-ladder of a Pisot number approaches the integers geometrically.**  The same
statement for `(θ-1)θᵐ`, the sequence that generates the Cantor set `C(θ)`; here
`C = (d-1)(1+ρ)`. -/
theorem IsPisot.exists_int_sub_one_mul_pow_close {θ : ℝ} (hθ : IsPisot θ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ m : ℕ, ∃ T : ℤ, |(θ - 1) * θ ^ m - (T : ℝ)| ≤ C * ρ ^ m := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := hθ.exists_ratio
  refine ⟨(Multiset.card (((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ)) : ℝ) * (1 + ρ), ρ,
    by positivity, hρ0, hρ1, ?_⟩
  intro m
  obtain ⟨T, hT⟩ := conj_shiftedPowerSum_isInt θ hθ.2.1 m
  refine ⟨T, ?_⟩
  rw [mul_assoc]
  refine exists_int_sub_le_of_conj θ hθ.2.1 hT (by push_cast; ring) ?_
  intro z hz
  have hz' := hρ z hz
  have h1 : ‖z - 1‖ ≤ 1 + ρ := by
    have h := norm_sub_le z (1 : ℂ)
    simp only [norm_one] at h
    linarith
  have h2 : ‖z‖ ^ m ≤ ρ ^ m := pow_le_pow_left₀ (norm_nonneg _) hz' m
  calc ‖(z - 1) * z ^ m‖ = ‖z - 1‖ * ‖z‖ ^ m := by rw [norm_mul, norm_pow]
    _ ≤ (1 + ρ) * ρ ^ m := by
        have := pow_nonneg (norm_nonneg z) m
        nlinarith [norm_nonneg (z - 1), pow_nonneg hρ0 m]
