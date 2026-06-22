/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section
/-!
# Divisibility and the norm in the `p`-adic integers

The `p`-adic integers `ℤ_[p]` form a discrete valuation ring whose norm takes the discrete set of
values `{0} ∪ {p ^ (-n) : n ∈ ℕ}`. Consequently divisibility is governed entirely by the norm:
`a ∣ b` holds exactly when `b` is no larger than `a`, i.e. `‖b‖ ≤ ‖a‖`.

## Main statements

* `PadicInt.dvd_iff_norm_le`: in `ℤ_[p]`, `a ∣ b ↔ ‖b‖ ≤ ‖a‖`.
-/

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Divisibility is determined by the norm in `ℤ_[p]`.** Since `ℤ_[p]` is a discrete valuation
ring, `a` divides `b` iff `b` is no larger than `a` in the `p`-adic norm: `a ∣ b ↔ ‖b‖ ≤ ‖a‖`.

The forward direction is multiplicativity, `‖a * c‖ = ‖a‖ * ‖c‖ ≤ ‖a‖`. The reverse uses that `a`
and `b` are units times `p ^ valuation`, so `‖b‖ ≤ ‖a‖` forces `a.valuation ≤ b.valuation`, whence
`a ∣ p ^ a.valuation ∣ b`. -/
theorem dvd_iff_norm_le (a b : ℤ_[p]) : a ∣ b ↔ ‖b‖ ≤ ‖a‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg a) (PadicInt.norm_le_one c)
  · intro h
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      rw [norm_zero] at h
      rw [norm_le_zero_iff.mp h]
    · rcases eq_or_ne b 0 with hb | hb
      · subst hb; exact dvd_zero a
      · obtain ⟨u, hu⟩ : ∃ u : ℤ_[p]ˣ, a = ↑u * (p : ℤ_[p]) ^ a.valuation :=
          ⟨unitCoeff ha, unitCoeff_spec ha⟩
        obtain ⟨v, hv⟩ : ∃ v : ℤ_[p]ˣ, b = ↑v * (p : ℤ_[p]) ^ b.valuation :=
          ⟨unitCoeff hb, unitCoeff_spec hb⟩
        generalize hm : a.valuation = m at hu
        generalize hk : b.valuation = k at hv
        have hval : m ≤ k := by
          rw [PadicInt.norm_eq_zpow_neg_valuation ha, PadicInt.norm_eq_zpow_neg_valuation hb,
            hm, hk] at h
          have h1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
          rwa [zpow_le_zpow_iff_right₀ h1, neg_le_neg_iff, Int.ofNat_le] at h
        have hap : a ∣ (p : ℤ_[p]) ^ m :=
          ⟨↑u⁻¹, by rw [hu, mul_right_comm, ← Units.val_mul]; simp⟩
        have hpb : (p : ℤ_[p]) ^ m ∣ b := (pow_dvd_pow _ hval).trans ⟨↑v, by rw [hv]; ring⟩
        exact hap.trans hpb

end PadicInt
