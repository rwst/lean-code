/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.ValuationArm

/-!
# The weighted two-place functional (strategy B2)

Strategy **B2** of `plans/report3-BB13.html` asks for a lower bound on a *weighted* quality,
mixing the archimedean size of the residue `kₐ = 3ᵃ − mₐ2ᵃ` with the `2`-adic depth
`v₂(mₐ)` of the nearest-integer numerator, and prices what such a bound would buy for the
per-line problem.  This file supplies the two halves that are mathematics rather than
construction: the **elimination step** that converts `2^H ∣ mₐ` into a factor `2^H` in the main
term (§1–§2), and the **payoff**, i.e. the fibre cap any weighted rate implies (§3).

## The statement to aim at, and a correction

The report writes the target as `|kₐ|·2^{β v₂(mₐ)} ≥ c₁ᵃ`.  With `β > 0` that inequality is
*weaker* than the unweighted `|kₐ| ≥ c₁ᵃ` and implies no cap at all: it lets `|kₐ|` shrink as the
depth grows, which is the opposite of what the `min` structure needs.  The intended statement —
the one whose cap is the report's own `(0.585 − log₂c₁)a/(1 + β)` — carries the weight on the
other side,

`|kₐ| ≥ c₁ᵃ · 2^{β·v₂(mₐ)}`   (equivalently `|kₐ|·2^{−β v₂(mₐ)} ≥ c₁ᵃ`),

"depth must be paid for in archimedean size".  `weighted_fibre_cap` proves the cap from this
form, and the `β = 0` case (`fibre_cap_of_rate`) is the classical `D`-arm cap that the rate
table of the report's §1.4 records, so the formula is calibrated at both ends.

## §1–§2: what `2^H ∣ mₐ` buys in the elimination

`TShift.transfer_one_form` (`TShift/MultiplierTransfer.lean`) is the elimination step of the
Padé method: two independent small integer forms `ℓᵢ = aᵢX + bᵢY` with contents `Γᵢ` give
`|Γ|·X ≤ |c|·Λ + B·|cY − mX|` for every `m`, because `Δ = c·aᵢ + m·bᵢ` is a nonzero multiple of
`Γᵢ` for at least one `i`.  The observation of this file is that the `2`-adic hypothesis enters
that step for free:

> if `2^H·Γ ∣ a` and `Γ ∣ b` and **`2^H ∣ m`**, then `2^H·Γ ∣ Δ`, so the main term is
> `2^H·|Γ|·X` instead of `|Γ|·X` (`weighted_elimination_one_form`).

At the frame columns `X = 2ᵃ`, `Y = 3ᵃ`, `c = 1`, `m = mₐ` this is exactly a weighted rate: the
hypothesis is `2^H ∣ mₐ`, i.e. `H ≤ v₂(mₐ)`, and the conclusion is `|kₐ| ≥ (2^H·2ᵃ − Λ)/B` —
`β = 1` in the display above, provided the forms satisfy the **design condition** `2^H ∣ a`.

Nothing in the published constructions supplies that condition: measured on [Hab03]'s own
two-column data (`BB13/b2_weighted.py`, block [C]), the content-reduced first coefficient has
`v₂ ≤ 7` across all 3599 forms with `m ≤ 60` and every Padé index, mean `1.54` — the
coefficients are `2`-adically generic, so the free depth is `O(1)`.  The condition can
be *manufactured*, though, from any two independent forms at the same index, by a `2`-dimensional
lattice reduction: `weighted_elimination_combined` charges the cost.  The lattice
`L_H = {(t₁,t₂) : 2^H ∣ t₁a₁ + t₂a₂}` has determinant `≤ 2^H`, so a reduced basis has vectors of
max-norm `≈ 2^{H/2}`, and the combined forms pay that norm in both columns — net gain
`2^{H}/2^{H/2} = 2^{H/2}`, i.e. **`β = 1/2`**.  Measured on [Hab03]'s two indices at
`m = 20, 40, 60` and `H ≤ 64`, both successive minima sit at `2^{H/2}`: the guaranteed gain
averages `0.492·H` over `H ≥ 16` (`b2_weighted.py`, block [D]).

What is *not* a theorem is that they always do: the guaranteed gain is `2^{H}/λ₂`, and only
`λ₁λ₂ ≍ 2^H` is automatic.  So B2 at `β = 1/2` is a per-index certificate, not yet a uniform
statement; the uniform statement needs one `2`-adic fact about the Padé coefficients — that
`a₂/a₁ mod 2^H` is not too well approximable by rationals of small height — which is a
well-posed finite question about a specific construction, and is the successor of B2 that this
file leaves open.

## §3: the payoff, and why it is worth having

`weighted_fibre_cap`: a weighted rate at exponent `β` and base `c₁` caps every fibre by

`2^{(1+β)·d} ≤ (3/(2c₁))ᵃ`,   i.e.   `d ≤ (log₂(3/2) − log₂c₁)·a/(1 + β)`.

At `β = 0` this is the `0.385a` (Habsieger, effective) and `0.371a` (Zudilin) rows of the report's
table.  At `β = 1/2` — the value the lattice step delivers — Zudilin's `c₁ = 2·0.5803` gives
`d ≤ 0.2468a`, and `zudilin_half_fibre_cap` states the clean consequence `4·d ≤ a`.  That would
be the first improvement of the `min(v₂(mₐ), D(a))` row since 2007, obtained without touching
the rate.

## What B2(i) — the "AE" finite check — turns out to be

The cheapest item on the report's board was A2's elimination of `mₙ` between the known forms at
consecutive indices under the pair hypothesis.  It is decisively negative, for a structural
reason worth recording here because no Lean statement carries it: with `m_{n+1} = 3mₙ/2` the
eliminant is

`Δ = 3b′·cₙ − 2b·c_{n+1} = 3a b′ − 2a′ b = (3b′Λₙ − bΛ_{n+1})/2ⁿ`,

in which **`kₙ` has cancelled identically**.  The test therefore carries no `2`-adic information
at all (contrary to the adjudication CB6 of the report's §8) and is a pure coefficient-quality
test: it fires only for forms with `|b|·|Λ| < 2ⁿ`, i.e. convergent quality.  Exact computation on
[Hab03]'s forms (`b2_weighted.py`, block [B]) gives `|Δ| = 2^{0.71 n}…2^{0.80 n}` at the
rate-optimal index, and a sweep over *every* Padé index (`20 ≤ m ≤ 60`) never gets the deficit
below `2^{0.42 n}`.  The deficit at the optimal index equals the engine's own rate exponent, because
the optimum sits at the break-even `Γ·2ⁿ ≈ Λ`; so AE fires only for a construction whose rate
exponent is `≈ 0`, which is incomparably stronger than what Problem 10.13 needs.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.  Every statement of §1–§2 is integer algebra; §3 consumes the elementary linkage
layer of `BB13/GapPrinciple.lean` and `vTwo` of `BB13/ValuationArm.lean`.

## Claim level

Formalization of a mechanism and of its payoff.  **No weighted rate is proved here** — `hrate` is
a hypothesis of every statement in §3, and the `β = 1/2` instance is conditional on the lattice
certificate discussed above.  What is unconditional is the elimination step, the cost accounting,
and the cap.

## References

* `plans/report3-BB13.html` §6 (B2), §5 (Q2.3, the pair event as one `2`-adic bit), §8 (CB6).
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)ᵏ‖`*, Acta Arith. **106** (2003),
  299–308 — the engine measured in `BB13/b2_weighted.py`.
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323 — `c₁ = 2·0.5803`, the base of `zudilin_half_fibre_cap`.
* `TShift/MultiplierTransfer.lean` — the `H = 0` case of §1, with the multiplier slot;
  `CITED/HabsiegerPade.lean`, `CITED/ZudilinPade.lean` — the two bundles the design condition
  would have to be imposed on.
-/

namespace BB13

open scoped Real

/-! ## 1. The weighted elimination step

The `H = 0` specialisation of every statement here is the standard rank-2 elimination of the
Padé method (`TShift.transfer_one_form`, `TShift.multiplier_transfer`); the `2`-adic hypothesis
`2^H ∣ m` and the design condition `2^H·Γ ∣ a` are what this section adds. -/

/-- **The weighted core estimate, one form at a time.**  With `ℓ = a·X + b·Y` and
`Δ = c·a + m·b`, the divisibility `2^H·Γ ∣ Δ` holds as soon as `2^H·Γ ∣ a`, `Γ ∣ b` and
`2^H ∣ m` — the second summand `m·b` is divisible by `2^H` through `m` and by `Γ` through `b`.
Hence, for `Δ ≠ 0`,

`2^H·|Γ|·X ≤ |c|·|ℓ| + |b|·|c·Y − m·X|`.

There is no hypothesis on `b`, and none on `Y`. -/
@[category research solved, AMS 11, ref "Hab03" "Bug12", group "bugeaud_10_13"]
theorem weighted_elimination_one_form {X Y c m a b Γ : ℤ} {H : ℕ} (hX : 0 ≤ X)
    (hΓa : 2 ^ H * Γ ∣ a) (hΓb : Γ ∣ b) (hm : (2 : ℤ) ^ H ∣ m) (hΔ : c * a + m * b ≠ 0) :
    2 ^ H * |Γ| * X ≤ |c| * |a * X + b * Y| + |b| * |c * Y - m * X| := by
  obtain ⟨m', rfl⟩ := hm
  have hdvd : 2 ^ H * Γ ∣ c * a + 2 ^ H * m' * b := by
    refine dvd_add (hΓa.mul_left c) ?_
    obtain ⟨b', rfl⟩ := hΓb
    exact ⟨m' * b', by ring⟩
  have habs : |(2 : ℤ) ^ H * Γ| ≤ |c * a + 2 ^ H * m' * b| :=
    Int.le_of_dvd (abs_pos.mpr hΔ) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvd))
  have hpow : |(2 : ℤ) ^ H * Γ| = 2 ^ H * |Γ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ H)]
  rw [hpow] at habs
  have hid : c * (a * X + b * Y) - b * (c * Y - 2 ^ H * m' * X)
      = X * (c * a + 2 ^ H * m' * b) := by ring
  calc 2 ^ H * |Γ| * X ≤ |c * a + 2 ^ H * m' * b| * X := mul_le_mul_of_nonneg_right habs hX
    _ = |X * (c * a + 2 ^ H * m' * b)| := by rw [abs_mul, abs_of_nonneg hX]; ring
    _ = |c * (a * X + b * Y) - b * (c * Y - 2 ^ H * m' * X)| := by rw [hid]
    _ ≤ |c * (a * X + b * Y)| + |b * (c * Y - 2 ^ H * m' * X)| := abs_sub _ _
    _ = |c| * |a * X + b * Y| + |b| * |c * Y - 2 ^ H * m' * X| := by rw [abs_mul, abs_mul]

/-- **The rank-2 step.**  If `c ≠ 0` and the two forms are independent, then for every `m` at
least one of `Δᵢ = c·aᵢ + m·bᵢ` is nonzero (`b₂Δ₁ − b₁Δ₂ = c(a₁b₂ − a₂b₁)`).  Copied from
`TShift.exists_delta_ne_zero` so that this file stands alone. -/
@[category API, AMS 11, ref "Hab03", group "bugeaud_10_13"]
theorem exists_delta_ne_zero' {c m a₁ b₁ a₂ b₂ : ℤ} (hc : c ≠ 0) (hdet : a₁ * b₂ ≠ a₂ * b₁) :
    c * a₁ + m * b₁ ≠ 0 ∨ c * a₂ + m * b₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hdet ?_
  have hcomb : b₂ * (c * a₁ + m * b₁) - b₁ * (c * a₂ + m * b₂) = c * (a₁ * b₂ - a₂ * b₁) := by
    ring
  have hz : c * (a₁ * b₂ - a₂ * b₁) = 0 := by rw [← hcomb, h1, h2]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)

/-- **The weighted transfer**, at content `1`: two independent forms of size `≤ Λ` with second
coefficients `≤ B` and **both first coefficients divisible by `2^H`** push `c·Y` away from the
multiples of `X` by a factor `2^H` more than the unweighted step does, for every `m` divisible
by `2^H`:

`2^H·X ≤ |c|·Λ + B·|c·Y − m·X|`. -/
@[category research solved, AMS 11, ref "Hab03" "Bug12", group "bugeaud_10_13"]
theorem weighted_elimination {X Y c m a₁ b₁ a₂ b₂ : ℤ} {H : ℕ} {Λ B : ℝ}
    (hX : 0 ≤ X) (hc : c ≠ 0) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hd₁ : (2 : ℤ) ^ H ∣ a₁) (hd₂ : (2 : ℤ) ^ H ∣ a₂) (hm : (2 : ℤ) ^ H ∣ m)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    2 ^ H * (X : ℝ) ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have main : ∀ a b : ℤ, (2 : ℤ) ^ H ∣ a →
      |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ Λ → |(b : ℝ)| ≤ B → c * a + m * b ≠ 0 →
      2 ^ H * (X : ℝ) ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
    intro a b hda hΛ hB hΔ
    have hZ := weighted_elimination_one_form (X := X) (Y := Y) (c := c) (m := m) (Γ := 1)
      (H := H) hX (by simpa using hda) (one_dvd _) hm hΔ
    have hZ' : (2 : ℤ) ^ H * X ≤ |c| * |a * X + b * Y| + |b| * |c * Y - m * X| := by
      simpa using hZ
    have hR : (2 : ℝ) ^ H * (X : ℝ)
        ≤ |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|
          + |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
      exact_mod_cast hZ'
    have h2 : |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ |(c : ℝ)| * Λ :=
      mul_le_mul_of_nonneg_left hΛ (abs_nonneg _)
    have h3 : |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)|
        ≤ B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    linarith
  rcases exists_delta_ne_zero' (c := c) (m := m) hc hdet with h | h
  · exact main a₁ b₁ hd₁ hΛ₁ hB₁ h
  · exact main a₂ b₂ hd₂ hΛ₂ hB₂ h

/-! ## 2. Manufacturing the design condition: the `2`-adic lattice step

Two integer vectors `t, u` in the lattice `L_H = {(t₁,t₂) : 2^H ∣ t₁a₁ + t₂a₂}`, independent over
`ℚ`, turn any pair of independent forms into a pair of independent forms satisfying the design
condition, at the price of their own size in both columns.  `det L_H ≤ 2^H`, so a reduced basis
has `‖t‖·‖u‖ ≲ 2^H`; the cost charged below is `L = max ‖·‖`. -/

/-- **The weighted transfer through a lattice combination.**  From two independent forms and two
independent integer vectors `t, u` with `2^H ∣ t·a` and `2^H ∣ u·a`, all of whose entries are
`≤ L` in absolute value:

`2^H·X ≤ 2L·Λ + 2L·B·|Y − m·X|`  for every `m` with `2^H ∣ m`.

The gain `2^H` is charged `2L` in the error column and `2L` in the coefficient column, so the
net gain over the unweighted step is `2^H/(2L)`. -/
@[category research solved, AMS 11, ref "Hab03" "Bug12", group "bugeaud_10_13"]
theorem weighted_elimination_combined {X Y m a₁ b₁ a₂ b₂ t₁ t₂ u₁ u₂ : ℤ} {H : ℕ} {Λ B L : ℝ}
    (hX : 0 ≤ X) (hdet : a₁ * b₂ ≠ a₂ * b₁) (hdetT : t₁ * u₂ ≠ t₂ * u₁)
    (hT : (2 : ℤ) ^ H ∣ t₁ * a₁ + t₂ * a₂) (hU : (2 : ℤ) ^ H ∣ u₁ * a₁ + u₂ * a₂)
    (hm : (2 : ℤ) ^ H ∣ m)
    (ht₁ : |(t₁ : ℝ)| ≤ L) (ht₂ : |(t₂ : ℝ)| ≤ L)
    (hu₁ : |(u₁ : ℝ)| ≤ L) (hu₂ : |(u₂ : ℝ)| ≤ L)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    2 ^ H * (X : ℝ) ≤ 2 * L * Λ + 2 * L * B * |(Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
  -- the combined forms
  set A₁ : ℤ := t₁ * a₁ + t₂ * a₂ with hA₁
  set C₁ : ℤ := t₁ * b₁ + t₂ * b₂ with hC₁
  set A₂ : ℤ := u₁ * a₁ + u₂ * a₂ with hA₂
  set C₂ : ℤ := u₁ * b₁ + u₂ * b₂ with hC₂
  have hdetA : A₁ * C₂ ≠ A₂ * C₁ := by
    have hexp : A₁ * C₂ - A₂ * C₁ = (t₁ * u₂ - t₂ * u₁) * (a₁ * b₂ - a₂ * b₁) := by
      rw [hA₁, hC₁, hA₂, hC₂]; ring
    intro hcon
    have hz : (t₁ * u₂ - t₂ * u₁) * (a₁ * b₂ - a₂ * b₁) = 0 := by
      rw [← hexp, hcon]; ring
    rcases mul_eq_zero.mp hz with h | h
    · exact hdetT (sub_eq_zero.mp h)
    · exact hdet (sub_eq_zero.mp h)
  -- sizes of the combined forms
  have hsize : ∀ s₁ s₂ : ℤ, |(s₁ : ℝ)| ≤ L → |(s₂ : ℝ)| ≤ L →
      |((s₁ * a₁ + s₂ * a₂ : ℤ) : ℝ) * (X : ℝ) + ((s₁ * b₁ + s₂ * b₂ : ℤ) : ℝ) * (Y : ℝ)|
        ≤ 2 * L * Λ := by
    intro s₁ s₂ hs₁ hs₂
    have hexp : ((s₁ * a₁ + s₂ * a₂ : ℤ) : ℝ) * (X : ℝ)
        + ((s₁ * b₁ + s₂ * b₂ : ℤ) : ℝ) * (Y : ℝ)
        = (s₁ : ℝ) * ((a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ))
          + (s₂ : ℝ) * ((a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)) := by push_cast; ring
    rw [hexp]
    calc |(s₁ : ℝ) * ((a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ))
            + (s₂ : ℝ) * ((a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ))|
        ≤ |(s₁ : ℝ) * ((a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ))|
            + |(s₂ : ℝ) * ((a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ))| := abs_add_le _ _
      _ = |(s₁ : ℝ)| * |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)|
            + |(s₂ : ℝ)| * |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| := by
          rw [abs_mul, abs_mul]
      _ ≤ L * Λ + L * Λ := by
          have h1 : |(s₁ : ℝ)| * |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ L * Λ :=
            mul_le_mul hs₁ hΛ₁ (abs_nonneg _) (le_trans (abs_nonneg _) hs₁)
          have h2 : |(s₂ : ℝ)| * |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ L * Λ :=
            mul_le_mul hs₂ hΛ₂ (abs_nonneg _) (le_trans (abs_nonneg _) hs₂)
          linarith
      _ = 2 * L * Λ := by ring
  have hcoeff : ∀ s₁ s₂ : ℤ, |(s₁ : ℝ)| ≤ L → |(s₂ : ℝ)| ≤ L →
      |((s₁ * b₁ + s₂ * b₂ : ℤ) : ℝ)| ≤ 2 * L * B := by
    intro s₁ s₂ hs₁ hs₂
    have hexp : ((s₁ * b₁ + s₂ * b₂ : ℤ) : ℝ) = (s₁ : ℝ) * (b₁ : ℝ) + (s₂ : ℝ) * (b₂ : ℝ) := by
      push_cast; ring
    rw [hexp]
    calc |(s₁ : ℝ) * (b₁ : ℝ) + (s₂ : ℝ) * (b₂ : ℝ)|
        ≤ |(s₁ : ℝ) * (b₁ : ℝ)| + |(s₂ : ℝ) * (b₂ : ℝ)| := abs_add_le _ _
      _ = |(s₁ : ℝ)| * |(b₁ : ℝ)| + |(s₂ : ℝ)| * |(b₂ : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ L * B + L * B := by
          have h1 : |(s₁ : ℝ)| * |(b₁ : ℝ)| ≤ L * B :=
            mul_le_mul hs₁ hB₁ (abs_nonneg _) (le_trans (abs_nonneg _) hs₁)
          have h2 : |(s₂ : ℝ)| * |(b₂ : ℝ)| ≤ L * B :=
            mul_le_mul hs₂ hB₂ (abs_nonneg _) (le_trans (abs_nonneg _) hs₂)
          linarith
      _ = 2 * L * B := by ring
  have h := weighted_elimination (X := X) (Y := Y) (c := 1) (m := m) (H := H)
    (a₁ := A₁) (b₁ := C₁) (a₂ := A₂) (b₂ := C₂) (Λ := 2 * L * Λ) (B := 2 * L * B)
    hX one_ne_zero hdetA hT hU hm (hsize t₁ t₂ ht₁ ht₂) (hsize u₁ u₂ hu₁ hu₂)
    (hcoeff t₁ t₂ ht₁ ht₂) (hcoeff u₁ u₂ hu₁ hu₂)
  simpa using h

/-- **The weighted step at the frame columns.**  At `X = 2ᴺ`, `Y = 3ᴺ`, `c = 1` and
`m = m_N = round((3/2)ᴺ)` the last factor is the residue itself, `|3ᴺ − m_N·2ᴺ| = |k_N|`, so
two forms meeting the design condition give the **weighted rate**

`|k_N| ≥ (2^H·2ᴺ − Λ)/B`

whenever `H ≤ v₂(m_N)`.  This is the shape §3 consumes, with `2^H` in place of the `1` of the
unweighted method. -/
@[category research solved, AMS 11, ref "Hab03" "Bug12", group "bugeaud_10_13"]
theorem weighted_rate_of_forms {N H : ℕ} {a₁ b₁ a₂ b₂ : ℤ} {Λ B : ℝ}
    (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hd₁ : (2 : ℤ) ^ H ∣ a₁) (hd₂ : (2 : ℤ) ^ H ∣ a₂) (hH : H ≤ vTwo N)
    (hΛ₁ : |(a₁ : ℝ) * (2 : ℝ) ^ N + (b₁ : ℝ) * (3 : ℝ) ^ N| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (2 : ℝ) ^ N + (b₂ : ℝ) * (3 : ℝ) ^ N| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    2 ^ H * (2 : ℝ) ^ N ≤ Λ + B * |((resid 3 2 N : ℤ) : ℝ)| := by
  have hm : (2 : ℤ) ^ H ∣ Mnum 3 2 N :=
    dvd_trans (pow_dvd_pow 2 hH) (two_pow_vTwo_dvd N)
  have h := weighted_elimination (X := (2 : ℤ) ^ N) (Y := (3 : ℤ) ^ N) (c := 1)
    (m := Mnum 3 2 N) (H := H) (by positivity) one_ne_zero hdet hd₁ hd₂ hm
    (by push_cast; exact hΛ₁) (by push_cast; exact hΛ₂) hB₁ hB₂
  have hres : ((1 : ℤ) : ℝ) * (((3 : ℤ) ^ N : ℤ) : ℝ)
      - ((Mnum 3 2 N : ℤ) : ℝ) * (((2 : ℤ) ^ N : ℤ) : ℝ) = ((resid 3 2 N : ℤ) : ℝ) := by
    rw [resid]; push_cast; ring
  rw [hres] at h
  push_cast at h
  simpa using h

/-! ## 3. The payoff: what a weighted rate does to a fibre

`d` below is the depth of the tower over its base `a` — the `d` of the linkage lemma, so that
`a, a+1, …, a+d` all lie on one line of the frame.  The report's exact multiplicity formula says
`d ≤ min(v₂(mₐ), D(a))`; the two hypotheses used here are exactly the two arms of that `min`,
supplied by `BB13.link_dvd` and `BB13.link_quality`. -/

/-- **The cap.**  A weighted rate `c₁ᵃ·2^{β·v₂(mₐ)} ≤ |kₐ|` at the base of a tower of depth `d`
forces `2^{(1+β)d} ≤ (3/(2c₁))ᵃ`.

Both arms are consumed: `d ≤ v₂(mₐ)` (so the weight, which is charged at `v₂(mₐ)`, is at least
`2^{βd}`) and `2ᵈ·|kₐ| < (3/2)ᵃ` (the dyadic quality surplus).  The exponent `1 + β` is where the
report's `(0.585 − log₂c₁)a/(1 + β)` comes from. -/
@[category research solved, AMS 11, ref "Hab03" "Zud07" "Bug12", group "bugeaud_10_13"]
theorem weighted_fibre_cap {β c₁ : ℝ} {a d : ℕ} (hβ : 0 ≤ β) (hc₁ : 0 < c₁)
    (hrate : c₁ ^ a * (2 : ℝ) ^ (β * (vTwo a : ℝ)) ≤ |((resid 3 2 a : ℤ) : ℝ)|)
    (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    (2 : ℝ) ^ ((1 + β) * (d : ℝ)) ≤ (3 / (2 * c₁)) ^ a := by
  -- (i) the `v` arm: `2ᵈ ∣ mₐ`, hence `d ≤ v₂(mₐ)`
  have hdvd : (2 : ℤ) ^ d ∣ Mnum 3 2 a := link_dvd 3 2 (by norm_num) hlink
  have hdv : (d : ℝ) ≤ (vTwo a : ℝ) := by exact_mod_cast le_vTwo_of_dvd hdvd
  -- (ii) the `D` arm: `2ᵈ·|kₐ| < (3/2)ᵃ`
  have hq := link_quality 3 2 (3 / 4) hfail hlink
  have hD : (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := by
    have hstep : (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
      have hcast : ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ (a + d) = (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
        rw [← pow_add]
        norm_num
      have h3 : (((3 : ℕ) : ℝ)) ^ d = (3 : ℝ) ^ d := by norm_num
      rw [hcast, h3] at hq
      exact hq
    have hpos : (0 : ℝ) < (3 / 2 : ℝ) ^ d := by positivity
    have hkey : (2 : ℝ) ^ d * ((3 / 2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)|)
        = (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by
      rw [div_pow]
      field_simp
    nlinarith [hstep, hkey, hpos, abs_nonneg ((resid 3 2 a : ℤ) : ℝ)]
  -- (iii) the weight, moved from `v₂(mₐ)` down to `d`
  have hw : (2 : ℝ) ^ (β * (d : ℝ)) ≤ (2 : ℝ) ^ (β * (vTwo a : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hc₁a : (0 : ℝ) < c₁ ^ a := pow_pos hc₁ a
  have hchain : (2 : ℝ) ^ (d : ℝ) * ((2 : ℝ) ^ (β * (d : ℝ)) * c₁ ^ a) < (3 / 2 : ℝ) ^ a := by
    have h2d : (0 : ℝ) < (2 : ℝ) ^ (d : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hstep : (2 : ℝ) ^ (β * (d : ℝ)) * c₁ ^ a ≤ |((resid 3 2 a : ℤ) : ℝ)| := by
      calc (2 : ℝ) ^ (β * (d : ℝ)) * c₁ ^ a
          ≤ (2 : ℝ) ^ (β * (vTwo a : ℝ)) * c₁ ^ a := by
            exact mul_le_mul_of_nonneg_right hw hc₁a.le
        _ = c₁ ^ a * (2 : ℝ) ^ (β * (vTwo a : ℝ)) := by ring
        _ ≤ |((resid 3 2 a : ℤ) : ℝ)| := hrate
    have hnat : (2 : ℝ) ^ (d : ℝ) = (2 : ℝ) ^ d := by
      rw [Real.rpow_natCast]
    rw [hnat]
    calc (2 : ℝ) ^ d * ((2 : ℝ) ^ (β * (d : ℝ)) * c₁ ^ a)
        ≤ (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ < (3 / 2 : ℝ) ^ a := hD
  -- (iv) collect
  have hsplit : (2 : ℝ) ^ ((1 + β) * (d : ℝ))
      = (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (β * (d : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hdiv : (3 / (2 * c₁)) ^ a = (3 / 2 : ℝ) ^ a / c₁ ^ a := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [hsplit, hdiv, le_div_iff₀ hc₁a]
  nlinarith [hchain]

/-- **The unweighted case `β = 0`** — the classical `D`-arm cap, in the same shape: a rate
`c₁ᵃ ≤ |kₐ|` caps the tower depth by `2ᵈ ≤ (3/(2c₁))ᵃ`.  With `c₁ = 2·0.5803` ([Zud07]) this is
the `d ≤ 0.371a` row of the report's table, and with `c₁ = 2·0.57434` ([Hab03], effective) the
`d ≤ 0.385a` row. -/
@[category research solved, AMS 11, ref "Hab03" "Zud07" "Bug12", group "bugeaud_10_13"]
theorem fibre_cap_of_rate {c₁ : ℝ} {a d : ℕ} (hc₁ : 0 < c₁)
    (hrate : c₁ ^ a ≤ |((resid 3 2 a : ℤ) : ℝ)|)
    (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    (2 : ℝ) ^ d ≤ (3 / (2 * c₁)) ^ a := by
  have h := weighted_fibre_cap (β := 0) (c₁ := c₁) (a := a) (d := d) le_rfl hc₁
    (by simpa using hrate) hfail hlink
  simpa using h

/-- **The `β = 1/2` instance at [Zud07]'s rate**, in integer form: a weighted rate with exponent
`β = 1/2` and base `c₁ = 2·0.5803 = 5803/5000` — the value the lattice step of §2 delivers when
the two successive minima are balanced — caps every tower by `4·d ≤ a`.

The exact cap is `d ≤ log₂(7500/5803)·(2/3)·a = 0.24672…·a`; `a/4` is the first clean rational
above it.  Against the unweighted `0.37008…·a` of `fibre_cap_of_rate` at the same base, this is a
`33 %` reduction of the best known linear bound on `min(v₂(mₐ), D(a))`. -/
@[category research solved, AMS 11, ref "Zud07" "Bug12", group "bugeaud_10_13"]
theorem zudilin_half_fibre_cap {a d : ℕ}
    (hrate : ((5803 : ℝ) / 5000) ^ a * (2 : ℝ) ^ ((1 / 2 : ℝ) * (vTwo a : ℝ))
      ≤ |((resid 3 2 a : ℤ) : ℝ)|)
    (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    4 * d ≤ a := by
  have hcap := weighted_fibre_cap (β := 1 / 2) (c₁ := (5803 : ℝ) / 5000) (a := a) (d := d)
    (by norm_num) (by norm_num) hrate hfail hlink
  have hbase : (3 : ℝ) / (2 * ((5803 : ℝ) / 5000)) = 7500 / 5803 := by norm_num
  rw [hbase] at hcap
  -- square, to clear the half-integer exponent
  have hsq : (2 : ℝ) ^ (3 * d) ≤ ((7500 : ℝ) / 5803) ^ (2 * a) := by
    have hL : ((2 : ℝ) ^ ((1 + 1 / 2 : ℝ) * (d : ℝ))) ^ (2 : ℕ) = (2 : ℝ) ^ (3 * d) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 + 1 / 2 : ℝ) * (d : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast (2 : ℝ) (3 * d)]
      congr 1
      push_cast
      ring
    have hR : (((7500 : ℝ) / 5803) ^ a) ^ (2 : ℕ) = ((7500 : ℝ) / 5803) ^ (2 * a) := by
      rw [← pow_mul, Nat.mul_comm]
    calc (2 : ℝ) ^ (3 * d) = ((2 : ℝ) ^ ((1 + 1 / 2 : ℝ) * (d : ℝ))) ^ (2 : ℕ) := hL.symm
      _ ≤ (((7500 : ℝ) / 5803) ^ a) ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hcap 2
      _ = ((7500 : ℝ) / 5803) ^ (2 * a) := hR
  -- and compare rational bases
  by_contra hcon
  push Not at hcon
  have hd1 : 1 ≤ d := by omega
  have ha : 2 * a ≤ 8 * d - 2 := by omega
  have hr1 : (1 : ℝ) ≤ (7500 : ℝ) / 5803 := by norm_num
  have hmono : ((7500 : ℝ) / 5803) ^ (2 * a) ≤ ((7500 : ℝ) / 5803) ^ (8 * d - 2) :=
    pow_le_pow_right₀ hr1 ha
  have hkey : (2 : ℝ) ^ (3 * d) ≤ ((7500 : ℝ) / 5803) ^ (8 * d - 2) := le_trans hsq hmono
  have hshift : ((7500 : ℝ) / 5803) ^ (8 * d - 2) * ((7500 : ℝ) / 5803) ^ 2
      = ((7500 : ℝ) / 5803) ^ (8 * d) := by
    rw [← pow_add]
    congr 1
    omega
  have h8 : ((7500 : ℝ) / 5803) ^ (8 * d) = (((7500 : ℝ) / 5803) ^ 8) ^ d := pow_mul _ 8 d
  have h2d : (2 : ℝ) ^ (3 * d) = ((8 : ℝ)) ^ d := by
    rw [pow_mul]; norm_num
  have hlt : (((7500 : ℝ) / 5803) ^ 8) ^ d ≤ (8 : ℝ) ^ d :=
    pow_le_pow_left₀ (by positivity) (by norm_num) d
  have hpos : (0 : ℝ) < ((7500 : ℝ) / 5803) ^ 2 := by positivity
  have hcontra : (8 : ℝ) ^ d * ((7500 : ℝ) / 5803) ^ 2 ≤ (8 : ℝ) ^ d := by
    calc (8 : ℝ) ^ d * ((7500 : ℝ) / 5803) ^ 2
        = (2 : ℝ) ^ (3 * d) * ((7500 : ℝ) / 5803) ^ 2 := by rw [h2d]
      _ ≤ ((7500 : ℝ) / 5803) ^ (8 * d - 2) * ((7500 : ℝ) / 5803) ^ 2 := by
          exact mul_le_mul_of_nonneg_right hkey hpos.le
      _ = (((7500 : ℝ) / 5803) ^ 8) ^ d := by rw [hshift, h8]
      _ ≤ (8 : ℝ) ^ d := hlt
  have h8d : (0 : ℝ) < (8 : ℝ) ^ d := by positivity
  nlinarith [hcontra, h8d]

end BB13
