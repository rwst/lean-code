/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Data.Real.NearestInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The content-refined multiplier transfer

Two independent integer forms `ℓᵢ = aᵢ·X + bᵢ·Y` that are *small* and whose coefficients carry a
*large common divisor* force `c·Y` away from the multiples of `X`.  This is the elimination step
of the Padé method for `‖(3/2)^k‖`, isolated from every Padé construction:

`P·X ≤ |c|·Λ + B·|c·Y − m·X|`  for every `m ∈ ℤ`,

whenever `|ℓᵢ| ≤ Λ`, `|bᵢ| ≤ B`, `Γᵢ ∣ aᵢ, bᵢ` with `|Γᵢ| ≥ P`, and `a₁b₂ ≠ a₂b₁`.

## Why it is the whole of the multiplier problem

In the classical application `X = 2^N`, `Y = 3^N` and `c = 1`, and the conclusion is a lower bound
for `‖(3/2)^N‖`.  The **multiplier** `D` — the denominator `D_p = 3^p − 2^p` of a T-shift cycle
target, see `TShift.Basic` — enters only through `c`, i.e. only through the single product `|c|·Λ`
on the error side.  It never touches the construction of the forms, the independence certificate,
or the content.  That is the content of `TShift.multiplier_transfer_pow` below: `c = 2^v·D`, and
`D` is charged exactly once.  The `v`-slot absorbs the 2-power shift needed when the date `k` is
not a multiple of the Padé period.

## What is proved here

* `TShift.transfer_one_form` — the core estimate for a single form.  The identity
  `c·ℓ − b·(c·Y − m·X) = X·Δ` with `Δ = c·a + m·b ∈ ℤ`, together with `Γ ∣ Δ`, `Δ ≠ 0`.
* `TShift.exists_delta_ne_zero` — the rank-2 step: if `c ≠ 0` and `a₁b₂ ≠ a₂b₁`, the two `Δᵢ`
  cannot both vanish.
* `TShift.multiplier_transfer` (and `TShift.multiplier_transfer_div` in fraction form) — the
  transfer lemma at general columns `X, Y`.
* `TShift.le_distToNearestInt_transfer` — the same bound read as a repulsion statement for
  `c·Y/X` in the `distToNearestInt` of `ForMathlib/Data/Real/NearestInt.lean`.
* `TShift.multiplier_transfer_pow`, `TShift.le_distToNearestInt_pow` — the two-power columns
  `X = 2^N`, `Y = 3^N`, `c = 2^v·D`; the displayed form the Padé engines are instantiated at.
* `TShift.transfer_prop_one` — the unrefined corollary `Γ = 1`, `v = 0`.
* `TShift.TwoForms` — the same hypotheses bundled, so a Padé engine supplies one structure and
  gets the three conclusions back.  This is the engine-agnostic socket: nothing here knows which
  construction produced the forms.

## Two hypotheses that are deliberately absent

* **`bᵢ ≠ 0` is not assumed.**  The classical write-up divides by the Padé denominator evaluated
  at the base point and never shows it is nonzero.  The two-column form never divides by it; when
  `b = 0` the estimate below still holds (and is then vacuous, not false).
* **`X` and `Y` need not be coprime**, nor powers of anything: only `0 ≤ X` is used.  Coprime
  columns `q^N, p^N` are a special case, at no cost.

Note also that the contents are **per form**: a single `Γ` dividing all four coefficients is in
general unavailable, because the content of a Padé form depends on its index.  What is shared is
the lower bound `P`.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.  Integer algebra only; nothing here is asserted about any particular
construction, so this file proves no instance of the T-shift problem.

## Claim level

Formalization of a known elimination step, stated in the generality the plan needs.  The estimate
is the standard rank-2 argument of the Padé method for `‖(3/2)^k‖` with two amendments recorded in
`plans/note-Tshift-S1-constants.html` §6.1: the `bᵢ ≠ 0` hypothesis is dropped and the content is
taken per form.

## References

* `plans/plan-Tshift-S1.html` §1.2 D2 (the statement) and §4 WP1 (this file).
* `plans/note-Tshift-S1-constants.html` §6.1 (the final form, and why the two hypotheses above are
  absent).
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308 — displays (3.1)–(3.2), the instance this lemma abstracts.
* [Beu81] F. Beukers, *Fractional parts of powers of rationals*, Math. Proc. Cambridge Philos.
  Soc. **90** (1981), 13–20.
-/

namespace TShift

/-! ## 1. The core estimate, one form at a time

Throughout, `Γ` is what the literature writes `Π` (the content of a Padé form); `Π` is reserved
syntax in Lean. -/

/-- **The core estimate for a single form.**  Let `ℓ = a·X + b·Y` and `Δ = c·a + m·b`.  The
identity `c·ℓ − b·(c·Y − m·X) = X·Δ` is an identity of integers, so if `Δ ≠ 0` and `Γ` divides
both `a` and `b` — hence `Δ` — then `|Δ| ≥ |Γ|` and

`|Γ|·X ≤ |c|·|ℓ| + |b|·|c·Y − m·X|`.

There is **no hypothesis on `b`**: the proof never divides by it. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem transfer_one_form {X Y c m a b Γ : ℤ} (hX : 0 ≤ X)
    (hΓa : Γ ∣ a) (hΓb : Γ ∣ b) (hΔ : c * a + m * b ≠ 0) :
    |Γ| * X ≤ |c| * |a * X + b * Y| + |b| * |c * Y - m * X| := by
  have hdvd : Γ ∣ c * a + m * b := dvd_add (hΓa.mul_left c) (hΓb.mul_left m)
  have habs : |Γ| ≤ |c * a + m * b| :=
    Int.le_of_dvd (abs_pos.mpr hΔ) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hdvd))
  have hid : c * (a * X + b * Y) - b * (c * Y - m * X) = X * (c * a + m * b) := by ring
  calc |Γ| * X ≤ |c * a + m * b| * X := mul_le_mul_of_nonneg_right habs hX
    _ = |X * (c * a + m * b)| := by rw [abs_mul, abs_of_nonneg hX]; ring
    _ = |c * (a * X + b * Y) - b * (c * Y - m * X)| := by rw [hid]
    _ ≤ |c * (a * X + b * Y)| + |b * (c * Y - m * X)| := abs_sub _ _
    _ = |c| * |a * X + b * Y| + |b| * |c * Y - m * X| := by rw [abs_mul, abs_mul]

/-- **The rank-2 step.**  If the multiplier `c` is nonzero and the two forms are independent
(`a₁b₂ ≠ a₂b₁`), then for every `m` at least one of `Δᵢ = c·aᵢ + m·bᵢ` is nonzero: from
`Δ₁ = Δ₂ = 0` one gets `b₂Δ₁ − b₁Δ₂ = c·(a₁b₂ − a₂b₁) = 0`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem exists_delta_ne_zero {c m a₁ b₁ a₂ b₂ : ℤ} (hc : c ≠ 0) (hdet : a₁ * b₂ ≠ a₂ * b₁) :
    c * a₁ + m * b₁ ≠ 0 ∨ c * a₂ + m * b₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hdet ?_
  have hcomb : b₂ * (c * a₁ + m * b₁) - b₁ * (c * a₂ + m * b₂) = c * (a₁ * b₂ - a₂ * b₁) := by
    ring
  have hz : c * (a₁ * b₂ - a₂ * b₁) = 0 := by rw [← hcomb, h1, h2]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)

/-! ## 2. The transfer lemma -/

/-- **The content-refined multiplier transfer.**  Two independent small forms with large contents
push `c·Y` away from `X·ℤ`:

`P·X ≤ |c|·Λ + B·|c·Y − m·X|`  for every `m ∈ ℤ`.

Only `0 ≤ X` is used about the columns.  The multiplier `c` is charged exactly once, in `|c|·Λ`;
this is the entire cost of a multiplier in the Padé method. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem multiplier_transfer {X Y c a₁ b₁ Γ₁ a₂ b₂ Γ₂ : ℤ} {P Λ B : ℝ}
    (hX : 0 ≤ X) (hc : c ≠ 0) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΓ₁a : Γ₁ ∣ a₁) (hΓ₁b : Γ₁ ∣ b₁) (hΓ₂a : Γ₂ ∣ a₂) (hΓ₂b : Γ₂ ∣ b₂)
    (hP₁ : P ≤ |(Γ₁ : ℝ)|) (hP₂ : P ≤ |(Γ₂ : ℝ)|)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) (m : ℤ) :
    P * (X : ℝ) ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have main : ∀ a b Γ : ℤ, Γ ∣ a → Γ ∣ b → P ≤ |(Γ : ℝ)| →
      |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ Λ → |(b : ℝ)| ≤ B → c * a + m * b ≠ 0 →
      P * (X : ℝ) ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
    intro a b Γ hΓa hΓb hP hΛ hB hΔ
    have hZ := transfer_one_form (X := X) (Y := Y) (c := c) (m := m) hX hΓa hΓb hΔ
    have hR : |(Γ : ℝ)| * (X : ℝ)
        ≤ |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|
          + |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
      exact_mod_cast hZ
    have h1 : P * (X : ℝ) ≤ |(Γ : ℝ)| * (X : ℝ) := mul_le_mul_of_nonneg_right hP hXR
    have h2 : |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ |(c : ℝ)| * Λ :=
      mul_le_mul_of_nonneg_left hΛ (abs_nonneg _)
    have h3 : |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)|
        ≤ B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    linarith
  rcases exists_delta_ne_zero (c := c) (m := m) hc hdet with h | h
  · exact main a₁ b₁ Γ₁ hΓ₁a hΓ₁b hP₁ hΛ₁ hB₁ h
  · exact main a₂ b₂ Γ₂ hΓ₂a hΓ₂b hP₂ hΛ₂ hB₂ h

/-- The transfer lemma in the displayed fraction form:
`|c·Y − m·X| ≥ (P·X − |c|·Λ)/B`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem multiplier_transfer_div {X Y c a₁ b₁ Γ₁ a₂ b₂ Γ₂ : ℤ} {P Λ B : ℝ}
    (hX : 0 ≤ X) (hc : c ≠ 0) (hB : 0 < B) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΓ₁a : Γ₁ ∣ a₁) (hΓ₁b : Γ₁ ∣ b₁) (hΓ₂a : Γ₂ ∣ a₂) (hΓ₂b : Γ₂ ∣ b₂)
    (hP₁ : P ≤ |(Γ₁ : ℝ)|) (hP₂ : P ≤ |(Γ₂ : ℝ)|)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) (m : ℤ) :
    (P * (X : ℝ) - |(c : ℝ)| * Λ) / B ≤ |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
  have h := multiplier_transfer hX hc hdet hΓ₁a hΓ₁b hΓ₂a hΓ₂b hP₁ hP₂ hΛ₁ hΛ₂ hB₁ hB₂ m
  rw [div_le_iff₀ hB]
  linarith

/-- **The transfer as a repulsion statement.**  Minimising over `m` turns the bound into one for
the distance from `c·Y/X` to the nearest integer:
`‖c·Y/X‖ ≥ (P·X − |c|·Λ)/(B·X)`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt_transfer {X Y c a₁ b₁ Γ₁ a₂ b₂ Γ₂ : ℤ} {P Λ B : ℝ}
    (hX : 0 < X) (hc : c ≠ 0) (hB : 0 < B) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΓ₁a : Γ₁ ∣ a₁) (hΓ₁b : Γ₁ ∣ b₁) (hΓ₂a : Γ₂ ∣ a₂) (hΓ₂b : Γ₂ ∣ b₂)
    (hP₁ : P ≤ |(Γ₁ : ℝ)|) (hP₂ : P ≤ |(Γ₂ : ℝ)|)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    (P * (X : ℝ) - |(c : ℝ)| * Λ) / (B * (X : ℝ))
      ≤ distToNearestInt ((c : ℝ) * (Y : ℝ) / (X : ℝ)) := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  set m : ℤ := round ((c : ℝ) * (Y : ℝ) / (X : ℝ)) with hm
  have h := multiplier_transfer hX.le hc hdet hΓ₁a hΓ₁b hΓ₂a hΓ₂b hP₁ hP₂ hΛ₁ hΛ₂ hB₁ hB₂ m
  have hid : (c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)
      = (X : ℝ) * ((c : ℝ) * (Y : ℝ) / (X : ℝ) - (m : ℝ)) := by
    field_simp
  have heq : |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)|
      = (X : ℝ) * distToNearestInt ((c : ℝ) * (Y : ℝ) / (X : ℝ)) := by
    rw [distToNearestInt, ← hm, hid, abs_mul, abs_of_pos hXR]
  rw [heq] at h
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < B * (X : ℝ))]
  linarith

/-! ## 3. Two-power columns: the form the Padé engines are instantiated at -/

/-- **D2, in the shape the engines supply.**  Columns `X = 2^N`, `Y = 3^N`, multiplier
`c = 2^v·D`:

`|2^v·D·3^N − m·2^N| ≥ (P·2^N − 2^v·D·Λ)/B`.

`D` is the T-shift multiplier and `v` the 2-power shift that lets the date `k = N − v` be
arbitrary; both enter only through the product `2^v·D` on the error side. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem multiplier_transfer_pow {N v D : ℕ} {a₁ b₁ Γ₁ a₂ b₂ Γ₂ : ℤ} {P Λ B : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΓ₁a : Γ₁ ∣ a₁) (hΓ₁b : Γ₁ ∣ b₁) (hΓ₂a : Γ₂ ∣ a₂) (hΓ₂b : Γ₂ ∣ b₂)
    (hP₁ : P ≤ |(Γ₁ : ℝ)|) (hP₂ : P ≤ |(Γ₂ : ℝ)|)
    (hΛ₁ : |(a₁ : ℝ) * 2 ^ N + (b₁ : ℝ) * 3 ^ N| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * 2 ^ N + (b₂ : ℝ) * 3 ^ N| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) (m : ℤ) :
    (P * 2 ^ N - 2 ^ v * (D : ℝ) * Λ) / B
      ≤ |2 ^ v * (D : ℝ) * 3 ^ N - (m : ℝ) * 2 ^ N| := by
  have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hc : ((2 : ℤ) ^ v * (D : ℤ)) ≠ 0 := by positivity
  have hcabs : |(((2 : ℤ) ^ v * (D : ℤ) : ℤ) : ℝ)| = 2 ^ v * (D : ℝ) := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((2 : ℤ) ^ v * (D : ℤ) : ℤ) : ℝ))]
    push_cast
    ring
  have h := multiplier_transfer_div (X := (2 : ℤ) ^ N) (Y := (3 : ℤ) ^ N)
    (c := (2 : ℤ) ^ v * (D : ℤ)) (by positivity) hc hB hdet hΓ₁a hΓ₁b hΓ₂a hΓ₂b hP₁ hP₂
    (by push_cast; exact hΛ₁) (by push_cast; exact hΛ₂) hB₁ hB₂ m
  rw [hcabs] at h
  push_cast at h
  exact h

/-- The repulsion form at two-power columns:
`‖2^v·D·(3/2)^N‖ ≥ (P·2^N − 2^v·D·Λ)/(B·2^N)`. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt_pow {N v D : ℕ} {a₁ b₁ Γ₁ a₂ b₂ Γ₂ : ℤ} {P Λ B : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΓ₁a : Γ₁ ∣ a₁) (hΓ₁b : Γ₁ ∣ b₁) (hΓ₂a : Γ₂ ∣ a₂) (hΓ₂b : Γ₂ ∣ b₂)
    (hP₁ : P ≤ |(Γ₁ : ℝ)|) (hP₂ : P ≤ |(Γ₂ : ℝ)|)
    (hΛ₁ : |(a₁ : ℝ) * 2 ^ N + (b₁ : ℝ) * 3 ^ N| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * 2 ^ N + (b₂ : ℝ) * 3 ^ N| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    (P * 2 ^ N - 2 ^ v * (D : ℝ) * Λ) / (B * 2 ^ N)
      ≤ distToNearestInt (2 ^ v * (D : ℝ) * ((3 : ℝ) / 2) ^ N) := by
  have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hc : ((2 : ℤ) ^ v * (D : ℤ)) ≠ 0 := by positivity
  have hcabs : |(((2 : ℤ) ^ v * (D : ℤ) : ℤ) : ℝ)| = 2 ^ v * (D : ℝ) := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((2 : ℤ) ^ v * (D : ℤ) : ℤ) : ℝ))]
    push_cast
    ring
  have harg : (((2 : ℤ) ^ v * (D : ℤ) : ℤ) : ℝ) * (((3 : ℤ) ^ N : ℤ) : ℝ)
      / (((2 : ℤ) ^ N : ℤ) : ℝ) = 2 ^ v * (D : ℝ) * ((3 : ℝ) / 2) ^ N := by
    push_cast
    rw [div_pow]
    field_simp
  have h := le_distToNearestInt_transfer (X := (2 : ℤ) ^ N) (Y := (3 : ℤ) ^ N)
    (c := (2 : ℤ) ^ v * (D : ℤ)) (by positivity) hc hB hdet hΓ₁a hΓ₁b hΓ₂a hΓ₂b hP₁ hP₂
    (by push_cast; exact hΛ₁) (by push_cast; exact hΛ₂) hB₁ hB₂
  rw [hcabs, harg] at h
  push_cast at h
  exact h

/-- **The unrefined corollary** (`Γ = 1`, `v = 0`): the rank-2 elimination with no content gain
and no 2-power shift, `|D·3^N − m·2^N| ≥ (2^N − D·Λ)/B`.  This is the form in which the step is
usually quoted; the content `P` and the shift `v` are what make it usable at the real Padé
parameters. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem transfer_prop_one {N D : ℕ} {a₁ b₁ a₂ b₂ : ℤ} {Λ B : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hdet : a₁ * b₂ ≠ a₂ * b₁)
    (hΛ₁ : |(a₁ : ℝ) * 2 ^ N + (b₁ : ℝ) * 3 ^ N| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * 2 ^ N + (b₂ : ℝ) * 3 ^ N| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) (m : ℤ) :
    ((2 : ℝ) ^ N - (D : ℝ) * Λ) / B ≤ |(D : ℝ) * 3 ^ N - (m : ℝ) * 2 ^ N| := by
  have h := multiplier_transfer_pow (N := N) (v := 0) (D := D) (Γ₁ := 1) (Γ₂ := 1) (P := 1)
    hD hB hdet (one_dvd _) (one_dvd _) (one_dvd _) (one_dvd _) (by norm_num) (by norm_num)
    hΛ₁ hΛ₂ hB₁ hB₂ m
  simpa using h

/-- **Orientation check.**  A worked instance of `transfer_prop_one` at `N = 4`, with the two
forms `−5·2⁴ + 1·3⁴ = 1` and `−81·2⁴ + 16·3⁴ = 0` (independent: the determinant is
`(−5)·16 − (−81)·1 = 1`), sizes `Λ = 1`, `B = 16`.  The lemma returns `15/16`, against the true
value `|3⁴ − 5·2⁴| = 1` — so the estimate is neither vacuous nor reversed, and the `Λ`, `B` slots
are charged in the direction claimed. -/
@[category test, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem transfer_prop_one_sanity (m : ℤ) : (15 : ℝ) / 16 ≤ |81 - (m : ℝ) * 16| := by
  have h := transfer_prop_one (N := 4) (D := 1) (a₁ := -5) (b₁ := 1) (a₂ := -81) (b₂ := 16)
    (Λ := 1) (B := 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num at h
  exact h

/-! ## 4. The socket

The hypotheses bundled.  A Padé engine — Habsieger's, Beukers', Zudilin's — supplies one
`TwoForms` per parameter and inherits the three conclusions.  Nothing in this section knows which
construction produced the forms; swapping engines means a new source of `TwoForms`, not a new
transfer lemma. -/

/-- Two independent integer forms `aᵢ·X + bᵢ·Y` of size at most `Λ`, with second coefficients of
size at most `B`, and with contents `Γᵢ` of absolute value at least `P`. -/
structure TwoForms (X Y : ℤ) (P Λ B : ℝ) where
  /-- First coefficient of the first form. -/
  a₁ : ℤ
  /-- Second coefficient of the first form. -/
  b₁ : ℤ
  /-- Content of the first form (written `Π` in the literature). -/
  Γ₁ : ℤ
  /-- First coefficient of the second form. -/
  a₂ : ℤ
  /-- Second coefficient of the second form. -/
  b₂ : ℤ
  /-- Content of the second form. -/
  Γ₂ : ℤ
  /-- The two forms are independent. -/
  det : a₁ * b₂ ≠ a₂ * b₁
  /-- The first content divides the first coefficient of the first form. -/
  dvd_a₁ : Γ₁ ∣ a₁
  /-- The first content divides the second coefficient of the first form. -/
  dvd_b₁ : Γ₁ ∣ b₁
  /-- The second content divides the first coefficient of the second form. -/
  dvd_a₂ : Γ₂ ∣ a₂
  /-- The second content divides the second coefficient of the second form. -/
  dvd_b₂ : Γ₂ ∣ b₂
  /-- Lower bound for the first content. -/
  le_content₁ : P ≤ |(Γ₁ : ℝ)|
  /-- Lower bound for the second content. -/
  le_content₂ : P ≤ |(Γ₂ : ℝ)|
  /-- Size of the first form. -/
  size₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ
  /-- Size of the second form. -/
  size₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ
  /-- Size of the second coefficient of the first form. -/
  coeff₁ : |(b₁ : ℝ)| ≤ B
  /-- Size of the second coefficient of the second form. -/
  coeff₂ : |(b₂ : ℝ)| ≤ B

namespace TwoForms

variable {X Y : ℤ} {P Λ B : ℝ}

/-- The transfer lemma, from bundled data. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem transfer (F : TwoForms X Y P Λ B) {c : ℤ} (hX : 0 ≤ X) (hc : c ≠ 0) (m : ℤ) :
    P * (X : ℝ) ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| :=
  multiplier_transfer hX hc F.det F.dvd_a₁ F.dvd_b₁ F.dvd_a₂ F.dvd_b₂ F.le_content₁
    F.le_content₂ F.size₁ F.size₂ F.coeff₁ F.coeff₂ m

/-- The fraction form, from bundled data. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem transfer_div (F : TwoForms X Y P Λ B) {c : ℤ} (hX : 0 ≤ X) (hc : c ≠ 0) (hB : 0 < B)
    (m : ℤ) :
    (P * (X : ℝ) - |(c : ℝ)| * Λ) / B ≤ |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| :=
  multiplier_transfer_div hX hc hB F.det F.dvd_a₁ F.dvd_b₁ F.dvd_a₂ F.dvd_b₂ F.le_content₁
    F.le_content₂ F.size₁ F.size₂ F.coeff₁ F.coeff₂ m

/-- The repulsion form, from bundled data. -/
@[category research solved, AMS 11, ref "TshiftS1", group "tshift_s1"]
theorem le_distToNearestInt (F : TwoForms X Y P Λ B) {c : ℤ} (hX : 0 < X) (hc : c ≠ 0)
    (hB : 0 < B) :
    (P * (X : ℝ) - |(c : ℝ)| * Λ) / (B * (X : ℝ))
      ≤ distToNearestInt ((c : ℝ) * (Y : ℝ) / (X : ℝ)) :=
  le_distToNearestInt_transfer hX hc hB F.det F.dvd_a₁ F.dvd_b₁ F.dvd_a₂ F.dvd_b₂ F.le_content₁
    F.le_content₂ F.size₁ F.size₂ F.coeff₁ F.coeff₂

end TwoForms

end TShift
