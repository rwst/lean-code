/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.MultiplierTransfer
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The determinant's budget: the Cramer cap, and why re-spending it is vacuous

The elimination step of `TShift.MultiplierTransfer` spends the independence of two integer forms
`ℓᵢ = aᵢ·X + bᵢ·Y` on *nonvanishing*: some eliminant `Δᵢ = c·aᵢ + m·bᵢ` is nonzero, hence
`|Δᵢ| ≥ |Γᵢ| ≥ P`.  The determinant `det = a₁b₂ − a₂b₁` carries more information than that, and a
standing proposal is to spend the surplus instead — to use `b₂Δ₁ − b₁Δ₂ = c·det` as a lower bound
`maxᵢ|Δᵢ| ≥ |c||det|/(2B)` and pocket the factor that treating the free integer `m` adversarially
gives away.

This file works out what that buys.  The answer is nothing, and the reason is a cap: the same two
forms that produce the determinant also bound it.

* **Cramer** (`det_cramer`): `X·det = b₂ℓ₁ − b₁ℓ₂` and `Y·det = a₁ℓ₂ − a₂ℓ₁`, two ring identities.
  The columns are recoverable from the forms; nothing is hidden in the system.
* **The cap** (`det_cap`, `det_cap_size`): hence `|det|·X ≤ |b₂||ℓ₁| + |b₁||ℓ₂| ≤ 2BΛ`.  A
  determinant is exponentially large only if the forms are exponentially bigger than the column
  they sit on.
* **The refinement** (`delta_det`, `det_le_delta_sum`, `multiplier_transfer_det`): the surplus is
  real — `|c||det| ≤ B|Δ₁| + B|Δ₂|` gives the sharper transfer
  `X·|c||det| ≤ 2B(B|N| + |c|Λ)` with `N = c·Y − m·X`.
* **The no-go** (`det_gain_vacuous`): the refinement beats `maxᵢ|Δᵢ| ≥ P` only when
  `|c||det| > 2BP`, and by the cap that *forces* `|c|Λ ≥ P·X` — the exact negation of the
  condition `P·X > |c|Λ` under which the transfer says anything at all.  The improvement region and
  the validity region are disjoint.

The content `P` is carried throughout, and this is the point: it appears on both sides of the
chain and cancels out of it, so the no-go is not an artefact of reading the classical bound at
`P = 1`.  The two regions are disjoint for a content-refined transfer exactly as they are for the
crude one.

## The remainder, and its ceiling

One branch survives as a constants question rather than a rate question.  When `Δ₁ = 0` the
identity is exact, `|Δ₂||b₁| = |c||det|` (`det_bad_case`), and the single-form estimate then runs
with `|Δ₂|` in place of `P` (`det_bad_case_transfer`).  That recovered factor has a ceiling that
needs no "in practice": inside the validity region `|Δ₂||b₁| < 2BP` (`det_bad_case_ceiling`), i.e.
`|Δ₂|/P < 2B/|b₁|`, a ratio of the crude coefficient bound to the actual coefficient.  On any Padé
family those two share their exponential rate, so the branch can never be a rate.

## What this file does not do

It proves a fact about a *method*, not about `‖(3/2)^k‖`: nothing here asserts any repulsion
bound, and no instance of the T-shift problem is proved or approached.  For orientation, the best
rates this elimination step carries are `θ = 0.57434` ([Hab03], `TShift.thetaHab`) and
`θ = 0.5803` ([Zud07]), with sojourn slopes `κ(0.57434) = 1.36761` and `κ(0.5803) = 1.34219` — both
`> 1`, i.e. both on the wrong side of the `2/3` threshold of `TShift.kappa_lt_one_iff`.  The
determinant channel does not move them: by the no-go it cannot move the exponent at all.

`MultiplierTransfer.lean` is left untouched; `delta_det` duplicates the `have` inside the proof of
`TShift.exists_delta_ne_zero` as a public declaration rather than refactoring it.

## Measured, elsewhere

Two numerical facts about the cap, both outside Lean and both recorded in the notes below, because
they are what make the no-go tight rather than merely true.  On [Hab03]'s own family the cap is
*saturated*: `lim (1/m)·log|det| = A(α) = lim (1/m)·log(2BΛ/X)`, the improvement margin is
`−0.0049395` nats per `m` and the validity margin `+0.0049395` — the same number, opposite signs,
and the margin the construction sits on is the one that proves `θ = 0.57434`.  And the triangle
step of `det_cap` is an *identity* there (`b₂ℓ₁` and `−b₁ℓ₂` carry the same sign at every `m`), so
the cap's entire slack is the printed size bounds.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide`.  Integer and real algebra only.

## Claim level

Elementary; the content is the *direction* of the two inequalities, not their difficulty.  The
no-go (`det_gain_vacuous`) is the formal statement of a negative audit result, and the orientation
check `det_gain_vacuous_sanity` exhibits it on the toy instance of `MultiplierTransfer`.

## References

* `plans/plan-Tshift-S8.html` §1.4 D1 (the derivation, items (1)–(5)) and §2.2 (targets T1–T7).
* `plans/note-Tshift-S8-WP0.html` §3 (the two amendments carried here: T4 with `P`, T6's provable
  ceiling) and §4 (the cap saturated on [Hab03]'s family).
* `plans/note-Tshift-S8-WPD.html` (the cap measured on the real two-column data: the triangle step
  lossless, the bad branch decaying at the validity margin).
* `plans/note-Tshift-S1-constants.html` §6.1 (the transfer this file extends).
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308 — §3, the instance the cap is measured on.
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)^k‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.
-/

namespace TShift

/-! ## 1. Cramer, and the cap it implies

`Γ` is the content, `Λ` the size of the forms, `B` the size of their second coefficients, exactly
as in `TShift.MultiplierTransfer`. -/

/-- **Cramer for two integer forms** (D1(1)).  With `ℓᵢ = aᵢ·X + bᵢ·Y` and
`det = a₁b₂ − a₂b₁`, both columns are recoverable from the two forms:

`X·det = b₂ℓ₁ − b₁ℓ₂`  and  `Y·det = a₁ℓ₂ − a₂ℓ₁`.

Two ring identities, with no hypothesis whatsoever on the data — in particular none on `bᵢ` and
none relating `X` to `Y`. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_cramer {X Y a₁ b₁ a₂ b₂ ℓ₁ ℓ₂ : ℤ} (h₁ : ℓ₁ = a₁ * X + b₁ * Y)
    (h₂ : ℓ₂ = a₂ * X + b₂ * Y) :
    X * (a₁ * b₂ - a₂ * b₁) = b₂ * ℓ₁ - b₁ * ℓ₂ ∧
      Y * (a₁ * b₂ - a₂ * b₁) = a₁ * ℓ₂ - a₂ * ℓ₁ := by
  subst h₁
  subst h₂
  constructor <;> ring

/-- **The determinant cap** (D1(2)), over `ℤ`.  The forms that produce the determinant also bound
it:

`|det|·|X| ≤ |b₂||ℓ₁| + |b₁||ℓ₂|`.

Only the first Cramer identity is used, so this is a statement about the column `X` alone. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_cap (X Y a₁ b₁ a₂ b₂ : ℤ) :
    |a₁ * b₂ - a₂ * b₁| * |X| ≤ |b₂| * |a₁ * X + b₁ * Y| + |b₁| * |a₂ * X + b₂ * Y| :=
  calc |a₁ * b₂ - a₂ * b₁| * |X| = |X * (a₁ * b₂ - a₂ * b₁)| := by
        rw [← abs_mul, mul_comm]
    _ = |b₂ * (a₁ * X + b₁ * Y) - b₁ * (a₂ * X + b₂ * Y)| := by
        rw [(det_cramer rfl rfl).1]
    _ ≤ |b₂ * (a₁ * X + b₁ * Y)| + |b₁ * (a₂ * X + b₂ * Y)| := abs_sub _ _
    _ = |b₂| * |a₁ * X + b₁ * Y| + |b₁| * |a₂ * X + b₂ * Y| := by rw [abs_mul, abs_mul]

/-- **The cap in the sizes** (D1(2), the form the transfer uses).  With `|ℓᵢ| ≤ Λ`, `|bᵢ| ≤ B` and
`0 ≤ X`:

`|det|·X ≤ 2·B·Λ`.

This is the whole budget of the determinant channel: the determinant is exponentially large only
if the forms are exponentially larger than the column. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_cap_size {X Y a₁ b₁ a₂ b₂ : ℤ} {Λ B : ℝ} (hX : 0 ≤ X)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)| * (X : ℝ) ≤ 2 * B * Λ := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hR : |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)| * |(X : ℝ)|
      ≤ |(b₂ : ℝ)| * |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)|
        + |(b₁ : ℝ)| * |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| := by
    exact_mod_cast det_cap X Y a₁ b₁ a₂ b₂
  rw [abs_of_nonneg hXR] at hR
  have h1 : |(b₂ : ℝ)| * |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ B * Λ :=
    mul_le_mul hB₂ hΛ₁ (abs_nonneg _) ((abs_nonneg _).trans hB₂)
  have h2 : |(b₁ : ℝ)| * |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ B * Λ :=
    mul_le_mul hB₁ hΛ₂ (abs_nonneg _) ((abs_nonneg _).trans hB₁)
  linarith

/-! ## 2. The eliminants, and the surplus the determinant really carries -/

/-- **The elimination identity** (D1(3)).  With `Δᵢ = c·aᵢ + m·bᵢ`,

`b₂Δ₁ − b₁Δ₂ = c·(a₁b₂ − a₂b₁)`.

This promotes the `have` inside the proof of `TShift.exists_delta_ne_zero`
(`MultiplierTransfer.lean`, §1) to a named declaration; there it is spent on nonvanishing, here on
the size of the determinant. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem delta_det (c m a₁ b₁ a₂ b₂ : ℤ) :
    b₂ * (c * a₁ + m * b₁) - b₁ * (c * a₂ + m * b₂) = c * (a₁ * b₂ - a₂ * b₁) := by
  ring

/-- **The surplus, max-free** (D1(3)).  From `delta_det` and `|bᵢ| ≤ B`:

`|c||det| ≤ B|Δ₁| + B|Δ₂|`,

which is the division-free reading of `maxᵢ|Δᵢ| ≥ |c||det|/(2B)`: a large determinant forces a
large eliminant, and this is the *only* thing the determinant contributes beyond nonvanishing. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_le_delta_sum {c m a₁ b₁ a₂ b₂ : ℤ} {B : ℝ} (hB₁ : |(b₁ : ℝ)| ≤ B)
    (hB₂ : |(b₂ : ℝ)| ≤ B) :
    |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)|
      ≤ B * |(c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ)|
        + B * |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| := by
  have hid : (c : ℝ) * ((a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ))
      = (b₂ : ℝ) * ((c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ))
        - (b₁ : ℝ) * ((c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)) := by ring
  have h1 : |(b₂ : ℝ)| * |(c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ)|
      ≤ B * |(c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ)| :=
    mul_le_mul_of_nonneg_right hB₂ (abs_nonneg _)
  have h2 : |(b₁ : ℝ)| * |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)|
      ≤ B * |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| :=
    mul_le_mul_of_nonneg_right hB₁ (abs_nonneg _)
  calc |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)|
      = |(c : ℝ) * ((a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ))| := (abs_mul _ _).symm
    _ = |(b₂ : ℝ) * ((c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ))
          - (b₁ : ℝ) * ((c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ))| := by rw [hid]
    _ ≤ |(b₂ : ℝ) * ((c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ))|
          + |(b₁ : ℝ) * ((c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ))| := abs_sub _ _
    _ = |(b₂ : ℝ)| * |(c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ)|
          + |(b₁ : ℝ)| * |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ B * |(c : ℝ) * (a₁ : ℝ) + (m : ℝ) * (b₁ : ℝ)|
          + B * |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| := by linarith

/-- **The single-form estimate, read as a ceiling on the eliminant.**  The identity
`X·Δ = c·ℓ − b·N` with `N = c·Y − m·X` — the identity `TShift.transfer_one_form` is built on —
bounds `Δ` from *above* as well:

`X·|Δ| ≤ |c|·Λ + B·|N|`.

`transfer_one_form` reads it downwards (`|Δ| ≥ |Γ|` gives a lower bound for `|N|`); the
determinant channel needs it upwards. -/
@[category API, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem mul_abs_delta_le {X Y c m a b : ℤ} {Λ B : ℝ} (hX : 0 ≤ X)
    (hΛ : |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ Λ) (hB : |(b : ℝ)| ≤ B) :
    (X : ℝ) * |(c : ℝ) * (a : ℝ) + (m : ℝ) * (b : ℝ)|
      ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hid : (X : ℝ) * ((c : ℝ) * (a : ℝ) + (m : ℝ) * (b : ℝ))
      = (c : ℝ) * ((a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ))
        - (b : ℝ) * ((c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)) := by ring
  have h1 : |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ |(c : ℝ)| * Λ :=
    mul_le_mul_of_nonneg_left hΛ (abs_nonneg _)
  have h2 : |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)|
      ≤ B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| :=
    mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  calc (X : ℝ) * |(c : ℝ) * (a : ℝ) + (m : ℝ) * (b : ℝ)|
      = |(X : ℝ) * ((c : ℝ) * (a : ℝ) + (m : ℝ) * (b : ℝ))| := by
        rw [abs_mul, abs_of_nonneg hXR]
    _ = |(c : ℝ) * ((a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ))
          - (b : ℝ) * ((c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ))| := by rw [hid]
    _ ≤ |(c : ℝ) * ((a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ))|
          + |(b : ℝ) * ((c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ))| := abs_sub _ _
    _ = |(c : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|
          + |(b : ℝ)| * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ |(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| := by linarith

/-! ## 3. The refined transfer, and the no-go -/

/-- **The determinant-refined transfer** (D1(3), division-free).  Combining the surplus
`|c||det| ≤ B|Δ₁| + B|Δ₂|` with the single-form ceiling:

`X·|c||det| ≤ 2B·(B|N| + |c|Λ)`,  `N = c·Y − m·X`.

Against `multiplier_transfer`'s `P·X ≤ |c|Λ + B|N|`, this replaces the content `P` by
`|c||det|/(2B)`: a genuine refinement whenever the latter is larger.  `det_gain_vacuous` shows
that never happens where the bound is useful.  No content hypothesis is needed, and division by
`B` or `bᵢ` is avoided throughout. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem multiplier_transfer_det {X Y c m a₁ b₁ a₂ b₂ : ℤ} {Λ B : ℝ} (hX : 0 ≤ X)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B) :
    (X : ℝ) * (|(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)|)
      ≤ 2 * B * (B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)| + |(c : ℝ)| * Λ) := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hB0 : (0 : ℝ) ≤ B := (abs_nonneg _).trans hB₁
  have hsum := det_le_delta_sum (c := c) (m := m) (a₁ := a₁) (a₂ := a₂) hB₁ hB₂
  have k1 := mul_abs_delta_le (X := X) (Y := Y) (c := c) (m := m) hX hΛ₁ hB₁
  have k2 := mul_abs_delta_le (X := X) (Y := Y) (c := c) (m := m) hX hΛ₂ hB₂
  have h1 := mul_le_mul_of_nonneg_left hsum hXR
  have h2 := mul_le_mul_of_nonneg_left k1 hB0
  have h3 := mul_le_mul_of_nonneg_left k2 hB0
  linarith

/-- **The no-go** (D1(4)).  The refinement of `multiplier_transfer_det` improves on the
nonvanishing bound `maxᵢ|Δᵢ| ≥ P` only in the region `|c||det| > 2BP`; there, the cap forces

`P·X ≤ |c|·Λ`,

which is the exact negation of the condition `P·X > |c|·Λ` under which `multiplier_transfer`'s
conclusion is not vacuous.  So the improvement region and the validity region are disjoint: the
determinant's exponential content is spent in full by `Δᵢ ≠ 0`, and there is no factor left to
recover at rate level.

Two things to note about the statement.  First, it carries the **content** `P`, not `1`: `P`
appears in the improvement hypothesis and in the conclusion, and cancels out of the argument — so
the no-go is not an artefact of reading the classical bound at `P = 1`, which is the one way it
could have been an artefact.  Second, the hypotheses are a strict subset of
`multiplier_transfer`'s: neither the independence `a₁b₂ ≠ a₂b₁` nor the divisibilities `Γᵢ ∣ aᵢ,
bᵢ` are used, only the sizes.  Nothing here says anything about `2/3`: `κ(0.57434) = 1.36761`. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_gain_vacuous {X Y c a₁ b₁ a₂ b₂ : ℤ} {P Λ B : ℝ} (hX : 0 ≤ X) (hB : 0 < B)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B)
    (himp : 2 * B * P < |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)|) :
    P * (X : ℝ) ≤ |(c : ℝ)| * Λ := by
  have hXR : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcap := det_cap_size hX hΛ₁ hΛ₂ hB₁ hB₂
  have h1 := mul_le_mul_of_nonneg_left hcap (abs_nonneg ((c : ℝ)))
  have h2 := mul_le_mul_of_nonneg_right himp.le hXR
  have key : 2 * B * (P * (X : ℝ)) ≤ 2 * B * (|(c : ℝ)| * Λ) := by linarith
  exact le_of_mul_le_mul_left key (by linarith)

/-! ## 4. The bad branch: the one surviving remainder, and its ceiling -/

/-- **The bad branch, exactly** (D1(5)).  When the first eliminant vanishes the surplus is an
identity rather than an inequality:

`Δ₁ = 0  ⟹  |Δ₂|·|b₁| = |c|·|det|`.

This is the branch where the determinant refinement is not merely an inequality about a maximum,
and it is the only part of the channel that survives the no-go — as a question about constants,
answered numerically at `plans/note-Tshift-S8-WPD.html`. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_bad_case {c m a₁ b₁ a₂ b₂ : ℤ} (h₁ : c * a₁ + m * b₁ = 0) :
    |c * a₂ + m * b₂| * |b₁| = |c| * |a₁ * b₂ - a₂ * b₁| := by
  have hid := delta_det c m a₁ b₁ a₂ b₂
  rw [h₁, mul_zero, zero_sub] at hid
  have key : (c * a₂ + m * b₂) * b₁ = -(c * (a₁ * b₂ - a₂ * b₁)) := by
    rw [← hid]; ring
  calc |c * a₂ + m * b₂| * |b₁| = |(c * a₂ + m * b₂) * b₁| := (abs_mul _ _).symm
    _ = |-(c * (a₁ * b₂ - a₂ * b₁))| := by rw [key]
    _ = |c| * |a₁ * b₂ - a₂ * b₁| := by rw [abs_neg, abs_mul]

/-- **The bad branch has a provable ceiling** (D1(5), as amended at WP0).  Inside the validity
region `|c|·Λ < P·X`, the factor the branch recovers is bounded outright:

`|Δ₂|·|b₁| < 2·B·P`,  i.e.  `|Δ₂|/P < 2B/|b₁|`,

with no "in practice" in it — the chain is `|Δ₂||b₁| = |c||det| ≤ 2B|c|Λ/X < 2BP`.  The surviving
stake of the whole channel is therefore the ratio of the crude coefficient bound `B` to the actual
`|b₁|`; on a Padé family both are `8^{n+1}` times a fixed base to the `m`, so they share their
exponential rate and the branch can never be a rate.  Measured on [Hab03]'s family it is below `1`
from `m = 64` on. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_bad_case_ceiling {X Y c m a₁ b₁ a₂ b₂ : ℤ} {P Λ B : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hΛ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ)
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B)
    (hval : |(c : ℝ)| * Λ < P * (X : ℝ)) (h₁ : c * a₁ + m * b₁ = 0) :
    |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| * |(b₁ : ℝ)| < 2 * B * P := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hcap := det_cap_size hX.le hΛ₁ hΛ₂ hB₁ hB₂
  have hid : |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| * |(b₁ : ℝ)|
      = |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)| := by
    exact_mod_cast det_bad_case h₁
  have h1 := mul_le_mul_of_nonneg_left hcap (abs_nonneg ((c : ℝ)))
  have h2 : 2 * B * (|(c : ℝ)| * Λ) < 2 * B * (P * (X : ℝ)) :=
    mul_lt_mul_of_pos_left hval (by linarith)
  have key : (X : ℝ) * (|(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| * |(b₁ : ℝ)|)
      < (X : ℝ) * (2 * B * P) := by rw [hid]; linarith
  exact lt_of_mul_lt_mul_left key hXR.le

/-- **The bad branch, through the single-form estimate** (D1(5), the per-form bound).  In the
branch `Δ₁ = 0` the second form carries the whole elimination, with `|Δ₂| = |c||det|/|b₁|` in place
of the content:

`|c|·|det|·X ≤ |b₁|·(|c|·Λ + B·|N|)`,  `N = c·Y − m·X`.

This is `mul_abs_delta_le` at `(ℓ₂, b₂)` multiplied by `|b₁|`, i.e. the refined transfer of the
branch; `det_bad_case_ceiling` is what keeps its gain over `multiplier_transfer` bounded. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_bad_case_transfer {X Y c m a₁ b₁ a₂ b₂ : ℤ} {Λ B : ℝ} (hX : 0 ≤ X)
    (hΛ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| ≤ Λ) (hB₂ : |(b₂ : ℝ)| ≤ B)
    (h₁ : c * a₁ + m * b₁ = 0) :
    |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)| * (X : ℝ)
      ≤ |(b₁ : ℝ)| * (|(c : ℝ)| * Λ + B * |(c : ℝ) * (Y : ℝ) - (m : ℝ) * (X : ℝ)|) := by
  have hid : |(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| * |(b₁ : ℝ)|
      = |(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)| := by
    exact_mod_cast det_bad_case h₁
  have k2 := mul_abs_delta_le (X := X) (Y := Y) (c := c) (m := m) hX hΛ₂ hB₂
  have h2 := mul_le_mul_of_nonneg_left k2 (abs_nonneg ((b₁ : ℝ)))
  have hmul : (X : ℝ) * (|(c : ℝ) * (a₂ : ℝ) + (m : ℝ) * (b₂ : ℝ)| * |(b₁ : ℝ)|)
      = (X : ℝ) * (|(c : ℝ)| * |(a₁ : ℝ) * (b₂ : ℝ) - (a₂ : ℝ) * (b₁ : ℝ)|) := by rw [hid]
  linarith

/-! ## 5. The socket

The same statements from bundled `TShift.TwoForms` data, so that a Padé engine which already
supplies one structure gets the cap and the no-go back without re-instantiating anything.  Note
that `TwoForms.det` is the *independence hypothesis* `a₁b₂ ≠ a₂b₁`; the integer itself is
`TwoForms.determinant`. -/

namespace TwoForms

variable {X Y : ℤ} {P Λ B : ℝ}

/-- The determinant `a₁b₂ − a₂b₁` of the two bundled forms.  The field `TwoForms.det` is the
hypothesis that this is nonzero. -/
def determinant (F : TwoForms X Y P Λ B) : ℤ := F.a₁ * F.b₂ - F.a₂ * F.b₁

/-- The determinant cap, from bundled data: `|det|·X ≤ 2BΛ`. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_cap_size (F : TwoForms X Y P Λ B) (hX : 0 ≤ X) :
    |(F.determinant : ℝ)| * (X : ℝ) ≤ 2 * B * Λ := by
  simp only [determinant]
  push_cast
  exact TShift.det_cap_size hX F.size₁ F.size₂ F.coeff₁ F.coeff₂

/-- The no-go, from bundled data: in the improvement region `2BP < |c||det|` the transfer is
vacuous, `P·X ≤ |c|Λ`. -/
@[category research solved, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_gain_vacuous (F : TwoForms X Y P Λ B) {c : ℤ} (hX : 0 ≤ X) (hB : 0 < B)
    (himp : 2 * B * P < |(c : ℝ)| * |(F.determinant : ℝ)|) : P * (X : ℝ) ≤ |(c : ℝ)| * Λ := by
  simp only [determinant] at himp
  push_cast at himp
  exact TShift.det_gain_vacuous hX hB F.size₁ F.size₂ F.coeff₁ F.coeff₂ himp

end TwoForms

/-! ## 6. Orientation check -/

/-- **Orientation check.**  The `81/16` toy of `TShift.transfer_prop_one_sanity`: columns
`X = 2⁴ = 16`, `Y = 3⁴ = 81`, forms `−5·16 + 1·81 = 1` and `−81·16 + 16·81 = 0`, sizes `Λ = 1`,
`B = 16`, content `P = 1`, multiplier `c = 1`.  Its determinant is
`(−5)·16 − (−81)·1 = 1`, so the improvement condition reads `32 < 1` and the validity condition
reads `1 < 16`: the toy sits strictly inside the validity region and therefore, by
`det_gain_vacuous`, strictly outside the improvement region — D1(4) in one worked instance.

The proof runs *through* the no-go rather than by evaluating the determinant: assuming the
improvement, `det_gain_vacuous` returns `1·16 ≤ 1·1`.  So this also checks that the toy's data
really does satisfy the size hypotheses at the stated `Λ` and `B`. -/
@[category test, AMS 11, ref "TshiftS8", group "tshift_s8"]
theorem det_gain_vacuous_sanity
    (himp : 2 * (16 : ℝ) * 1 < |((1 : ℤ) : ℝ)| *
      |((-5 : ℤ) : ℝ) * ((16 : ℤ) : ℝ) - ((-81 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)|) : False := by
  have h := det_gain_vacuous (X := 16) (Y := 81) (c := 1) (a₁ := -5) (b₁ := 1) (a₂ := -81)
    (b₂ := 16) (P := 1) (Λ := 1) (B := 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) himp
  norm_num at h

end TShift
