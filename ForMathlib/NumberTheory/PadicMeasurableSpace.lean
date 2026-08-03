/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace

@[expose] public section

/-!
# The Borel σ-algebra on `ℚ_[p]` and on `ℤ_[p]`

Mathlib equips `ℚ_[p]` and `ℤ_[p]` with a complete metric and (via
`Mathlib/NumberTheory/Padics/ProperSpace.lean`) with `ProperSpace ℚ_[p]` and `CompactSpace ℤ_[p]`,
but it gives neither type a `MeasurableSpace` instance, so that even
`MeasurableSpace (ℝ × ℚ_[2] × ℚ_[3])` fails to synthesize.  (`Mathlib/NumberTheory/Padics/Measure/`
is a false friend: it is Iwasawa-style *abstract* `p`-adic measure theory — continuous linear
functionals on `C(X, R)` — and has no σ-algebra in it.)

This file supplies the missing instances in the standard way, exactly as Mathlib does for `ℝ`,
`ℂ` and `ENNReal`: the σ-algebra is the Borel σ-algebra of the metric topology, declared together
with the `BorelSpace` instance that identifies the two.  Both types are second countable
(`ℚ_[p]` is proper, `ℤ_[p]` is compact), so products, subtypes and quotients inherit well-behaved
Borel structures — in particular `Prod.borelSpace` applies to `ℝ × ℚ_[2] × ℚ_[3]`.

These four lines are upstreamable as they stand.  Note that
`ForMathlib/NumberTheory/PadicIntHaar.lean` currently carries `[MeasurableSpace ℤ_[p]]` and
`[BorelSpace ℤ_[p]]` as explicit hypotheses precisely because they were unavailable; with this file
imported they are discharged by instance search.

## Main declarations

* `Padic.instMeasurableSpace`, `Padic.instBorelSpace` — the Borel σ-algebra on `ℚ_[p]`.
* `PadicInt.instMeasurableSpace`, `PadicInt.instBorelSpace` — the Borel σ-algebra on `ℤ_[p]`.
* `PadicInt.measurable_coe` — the inclusion `ℤ_[p] → ℚ_[p]` is measurable.
* `Padic.measurableSet_norm_le_one` — the unit ball of `ℚ_[p]` is measurable.
-/

open MeasureTheory Metric

variable (p : ℕ) [Fact p.Prime]

/-- The `p`-adic numbers carry the Borel σ-algebra of their metric topology. -/
noncomputable instance Padic.instMeasurableSpace : MeasurableSpace ℚ_[p] := borel _

instance Padic.instBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The `p`-adic integers carry the Borel σ-algebra of their metric topology. -/
noncomputable instance PadicInt.instMeasurableSpace : MeasurableSpace ℤ_[p] := borel _

instance PadicInt.instBorelSpace : BorelSpace ℤ_[p] := ⟨rfl⟩

variable {p}

/-- The inclusion `ℤ_[p] → ℚ_[p]` is measurable, being an isometry. -/
theorem PadicInt.measurable_coe : Measurable ((↑) : ℤ_[p] → ℚ_[p]) :=
  continuous_subtype_val.measurable

/-- The unit ball `{x : ℚ_[p] | ‖x‖ ≤ 1}` — the image of `ℤ_[p]` — is a measurable set. -/
theorem Padic.measurableSet_norm_le_one : MeasurableSet {x : ℚ_[p] | ‖x‖ ≤ 1} :=
  (isClosed_le continuous_norm continuous_const).measurableSet
