/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Dynamics.StronglyMixing

@[expose] public section

/-!
# Bernoulli systems

A measure-preserving system `(f, μ)` is a **Bernoulli system** if it is isomorphic — via a
measure-preserving measurable equivalence intertwining the dynamics — to a one-sided **Bernoulli
shift**: the coordinate shift `seqShift` on `ℕ → α` equipped with an i.i.d. product measure
`Measure.infinitePi (fun _ => ν)`, for some probability space `(α, ν)`. This is the standard
(Ornstein-theoretic) notion: "Bernoulli" means "isomorphic to *some* Bernoulli shift", so the
single-coordinate law `(α, ν)` is existentially quantified.

* `IsBernoulli` — the predicate.
* `IsBernoulli.isStronglyMixing` — **every Bernoulli system is strongly mixing.** Immediate from
  `isStronglyMixing_infinitePi_shift` (the Bernoulli shift itself is strongly mixing) transported
  across the isomorphism (`IsStronglyMixing.of_measurableEquiv`).

## References
* Ornstein, Donald S. *Ergodic theory, randomness, and dynamical systems.* Yale Univ. Press, 1974
  (a system is *Bernoulli* iff it is measure-theoretically isomorphic to a Bernoulli shift).
-/

namespace MeasureTheory

open ProbabilityTheory

variable {β : Type*} [MeasurableSpace β]

/-- A measure-preserving system `(f, μ)` is **Bernoulli** if it is isomorphic — via a
measure-preserving measurable equivalence `e` intertwining the dynamics (`Function.Semiconj e f
seqShift`) — to a one-sided Bernoulli shift: the coordinate shift `seqShift` on `ℕ → α` with an
i.i.d. product measure `Measure.infinitePi (fun _ => ν)`, for some probability space `(α, ν)`. -/
def IsBernoulli (f : β → β) (μ : Measure β) : Prop :=
  ∃ (α : Type) (_ : MeasurableSpace α) (ν : Measure α) (_ : IsProbabilityMeasure ν)
    (e : β ≃ᵐ (ℕ → α)),
    MeasurePreserving (⇑e) μ (Measure.infinitePi fun _ => ν) ∧ Function.Semiconj (⇑e) f seqShift

/-- **Every Bernoulli system is strongly mixing.** The Bernoulli shift `(seqShift,
Measure.infinitePi (fun _ => ν))` is strongly mixing (`isStronglyMixing_infinitePi_shift`), and
strong mixing is an isomorphism invariant (`IsStronglyMixing.of_measurableEquiv`), so it transfers
to any system isomorphic to it. -/
theorem IsBernoulli.isStronglyMixing {f : β → β} {μ : Measure β} (h : IsBernoulli f μ) :
    IsStronglyMixing f μ := by
  obtain ⟨α, hα, ν, hν, e, he_mp, he_sc⟩ := h
  exact IsStronglyMixing.of_measurableEquiv e he_mp he_sc (isStronglyMixing_infinitePi_shift ν)

end MeasureTheory
