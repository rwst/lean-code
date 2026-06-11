/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.SetSTU
import BertinPisot.AlphaPowTheorem
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem 5.2.4 — the `‖λαⁿ‖` characterization of `U` (Bertin §5.2)

Bertin's **Theorem 5.2.4** (*Pisot and Salem Numbers* [Ber92], §5.2): a real `α > 1` belongs to
`U = S ∪ T` (the Pisot–Salem numbers) **iff** there is a real `λ ≥ 1` with
```
  ‖λαⁿ‖ ≤ 1 / (2eα(α+1)(1 + log λ))      for all n ∈ ℕ,
```
where `‖·‖ = distToNearestInt` is the distance to the nearest integer.

**Backward direction (`∃λ ⟹ α ∈ U`) — proved.** This is exactly Theorem 5.1.1
(`Bertin.AlphaPow.pisotSalem_theorem_5_1_1'`, proved in full in `AlphaPowTheorem.lean`): its
hypothesis is the very bound above, and its conclusion `IsIntegral ℤ α ∧ (∀ conjugate β ≠ α, ‖β‖ ≤ 1)`
is, together with `1 < α`, precisely membership in `U` (`Bertin.mem_U_iff`).

**Forward direction (necessary condition, `α ∈ U ⟹ ∃λ`) — cited.** Bertin's construction: pick a Pisot
number `μ ∈ ℚ(α) ∩ S` (such `μ` exists by Theorem 5.2.2) and set `λ = μ^ν`. Then
`λαⁿ + ∑_{j=2}^{s} λ⁽ʲ⁾α⁽ʲ⁾ⁿ` is a rational integer (the trace of `λαⁿ`), and the conjugate sum is
bounded by `(s−1)δ^ν` (`δ < 1` the largest modulus among the conjugates of `μ`), which for large `ν`
falls below `1 / (2eα(α+1)(1 + log λ))`; hence `‖λαⁿ‖` equals that conjugate sum and obeys (1). This
rests on Theorem 5.2.2 and a calibration not formalized here, so it is recorded as a `cited` axiom.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.2, Thm 5.2.4.
-/

namespace Bertin

/- The necessary condition of Theorem 5.2.4 — Bertin's construction of a multiplier `λ = μ^ν` from a
Pisot number `μ ∈ ℚ(α) ∩ S` (Theorem 5.2.2); not formalized here. -/
informal_result "pisot-multiplier-necessary-condition"
  latex "Let $\\alpha\\in U$ with conjugates $\\alpha=\\alpha^{(1)},\\alpha^{(2)},\\dots,\\alpha^{(s)}$ (so $|\\alpha^{(j)}|\\le 1$ for $j\\ge 2$). By Theorem 5.2.2 the real field $\\mathbb{Q}(\\alpha)$ contains a Pisot number $\\mu\\in S$; let $\\delta<1$ bound the moduli of its conjugates $\\mu^{(j)}$ ($j\\ge 2$). Put $\\lambda=\\mu^{\\nu}$ ($\\nu\\in\\mathbb{N}^*$), so $|\\lambda^{(j)}|\\le\\delta^{\\nu}$. The number $\\lambda\\alpha^n+\\sum_{j=2}^{s}\\lambda^{(j)}{\\alpha^{(j)}}^{n}$ is a rational integer (the trace of $\\lambda\\alpha^n$), and $\\big|\\sum_{j=2}^{s}\\lambda^{(j)}{\\alpha^{(j)}}^{n}\\big|\\le(s-1)\\delta^{\\nu}$. Choosing $\\nu$ with $(s-1)\\delta^{\\nu}\\le\\frac{1}{2e\\alpha(\\alpha+1)(1+\\nu\\log\\mu)}=\\frac{1}{2e\\alpha(\\alpha+1)(1+\\log\\lambda)}$ gives $\\|\\lambda\\alpha^n\\|=\\big|\\sum_{j=2}^{s}\\lambda^{(j)}{\\alpha^{(j)}}^{n}\\big|\\le\\frac{1}{2e\\alpha(\\alpha+1)(1+\\log\\lambda)}$ for all $n$."
  refs "Ber92"

/-- **Theorem 5.2.4, necessary condition** (Bertin §5.2). If `α > 1` is a Pisot or Salem number
(`α ∈ U`), then there is a multiplier `λ ≥ 1` with `‖λαⁿ‖ ≤ 1/(2eα(α+1)(1 + log λ))` for all `n`.
Bertin's construction takes `λ = μ^ν` for a Pisot number `μ ∈ ℚ(α) ∩ S` (Theorem 5.2.2) and `ν` large;
it is recorded here as a `cited` axiom (see `pisot-multiplier-necessary-condition`). -/
@[category research solved, AMS 11, ref "Ber92", formal_uses U,
  informal_uses "pisot-multiplier-necessary-condition"]
axiom theorem_5_2_4_necessary (α : ℝ) (hα : 1 < α) (hU : α ∈ U) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ n : ℕ,
      distToNearestInt (lam * α ^ n) ≤
        1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam))

/-- **Theorem 5.2.4** (Bertin §5.2). A real `α > 1` belongs to `U` (is a Pisot or Salem number) **iff**
there is a real `λ ≥ 1` with
`‖λαⁿ‖ ≤ 1/(2eα(α+1)(1 + log λ))` for every `n`.

The backward direction is Theorem 5.1.1 (`Bertin.AlphaPow.pisotSalem_theorem_5_1_1'`, proved): the
bound forces `α` to be an algebraic integer all of whose other conjugates have modulus `≤ 1`, i.e.
`α ∈ U`. The forward (necessary) direction is the `cited` `theorem_5_2_4_necessary`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses U,
  informal_uses "pisot-multiplier-necessary-condition"]
theorem theorem_5_2_4 (α : ℝ) (hα : 1 < α) :
    α ∈ U ↔ ∃ lam : ℝ, 1 ≤ lam ∧ ∀ n : ℕ,
      distToNearestInt (lam * α ^ n) ≤
        1 / (2 * Real.exp 1 * α * (α + 1) * (1 + Real.log lam)) := by
  constructor
  · intro hU
    exact theorem_5_2_4_necessary α hα hU
  · rintro ⟨lam, hlam, hbound⟩
    have h := AlphaPow.pisotSalem_theorem_5_1_1' α lam hα hlam hbound
    exact (mem_U_iff α).mpr ⟨hα, h.1, h.2.1⟩

end Bertin
