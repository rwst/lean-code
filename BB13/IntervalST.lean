/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import QuantitativeSubspace.SubspaceCountTwo

/-!
# The large solutions of a system, as an interval result (WP A5 of plan-beyond-BB13)

Subspace-Theorems' assembly `NumberField.exists_finset_submodule_of_forall_interval` takes an
interval result for the domains and turns it into subspaces for the solutions of a normalized
system, in two steps: it brings the solutions into the domain (raised exponents and one scalar
for the constants), and then it spends Layer 9.4's gap principle at ratio `1 + δ / (2 n)` on
each interval. The first step alone says that the large solutions lie in `NS` proper subspaces,
or have `log H(x)` in one of `NI` intervals `[s, ρ s)` that do not depend on the solution. A
system with a better gap principle of its own can then count each interval itself; for the frame
of Problem 10.13 this is the elementary ratio `ρ₀ ≈ 1.2618` against `1 + δ/4 ≈ 1.065`
(`BB13/LineCoverRho.lean`).

This file first proved that step here. It is now upstream (item M1 of
`plans/plan-beyond-BB13.html` §7, Subspace-Theorems `eefd0e0`), and the two names below, which
the preprint cites, are aliases of the upstream theorems.

## Main results

* `BB13.exists_interval_of_forall_interval`: the first step of the assembly, for any interval
  result of the conjugated forms (`NumberField.exists_forall_mem_interval_systemSet`).
* `BB13.exists_interval_of_isNormalizedSystem_two`: the same with the interval result in two
  variables: at most two subspaces and `subspaceChainLength 1 s (2 ε) A` intervals of ratio
  `4 σ⁻¹`, above any `X₀ ≥ systemThresholdTwo`
  (`NumberField.exists_forall_mem_interval_systemSet_two`).

## References

* J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
  proof of Theorem 2.1.
* R. Stephan, *Line counts and a census for the exceptions to `‖(3/2)^n‖ ≥ (3/4)^n`, with an
  application to Waring's problem*, preprint (2026), doi:10.13140/RG.2.2.15019.20008, Thm 7.2.
* `plans/plan-beyond-BB13.html`, §3.4, WP A5; §7, M1.
-/

namespace BB13

/-- **The large solutions of a system lie in `NS` subspaces or in `NI` height intervals**, from
any interval result above `X₀` for the conjugated forms. Upstream as
`NumberField.exists_forall_mem_interval_systemSet`. -/
alias exists_interval_of_forall_interval := NumberField.exists_forall_mem_interval_systemSet

/-- **The large solutions of a system in two variables lie in two subspaces or in `m` height
intervals** `[s, 4 σ⁻¹ s)`, `s ≥ X₀`, for every `X₀ ≥ systemThresholdTwo`. Upstream as
`NumberField.exists_forall_mem_interval_systemSet_two`. -/
alias exists_interval_of_isNormalizedSystem_two :=
  NumberField.exists_forall_mem_interval_systemSet_two

end BB13
