/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.Z32Balance

/-! # Axiom audit of `CarryBridge/` — every theorem must be std3
(`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no `native_decide`.
Regenerate the list when a file is added.  `Z32Balance` has its own file: `Z32.BalanceVectors`
and `Z32.CertComplete` cannot be imported together. -/

-- Z32Balance.lean
#print axioms CarryBridge.under_edgeGraph
#print axioms CarryBridge.outflow_balanceFlow
#print axioms CarryBridge.isCirculation_balanceFlow
#print axioms CarryBridge.isTrap_map_iff
#print axioms CarryBridge.BalanceVec.isTrap_supp'
#print axioms CarryBridge.BalanceVec.reach_of_pos
#print axioms CarryBridge.BalanceVec.mem_core
#print axioms CarryBridge.extFlow_fin
#print axioms CarryBridge.extFlow_pos
#print axioms CarryBridge.toBalanceVec_μ
#print axioms CarryBridge.exists_balanceVec'
