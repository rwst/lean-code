/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import paradoxical.RCircuitSlice
import paradoxical.PigeonholeFiniteness
import paradoxical.RunPigeonhole
import paradoxical.RhinPolyBound

/-!
# The assembled bounded-circuit Baker reduction (research program I.1.2)

End-to-end assembly of the per-`R` reduction of `length-bound.html` §4d: the three
ingredient files are instantiated into one theorem whose **sole hypothesis is the
excursion bound** `M ≤ m^β` — the named quantitative wall of the program (the
excursion half of RT Conjecture 6.2, taken at the window minimum; `β_obs ∈
[1.58, 2.06]` on the computed slice, `nearcycle_baker.py`).

* the class: `RCircuitSlice R j n` — paradoxical `Ωⱼ(n)` with `n > 2` whose
  length-`j` parity word is the word of an `R`-circuit shape
  `1^{a₁}0^{e₁}⋯1^{a_R}0^{e_R}`;
* `Exc := excWin` (windowed excursion `maxₖ≤ⱼ Tᵏ(n)`, `RunPigeonhole`) — hypothesis
  `hpigeon` discharged by `pigeonhole_hyp`;
* `m := minWin` (windowed minimum `minₖ≤ⱼ Tᵏ(n)`, defined here) — hypothesis
  `hmH` discharged by `least_odd_poly_bound` (`RhinPolyBound`, Rhin + Cor 4.4′),
  since the window minimum bounds every odd term from below;
* engine: `finite_of_pigeonhole` (`PigeonholeFiniteness`) with `C = 1/3`,
  `Pw = 14.3`.

**`finite_RCircuitSlice`**: given `β ≥ 0` and the excursion bound
`excWin j n ≤ (minWin j n)^β` on the slice, the slice `{(j, n)}` is **finite**.

A bound uniform over *all* `R` would be the Collatz conjecture itself
(`length-bound.html` §0); the per-`R` statement is the honest endpoint.

`sorry`-free; axioms = std3 + the cited `Rhin.logForm_lower_bound` ([Rhi87]).

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz
  sequences." arXiv:2502.00948 (2025). §4 Corollary 4.4, §6 Conjecture 6.2.
* [Rhi87] Rhin, Georges. "Approximants de Padé et mesures effectives d'irrationalité."
  *Séminaire de Théorie des Nombres, Paris 1985–86*, 155–164. Birkhäuser, 1987.
-/

namespace Paradoxical

open CC RT

/-- The windowed minimum `minₖ≤ⱼ Tᵏ(n)` (a natural number) — the concrete `m` of the
reduction, companion to `excWin`. -/
def minWin (j n : ℕ) : ℕ :=
  (Finset.range (j + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
    fun k => T_iter k n

/-- Every window term is `≥ 1`, hence so is the windowed minimum. -/
lemma one_le_minWin (j n : ℕ) (hn : 1 ≤ n) : 1 ≤ minWin j n := by
  unfold minWin
  apply Finset.le_inf'
  intro k _
  exact T_iter_pos hn k

/-- The windowed minimum bounds every window term from below. -/
lemma minWin_le (j n k : ℕ) (hk : k ≤ j) : minWin j n ≤ T_iter k n := by
  unfold minWin
  exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- **The assembled bounded-circuit Baker reduction** (`length-bound.html` §4d).  Fix
`R ≥ 1` and `β ≥ 0`.  If every member of the `R`-circuit paradoxical slice satisfies
the excursion bound `excWin j n ≤ (minWin j n)^β` — the sole remaining hypothesis, the
excursion half of RT Conjecture 6.2 taken at the window minimum — then the slice is
**finite**.

All other links are unconditional: `hpigeon` is `pigeonhole_hyp` (run-length
pigeonhole, `RunPigeonhole`), `hmH` is `least_odd_poly_bound` (Rhin polynomial bound
`m ≤ (1/3)·j^{14.3}`, `RhinPolyBound`), and the collision engine is
`finite_of_pigeonhole` (`PigeonholeFiniteness`). -/
theorem finite_RCircuitSlice (R : ℕ) (hR : 0 < R) (β : ℝ) (hβ : 0 ≤ β)
    (hexc : ∀ j n, RCircuitSlice R j n → (excWin j n : ℝ) ≤ (minWin j n : ℝ) ^ β) :
    {p : ℕ × ℕ | RCircuitSlice R p.1 p.2}.Finite := by
  refine finite_of_pigeonhole R hR β 14.3 (1 / 3) hβ (by norm_num) (by norm_num)
    (RCircuitSlice R) (fun j n => (excWin j n : ℝ)) (fun j n => (minWin j n : ℝ))
    (fun j n hs => hs.2.1) (fun j n hs => hs.1) ?_ ?_ ?_ hexc
  · -- `hpigeon`, via `pigeonhole_hyp` at the witnessing shape
    rintro j n ⟨hn2, hpara, S, hlen, hwlen, hshape⟩
    subst hwlen
    have hSne : S ≠ [] := by rintro rfl; simp at hlen; omega
    rw [← hlen]
    exact pigeonhole_hyp S n (by omega) hSne hshape
  · -- `hm1`
    rintro j n ⟨hn2, -, -⟩
    exact_mod_cast one_le_minWin j n (by omega)
  · -- `hmH`, via the Rhin polynomial bound at the window minimum
    rintro j n ⟨hn2, hpara, -⟩
    exact least_odd_poly_bound j n (minWin j n) (by omega)
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_minWin j n (by omega)))
      (fun k hk _ => minWin_le j n k (by omega)) hpara

end Paradoxical
