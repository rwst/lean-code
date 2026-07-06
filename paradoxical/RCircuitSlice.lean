import paradoxical.Defs
import RT.CRozLemma32

open RT

/-- The **`R`-circuit paradoxical slice**: paradoxical `Ωⱼ(n)` with `n > 2` whose
length-`j` parity word is the word of an `R`-circuit shape
`1^{a₁}0^{e₁}⋯1^{a_R}0^{e_R}` (`R = S.length`, `j = wlen S`). -/
def RCircuitSlice (R j n : ℕ) : Prop :=
  2 < n ∧ IsParadoxical j n ∧
    ∃ S : List (ℕ × ℕ), S.length = R ∧ wlen S = j ∧ pbits j n = wordOfShape S

