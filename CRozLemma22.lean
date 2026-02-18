import C2
import CRoz
import ParityVector


/-!
* [Gar81] Garner, Lynn E. "On the Collatz 3𝑛+ 1 algorithm." Proceedings of the American
  Mathematical Society 82.1 (1981): 19-22.
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

/-- **Theorem 2.2** (Rozier–Terracol), inequality (3).
    For every positive integers `j` and `n`, writing `q = num_odd_steps j n`,
    we have `(3^q - 2^q) / 2^j ≤ E_j(n) ≤ (3^q - 2^q) / 2^q`. -/
theorem E_bounds (j n : ℕ) (hj : 0 < j) (hn : 0 < n) :
    let q := num_odd_steps j n
    ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ j ≤ E j n ∧
    E j n ≤ ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ q := by
  sorry

/-- The upper bound in Theorem 2.2 is reached iff `V_j(n) = ⟨0^{j-q} 1^q⟩`,
    i.e. `n ≡ -2^{j-q} (mod 2^j)`. -/
theorem E_upper_bound_iff (j n : ℕ) (hj : 0 < j) (hn : 0 < n) :
    let q := num_odd_steps j n
    E j n = ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ q ↔
      V j n = List.replicate (j - q) false ++ List.replicate q true := by
  sorry

/-- The lower bound in Theorem 2.2 is reached iff `V_j(n) = ⟨1^q 0^{j-q}⟩`,
    i.e. `n ≡ (2/3)^q - 1 (mod 2^j)`. -/
theorem E_lower_bound_iff (j n : ℕ) (hj : 0 < j) (hn : 0 < n) :
    let q := num_odd_steps j n
    E j n = ((3 : ℚ) ^ q - 2 ^ q) / 2 ^ j ↔
      V j n = List.replicate q true ++ List.replicate (j - q) false := by
  sorry
