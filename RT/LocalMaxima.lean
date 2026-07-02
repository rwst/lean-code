/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.CRozLemma32
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Paradoxical sequences and circuit-shaped parity vectors (Rozier–Terracol, Appendix A)

A parity vector of the form `⟨1^q 0^{j-q}⟩` (`q` odd steps, each roughly tripling, followed by
`j - q` even steps, each halving) is the signature of a single excursion that climbs to a **local
maximum** at step `q` and then descends — Steiner's notion of a *circuit*.

**Lemma A.1** ([Roz25]).  There is no paradoxical sequence whose parity vector has the circuit form
`⟨1^q 0^{j-q}⟩` with `j ≥ q ≥ 1`.

## Proof outline
Write `T^j(n) = n + d` with `d ≥ 0`.  By Theorem 2.2 the circuit shape forces the correction term
to attain its lower bound, `E_j(n) = L_j(q) = (3^q - 2^q)/2^j` (`RT.E_lower_bound_iff`), so the
linear decomposition (`CC.linear_decomposition`) becomes the paper's equation (23):
`2^j · T^j(n) = 3^q · n + (3^q - 2^q)`.

* `d ≥ 1`: purely algebraic.  Paradoxicality gives `3^q < 2^j`, and with `n > 2` the equation is
  impossible (formalized here, no external input).
* `d = 0`: the sequence is a genuine *circuit* `T^j(n) = n`.  By **Steiner's theorem** ([Ste77]) the
  only Collatz circuit is the trivial cycle, so no circuit exists for `n > 2`.  This deep result
  (a linear-forms-in-logarithms estimate) is recorded as the cited axiom `no_nontrivial_circuit`.

## Contents
* `RT.no_nontrivial_circuit` — Steiner's circuit theorem ([Ste77]), a cited axiom.
* `RT.no_paradoxical_of_circuit_vector` — **Lemma A.1** ([Roz25]).

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Appendix A, Lemma A.1, eq. (23).
* [Ste77] Steiner, R. P. "A theorem on the Syracuse problem." *Proceedings of the 7th Manitoba
  Conference on Numerical Mathematics* (Winnipeg, 1977), 553–559. Utilitas Math., Winnipeg, 1978.
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241–252.
-/

open Classical

open CC

namespace RT

/-- **Steiner's circuit theorem** ([Ste77]).  A *circuit* of the Collatz map is a sequence whose
parity vector has the form `⟨1^q 0^{j-q}⟩` (`q` consecutive odd steps followed by even steps) and
which returns to its start, `T^j(n) = n`.  Steiner proved — via an effective linear-forms-in-two-
logarithms estimate for `|q log 3 - j log 2|` — that the only circuit is the trivial cycle.  Hence
for `n > 2` no circuit exists.

Recorded as a cited `axiom`: the transcendence input is not re-derived here. -/
@[category research solved, AMS 11 37, ref "Ste77", group "roz_lemma_a1"]
axiom no_nontrivial_circuit {j n : ℕ} (q : ℕ) (hn : 2 < n) (hq : 1 ≤ q) (hqj : q ≤ j)
    (hV : (V j n : List Bool) = List.replicate q true ++ List.replicate (j - q) false)
    (hcirc : T_iter j n = n) : False

/-- **Lemma A.1** ([Roz25], Appendix A).  There is no paradoxical sequence whose parity vector is of
the circuit form `⟨1^q 0^{j-q}⟩` with `j ≥ q ≥ 1` (and first term `n > 2`).

Writing the number of odd steps `q = num_odd_steps j n ≥ 1`, the hypothesis `hV` says the parity
vector `V j n` equals `⟨1^q 0^{j-q}⟩`.  By `E_lower_bound_iff` this pins the correction term to its
lower bound, turning the linear decomposition into equation (23)
`2^j · T^j(n) = 3^q · n + (3^q - 2^q)`.  If `T^j(n) > n` the equation is impossible for `n > 2`
under `3^q < 2^j` (paradoxicality); if `T^j(n) = n` it is a circuit, excluded by
`no_nontrivial_circuit` ([Ste77]). -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_lemma_a1"]
theorem no_paradoxical_of_circuit_vector (j n : ℕ) (hn : 2 < n)
    (h_para : IsParadoxical j n) (hq : 1 ≤ num_odd_steps j n)
    (hV : (V j n : List Bool) =
      List.replicate (num_odd_steps j n) true ++ List.replicate (j - num_odd_steps j n) false) :
    False := by
  set q := num_odd_steps j n with hqdef
  have hqj : q ≤ j := num_odd_steps_le j n
  have hj : 0 < j := by omega
  obtain ⟨h_ge, h_C⟩ := h_para
  -- Parity vector `⟨1^q 0^{j-q}⟩` ⟺ the correction attains its lower bound `L j q` (Thm 2.2).
  have hEL : E j n = L j q := (E_lower_bound_iff j n hj).mpr hV
  have h2j : (2 : ℚ) ^ j ≠ 0 := by positivity
  -- Hence the accumulated correction is exactly `Q_j(n) = 3^q - 2^q`.
  have hDQ : (decomposition_correction j n : ℚ) = (3 : ℚ) ^ q - 2 ^ q := by
    rw [E, L] at hEL
    field_simp at hEL
    linarith [hEL]
  have hDZ : (decomposition_correction j n : ℤ) = 3 ^ q - 2 ^ q := by exact_mod_cast hDQ
  -- Master equation (23) over `ℤ`: `2^j · T^j(n) = 3^q · n + (3^q - 2^q)`.
  have hlin := linear_decomposition j n
  have master : (2 : ℤ) ^ j * (T_iter j n) = 3 ^ q * n + (3 ^ q - 2 ^ q) := by
    have hcast : (2 : ℤ) ^ j * (T_iter j n) = 3 ^ q * n + (decomposition_correction j n : ℤ) := by
      exact_mod_cast hlin
    rw [hDZ] at hcast; exact hcast
  -- Paradoxicality `C_j(n) < 1` means `3^q < 2^j`.
  have hgap : (3 : ℤ) ^ q < 2 ^ j := by
    have hC' : (3 : ℚ) ^ q / 2 ^ j < 1 := by rw [C, ← hqdef] at h_C; exact h_C
    rw [div_lt_one (by positivity)] at hC'
    exact_mod_cast hC'
  have hTN : (n : ℤ) ≤ T_iter j n := by exact_mod_cast h_ge
  have hN3 : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have h2q : (2 : ℤ) ≤ 2 ^ q := by
    calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  rcases eq_or_lt_of_le hTN with hEq | hLt
  · -- `d = 0`: a circuit `T^j(n) = n`, excluded by Steiner's theorem.
    have hcirc : T_iter j n = n := by exact_mod_cast hEq.symm
    exact no_nontrivial_circuit q hn hq hqj hV hcirc
  · -- `d ≥ 1`: the algebraic contradiction (23) vs. `3^q < 2^j` and `n > 2`.
    have hTge : (n : ℤ) + 1 ≤ T_iter j n := hLt
    have hprod1 : (2 : ℤ) ^ j * n + 2 ^ j ≤ 2 ^ j * T_iter j n := by
      have h0 : (0 : ℤ) ≤ 2 ^ j := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hTge h0]
    have hprod2 : (3 : ℤ) ≤ 2 ^ j * n - 3 ^ q * n := by
      have hb : (1 : ℤ) ≤ 2 ^ j - 3 ^ q := by linarith [hgap]
      nlinarith [mul_le_mul hb hN3 (by norm_num : (0 : ℤ) ≤ 3)
        (by linarith : (0 : ℤ) ≤ 2 ^ j - 3 ^ q)]
    linarith [master, hprod1, hprod2, hgap, h2q]

end RT
