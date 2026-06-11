/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowDistribution
import BertinPisot.SetSTU
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorems 5.1.2 and 5.1.3 — mean-square / sup-norm criteria for `α ∈ U` (Bertin §5.1)

Bertin's **Theorem 5.1.2** (*Pisot and Salem Numbers*, [Ber92], §5.1): the `L²` companion of
Theorem 5.1.1. Where 5.1.1 assumes a *uniform* (sup-norm) smallness of the residues `‖λαⁿ‖`, here the
hypothesis is an *averaged, quadratic* smallness of the residual differences `εᵢ₊₁ - αεᵢ`.

Let `α > 1` and assume there is a real `λ ≥ 1/2` with
* **(4)** `(α + 1)² · Σ_{i=m}^{m+n} (εᵢ₊₁ - αεᵢ)² < ρ(n + 1)` for all `(m, n) ∈ ℕ²`, and
* **(5)** `ρ ≤ 1 / (e · [log(u₀² + 1/(α+1)³) + 2])`,

where `εₙ = ε(λαⁿ)` (`Bertin.AlphaPow.ε`), `u₀ = E(λ)` (`Bertin.AlphaPow.u … 0`, an integer `≥ 1`
since `λ ≥ 1/2`), and `e = exp 1`. Then `α ∈ U` (`Bertin.U`): `α` is an algebraic integer whose
remaining conjugates lie in the closed unit disk — a Pisot or Salem number.

**Status: cited** (the excerpt shows only the statement). The mechanism parallels 5.1.1 and rests on
the same (currently uncited-in-Mathlib) analytic core. Since `εᵢ₊₁ - αεᵢ = -(uᵢ₊₁ - αuᵢ)` (the
integer-recurrence residual, cf. `Bertin.AlphaPow.u_succ_sub_smul`), the mean-square bound (4)
controls a Gram/Hankel determinant of `(uₙ)` — a least-squares residual — forcing the Kronecker
determinants to vanish, hence `Σ uₙ Xⁿ` rational; rationality exhibits `1/α` as the only pole in the
unit disk, giving `α ∈ U`. The constant in (5) calibrates this quadratic estimate (the rôle played by
`2eα(α+1)(1+log λ)` in 5.1.1). A full formalization needs the `L²`/Gram-determinant rationality
bridge and the analytic pole structure (the cited `fatou_*` core of `AlphaPowTheorem`), so the
theorem is recorded as a cited axiom; supply Bertin's proof text to formalize it.

**Theorem 5.1.3** (`pisotSalem_theorem_5_1_3`, **proved**) is the sup-norm corollary: if some `λ ≥ 1`
makes `‖λαⁿ‖ ≤ 1/(e(α+1)²(2 + √log λ))` for all `n`, then `α ∈ U`. Its proof (formalized here in full)
*derives* the mean-square hypothesis (4) of 5.1.2 — `(α+1)²Σ(εᵢ₊₁-αεᵢ)² ≤ (n+1)/(e²(2+√log λ)²)`
from the termwise bound `|εₙ| ≤ 1/(e(α+1)²(2+√log λ))` via the triangle inequality — together with its
calibration (5), via `u₀² + 1/(α+1)³ < (λ + 1/2)²` (using `ε₀ < 1/8`) and
`log(u₀²+1/(α+1)³) + 2 ≤ 2(log λ + 2)`, then applies 5.1.2 with `ρ = 1/(2e(2 + log λ))`. So 5.1.3
rests, through 5.1.2, on the same cited analytic core.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.1, Thm 5.1.2.
  - [Pat69] Pathiaux, Martine. "Répartition modulo 1 de la suite `λαⁿ`."
    *Séminaire Delange-Pisot-Poitou. Théorie des nombres* 11.1 (1969), 1–6.
-/

namespace Bertin.AlphaPow

/-! ### Theorem 5.1.2 — `α ∈ U` from a mean-square bound on the residual differences -/

informal_result "generating-series-rationality-from-l2-bound"
  latex "An averaged (mean-square) smallness of the residual differences $\\varepsilon_{i+1}-\\alpha\\varepsilon_i$ — namely $(\\alpha+1)^2\\sum_{i=m}^{m+n}(\\varepsilon_{i+1}-\\alpha\\varepsilon_i)^2 < \\rho(n+1)$ uniformly in $(m,n)\\in\\mathbb{N}^2$, with $\\rho$ calibrated by the bound $(5)$ — forces the formal generating series $\\sum u_n X^n$ ($u_n=E(\\lambda\\alpha^n)$) to be rational. Since $\\varepsilon_{i+1}-\\alpha\\varepsilon_i=-(u_{i+1}-\\alpha u_i)$ is the integer-recurrence residual, the quadratic condition bounds a Gram/Hankel determinant of $(u_n)$ (a least-squares residual), driving the Kronecker determinants to zero; rationality then exhibits $1/\\alpha$ as the only pole in the open unit disk, so $\\alpha$ is an algebraic integer whose remaining conjugates lie in the closed unit disk, i.e. $\\alpha\\in U$. This is the $L^2$ companion of the sup-norm mechanism of Theorem 5.1.1."
  refs "Ber92"

/-- **Theorem 5.1.2** (Bertin). Let `α > 1` be real and suppose there is a real `λ ≥ 1/2` such that
`(α + 1)² · Σ_{i=m}^{m+n} (εᵢ₊₁ - αεᵢ)² < ρ(n + 1)` for all `(m, n) ∈ ℕ²` (the mean-square bound `(4)`,
with `εₙ = ε(λαⁿ)`), where `ρ` satisfies `ρ ≤ 1 / (e·[log(u₀² + 1/(α+1)³) + 2])` (the calibration
`(5)`, with `u₀ = E(λ)` and `e = exp 1`). Then `α ∈ U`: `α` is an algebraic integer all of whose
remaining conjugates have modulus `≤ 1` (a Pisot or Salem number).

Proof (cited; **the excerpt shows only the statement**). Bertin's argument runs parallel to 5.1.1 but
through an `L²`/least-squares estimate: as `εᵢ₊₁ - αεᵢ = -(uᵢ₊₁ - αuᵢ)`, the averaged bound `(4)`
bounds a Gram/Hankel determinant of the integer sequence `(uₙ)`, forcing its Kronecker determinants to
vanish, hence `Σ uₙ Xⁿ` is rational (Chapter 1 criteria,
`generating-series-rationality-from-l2-bound`); rationality exhibits `1/α` as the only pole in the
open unit disk, so `α` is an algebraic integer with remaining conjugates in the closed unit disk
(`α ∈ U`). The quadratic estimate is calibrated by `(5)`. Recorded as a cited axiom (the
`L²`-determinant bridge and analytic pole structure are not yet formalized). -/
@[category research solved, AMS 11, ref "Ber92" "Pat69",
  formal_uses ε u Bertin.U,
  informal_uses "generating-series-rationality-from-l2-bound"]
axiom pisotSalem_theorem_5_1_2 (α lam ρ : ℝ) (hα : 1 < α) (hlam : (1 : ℝ) / 2 ≤ lam)
    (h4 : ∀ m n : ℕ, (α + 1) ^ 2 * ∑ i ∈ Finset.Icc m (m + n),
        (ε lam α (i + 1) - α * ε lam α i) ^ 2 < ρ * ((n : ℝ) + 1))
    (h5 : ρ ≤ 1 / (Real.exp 1 * (Real.log ((u lam α 0 : ℝ) ^ 2 + 1 / (α + 1) ^ 3) + 2))) :
    α ∈ Bertin.U

/-! ### Theorem 5.1.3 — `α ∈ U` from a sup-norm bound, by reduction to 5.1.2 -/

/-- **Theorem 5.1.3** (Bertin). Let `α > 1` be real and suppose there is a real `λ ≥ 1` with
`‖λαⁿ‖ ≤ 1 / (e(α+1)²(2 + √log λ))` for every `n ∈ ℕ` (the bound `(11)`, `‖·‖ = distToNearestInt`,
`e = exp 1`). Then `α ∈ U`: `α` is an algebraic integer all of whose remaining conjugates have modulus
`≤ 1` (a Pisot or Salem number).

Proof (formalized in full, by reduction to Theorem 5.1.2). The sup-norm bound `(11)` gives
`|εₙ| ≤ 1/(e(α+1)²(2+√log λ))` for all `n`. The triangle inequality on
`εᵢ₊₁ - αεᵢ` and summation over the `n+1` indices `Icc m (m+n)` yield the mean-square bound
`(α+1)²·Σ (εᵢ₊₁-αεᵢ)² ≤ (n+1)/(e²(2+√log λ)²)`, which is `< ρ(n+1)` for `ρ = 1/(2e(2+log λ))` because
`2e(2+log λ) < e²(2+√log λ)²` (from `2 < e` and `log λ + 2 ≤ (2+√log λ)²`) — that is condition `(4)` of
5.1.2. The same `ρ` satisfies `(5)`: `ε₀ < 1/8` gives `0 < u₀ < λ + 1/8` and
`u₀² + 1/(α+1)³ < (λ+1/2)²`, whence `log(u₀²+1/(α+1)³) + 2 ≤ 2 log(λ+1/2) + 2 ≤ 2(log λ + 2)`
(the last via `λ + 1/2 ≤ eλ`). Theorem 5.1.2 then gives `α ∈ U`. -/
@[category research solved, AMS 11, ref "Ber92" "Pat69",
  formal_uses pisotSalem_theorem_5_1_2 ε u Bertin.U]
theorem pisotSalem_theorem_5_1_3 (α lam : ℝ) (hα : 1 < α) (hlam : 1 ≤ lam)
    (h11 : ∀ n : ℕ, distToNearestInt (lam * α ^ n) ≤
      1 / (Real.exp 1 * (α + 1) ^ 2 * (2 + Real.sqrt (Real.log lam)))) :
    α ∈ Bertin.U := by
  set s := Real.sqrt (Real.log lam) with hs
  have hεB : ∀ n : ℕ, |ε lam α n| ≤ 1 / (Real.exp 1 * (α + 1) ^ 2 * (2 + s)) := by
    intro n; rw [← distToNearestInt_eq_abs_ε]; exact h11 n
  refine pisotSalem_theorem_5_1_2 α lam (1 / (2 * Real.exp 1 * (2 + Real.log lam)))
    hα (by linarith) ?_ ?_
  · -- Condition (4): the mean-square bound, from the termwise bound via the triangle inequality.
    intro m n
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have he2 : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero); linarith
    have hα1 : 0 < α + 1 := by linarith
    have hL0 : 0 ≤ Real.log lam := Real.log_nonneg hlam
    have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    have hssq : s ^ 2 = Real.log lam := by rw [hs]; exact Real.sq_sqrt hL0
    set B := 1 / (Real.exp 1 * (α + 1) ^ 2 * (2 + s)) with hB
    have hterm : ∀ i, (ε lam α (i + 1) - α * ε lam α i) ^ 2 ≤ ((1 + α) * B) ^ 2 := by
      intro i
      have hb : |ε lam α (i + 1) - α * ε lam α i| ≤ (1 + α) * B := by
        calc |ε lam α (i + 1) - α * ε lam α i|
            ≤ |ε lam α (i + 1) - 0| + |0 - α * ε lam α i| := abs_sub_le _ _ _
          _ = |ε lam α (i + 1)| + α * |ε lam α i| := by
              rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos (by linarith : (0:ℝ) < α)]
          _ ≤ B + α * B := by have h1 := hεB (i + 1); have h2 := hεB i; gcongr
          _ = (1 + α) * B := by ring
      calc (ε lam α (i + 1) - α * ε lam α i) ^ 2
          = |ε lam α (i + 1) - α * ε lam α i| ^ 2 := (sq_abs _).symm
        _ ≤ ((1 + α) * B) ^ 2 := by gcongr
    have hsum : ∑ i ∈ Finset.Icc m (m + n), (ε lam α (i + 1) - α * ε lam α i) ^ 2
        ≤ ((n : ℝ) + 1) * ((1 + α) * B) ^ 2 := by
      calc ∑ i ∈ Finset.Icc m (m + n), (ε lam α (i + 1) - α * ε lam α i) ^ 2
          ≤ ∑ _i ∈ Finset.Icc m (m + n), ((1 + α) * B) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = (Finset.Icc m (m + n)).card • ((1 + α) * B) ^ 2 := Finset.sum_const _
        _ = ((n : ℝ) + 1) * ((1 + α) * B) ^ 2 := by
            rw [Nat.card_Icc, nsmul_eq_mul]
            have : (m + n + 1 - m : ℕ) = n + 1 := by omega
            rw [this]; push_cast; ring
    have hval : (α + 1) ^ 2 * (((n : ℝ) + 1) * ((1 + α) * B) ^ 2)
        = ((n : ℝ) + 1) / (Real.exp 1 ^ 2 * (2 + s) ^ 2) := by rw [hB]; field_simp; ring
    have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hkey : 2 * Real.exp 1 * (2 + Real.log lam) < Real.exp 1 ^ 2 * (2 + s) ^ 2 := by
      nlinarith [he2, hL0, hs0, hssq, mul_pos he (show (0:ℝ) < Real.exp 1 - 1 by linarith),
        mul_nonneg (mul_nonneg he.le he.le) hs0,
        mul_nonneg (mul_nonneg hL0 he.le) (show (0:ℝ) ≤ Real.exp 1 - 2 by linarith)]
    have hlt : ((n : ℝ) + 1) / (Real.exp 1 ^ 2 * (2 + s) ^ 2)
        < 1 / (2 * Real.exp 1 * (2 + Real.log lam)) * ((n : ℝ) + 1) := by
      rw [one_div_mul_eq_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      exact mul_lt_mul_of_pos_left hkey hn1
    calc (α + 1) ^ 2 * ∑ i ∈ Finset.Icc m (m + n), (ε lam α (i + 1) - α * ε lam α i) ^ 2
        ≤ (α + 1) ^ 2 * (((n : ℝ) + 1) * ((1 + α) * B) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((n : ℝ) + 1) / (Real.exp 1 ^ 2 * (2 + s) ^ 2) := hval
      _ < _ := hlt
  · -- Condition (5): the calibration, via `u₀² + 1/(α+1)³ < (λ+1/2)²`.
    have hdecomp : lam = (u lam α 0 : ℝ) + ε lam α 0 := by
      have h := self_eq_u_add_ε lam α 0; simpa using h
    have hU0int : ∃ k : ℤ, (u lam α 0 : ℝ) = (k : ℝ) := ⟨u lam α 0, rfl⟩
    set U0 := (u lam α 0 : ℝ) with hU0def
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have he2 : 2 < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero); linarith
    have hα1 : 0 < α + 1 := by linarith
    have hL0 : 0 ≤ Real.log lam := Real.log_nonneg hlam
    have hlampos : 0 < lam := by linarith
    have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
    have h4 : (4:ℝ) ≤ (α + 1) ^ 2 := by nlinarith [hα]
    have hstep : (8:ℝ) ≤ Real.exp 1 * (α + 1) ^ 2 := by
      nlinarith [h4, mul_nonneg (show (0:ℝ) ≤ Real.exp 1 - 2 by linarith) (sq_nonneg (α + 1))]
    have hden8 : 8 < Real.exp 1 * (α + 1) ^ 2 * (2 + s) := by
      nlinarith [hstep, hs0, mul_nonneg (show (0:ℝ) ≤ Real.exp 1 * (α + 1) ^ 2 by positivity) hs0]
    have hB18 : 1 / (Real.exp 1 * (α + 1) ^ 2 * (2 + s)) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hε0' : |ε lam α 0| < 1 / 8 := lt_of_le_of_lt (hεB 0) hB18
    rw [abs_lt] at hε0'
    obtain ⟨hlo, hhi⟩ := hε0'
    have hU0eq : U0 = lam - ε lam α 0 := by linarith [hdecomp]
    have hU0pos : 0 < U0 := by rw [hU0eq]; linarith
    have hU0lt : U0 < lam + 1 / 8 := by rw [hU0eq]; linarith
    have hU0ge1 : (1:ℝ) ≤ U0 := by
      obtain ⟨k, hk⟩ := hU0int
      have hkpos : 0 < k := by rw [hk] at hU0pos; exact_mod_cast hU0pos
      rw [hk]; have : (1:ℤ) ≤ k := by omega
      exact_mod_cast this
    have hcube : (8:ℝ) < (α + 1) ^ 3 := by
      nlinarith [mul_pos (show (0:ℝ) < (α + 1) - 2 by linarith)
        (show (0:ℝ) < (α + 1) ^ 2 + 2 * (α + 1) + 4 by positivity)]
    have hinv8 : 1 / (α + 1) ^ 3 < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hUsq : U0 ^ 2 < (lam + 1 / 8) ^ 2 := by nlinarith [hU0pos, hU0lt]
    have hstep4 : U0 ^ 2 + 1 / (α + 1) ^ 3 < (lam + 1 / 2) ^ 2 := by nlinarith [hUsq, hinv8, hlam]
    have hargpos : 0 < U0 ^ 2 + 1 / (α + 1) ^ 3 := by positivity
    have hlamhalf : 0 < lam + 1 / 2 := by linarith
    have hD1 : Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) ≤ 2 * Real.log (lam + 1 / 2) := by
      calc Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) ≤ Real.log ((lam + 1 / 2) ^ 2) :=
            Real.log_le_log hargpos hstep4.le
        _ = 2 * Real.log (lam + 1 / 2) := by rw [Real.log_pow]; push_cast; ring
    have hle_elam : lam + 1 / 2 ≤ Real.exp 1 * lam := by
      nlinarith [he2, hlam, mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ Real.exp 1 - 1 by linarith)
        (show (0:ℝ) ≤ lam by linarith)]
    have hD2 : Real.log (lam + 1 / 2) ≤ 1 + Real.log lam := by
      calc Real.log (lam + 1 / 2) ≤ Real.log (Real.exp 1 * lam) :=
            Real.log_le_log hlamhalf hle_elam
        _ = 1 + Real.log lam := by rw [Real.log_mul he.ne' hlampos.ne', Real.log_exp]
    have hDle : Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) + 2 ≤ 2 * (2 + Real.log lam) := by
      have := le_trans hD1
        (show 2 * Real.log (lam + 1 / 2) ≤ 2 * (1 + Real.log lam) by linarith)
      linarith
    have hDpos : 0 < Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) + 2 := by
      have h1 : (1:ℝ) ≤ U0 ^ 2 + 1 / (α + 1) ^ 3 := by
        nlinarith [hU0ge1, show (0:ℝ) ≤ 1 / (α + 1) ^ 3 by positivity]
      have : 0 ≤ Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) := Real.log_nonneg h1
      linarith
    have hab : Real.exp 1 * (Real.log (U0 ^ 2 + 1 / (α + 1) ^ 3) + 2)
        ≤ 2 * Real.exp 1 * (2 + Real.log lam) := by
      nlinarith [mul_le_mul_of_nonneg_left hDle he.le]
    exact one_div_le_one_div_of_le (mul_pos he hDpos) hab

end Bertin.AlphaPow
