/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Algebra.Polynomial.Roots
import BertinPisot.SchurClass
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Smyth's theorem — coefficient bounds for real Schur functions (Bertin §3.5)

Bertin's **§3.5** (*Pisot and Salem Numbers*, [Ber92]) develops **Smyth's theorem**. This file opens
the section with **Lemma 3.5.1**, the basic coefficient inequalities for a Schur function `f ∈ 𝓜`
(`Complex.schurClass`, analytic and bounded by `1` on `D(0,1)`) whose Taylor coefficients are **real**,
`f(z) = Σₙ aₙ zⁿ` on `D(0,1)`.

The hypothesis is encoded as `f ∈ schurClass` together with a real sequence `a : ℕ → ℝ` and
`∀ z ∈ ball 0 1, HasSum (fun n => (aₙ : ℂ) · zⁿ) (f z)` (the power series represents `f` on the disk).

* i) `Complex.abs_coeff_zero_le_one_lemma_3_5_1` — `|a₀| ≤ 1` (**proved**: `a₀ = f(0)` and
  `|f(0)| ≤ 1` since `f ∈ 𝓜`).
* ii) `Complex.abs_coeff_le_one_sub_sq_lemma_3_5_1` — `|aₖ| ≤ 1 − a₀²` for every `k` (**cited**).
* iii) `Complex.coeff_two_mul_bounds_lemma_3_5_1` — the two-sided bound
  `−(1 − a₀² − aₖ²/(1+a₀)) ≤ a₂ₖ ≤ 1 − a₀² − aₖ²/(1−a₀)` for `k ≥ 1` (**cited**).

**Lemma 3.5.2** (`Complex.posSemidef_one_sub_sq_pm_lemma_3_5_2`, **proved**): under the same hypotheses,
for `k < l < 2k` the `2×2` matrices `I₂ − B² ± A` are positive Hermitian, where `A`, `B` are built from
consecutive coefficients. Fully formalised from Corollary 3.2.3 via three proved ingredients here:
`Complex.coeff_taylorSeries_eq` (`coeff = aₙ`), `Complex.exch_mul_toeplitz_apply` (the `Jₗ Fₗ` entries),
and the Schur-complement core `Complex.posSemidef_sub_mul_self_of_fromBlocks_one`
(`[P B; B I] ⪰ 0 → P − B² ⪰ 0`). Its only literature dependency is Corollary 3.2.2 (Schur's criterion),
inherited through Corollary 3.2.3.

**Theorem 3.5** (`Complex.smyth_theorem_3_5`, **cited**, Smyth [Smy71]): for a non-reciprocal monic
`P ∈ ℤ[z]` with `P(0) ≠ 0`, the product of the moduli of the roots outside the unit circle is at least
the smallest Pisot number `θ₀ = 1.3247…` (root of `x³ − x − 1`). The number-theoretic capstone of the
chapter; recorded as a `cited` axiom (its proof runs the §3.4–3.5 meromorphic/Schur machinery).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
  (§3.5, Lemmas 3.5.1–3.5.2, Theorem 3.5.)
* [Smy71] Smyth, C. J. *On the product of the conjugates outside the unit circle of an algebraic
  integer.* Bull. London Math. Soc. **3** (1971), 169–175. (Theorem 3.5 — Smyth's theorem.)
-/

open Metric Filter
open scoped ComplexOrder Topology NNReal ENNReal
open Matrix

namespace Complex

/-- **Lemma 3.5.1 i)** (Bertin). If `f ∈ 𝓜` has real Taylor coefficients `f(z) = Σ aₙ zⁿ` on `D(0,1)`,
then `|a₀| ≤ 1`.

**Proved.** At `z = 0` the power series collapses to its constant term, so `a₀ = f(0)`
(`HasSum.unique` against the single-term sum), and `|f(0)| ≤ 1` because `f ∈ 𝓜` is bounded by `1` on
the disk (`0 ∈ D(0,1)`). -/
@[category research solved, AMS 30, ref "Ber92", formal_uses schurClass]
theorem abs_coeff_zero_le_one_lemma_3_5_1 {f : ℂ → ℂ} (hf : f ∈ schurClass) {a : ℕ → ℝ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => (a n : ℂ) * z ^ n) (f z)) :
    |a 0| ≤ 1 := by
  have h0 : HasSum (fun n => (a n : ℂ) * (0 : ℂ) ^ n) (f 0) := hsum 0 (mem_ball_self one_pos)
  have hsingle : HasSum (fun n : ℕ => (a n : ℂ) * (0 : ℂ) ^ n) (a 0 : ℂ) := by
    simpa using hasSum_single (0 : ℕ) (f := fun n : ℕ => (a n : ℂ) * (0 : ℂ) ^ n)
      (fun b' hb' => by simp [zero_pow hb'])
  have hf0 : f 0 = (a 0 : ℂ) := h0.unique hsingle
  have hbound : ‖f 0‖ ≤ 1 := (mem_schurClass.mp hf).2 0 (mem_ball_self one_pos)
  simpa [hf0] using hbound

/-- **Lemma 3.5.1 ii)** (Bertin). With the hypotheses of i), `|aₖ| ≤ 1 − a₀²` for every `k ∈ ℕ`.

Recorded as a `cited` axiom (`ref "Ber92"`). This Schur coefficient estimate is **stronger** than the
Parseval/`H²` bound `|aₖ| ≤ √(1 − a₀²)` (from `Σ_{n≥1} |aₙ|² ≤ 1 − a₀²`). Bertin's proof passes to the
Schur step `φ = (f − a₀)/(1 − a₀ f) ∈ 𝓜` with `φ(0) = 0`, rewrites `f − a₀ = (1 − a₀²)·ψ` with
`ψ = φ/(1 + a₀ φ) ∈ 𝓜`, `ψ(0) = 0`, giving `aₖ = (1 − a₀²)·dₖ` where `|dₖ| ≤ 1` by the Cauchy
coefficient estimate. The ingredients (Schwarz/Cauchy/Möbius) exist in Mathlib but the assembly — in
particular the power-series identities for the Möbius transform `ψ` — is not carried out here. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses schurClass]
axiom abs_coeff_le_one_sub_sq_lemma_3_5_1 {f : ℂ → ℂ} (hf : f ∈ schurClass) {a : ℕ → ℝ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => (a n : ℂ) * z ^ n) (f z)) (k : ℕ) :
    |a k| ≤ 1 - (a 0) ^ 2

/-- **Lemma 3.5.1 iii)** (Bertin). With the hypotheses of i), for every `k ≥ 1`,
`−(1 − a₀² − aₖ²/(1 + a₀)) ≤ a₂ₖ ≤ 1 − a₀² − aₖ²/(1 − a₀)`.

Recorded as a `cited` axiom (`ref "Ber92"`). A refined **second-order** coefficient inequality: `a₂ₖ`
is pinned between bounds built from `a₀` and `aₖ` (a `2×2` Schur-positivity / real-coefficient
argument, sharpening ii). The divisions by `1 ± a₀` use Lean's junk value `x / 0 = 0` at `|a₀| = 1`,
the degenerate case where `f` is constant. Deeper than ii) and not formalised here. -/
@[category research solved, AMS 30, ref "Ber92", formal_uses schurClass]
axiom coeff_two_mul_bounds_lemma_3_5_1 {f : ℂ → ℂ} (hf : f ∈ schurClass) {a : ℕ → ℝ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => (a n : ℂ) * z ^ n) (f z)) (k : ℕ) (hk : 1 ≤ k) :
    -(1 - (a 0) ^ 2 - (a k) ^ 2 / (1 + a 0)) ≤ a (2 * k) ∧
      a (2 * k) ≤ 1 - (a 0) ^ 2 - (a k) ^ 2 / (1 - a 0)

/-! ### Lemma 3.5.2 — positivity of `I₂ − B² ± A` -/

/-- The Taylor coefficients of `f` recovered from a convergent power-series representation: if
`f(z) = Σ aₙ zⁿ` on `D(0,1)` then `coeff n (taylorSeries f) = aₙ`. (Built by exhibiting
`FormalMultilinearSeries.ofScalars ℂ (aₙ)` as a power series of `f` on a sub-ball — its radius is
positive since the `Σ aₙ zⁿ` is summable at `z = 3/4` — and reading off `iteratedDeriv` via
`HasFPowerSeriesOnBall.factorial_smul`.) -/
@[category API, AMS 30, ref "Ber92", formal_uses taylorSeries]
theorem coeff_taylorSeries_eq {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun m => (a m : ℂ) * z ^ m) (f z)) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries f) = (a n : ℂ) := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)) with hp
  have hmem34 : (3 / 4 : ℂ) ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; norm_num
  have hsummable : Summable (fun m => (a m : ℂ) * (3 / 4 : ℂ) ^ m) := (hsum (3 / 4) hmem34).summable
  have htend : Tendsto (fun m => ‖(a m : ℂ) * (3 / 4 : ℂ) ^ m‖) atTop (𝓝 0) := by
    simpa using hsummable.tendsto_atTop_zero.norm
  obtain ⟨M, hMub⟩ := htend.bddAbove_range
  have hrad : (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    apply FormalMultilinearSeries.le_radius_of_bound p M
    intro m
    have h1 : ‖p m‖ = |a m| := by
      rw [hp, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs]
    have hc : (↑(1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; norm_num
    rw [h1, hc]
    calc |a m| * ((1 : ℝ) / 2) ^ m
        ≤ |a m| * ((3 : ℝ) / 4) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (abs_nonneg _)
      _ = ‖(a m : ℂ) * (3 / 4 : ℂ) ^ m‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by norm_num, Complex.norm_real,
            Real.norm_eq_abs]; norm_num
      _ ≤ M := hMub (Set.mem_range_self m)
  have hball : HasFPowerSeriesOnBall f p 0 (↑(1 / 2 : ℝ≥0)) := by
    refine ⟨hrad, ENNReal.coe_pos.mpr (by norm_num), ?_⟩
    intro y hy
    rw [Metric.eball_coe, mem_ball, dist_zero_right] at hy
    have hy1 : y ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]
      have hc : (↑(1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; norm_num
      rw [hc] at hy; linarith
    rw [hp]
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add, mul_comm]
      using hsum y hy1
  have hfs := hball.factorial_smul 1 n
  rw [hp] at hfs
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] at hfs
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfs
  rw [taylorSeries, PowerSeries.coeff_mk, ← hfs, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)

/-- The entries of `Jₗ Fₗ` (`Jₗ = exchangeMatrix l`, `Fₗ = schurToeplitz F l`): `(J F)ᵢⱼ = a_{l−i−j}`
when `i + j ≤ l`, and `0` otherwise (the anti-diagonal `J` reflects the lower-triangular Toeplitz `F`
into an anti-lower-triangular layout). -/
@[category API, AMS 15 30, ref "Ber92", formal_uses exchangeMatrix schurToeplitz]
theorem exch_mul_toeplitz_apply (F : PowerSeries ℂ) (l : ℕ) (i j : Fin (l + 1)) :
    (exchangeMatrix l * schurToeplitz F l) i j
      = if (i : ℕ) + (j : ℕ) ≤ l then PowerSeries.coeff (l - (i : ℕ) - (j : ℕ)) F else 0 := by
  rw [Matrix.mul_apply]
  have hi : (i : ℕ) ≤ l := Nat.lt_succ_iff.mp i.isLt
  set b : Fin (l + 1) := ⟨l - (i : ℕ), by omega⟩ with hb
  have hbval : (b : ℕ) = l - (i : ℕ) := rfl
  rw [Fintype.sum_eq_single b]
  · have h1 : exchangeMatrix l i b = 1 := by
      simp only [exchangeMatrix, hbval]; rw [if_pos (by omega)]
    rw [h1, one_mul, schurToeplitz, hbval]
    by_cases hc : (j : ℕ) ≤ l - (i : ℕ)
    · rw [if_pos (by rw [Fin.le_def, hbval]; omega), if_pos (by omega)]
    · rw [if_neg (by rw [Fin.le_def, hbval]; omega), if_neg (by omega)]
  · intro x hx
    have hx0 : exchangeMatrix l i x = 0 := by
      simp only [exchangeMatrix]; rw [if_neg]
      intro hcon; apply hx; apply Fin.ext; rw [hbval]; omega
    rw [hx0, zero_mul]

/-- **Schur-complement positivity** (the linear-algebra core of Lemma 3.5.2, **proved**). For square
complex matrices `P, B` with `B` Hermitian (`Bᴴ = B`), if the block matrix `[ P  B ; B  I ]` is
positive semidefinite, then so is the **Schur complement** `P − B²` of its bottom-right identity block.

The proof is Bertin's congruence `(I −B; O I)(P B; B I)(I O; −B I) = (P − B² O; O I)`: with
`C = (I O; −B I)` one has `Cᴴ · [P B; B I] · C = [P − B² O; O I]`, positive semidefinite by
`PosSemidef.conjTranspose_mul_mul_same`, and `P − B²` is then its top-left principal block
(`PosSemidef.submatrix`). -/
@[category API, AMS 15, ref "Ber92"]
theorem posSemidef_sub_mul_self_of_fromBlocks_one {N : Type*} [Fintype N] [DecidableEq N]
    (P B : Matrix N N ℂ) (hB : Bᴴ = B) (h : (fromBlocks P B B 1).PosSemidef) :
    (P - B * B).PosSemidef := by
  set C : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
    fromBlocks (1 : Matrix N N ℂ) (0 : Matrix N N ℂ) (-B) (1 : Matrix N N ℂ) with hCdef
  have hcong := h.conjTranspose_mul_mul_same C
  have heq : Cᴴ * fromBlocks P B B 1 * C = fromBlocks (P - B * B) 0 0 1 := by
    rw [hCdef, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, hB,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.neg_mul,
      Matrix.mul_neg, add_zero, zero_add, neg_zero, add_neg_cancel, sub_eq_add_neg]
  rw [heq] at hcong
  have hsub := hcong.submatrix (Sum.inl : N → N ⊕ N)
  have hblk : (fromBlocks (P - B * B) (0 : Matrix N N ℂ) 0 1).submatrix
      (Sum.inl : N → N ⊕ N) Sum.inl = P - B * B := by
    ext i j; simp [Matrix.submatrix_apply]
  rwa [hblk] at hsub

/-- **Lemma 3.5.2** (Bertin). Keep the hypotheses of Lemma 3.5.1 (`f ∈ 𝓜`, real coefficients
`f(z) = Σ aₙ zⁿ`). For integers `k < l < 2k`, both `2×2` matrices `I₂ − B² + A` and `I₂ − B² − A` are
positive (Hermitian) — Bertin's `I₂ − B² + εA`, `ε = ±1` — where
`A = (aₗ aₖ; aₖ a₂ₖ₋ₗ)` and `B = (aₗ₋ₖ a₀; a₀ 0)`.

**Proof** (Bertin, fully formalised). By **Corollary 3.2.3**
(`posSemidef_one_pm_exchangeMatrix_schurToeplitz_of_real`, proved in `BertinPisot.SchurClass`) the
`(l+1)×(l+1)` matrices `I_{l+1} ± J_{l+1} F_l` are positive (real Taylor series, `hreal` from
`coeff_taylorSeries_eq`). Their principal submatrix on the indices `{0, l−k, k, l}` has the block form
`(I₂ ± A  B ; B  I₂)` — the `16`-entry computation `hJF`, via `exch_mul_toeplitz_apply`
(`(JF)_{ij} = a_{l−i−j}` for `i+j ≤ l`) and `coeff_taylorSeries_eq` (`coeff = aₙ`) — so by
`Matrix.PosSemidef.submatrix` it is positive, and the Schur-complement step
`posSemidef_sub_mul_self_of_fromBlocks_one` turns block positivity into `I₂ ± A − B²` positive. -/
@[category research solved, AMS 15 30, ref "Ber92",
  formal_uses schurClass coeff_taylorSeries_eq exch_mul_toeplitz_apply
    posSemidef_sub_mul_self_of_fromBlocks_one]
theorem posSemidef_one_sub_sq_pm_lemma_3_5_2 {f : ℂ → ℂ} (hf : f ∈ schurClass) {a : ℕ → ℝ}
    (hsum : ∀ z ∈ ball (0 : ℂ) 1, HasSum (fun n => (a n : ℂ) * z ^ n) (f z))
    {k l : ℕ} (hkl : k < l) (hl2k : l < 2 * k) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (!![(a (l - k) : ℂ), (a 0 : ℂ); (a 0 : ℂ), 0]) ^ 2
        + !![(a l : ℂ), (a k : ℂ); (a k : ℂ), (a (2 * k - l) : ℂ)]).PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - (!![(a (l - k) : ℂ), (a 0 : ℂ); (a 0 : ℂ), 0]) ^ 2
        - !![(a l : ℂ), (a k : ℂ); (a k : ℂ), (a (2 * k - l) : ℂ)]).PosSemidef := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![(a l : ℂ), (a k : ℂ); (a k : ℂ), (a (2 * k - l) : ℂ)] with hA
  set B : Matrix (Fin 2) (Fin 2) ℂ := !![(a (l - k) : ℂ), (a 0 : ℂ); (a 0 : ℂ), 0] with hBdef
  set e : Fin 2 ⊕ Fin 2 → Fin (l + 1) :=
    Sum.elim ![(⟨0, by omega⟩ : Fin (l + 1)), ⟨l - k, by omega⟩] ![⟨k, by omega⟩, ⟨l, by omega⟩]
    with he
  have hreal : ∀ n, (PowerSeries.coeff n (taylorSeries f)).im = 0 := fun n => by
    rw [coeff_taylorSeries_eq hsum]; exact Complex.ofReal_im _
  obtain ⟨hplus, hminus⟩ := posSemidef_one_pm_exchangeMatrix_schurToeplitz_of_real hf hreal l
  have he_inj : Function.Injective e := by
    rw [he]
    intro x y hxy
    rcases x with (x | x) <;> rcases y with (y | y) <;> fin_cases x <;> fin_cases y <;>
      first
      | rfl
      | (exfalso; have hv := congrArg Fin.val hxy;
         simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.mk_one,
           Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero] at hv; omega)
  have hJF : (exchangeMatrix l * schurToeplitz (taylorSeries f) l).submatrix e e
      = fromBlocks A B B 0 := by
    rw [he]
    ext r c
    rcases r with (r | r) <;> rcases c with (c | c) <;> fin_cases r <;> fin_cases c <;>
      simp only [hA, hBdef, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr, Fin.mk_zero,
        Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
        exch_mul_toeplitz_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply] <;>
      rw [coeff_taylorSeries_eq hsum] <;> split_ifs with h <;>
      first
        | rfl
        | exact congrArg (fun m => ((a m : ℝ) : ℂ)) (by omega)
        | (exfalso; omega)
  have hBh : Bᴴ = B := by
    rw [hBdef]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
  have h1sub : (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ).submatrix e e = 1 := by
    ext r c
    rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hrc : r = c
    · rw [hrc]; simp
    · rw [if_neg hrc, if_neg (fun h => hrc (he_inj h))]
  have hplus' : (fromBlocks (1 + A) B B 1).PosSemidef := by
    have h := hplus.submatrix e
    rw [show (1 + exchangeMatrix l * schurToeplitz (taylorSeries f) l).submatrix e e
        = (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ).submatrix e e
          + (exchangeMatrix l * schurToeplitz (taylorSeries f) l).submatrix e e from rfl,
      h1sub, hJF] at h
    rwa [show (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) + fromBlocks A B B 0
        = fromBlocks (1 + A) B B 1 from by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp] at h
  have hminus' : (fromBlocks (1 - A) (-B) (-B) 1).PosSemidef := by
    have h := hminus.submatrix e
    rw [show (1 - exchangeMatrix l * schurToeplitz (taylorSeries f) l).submatrix e e
        = (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) ℂ).submatrix e e
          - (exchangeMatrix l * schurToeplitz (taylorSeries f) l).submatrix e e from rfl,
      h1sub, hJF] at h
    rwa [show (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) - fromBlocks A B B 0
        = fromBlocks (1 - A) (-B) (-B) 1 from by
      ext i j
      rcases i with (i | i) <;> rcases j with (j | j) <;>
        simp [Matrix.sub_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]] at h
  refine ⟨?_, ?_⟩
  · have hp := posSemidef_sub_mul_self_of_fromBlocks_one (1 + A) B hBh hplus'
    rwa [show (1 : Matrix (Fin 2) (Fin 2) ℂ) - B ^ 2 + A = (1 + A) - B * B from by
      rw [pow_two]; abel]
  · have hBh' : (-B)ᴴ = -B := by rw [Matrix.conjTranspose_neg, hBh]
    have hm := posSemidef_sub_mul_self_of_fromBlocks_one (1 - A) (-B) hBh' hminus'
    rwa [show (1 : Matrix (Fin 2) (Fin 2) ℂ) - B ^ 2 - A = (1 - A) - (-B) * (-B) from by
      rw [pow_two, neg_mul_neg]; abel]

/-! ### Theorem 3.5 — Smyth's theorem -/

open Classical in
/-- **Theorem 3.5** (Smyth [Smy71]; Bertin [Ber92], §3.5). Let `P ∈ ℤ[z]` be **monic**, with
`P(0) ≠ 0`, and **non-reciprocal** (`P ≠ ± P*`, where `P* = P.reverse` is the reciprocal polynomial).
Then the product of the moduli of the roots `θᵢ` of `P` lying **outside** the closed unit disk is at
least the **smallest Pisot number** `θ₀ = 1.3247…` (the plastic number, the real root of
`x³ − x − 1 = 0`):  `∏_{|θᵢ| > 1} |θᵢ| ≥ θ₀`.

This is **Smyth's theorem** (C. J. Smyth, 1971), the capstone of §3.5 — the Mahler-measure lower bound
for non-reciprocal integer polynomials. Bertin's proof associates to `P` a function of `𝓜_∞` and pits
the Schur-coefficient inequalities of Lemmas 3.5.1–3.5.2 against the §3.4 meromorphic theory; recorded
here as a `cited` axiom (`ref "Ber92" "Smy71"`). `θ₀` is pinned by its defining cubic
(`θ₀³ − θ₀ − 1 = 0`, `θ₀ > 0` — the unique real root); the product runs over the root multiset of `P`
in `ℂ` (`P.map (Int.castRingHom ℂ)).roots`) keeping the roots of modulus `> 1`. -/
@[category research solved, AMS 11 12 30, ref "Ber92" "Smy71",
  formal_uses abs_coeff_zero_le_one_lemma_3_5_1 abs_coeff_le_one_sub_sq_lemma_3_5_1
    coeff_two_mul_bounds_lemma_3_5_1 posSemidef_one_sub_sq_pm_lemma_3_5_2]
axiom smyth_theorem_3_5 (P : Polynomial ℤ) (hmonic : P.Monic) (h0 : P.eval 0 ≠ 0)
    (hnonrecip : P ≠ P.reverse ∧ P ≠ -P.reverse)
    (θ₀ : ℝ) (hθ₀ : θ₀ ^ 3 - θ₀ - 1 = 0) (hθ₀pos : 0 < θ₀) :
    θ₀ ≤ (((P.map (Int.castRingHom ℂ)).roots.filter (fun θ => 1 < ‖θ‖)).map
      (fun θ => ‖θ‖)).prod

end Complex
