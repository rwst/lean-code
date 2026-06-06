/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.RingTheory.PowerSeries.Rationality
import ForMathlib.Analysis.InnerProductSpace.Hadamard
import BertinPisot.NevanlinnaFactorization
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# A rationality criterion via block-`ℓ²` coefficient decay (Bertin §1.2, Theorem 1.2.2)

This file records Bertin's **Theorem 1.2.2** (Bertin, *Pisot and Salem Numbers*, §1.2, "Criteria of
rationality in ℂ"): a meromorphic `f = s/t` on `D(0,1)` with integer Taylor coefficients, whose
numerator/denominator coefficients have *doubling-block* `ℓ²` decay at admissible rates `(α, β)`, is
rational. It is stated as the capstone `theorem`, with the three technical lemmas it rests on
(Bertin's **Lemmas 1.2.3, 1.2.4, 1.2.5**) recorded as `private` helpers above it.

## Supporting lemmas

* `window_sum_le_eight_delta_sum` — **Lemma 1.2.3**: a doubling-block covering estimate. With
  `S(m) = ∑_{i=m}^{2m-1} yᵢ` and `δₙ = sup_{m ≥ n} S(m)` (and `δ₀ = max(y₀, δ₁)`), the windowed double
  sum over a strictly increasing `(i₀, …, iₛ)` obeys `∑_{h≤s} ∑_{m≤s} y_{iₕ+m} ≤ 8 ∑_{j≤s} δⱼ`.
* `blockNormSq_littleO_asymptotics` — **Lemma 1.2.4**: from `∑_{m=n}^{2n-1} |vₘ|² = o(n^{-γ})`, three
  asymptotic estimates for the partial sums follow (parts i–iii). Its `ρᵢ = sup_{n≥i} ∑ |vₕ|²` is
  precisely Lemma 1.2.3's `δ` for `yₙ = |vₙ|²`, so the two lemmas chain.
* `norm_det_lt_one_of_sum_normSq_lt` — **Lemma 1.2.5**: a square matrix `X` of order `n+1` with
  `∑_{i,j} |x_{i,j}|² < n+1` has `|det X| < 1`. This is Hadamard's inequality
  (`OrthonormalBasis.norm_det_le_prod_norm`, in `ForMathlib`) plus AM–GM.

## Status

* **Lemma 1.2.5** (Hadamard/AM–GM estimate) is **proved**.
* **Lemma 1.2.4** is **fully proved** (all of parts (i)–(iii), both `γ ≷ 1` regimes): part **(i)**
  (`part_i`); **(ii)** via `part_ii_ge` (`γ > 1`, Cauchy–Schwarz) and `part_ii_lt` (`γ < 1`, dyadic
  Cauchy–Schwarz `ℓ¹`-block bound summed with geometric weights `s = 2^{(1-γ)/2} > 1` over levels up
  to `Nat.log 2 r`, then squared); **(iii)** via `part_iii_ge` (`γ > 1`, supremum bound + `p`-series)
  and `part_iii_lt` (`γ < 1`, `ρᵢ = o(i^{-γ})` + `psum_le` + ε-summation). Reusable helpers:
  `sum_Ico_one_two_pow` (dyadic grouping), `exists_global_bound` (globalising the `o`-bound),
  `exists_block_geom_bound` (geometric block decay), `partialSum_bounded` (dyadic→bounded sums),
  `psum_le` (`p`-series bound via integral comparison), `cast_two_pow_rpow`, `block_l1_sq_le`.
* **Lemma 1.2.3** (doubling-block covering count) is **proved** (constant `6 ≤ 8`), via the helpers
  `sum_dilate_le`, `sum_Ico_anchored`, `window_cover`, `cover_sum_le`, `window_double_sum_tail_le`.
* **Theorem 1.2.2** is **proved**. Case `α, β > 0` routes through Theorem 1.2.1 (`s, t ∈ H²` ⟹ bounded
  characteristic). Case `{α=0<1<β} ∪ {1<α, β=0}` is the multiplier-determinant argument, assembled
  from Lemmas 1.2.3/1.2.4/1.2.5, the Kronecker criterion, and three cited `[Ber92]` axioms for the
  deep analytic/algebraic inputs not in Mathlib: `uvSetup` (Bertin's Lemma 1.1.6 determinant
  identity, with the `t₀ = 1` normalisation), `uvMatrix_normSq_le` (the Parseval block majoration),
  and `hasBoundedCharacteristic_of_quotient_summable` (the Hardy-quotient bridge for case i).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open Asymptotics Filter Topology

/-! ### Supporting lemmas for Lemma 1.2.3

The proof of Lemma 1.2.3 below follows Bertin's doubling-block covering idea but uses a streamlined
accounting (the explicit `Γ`-regrouping of Bertin's text is replaced by an order-swap plus a discrete
"dilation" estimate), yielding the constant `6 ≤ 8`. The pieces are:

* `sum_dilate_le` — a discrete dilation/averaging bound: `c · ∑_{h<H} δ(c(h+1)) ≤ ∑_{j<cH} δ(j+1)`
  for antitone `δ` (each `δ(c(h+1))` is dominated by the `c`-block of `δ` ending at `c(h+1)`).
* `sum_Ico_anchored` — the doubling blocks `[2ᵗa, 2ᵗ⁺¹a)`, `t ≤ P`, tile the interval
  `[a, 2^(P+1)·a)`.
* `window_cover` — a length-`(s+1)` window `[a, a+s]` (with `a ≥ 1`) is covered by the doubling
  blocks anchored at `a` up to scale `P = log₂((a+s)/a)`, so its `y`-sum is `≤ ∑_{t≤P} δ(2ᵗa)`.
* `cover_sum_le` — that cover sum is itself `≤ ∑_{j≤s} δⱼ` (since the scales `2ᵗa ≥ t` and `P ≤ s`).
* `window_double_sum_tail_le` — the `h ≥ 1` part of the double sum, bounded by `4 ∑_{j≤s} δⱼ` via
  `window_cover`, an order-swap, and `sum_dilate_le` summed geometrically (`∑ 2⁻ᵗ = 2`). -/

/-- Discrete dilation bound: for antitone `δ`, `c · ∑_{h<H} δ(c(h+1)) ≤ ∑_{j<cH} δ(j+1)`. -/
private lemma sum_dilate_le {δ : ℕ → ℝ} (hδanti : Antitone δ) {c : ℕ} (H : ℕ) :
    (c : ℝ) * ∑ h ∈ Finset.range H, δ (c * (h + 1)) ≤ ∑ j ∈ Finset.range (c * H), δ (j + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hle : c * H ≤ c * (H + 1) := by gcongr; omega
    have key : (c : ℝ) * δ (c * (H + 1)) ≤ ∑ j ∈ Finset.Ico (c * H) (c * (H + 1)), δ (j + 1) := by
      have hcard : (Finset.Ico (c * H) (c * (H + 1))).card = c := by
        rw [Nat.card_Ico, Nat.mul_succ]; omega
      have hb : ∀ j ∈ Finset.Ico (c * H) (c * (H + 1)), δ (c * (H + 1)) ≤ δ (j + 1) := by
        intro j hj; rw [Finset.mem_Ico] at hj; exact hδanti (by omega)
      have := Finset.card_nsmul_le_sum _ _ _ hb
      rw [hcard, nsmul_eq_mul] at this; exact this
    have hsplitR : ∑ j ∈ Finset.range (c * (H + 1)), δ (j + 1)
        = (∑ j ∈ Finset.range (c * H), δ (j + 1))
          + ∑ j ∈ Finset.Ico (c * H) (c * (H + 1)), δ (j + 1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun j => δ (j + 1)) (Nat.zero_le _) hle]
    rw [hsplitR]; exact add_le_add ih key

/-- The doubling blocks `[2ᵗa, 2ᵗ⁺¹a)`, `t = 0, …, P`, tile `[a, 2^(P+1)·a)`. -/
private lemma sum_Ico_anchored (y : ℕ → ℝ) (a P : ℕ) :
    ∑ i ∈ Finset.Ico a (2 ^ (P + 1) * a), y i
      = ∑ t ∈ Finset.range (P + 1), ∑ i ∈ Finset.Ico (2 ^ t * a) (2 ^ (t + 1) * a), y i := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ← ih]
    refine (Finset.sum_Ico_consecutive y ?_ ?_).symm
    · exact Nat.le_mul_of_pos_left a (by positivity)
    · gcongr <;> omega

/-- A length-`(s+1)` window `[a, a+s]` (with `a ≥ 1`) is covered by the doubling blocks anchored at
`a`, giving `∑_{m≤s} y(a+m) ≤ ∑_{t≤P} δ(2ᵗa)` with `P = log₂((a+s)/a)`. -/
private lemma window_cover {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) {δ : ℕ → ℝ}
    (hδub : ∀ n m : ℕ, n ≤ m → (∑ i ∈ Finset.Ico m (2 * m), y i) ≤ δ n)
    {a s : ℕ} (ha : 1 ≤ a) :
    ∑ m ∈ Finset.range (s + 1), y (a + m)
      ≤ ∑ t ∈ Finset.range (Nat.log 2 ((a + s) / a) + 1), δ (2 ^ t * a) := by
  set P := Nat.log 2 ((a + s) / a) with hP
  have hlog : (a + s) / a < 2 ^ (P + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hdiv : a + s < ((a + s) / a + 1) * a := by
    have h := Nat.div_add_mod (a + s) a
    have hmod : (a + s) % a < a := Nat.mod_lt _ ha
    rw [mul_comm a ((a + s) / a)] at h; rw [add_mul, one_mul]; omega
  have hmul : ((a + s) / a + 1) * a ≤ 2 ^ (P + 1) * a := by gcongr; omega
  have hcover : a + s + 1 ≤ 2 ^ (P + 1) * a := by omega
  calc ∑ m ∈ Finset.range (s + 1), y (a + m)
      = ∑ i ∈ Finset.Ico a (a + s + 1), y i := by
        rw [Finset.sum_Ico_eq_sum_range, show a + s + 1 - a = s + 1 from by omega]
    _ ≤ ∑ i ∈ Finset.Ico a (2 ^ (P + 1) * a), y i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hcover) (fun i _ _ => hy i)
    _ = ∑ t ∈ Finset.range (P + 1), ∑ i ∈ Finset.Ico (2 ^ t * a) (2 ^ (t + 1) * a), y i :=
        sum_Ico_anchored y a P
    _ ≤ ∑ t ∈ Finset.range (P + 1), δ (2 ^ t * a) := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        have h := hδub (2 ^ t * a) (2 ^ t * a) (le_refl _)
        have he : 2 * (2 ^ t * a) = 2 ^ (t + 1) * a := by rw [pow_succ]; ring
        rwa [he] at h

/-- The anchored cover sum is dominated by `∑_{j≤s} δⱼ` (since the scales `2ᵗa ≥ t` and `P ≤ s`). -/
private lemma cover_sum_le {δ : ℕ → ℝ} (hδanti : Antitone δ) (hδnn : ∀ n, 0 ≤ δ n)
    {a s : ℕ} (ha : 1 ≤ a) :
    ∑ t ∈ Finset.range (Nat.log 2 ((a + s) / a) + 1), δ (2 ^ t * a)
      ≤ ∑ j ∈ Finset.range (s + 1), δ j := by
  set P := Nat.log 2 ((a + s) / a) with hP
  have hPs : P ≤ s := by
    have h1 : 2 ^ P ≤ (a + s) / a := Nat.pow_log_le_self 2 (by
      have : 1 ≤ (a + s) / a := (Nat.one_le_div_iff (by omega)).2 (by omega)
      omega)
    have h2 : (a + s) / a ≤ s + 1 := by
      rw [Nat.add_comm a s, Nat.add_div_right s (by omega : 0 < a)]
      have : s / a ≤ s := Nat.div_le_self s a
      omega
    have h3 : P < 2 ^ P := Nat.lt_two_pow_self
    omega
  calc ∑ t ∈ Finset.range (P + 1), δ (2 ^ t * a)
      ≤ ∑ t ∈ Finset.range (P + 1), δ t := by
        apply Finset.sum_le_sum; intro t _; apply hδanti
        have h1 : t ≤ 2 ^ t := Nat.lt_two_pow_self.le
        have h2 : (2 : ℕ) ^ t ≤ 2 ^ t * a := le_mul_of_one_le_right (Nat.zero_le _) ha
        omega
    _ ≤ ∑ j ∈ Finset.range (s + 1), δ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht; rw [Finset.mem_range] at ht ⊢; omega
        · intro j _ _; exact hδnn _

/-- The `h ≥ 1` part of Bertin's windowed double sum, controlled by `4 ∑_{j≤s} δⱼ`. Each window
`[idx(i+1), idx(i+1)+s]` is covered (`window_cover`), the cover index is shifted down to `i+1`
(`idx(i+1) ≥ i+1`, antitone), the order of summation is swapped, and the dilation bound
`sum_dilate_le` is summed geometrically (`∑ₜ 2⁻ᵗ = 2`). -/
private lemma window_double_sum_tail_le {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) {δ : ℕ → ℝ}
    (hδub : ∀ n m : ℕ, n ≤ m → (∑ i ∈ Finset.Ico m (2 * m), y i) ≤ δ n)
    (hδanti : Antitone δ) (hδnn : ∀ n, 0 ≤ δ n)
    {s : ℕ} {idx : ℕ → ℕ} (hidx : StrictMono idx) :
    ∑ i ∈ Finset.range s, (∑ m ∈ Finset.range (s + 1), y (idx (i + 1) + m))
      ≤ 4 * ∑ j ∈ Finset.range (s + 1), δ j := by
  set B := ∑ j ∈ Finset.range (2 * s), δ (j + 1) with hB
  have per_h : ∀ i ∈ Finset.range s,
      (∑ m ∈ Finset.range (s + 1), y (idx (i + 1) + m))
        ≤ ∑ t ∈ Finset.range (2 * s),
            (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0) := by
    intro i hi
    have hile : i + 1 ≤ idx (i + 1) := by have := hidx.id_le (i + 1); simpa using this
    have his : i + 1 ≤ s := Finset.mem_range.1 hi
    have hipos : 1 ≤ idx (i + 1) := le_trans (by omega) hile
    have hwc := window_cover hy hδub (a := idx (i + 1)) (s := s) hipos
    set a := idx (i + 1) with ha
    set P := Nat.log 2 ((a + s) / a) with hP
    have e1 : 2 ^ P * a ≤ a + s := by
      have hpow : 2 ^ P ≤ (a + s) / a := Nat.pow_log_le_self 2 (by
        have : 1 ≤ (a + s) / a := (Nat.one_le_div_iff (by omega)).2 (by omega)
        omega)
      calc 2 ^ P * a ≤ ((a + s) / a) * a := by gcongr
        _ ≤ a + s := Nat.div_mul_le_self (a + s) a
    have hcharge : 2 ^ P * (i + 1) ≤ 2 * s := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hile
      have hdd : d ≤ 2 ^ P * d := Nat.le_mul_of_pos_left d (by positivity)
      rw [hd, Nat.mul_add] at e1; omega
    have hcharge_t : ∀ t ∈ Finset.range (P + 1), 2 ^ t * (i + 1) ≤ 2 * s := by
      intro t ht
      have htP : t ≤ P := Nat.le_of_lt_succ (Finset.mem_range.1 ht)
      have h2 : 2 ^ t * (i + 1) ≤ 2 ^ P * (i + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) htP) (le_refl _)
      exact le_trans h2 hcharge
    calc (∑ m ∈ Finset.range (s + 1), y (a + m))
        ≤ ∑ t ∈ Finset.range (P + 1), δ (2 ^ t * a) := hwc
      _ ≤ ∑ t ∈ Finset.range (P + 1), δ (2 ^ t * (i + 1)) :=
          Finset.sum_le_sum (fun t _ => hδanti (by gcongr))
      _ = ∑ t ∈ Finset.range (P + 1),
            (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0) :=
          Finset.sum_congr rfl (fun t ht => (if_pos (hcharge_t t ht)).symm)
      _ ≤ ∑ t ∈ Finset.range (2 * s),
            (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro t ht
            rw [Finset.mem_range] at ht ⊢
            have hP2 : 2 ^ P ≤ 2 * s := by
              calc 2 ^ P = 2 ^ P * 1 := (mul_one _).symm
                _ ≤ 2 ^ P * (i + 1) := by gcongr; omega
                _ ≤ 2 * s := hcharge
            have hPlt : P < 2 ^ P := Nat.lt_two_pow_self
            omega
          · intro t _ _; split_ifs; exacts [hδnn _, le_refl 0]
  have per_t : ∀ t : ℕ,
      (∑ i ∈ Finset.range s, (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0))
        ≤ B / (2 : ℝ) ^ t := by
    intro t
    set H := (2 * s) / 2 ^ t with hH
    have hsub : (Finset.range s).filter (fun i => 2 ^ t * (i + 1) ≤ 2 * s) ⊆ Finset.range H := by
      intro i hi; rw [Finset.mem_filter] at hi; rw [Finset.mem_range]
      have : i + 1 ≤ H := (Nat.le_div_iff_mul_le (by positivity)).2 (by rw [mul_comm]; exact hi.2)
      omega
    have ha2 : (∑ i ∈ Finset.range s, (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0))
          ≤ ∑ i ∈ Finset.range H, δ (2 ^ t * (i + 1)) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hδnn _)
    have hle2 : 2 ^ t * H ≤ 2 * s := by rw [hH, mul_comm]; exact Nat.div_mul_le_self (2 * s) (2 ^ t)
    have hb2 : (2 : ℝ) ^ t * ∑ i ∈ Finset.range H, δ (2 ^ t * (i + 1)) ≤ B := by
      have hdil := sum_dilate_le hδanti (c := 2 ^ t) (H := H)
      have hsub2set : Finset.range (2 ^ t * H) ⊆ Finset.range (2 * s) := by
        intro j hj; rw [Finset.mem_range] at hj ⊢; omega
      have hsub2 : ∑ j ∈ Finset.range (2 ^ t * H), δ (j + 1) ≤ B :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2set (fun j _ _ => hδnn _)
      push_cast at hdil; linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ t)]
    calc (∑ i ∈ Finset.range s, (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0)) * 2 ^ t
        ≤ (∑ i ∈ Finset.range H, δ (2 ^ t * (i + 1))) * 2 ^ t :=
          mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ = 2 ^ t * ∑ i ∈ Finset.range H, δ (2 ^ t * (i + 1)) := by ring
      _ ≤ B := hb2
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => hδnn _)
  have hBsplit : ∑ j ∈ Finset.range (2 * s), δ (j + 1)
      = (∑ j ∈ Finset.range s, δ (j + 1)) + ∑ j ∈ Finset.range s, δ (s + j + 1) := by
    rw [two_mul, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun j => δ (j + 1)) (Nat.zero_le s) (Nat.le_add_right s s)]
    rw [← Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range, show s + s - s = s from by omega]
  calc ∑ i ∈ Finset.range s, (∑ m ∈ Finset.range (s + 1), y (idx (i + 1) + m))
      ≤ ∑ i ∈ Finset.range s, ∑ t ∈ Finset.range (2 * s),
          (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0) := Finset.sum_le_sum per_h
    _ = ∑ t ∈ Finset.range (2 * s), ∑ i ∈ Finset.range s,
          (if 2 ^ t * (i + 1) ≤ 2 * s then δ (2 ^ t * (i + 1)) else 0) := Finset.sum_comm
    _ ≤ ∑ t ∈ Finset.range (2 * s), B / (2 : ℝ) ^ t := Finset.sum_le_sum (fun t _ => per_t t)
    _ = B * ∑ t ∈ Finset.range (2 * s), (1 / 2 : ℝ) ^ t := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [one_div, inv_pow, div_eq_mul_inv]
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hB0
    _ ≤ 4 * ∑ j ∈ Finset.range (s + 1), δ j := by
        have hBle : B ≤ 2 * ∑ j ∈ Finset.range (s + 1), δ j := by
          rw [hB, hBsplit, two_mul]
          apply add_le_add
          · rw [Finset.sum_range_succ']; linarith [hδnn 0]
          · refine le_trans (Finset.sum_le_sum (fun j _ => hδanti (by omega : j + 1 ≤ s + j + 1))) ?_
            rw [Finset.sum_range_succ']; linarith [hδnn 0]
        linarith

/-- **Lemma 1.2.3** (Bertin). Let `(yₙ)` be nonnegative reals and let `δ : ℕ → ℝ` dominate the
*doubling-block* sums in the sense of Bertin's `δₙ = sup_{m ≥ n} ∑_{i=m}^{2m-1} yᵢ`: it is
non-increasing (`Antitone δ`), dominates every block `[m, 2m)` with `m ≥ n` (`hδub`), and dominates
`y₀` (`hδ0`, the `δ₀ = max(y₀, δ₁)` clause). Then for every strictly increasing index sequence
`idx`, the windowed double sum is controlled by `8 ∑_{j ≤ s} δⱼ`:
`∑_{h ≤ s} ∑_{m ≤ s} y_(idx h + m) ≤ 8 ∑_{j ≤ s} δⱼ`.

This is the combinatorial heart of the rationality criterion below. -/
private lemma window_sum_le_eight_delta_sum
    {y : ℕ → ℝ} (hy : ∀ n, 0 ≤ y n) {δ : ℕ → ℝ}
    (hδub : ∀ n m : ℕ, n ≤ m → (∑ i ∈ Finset.Ico m (2 * m), y i) ≤ δ n)
    (hδ0 : y 0 ≤ δ 0) (hδanti : Antitone δ)
    {s : ℕ} {idx : ℕ → ℕ} (hidx : StrictMono idx) :
    (∑ h ∈ Finset.range (s + 1), ∑ m ∈ Finset.range (s + 1), y (idx h + m))
      ≤ 8 * ∑ j ∈ Finset.range (s + 1), δ j := by
  have hδnn : ∀ n, 0 ≤ δ n :=
    fun n => le_trans (Finset.sum_nonneg fun i _ => hy i) (hδub n n le_rfl)
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (s + 1), δ j := Finset.sum_nonneg (fun j _ => hδnn _)
  -- The `h = 0` window, bounded by `2 ∑_{j≤s} δⱼ` (using the `a = 1` cover when `idx 0 = 0`).
  have hF0 : (∑ m ∈ Finset.range (s + 1), y (idx 0 + m)) ≤ 2 * ∑ j ∈ Finset.range (s + 1), δ j := by
    rcases Nat.eq_zero_or_pos (idx 0) with h0 | h0
    · rw [h0]
      have hsplit : ∑ m ∈ Finset.range (s + 1), y (0 + m)
          = (∑ m ∈ Finset.range s, y (m + 1)) + y 0 := by
        rw [Finset.sum_range_succ']; simp
      rw [hsplit]
      have htail : ∑ m ∈ Finset.range s, y (m + 1) ≤ ∑ j ∈ Finset.range (s + 1), δ j := by
        have hcv : ∑ m ∈ Finset.range s, y (m + 1) = ∑ m ∈ Finset.range s, y (1 + m) :=
          Finset.sum_congr rfl (fun m _ => by rw [Nat.add_comm])
        rw [hcv]
        calc ∑ m ∈ Finset.range s, y (1 + m)
            ≤ ∑ m ∈ Finset.range (s + 1), y (1 + m) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro m hm; rw [Finset.mem_range] at hm ⊢; omega
              · intro m _ _; exact hy _
          _ ≤ ∑ t ∈ Finset.range (Nat.log 2 ((1 + s) / 1) + 1), δ (2 ^ t * 1) :=
              window_cover hy hδub (a := 1) (s := s) (le_refl 1)
          _ ≤ ∑ j ∈ Finset.range (s + 1), δ j :=
              cover_sum_le hδanti hδnn (a := 1) (s := s) (le_refl 1)
      have hδ0le : δ 0 ≤ ∑ j ∈ Finset.range (s + 1), δ j := by
        rw [Finset.sum_range_succ']
        have : 0 ≤ ∑ j ∈ Finset.range s, δ (j + 1) := Finset.sum_nonneg (fun j _ => hδnn _)
        linarith
      linarith [htail, hδ0, hδ0le]
    · calc ∑ m ∈ Finset.range (s + 1), y (idx 0 + m)
          ≤ ∑ t ∈ Finset.range (Nat.log 2 ((idx 0 + s) / idx 0) + 1), δ (2 ^ t * idx 0) :=
            window_cover hy hδub (a := idx 0) (s := s) h0
        _ ≤ ∑ j ∈ Finset.range (s + 1), δ j := cover_sum_le hδanti hδnn (a := idx 0) (s := s) h0
        _ ≤ 2 * ∑ j ∈ Finset.range (s + 1), δ j := by linarith
  -- The `h ≥ 1` tail, bounded by `4 ∑_{j≤s} δⱼ`; total `≤ 6 ∑ ≤ 8 ∑`.
  have hPA := window_double_sum_tail_le hy hδub hδanti hδnn hidx (s := s)
  rw [Finset.sum_range_succ']
  linarith [hPA, hF0, hsum_nn]

/-- Dyadic grouping: the sum over `[1, 2^(K+1))` splits into the doubling blocks `[2^k, 2^(k+1))`,
`k = 0, …, K`. -/
private lemma sum_Ico_one_two_pow (a : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ Finset.Ico 1 (2 ^ (K + 1)), a i
      = ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), a i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive a Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))).symm

/-- A function that is `o(n^{-γ})` is, globally on `n ≥ 1`, bounded by `C · n^{-γ}` for some `C ≥ 0`
(the `o`-hypothesis makes `B n · n^γ` a null sequence, hence bounded). -/
private lemma exists_global_bound {B : ℕ → ℝ} {γ : ℝ}
    (hv : B =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → B n ≤ C * (n : ℝ) ^ (-γ) := by
  obtain ⟨C, hC⟩ := hv.tendsto_div_nhds_zero.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hle : B n / (n : ℝ) ^ (-γ) ≤ C := hC ⟨n, rfl⟩
  rw [div_le_iff₀ hpos] at hle
  exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)

/-- The doubling blocks `[2^k, 2^(k+1))` of `|vₙ|²` decay geometrically: `B(2^k) ≤ C·(2^{-γ})^k`. -/
private lemma exists_block_geom_bound {v : ℕ → ℂ} {γ : ℝ}
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ ^ 2)
      ≤ C * ((2 : ℝ) ^ (-γ)) ^ k := by
  obtain ⟨C, hC0, hCb⟩ := exists_global_bound hv
  refine ⟨C, hC0, fun k => ?_⟩
  have h := hCb (2 ^ k) Nat.one_le_two_pow
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) from by rw [pow_succ]; ring] at h
  rwa [show ((2 ^ k : ℕ) : ℝ) ^ (-γ) = ((2 : ℝ) ^ (-γ)) ^ k from by
    rw [Nat.cast_pow, Nat.cast_two, ← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_natCast ((2 : ℝ) ^ (-γ)) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]; congr 1; ring] at h

/-- If the doubling blocks of a nonnegative `a` are bounded by a geometric `D·ρ^k` (`0 ≤ ρ < 1`), the
partial sums `∑_{i≤R} a i` are bounded by `a 0 + D·∑' ρ^k`, uniformly in `R`. -/
private lemma partialSum_bounded {a : ℕ → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    {D ρ : ℝ} (hD0 : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hblock : ∀ k, (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), a i) ≤ D * ρ ^ k) (R : ℕ) :
    ∑ i ∈ Finset.range (R + 1), a i ≤ a 0 + D * ∑' k, ρ ^ k := by
  have hsummable : Summable (fun k => ρ ^ k) := summable_geometric_of_lt_one hρ0 hρ1
  calc ∑ i ∈ Finset.range (R + 1), a i
      ≤ ∑ i ∈ Finset.range (2 ^ (R + 1)), a i :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.mpr
            ((Finset.mem_range.mp hi).trans_le (Nat.lt_two_pow_self (n := R + 1)).le))
          (fun i _ _ => ha0 i)
    _ = a 0 + ∑ i ∈ Finset.Ico 1 (2 ^ (R + 1)), a i := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) Nat.one_le_two_pow]; congr 1; simp
    _ = a 0 + ∑ k ∈ Finset.range (R + 1), ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), a i := by
        rw [sum_Ico_one_two_pow]
    _ ≤ a 0 + ∑ k ∈ Finset.range (R + 1), D * ρ ^ k := by gcongr with i hi; exact hblock i
    _ ≤ a 0 + D * ∑' k, ρ ^ k := by
        rw [← tsum_mul_left]
        gcongr
        exact Summable.sum_le_tsum (Finset.range (R + 1)) (fun k _ => by positivity)
          (hsummable.mul_left D)

/-- **Lemma 1.2.4(i)**: `∑_{i≤r} |vᵢ|² = O(1)` — the geometric block decay makes the partial sums
bounded (`partialSum_bounded`). -/
private lemma part_i {v : ℕ → ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => ∑ i ∈ Finset.range (r + 1), ‖v i‖ ^ 2) =O[atTop] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC0, hblock⟩ := exists_block_geom_bound hv
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ (-γ) := Real.rpow_pos_of_pos two_pos _
  have ht1 : (2 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [Asymptotics.isBigO_iff]
  refine ⟨‖v 0‖ ^ 2 + C * ∑' k, ((2 : ℝ) ^ (-γ)) ^ k, Filter.Eventually.of_forall fun R => ?_⟩
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity), norm_one, mul_one]
  exact partialSum_bounded (fun i => by positivity) hC0 ht0.le ht1 hblock R

/-- **Lemma 1.2.4(ii), case `γ > 1`**: `(∑_{i≤r} |vᵢ|)² = O(1)`. Cauchy–Schwarz bounds each block's
`ℓ¹` mass by `√C · sᵏ` with `s = √(2^{1-γ}) < 1`, so `∑|vᵢ|` is bounded; squaring gives `O(1)`. -/
private lemma part_ii_ge {v : ℕ → ℂ} {γ : ℝ} (hγ : 1 < γ)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => (∑ i ∈ Finset.range (r + 1), ‖v i‖) ^ 2) =O[atTop] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC0, hblock⟩ := exists_block_geom_bound hv
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos two_pos _
  have h2lt1 : (2 : ℝ) ^ (1 - γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set s : ℝ := Real.sqrt ((2 : ℝ) ^ (1 - γ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by
    rw [hs]
    calc Real.sqrt ((2 : ℝ) ^ (1 - γ)) < Real.sqrt 1 := Real.sqrt_lt_sqrt h2pos.le h2lt1
      _ = 1 := Real.sqrt_one
  have hssq : s ^ 2 = (2 : ℝ) ^ (1 - γ) := Real.sq_sqrt h2pos.le
  have hbase : (2 : ℝ) ^ (-γ) * 2 = (2 : ℝ) ^ (1 - γ) := by
    rw [show (1 : ℝ) - γ = -γ + 1 from by ring, Real.rpow_add two_pos, Real.rpow_one]
  have hblockL1 : ∀ k, (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ≤ Real.sqrt C * s ^ k := by
    intro k
    have hcard : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
      rw [Nat.card_Ico, pow_succ]; omega
    have hnn : 0 ≤ ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico (2 ^ k) (2 ^ (k + 1)))
      (fun i => ‖v i‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at hcs
    rw [Nat.cast_pow, Nat.cast_two] at hcs
    have heq : (C * ((2 : ℝ) ^ (-γ)) ^ k) * ((2 : ℝ) ^ k) = (Real.sqrt C * s ^ k) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC0, pow_right_comm, hssq, mul_assoc, ← mul_pow, hbase]
    have hkey : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ^ 2
        ≤ (Real.sqrt C * s ^ k) ^ 2 := by
      calc (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ^ 2
          ≤ (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ ^ 2) * (2 : ℝ) ^ k := hcs
        _ ≤ (C * ((2 : ℝ) ^ (-γ)) ^ k) * (2 : ℝ) ^ k := by gcongr; exact hblock k
        _ = (Real.sqrt C * s ^ k) ^ 2 := heq
    have hsqrt := Real.sqrt_le_sqrt hkey
    rwa [Real.sqrt_sq hnn,
      Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg C) (pow_nonneg hs0 k))] at hsqrt
  rw [Asymptotics.isBigO_iff]
  refine ⟨(‖v 0‖ + Real.sqrt C * ∑' k, s ^ k) ^ 2, Filter.Eventually.of_forall fun R => ?_⟩
  rw [Real.norm_of_nonneg (by positivity), norm_one, mul_one]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _)
    (partialSum_bounded (fun i => norm_nonneg _) (Real.sqrt_nonneg C) hs0 hs1 hblockL1 R) 2

/-- **Lemma 1.2.4(iii), case `γ > 1`**: `∑_{i≤r} ρᵢ = O(1)`. The supremum obeys `ρᵢ ≤ C·i^{-γ}`
(`Real.iSup_le`), and `∑ i^{-γ}` converges for `γ > 1` (`Real.summable_nat_rpow`). -/
private lemma part_iii_ge {v : ℕ → ℂ} {γ : ℝ} (hγ : 1 < γ)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ))
    {ρ : ℕ → ℝ}
    (hρ : ∀ i, ρ i = ⨆ n ∈ Set.Ici i, ∑ h ∈ Finset.Ico n (2 * n), ‖v h‖ ^ 2) :
    (fun r => ∑ i ∈ Finset.range (r + 1), ρ i) =O[atTop] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC0, hCb⟩ := exists_global_bound hv
  have hsummγ : Summable (fun n : ℕ => (n : ℝ) ^ (-γ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hρnn : ∀ i, 0 ≤ ρ i := fun i => by
    rw [hρ i]
    exact Real.iSup_nonneg fun n => Real.iSup_nonneg fun _ =>
      Finset.sum_nonneg fun h _ => by positivity
  have hρbound : ∀ i, 1 ≤ i → ρ i ≤ C * (i : ℝ) ^ (-γ) := by
    intro i hi
    rw [hρ i]
    refine Real.iSup_le (fun n => Real.iSup_le (fun hn => ?_) (by positivity)) (by positivity)
    have hin : i ≤ n := hn
    calc (∑ h ∈ Finset.Ico n (2 * n), ‖v h‖ ^ 2)
        ≤ C * (n : ℝ) ^ (-γ) := hCb n (le_trans hi hin)
      _ ≤ C * (i : ℝ) ^ (-γ) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hi) (by exact_mod_cast hin)
            (by linarith)
  have hSle : ∀ r, ∑ i ∈ Finset.range (r + 1), ρ i ≤ ρ 0 + C * ∑' n : ℕ, (n : ℝ) ^ (-γ) := by
    intro r
    calc ∑ i ∈ Finset.range (r + 1), ρ i
        = ρ 0 + ∑ i ∈ Finset.Ico 1 (r + 1), ρ i := by
          rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega)]
          congr 1; simp
      _ ≤ ρ 0 + ∑ i ∈ Finset.Ico 1 (r + 1), C * (i : ℝ) ^ (-γ) := by
          gcongr with i hi
          exact hρbound i (Finset.mem_Ico.mp hi).1
      _ ≤ ρ 0 + C * ∑' n : ℕ, (n : ℝ) ^ (-γ) := by
          rw [← Finset.mul_sum]
          gcongr
          exact Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsummγ
  rw [Asymptotics.isBigO_iff]
  refine ⟨ρ 0 + C * ∑' n : ℕ, (n : ℝ) ^ (-γ), Filter.Eventually.of_forall fun r => ?_⟩
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hρnn i), norm_one, mul_one]
  exact hSle r

/-- `p`-series partial-sum bound `∑_{i≤r} i^{-γ} ≤ 1 + r^{1-γ}/(1-γ)` for `0 < γ < 1`, via the
integral comparison `∑_{i=2}^r i^{-γ} ≤ ∫₁ʳ x^{-γ} = (r^{1-γ}-1)/(1-γ)`. -/
private lemma psum_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ Finset.range (r + 1), (i : ℝ) ^ (-γ) ≤ 1 + (r : ℝ) ^ (1 - γ) / (1 - γ) := by
  have hγ1' : 0 < 1 - γ := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-γ)) (Set.Icc ((1 : ℕ) : ℝ) (r : ℝ)) := by
    intro x hx y hy hxy
    rw [Set.mem_Icc] at hx
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (by exact_mod_cast hx.1)) hxy
      (by linarith)
  have hint := AntitoneOn.sum_le_integral_Ico hr hanti
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -γ)), Nat.cast_one, Real.one_rpow,
    show -γ + 1 = 1 - γ from by ring] at hint
  have hreindex : ∑ i ∈ Finset.range (r + 1), (i : ℝ) ^ (-γ)
      = 1 + ∑ i ∈ Finset.Ico 1 r, ((i + 1 : ℕ) : ℝ) ^ (-γ) := by
    rw [Finset.sum_range_succ' (fun i => (i : ℝ) ^ (-γ)) r, Nat.cast_zero,
      Real.zero_rpow (ne_of_lt (by linarith : -γ < 0)), add_zero, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hr]
    simp [Real.one_rpow]
  rw [hreindex]
  have hdiv : ((r : ℝ) ^ (1 - γ) - 1) / (1 - γ) ≤ (r : ℝ) ^ (1 - γ) / (1 - γ) := by
    rw [sub_div]; linarith [div_nonneg (zero_le_one (α := ℝ)) hγ1'.le]
  linarith [hint, hdiv]

/-- **Lemma 1.2.4(iii), case `γ < 1`**: `∑_{i≤r} ρᵢ = o(r^{1-γ})`. The supremum is `ρᵢ = o(i^{-γ})`
(same `iSup_le` bound, now with the `o`-eventual constant), and `∑_{i≤r} i^{-γ} = O(r^{1-γ})`
(`psum_le`); an ε-summation argument (split at the `o`-threshold, the head `→ 0` relative to
`r^{1-γ} → ∞`) yields the `o`-bound. -/
private lemma part_iii_lt {v : ℕ → ℂ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ))
    {ρ : ℕ → ℝ}
    (hρ : ∀ i, ρ i = ⨆ n ∈ Set.Ici i, ∑ h ∈ Finset.Ico n (2 * n), ‖v h‖ ^ 2) :
    (fun r => ∑ i ∈ Finset.range (r + 1), ρ i) =o[atTop] fun r => (r : ℝ) ^ (1 - γ) := by
  have hγ1' : 0 < 1 - γ := by linarith
  set C : ℝ := 1 + 1 / (1 - γ) with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  have hρnn : ∀ i, 0 ≤ ρ i := fun i => by
    rw [hρ i]
    exact Real.iSup_nonneg fun n => Real.iSup_nonneg fun _ =>
      Finset.sum_nonneg fun h _ => by positivity
  have hρo : (fun i => ρ i) =o[atTop] fun i => (i : ℝ) ^ (-γ) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Asymptotics.isLittleO_iff.mp hv) hc)
    filter_upwards [eventually_ge_atTop (max N 1)] with i hi
    have hiN : N ≤ i := le_trans (le_max_left _ _) hi
    have hi1 : 1 ≤ i := le_trans (le_max_right _ _) hi
    rw [Real.norm_of_nonneg (hρnn i), Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _),
      hρ i]
    refine Real.iSup_le (fun n => Real.iSup_le (fun hn => ?_) (by positivity)) (by positivity)
    have hin : i ≤ n := hn
    have hBn := hN n (le_trans hiN hin)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun h _ => by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hBn
    refine hBn.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hi1) (by exact_mod_cast hin) (by linarith)
  have hpsum : ∀ r : ℕ, 1 ≤ r →
      ∑ i ∈ Finset.range (r + 1), (i : ℝ) ^ (-γ) ≤ C * (r : ℝ) ^ (1 - γ) := by
    intro r hr
    have hCexp : C * (r : ℝ) ^ (1 - γ) = (r : ℝ) ^ (1 - γ) + (r : ℝ) ^ (1 - γ) / (1 - γ) := by
      rw [hC]; ring
    rw [hCexp]
    linarith [psum_le hγ0 hγ1 hr,
      Real.one_le_rpow (show (1 : ℝ) ≤ r by exact_mod_cast hr) hγ1'.le]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Asymptotics.isLittleO_iff.mp hρo) (show (0 : ℝ) < c / (2 * C) by positivity))
  have hAev : ∀ᶠ r : ℕ in atTop, (∑ i ∈ Finset.range N, ρ i) ≤ c / 2 * (r : ℝ) ^ (1 - γ) := by
    have htend : Tendsto (fun r : ℕ => c / 2 * (r : ℝ) ^ (1 - γ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        ((tendsto_rpow_atTop hγ1').comp tendsto_natCast_atTop_atTop)
    exact htend.eventually_ge_atTop _
  filter_upwards [hAev, eventually_ge_atTop (max N 1)] with r hAr hr
  have hrN : N ≤ r := le_trans (le_max_left _ _) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hρnn i),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _)]
  calc ∑ i ∈ Finset.range (r + 1), ρ i
      = (∑ i ∈ Finset.range N, ρ i) + ∑ i ∈ Finset.Ico N (r + 1), ρ i := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (by omega : N ≤ r + 1)]
    _ ≤ (∑ i ∈ Finset.range N, ρ i)
        + ∑ i ∈ Finset.Ico N (r + 1), c / (2 * C) * (i : ℝ) ^ (-γ) := by
        gcongr with i hi
        have hBi := hN i (Finset.mem_Ico.mp hi).1
        rwa [Real.norm_of_nonneg (hρnn i),
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _)] at hBi
    _ ≤ (∑ i ∈ Finset.range N, ρ i)
        + c / (2 * C) * ∑ i ∈ Finset.range (r + 1), (i : ℝ) ^ (-γ) := by
        rw [← Finset.mul_sum]
        gcongr
        exact fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
    _ ≤ (∑ i ∈ Finset.range N, ρ i) + c / (2 * C) * (C * (r : ℝ) ^ (1 - γ)) := by
        gcongr; exact hpsum r hr1
    _ = (∑ i ∈ Finset.range N, ρ i) + c / 2 * (r : ℝ) ^ (1 - γ) := by rw [hC]; field_simp
    _ ≤ c * (r : ℝ) ^ (1 - γ) := by linarith [hAr]

/-- The `rpow`/cast identity `((2^k : ℕ) : ℝ)^p = (2^p)^k`. -/
private lemma cast_two_pow_rpow (p : ℝ) (k : ℕ) : ((2 ^ k : ℕ) : ℝ) ^ p = ((2 : ℝ) ^ p) ^ k := by
  rw [Nat.cast_pow, Nat.cast_two, ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_natCast ((2:ℝ)^p) k,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

/-- Cauchy–Schwarz on a doubling block (against the constant `1`): the `ℓ¹`-mass squared is at most
the `ℓ²`-mass times the block size `2^k`: `(∑_block |vᵢ|)² ≤ (∑_block |vᵢ|²)·2^k`. -/
private lemma block_l1_sq_le (v : ℕ → ℂ) (k : ℕ) :
    (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ^ 2
      ≤ (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ ^ 2) * (2 : ℝ) ^ k := by
  have hcard : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
    rw [Nat.card_Ico, pow_succ]; omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico (2 ^ k) (2 ^ (k + 1)))
    (fun i => ‖v i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at hcs
  rwa [Nat.cast_pow, Nat.cast_two] at hcs

/-- **Lemma 1.2.4(ii), case `γ < 1`**: `(∑_{i≤r} |vᵢ|)² = o(r^{1-γ})`. Per dyadic block,
Cauchy–Schwarz (`block_l1_sq_le`) gives `∑_block |vᵢ| ≤ √(B(2^k)·2^k)`, which is `o(sᵏ)` with
`s = 2^{(1-γ)/2} > 1` (since `B(2^k) = o((2^{-γ})^k)`). Summing geometrically (ratio `s > 1`) over the
dyadic levels up to `Nat.log 2 r`, an ε-argument gives `∑_{i≤r}|vᵢ| = o(r^{(1-γ)/2})`; squaring (via
`IsLittleO.pow`) yields the claim. -/
private lemma part_ii_lt {v : ℕ → ℂ} {γ : ℝ} (hγ1 : γ < 1)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => (∑ i ∈ Finset.range (r + 1), ‖v i‖) ^ 2) =o[atTop] fun r => (r : ℝ) ^ (1 - γ) := by
  set p : ℝ := (1 - γ) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; positivity
  set s : ℝ := (2 : ℝ) ^ p with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hs0 : 0 ≤ s := hspos.le
  have hs1 : 1 < s := by
    rw [hs, ← Real.rpow_zero (2 : ℝ)]; exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hp0
  have hsne : s ≠ 0 := hspos.ne'
  have hs1ne : s - 1 ≠ 0 := by linarith
  have hssq : s ^ 2 = (2 : ℝ) ^ (1 - γ) := by
    rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ p) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; rw [hp]; ring
  have hbase : (2 : ℝ) ^ (-γ) * 2 = (2 : ℝ) ^ (1 - γ) := by
    rw [show (1 : ℝ) - γ = -γ + 1 from by ring, Real.rpow_add two_pos, Real.rpow_one]
  have hbLo : (fun k => ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖)
      =o[atTop] fun k => s ^ k := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((Asymptotics.isLittleO_iff.mp hv) (show (0 : ℝ) < c ^ 2 by positivity))
    filter_upwards [eventually_ge_atTop N] with k hk
    have hN2 : N ≤ 2 ^ k := (lt_of_le_of_lt hk (Nat.lt_two_pow_self)).le
    have hBk := hN (2 ^ k) hN2
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun m _ => by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      show 2 * 2 ^ k = 2 ^ (k + 1) from by rw [pow_succ]; ring, cast_two_pow_rpow (-γ) k] at hBk
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hs0 k)]
    have hbsq : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ^ 2 ≤ (c * s ^ k) ^ 2 := by
      calc (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖) ^ 2
          ≤ (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ ^ 2) * (2 : ℝ) ^ k := block_l1_sq_le v k
        _ ≤ (c ^ 2 * ((2 : ℝ) ^ (-γ)) ^ k) * (2 : ℝ) ^ k := by gcongr
        _ = (c * s ^ k) ^ 2 := by
            rw [mul_pow, pow_right_comm s k 2, hssq, mul_assoc, ← mul_pow, hbase]
    have hsqrt := Real.sqrt_le_sqrt hbsq
    rwa [Real.sqrt_sq (Finset.sum_nonneg fun i _ => norm_nonneg _),
      Real.sqrt_sq (by positivity)] at hsqrt
  have hSumo : (fun r => ∑ i ∈ Finset.range (r + 1), ‖v i‖) =o[atTop] fun r => (r : ℝ) ^ p := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((Asymptotics.isLittleO_iff.mp hbLo)
      (show (0 : ℝ) < c * (s - 1) / (2 * s) from div_pos (mul_pos hc (by linarith)) (by linarith)))
    set A : ℝ := ‖v 0‖ + ∑ k ∈ Finset.range M, ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ with hA
    have hAev : ∀ᶠ r : ℕ in atTop, A ≤ c / 2 * (r : ℝ) ^ p := by
      have htend : Tendsto (fun r : ℕ => c / 2 * (r : ℝ) ^ p) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity)
          ((tendsto_rpow_atTop hp0).comp tendsto_natCast_atTop_atTop)
      exact htend.eventually_ge_atTop _
    filter_upwards [hAev, eventually_ge_atTop (max (2 ^ M) 1)] with r hAr hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have hrM : 2 ^ M ≤ r := le_trans (le_max_left _ _) hr
    set K : ℕ := Nat.log 2 r with hK
    have h2K : 2 ^ K ≤ r := Nat.pow_log_le_self 2 (by omega)
    have hrK : r < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
    have hMK : M ≤ K := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num : (1:ℕ) < 2)).mp
      (lt_of_le_of_lt hrM hrK))
    have hgeom : ∑ k ∈ Finset.range (K + 1), s ^ k ≤ s ^ (K + 1) / (s - 1) := by
      rw [geom_sum_eq (by linarith : s ≠ 1), sub_div]
      linarith [div_nonneg (zero_le_one (α := ℝ)) (by linarith : (0:ℝ) ≤ s - 1)]
    have hsKr : s ^ K ≤ (r : ℝ) ^ p := by
      rw [hs, ← cast_two_pow_rpow p K]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h2K) hp0.le
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _)]
    calc ∑ i ∈ Finset.range (r + 1), ‖v i‖
        ≤ ∑ i ∈ Finset.range (2 ^ (K + 1)), ‖v i‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => Finset.mem_range.mpr
              (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hrK))
            (fun i _ _ => norm_nonneg _)
      _ = ‖v 0‖ + ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ := by
          rw [Finset.range_eq_Ico,
            ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) Nat.one_le_two_pow, sum_Ico_one_two_pow]
          congr 1; simp
      _ = A + ∑ k ∈ Finset.Ico M (K + 1), ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), ‖v i‖ := by
          rw [hA, add_assoc]; congr 1
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
            ← Finset.sum_Ico_consecutive _ (Nat.zero_le M) (Nat.le_succ_of_le hMK)]
      _ ≤ A + ∑ k ∈ Finset.Ico M (K + 1), c * (s - 1) / (2 * s) * s ^ k := by
          gcongr with k hk
          have := hM k (Finset.mem_Ico.mp hk).1
          rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _),
            Real.norm_of_nonneg (pow_nonneg hspos.le k)] at this
      _ ≤ A + c * (s - 1) / (2 * s) * ∑ k ∈ Finset.range (K + 1), s ^ k := by
          rw [← Finset.mul_sum]; gcongr
          exact fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      _ ≤ A + c * (s - 1) / (2 * s) * (s ^ (K + 1) / (s - 1)) := by gcongr
      _ = A + c / 2 * s ^ K := by congr 1; rw [pow_succ s K]; field_simp
      _ ≤ A + c / 2 * (r : ℝ) ^ p := by gcongr
      _ ≤ c * (r : ℝ) ^ p := by linarith [hAr]
  have hsq := hSumo.pow (n := 2) (by norm_num)
  have hpow : ∀ r : ℕ, ((r : ℝ) ^ p) ^ 2 = (r : ℝ) ^ (1 - γ) := fun r => by
    rw [← Real.rpow_natCast ((r : ℝ) ^ p) 2, ← Real.rpow_mul (Nat.cast_nonneg r)]
    congr 1; rw [hp]; push_cast; ring
  exact hsq.congr' (Filter.EventuallyEq.refl _ _) (Filter.Eventually.of_forall hpow)

/-- **Lemma 1.2.4** (Bertin). Let `(vₙ)` be complex and `γ > 0`, and suppose the doubling-block sums
of `|vₙ|²` decay like `∑_{m=n}^{2n-1} |vₘ|² = o(n^{-γ})`. Set `ρᵢ = sup_{n≥i} ∑_{h=n}^{2n-1} |vₕ|²`
(Bertin's `ρ`; this is Lemma 1.2.3's `δ` for `yₙ = |vₙ|²`). Then, as `r → ∞`:

* **(i)** `∑_{i≤r} |vᵢ|² = O(1)`;
* **(ii)** `(∑_{i≤r} |vᵢ|)² = o(r^{1-γ})` if `γ < 1`, and `= O(1)` if `γ > 1`;
* **(iii)** `∑_{i≤r} ρᵢ = o(r^{1-γ})` if `γ < 1`, and `= O(1)` if `γ > 1`.

(The boundary case `γ = 1` is excluded in (ii), (iii), matching Bertin.) -/
private lemma blockNormSq_littleO_asymptotics {v : ℕ → ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hv : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖v m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ))
    {ρ : ℕ → ℝ}
    (hρ : ∀ i, ρ i = ⨆ n ∈ Set.Ici i, ∑ h ∈ Finset.Ico n (2 * n), ‖v h‖ ^ 2) :
    -- (i)
    ((fun r => ∑ i ∈ Finset.range (r + 1), ‖v i‖ ^ 2) =O[atTop] fun _ => (1 : ℝ)) ∧
    -- (ii)
    ((γ < 1 → (fun r => (∑ i ∈ Finset.range (r + 1), ‖v i‖) ^ 2) =o[atTop]
        fun r => (r : ℝ) ^ (1 - γ)) ∧
      (1 < γ → (fun r => (∑ i ∈ Finset.range (r + 1), ‖v i‖) ^ 2) =O[atTop] fun _ => (1 : ℝ))) ∧
    -- (iii)
    ((γ < 1 → (fun r => ∑ i ∈ Finset.range (r + 1), ρ i) =o[atTop] fun r => (r : ℝ) ^ (1 - γ)) ∧
      (1 < γ → (fun r => ∑ i ∈ Finset.range (r + 1), ρ i) =O[atTop] fun _ => (1 : ℝ))) :=
  -- Part (i) and the `γ > 1` cases of (ii), (iii) are proved; the `γ < 1` cases remain.
  ⟨part_i hγ hv, ⟨fun h => part_ii_lt h hv, fun h => part_ii_ge h hv⟩,
    ⟨fun h => part_iii_lt hγ h hv hρ, fun h => part_iii_ge h hv hρ⟩⟩

/-- **Lemma 1.2.5** (Bertin). A square matrix `X` of order `n + 1` over `ℂ` whose squared
Frobenius norm is strictly below its order, `∑_{i,j} |x_{i,j}|² < n + 1`, has determinant of modulus
`< 1`. This is Hadamard's inequality `|det X| ≤ ∏ⱼ ‖colⱼ‖` (see `ForMathlib`'s
`OrthonormalBasis.norm_det_le_prod_norm`) combined with the AM–GM inequality:
`|det X|² ≤ ∏ⱼ (∑ᵢ |x_{i,j}|²) ≤ ((∑_{i,j} |x_{i,j}|²)/(n+1))^{n+1} < 1`. -/
private lemma norm_det_lt_one_of_sum_normSq_lt {n : ℕ}
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hX : ∑ j, ∑ i, ‖X i j‖ ^ 2 < (n + 1 : ℝ)) :
    ‖X.det‖ < 1 := by
  set c : Fin (n + 1) → ℝ := fun j => ∑ i, ‖X i j‖ ^ 2 with hc
  have hcnn : ∀ j, 0 ≤ c j := fun j => Finset.sum_nonneg fun i _ => by positivity
  -- AM–GM: the product of the column squared-norms is `< 1`.
  have hprodc : ∏ j, c j < 1 := by
    have hw : ∑ _j : Fin (n + 1), ((n + 1 : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (by positivity)]
    have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => ((n + 1 : ℝ))⁻¹) c
      (fun i _ => by positivity) hw (fun i _ => hcnn i)
    rw [Real.finsetProd_rpow Finset.univ c (fun i _ => hcnn i)] at hgm
    have harith : ∑ j, ((n + 1 : ℝ))⁻¹ * c j < 1 := by
      rw [← Finset.mul_sum]
      have hmul : (n + 1 : ℝ)⁻¹ * ∑ j, c j < (n + 1 : ℝ)⁻¹ * (n + 1 : ℝ) :=
        mul_lt_mul_of_pos_left hX (inv_pos.mpr (by positivity))
      rwa [inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)] at hmul
    have hlt : (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ < 1 := lt_of_le_of_lt hgm harith
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ :=
      calc (1 : ℝ) = (1 : ℝ) ^ ((n + 1 : ℝ))⁻¹ := (Real.one_rpow _).symm
        _ ≤ (∏ j, c j) ^ ((n + 1 : ℝ))⁻¹ := Real.rpow_le_rpow zero_le_one hge (by positivity)
    linarith
  -- Hadamard `‖det X‖ ≤ ∏ⱼ √(cⱼ)`, and `(∏ⱼ √(cⱼ))² = ∏ⱼ cⱼ < 1`.
  have had : ‖X.det‖ ≤ ∏ j, Real.sqrt (c j) := Matrix.norm_det_le_prod_col_norm X
  have hsqrtnn : 0 ≤ ∏ j, Real.sqrt (c j) := Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  have hsq : (∏ j, Real.sqrt (c j)) ^ 2 = ∏ j, c j := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (hcnn j)
  have hprodsqrt : ∏ j, Real.sqrt (c j) < 1 := by nlinarith [hsq, hprodc, hsqrtnn]
  linarith [had, hprodsqrt]

/-! ### Bertin's matrix `A(t, L_r, f)` for the proof of Theorem 1.2.2

Bertin's proof (case ii, `α = 0 < 1 < β` or symmetric) writes the Kronecker determinant `Dᵣ(F)` of
`F = S(f)` as `det(xₘₙ)` where `xₘₙ = uₘₙ + vₘₙ` is built from the numerator/denominator Taylor
coefficients `sc, tc` (this is **Bertin's Lemma 1.1.6**), bounds `∑|xₘₙ|²` by Parseval and the
windowed block sums (`window_sum_le_eight_delta_sum`), and concludes via the asymptotics
(`blockNormSq_littleO_asymptotics`) and Hadamard/AM–GM (`norm_det_lt_one_of_sum_normSq_lt`) that
`|Dᵣ(F)| < 1`, so the integer `Dᵣ(F)` vanishes and Kronecker's criterion applies. -/

/-- Bertin's entry `xₘₙ = uₘₙ + vₘₙ` (Lemma 1.1.6), with `uₘₙ = ∑_{i≤n} tᵢ s_{m+n-i}` and
`vₘₙ = -∑_{i<n} sᵢ t_{m+n-i}`, built from the Taylor coefficients `sc, tc`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def uvEntry (sc tc : ℕ → ℂ) (m n : ℕ) : ℂ :=
  (∑ i ∈ Finset.range (n + 1), tc i * sc (m + n - i))
    - ∑ i ∈ Finset.range n, sc i * tc (m + n - i)

/-- Bertin's matrix `A(t, L_r, f)` on the index sequence `L = (0, 1, …, r)`: the `(r+1)×(r+1)`
matrix with `(i, j)` entry `uvEntry sc tc i j`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def uvMatrix (sc tc : ℕ → ℂ) (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => uvEntry sc tc i j

/-- **Bertin's Lemma 1.1.6** (cited; the determinant identity for the proof of Theorem 1.2.2). For
`f = s/t` analytic on `D(0,1)` with `f` regular at `0` and Taylor coefficients `a, sc, tc`, there is a
normalising constant `c = tc₀⁻¹ ≠ 0` (so `c·tc₀ = 1`) for which the Kronecker determinant of `S(f)`
equals the determinant of Bertin's matrix in the normalised coefficients: `Dᵣ(S(f)) = det A(t, Lᵣ, f)`
for every `r`. (Bundles the `s = t·f` coefficient convolution and the harmless `t₀ = 1` normalisation;
asserted on the authority of [Ber92], §1.1.) -/
@[category API, AMS 15, ref "Ber92"]
axiom uvSetup {f s t : ℂ → ℂ} {a sc tc : ℕ → ℂ} {ρ : ENNReal}
    (hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ)
    (hs : HasFPowerSeriesOnBall s (FormalMultilinearSeries.ofScalars ℂ sc) 0 1)
    (ht : HasFPowerSeriesOnBall t (FormalMultilinearSeries.ofScalars ℂ tc) 0 1)
    (hft : ∀ z ∈ Metric.ball (0 : ℂ) 1, t z ≠ 0 → f z = s z / t z) :
    ∃ c : ℂ, c ≠ 0 ∧ c * tc 0 = 1 ∧
      ∀ r, kroneckerDet (PowerSeries.mk a) r
        = (uvMatrix (fun n => c * sc n) (fun n => c * tc n) r).det

/-- **Parseval majoration** (cited; the analytic core of Bertin's bound in the proof of
Theorem 1.2.2). The squared Frobenius norm of Bertin's matrix is controlled by the windowed block
sums of `|sc|²` and `|tc|²`, weighted by the `ℓ¹` partial sums of the other sequence:
`∑_{i,j} |xᵢⱼ|² ≤ 2[(∑_{k≤r}|tcₖ|)² ∑_{m,j≤r}|sc_{m+j}|² + (∑_{k≤r}|scₖ|)² ∑_{m,j≤r}|tc_{m+j}|²]`.
This is `|x|² ≤ 2(|u|² + |v|²)` together with the two Parseval/Cauchy–Schwarz estimates
`∑ₙ|uₘₙ|² ≤ (∑|tₖ|)² ∑ⱼ|s_{m+j}|²` (and symmetrically for `v`); asserted on the authority of
[Ber92]. -/
@[category API, AMS 30, ref "Ber92"]
axiom uvMatrix_normSq_le (sc tc : ℕ → ℂ) (r : ℕ) :
    ∑ j, ∑ i, ‖uvMatrix sc tc r i j‖ ^ 2
      ≤ 2 * ((∑ k ∈ Finset.range (r + 1), ‖tc k‖) ^ 2
              * ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖sc (m + j)‖ ^ 2
            + (∑ k ∈ Finset.range (r + 1), ‖sc k‖) ^ 2
              * ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖tc (m + j)‖ ^ 2)

/-- **Hardy-quotient bounded characteristic** (cited; the case `α, β > 0` of Theorem 1.2.2). If the
numerator and denominator are in the Hardy space `H²` (`∑|scₙ|², ∑|tcₙ|² < ∞`), then `f = s/t` has
bounded Nevanlinna characteristic. This is the standard fact that a quotient of `H²` functions is of
bounded characteristic; asserted on the authority of [Ber92] (and [Nevanlinna]). -/
@[category API, AMS 30, ref "Ber92"]
axiom hasBoundedCharacteristic_of_quotient_summable {f s t : ℂ → ℂ} {sc tc : ℕ → ℂ}
    (hs : HasFPowerSeriesOnBall s (FormalMultilinearSeries.ofScalars ℂ sc) 0 1)
    (ht : HasFPowerSeriesOnBall t (FormalMultilinearSeries.ofScalars ℂ tc) 0 1)
    (hft : ∀ z ∈ Metric.ball (0 : ℂ) 1, t z ≠ 0 → f z = s z / t z)
    (hssum : Summable fun n => ‖sc n‖ ^ 2) (htsum : Summable fun n => ‖tc n‖ ^ 2) :
    Complex.HasBoundedCharacteristic f

/-- The doubling block `∑_{n ≤ h < 2n} ‖w h‖²` of a sequence `w`. -/
private noncomputable def blk (w : ℕ → ℂ) (n : ℕ) : ℝ := ∑ h ∈ Finset.Ico n (2 * n), ‖w h‖ ^ 2

/-- Bertin's `δ`-supremum `sup_{n ≥ i} ∑_{n ≤ h < 2n} ‖w h‖²` (the `ρ` of Lemma 1.2.4). -/
private noncomputable def blockSup (w : ℕ → ℂ) (i : ℕ) : ℝ := ⨆ n ∈ Set.Ici i, blk w n

/-- Bertin's dominating sequence `δᵢ` for `yₙ = ‖wₙ‖²`: the `δ`-supremum, patched at `0` to dominate
`‖w₀‖²` (Bertin's `δ₀ = max(y₀, δ₁)`). It satisfies the hypotheses of `window_sum_le_eight_delta_sum`
(Lemma 1.2.3). -/
private noncomputable def deltaSeq (w : ℕ → ℂ) (i : ℕ) : ℝ :=
  if i = 0 then max (‖w 0‖ ^ 2) (blockSup w 0) else blockSup w i

/-- With a global bound `B` on the doubling blocks, `blockSup` is well-behaved: each block is `≤` it,
and it is antitone. -/
private lemma blk_le_blockSup {w : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, blk w n ≤ B)
    {i m : ℕ} (him : i ≤ m) : blk w m ≤ blockSup w i :=
  le_ciSup_of_le ⟨B, by rintro x ⟨n, rfl⟩; exact Real.iSup_le (fun _ => hB n) hB0⟩ m
    (le_ciSup_of_le ⟨B, by rintro x ⟨_, rfl⟩; exact hB m⟩ (Set.mem_Ici.2 him) le_rfl)

private lemma blockSup_antitone {w : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, blk w n ≤ B) :
    Antitone (blockSup w) := by
  intro i j hij
  have hbn : (0 : ℝ) ≤ blockSup w i :=
    le_trans (Finset.sum_nonneg fun h _ => by positivity) (blk_le_blockSup hB0 hB (le_refl i))
  exact Real.iSup_le
    (fun n => Real.iSup_le (fun hn => blk_le_blockSup hB0 hB (le_trans hij (Set.mem_Ici.1 hn))) hbn)
    hbn

/-- **Lemma 1.2.3 in action**: the windowed double sum of `‖w·‖²` over the identity sequence is
controlled by `8 ∑ δᵢ`. -/
private lemma windowDoubleSum_le {w : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, blk w n ≤ B) (r : ℕ) :
    ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖w (m + j)‖ ^ 2
      ≤ 8 * ∑ i ∈ Finset.range (r + 1), deltaSeq w i := by
  have hanti := blockSup_antitone hB0 hB
  have key := window_sum_le_eight_delta_sum (y := fun n => ‖w n‖ ^ 2) (fun n => by positivity)
    (δ := deltaSeq w)
    (hδub := by
      intro n m hnm
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact le_trans (blk_le_blockSup hB0 hB (Nat.zero_le m)) (le_max_right _ _)
      · rw [deltaSeq, if_neg (by omega)]; exact blk_le_blockSup hB0 hB hnm)
    (hδ0 := by rw [deltaSeq, if_pos rfl]; exact le_max_left _ _)
    (hδanti := by
      refine antitone_nat_of_succ_le (fun i => ?_)
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; rw [deltaSeq, if_neg (by norm_num), deltaSeq, if_pos rfl]
        exact le_trans (hanti (Nat.zero_le 1)) (le_max_right _ _)
      · rw [deltaSeq, if_neg (by omega), deltaSeq, if_neg (by omega)]; exact hanti (by omega))
    (idx := id) strictMono_id (s := r)
  simpa using key

/-- `∑ δᵢ` differs from `∑ blockSupᵢ` only in the patched `i = 0` term (a constant in `r`). -/
private lemma sumDelta_eq (w : ℕ → ℂ) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), deltaSeq w i
      = (∑ i ∈ Finset.range (r + 1), blockSup w i) + (deltaSeq w 0 - blockSup w 0) := by
  have hcongr : ∀ i ∈ Finset.range r, deltaSeq w (i + 1) = blockSup w (i + 1) :=
    fun i _ => by rw [deltaSeq, if_neg (Nat.succ_ne_zero i)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_congr rfl hcongr]; ring

/-- For `γ > 1`, `∑_{i≤r} δᵢ = O(1)` (Lemma 1.2.4 (iii), plus the constant patch term). -/
private lemma sumDelta_isBigO_one {w : ℕ → ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : 1 < γ)
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => ∑ i ∈ Finset.range (r + 1), deltaSeq w i) =O[atTop] fun _ => (1 : ℝ) := by
  have hblock := (blockNormSq_littleO_asymptotics hγ hw (ρ := blockSup w) (fun _ => rfl)).2.2.2 hγ1
  have hconst : (fun _ : ℕ => deltaSeq w 0 - blockSup w 0) =O[atTop] fun _ => (1 : ℝ) :=
    Asymptotics.isBigO_const_const _ one_ne_zero atTop
  simpa only [sumDelta_eq] using hblock.add hconst

/-- For `block(w) = o(1)` (the `γ = 0` regime), `∑_{i≤r} δᵢ = o(r)` (`blockSup → 0` by tail-sup of a
null sequence, then Cesàro). -/
private lemma sumDelta_isLittleO_self {w : ℕ → ℂ}
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun _ => (1 : ℝ)) :
    (fun r => ∑ i ∈ Finset.range (r + 1), deltaSeq w i) =o[atTop] fun r => (r : ℝ) + 1 := by
  have h0 : Tendsto (blk w) atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hw
  obtain ⟨B, hB⟩ := h0.bddAbove_range
  have hB' : ∀ n, blk w n ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := le_trans (by simp [blk]) (hB' 0)
  have hbs0 : Tendsto (blockSup w) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h0) (ε / 2) (by linarith)
    refine ⟨N, fun i hi => ?_⟩
    have hlb : 0 ≤ blockSup w i :=
      le_trans (Finset.sum_nonneg fun h _ => by positivity) (blk_le_blockSup hB0 hB' (le_refl i))
    have hub : blockSup w i ≤ ε / 2 := by
      refine Real.iSup_le (fun n => Real.iSup_le (fun hn => ?_) (by linarith)) (by linarith)
      have hd := hN n (le_trans hi (Set.mem_Ici.1 hn))
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (Finset.sum_nonneg fun h _ => by positivity)] at hd
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hlb]; linarith
  -- `deltaSeq` agrees with `blockSup` for `i ≥ 1`, hence also `→ 0`; Cesàro then gives `o(r+1)`.
  have hdelta0 : Tendsto (deltaSeq w) atTop (𝓝 0) := by
    refine hbs0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with i hi
    rw [deltaSeq, if_neg (by omega)]
  refine Asymptotics.isLittleO_of_tendsto
    (fun r hr => absurd hr (by positivity : (0 : ℝ) < (r : ℝ) + 1).ne') ?_
  refine ((hdelta0.cesaro).comp (tendsto_add_atTop_nat 1)).congr (fun r => ?_)
  simp only [Function.comp_apply]
  rw [div_eq_inv_mul]; push_cast; ring

private lemma deltaSeq_nonneg {w : ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, blk w n ≤ B) (i : ℕ) :
    0 ≤ deltaSeq w i := by
  have hbs : 0 ≤ blockSup w i :=
    le_trans (Finset.sum_nonneg fun h _ => by positivity) (blk_le_blockSup hB0 hB (le_refl i))
  rw [deltaSeq]; split_ifs with hi
  · exact le_trans (by positivity) (le_max_left _ _)
  · exact hbs

/-- `WDS_w := ∑_{m,j ≤ r} ‖w(m+j)‖²`. For `block(w) = o(1)`, `WDS_w = o(r+1)`. -/
private lemma WDS_o {w : ℕ → ℂ}
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun _ => (1 : ℝ)) :
    (fun r => ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖w (m + j)‖ ^ 2)
      =o[atTop] fun r => (r : ℝ) + 1 := by
  have h0 : Tendsto (blk w) atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hw
  obtain ⟨B, hB⟩ := h0.bddAbove_range
  have hB' : ∀ n, blk w n ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := le_trans (by simp [blk]) (hB' 0)
  refine (Asymptotics.isBigO_of_le atTop (fun r => ?_)).trans_isLittleO
    ((sumDelta_isLittleO_self hw).const_mul_left 8)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => by positivity),
    Real.norm_of_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun i _ => deltaSeq_nonneg hB0 hB' i))]
  exact windowDoubleSum_le hB0 hB' r

/-- For `block(w) = o(n^{-γ})` with `γ > 1`, `WDS_w = O(1)`. -/
private lemma WDS_O {w : ℕ → ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : 1 < γ)
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖w (m + j)‖ ^ 2)
      =O[atTop] fun _ => (1 : ℝ) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (blk w) atTop (𝓝 0) := hw.isBigO.trans_tendsto hg
  obtain ⟨B, hB⟩ := h0.bddAbove_range
  have hB' : ∀ n, blk w n ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := le_trans (by simp [blk]) (hB' 0)
  refine (Asymptotics.isBigO_of_le atTop (fun r => ?_)).trans
    ((sumDelta_isBigO_one hγ hγ1 hw).const_mul_left 8)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => by positivity),
    Real.norm_of_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun i _ => deltaSeq_nonneg hB0 hB' i))]
  exact windowDoubleSum_le hB0 hB' r

/-- For `γ > 1`, the squared `ℓ¹` partial sum `(∑_{k≤r} ‖wₖ‖)² = O(1)` (Lemma 1.2.4 (ii)). -/
private lemma partialL1Sq_O {w : ℕ → ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : 1 < γ)
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-γ)) :
    (fun r => (∑ k ∈ Finset.range (r + 1), ‖w k‖) ^ 2) =O[atTop] fun _ => (1 : ℝ) :=
  (blockNormSq_littleO_asymptotics hγ hw (ρ := blockSup w) (fun _ => rfl)).2.1.2 hγ1

/-- For `block(w) = o(1)` (the `γ = 0` regime), `(∑_{k≤r} ‖wₖ‖)² = o(r+1)` (`part_ii_lt` at `γ = 0`,
where `r^{1-0} = r ≤ r + 1`). -/
private lemma partialL1Sq_o {w : ℕ → ℂ}
    (hw : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-(0 : ℝ))) :
    (fun r => (∑ k ∈ Finset.range (r + 1), ‖w k‖) ^ 2) =o[atTop] fun r => (r : ℝ) + 1 := by
  refine (part_ii_lt (by norm_num : (0 : ℝ) < 1) hw).trans_isBigO ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.eventually_atTop.2 ⟨0, fun r _ => ?_⟩⟩
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), Real.norm_of_nonneg (by positivity),
    one_mul, sub_zero, Real.rpow_one]
  linarith [Nat.cast_nonneg (α := ℝ) r]

/-- Case ii spine: if the (integer) Kronecker determinants of `S(f)` equal the determinants of
Bertin's matrix, and the squared Frobenius norm of that matrix is `< r + 1` for all large `r`, then
`S(f)` is a rational series. Indeed Hadamard/AM–GM (`norm_det_lt_one_of_sum_normSq_lt`, Lemma 1.2.5)
makes `|det| < 1`, and an integer of modulus `< 1` vanishes, so Kronecker's criterion applies. -/
private lemma rational_of_uv_eventually_lt {a sc tc : ℕ → ℂ}
    (hint : ∀ n, ∃ m : ℤ, a n = (m : ℂ))
    (hdet : ∀ r, kroneckerDet (PowerSeries.mk a) r = (uvMatrix sc tc r).det)
    (hlt : ∀ᶠ r in atTop, ∑ j, ∑ i, ‖uvMatrix sc tc r i j‖ ^ 2 < (r : ℝ) + 1) :
    IsRationalSeries (PowerSeries.mk a) := by
  classical
  choose b hb using hint
  have hcast : ∀ n, kroneckerDet (PowerSeries.mk a) n
      = ((kroneckerDet (PowerSeries.mk b) n : ℤ) : ℂ) := by
    intro n
    have hmap : hankelMatrix (PowerSeries.mk a) n
        = (hankelMatrix (PowerSeries.mk b) n).map (Int.castRingHom ℂ) := by
      ext i j
      simp only [hankelMatrix_apply, PowerSeries.coeff_mk, Matrix.map_apply, Int.coe_castRingHom, hb]
    show (hankelMatrix (PowerSeries.mk a) n).det = (((hankelMatrix (PowerSeries.mk b) n).det : ℤ) : ℂ)
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom]
  rw [isRationalSeries_iff_kroneckerDet_eventually_zero]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlt
  refine ⟨N, fun r hr => ?_⟩
  have hdetlt : ‖(uvMatrix sc tc r).det‖ < 1 :=
    norm_det_lt_one_of_sum_normSq_lt (uvMatrix sc tc r) (hN r hr)
  have hnorm : ‖kroneckerDet (PowerSeries.mk a) r‖ < 1 := by rw [hdet r]; exact hdetlt
  have hzero : kroneckerDet (PowerSeries.mk b) r = 0 := by
    rw [hcast r, Complex.norm_intCast] at hnorm
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hnorm)
  rw [hcast r, hzero, Int.cast_zero]

/-- **Case ii** of Theorem 1.2.2 (for already-normalised coefficient sequences `sc, tc` whose
Kronecker determinants match Bertin's matrix). In the admissible region `{α=0<1<β} ∪ {1<α, β=0}`, the
Frobenius norm `∑|xᵢⱼ|²` is `o(r+1)` — each Parseval term is a product of an `O(1)` factor and an
`o(r+1)` factor (Lemma 1.2.4 + the `γ=0` helpers) — so it is eventually `< r+1` and the spine applies. -/
private lemma rational_case_ii {a sc tc : ℕ → ℂ} {α β : ℝ}
    (hint : ∀ n, ∃ m : ℤ, a n = (m : ℂ))
    (hdet : ∀ r, kroneckerDet (PowerSeries.mk a) r = (uvMatrix sc tc r).det)
    (hαβ : (α = 0 ∧ 1 < β) ∨ (1 < α ∧ β = 0))
    (hs2 : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖sc m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-α))
    (ht2 : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖tc m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-β)) :
    IsRationalSeries (PowerSeries.mk a) := by
  have hpow : (fun n : ℕ => (n : ℝ) ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by
    funext n; rw [neg_zero, Real.rpow_zero]
  apply rational_of_uv_eventually_lt hint hdet
  have hT1 : (fun r => (∑ k ∈ Finset.range (r + 1), ‖tc k‖) ^ 2
      * ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖sc (m + j)‖ ^ 2)
      =o[atTop] fun r => (r : ℝ) + 1 := by
    rcases hαβ with ⟨hα0, hβ1⟩ | ⟨hα1, hβ0⟩
    · subst hα0
      simpa using (partialL1Sq_O (by linarith) hβ1 ht2).mul_isLittleO (WDS_o (hpow ▸ hs2))
    · subst hβ0
      simpa using (partialL1Sq_o ht2).mul_isBigO (WDS_O (by linarith) hα1 hs2)
  have hT2 : (fun r => (∑ k ∈ Finset.range (r + 1), ‖sc k‖) ^ 2
      * ∑ m ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1), ‖tc (m + j)‖ ^ 2)
      =o[atTop] fun r => (r : ℝ) + 1 := by
    rcases hαβ with ⟨hα0, hβ1⟩ | ⟨hα1, hβ0⟩
    · subst hα0
      simpa using (partialL1Sq_o hs2).mul_isBigO (WDS_O (by linarith) hβ1 ht2)
    · subst hβ0
      simpa using (partialL1Sq_O (by linarith) hα1 hs2).mul_isLittleO (WDS_o (hpow ▸ ht2))
  have hFrob : (fun r => ∑ j, ∑ i, ‖uvMatrix sc tc r i j‖ ^ 2) =o[atTop] fun r => (r : ℝ) + 1 := by
    refine (Asymptotics.isBigO_of_le atTop (fun r => ?_)).trans_isLittleO
      ((hT1.add hT2).const_mul_left 2)
    rw [Real.norm_of_nonneg
        (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => by positivity),
      Real.norm_of_nonneg (by positivity)]
    exact uvMatrix_normSq_le sc tc r
  filter_upwards [Asymptotics.isLittleO_iff.mp hFrob (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => by positivity),
    Real.norm_of_nonneg (by positivity)] at hr
  linarith

/-- **Theorem 1.2.2** (Bertin). Let `f` be meromorphic on `D(0,1)` with no pole at `0` and **integer**
Taylor coefficients `a` at `0`. Suppose `f = s / t` with `s, t` analytic on `D(0,1)` (Taylor series
`s = ∑ sₙ zⁿ`, `t = ∑ tₙ zⁿ`), and that there are reals `α, β` with

* `(α, β)` in the admissible region `{α>0, β>0} ∪ {α=0, β>1} ∪ {α>1, β=0}`, and
* doubling-block `ℓ²` decay `∑_{m=n}^{2n-1} |sₘ|² = o(n^{-α})` and `∑_{m=n}^{2n-1} |tₘ|² = o(n^{-β})`.

Then `f` is a rational function — its Taylor series `S(f)` is a rational series (`IsRationalSeries`;
over `ℂ` this is exactly "the expansion of a rational function", as in Theorem 1.2.1).

Proof strategy (Bertin; **not yet formalized** — deferred with the three lemmas above). Test `f`
against the multiplier `t` (Bertin's multiplier criterion, Theorem 1.1.2): the matrix `A(t, L_r, f)`
has integer determinant (integer Taylor coefficients) and entries built from the coefficients of
`s = t·f`. Its squared Frobenius norm is controlled by the windowed block sums of `|sₘ|²` and `|tₘ|²`
via `window_sum_le_eight_delta_sum` (Lemma 1.2.3), whose asymptotics — `o(r^{1-γ})` or `O(1)` per the
admissible region — come from `blockNormSq_littleO_asymptotics` (Lemma 1.2.4); this forces
`∑ |entries|² < n+1` on suitable index sets, so `norm_det_lt_one_of_sum_normSq_lt` (Lemma 1.2.5) gives
`|det A| < 1`. An integer determinant of modulus `< 1` vanishes, so the multiplier criterion makes
`S(f)` rational, whence — as in Theorem 1.2.1 — `f` is rational. -/
@[category research solved, AMS 30, ref "Ber92"]
theorem isRationalSeries_of_quotient_blockNormSq_littleO
    {f s t : ℂ → ℂ} {a sc tc : ℕ → ℂ} {ρ : ENNReal} {α β : ℝ}
    (hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ)
    (hint : ∀ n, ∃ m : ℤ, a n = (m : ℂ))
    (hs : HasFPowerSeriesOnBall s (FormalMultilinearSeries.ofScalars ℂ sc) 0 1)
    (ht : HasFPowerSeriesOnBall t (FormalMultilinearSeries.ofScalars ℂ tc) 0 1)
    (hft : ∀ z ∈ Metric.ball (0 : ℂ) 1, t z ≠ 0 → f z = s z / t z)
    (hαβ : (0 < α ∧ 0 < β) ∨ (α = 0 ∧ 1 < β) ∨ (1 < α ∧ β = 0))
    (hs2 : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖sc m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-α))
    (ht2 : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖tc m‖ ^ 2) =o[atTop] fun n => (n : ℝ) ^ (-β)) :
    IsRationalSeries (PowerSeries.mk a) := by
  -- A nonnegative sequence whose doubling blocks are `o(n^{-δ})` with `δ > 0` is square-summable
  -- (Lemma 1.2.4 (i): the partial sums of `‖·‖²` are `O(1)`).
  have hsummable : ∀ {w : ℕ → ℂ} {d : ℝ}, 0 < d →
      (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2) =o[atTop] (fun n => (n : ℝ) ^ (-d)) →
      Summable fun n => ‖w n‖ ^ 2 := by
    intro w d hd hw
    have hO := (blockNormSq_littleO_asymptotics hd hw
      (ρ := fun i => ⨆ n ∈ Set.Ici i, ∑ h ∈ Finset.Ico n (2 * n), ‖w h‖ ^ 2) (fun _ => rfl)).1
    obtain ⟨C, hC⟩ := hO.bound
    obtain ⟨R, hR⟩ := eventually_atTop.mp hC
    refine summable_of_sum_range_le (fun n => by positivity) (c := C) (fun n => ?_)
    have hmono : ∑ i ∈ Finset.range n, ‖w i‖ ^ 2
        ≤ ∑ i ∈ Finset.range (max n R + 1), ‖w i‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro i hi; rw [Finset.mem_range] at hi ⊢; omega) (fun i _ _ => by positivity)
    have hbnd := hR (max n R) (by omega)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity),
      norm_one, mul_one] at hbnd
    exact hmono.trans hbnd
  rcases hαβ with ⟨hα, hβ⟩ | hii
  · -- **Case i** (`α, β > 0`): `s, t ∈ H²`, so `f = s/t` has bounded characteristic (Theorem 1.2.1).
    exact Complex.isRationalSeries_of_boundedCharacteristic_intCoeffs
      (hasBoundedCharacteristic_of_quotient_summable hs ht hft
        (hsummable hα hs2) (hsummable hβ ht2)) hfp hint
  · -- **Case ii** (`α = 0 < 1 < β`, or symmetrically `1 < α, β = 0`): the multiplier-determinant
    -- argument. Normalise `t₀ = 1` via `uvSetup`'s constant `c`, then apply `rational_case_ii`.
    obtain ⟨c, -, -, hdet⟩ := uvSetup hfp hs ht hft
    have hblkeq : ∀ (w : ℕ → ℂ) (n : ℕ), ∑ m ∈ Finset.Ico n (2 * n), ‖c * w m‖ ^ 2
        = ‖c‖ ^ 2 * ∑ m ∈ Finset.Ico n (2 * n), ‖w m‖ ^ 2 :=
      fun w n => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by rw [norm_mul, mul_pow])
    exact rational_case_ii hint hdet hii
      ((hs2.const_mul_left (‖c‖ ^ 2)).congr'
        (Filter.Eventually.of_forall fun n => (hblkeq sc n).symm) (EventuallyEq.refl _ _))
      ((ht2.const_mul_left (‖c‖ ^ 2)).congr'
        (Filter.Eventually.of_forall fun n => (hblkeq tc n).symm) (EventuallyEq.refl _ _))

/-- **Corollary** (Bertin, deduced from Theorem 1.2.2 by taking `α = 0` and `β > 1`). Let `f` be
meromorphic on `D(0,1)` with no pole at `0` and **integer** Taylor coefficients `a` at `0`. Suppose
`f = s / t` where:

* `t` is a **polynomial** with complex coefficients — equivalently, its Taylor coefficients `tc` are
  eventually zero (`htpoly`); and
* `s` is analytic on `D(0,1)` with `s = ∑ sₙ zⁿ` (`hs`), whose doubling-block `ℓ²` sums vanish,
  `∑_{m=n}^{2n-1} |sₘ|² = o(1)` (`hs1`).

Then `f` is a rational function (its Taylor series is an `IsRationalSeries`).

This is the `α = 0`, `β > 1` corner of Theorem 1.2.2's admissible region. The numerator hypothesis
`o(1)` is exactly the `α = 0` instance of `o(n^{-α})` (since `n^{-0} = 1`). A polynomial denominator
has *eventually zero* coefficients, so its doubling-block sums are eventually `0`, hence `o(n^{-β})`
for every `β`; we discharge the `β > 1` slot with `β = 2`. -/
@[category research solved, AMS 30, ref "Ber92"]
theorem isRationalSeries_of_polynomialDenom_blockNormSq_o1
    {f s t : ℂ → ℂ} {a sc tc : ℕ → ℂ} {ρ : ENNReal}
    (hfp : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 ρ)
    (hint : ∀ n, ∃ m : ℤ, a n = (m : ℂ))
    (hs : HasFPowerSeriesOnBall s (FormalMultilinearSeries.ofScalars ℂ sc) 0 1)
    (ht : HasFPowerSeriesOnBall t (FormalMultilinearSeries.ofScalars ℂ tc) 0 1)
    (hft : ∀ z ∈ Metric.ball (0 : ℂ) 1, t z ≠ 0 → f z = s z / t z)
    (htpoly : ∃ N, ∀ n, N ≤ n → tc n = 0)
    (hs1 : (fun n => ∑ m ∈ Finset.Ico n (2 * n), ‖sc m‖ ^ 2) =o[atTop] fun _ => (1 : ℝ)) :
    IsRationalSeries (PowerSeries.mk a) := by
  apply isRationalSeries_of_quotient_blockNormSq_littleO hfp hint hs ht hft
    (α := 0) (β := 2) (Or.inr (Or.inl ⟨rfl, by norm_num⟩))
  · -- numerator: `o(1) = o(n^{-0})` since `n^{-0} = 1`
    have h0 : (fun n : ℕ => (n : ℝ) ^ (-(0 : ℝ))) = fun _ => (1 : ℝ) := by
      funext n; rw [neg_zero, Real.rpow_zero]
    rw [h0]; exact hs1
  · -- denominator: a polynomial has eventually-zero doubling blocks, hence `o(n^{-2})`
    obtain ⟨N, hN⟩ := htpoly
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [eventually_ge_atTop N] with n hn
    have hz : ∑ m ∈ Finset.Ico n (2 * n), ‖tc m‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun m hm => by
        rw [Finset.mem_Ico] at hm; simp [hN m (le_trans hn hm.1)]
    rw [hz, norm_zero]
    exact mul_nonneg hc.le (norm_nonneg _)
