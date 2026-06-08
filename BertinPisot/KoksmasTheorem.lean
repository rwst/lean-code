/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import BertinPisot.UniformDistribution
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Koksma's theorem (Bertin §4.5)

Koksma's metric theorem on uniform distribution modulo one of `(fₙ(t))` for almost every `t`
(**Theorem 4.5.1**, `koksma_theorem_4_5_1`, cited), together with its two preliminary lemmas.

* **Lemma 1** (`exists_strictMono_ratio_tendsto_one_summable`): from a strictly increasing sequence
  of (positive) integers `(Nᵥ)` with `N_{ν+1}/Nᵥ → 1` one can extract a subsequence `(N_{νₖ})` that
  keeps the ratio property `N_{νₖ₊₁}/N_{νₖ} → 1` **and** has a convergent reciprocal series
  `Σ 1/N_{νₖ}`. We model the positive integer sequence as `N : ℕ → ℕ` with `StrictMono N` and
  `0 < N 0`, and the extraction as a strictly monotone reindexing `φ : ℕ → ℕ` (`νₖ = φ k`).

* **Lemma 2** (`exists_monotone_tendsto_atTop_summable_mul`): for a convergent series of positive
  reals `Σ uₙ` there is an increasing sequence `γₙ → +∞` such that `Σ uₙ γₙ` still converges
  (a convergence-preserving "speed-up" of the series).

**Construction.** Bertin's proof keeps, in each interval `[m², (m+1)²]`, the smallest and largest
terms of `(Nᵥ)`. We use an equivalent but reindexing-free variant — *first passage to the next
square*: from `N_{φ k}` jump to the first index whose value reaches `(⌊√(N_{φ k})⌋ + 1)²`. This is
strictly monotone by construction, gives `N_{φ k} ≥ k²` directly (so `Σ 1/N_{φ k} ≤ Σ 1/k² < ∞`),
and the ratio limit follows from the squeeze
`1 ≤ N_{φ(k+1)}/N_{φ k} ≤ (N_{φ(k+1)}/N_{φ(k+1)−1}) · ((⌊√(N_{φ k})⌋+1)/⌊√(N_{φ k})⌋)²`,
whose right-hand side tends to `1` (the first factor by the hypothesis at the diverging index
`φ(k+1)−1`, the second since `⌊√(N_{φ k})⌋ ≥ k → ∞`).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.5.
-/

namespace Bertin

open Filter Topology MeasureTheory

/-- **Lemma 1** (Bertin, §4.5, preceding Koksma's theorem). Let `(Nᵥ)` be a strictly increasing
sequence of positive integers with `N_{ν+1}/Nᵥ → 1`. Then there is a strictly monotone reindexing
`φ` such that the subsequence `(N_{φ k})` still satisfies `N_{φ(k+1)}/N_{φ k} → 1` and the series
`Σ_k 1/N_{φ k}` converges. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem exists_strictMono_ratio_tendsto_one_summable (N : ℕ → ℕ) (hmono : StrictMono N)
    (hpos : 0 < N 0) (hratio : Tendsto (fun ν => (N (ν + 1) : ℝ) / (N ν)) atTop (𝓝 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => (N (φ (k + 1)) : ℝ) / (N (φ k))) atTop (𝓝 1) ∧
      Summable (fun k => (1 : ℝ) / (N (φ k))) := by
  have hposν : ∀ ν, 0 < N ν := fun ν => lt_of_lt_of_le hpos (hmono.monotone (Nat.zero_le ν))
  -- the "first passage": `step ν` is the first index whose value reaches the next square above `N ν`
  have hex : ∀ ν, ∃ μ, (Nat.sqrt (N ν) + 1) ^ 2 ≤ N μ := fun ν =>
    ⟨(Nat.sqrt (N ν) + 1) ^ 2, hmono.le_apply⟩
  set step : ℕ → ℕ := fun ν => Nat.find (hex ν) with hstepdef
  have hstep_spec : ∀ ν, (Nat.sqrt (N ν) + 1) ^ 2 ≤ N (step ν) := fun ν => Nat.find_spec (hex ν)
  have hstep_gt : ∀ ν, ν < step ν := fun ν =>
    hmono.lt_iff_lt.mp (lt_of_lt_of_le (Nat.lt_succ_sqrt' (N ν)) (hstep_spec ν))
  have hstep_min : ∀ ν μ, μ < step ν → N μ < (Nat.sqrt (N ν) + 1) ^ 2 := fun ν μ hμ =>
    not_le.mp (Nat.find_min (hex ν) hμ)
  -- the subsequence indices `φ k = stepᵏ 0`
  set φ : ℕ → ℕ := fun k => step^[k] 0 with hφdef
  have hφsucc : ∀ k, φ (k + 1) = step (φ k) := fun k => Function.iterate_succ_apply' step k 0
  have hφmono : StrictMono φ :=
    strictMono_nat_of_lt_succ (fun k => by rw [hφsucc]; exact hstep_gt (φ k))
  -- `√(N_{φ k}) ≥ k`, hence `N_{φ k} ≥ k²`
  have hsqrt : ∀ k, k ≤ Nat.sqrt (N (φ k)) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        rw [hφsucc]
        calc k + 1 ≤ Nat.sqrt (N (φ k)) + 1 := Nat.add_le_add_right ih 1
          _ = Nat.sqrt ((Nat.sqrt (N (φ k)) + 1) ^ 2) := (Nat.sqrt_eq' _).symm
          _ ≤ Nat.sqrt (N (step (φ k))) := Nat.sqrt_le_sqrt (hstep_spec (φ k))
  have hNk : ∀ k, k ^ 2 ≤ N (φ k) := fun k =>
    le_trans (Nat.pow_le_pow_left (hsqrt k) 2) (Nat.sqrt_le' _)
  have hφpos : ∀ k, 0 < φ (k + 1) := fun k => by
    have := hφmono (Nat.succ_pos k); rwa [show φ 0 = 0 from rfl] at this
  refine ⟨φ, hφmono, ?_, ?_⟩
  · -- ratio `N_{φ(k+1)}/N_{φ k} → 1`, by a squeeze between `1` and a product tending to `1`
    have hsqrt_atTop : Tendsto (fun k => ((Nat.sqrt (N (φ k))) : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun k => by exact_mod_cast hsqrt k) tendsto_natCast_atTop_atTop
    -- first factor: `N_{φ(k+1)}/N_{φ(k+1)−1} → 1` (the hypothesis at the diverging index `φ(k+1)−1`)
    have hρ : Tendsto (fun k => (N (φ (k + 1)) : ℝ) / (N (φ (k + 1) - 1))) atTop (𝓝 1) := by
      have hJ : Tendsto (fun k => φ (k + 1) - 1) atTop atTop := by
        apply tendsto_atTop_mono (fun k => ?_) tendsto_id
        show k ≤ φ (k + 1) - 1
        have h1 : k ≤ φ k := hφmono.le_apply
        have h2 : φ k < φ (k + 1) := hφmono (Nat.lt_succ_self k)
        omega
      refine (hratio.comp hJ).congr (fun k => ?_)
      simp only [Function.comp_apply]
      rw [Nat.sub_add_cancel (hφpos k)]
    -- second factor: `((√(N_{φ k})+1)/√(N_{φ k}))² → 1`
    have hw : Tendsto
        (fun k => (((Nat.sqrt (N (φ k)) : ℝ) + 1) / (Nat.sqrt (N (φ k)))) ^ 2) atTop (𝓝 1) := by
      have hinv : Tendsto (fun k => ((Nat.sqrt (N (φ k)) : ℝ))⁻¹) atTop (𝓝 0) :=
        hsqrt_atTop.inv_tendsto_atTop
      have h1 : Tendsto (fun k => ((Nat.sqrt (N (φ k)) : ℝ) + 1) / (Nat.sqrt (N (φ k)))) atTop
          (𝓝 1) := by
        have h2 : Tendsto (fun k => 1 + ((Nat.sqrt (N (φ k)) : ℝ))⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hinv
        rw [add_zero] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hms : (0 : ℝ) < Nat.sqrt (N (φ k)) := by
          have : 1 ≤ Nat.sqrt (N (φ k)) := le_trans hk (hsqrt k)
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        field_simp
      simpa using h1.pow 2
    have hu : Tendsto (fun k => (N (φ (k + 1)) : ℝ) / (N (φ (k + 1) - 1)) *
        (((Nat.sqrt (N (φ k)) : ℝ) + 1) / (Nat.sqrt (N (φ k)))) ^ 2) atTop (𝓝 1) := by
      have := hρ.mul hw; simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Filter.Eventually.of_forall (fun k => ?_)) ?_
    · -- lower bound `1 ≤ N_{φ(k+1)}/N_{φ k}`
      have hb : (0 : ℝ) < N (φ k) := by exact_mod_cast hposν (φ k)
      rw [one_le_div₀ hb]
      exact_mod_cast (hmono (hφmono (Nat.lt_succ_self k))).le
    · -- upper bound, eventually
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hms1 : 1 ≤ Nat.sqrt (N (φ k)) := le_trans hk (hsqrt k)
      have hms : (0 : ℝ) < Nat.sqrt (N (φ k)) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hms1
      have hsq : (0 : ℝ) < ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2 := by positivity
      have hpred : (0 : ℝ) < N (φ (k + 1) - 1) := by exact_mod_cast hposν (φ (k + 1) - 1)
      have hNφk1 : (0 : ℝ) ≤ N (φ (k + 1)) := by positivity
      have hlow : ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2 ≤ N (φ k) := by
        exact_mod_cast Nat.sqrt_le' (N (φ k))
      have hpred_lt : (N (φ (k + 1) - 1) : ℝ) ≤ ((Nat.sqrt (N (φ k)) : ℝ) + 1) ^ 2 := by
        have hlt : φ (k + 1) - 1 < step (φ k) := by
          rw [← hφsucc k]; exact Nat.sub_lt (hφpos k) Nat.one_pos
        exact_mod_cast (hstep_min (φ k) (φ (k + 1) - 1) hlt).le
      have hpredne : (N (φ (k + 1) - 1) : ℝ) ≠ 0 := hpred.ne'
      have hsqne : ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2 ≠ 0 := hsq.ne'
      calc (N (φ (k + 1)) : ℝ) / (N (φ k))
          ≤ (N (φ (k + 1)) : ℝ) / ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2 :=
            div_le_div_of_nonneg_left hNφk1 hsq hlow
        _ = (N (φ (k + 1)) : ℝ) / (N (φ (k + 1) - 1)) *
              ((N (φ (k + 1) - 1) : ℝ) / ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2) := by field_simp
        _ ≤ (N (φ (k + 1)) : ℝ) / (N (φ (k + 1) - 1)) *
              (((Nat.sqrt (N (φ k)) : ℝ) + 1) ^ 2 / ((Nat.sqrt (N (φ k)) : ℝ)) ^ 2) := by gcongr
        _ = (N (φ (k + 1)) : ℝ) / (N (φ (k + 1) - 1)) *
              (((Nat.sqrt (N (φ k)) : ℝ) + 1) / (Nat.sqrt (N (φ k)))) ^ 2 := by rw [div_pow]
  · -- summability, by comparison with the convergent `2`-series via `N_{φ k} ≥ k²`
    have hg : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa using h
    apply (summable_nat_add_iff 1).mp
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hg
    have h1 : ((k : ℝ) + 1) ^ 2 ≤ N (φ (k + 1)) := by
      have hcast : (((k + 1) ^ 2 : ℕ) : ℝ) ≤ ((N (φ (k + 1)) : ℕ) : ℝ) := by exact_mod_cast hNk (k + 1)
      push_cast at hcast; linarith
    exact one_div_le_one_div_of_le (by positivity) h1

/-- **Lemma 2** (Bertin, §4.5, preceding Koksma's theorem). Let `(uₙ)` be a sequence of positive
reals with `Σ uₙ` convergent. Then there is an increasing sequence `(γₙ)` with `γₙ → +∞` such that
`Σ uₙ γₙ` still converges.

**Construction.** With `S = Σ uₙ > 0` and the tails `Rₙ = Σ_{k ≥ n} uₖ = S − Σ_{k<n} uₖ` (so
`Rₙ ↓ 0`, `R₀ = S`, `Rₙ − Rₙ₊₁ = uₙ`), set `γₙ = √S / (√Rₙ + √Rₙ₊₁)`. This is increasing (`Rₙ`
decreases) with `γₙ → +∞` (`Rₙ → 0`), and the key telescoping
`uₙ γₙ = √S (√Rₙ − √Rₙ₊₁)` gives bounded partial sums
`Σ_{k<n} uₖ γₖ = √S (√R₀ − √Rₙ) = √S(√S − √Rₙ) ≤ S`, so `Σ uₙ γₙ` converges. (Bertin's printed
partial sum `√S(S − √Rₙ)` is a misprint for `√S(√S − √Rₙ)`; only boundedness matters.) -/
@[category research solved, AMS 11, ref "Ber92"]
theorem exists_monotone_tendsto_atTop_summable_mul (u : ℕ → ℝ) (hpos : ∀ n, 0 < u n)
    (hu : Summable u) :
    ∃ γ : ℕ → ℝ, Monotone γ ∧ Tendsto γ atTop atTop ∧ Summable (fun n => u n * γ n) := by
  set S : ℝ := ∑' n, u n with hSdef
  have hSpos : 0 < S := by
    have h := Summable.sum_le_tsum (Finset.range 1) (fun i _ => (hpos i).le) hu
    rw [Finset.sum_range_one] at h; exact lt_of_lt_of_le (hpos 0) h
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  -- the tails `Rₙ = S − Σ_{k<n} uₖ`
  set R : ℕ → ℝ := fun n => S - ∑ k ∈ Finset.range n, u k with hRdef
  have hRsucc : ∀ n, R n - R (n + 1) = u n := by
    intro n; simp only [hRdef, Finset.sum_range_succ]; ring
  have hR0 : R 0 = S := by simp [hRdef]
  have hRnonneg : ∀ n, 0 ≤ R n := fun n =>
    sub_nonneg.mpr (Summable.sum_le_tsum (Finset.range n) (fun i _ => (hpos i).le) hu)
  have hRpos : ∀ n, 0 < R n := fun n => by
    have h := Summable.sum_le_tsum (Finset.range (n + 1)) (fun i _ => (hpos i).le) hu
    rw [Finset.sum_range_succ] at h
    simp only [hRdef]; linarith [hpos n]
  have hRanti : Antitone R := antitone_nat_of_succ_le (fun n => by linarith [hRsucc n, (hpos n).le])
  have hRtendsto : Tendsto R atTop (𝓝 0) := by
    have h := hu.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun n => S - ∑ k ∈ Finset.range n, u k) atTop (𝓝 (S - S)) :=
      tendsto_const_nhds.sub h
    rw [sub_self] at h2; exact h2
  -- `√Rₙ` is positive, antitone, and tends to `0`
  have hsR_pos : ∀ n, 0 < Real.sqrt (R n) := fun n => Real.sqrt_pos.mpr (hRpos n)
  have hsR_anti : Antitone (fun n => Real.sqrt (R n)) := fun a b hab => Real.sqrt_le_sqrt (hRanti hab)
  have hsR_tendsto : Tendsto (fun n => Real.sqrt (R n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hRtendsto
    rwa [Real.sqrt_zero] at this
  set γ : ℕ → ℝ := fun n => Real.sqrt S / (Real.sqrt (R n) + Real.sqrt (R (n + 1))) with hγdef
  have hdenom_pos : ∀ n, 0 < Real.sqrt (R n) + Real.sqrt (R (n + 1)) := fun n => by
    have := hsR_pos n; have := hsR_pos (n + 1); linarith
  refine ⟨γ, ?_, ?_, ?_⟩
  · -- `γ` increasing: the denominator `√Rₙ + √Rₙ₊₁` is antitone and positive
    intro a b hab
    simp only [hγdef]
    apply div_le_div_of_nonneg_left hsS.le (hdenom_pos b)
    have h1 := hsR_anti hab
    have h2 := hsR_anti (show a + 1 ≤ b + 1 by omega)
    simp only at h1 h2; linarith
  · -- `γ → +∞`: the denominator tends to `0` from above, so its reciprocal diverges
    have hdenom_tendsto :
        Tendsto (fun n => Real.sqrt (R n) + Real.sqrt (R (n + 1))) atTop (𝓝 0) := by
      have hshift : Tendsto (fun n => Real.sqrt (R (n + 1))) atTop (𝓝 0) :=
        hsR_tendsto.comp (tendsto_add_atTop_nat 1)
      have := hsR_tendsto.add hshift; rwa [add_zero] at this
    have hwithin : Tendsto (fun n => Real.sqrt (R n) + Real.sqrt (R (n + 1))) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdenom_tendsto
        (Filter.Eventually.of_forall hdenom_pos)
    have hinv : Tendsto (fun n => (Real.sqrt (R n) + Real.sqrt (R (n + 1)))⁻¹) atTop atTop :=
      hwithin.inv_tendsto_nhdsGT_zero
    refine (Tendsto.const_mul_atTop hsS hinv).congr (fun n => ?_)
    simp only [hγdef, div_eq_mul_inv]
  · -- summability: bounded partial sums via the telescoping `uₙ γₙ = √S (√Rₙ − √Rₙ₊₁)`
    apply summable_of_sum_range_le (c := Real.sqrt S * Real.sqrt S)
    · intro n
      exact mul_nonneg (hpos n).le (by simp only [hγdef]; positivity)
    · intro n
      have hterm : ∀ i, u i * γ i = Real.sqrt S * (Real.sqrt (R i) - Real.sqrt (R (i + 1))) := by
        intro i
        have hd : Real.sqrt (R i) + Real.sqrt (R (i + 1)) ≠ 0 := (hdenom_pos i).ne'
        have hsq1 : Real.sqrt (R i) ^ 2 = R i := Real.sq_sqrt (hRnonneg i)
        have hsq2 : Real.sqrt (R (i + 1)) ^ 2 = R (i + 1) := Real.sq_sqrt (hRnonneg (i + 1))
        have hui : u i = Real.sqrt (R i) ^ 2 - Real.sqrt (R (i + 1)) ^ 2 := by
          rw [hsq1, hsq2]; linarith [hRsucc i]
        simp only [hγdef]; rw [hui]; field_simp; ring
      simp only [hterm]
      rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i => Real.sqrt (R i)) n, hR0]
      nlinarith [hsS.le, Real.sqrt_nonneg (R n)]

/-! ### Theorem 4.5.1 — Koksma's metric theorem -/

/-- **Theorem 4.5.1** (Koksma), in the **condition (ii)** form. Let `(fₙ)` be functions with
continuous derivative `f'ₙ` on `[a, b]`, and set `F_{m,n} = fₘ − fₙ`. Suppose that for every pair
`m ≠ n`:
* (i) the derivative `F'_{m,n} = f'ₘ − f'ₙ` is monotone (increasing or decreasing) and never `0` on
  `[a, b]`;
* (ii) there is an increasing integer sequence `(Nᵥ)` with `N_{ν+1}/Nᵥ → 1` such that the series
  `Σ_ν A_{Nᵥ}` converges, where
  `A_N = (1/N²) Σ_{n=2}^{N} Σ_{m=1}^{n-1} max(1/|F'_{m,n}(a)|, 1/|F'_{m,n}(b)|)`.

Then `(fₙ(t))` is uniformly distributed modulo one for **almost every** `t ∈ [a, b]`.

The proof (Koksma) combines the two preliminary lemmas of this file — the subsequence extraction
`exists_strictMono_ratio_tendsto_one_summable` (Lemma 1) and the convergence-factor lemma
`exists_monotone_tendsto_atTop_summable_mul` (Lemma 2) — with a Borel–Cantelli / second-moment
(Weyl-sum variance) estimate for the exceptional set; the metric machinery is not available at this
level, so the theorem is recorded as a cited result. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses exists_strictMono_ratio_tendsto_one_summable
    exists_monotone_tendsto_atTop_summable_mul]
axiom koksma_theorem_4_5_1 (a b : ℝ) (hab : a < b) (f f' : ℕ → ℝ → ℝ)
    (hderiv : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (f n) (f' n t) t)
    (hcont : ∀ n, ContinuousOn (f' n) (Set.Icc a b))
    (hmono : ∀ m n, m ≠ n →
      MonotoneOn (fun t => f' m t - f' n t) (Set.Icc a b) ∨
        AntitoneOn (fun t => f' m t - f' n t) (Set.Icc a b))
    (hnonzero : ∀ m n, m ≠ n → ∀ t ∈ Set.Icc a b, f' m t - f' n t ≠ 0)
    (hii : ∃ Nν : ℕ → ℕ, StrictMono Nν ∧ 0 < Nν 0 ∧
      Tendsto (fun ν => (Nν (ν + 1) : ℝ) / (Nν ν)) atTop (𝓝 1) ∧
      Summable (fun ν => (1 / (Nν ν : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc 2 (Nν ν), ∑ m ∈ Finset.Icc 1 (n - 1),
          max (1 / |f' m a - f' n a|) (1 / |f' m b - f' n b|))) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), UniformlyDistributedModOne (fun n => f n t)

/-- **Theorem 4.5.1** (Koksma), in the **condition (iii)** form — the version most often used in
practice. Same hypotheses as `koksma_theorem_4_5_1` except that the subsequence-series condition (ii)
is replaced by the simpler uniform lower bound

* (iii) there is a real `K > 0` with `|F'_{m,n}(t)| ≥ K` for all `t ∈ [a, b]` and all `m ≠ n`,

`K` being independent of the pair `(m, n)`. (A pair-dependent `K` would already follow from
continuity and condition (i)'s non-vanishing on the compact interval `[a, b]`, so it is the
*uniformity* over pairs that gives content here — the classical Koksma hypothesis.) The conclusion is
the same: `(fₙ(t))` is uniformly distributed modulo one for almost every `t ∈ [a, b]`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses exists_strictMono_ratio_tendsto_one_summable
    exists_monotone_tendsto_atTop_summable_mul]
axiom koksma_theorem_4_5_1_condition_iii (a b : ℝ) (hab : a < b) (f f' : ℕ → ℝ → ℝ)
    (hderiv : ∀ n, ∀ t ∈ Set.Icc a b, HasDerivAt (f n) (f' n t) t)
    (hcont : ∀ n, ContinuousOn (f' n) (Set.Icc a b))
    (hmono : ∀ m n, m ≠ n →
      MonotoneOn (fun t => f' m t - f' n t) (Set.Icc a b) ∨
        AntitoneOn (fun t => f' m t - f' n t) (Set.Icc a b))
    (hnonzero : ∀ m n, m ≠ n → ∀ t ∈ Set.Icc a b, f' m t - f' n t ≠ 0)
    (hiii : ∃ K : ℝ, 0 < K ∧ ∀ m n, m ≠ n → ∀ t ∈ Set.Icc a b, K ≤ |f' m t - f' n t|) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), UniformlyDistributedModOne (fun n => f n t)

end Bertin
