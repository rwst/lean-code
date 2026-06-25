/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Decomposition
import CC.Parity
import SRS.ArcticInterpretation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The two-semiring bridge: from density to worst-case certificates (Ter76; YAH; KW09)

This file begins **Report B3, item 6** — making explicit the bridge between the two semiring views of
a Collatz orbit. The same combinatorial datum — the **parity vector** `V k n` of the length-`k` orbit
of `n` under the compact map `T` (`CC.V`), equivalently the odd-step count
`num_odd_steps k n` — controls two dual evaluations:

* **`(ℝ, +, ×)` — the density side.** The multiplicative coefficient
  `C k n = 3^{num_odd_steps k n} / 2^k` (`CC.C`) is the factor by which the orbit scales
  `n` (`linear_decomposition' : T_iter j n = C j n · n + E j n`). Its long-run behaviour is the
  Terras–Lagarias drift: along almost every orbit the ones-ratio `q/k → 1/2`, giving
  `C ≈ (√3/2)^k → 0`. This is the world of *density* theorems ([Ter76]).
* **`(ℝ ∪ {−∞}, max, +)` — the certificate side.** The arctic / max–plus semiring
  (`Arctic ℝ = ℝ ∪ {−∞}`, `SRS.ArcticInterpretation`) is where YAH-style worst-case termination
  certificates live ([YAH], [KW09]). The additive path-weight of the orbit is
  `tropWeight k n = num_odd_steps k n · log 3 − k · log 2`.

The semiring isomorphism `log : (ℝ_{>0}, ×) ≃ (ℝ, +)` turns the first into the second:

> **Bridge** (`tropWeight_eq_log_C`): `tropWeight k n = log (C k n)`.

So the `(max, +)` path-weight is *literally the logarithm* of the `(+, ×)` coefficient — the two
semiring pictures are one object seen through `log`. Everything else is a corollary read off the
sign of this quantity, with the threshold ratio

> `criticalRatio = log 2 / log 3 ≈ 0.6309`.

## Contents

* `tropWeight`, `arcticWeight`, `criticalRatio` — the tropical path-weight (in `ℝ` and in the SRS
  arctic carrier `Arctic ℝ`) and the contraction threshold.
* `tropWeight_eq_log_C` — **the bridge**: tropical weight `=` `log` of the density coefficient.
* `C_lt_one_iff_tropWeight_neg` / `C_lt_one_iff_arcticWeight_neg` — **contraction = negative weight**:
  the orbit contracts (`C < 1`) iff its tropical weight is negative (in `ℝ`, resp. below `⊥`'s
  successor `0` in the arctic order).
* `tropWeight_neg_iff_ratio` / `C_lt_one_iff_onesRatio` — **the threshold dictionary**: contraction
  iff the ones-ratio `num_odd_steps k n / k` (= `onesRatio (V k n)`, the Parity.lean datum) is below
  `criticalRatio`.
* `half_lt_criticalRatio`, `criticalRatio_lt_one` — `1/2 < criticalRatio < 1`: the Terras a.e.
  ones-ratio `1/2` sits strictly below the threshold, so almost every orbit contracts — the density
  side — while the certificate side must control the worst case up to the threshold.

## References
* [Ter76] Terras. *A stopping time problem on the positive integers.* Acta Arith. 30 (1976), 241–252.
* [YAH] Yolcu, Aaronson, Heule. *An Automated Approach to the Collatz Conjecture.* arXiv:2105.14697.
* [KW09] Koprowski, Waldmann. *Max/plus tree automata for termination of term rewriting.*
  Acta Cybernetica 19.2 (2009), 357–392.
-/

namespace CC.SRSBridge

open CC StringRewriting.ArcticInterpretation

/-! ### The threshold and the tropical path-weight -/

/-- The **contraction threshold** `ρ* = log 2 / log 3 ≈ 0.6309`. An orbit of the compact map `T`
contracts over a window exactly when its ones-ratio (fraction of odd steps) stays below `ρ*`. -/
@[category API, AMS 11 68, ref "YAH", group "two_semiring_bridge"]
noncomputable def criticalRatio : ℝ := Real.log 2 / Real.log 3

/-- The **tropical `(max, +)` path-weight** of the length-`k` orbit of `n`: each of the
`num_odd_steps k n` odd (tripling) steps contributes `log 3` and each of the `k` halvings contributes
`−log 2`, so the additive weight is `num_odd_steps k n · log 3 − k · log 2`. -/
@[category API, AMS 11 68, ref "YAH" "KW09", group "two_semiring_bridge"]
noncomputable def tropWeight (k n : ℕ) : ℝ :=
  (num_odd_steps k n : ℝ) * Real.log 3 - (k : ℝ) * Real.log 2

/-- The tropical path-weight as an element of the **arctic carrier** `Arctic ℝ = ℝ ∪ {−∞}` used by
the SRS arctic matrix interpretations (`SRS.ArcticInterpretation`). It is always finite here — the
`−∞` value is reserved for absent transitions in a genuine arctic matrix. -/
@[category API, AMS 11 68, ref "KW09", group "two_semiring_bridge"]
noncomputable def arcticWeight (k n : ℕ) : Arctic ℝ := (tropWeight k n : ℝ)

/-! ### The parity vector is the ones-count (link to `Parity.lean`) -/

/-- The parity vector `V k n` rewritten as a `List.range` map — the `Fin`-indexing is cosmetic. -/
@[category API, AMS 11, group "two_semiring_bridge"]
lemma V_eq_range_map (k n : ℕ) :
    V k n = (List.range k).map (fun i => decide (X (T_iter i n) = 1)) := by
  rw [V, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- Counting the `true`s in a `{0,1}`-valued `range`-map is summing the values. -/
@[category API, AMS 11, group "two_semiring_bridge"]
lemma count_true_range_map (k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) :
    List.count true ((List.range k).map (fun i => decide (f i = 1)))
      = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih, Finset.sum_range_succ]
    have hk := hf k
    rcases (show f k = 0 ∨ f k = 1 by omega) with h | h <;> simp [h]

/-- The number of ones `q (V k n)` of the parity vector **is** the odd-step count
`num_odd_steps k n`: the parity-vector infrastructure of `Parity.lean` and the Terras odd-step
counter of `Terras.lean` record the same datum. -/
@[category research solved, AMS 11, ref "Ter76", group "two_semiring_bridge"]
lemma q_V (k n : ℕ) : q (V k n) = num_odd_steps k n := by
  unfold q num_odd_steps
  rw [V_eq_range_map]
  exact count_true_range_map k (fun i => X (T_iter i n)) (fun i => by rw [X_eq_mod]; omega)

/-- The ones-ratio of the parity vector is the odd-step density `num_odd_steps k n / k`. -/
@[category API, AMS 11, group "two_semiring_bridge"]
lemma onesRatio_V (k n : ℕ) : onesRatio (V k n) = (num_odd_steps k n : ℚ) / (k : ℚ) := by
  unfold onesRatio size
  rw [V_length, q_V]

/-! ### The density coefficient over `ℝ` -/

/-- The density coefficient `C k n` cast to `ℝ`: `C k n = 3^{num_odd_steps k n} / 2^k`. -/
@[category API, AMS 11, group "two_semiring_bridge"]
lemma C_cast (k n : ℕ) : ((C k n : ℝ)) = (3 : ℝ) ^ num_odd_steps k n / (2 : ℝ) ^ k := by
  rw [C]; push_cast; ring

/-- The density coefficient is strictly positive. -/
@[category API, AMS 11, group "two_semiring_bridge"]
lemma C_pos (k n : ℕ) : (0 : ℝ) < (C k n : ℝ) := by
  rw [C_cast]; positivity

/-! ### The bridge -/

/-- **The two-semiring bridge** ([Ter76] density side ↔ [YAH] certificate side). The tropical
`(max, +)` path-weight of an orbit equals the logarithm of its `(+, ×)` density coefficient:
`tropWeight k n = log (C k n)`. The two semiring evaluations of the parity vector are one object
related by the isomorphism `log : (ℝ_{>0}, ×) ≃ (ℝ, +)`. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
theorem tropWeight_eq_log_C (k n : ℕ) :
    tropWeight k n = Real.log ((C k n : ℝ)) := by
  rw [tropWeight, C_cast, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]

/-- **Contraction = negative weight.** The orbit contracts (`C k n < 1`, the density obstruction is
absent) iff its tropical path-weight is negative. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
theorem C_lt_one_iff_tropWeight_neg (k n : ℕ) :
    (C k n : ℝ) < 1 ↔ tropWeight k n < 0 := by
  rw [tropWeight_eq_log_C]
  exact (Real.log_neg_iff (C_pos k n)).symm

/-- The arctic-carrier form of contraction: `C k n < 1` iff the arctic weight is below `0`
(`= ⊥`'s successor) in the arctic order of `Arctic ℝ`. -/
@[category research solved, AMS 11 68, ref "KW09", group "two_semiring_bridge"]
theorem C_lt_one_iff_arcticWeight_neg (k n : ℕ) :
    (C k n : ℝ) < 1 ↔ arcticWeight k n < (0 : Arctic ℝ) := by
  rw [C_lt_one_iff_tropWeight_neg, arcticWeight]
  norm_cast

/-! ### The threshold dictionary -/

/-- **The threshold dictionary.** For a nonempty window the orbit's tropical weight is negative iff
its ones-ratio (odd-step density) is below `criticalRatio = log 2 / log 3`. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
theorem tropWeight_neg_iff_ratio {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    tropWeight k n < 0 ↔ (num_odd_steps k n : ℝ) / k < criticalRatio := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [tropWeight, criticalRatio, div_lt_div_iff₀ hk' hlog3]
  constructor <;> intro h <;> nlinarith [mul_comm (Real.log 2) (k : ℝ)]

/-- **Contraction in terms of the Parity.lean ones-ratio.** `C k n < 1` iff `onesRatio (V k n)` is
below the threshold — the explicit density ↔ certificate dictionary on the shared parity vector. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
theorem C_lt_one_iff_onesRatio {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (C k n : ℝ) < 1 ↔ ((onesRatio (V k n) : ℚ) : ℝ) < criticalRatio := by
  rw [C_lt_one_iff_tropWeight_neg, tropWeight_neg_iff_ratio hk, onesRatio_V]
  push_cast
  rfl

/-! ### Where the Terras a.e. ratio sits -/

/-- The Terras a.e. ones-ratio `1/2` lies strictly below the contraction threshold: `1/2 < ρ*`.
Hence almost every orbit contracts — the density side of the bridge. -/
@[category research solved, AMS 11, ref "Ter76", group "two_semiring_bridge"]
theorem half_lt_criticalRatio : (1 : ℝ) / 2 < criticalRatio := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [criticalRatio, div_lt_div_iff₀ (by norm_num) hlog3]
  nlinarith [h34, h4]

/-- The threshold is below `1`: `ρ* < 1` (since `log 2 < log 3`). -/
@[category API, AMS 11, group "two_semiring_bridge"]
theorem criticalRatio_lt_one : criticalRatio < 1 := by
  rw [criticalRatio, div_lt_one (Real.log_pos (by norm_num))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

end CC.SRSBridge
