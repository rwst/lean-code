/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DistributionModOne.Problem10_6
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud's Problem 10.6 — basic vocabulary

Problem 10.6 [Bug12, Ch. 10] asks for a *very rapidly increasing* sequence `(mₙ)` of positive
integers with `(ξ mₙ)` dense modulo one for every irrational `ξ`.  Katz's term for the density
property is **universally densifying** (UD); Bugeaud's own notation [Bug09] for its failure set
is `E_m`, so UD is `E_m = ∅`.

This file fixes the vocabulary shared by the rest of the `BB6` root:

* `BB6.UniversallyDensifying` — the density property, in the same `AddCircle (1 : ℝ)` shape the
  ported `DistributionModOne.Problem10_6` already uses, so the two files compose without a bridge;
* `BB6.HasLongRuns` — the hypothesis of Lemma R (`BB6/Runs.lean`): `A = {mₙ}` contains arbitrarily
  long runs of *consecutive* integers;
* `BB6.countingFn` — the counting function `π_A(N) = #(A ∩ [1,N])`, with the one lemma that makes
  it usable for a strictly increasing sequence (`countingFn_le`).

Two calibration facts also live here.  `BB6.not_dense_of_rat` is why the problem quantifies over
*irrational* `ξ` only: for rational `ξ` the orbit is finite, so it is never dense — the rationals
are unconditionally exceptional, for every sequence whatsoever.  And
`BB6.dimH_exceptional_eq_zero` records that a UD sequence has an exceptional set of Hausdorff
dimension zero, the input to the pinch (Theorem D₀, `BB6/Pinch.lean`).

Finally `BB6.eventually_log_le` and `BB6.tendsto_log_natCast` are the two asymptotic facts every
growth computation in this root reduces to (`BB6/AristotleSeq.lean`, `BB6/Readings.lean`): `log`
is dominated by every positive power, and `log n → ∞` along the naturals.

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
  - [Kat16] Katz, A. "Generalizations of Furstenberg's Diophantine result." arXiv:1607.00670.
-/

namespace BB6

open Filter Set

/-! ## The two predicates -/

/-- A sequence `m` of positive integers is **universally densifying** (UD) if `(ξ mₙ)` is dense
modulo one for every irrational `ξ`.  Equivalently, Bugeaud's exceptional set `E_m` [Bug09] is
empty.  The `AddCircle (1 : ℝ)` shape is deliberate and matches
`DistributionModOne.Problem10_6`: density of the fractional parts *in `ℝ`* would be vacuously
false, since `Int.fract` takes values in `[0,1)`. -/
@[category API, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6"]
def UniversallyDensifying (m : ℕ → ℕ) : Prop :=
  ∀ ξ : ℝ, Irrational ξ → Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))

/-- `m` **has long runs** if for every `L` some window of `L + 1` consecutive indices is mapped to
`L + 1` consecutive integers.  This is the hypothesis of Lemma R, and it is the exact opposite of
"rapidly increasing" *locally*: inside a run `mₙ₊₁ - mₙ = 1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def HasLongRuns (m : ℕ → ℕ) : Prop :=
  ∀ L : ℕ, ∃ a : ℕ, ∀ j ≤ L, m (a + j) = m a + j

/-! ## The rationals are unconditionally exceptional -/

/-- For a **rational** `ξ = q` the orbit `(q mₙ)` lives in the finite subgroup `(1/q.den)ℤ/ℤ` of
the circle, so it stays at distance `≥ 1/(2 q.den)` from the point `1/(2 q.den)` and is never
dense — whatever the sequence `m` is.  This is why Problem 10.6, and the definition of
`UniversallyDensifying`, quantify over irrational `ξ` only. -/
@[category test, AMS 11, ref "Bug12", group "bugeaud_10_6"]
theorem not_dense_of_rat (m : ℕ → ℕ) (q : ℚ) :
    ¬ Dense (Set.range fun n => (↑((q : ℝ) * m n) : AddCircle (1 : ℝ))) := by
  set d : ℕ := q.den with hd
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast q.pos
  intro hdense
  -- The witness point: half a step of the finite subgroup.
  obtain ⟨y, hy₁, hy₂⟩ :=
    Metric.dense_iff.1 hdense ((((1 : ℝ) / (2 * d) : ℝ) : AddCircle (1 : ℝ))) (1 / (2 * d))
      (by positivity)
  obtain ⟨n, rfl⟩ := hy₂
  rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hy₁
  -- Every orbit point is `k / d` with `k = q.num * m n` an integer, so the difference from
  -- `1 / (2d)` has odd numerator over `2d` and is `≥ 1/(2d)` away from every integer.
  obtain ⟨k, hkk⟩ : ∃ k : ℤ, (q : ℝ) * m n = (k : ℝ) / (d : ℝ) :=
    ⟨q.num * m n, by rw [hd, Rat.cast_def]; push_cast; ring⟩
  set r : ℤ := round ((q : ℝ) * m n - 1 / (2 * d)) with hr
  have hodd : (1 : ℤ) ≤ |2 * k - 1 - 2 * (r * d)| := by
    refine Int.one_le_abs (fun hcon => ?_)
    obtain ⟨s, hs⟩ : ∃ s : ℤ, s = r * d := ⟨_, rfl⟩
    rw [← hs] at hcon
    omega
  have hlb : 1 / (2 * (d : ℝ)) ≤ |(q : ℝ) * m n - 1 / (2 * d) - (r : ℝ)| := by
    have hrw : (q : ℝ) * m n - 1 / (2 * d) - (r : ℝ)
        = ((2 * k - 1 - 2 * (r * d) : ℤ) : ℝ) / (2 * (d : ℝ)) := by
      rw [hkk]; push_cast; field_simp
    rw [hrw, abs_div, abs_of_pos (show (0 : ℝ) < 2 * (d : ℝ) by positivity)]
    gcongr
    rw [← Int.cast_abs]
    exact_mod_cast hodd
  linarith

/-! ## The exceptional set of a UD sequence -/

/-- A UD sequence has exceptional set contained in `ℚ`, hence of Hausdorff dimension zero.  This
is one half of the pinch: [Pol79]/[Mat80] give dimension **one** for a lacunary sequence, so a UD
sequence cannot be lacunary (`BB6/Pinch.lean`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6"]
theorem dimH_exceptional_eq_zero {m : ℕ → ℕ} (h : UniversallyDensifying m) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 0 := by
  refine Set.Countable.dimH_zero (Set.Countable.mono (fun ξ hξ => ?_) (Set.countable_range
    ((↑) : ℚ → ℝ)))
  by_contra hξr
  exact hξ (h ξ (fun ⟨s, hs⟩ => hξr ⟨s, hs⟩))

/-! ## The counting function -/

/-- `countingFn m N = π_A(N) = #(A ∩ [0,N])` for `A = {mₙ}`.  The outer `Finset.range (N+1)` is
harmless for a strictly increasing `m`, since then `n ≤ mₙ`. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
def countingFn (m : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun n => m n ≤ N).card

/-- The counting function of a strictly increasing sequence is bounded by any index whose value
already exceeds `N`.  This is the only property of `countingFn` the sparsity theorem needs. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem countingFn_le {m : ℕ → ℕ} (hm : StrictMono m) {N M : ℕ} (h : N < m M) :
    countingFn m N ≤ M := by
  have hsub : ((Finset.range (N + 1)).filter fun n => m n ≤ N) ⊆ Finset.range M := by
    intro n hn
    rw [Finset.mem_filter] at hn
    refine Finset.mem_range.2 ?_
    by_contra hcon
    exact absurd (hm.monotone (not_lt.1 hcon)) (not_le.2 (lt_of_le_of_lt hn.2 h))
  show ((Finset.range (N + 1)).filter fun n => m n ≤ N).card ≤ M
  simpa using Finset.card_le_card hsub

/-! ## Two asymptotic facts

Everything the growth arguments of this root need about `Real.log`, in the two shapes they need
it: `log` is `o(nʳ)` for every `r > 0`, and `log n → ∞` along `ℕ`. -/

/-- `log n = o(nʳ)` in the form used below. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem eventually_log_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ (n : ℕ) in atTop, Real.log n ≤ c * (n : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).def hc
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [h', Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1R),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) r)] at hn

/-- `log n → ∞` along the naturals. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem tendsto_log_natCast : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

end BB6
