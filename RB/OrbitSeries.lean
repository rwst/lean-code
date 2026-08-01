/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.EventuallyPeriodic
import ForMathlib.Analysis.Polynomial.Growth
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The orbit series: the Möbius relation, and `A061419` is not holonomic ([B1E2b] WP6)

The companion of `RB.EventuallyPeriodic`, one level up: instead of the word `w`, the **orbit**
`x` itself.  Three things live here.

* **`RB.orbitSeries_mobius`** — the purely formal relation between the two generating functions
  `F(z) = ∑ xₙzⁿ` and `f(z) = ∑ wⱼzʲ`:

    `(2 − 3z)·F(z) = z·f(z) + 2x₀`.

  It is one line of `two_mul_x_succ` read off coefficientwise.  The *analytic* readings of it —
  radius of convergence `2/3`, a simple pole at `z = 2/3` with residue `−2K/3`, transcendence of
  `F` as a function — belong to the paper, not here: `PowerSeries` has no analytic structure in
  Mathlib.  (The residue is `−2K/3`; a factor `−3` slipped in the review's `2K`.)

* **`RB.not_isPRecursive_orbit`** — the orbit `x` (OEIS **A061419** at `x₀ = 1`) is **not
  P-recursive**: it satisfies no linear recurrence with polynomial coefficients.  `std3`.

* **`RB.irrational_tsum_wmin_iff`** — `f(2/3)` is irrational **iff** `K` is: the value of the word
  series at the pole is `3(K − x₀)` (`RB.tsum_wmin_eq`), so the two irrationality questions are the
  same question — open since Wang–Washburn 1977.

## How the non-holonomy of the orbit is obtained

Closure of P-recursiveness under shifts and linear combinations — the textbook route — is *not*
cheap: it is a finite-dimensionality argument over `ℚ(n)` and Mathlib has none of it.  It can be
bypassed completely, using only the corpus's exact circuit identity and the flagship
`RB.not_isPRecursive_wmin`.

Suppose `∑_{j≤s} Qⱼ(n)·x(n+j) = 0` nontrivially, and let `sb` be the largest index with
`Q_{sb} ≠ 0`.  Multiply by `2^s` and substitute `2ʲx(n+j) = 3ʲx(n) + W(n,j)`
(`RB.circuit_sum`), `W(n,j) = ∑_{i<j} 3^{j−1−i}2ⁱw(n+i)`:

  `A(n)·x(n) + ∑_{i<s} Bᵢ(n)·w(n+i) = 0`,
  `A = ∑ⱼ Qⱼ2^{s−j}3ʲ`,  `Bᵢ = ∑_{j>i} Qⱼ2^{s−j+i}3^{j−1−i}`,  and `B_{sb−1} = 2^{s−1}Q_{sb} ≠ 0`.

* If `A = 0`, what is left is a *nontrivial P-recurrence for the word* — contradicting
  `RB.not_isPRecursive_wmin`.
* If `A ≠ 0`, then `|A(n)|·x(n) ≤ ∑ᵢ|Bᵢ(n)|` because `|w| ≤ 1`, while `x(n) ≥ (3/2)ⁿ`
  (`RB.three_pow_mul_le`).  So `|A(n)| ≤ (∑ᵢ|Bᵢ(n)|)·(2/3)ⁿ → 0`, and a polynomial whose values
  along `ℕ` tend to `0` is `0` (`Polynomial.eq_zero_of_tendsto_eval_natCast`).  Contradiction.

The polynomial-growth facts this needs are generic and live in
`ForMathlib/Analysis/Polynomial/Growth.lean`: `Polynomial.abs_eval_le_of_one_le`,
`Polynomial.tendsto_abs_eval_mul_pow`, `Polynomial.eq_zero_of_tendsto_eval_natCast`.  Note that no
integrality argument is needed — the plan's "clear denominators, so `|A(n)| ≥ 1/M` off the roots"
step is replaced by the last of those three.

(The degenerate case `sb = 0` is separate and immediate: `Q₀(n)·x(n) = 0` with `x(n) > 0` makes
`Q₀` vanish at every natural, hence `Q₀ = 0`.)

Nothing in the argument is special to `3/2`: it uses a circuit identity, a bounded word, and
exponential growth, so it transports to the families of [B1E2b] WP4/WP5.

## Contents

* `RB.orbitSeries`, `RB.wordSeries`, **`RB.orbitSeries_mobius`**.
* **`RB.not_isPRecursive_orbit`**, `RB.not_isAlgebraic_orbitSeries`.
* **`RB.irrational_tsum_wmin_iff`**.

## References

* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91.
* [Sta80] R. P. Stanley. European J. Combin. **1** (1980), 175–188.  (The algebraicity corollary.)
* [WW77] Wang, Washburn (1977); OEIS **A083286** — the irrationality of `K` is open.
* OEIS **A061419** — the orbit `xₙ = ⌈3xₙ₋₁/2⌉` from `x₀ = 1`.
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP6.
-/

namespace RB

open Stanley Filter Topology

/-! ## The two generating functions, and the Möbius relation -/

/-- The **orbit series** `F(z) = ∑ₙ xₙzⁿ`. -/
@[category API, AMS 11 05, ref "B1E2b", group "rb_orbit_series"]
noncomputable def orbitSeries (x₀ : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => (x x₀ n : ℚ)

/-- The **word series** `f(z) = ∑ⱼ wⱼzʲ`. -/
@[category API, AMS 11 05, ref "B1E2b", group "rb_orbit_series"]
noncomputable def wordSeries (x₀ : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => (wmin x₀ n : ℚ)

/-- **The Möbius relation** `(2 − 3z)·F(z) = z·f(z) + 2x₀`, as formal power series over `ℚ`.

Coefficientwise this is exactly the selection rule `2x_{n+1} = 3xₙ + wₙ` (`RB.two_mul_x_succ`),
plus `2x₀` in degree `0`.  Purely formal: no convergence, no pole, no residue — those are the
paper's analytic statements about the same identity. -/
@[category research solved, AMS 11 05, ref "B1E2b", group "rb_orbit_series"]
theorem orbitSeries_mobius (x₀ : ℕ) :
    (PowerSeries.C 2 - PowerSeries.C 3 * PowerSeries.X) * orbitSeries x₀
      = PowerSeries.X * wordSeries x₀ + PowerSeries.C (2 * (x₀ : ℚ)) := by
  refine PowerSeries.ext fun n => ?_
  have hsplit : (PowerSeries.C 2 - PowerSeries.C 3 * PowerSeries.X) * orbitSeries x₀
      = PowerSeries.C 2 * orbitSeries x₀
        - PowerSeries.C 3 * (PowerSeries.X * orbitSeries x₀) := by ring
  rw [hsplit]
  cases n with
  | zero =>
    simp [orbitSeries, wordSeries]
  | succ n =>
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C, orbitSeries, wordSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero,
      if_false, add_zero]
    have := two_mul_x_succ x₀ n
    have : (2 : ℚ) * (x x₀ (n + 1) : ℚ) = 3 * (x x₀ n : ℚ) + (wmin x₀ n : ℚ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) this
    linarith

/-! ## The orbit is not holonomic -/

/-- **[B1E2b] WP6**: the ceiling orbit `xₙ = ⌈3xₙ₋₁/2⌉` — OEIS **A061419** at `x₀ = 1` — is
**not P-recursive**.

Footprint: `std3`.  See the module doc for the two-branch proof; the only inputs are the corpus's
circuit identity `RB.circuit_sum`, the growth ceiling `RB.three_pow_mul_le`, the `{0,1}`-alphabet
of the word, and the flagship `RB.not_isPRecursive_wmin`.  No closure theory for P-recursive
sequences is used — and none is available in Mathlib. -/
@[category research solved, AMS 11 68 05, ref "AFS08" "B1E2b", group "rb_orbit_series"]
theorem not_isPRecursive_orbit {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsPRecursive (fun n => (x x₀ n : ℚ)) := by
  classical
  rintro ⟨s, Q, ⟨j₀, hj₀⟩, hrec⟩
  -- the largest index carrying a nonzero coefficient
  set F : Finset (Fin (s + 1)) := Finset.univ.filter (fun j => Q j ≠ 0) with hF
  have hFne : F.Nonempty := ⟨j₀, by simp [hF, hj₀]⟩
  obtain ⟨jb, hjbF, hjbmax⟩ := F.exists_max_image (fun j => (j : ℕ)) hFne
  have hQb : Q jb ≠ 0 := by simpa [hF] using hjbF
  have hzero_above : ∀ j : Fin (s + 1), (jb : ℕ) < (j : ℕ) → Q j = 0 := by
    intro j hj
    by_contra hne
    exact absurd (hjbmax j (by simp [hF, hne])) (by omega)
  set sb : ℕ := (jb : ℕ) with hsb
  have hsbs : sb ≤ s := Nat.lt_succ_iff.mp jb.isLt
  rcases Nat.eq_zero_or_pos sb with hsb0 | hsbpos
  · -- degenerate case: the recurrence reads `Q_{jb}(n)·xₙ = 0`
    refine hQb (poly_eq_zero_of_infinite_nat_roots (T := Set.univ) Set.infinite_univ ?_)
    intro m _
    have hsingle : ∑ j : Fin (s + 1), (Q j).eval (m : ℚ) * (x x₀ (m + (j : ℕ)) : ℚ)
        = (Q jb).eval (m : ℚ) * (x x₀ (m + sb) : ℚ) := by
      refine Finset.sum_eq_single jb (fun j _ hjne => ?_) (fun h => absurd (Finset.mem_univ jb) h)
      have hj0 : (jb : ℕ) < (j : ℕ) := by
        have : (j : ℕ) ≠ sb := fun h => hjne (Fin.ext h)
        omega
      rw [hzero_above j hj0]
      simp
    have h := hrec m
    rw [hsingle] at h
    have hxpos : (0 : ℚ) < (x x₀ (m + sb) : ℚ) := by exact_mod_cast x_pos hx₀ (m + sb)
    exact (mul_eq_zero.mp h).resolve_right hxpos.ne'
  -- the main case
  set A : Polynomial ℚ :=
    ∑ j : Fin (s + 1), Q j * Polynomial.C ((2 : ℚ) ^ (s - (j : ℕ)) * 3 ^ (j : ℕ)) with hAdef
  set B : ℕ → Polynomial ℚ := fun i => ∑ j : Fin (s + 1),
    if i < (j : ℕ) then
      Q j * Polynomial.C ((2 : ℚ) ^ (s - (j : ℕ) + i) * 3 ^ ((j : ℕ) - 1 - i)) else 0 with hBdef
  have hBeval : ∀ i n, (B i).eval (n : ℚ) = ∑ j : Fin (s + 1),
      if i < (j : ℕ) then
        (Q j).eval (n : ℚ) * ((2 : ℚ) ^ (s - (j : ℕ) + i) * 3 ^ ((j : ℕ) - 1 - i)) else 0 := by
    intro i n
    rw [hBdef]
    simp only [Polynomial.eval_finsetSum, apply_ite (Polynomial.eval (n : ℚ)),
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero]
  -- the derived identity
  have key : ∀ n : ℕ, A.eval (n : ℚ) * (x x₀ n : ℚ)
      + ∑ i ∈ Finset.range s, (B i).eval (n : ℚ) * (wmin x₀ (n + i) : ℚ) = 0 := by
    intro n
    have hterm : ∀ j : Fin (s + 1), (2 : ℚ) ^ s * ((Q j).eval (n : ℚ) * (x x₀ (n + (j : ℕ)) : ℚ))
        = (Q j).eval (n : ℚ) * ((2 : ℚ) ^ (s - (j : ℕ)) * 3 ^ (j : ℕ)) * (x x₀ n : ℚ)
          + ∑ i ∈ Finset.range s,
              (if i < (j : ℕ) then
                (Q j).eval (n : ℚ) * ((2 : ℚ) ^ (s - (j : ℕ) + i) * 3 ^ ((j : ℕ) - 1 - i))
                  * (wmin x₀ (n + i) : ℚ) else 0) := by
      intro j
      have hjs : (j : ℕ) ≤ s := Nat.lt_succ_iff.mp j.isLt
      have hpow : (2 : ℚ) ^ s = (2 : ℚ) ^ (s - (j : ℕ)) * 2 ^ (j : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel hjs]
      have hc : (2 : ℚ) ^ (j : ℕ) * (x x₀ (n + (j : ℕ)) : ℚ)
          = 3 ^ (j : ℕ) * (x x₀ n : ℚ) + (W x₀ n (j : ℕ) : ℚ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (circuit_sum x₀ n (j : ℕ))
      have hW : (W x₀ n (j : ℕ) : ℚ)
          = ∑ i ∈ Finset.range (j : ℕ),
              (3 : ℚ) ^ ((j : ℕ) - 1 - i) * 2 ^ i * (wmin x₀ (n + i) : ℚ) := by
        rw [W]; push_cast; rfl
      have hextend : ∑ i ∈ Finset.range s,
            (if i < (j : ℕ) then
              (Q j).eval (n : ℚ) * ((2 : ℚ) ^ (s - (j : ℕ) + i) * 3 ^ ((j : ℕ) - 1 - i))
                * (wmin x₀ (n + i) : ℚ) else 0)
          = ∑ i ∈ Finset.range (j : ℕ),
              (Q j).eval (n : ℚ) * ((2 : ℚ) ^ (s - (j : ℕ) + i) * 3 ^ ((j : ℕ) - 1 - i))
                * (wmin x₀ (n + i) : ℚ) := by
        rw [← Finset.sum_subset (Finset.range_subset_range.mpr hjs)
          (fun i _ hi => if_neg (by simpa using hi))]
        exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
      rw [hextend]
      calc (2:ℚ) ^ s * ((Q j).eval (n : ℚ) * (x x₀ (n + (j:ℕ)) : ℚ))
          = (Q j).eval (n : ℚ) * ((2:ℚ) ^ (s - (j:ℕ))
              * ((2:ℚ) ^ (j:ℕ) * (x x₀ (n + (j:ℕ)) : ℚ))) := by rw [hpow]; ring
        _ = (Q j).eval (n : ℚ) * ((2:ℚ) ^ (s - (j:ℕ))
              * (3 ^ (j:ℕ) * (x x₀ n : ℚ)
                + ∑ i ∈ Finset.range (j:ℕ),
                    (3:ℚ) ^ ((j:ℕ) - 1 - i) * 2 ^ i * (wmin x₀ (n + i) : ℚ))) := by
            rw [hc, hW]
        _ = (Q j).eval (n : ℚ) * ((2:ℚ) ^ (s - (j:ℕ)) * 3 ^ (j:ℕ)) * (x x₀ n : ℚ)
              + ∑ i ∈ Finset.range (j:ℕ),
                  (Q j).eval (n : ℚ) * ((2:ℚ) ^ (s - (j:ℕ) + i) * 3 ^ ((j:ℕ) - 1 - i))
                    * (wmin x₀ (n + i) : ℚ) := by
            rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
            refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun i _ => ?_)
            rw [pow_add]
            ring
    have h0 : ∑ j : Fin (s + 1), (2 : ℚ) ^ s
        * ((Q j).eval (n : ℚ) * (x x₀ (n + (j : ℕ)) : ℚ)) = 0 := by
      rw [← Finset.mul_sum, hrec n, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_comm] at h0
    rw [← h0, hAdef]
    congr 1
    · rw [Polynomial.eval_finsetSum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by simp [Polynomial.eval_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hBeval, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < (j : ℕ) <;> simp [hij]
  -- `Bᵢ` vanishes above the top index, and `B_{sb−1}` does not
  have hBzero : ∀ i, sb ≤ i → B i = 0 := by
    intro i hi
    rw [hBdef]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : i < (j : ℕ)
    · rw [if_pos hij, hzero_above j (by omega), zero_mul]
    · rw [if_neg hij]
  have hBtop : B (sb - 1) = Q jb * Polynomial.C ((2 : ℚ) ^ (s - 1)) := by
    have hstep : B (sb - 1)
        = (if sb - 1 < sb then
            Q jb * Polynomial.C ((2 : ℚ) ^ (s - sb + (sb - 1)) * 3 ^ (sb - 1 - (sb - 1)))
          else 0) := by
      simp only [hBdef]
      refine Finset.sum_eq_single jb (fun j _ hjne => ?_) (fun h => absurd (Finset.mem_univ jb) h)
      by_cases hij : sb - 1 < (j : ℕ)
      · have hne : (j : ℕ) ≠ sb := by
          intro h
          exact hjne (Fin.ext (by omega))
        rw [if_pos hij, hzero_above j (by omega), zero_mul]
      · rw [if_neg hij]
    rw [hstep, if_pos (by omega)]
    congr 1
    have h1 : s - sb + (sb - 1) = s - 1 := by omega
    have h2 : sb - 1 - (sb - 1) = 0 := by omega
    rw [h1, h2, pow_zero, mul_one]
  have hBtop_ne : B (sb - 1) ≠ 0 := by
    rw [hBtop]
    exact mul_ne_zero hQb (Polynomial.C_ne_zero.mpr (by positivity))
  have hrange : ∀ n : ℕ, ∑ i ∈ Finset.range sb, (B i).eval (n : ℚ) * (wmin x₀ (n + i) : ℚ)
      = ∑ i ∈ Finset.range s, (B i).eval (n : ℚ) * (wmin x₀ (n + i) : ℚ) :=
    fun n => Finset.sum_subset (Finset.range_subset_range.mpr hsbs) fun i _ hi => by
      rw [hBzero i (by simpa using hi), Polynomial.eval_zero, zero_mul]
  by_cases hA : A = 0
  · -- **Branch `A = 0`**: what is left is a nontrivial P-recurrence for the word
    refine not_isPRecursive_wmin hx₀ ⟨sb - 1, fun i : Fin (sb - 1 + 1) => B (i : ℕ),
      ⟨⟨sb - 1, by omega⟩, by simpa using hBtop_ne⟩, fun n => ?_⟩
    have h := key n
    rw [hA, Polynomial.eval_zero, zero_mul, zero_add] at h
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (B i).eval (n : ℚ) * (wmin x₀ (n + i) : ℚ)) (sb - 1 + 1),
      show sb - 1 + 1 = sb by omega, hrange n]
    exact h
  · -- **Branch `A ≠ 0`**: geometric decay beats polynomial growth
    refine hA ?_
    have hmapinj : Function.Injective (Polynomial.map (algebraMap ℚ ℝ)) :=
      Polynomial.map_injective _ (algebraMap ℚ ℝ).injective
    refine hmapinj ?_
    rw [Polynomial.map_zero]
    have heval : ∀ (p : Polynomial ℚ) (n : ℕ),
        (p.map (algebraMap ℚ ℝ)).eval (n : ℝ) = ((p.eval (n : ℚ) : ℚ) : ℝ) := by
      intro p n
      rw [Polynomial.eval_map, show ((n : ℝ)) = algebraMap ℚ ℝ (n : ℚ) by norm_num,
        Polynomial.eval₂_at_apply]
      rfl
    refine Polynomial.eq_zero_of_tendsto_eval_natCast (squeeze_zero_norm (a := fun n : ℕ => ∑ i ∈ Finset.range s,
      |((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)| * ((2 : ℝ) / 3) ^ n) (fun n => ?_) ?_)
    · -- the pointwise bound `|A(n)| ≤ (∑ᵢ|Bᵢ(n)|)·(2/3)ⁿ`
      have hkeyR : (A.map (algebraMap ℚ ℝ)).eval (n : ℝ) * (x x₀ n : ℝ)
          + ∑ i ∈ Finset.range s,
              ((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ) * (wmin x₀ (n + i) : ℝ) = 0 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (key n)
        push_cast at h
        simpa [heval] using h
      have hxpos : (0 : ℝ) ≤ (x x₀ n : ℝ) := by positivity
      have hneg : (A.map (algebraMap ℚ ℝ)).eval (n : ℝ) * (x x₀ n : ℝ)
          = -(∑ i ∈ Finset.range s,
              ((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ) * (wmin x₀ (n + i) : ℝ)) := by
        linarith [hkeyR]
      have h1 : |∑ i ∈ Finset.range s,
            ((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ) * (wmin x₀ (n + i) : ℝ)|
          = |(A.map (algebraMap ℚ ℝ)).eval (n : ℝ)| * (x x₀ n : ℝ) := by
        rw [← abs_neg, ← hneg, abs_mul, abs_of_nonneg hxpos]
      have hbound : |(A.map (algebraMap ℚ ℝ)).eval (n : ℝ)| * (x x₀ n : ℝ)
          ≤ ∑ i ∈ Finset.range s, |((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)| := by
        rw [← h1]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        have hw : |(wmin x₀ (n + i) : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg (by positivity)]
          exact_mod_cast wmin_le_one x₀ (n + i)
        nlinarith [abs_nonneg (((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)),
          abs_nonneg ((wmin x₀ (n + i) : ℝ))]
      have hgrow : ((3 : ℝ) / 2) ^ n ≤ (x x₀ n : ℝ) := by
        have h : (3 : ℝ) ^ n * (x₀ : ℝ) ≤ 2 ^ n * (x x₀ n : ℝ) := by
          exact_mod_cast three_pow_mul_le x₀ n
        have hx₀' : (1 : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hx₀
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) n, pow_pos (by norm_num : (0:ℝ) < 2) n]
      have h32 : ((3 : ℝ) / 2) ^ n * ((2 : ℝ) / 3) ^ n = 1 := by
        rw [← mul_pow]; norm_num
      have hmain : |(A.map (algebraMap ℚ ℝ)).eval (n : ℝ)| * ((3 : ℝ) / 2) ^ n
          ≤ ∑ i ∈ Finset.range s, |((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)| := by
        refine le_trans ?_ hbound
        exact mul_le_mul_of_nonneg_left hgrow (abs_nonneg _)
      calc ‖(A.map (algebraMap ℚ ℝ)).eval (n : ℝ)‖
          = |(A.map (algebraMap ℚ ℝ)).eval (n : ℝ)| * ((3 : ℝ) / 2) ^ n * ((2 : ℝ) / 3) ^ n := by
            rw [mul_assoc, h32, mul_one]; rfl
        _ ≤ (∑ i ∈ Finset.range s, |((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)|)
              * ((2 : ℝ) / 3) ^ n := mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = ∑ i ∈ Finset.range s,
              |((B i).map (algebraMap ℚ ℝ)).eval (n : ℝ)| * ((2 : ℝ) / 3) ^ n :=
            Finset.sum_mul _ _ _
    · -- and the bound tends to `0`
      simpa using tendsto_finsetSum (Finset.range s) fun i _ =>
        Polynomial.tendsto_abs_eval_mul_pow ((B i).map (algebraMap ℚ ℝ)) (r := (2 : ℝ) / 3)
          (by norm_num) (by norm_num)

/-- The orbit series `F(z) = ∑ₙ xₙzⁿ` is not algebraic over `ℚ(z)`.

Footprint: `std3 + Stanley.pRecursive_of_isAlgebraic`. -/
@[category research solved, AMS 11 68 05, ref "Sta80" "B1E2b", group "rb_orbit_series"]
theorem not_isAlgebraic_orbitSeries {x₀ : ℕ} (hx₀ : 0 < x₀) :
    ¬ IsAlgebraic (Polynomial ℚ) (orbitSeries x₀) := fun halg =>
  not_isPRecursive_orbit hx₀ (by simpa [orbitSeries] using pRecursive_of_isAlgebraic halg)

/-! ## The value at the pole -/

/-- **`f(2/3)` is irrational iff `K` is.**  The word series evaluated at the pole of `F` is
`3(K − x₀)` (`RB.tsum_wmin_eq`), so the two irrationality questions coincide — and both are open
(Wang–Washburn 1977; OEIS A083286). -/
@[category research solved, AMS 11, ref "WW77" "B1E2b", group "rb_orbit_series"]
theorem irrational_tsum_wmin_iff (x₀ : ℕ) :
    Irrational (∑' j, (2 / 3 : ℝ) ^ j * wmin x₀ j) ↔ Irrational (K x₀) := by
  rw [tsum_wmin_eq, show (3 : ℝ) * (K x₀ - x₀) = ((3 : ℚ) : ℝ) * (K x₀ - (x₀ : ℕ)) by
    push_cast; ring, irrational_ratCast_mul_iff, irrational_sub_natCast_iff]
  simp

end RB
