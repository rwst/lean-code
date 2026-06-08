/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Distribution modulo one — basics (Bertin §4)

Opening examples of Bertin's **§4** (*Pisot and Salem Numbers*, [Ber92]) on distribution
modulo one.

**Convention (Bertin).** Every real `x` decomposes uniquely as `x = E(x) + ε(x)` with
`E(x) ∈ ℤ` and `ε(x) ∈ [-1/2, 1/2)`. Here `E(x)` is Mathlib's `round x` (rounding to the
nearest integer, halves up) and we write `ε x := x - round x` for the centered fractional
part. From here on, "mod 1" of a real number means `ε` (the representative in `[-1/2, 1/2)`),
the convention used throughout the chapter.

Examples:
* `(nα)` with `α` rational takes finitely many values modulo one
  (`Bertin.finite_range_fract_mul_of_not_irrational`).
* `(φⁿ)`, `φ = (1+√5)/2` the golden ratio, has a single limit point modulo one, namely `0`:
  `ε(φⁿ) = -ψⁿ` (`ψ = (1-√5)/2`) for `n ≥ 2`, and `ε(φⁿ) → 0`
  (`Bertin.tendsto_ε_goldenRatio_pow`). This is the basic example of a Pisot number.
* `(1/p(n))`, `p(n)` the smallest prime factor of `n`, has infinitely many limit points but
  is not dense in `[-1/2, 1/2)` (`Bertin.infinite_mapClusterPt_one_div_minFac`,
  `Bertin.not_dense_one_div_minFac`).
* `(log n)` is dense modulo one (`Bertin.exists_eps_log_mem_Ico`, `Bertin.dense_eps_log`).

Plus a reduction (`Bertin.mapClusterPt_zero_of_rational_limitPoint`): multiplying by a common
denominator turns each rational limit point modulo one into `0`, so one may assume all rational
limit points are `0`.

The section's main result is **Theorem 4.1** (Pisot [Pis46], `Bertin.pisot_theorem_4_1`, cited):
a sequence with finitely many limit points modulo one (rational ones `= 0`) can be multiplied by
a non-zero integer `h ≤ qᵏ` so that `‖hxₙ‖ ≤ η` eventually.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §4.
  - [Pis46] Pisot, Charles. "Répartition modulo 1 des puissances successives des nombres réels."
    Comment. Math. Helv. 19 (1946), 153–160.
-/

namespace Bertin

open Filter
open scoped Topology goldenRatio

/-! ### Bertin's `ε`: the centered fractional part -/

/-- Bertin's `ε(x) = x - E(x)`: the signed distance from `x` to the nearest integer,
the canonical representative of `x mod 1` in `[-1/2, 1/2)`. Bertin's integer part `E(x)`
is Mathlib's `round x`. -/
@[category API, AMS 11, ref "Ber92"]
noncomputable def ε (x : ℝ) : ℝ := x - round x

/-- The decomposition `x = E(x) + ε(x)`, with `E(x) = round x`. -/
@[category API, AMS 11, ref "Ber92"]
theorem self_eq_round_add_ε (x : ℝ) : x = round x + ε x := by rw [ε]; ring

/-- `ε(x) ∈ [-1/2, 1/2)`. -/
@[category API, AMS 11, ref "Ber92"]
theorem ε_mem_Ico (x : ℝ) : ε x ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
  have h1 := Int.floor_le (x + 1/2)
  have h2 := Int.lt_floor_add_one (x + 1/2)
  rw [ε, round_eq, Set.mem_Ico]
  exact ⟨by linarith, by linarith⟩

/-- Bertin's decomposition `x = E(x) + ε(x)` holds in *one and only one* way: there is a
unique integer `e = E(x)` with `x - e ∈ [-1/2, 1/2)`. -/
@[category textbook, AMS 11, ref "Ber92", formal_uses ε_mem_Ico]
theorem existsUnique_intPart (x : ℝ) :
    ∃! e : ℤ, x - (e : ℝ) ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
  refine ⟨round x, ?_, ?_⟩
  · have := ε_mem_Ico x; rwa [ε] at this
  · intro e he
    have h := ε_mem_Ico x; rw [ε] at h
    rw [Set.mem_Ico] at he h
    have hlt : (e : ℝ) - round x < 1 := by linarith [h.2, he.1]
    have hgt : (-1 : ℝ) < (e : ℝ) - round x := by linarith [h.1, he.2]
    have e1 : e - round x < 1 := by exact_mod_cast hlt
    have e2 : -1 < e - round x := by exact_mod_cast hgt
    omega

/-! ### Example: `(nα)` with `α` rational -/

/--
The sequence `(nα)_{n ≥ 0}` with `α` rational takes on a finite number of values modulo one:
if `α = p/q` then `nα mod 1` depends only on `n mod q`, so it takes at most `q` distinct
values. (Contrast the irrational case, where `(nα)` is equidistributed modulo one and hence
takes infinitely many values.)
-/
@[category textbook, AMS 11, ref "Ber92"]
theorem finite_range_fract_mul_of_not_irrational (α : ℝ) (hα : ¬ Irrational α) :
    (Set.range fun n : ℕ => Int.fract ((n : ℝ) * α)).Finite := by
  -- `α` rational: write `α = ↑q` for some `q : ℚ`.
  obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = α := by
    simpa [Irrational, not_not] using hα
  -- Every value is `Int.fract (k * α)` for some `k < q.den`, a finite set.
  apply Set.Finite.subset (Set.finite_range (fun k : Fin q.den => Int.fract ((k : ℝ) * (q : ℝ))))
  rintro _ ⟨n, rfl⟩
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  -- `q.den * q = q.num` is an integer, which is what makes the sequence periodic mod 1.
  have hd : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by rw [Rat.cast_def]; field_simp
  refine ⟨⟨n % q.den, Nat.mod_lt n q.pos⟩, ?_⟩
  show Int.fract ((↑(n % q.den) : ℝ) * (q : ℝ)) = Int.fract ((↑n : ℝ) * (q : ℝ))
  -- `n = n % q.den + (n / q.den) * q.den`, so `n * q` and `(n % q.den) * q` differ by an integer.
  have hsplit : (↑n : ℝ) = (↑(n % q.den) : ℝ) + (↑(n / q.den) : ℝ) * (q.den : ℝ) := by
    have h := Nat.mod_add_div n q.den
    have h2 : ((n % q.den + q.den * (n / q.den) : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h
    push_cast at h2; linarith
  rw [hsplit, add_mul, mul_assoc, hd,
    show (↑(n / q.den) : ℝ) * (↑q.num : ℝ) = Int.cast ((↑(n / q.den) : ℤ) * q.num) from by
      rw [Int.cast_mul, Int.cast_natCast],
    Int.fract_add_intCast]

/-! ### Example: the golden ratio `φ = (1+√5)/2` -/

/-- `φⁿ + ψⁿ` is an integer (the Lucas number `2 F_{n+1} - F_n`), where `φ`, `ψ` are the
golden ratio and its conjugate and `F` is the Fibonacci sequence. This is the algebraic
fact behind `φ` being a Pisot number. -/
@[category API, AMS 11, ref "Ber92"]
theorem goldenRatio_pow_add_goldenConj_pow (n : ℕ) :
    φ ^ n + ψ ^ n = ((2 * Nat.fib (n + 1) - Nat.fib n : ℤ) : ℝ) := by
  have h1 := Real.fib_succ_sub_goldenConj_mul_fib n
  have h2 := Real.fib_succ_sub_goldenRatio_mul_fib n
  have hsum := Real.goldenRatio_add_goldenConj
  push_cast
  linear_combination -h1 - h2 - (Nat.fib n : ℝ) * hsum

/-- The golden conjugate `ψ = (1-√5)/2` satisfies `|ψ| < 1`; this is exactly the Pisot
condition (all conjugates inside the unit disk). -/
@[category API, AMS 11, ref "Ber92"]
theorem abs_goldenConj_lt_one : |ψ| < 1 := by
  rw [abs_lt]; exact ⟨Real.neg_one_lt_goldenConj, by linarith [Real.goldenConj_neg]⟩

/-- `ψ < -1/2`, hence `ψ² = ψ + 1 < 1/2`. -/
@[category API, AMS 11, ref "Ber92"]
theorem goldenConj_lt_neg_half : ψ < -(1/2) := by
  rw [Real.goldenConj]
  have : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  linarith

/-- For `n ≥ 2`, `ε(φⁿ) = -ψⁿ`: the nearest integer to `φⁿ` is the Lucas number `φⁿ + ψⁿ`,
since `|ψⁿ| ≤ ψ² < 1/2`. (For `n ≤ 1`, `|ψⁿ| > 1/2`, so the identity fails there.) -/
@[category textbook, AMS 11, ref "Ber92",
  formal_uses goldenRatio_pow_add_goldenConj_pow abs_goldenConj_lt_one goldenConj_lt_neg_half]
theorem ε_goldenRatio_pow (n : ℕ) (hn : 2 ≤ n) : ε (φ ^ n) = -(ψ ^ n) := by
  have hint := goldenRatio_pow_add_goldenConj_pow n
  have habsψ : |ψ| < 1 := abs_goldenConj_lt_one
  have hsqlt : ψ ^ 2 < 1/2 := by rw [Real.goldenConj_sq]; linarith [goldenConj_lt_neg_half]
  have habs : |ψ ^ n| ≤ ψ ^ 2 := by
    rw [abs_pow, ← sq_abs ψ]
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    rw [pow_add]
    have h1 : |ψ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg ψ) habsψ.le
    have h2 : (0 : ℝ) ≤ |ψ| ^ 2 := pow_nonneg (abs_nonneg ψ) 2
    nlinarith [h1, h2]
  have hsmall : -(ψ ^ n) ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by
    have hlt2 := abs_lt.mp (lt_of_le_of_lt habs hsqlt)
    rw [Set.mem_Ico]
    exact ⟨by linarith [hlt2.2], by linarith [hlt2.1]⟩
  have hsplit : φ ^ n = ((2 * Nat.fib (n + 1) - Nat.fib n : ℤ) : ℝ) + (-(ψ ^ n)) := by
    linarith [hint]
  rw [ε, hsplit, round_intCast_add, round_eq_zero_iff.mpr hsmall]
  push_cast; ring

/-- The sequence `(φⁿ)` has a single limit point modulo one, namely `0`: `ε(φⁿ) → 0` as
`n → ∞`. This expresses that the golden ratio is a Pisot number. -/
@[category textbook, AMS 11, ref "Ber92",
  formal_uses ε_goldenRatio_pow abs_goldenConj_lt_one]
theorem tendsto_ε_goldenRatio_pow :
    Tendsto (fun n => ε (φ ^ n)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => -(ψ ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_goldenConj_lt_one).neg
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [ε_goldenRatio_pow n hn]

/-! ### Example: the smallest-prime-factor sequence `1/p(n)`

`p(n)` is the smallest prime in the factorization of `n` — Mathlib's `Nat.minFac`. -/

/-- The sequence `(1/p(n))`, `p(n) = Nat.minFac n` the smallest prime factor, has **infinitely
many limit points**: for every prime `q`, the value `1/q` is a limit point (it is attained at
`n = qᵏ` for every `k`), and there are infinitely many primes. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem infinite_mapClusterPt_one_div_minFac :
    {x : ℝ | MapClusterPt x atTop (fun n => 1 / (Nat.minFac n : ℝ))}.Infinite := by
  -- Each `1/q` (`q` prime) is a cluster point: `p(qᵏ) = q`, and `qᵏ → ∞`.
  have hcluster : ∀ q : ℕ, q.Prime →
      MapClusterPt (1 / (q : ℝ)) atTop (fun n => 1 / (Nat.minFac n : ℝ)) := by
    intro q hq
    rw [mapClusterPt_iff_frequently]
    intro s hs
    have hfreq : ∃ᶠ n in atTop, (fun n => 1 / (Nat.minFac n : ℝ)) n = 1 / (q : ℝ) := by
      rw [Filter.frequently_atTop]
      intro m
      refine ⟨q ^ (m + 1), ?_, ?_⟩
      · have hb : m + 1 < q ^ (m + 1) := Nat.lt_pow_self hq.one_lt
        omega
      · have hk1 : q ^ (m + 1) ≠ 1 := (Nat.one_lt_pow (Nat.succ_ne_zero m) hq.one_lt).ne'
        have hp := Nat.minFac_prime hk1
        have hd : Nat.minFac (q ^ (m + 1)) ∣ q :=
          (Nat.Prime.prime hp).dvd_of_dvd_pow (Nat.minFac_dvd _)
        have hmin : Nat.minFac (q ^ (m + 1)) = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
        show (1 : ℝ) / (Nat.minFac (q ^ (m + 1)) : ℝ) = 1 / (q : ℝ)
        rw [hmin]
    refine hfreq.mono fun n hn => ?_
    change (1 : ℝ) / (Nat.minFac n : ℝ) = 1 / (q : ℝ) at hn
    show (1 : ℝ) / (Nat.minFac n : ℝ) ∈ s
    rw [hn]
    exact mem_of_mem_nhds hs
  -- `q ↦ 1/q` is injective on the (infinite) set of primes, with image inside the limit points.
  have hInj : Set.InjOn (fun q : ℕ => 1 / (q : ℝ)) {q | q.Prime} := by
    intro p _ q _ hpq
    simp only [one_div, inv_inj] at hpq
    exact_mod_cast hpq
  have hsub : (fun q : ℕ => 1 / (q : ℝ)) '' {q | q.Prime} ⊆
      {x : ℝ | MapClusterPt x atTop (fun n => 1 / (Nat.minFac n : ℝ))} := by
    rintro _ ⟨q, hq, rfl⟩
    exact hcluster q hq
  exact ((Set.infinite_image_iff hInj).2 Nat.infinite_setOf_prime).mono hsub

/-- The sequence `(1/p(n))` is **not dense** in `[-1/2, 1/2)`: every value is `≥ 0` (a reciprocal
of a positive integer), so its closure misses the whole subinterval `[-1/2, 0)`. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem not_dense_one_div_minFac :
    ¬ Set.Ico (-(1/2) : ℝ) (1/2) ⊆ closure (Set.range (fun n => 1 / (Nat.minFac n : ℝ))) := by
  intro hsub
  have hmem : (-(1/4) : ℝ) ∈ Set.Ico (-(1/2) : ℝ) (1/2) := by constructor <;> norm_num
  have hcl : closure (Set.range (fun n => 1 / (Nat.minFac n : ℝ))) ⊆ Set.Ici (0 : ℝ) :=
    closure_minimal (by rintro _ ⟨n, rfl⟩; exact Set.mem_Ici.2 (by positivity)) isClosed_Ici
  have h4 := hcl (hsub hmem)
  rw [Set.mem_Ici] at h4; norm_num at h4

/-! ### Example: `(log n)` is dense modulo one -/

/-- The sequence `(log n)_{n ≥ 1}` is **dense modulo one**: for arbitrary reals
`-1/2 ≤ a < b ≤ 1/2` there is an `n` with `ε(log n) ∈ [a, b)`. Proof: for `m` large enough,
the interval `[e^{m+a}, e^{m+b})` has length `≥ 1`, hence contains an integer `n`; then
`log n ∈ [m+a, m+b) ⊆ [m-1/2, m+1/2)`, so `round (log n) = m` and `ε(log n) = log n - m ∈ [a, b)`. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem exists_eps_log_mem_Ico (a b : ℝ) (ha : -(1/2) ≤ a) (hab : a < b) (hb : b ≤ 1/2) :
    ∃ n : ℕ, 1 ≤ n ∧ ε (Real.log n) ∈ Set.Ico a b := by
  have hexp : 0 < Real.exp b - Real.exp a := sub_pos.mpr (Real.exp_lt_exp.mpr hab)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (1 / (Real.exp b - Real.exp a)))
  have hminv : 1 / (Real.exp b - Real.exp a) < m := lt_of_le_of_lt (le_max_right _ _) hm
  set L := Real.exp ((m : ℝ) + a) with hL
  set R := Real.exp ((m : ℝ) + b) with hR
  have hLpos : 0 < L := by rw [hL]; exact Real.exp_pos _
  have hRL : R - L = Real.exp (m : ℝ) * (Real.exp b - Real.exp a) := by
    rw [hL, hR, Real.exp_add, Real.exp_add]; ring
  have hLR : L + 1 ≤ R := by
    have hexpm : (1 : ℝ) / (Real.exp b - Real.exp a) < Real.exp (m : ℝ) :=
      lt_of_lt_of_le hminv (by linarith [Real.add_one_le_exp (m : ℝ)])
    rw [div_lt_iff₀ hexp] at hexpm
    linarith [hRL, hexpm]
  -- the interval `[L, R)` has length `≥ 1`, so `⌈L⌉` lands in it.
  set N : ℤ := ⌈L⌉ with hN
  have hNpos : 0 < N := by rw [hN]; exact Int.ceil_pos.mpr hLpos
  have hNrpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNL : L ≤ (N : ℝ) := Int.le_ceil L
  have hNR : (N : ℝ) < R := by
    have h := Int.ceil_lt_add_one L; rw [← hN] at h; linarith [hLR]
  -- hence `log N ∈ [m+a, m+b)`.
  have hlogL : (m : ℝ) + a ≤ Real.log N := by
    have := Real.log_le_log hLpos hNL; rwa [hL, Real.log_exp] at this
  have hlogR : Real.log N < (m : ℝ) + b := by
    have := Real.log_lt_log hNrpos hNR; rwa [hR, Real.log_exp] at this
  refine ⟨N.toNat, by omega, ?_⟩
  have hcast : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hNpos.le
  rw [hcast]
  -- `round (log N) = m`, since `log N + 1/2 ∈ [m, m+1)`.
  have hround : round (Real.log N) = (m : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith [hlogL, hlogR]
  rw [ε, hround, Set.mem_Ico]
  push_cast
  constructor <;> linarith [hlogL, hlogR]

/-- Restatement of `(log n)` dense modulo one: the values `ε(log n)` are dense in `[-1/2, 1/2)`. -/
@[category textbook, AMS 11, ref "Ber92", formal_uses exists_eps_log_mem_Ico]
theorem dense_eps_log :
    Set.Ico (-(1/2) : ℝ) (1/2) ⊆ closure (Set.range (fun n : ℕ => ε (Real.log n))) := by
  intro x hx
  rw [Set.mem_Ico] at hx
  rw [Metric.mem_closure_iff]
  intro δ hδ
  -- shrink to a subinterval `[a, b) ⊆ [-1/2, 1/2)` around `x` of length `≤ δ`.
  set a := max (-(1/2)) (x - δ/2) with ha'
  set b := min (1/2) (x + δ/2) with hb'
  have hax : a ≤ x := max_le hx.1 (by linarith)
  have hxb : x < b := lt_min hx.2 (by linarith)
  have ha2 : -(1/2) ≤ a := le_max_left _ _
  have hb2 : b ≤ 1/2 := min_le_left _ _
  have hba : b - a ≤ δ := by
    have h1 : b ≤ x + δ/2 := min_le_right _ _
    have h2 : x - δ/2 ≤ a := le_max_right _ _
    linarith
  obtain ⟨n, _, hn⟩ := exists_eps_log_mem_Ico a b ha2 (lt_of_le_of_lt hax hxb) hb2
  rw [Set.mem_Ico] at hn
  refine ⟨ε (Real.log n), Set.mem_range_self n, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hn.1, hn.2, hax, hxb, hba]

/-! ### Reduction: rational limit points modulo one can be normalised to `0`

For limit points modulo one it is cleaner to work in the circle `AddCircle 1 = ℝ ⧸ ℤ`: a
"limit point modulo one" of a real sequence `x` is a cluster point of `(↑xₙ : AddCircle 1)`,
and a *rational* limit point `r` is a torsion point, i.e. one with `d • r = 0` for some
`d : ℕ` (a common denominator). Multiplying the sequence by such a `d` sends that limit point
to `0`. This justifies assuming, in the sequel, that all rational limit points are `0`. -/

/-- If `r` is a limit point modulo one of `(xₙ)` (a cluster point of `↑xₙ` in `AddCircle 1`)
and `d • r = 0` — i.e. `r` is rational with denominator dividing `d` — then `0` is a limit
point modulo one of the scaled sequence `(d · xₙ)`. Hence, multiplying by a common denominator
of the (finitely many) rational limit points turns each of them into `0`. -/
@[category textbook, AMS 11, ref "Ber92"]
theorem mapClusterPt_zero_of_rational_limitPoint (x : ℕ → ℝ) (d : ℕ) (r : AddCircle (1 : ℝ))
    (hr : MapClusterPt r atTop (fun n => ((x n : ℝ) : AddCircle (1 : ℝ))))
    (hdr : d • r = 0) :
    MapClusterPt (0 : AddCircle (1 : ℝ)) atTop
      (fun n => (((d : ℝ) * x n : ℝ) : AddCircle (1 : ℝ))) := by
  -- multiplication by `d` is continuous on the circle, so it preserves cluster points
  have hcont : ContinuousAt (fun t : AddCircle (1 : ℝ) => d • t) r := by fun_prop
  have h := MapClusterPt.continuousAt_comp hcont hr
  rw [hdr] at h
  -- and `↑(d · xₙ) = d • ↑xₙ`, so the scaled sequence is the image of the original
  have hfun : (fun n => (((d : ℝ) * x n : ℝ) : AddCircle (1 : ℝ)))
      = (fun t : AddCircle (1 : ℝ) => d • t) ∘ (fun n => ((x n : ℝ) : AddCircle (1 : ℝ))) := by
    funext n
    simp only [Function.comp_apply, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [hfun]
  exact h

/-! ### Pisot's Theorem 4.1 -/

/-- The set of limit points modulo one of a real sequence `x`: the cluster points of
`(↑xₙ : AddCircle 1)`. -/
@[category API, AMS 11, ref "Ber92"]
def limitPointsModOne (x : ℕ → ℝ) : Set (AddCircle (1 : ℝ)) :=
  {r | MapClusterPt r atTop (fun n => ((x n : ℝ) : AddCircle (1 : ℝ)))}

/-- The irrational limit points modulo one: those of infinite additive order
(`addOrderOf r = 0`), i.e. the limit points that are not rational points of the circle. -/
@[category API, AMS 11, ref "Ber92"]
def irrationalLimitPointsModOne (x : ℕ → ℝ) : Set (AddCircle (1 : ℝ)) :=
  {r ∈ limitPointsModOne x | addOrderOf r = 0}

informal_result "dirichlet-simultaneous-approximation"
  latex "Dirichlet's theorem on simultaneous Diophantine approximation: given reals $\\gamma_1, \\dots, \\gamma_k$ and an integer $q > 1$, there exist an integer $h$ with $0 < h \\le q^k$ and integers $\\ell_1, \\dots, \\ell_k$ such that $h\\gamma_i = \\ell_i + \\xi_i$ with $|\\xi_i| \\le 1/q$ for every $i$ (equivalently $\\lVert h\\gamma_i\\rVert \\le 1/q$)."
  refs "Ber92"

/-- **Theorem 4.1** (Pisot [Pis46]). Let `(xₙ)` have finitely many limit points modulo one, all
of whose *rational* ones equal `0` (the normalisation justified by
`mapClusterPt_zero_of_rational_limitPoint`). Then for every `η > 0` there is a non-zero integer
`h` with `‖hxₙ‖ ≤ η` for `n` large enough; moreover, with `k` the number of irrational limit
points and `q ≥ max(4, 2/η)`, one can take `0 < h ≤ qᵏ`. Here `‖y‖ = |ε y|` is the distance from
`y` to the nearest integer.

Proof (Pisot): along the subsequence approaching the `i`-th irrational limit point `γᵢ`, write
`xₙ = E(xₙ) + γᵢ + ηₙ` with `ηₙ → 0`; apply Dirichlet's simultaneous approximation
(`dirichlet-simultaneous-approximation`) to obtain `0 < h ≤ qᵏ` with `hγᵢ = ℓᵢ + ξᵢ`,
`|ξᵢ| ≤ 1/q`; then `hxₙ = hE(xₙ) + ℓᵢ + ξᵢ + hηₙ` and `|ξᵢ + hηₙ| < 2/q < 1/2` for `n` large, so
`|ε(hxₙ)| = |ξᵢ + hηₙ| ≤ η`. The argument rests on simultaneous Diophantine approximation, which
is not in Mathlib, so this is recorded as a cited axiom. -/
@[category research solved, AMS 11, ref "Ber92" "Pis46",
  formal_uses mapClusterPt_zero_of_rational_limitPoint,
  informal_uses "dirichlet-simultaneous-approximation"]
axiom pisot_theorem_4_1 (x : ℕ → ℝ) (hfin : (limitPointsModOne x).Finite)
    (hrat : ∀ r ∈ limitPointsModOne x, addOrderOf r ≠ 0 → r = 0)
    (η : ℝ) (hη : 0 < η) (q : ℕ) (hq4 : 4 ≤ q) (hqη : 2 / η ≤ q) :
    ∃ h : ℤ, 0 < h ∧ h ≤ (q : ℤ) ^ (irrationalLimitPointsModOne x).ncard ∧
      ∀ᶠ n in atTop, |ε ((h : ℝ) * x n)| ≤ η

end Bertin
