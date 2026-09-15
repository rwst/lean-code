/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.PressureCriterion
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The window modelling lemma at `α = 2 + √3`

Formal companion of `note-1061-M4.html` (milestone M4 of `plans/plan-1061.html`), the last
piece of the chain `BB61/Pressure.lean` → `BB61/PressureCriterion.lean` → 10.61 at `2 + √3`.

`BB61/Pressure.lean` certifies a **finite-state transfer operator**: `64` states, two symbols,
integer edge weights, growth ratio `a/b` below the entropy floor.  `BB61/PressureCriterion.lean`
turns any such certificate into 10.61 at `α`, *provided* someone exhibits the state observable
that the operator is meant to model.  This file exhibits it.

## The observable

Let `Shift = ℤ → Bool` and `σ` the left shift.  The state of `ω` is the six-bit word

`stateOf ω = ∑_{i<6} 2^i · ω(i-6)`,

so that appending the letter `ω 0` at the top and dropping the oldest bit is exactly the
successor map `tgtB` of the certificate: `stateOf (σ ω) = tgtB (stateOf ω) (ω 0)`
(`stateOf_shiftZ`).  The **word** `wordOf ω = stateOf ω + 64 · ω 0` is the seven-bit block
`ω(-6), …, ω(0)`, and the certificate's edge weight is `wcert (wordOf ω)` (`wB_eq_wcert`).

## The potential

The potential is the logarithm of the weight of the cell of the equipartition of the circle
into `B = 8` intervals that the factor map falls into, read three steps in the past:

`gWin P ω = log (cw ⌊8 · F(σ⁻³ω)⌋)`,  `F = fRaw` of `BB61/Factor.lean`.

The three-step delay is forced: the transfer operator shifts states *downwards*, so its newest
letter must be the one the partition reads, `ω 0`, while the window `N = M = 3` of
`note-1061-M3.html` looks three letters into the future.  It costs nothing — the mean of `gWin`
is shift-invariant.

## The estimate

Everything at `α = 2 + √3` lives in `ℤ[√3]` **exactly**.  Writing `β = 2 - √3 = α⁻¹`, all seven
window weights are `(1-β)βᵏ`:

`(1-β)β⁰ = -1+√3`,  `(1-β)β¹ = -5+3√3`,  `(1-β)β² = -19+11√3`,  `(1-β)β³ = -71+41√3`,

so the window value of each of the `128` words is an exact `p + q√3` (`winP`, `winQ`), and M1
Lemma 6's truncation bound is exact too:

`ε = α⁻³ + |β-1|·|β|⁴/(1-|β|) = (2-√3)³ + (2-√3)⁴ = 123 - 71√3`.

Hence the cell of the true point is decided by two integer comparisons per word: with
`L u = ⌊8(F̃ - ε)⌋` and `H u = ⌊8(F̃ + ε)⌋` tabulated (`LLL`, `HHL`, from
`BB61/m4_window_tables.py`), the four facts

* `8(F̃ - ε) ≥ L u`,  * `8(F̃ + ε) < H u + 1`,  * `L u ≤ H u ≤ L u + 1`,
* `cw (L u mod 8) ≤ wcert u` and `cw (H u mod 8) ≤ wcert u`

are decidable in `ℤ` and hold for all `128` words (`windowOK_true`).  The third is where
`16 ε < 1` enters, and the fourth is the definition `wcert u = max(cw lo, cw hi)` that
`BB61/m4_lean_cert.py` used to build the transfer weights in the first place.

Comparisons `0 ≤ A + B√3` are decided by squaring (`nnneg3`, `pos3`); `√3` never appears in the
`decide`.

## The mean

The potential being a **step function** also makes its Lebesgue mean a finite sum: splitting
`[0,1]` into the eight cells gives `∫ cellPot = (1/8) log W`, `W = ∏ⱼ wⱼ`, and a measure with
`F_*μ = Leb` reproduces it (`integral_gWin`).  The three-step delay washes out because
`back3 ∘ σ³ = id` and `μ` is `σ`-invariant.

## Result

`two_add_sqrt3_not_equidistributed` — **Problem 10.61 at `2 + √3`**, with a single hypothesis
left: M3 Theorem 11's entropy floor ([You82] at `d = 2`, [LY85], [BPS99]), which is far outside
Mathlib and is carried here as a hypothesis rather than a cited axiom, so this file stays
axiom-free and citation-free.  `BB61/Floor.lean` discharges it from the root's one cited axiom,
`LY.entropyRate_floor` of `CITED/LedrappierYoung.lean`, and states the unconditional
`problem_10_61_two_add_sqrt3`.
-/

namespace BB61

open QuadSetup MeasureTheory Dynamics

/-! ## Truncating the factor map

Two finite-sum forms of M1 Lemma 6.  The window half is stated with the **sharp** constant
`|β-1|·|β|ⁿ/(1-|β|)`: `BB61/Factor.lean`'s `abs_wVal_sub_le_of_agree` charges `(1+|β|)` where
`|c_m| = |β-1|·|β|ᵐ` is exact, and at `α = 2+√3` that difference is the whole margin — the
sharp constant gives `ε = 123 - 71√3`, the crude one nearly `0.028`, and the cell tables are
computed at the former. -/

/-- The Cantor half truncated at depth `n`, with the tail bound `α^{-n}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_piVal_sub_range {α : ℝ} (hα : 1 < α) (δ : ℕ → Bool) (n : ℕ) :
    |piVal α δ - (α - 1) * ∑ k ∈ Finset.range n, dR δ k * (α⁻¹) ^ (k + 1)| ≤ (α⁻¹) ^ n := by
  classical
  set δ' : ℕ → Bool := fun k => if k < n then δ k else false with hδ'
  have hagree : ∀ k, k < n → δ k = δ' k := by intro k hk; simp [hδ', hk]
  have hvanish : ∀ k ∉ Finset.range n, dR δ' k * (α⁻¹) ^ (k + 1) = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp [hδ', hk, dR]
  have hval : piVal α δ' = (α - 1) * ∑ k ∈ Finset.range n, dR δ k * (α⁻¹) ^ (k + 1) := by
    rw [piVal, tsum_eq_sum hvanish]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [dR_congr (hagree k (Finset.mem_range.mp hk))]
  rw [← hval]
  exact abs_piVal_sub_le_of_agree hα hagree

/-- The window half truncated at depth `n`, with the **sharp** tail bound
`|β-1|·|β|ⁿ/(1-|β|)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_wVal_sub_range (P : QuadSetup) (δ : ℕ → Bool) (n : ℕ) :
    |P.wVal δ - ∑ m ∈ Finset.range n, P.cCoef m * dR δ m|
      ≤ |P.β - 1| * |P.β| ^ n / (1 - |P.β|) := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hs := P.summable_cCoef δ
  have hsplit : P.wVal δ - ∑ m ∈ Finset.range n, P.cCoef m * dR δ m
      = ∑' m : ℕ, P.cCoef (m + n) * dR δ (m + n) := by
    rw [wVal, ← hs.sum_add_tsum_nat_add n]
    ring
  have hbd : ∀ m : ℕ, ‖P.cCoef (m + n) * dR δ (m + n)‖
      ≤ (|P.β - 1| * |P.β| ^ n) * |P.β| ^ m := by
    intro m
    have h1 : |dR δ (m + n)| ≤ 1 := by
      rw [abs_of_nonneg (dR_nonneg _ _)]; exact dR_le_one _ _
    have hcc : |P.cCoef (m + n)| = |P.β - 1| * (|P.β| ^ m * |P.β| ^ n) := by
      rw [cCoef, abs_mul, abs_pow, pow_add]
    rw [Real.norm_eq_abs, abs_mul, hcc]
    calc |P.β - 1| * (|P.β| ^ m * |P.β| ^ n) * |dR δ (m + n)|
        ≤ |P.β - 1| * (|P.β| ^ m * |P.β| ^ n) * 1 := by gcongr
      _ = (|P.β - 1| * |P.β| ^ n) * |P.β| ^ m := by ring
  have hgeom : Summable fun m : ℕ => (|P.β - 1| * |P.β| ^ n) * |P.β| ^ m :=
    (summable_geometric_of_lt_one hβ0 hβ).mul_left _
  rw [hsplit]
  have hb := tsum_of_norm_bounded hgeom.hasSum hbd
  rw [Real.norm_eq_abs] at hb
  refine hb.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ]
  field_simp

/-! ## The three-step delay

The transfer operator of `BB61/Pressure.lean` shifts states downwards, so the letter it
appends must be the one `coordPartition` reads.  The window of `note-1061-M3.html`, on the
other hand, looks `M = 3` letters into the future.  The two are reconciled by evaluating the
factor map three steps in the past — a shift of the potential, which costs nothing, since
every measure in sight is shift-invariant. -/

/-- The three-fold backward shift `(τ³ω)_k = ω_{k-3}`. -/
def back3 (ω : Shift) : Shift := fun k => ω (k - 3)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_back3 : Continuous back3 :=
  continuous_pi fun k => continuous_apply (k - 3)

/-- The window value: the factor map at `τ³ω`, truncated to the seven letters
`ω(-6), …, ω(0)`. -/
noncomputable def winSum (P : QuadSetup) (ω : Shift) : ℝ :=
  (P.α - 1) * ∑ k ∈ Finset.range 3, dR (futures (back3 ω)) k * (P.α⁻¹) ^ (k + 1)
    - ∑ m ∈ Finset.range 4, P.cCoef m * dR (pasts (back3 ω)) m

/-- **M1 Lemma 6 at `N = M = 3`.**  The window value is within
`α⁻³ + |β-1||β|⁴/(1-|β|)` of the true value of the factor map. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fRaw_back3_sub (P : QuadSetup) (ω : Shift) :
    |P.fRaw (back3 ω) - winSum P ω| ≤ (P.α⁻¹) ^ 3 + |P.β - 1| * |P.β| ^ 4 / (1 - |P.β|) := by
  have h1 := abs_piVal_sub_range P.one_lt (futures (back3 ω)) 3
  have h2 := abs_wVal_sub_range P (pasts (back3 ω)) 4
  have hsplit : P.fRaw (back3 ω) - winSum P ω
      = (piVal P.α (futures (back3 ω))
            - (P.α - 1) * ∑ k ∈ Finset.range 3, dR (futures (back3 ω)) k * (P.α⁻¹) ^ (k + 1))
        - (P.wVal (pasts (back3 ω))
            - ∑ m ∈ Finset.range 4, P.cCoef m * dR (pasts (back3 ω)) m) := by
    rw [fRaw, winSum]; ring
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add h1 h2)


namespace TwoAddSqrt3

/-! ## Exact comparisons in `ℤ[√3]`

`0 ≤ A + B√3` and `0 < A + B√3` are decided by squaring.  These two predicates are the only
place the certificate touches `√3`; every table check below runs in `ℤ`. -/

/-- Decides `0 ≤ A + B√3` for integers `A`, `B`. -/
def nnneg3 (A B : ℤ) : Bool :=
  if 0 ≤ B then (0 ≤ A || A * A ≤ 3 * B * B) else (0 ≤ A && 3 * B * B ≤ A * A)

/-- Decides `0 < A + B√3` for integers `A`, `B`. -/
def pos3 (A B : ℤ) : Bool :=
  if 0 ≤ B then (0 < A || A * A < 3 * B * B) else (0 < A && 3 * B * B < A * A)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem nonneg_of_nnneg3 {A B : ℤ} (h : nnneg3 A B = true) :
    (0 : ℝ) ≤ (A : ℝ) + (B : ℝ) * Real.sqrt 3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [nnneg3] at h
  split_ifs at h with hB <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  · have hB' : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    rcases h with hA | hA
    · have : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      nlinarith [mul_nonneg hB' hs0]
    · have : (A : ℝ) * A ≤ 3 * (B : ℝ) * B := by exact_mod_cast hA
      nlinarith [mul_nonneg hB' hs0, sq_nonneg ((A : ℝ) + (B : ℝ) * Real.sqrt 3)]
  · have hB' : (B : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hB
    have hA : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast h.1
    have hA2 : 3 * (B : ℝ) * B ≤ (A : ℝ) * A := by exact_mod_cast h.2
    nlinarith [sq_nonneg ((A : ℝ) + (B : ℝ) * Real.sqrt 3),
      mul_nonpos_of_nonpos_of_nonneg hB'.le hs0]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pos_of_pos3 {A B : ℤ} (h : pos3 A B = true) :
    (0 : ℝ) < (A : ℝ) + (B : ℝ) * Real.sqrt 3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [pos3] at h
  split_ifs at h with hB <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  · have hB' : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    rcases h with hA | hA
    · have : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
      nlinarith [mul_nonneg hB' hs0]
    · have : (A : ℝ) * A < 3 * (B : ℝ) * B := by exact_mod_cast hA
      nlinarith [mul_nonneg hB' hs0, sq_nonneg ((A : ℝ) + (B : ℝ) * Real.sqrt 3)]
  · have hB' : (B : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hB
    have hA : (0 : ℝ) < (A : ℝ) := by exact_mod_cast h.1
    have hA2 : 3 * (B : ℝ) * B < (A : ℝ) * A := by exact_mod_cast h.2
    nlinarith [sq_nonneg ((A : ℝ) + (B : ℝ) * Real.sqrt 3),
      mul_nonpos_of_nonpos_of_nonneg hB'.le hs0]

/-! ## The window tables

Generated by `BB61/m4_window_tables.py`, which cross-checks every entry against
`BB61/m4_lean_cert.json` — the same run that produced `w0L`, `w1L` in `BB61/Pressure.lean`. -/

/-- `bN b` is the digit `b ∈ {0,1}` as a natural number. -/
def bN (b : Bool) : ℕ := if b then 1 else 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bN_le (b : Bool) : bN b ≤ 1 := by cases b <;> simp [bN]

/-- The bit of the word `u` at place value `k`, as an integer. -/
def bitAt (u k : ℕ) : ℤ := (u / k % 2 : ℕ)

/-- The rational part of the exact window value `p + q√3` of the seven-bit word `u`.
The weights are `(1-β)βᵏ` with `β = 2 - √3`, ordered `k = 3,2,1,0,0,1,2` from the oldest
letter `ω(-6)` to the newest letter `ω 0`. -/
def winP (u : ℕ) : ℤ :=
  -71 * bitAt u 1 - 19 * bitAt u 2 - 5 * bitAt u 4 - bitAt u 8
    - bitAt u 16 - 5 * bitAt u 32 - 19 * bitAt u 64

/-- The `√3`-part of the exact window value of the word `u`. -/
def winQ (u : ℕ) : ℤ :=
  41 * bitAt u 1 + 11 * bitAt u 2 + 3 * bitAt u 4 + bitAt u 8
    + bitAt u 16 + 3 * bitAt u 32 + 11 * bitAt u 64

/-- `⌊8 (F̃ - ε)⌋` for each of the `128` words. -/
def LLL : List ℤ :=
  [-1, -1, 0, 0, 1, 1, 1, 1, 5, 5, 6, 6, 7, 7, 7, 7, 5, 5, 6, 6, 7, 7, 7, 7, 11, 11, 11, 12,
   13, 13, 13, 13, 1, 1, 1, 1, 2, 3, 3, 3, 7, 7, 7, 7, 8, 8, 9, 9, 7, 7, 7, 7, 8, 8, 9, 9, 13,
   13, 13, 13, 14, 14, 15, 15, 0, 0, 0, 0, 1, 1, 2, 2, 6, 6, 6, 6, 7, 7, 8, 8, 6, 6, 6, 6, 7,
   7, 8, 8, 11, 12, 12, 12, 13, 13, 13, 14, 1, 1, 2, 2, 3, 3, 3, 3, 7, 7, 8, 8, 9, 9, 9, 9, 7,
   7, 8, 8, 9, 9, 9, 9, 13, 13, 13, 14, 15, 15, 15, 15]

/-- `⌊8 (F̃ + ε)⌋` for each of the `128` words. -/
def HHL : List ℤ :=
  [0, 0, 0, 0, 1, 1, 2, 2, 6, 6, 6, 6, 7, 7, 8, 8, 6, 6, 6, 6, 7, 7, 8, 8, 11, 12, 12, 12, 13,
   13, 13, 14, 1, 1, 2, 2, 3, 3, 3, 3, 7, 7, 8, 8, 9, 9, 9, 9, 7, 7, 8, 8, 9, 9, 9, 9, 13, 13,
   13, 14, 15, 15, 15, 15, 0, 0, 1, 1, 2, 2, 2, 2, 6, 6, 6, 7, 8, 8, 8, 8, 6, 6, 6, 7, 8, 8, 8,
   8, 12, 12, 12, 12, 13, 14, 14, 14, 2, 2, 2, 2, 3, 3, 4, 4, 8, 8, 8, 8, 9, 9, 10, 10, 8, 8,
   8, 8, 9, 9, 10, 10, 13, 14, 14, 14, 15, 15, 15, 16]

/-- The eight cell weights of the equipartition of the circle. -/
def cwL : List ℕ := [24, 32, 54, 153, 153, 50, 32, 24]

/-- The weight of the cell an integer indexes, `cw (n mod 8)`. -/
def cwZ (n : ℤ) : ℕ := cwL.getD (n % 8).toNat 0

/-- The certificate's edge weight, re-indexed by the seven-bit word instead of by
`(state, symbol)`: `wcert u = w0 u` for `u < 64` and `w1 (u-64)` above. -/
def wcert (u : ℕ) : ℕ := if u < 64 then w0L.getD u 0 else w1L.getD (u - 64) 0

/-- The four table facts, as one closed boolean computation over the `128` words:
`8(F̃-ε) ≥ L`, `8(F̃+ε) < H+1`, `L ≤ H ≤ L+1`, and both cells are dominated by the edge
weight.  Note `8ε = 984 - 568√3`. -/
def wordOK (u : ℕ) : Bool :=
  let L := LLL.getD u 0
  let H := HHL.getD u 0
  nnneg3 (8 * winP u - 984 - L) (8 * winQ u + 568)
    && pos3 (H + 1 - 8 * winP u - 984) (568 - 8 * winQ u)
    && (L ≤ H && H ≤ L + 1)
    && (cwZ L ≤ wcert u && cwZ H ≤ wcert u)

/-- All `128` words pass, in exact integer arithmetic. -/
def windowOK : Bool := (List.range 128).all wordOK

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem windowOK_true : windowOK = true := by decide

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wordOK_true {u : ℕ} (hu : u < 128) : wordOK u = true := by
  have h := windowOK_true
  simp only [windowOK, List.all_eq_true, List.mem_range] at h
  exact h u hu

/-! ## The cell weight of a point

`cwZ n` is the weight of the cell indexed by `n mod 8`; the cell of a real `x` is
`cwZ ⌊8x⌋`, since `⌊8 · Int.fract x⌋ ≡ ⌊8x⌋ (mod 8)`.  The one estimate this section
proves is the modelling bound itself: a point within `ε` of the window value of a word
lies in one of the (at most two) cells the word admits, both dominated by its edge
weight. -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cwL_bounds {k : ℕ} (hk : k < 8) : 24 ≤ cwL.getD k 0 ∧ cwL.getD k 0 ≤ 153 := by
  interval_cases k <;> simp [cwL]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cwZ_bounds (n : ℤ) : 24 ≤ cwZ n ∧ cwZ n ≤ 153 := cwL_bounds (by omega)

/-- **The modelling bound, per word.**  If `x` is within `ε = 123 - 71√3` of the exact window
value `winP u + winQ u · √3`, then the weight of the cell of `x` is at most the edge weight
`wcert u` the transfer certificate assigns to the word `u`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cwZ_floor_le {u : ℕ} (hu : u < 128) {x : ℝ}
    (hx : |x - ((winP u : ℝ) + (winQ u : ℝ) * Real.sqrt 3)| ≤ 123 - 71 * Real.sqrt 3) :
    cwZ ⌊8 * x⌋ ≤ wcert u := by
  have h := wordOK_true hu
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := h
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have hlo := nonneg_of_nnneg3 h1
  have hhi := pos_of_pos3 h2
  push_cast at hlo hhi
  have hL : ((LLL.getD u 0 : ℤ) : ℝ) ≤ 8 * x := by nlinarith
  have hH : 8 * x < ((HHL.getD u 0 : ℤ) : ℝ) + 1 := by nlinarith
  have hfl : LLL.getD u 0 ≤ ⌊8 * x⌋ := Int.le_floor.2 hL
  have hfh : ⌊8 * x⌋ ≤ HHL.getD u 0 := by
    have h' : ⌊8 * x⌋ < HHL.getD u 0 + 1 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  have hcase : ⌊8 * x⌋ = LLL.getD u 0 ∨ ⌊8 * x⌋ = HHL.getD u 0 := by omega
  rcases hcase with he | he <;> rw [he] <;> assumption

/-! ## The state observable

The transfer operator shifts states downwards, so the newest letter of the window has to be
the one the partition reads.  That fixes the bit convention: bit `i` of the word is `ω(i-6)`,
the state is bits `0..5` and the symbol `ω 0` is bit `6`. -/

/-- The six-bit state of `ω`: bit `i` is `ω(i-6)`, for `i < 6`. -/
def stVal (ω : Shift) : ℕ :=
  bN (ω (-6)) + 2 * bN (ω (-5)) + 4 * bN (ω (-4)) + 8 * bN (ω (-3))
    + 16 * bN (ω (-2)) + 32 * bN (ω (-1))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem stVal_lt (ω : Shift) : stVal ω < 64 := by
  have h6 := bN_le (ω (-6)); have h5 := bN_le (ω (-5)); have h4 := bN_le (ω (-4))
  have h3 := bN_le (ω (-3)); have h2 := bN_le (ω (-2)); have h1 := bN_le (ω (-1))
  unfold stVal
  omega

/-- **The state observable of the window certificate.** -/
def stateOf (ω : Shift) : St := ⟨stVal ω, stVal_lt ω⟩

/-- The seven-bit window word `ω(-6), …, ω(0)`: the state, plus the new letter on top. -/
def wordOf (ω : Shift) : ℕ := stVal ω + 64 * bN (ω 0)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wordOf_lt (ω : Shift) : wordOf ω < 128 := by
  have h0 := bN_le (ω 0)
  have := stVal_lt ω
  unfold wordOf
  omega

/-- **The window slides under the shift.**  This is the successor map `tgtB` of the
certificate of `BB61/Pressure.lean`, and it is the reason the state has to be read six
places *behind* the coordinate the partition reads. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem stateOf_shiftZ (ω : Shift) :
    stateOf (shiftZ ω) = tgtB (stateOf ω) (coordPartition ω) := by
  have e6 : shiftZ ω (-6) = ω (-5) := by norm_num [shiftZ]
  have e5 : shiftZ ω (-5) = ω (-4) := by norm_num [shiftZ]
  have e4 : shiftZ ω (-4) = ω (-3) := by norm_num [shiftZ]
  have e3 : shiftZ ω (-3) = ω (-2) := by norm_num [shiftZ]
  have e2 : shiftZ ω (-2) = ω (-1) := by norm_num [shiftZ]
  have e1 : shiftZ ω (-1) = ω 0 := by norm_num [shiftZ]
  have hval : ∀ b : Bool, (tgtB (stateOf ω) b).val = stVal ω / 2 + 32 * bN b := by
    intro b; cases b <;> simp [tgtB, t0, t1, stateOf, bN]
  have h6 := bN_le (ω (-6)); have h5 := bN_le (ω (-5)); have h4 := bN_le (ω (-4))
  have h3 := bN_le (ω (-3)); have h2 := bN_le (ω (-2)); have h1 := bN_le (ω (-1))
  apply Fin.ext
  show stVal (shiftZ ω) = (tgtB (stateOf ω) (coordPartition ω)).val
  rw [hval, stVal, stVal, e6, e5, e4, e3, e2, e1, coordPartition]
  omega

/-- The certificate's edge weight, read off the window word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wB_eq_wcert (ω : Shift) :
    wB (stateOf ω) (coordPartition ω) = wcert (wordOf ω) := by
  have hs := stVal_lt ω
  cases hc : ω 0 <;>
    simp [wB, wcert, w0, w1, coordPartition, hc, wordOf, bN, stateOf, hs]

/-- The seven bits of the window word are the seven letters `ω(-6), …, ω(0)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bitAt_wordOf (ω : Shift) :
    bitAt (wordOf ω) 1 = (bN (ω (-6)) : ℤ) ∧ bitAt (wordOf ω) 2 = (bN (ω (-5)) : ℤ) ∧
      bitAt (wordOf ω) 4 = (bN (ω (-4)) : ℤ) ∧ bitAt (wordOf ω) 8 = (bN (ω (-3)) : ℤ) ∧
      bitAt (wordOf ω) 16 = (bN (ω (-2)) : ℤ) ∧ bitAt (wordOf ω) 32 = (bN (ω (-1)) : ℤ) ∧
      bitAt (wordOf ω) 64 = (bN (ω 0) : ℤ) := by
  have h6 := bN_le (ω (-6)); have h5 := bN_le (ω (-5)); have h4 := bN_le (ω (-4))
  have h3 := bN_le (ω (-3)); have h2 := bN_le (ω (-2)); have h1 := bN_le (ω (-1))
  have h0 := bN_le (ω 0)
  simp only [bitAt, wordOf, stVal, Nat.cast_inj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega


/-! ## `√3`, and the conjugate at `α = 2 + √3` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_lt_sqrt3 : (1 : ℝ) < Real.sqrt 3 := by
  nlinarith [sq_sqrt3, Real.sqrt_nonneg 3]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrt3_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sq_sqrt3, Real.sqrt_nonneg 3]

/-- `α = 2 + √3` forces the trace to be `4`: `√3` is irrational, so the coefficient of `√3` in
`α² = aα + b` has to vanish. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem trace_eq_four (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) : P.a = 4 := by
  by_contra hne
  have hcoef : (P.a - 4 : ℤ) ≠ 0 := by omega
  have h := P.root
  rw [hα] at h
  have heq : ((P.a - 4 : ℤ) : ℝ) * Real.sqrt 3 = ((7 - 2 * P.a - P.b : ℤ) : ℝ) := by
    push_cast
    linear_combination -h + sq_sqrt3
  have hirr : Irrational (Real.sqrt 3) := by
    simpa using (Nat.prime_three).irrational_sqrt
  exact (hirr.intCast_mul hcoef).ne_int (7 - 2 * P.a - P.b) heq

/-- `α = 2 + √3` is a **unit**: the norm `-b` is `1`.  This is what the entropy floor of
`CITED/LedrappierYoung.lean` needs, and it comes for free from the trace. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_eq_neg_one (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) : P.b = -1 := by
  have ha := trace_eq_four P hα
  have h := P.root
  rw [hα, ha] at h
  have hb : ((P.b : ℤ) : ℝ) = -1 := by push_cast at h ⊢; linear_combination -h + sq_sqrt3
  exact_mod_cast hb

/-- The conjugate at `α = 2 + √3`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_eq (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) : P.β = 2 - Real.sqrt 3 := by
  rw [QuadSetup.β, trace_eq_four P hα, hα]
  push_cast
  ring

/-- `2 + √3` is a unit of norm one: `α⁻¹ = 2 - √3 = β`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_alpha (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) : P.α⁻¹ = 2 - Real.sqrt 3 := by
  rw [hα]
  exact inv_eq_of_mul_eq_one_right (by linear_combination -sq_sqrt3)

/-! ## The window value is exactly `winP + winQ √3` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_eq_bN (δ : ℕ → Bool) (k : ℕ) : dR δ k = (bN (δ k) : ℝ) := by
  unfold dR bN
  split <;> norm_num

/-- **The window value, exactly.**  All seven weights are `(1-β)βᵏ`, `k ≤ 3`, and each is an
element `p + q√3` of `ℤ[√3]`; the resulting value of the seven-letter block is the certificate
table entry `winP (wordOf ω) + winQ (wordOf ω) √3`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem winSum_eq (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) (ω : Shift) :
    winSum P ω = (winP (wordOf ω) : ℝ) + (winQ (wordOf ω) : ℝ) * Real.sqrt 3 := by
  have hβ := beta_eq P hα
  have hinv := inv_alpha P hα
  have c0 : (P.α - 1) * P.α⁻¹ ^ 1 = -1 + Real.sqrt 3 := by
    rw [hinv, hα]; linear_combination (-1 : ℝ) * sq_sqrt3
  have c1 : (P.α - 1) * P.α⁻¹ ^ 2 = -5 + 3 * Real.sqrt 3 := by
    rw [hinv, hα]; linear_combination (Real.sqrt 3 - 3) * sq_sqrt3
  have c2 : (P.α - 1) * P.α⁻¹ ^ 3 = -19 + 11 * Real.sqrt 3 := by
    rw [hinv, hα]; linear_combination (-(Real.sqrt 3 ^ 2) + 5 * Real.sqrt 3 - 9) * sq_sqrt3
  have d0 : (P.β - 1) * P.β ^ 0 = 1 - Real.sqrt 3 := by rw [hβ]; ring
  have d1 : (P.β - 1) * P.β ^ 1 = 5 - 3 * Real.sqrt 3 := by
    rw [hβ]; linear_combination sq_sqrt3
  have d2 : (P.β - 1) * P.β ^ 2 = 19 - 11 * Real.sqrt 3 := by
    rw [hβ]; linear_combination (5 - Real.sqrt 3) * sq_sqrt3
  have d3 : (P.β - 1) * P.β ^ 3 = 71 - 41 * Real.sqrt 3 := by
    rw [hβ]; linear_combination (Real.sqrt 3 ^ 2 - 7 * Real.sqrt 3 + 21) * sq_sqrt3
  have f0 : futures (back3 ω) 0 = ω (-2) := by norm_num [futures, back3]
  have f1 : futures (back3 ω) 1 = ω (-1) := by norm_num [futures, back3]
  have f2 : futures (back3 ω) 2 = ω 0 := by norm_num [futures, back3]
  have p0 : pasts (back3 ω) 0 = ω (-3) := by norm_num [pasts, back3]
  have p1 : pasts (back3 ω) 1 = ω (-4) := by norm_num [pasts, back3]
  have p2 : pasts (back3 ω) 2 = ω (-5) := by norm_num [pasts, back3]
  have p3 : pasts (back3 ω) 3 = ω (-6) := by norm_num [pasts, back3]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := bitAt_wordOf ω
  rw [winP, winQ, b0, b1, b2, b3, b4, b5, b6]
  simp only [winSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, QuadSetup.cCoef,
    dR_eq_bN, f0, f1, f2, p0, p1, p2, p3]
  push_cast
  linear_combination (bN (ω (-2)) : ℝ) * c0 + (bN (ω (-1)) : ℝ) * c1 + (bN (ω 0) : ℝ) * c2
    - (bN (ω (-3)) : ℝ) * d0 - (bN (ω (-4)) : ℝ) * d1 - (bN (ω (-5)) : ℝ) * d2
    - (bN (ω (-6)) : ℝ) * d3

/-- **M1 Lemma 6's truncation bound, exactly.**  `ε = α⁻³ + |β-1||β|⁴/(1-|β|) = 123 - 71√3`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eps_eq (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) :
    (P.α⁻¹) ^ 3 + |P.β - 1| * |P.β| ^ 4 / (1 - |P.β|) = 123 - 71 * Real.sqrt 3 := by
  have h1 := one_lt_sqrt3
  have h2 := sqrt3_lt_two
  have hβ := beta_eq P hα
  have hinv := inv_alpha P hα
  have habs : |P.β| = 2 - Real.sqrt 3 := by
    rw [hβ, abs_of_nonneg (by linarith)]
  have habs1 : |P.β - 1| = Real.sqrt 3 - 1 := by
    rw [hβ, abs_of_nonpos (by linarith)]
    ring
  have hne : Real.sqrt 3 - 1 ≠ 0 := by linarith
  have key : (Real.sqrt 3 - 1) * (2 - Real.sqrt 3) ^ 4 / (Real.sqrt 3 - 1)
      = (2 - Real.sqrt 3) ^ 4 := by field_simp
  rw [hinv, habs, habs1, show (1 : ℝ) - (2 - Real.sqrt 3) = Real.sqrt 3 - 1 by ring, key]
  linear_combination (Real.sqrt 3 ^ 2 - 9 * Real.sqrt 3 + 33) * sq_sqrt3

/-! ## The cell potential and the modelling lemma -/

/-- The cell potential on the line: the logarithm of the weight of the cell of the
equipartition of the circle into `B = 8` intervals that `x` falls into.  It is `1`-periodic,
bounded, Borel — and nowhere continuous, which is exactly M4's point: the Jensen half of the
variational principle never asked for continuity. -/
noncomputable def cellPot (x : ℝ) : ℝ := Real.log ((cwZ ⌊8 * x⌋ : ℕ) : ℝ)

/-- **The potential of the certificate**: the cell potential of the factor map, read three
steps in the past. -/
noncomputable def gWin (P : QuadSetup) (ω : Shift) : ℝ := cellPot (P.fRaw (back3 ω))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_cellPot : Measurable cellPot :=
  (Measurable.of_discrete (f := fun n : ℤ => Real.log ((cwZ n : ℕ) : ℝ))).comp
    (Int.measurable_floor.comp (measurable_id.const_mul 8))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_gWin (P : QuadSetup) : Measurable (gWin P) :=
  measurable_cellPot.comp (P.continuous_fRaw.comp continuous_back3).measurable

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_cellPot_le (x : ℝ) : |cellPot x| ≤ Real.log 153 := by
  obtain ⟨h1, h2⟩ := cwZ_bounds ⌊8 * x⌋
  have hlo : (1 : ℝ) ≤ ((cwZ ⌊8 * x⌋ : ℕ) : ℝ) := by exact_mod_cast le_trans (by norm_num) h1
  have hhi : ((cwZ ⌊8 * x⌋ : ℕ) : ℝ) ≤ 153 := by exact_mod_cast h2
  have hnn : 0 ≤ cellPot x := Real.log_nonneg hlo
  have hup : cellPot x ≤ Real.log 153 := Real.log_le_log (by linarith) hhi
  rw [abs_of_nonneg hnn]
  exact hup

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_gWin_le (P : QuadSetup) (ω : Shift) : |gWin P ω| ≤ Real.log 153 :=
  abs_cellPot_le _

/-- **The window modelling lemma.**  The state observable `stateOf` slides under the shift into
the successor map of the certificate, and the exponential of the cell potential is dominated by
the certificate's edge weight.  These are exactly the two hypotheses
`two_add_sqrt3_not_equidistributed_of_window` asks for. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exp_gWin_le (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3) (ω : Shift) :
    Real.exp (gWin P ω) ≤ (wB (stateOf ω) (coordPartition ω) : ℝ) := by
  have hpos : (0 : ℝ) < ((cwZ ⌊8 * P.fRaw (back3 ω)⌋ : ℕ) : ℝ) := by
    have := (cwZ_bounds ⌊8 * P.fRaw (back3 ω)⌋).1
    have : (0 : ℕ) < cwZ ⌊8 * P.fRaw (back3 ω)⌋ := by omega
    exact_mod_cast this
  have hx : |P.fRaw (back3 ω)
      - ((winP (wordOf ω) : ℝ) + (winQ (wordOf ω) : ℝ) * Real.sqrt 3)|
      ≤ 123 - 71 * Real.sqrt 3 := by
    rw [← winSum_eq P hα ω, ← eps_eq P hα]
    exact abs_fRaw_back3_sub P ω
  rw [gWin, cellPot, Real.exp_log hpos, wB_eq_wcert]
  exact_mod_cast cwZ_floor_le (wordOf_lt ω) hx


/-! ## The Lebesgue mean of the cell potential

The last input the criterion needs beyond the cited entropy floor: every measure with
`F_*μ = Leb` gives the cell potential its Lebesgue mean `(1/8) log W`, `W = ∏ⱼ wⱼ`.  This is
where the potential being a *step function* pays for itself — the mean is a finite sum of
`log wⱼ`, computed by splitting `[0,1]` into the eight cells. -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cwZ_add_eight (n : ℤ) : cwZ (n + 8) = cwZ n := by
  have h : (n + 8) % 8 = n % 8 := by omega
  rw [cwZ, cwZ, h]

/-- The cell potential is invariant under integer translation — it is a function on the
circle. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cellPot_add_int (x : ℝ) (n : ℤ) : cellPot (x + n) = cellPot x := by
  have h : (8 : ℝ) * (x + n) = 8 * x + ((8 * n : ℤ) : ℝ) := by push_cast; ring
  have hm : (⌊8 * x⌋ + 8 * n) % 8 = ⌊8 * x⌋ % 8 := by omega
  rw [cellPot, cellPot, h, Int.floor_add_intCast, cwZ, cwZ, hm]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem periodic_cellPot : Function.Periodic cellPot 1 := by
  intro x
  simpa using cellPot_add_int x 1

/-- The cell potential as a function on the circle. -/
noncomputable def cellPotC : AddCircle (1 : ℝ) → ℝ := AddCircle.liftIoc 1 0 cellPot

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cellPotC_coe (y : ℝ) : cellPotC ((y : ℝ) : AddCircle (1 : ℝ)) = cellPot y := by
  have hc : (((AddCircle.equivIoc (1 : ℝ) 0) ((y : ℝ) : AddCircle (1 : ℝ)) : ℝ)
      : AddCircle (1 : ℝ)) = ((y : ℝ) : AddCircle (1 : ℝ)) := AddCircle.coe_equivIoc
  obtain ⟨n, hn⟩ :=
    AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_iff_sub_mem.1 hc)
  have hrep : (((AddCircle.equivIoc (1 : ℝ) 0) ((y : ℝ) : AddCircle (1 : ℝ))) : ℝ) = y + n := by
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  show cellPot _ = cellPot y
  rw [hrep, cellPot_add_int]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_cellPotC : Measurable cellPotC :=
  measurable_cellPot.comp
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable)

/-! ### The eight cells -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cellPot_eq_of_mem {j : ℕ} (hj : j < 8) {x : ℝ}
    (h1 : (j : ℝ) / 8 ≤ x) (h2 : x < ((j : ℝ) + 1) / 8) :
    cellPot x = Real.log ((cwL.getD j 0 : ℕ) : ℝ) := by
  have hfl : ⌊8 * x⌋ = (j : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have hmod : ((j : ℤ) % 8).toNat = j := by omega
  rw [cellPot, hfl, cwZ, hmod]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem intervalIntegrable_cellPot (a b : ℝ) :
    IntervalIntegrable cellPot (volume : Measure ℝ) a b := by
  constructor <;>
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      measurable_cellPot.aestronglyMeasurable (M := Real.log 153)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_cellPot_le x)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cell {j : ℕ} (hj : j < 8) :
    ∫ x in ((j : ℝ) / 8)..(((j : ℝ) + 1) / 8), cellPot x
      = Real.log ((cwL.getD j 0 : ℕ) : ℝ) / 8 := by
  have hle : (j : ℝ) / 8 ≤ ((j : ℝ) + 1) / 8 := by linarith
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ ((j : ℝ) + 1) / 8 := by
    rw [ae_iff]
    simp
  have hcongr : ∫ x in ((j : ℝ) / 8)..(((j : ℝ) + 1) / 8), cellPot x
      = ∫ _x in ((j : ℝ) / 8)..(((j : ℝ) + 1) / 8), Real.log ((cwL.getD j 0 : ℕ) : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hle] at hmem
    exact cellPot_eq_of_mem hj hmem.1.le (lt_of_le_of_ne hmem.2 hx)
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- `W = ∏ⱼ wⱼ`, split. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_WW : Real.log ((WW : ℕ) : ℝ)
    = Real.log 24 + Real.log 32 + Real.log 54 + Real.log 153 + Real.log 153 + Real.log 50
      + Real.log 32 + Real.log 24 := by
  have h : ((WW : ℕ) : ℝ) = 24 * 32 * 54 * 153 * 153 * 50 * 32 * 24 := by norm_num [WW]
  rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- **The Lebesgue mean.**  The cell potential integrates to `(1/8) log W` over one period. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cellPot_unit :
    ∫ x in (0 : ℝ)..1, cellPot x = Real.log ((WW : ℕ) : ℝ) / 8 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := (volume : Measure ℝ)) (f := cellPot) (a := fun k : ℕ => (k : ℝ) / 8) (n := 8)
    (fun k _ => intervalIntegrable_cellPot _ _)
  have hterm : ∀ k ∈ Finset.range 8,
      ∫ x in ((k : ℝ) / 8)..(((k + 1 : ℕ) : ℝ) / 8), cellPot x
        = Real.log ((cwL.getD k 0 : ℕ) : ℝ) / 8 := by
    intro k hk
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    exact integral_cell (Finset.mem_range.mp hk)
  rw [Finset.sum_congr rfl hterm, show ((0 : ℕ) : ℝ) / 8 = (0 : ℝ) by norm_num,
    show ((8 : ℕ) : ℝ) / 8 = (1 : ℝ) by norm_num] at hsum
  rw [← hsum, log_WW]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cwL]
  norm_num
  ring

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cellPotC :
    ∫ z, cellPotC z ∂(volume : Measure (AddCircle (1 : ℝ))) = Real.log ((WW : ℕ) : ℝ) / 8 := by
  have h : ∫ z, cellPotC z ∂(volume : Measure (AddCircle (1 : ℝ)))
      = ∫ a in (0 : ℝ)..(0 + 1), cellPot a :=
    AddCircle.integral_liftIoc_eq_intervalIntegral (T := 1) (t := 0) (f := cellPot)
  rw [h]
  simpa using integral_cellPot_unit

/-! ### The mean against a counterexample measure -/

/-- **`hann`, discharged.**  A shift-invariant measure whose `F`-image is Lebesgue gives the
cell potential its Lebesgue mean.  The three-step delay washes out: `back3 ∘ σ³ = id`, and `μ`
is `σ³`-invariant. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_gWin (P : QuadSetup) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ)
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) :
    ∫ ω, gWin P ω ∂μ = Real.log ((WW : ℕ) : ℝ) / 8 := by
  have hmp : MeasurePreserving shiftZ μ μ := ⟨continuous_shiftZ.measurable, hinv⟩
  have hmp3 : MeasurePreserving (shiftZ^[3]) μ μ := hmp.iterate 3
  have hmeas : Measurable fun ω : Shift => cellPotC (P.fMap ω) :=
    measurable_cellPotC.comp P.measurable_fMap
  have hgw : ∀ ω : Shift, gWin P ω = cellPotC (P.fMap (back3 ω)) := by
    intro ω
    rw [gWin, QuadSetup.fMap, cellPotC_coe]
  have hback : ∀ ω : Shift, back3 (shiftZ^[3] ω) = ω := by
    intro ω
    funext k
    simp only [back3, shiftZ_iterate]
    congr 1
    push_cast
    ring
  have hcomp := integral_comp_of_measurePreserving (μ := μ) (S := shiftZ^[3])
    (φ := fun ω : Shift => cellPotC (P.fMap (back3 ω))) hmp3
    ((hmeas.comp continuous_back3.measurable).aestronglyMeasurable)
  simp only [hback] at hcomp
  calc ∫ ω, gWin P ω ∂μ
      = ∫ ω, cellPotC (P.fMap (back3 ω)) ∂μ := by simp_rw [hgw]
    _ = ∫ ω, cellPotC (P.fMap ω) ∂μ := hcomp.symm
    _ = ∫ z, cellPotC z ∂(Measure.map P.fMap μ) :=
        (integral_map P.measurable_fMap.aemeasurable measurable_cellPotC.aestronglyMeasurable).symm
    _ = Real.log ((WW : ℕ) : ℝ) / 8 := by rw [hmap]; exact integral_cellPotC


/-! ## Problem 10.61 at `α = 2 + √3`

Everything the certificate needs about the shift is now a theorem: the state observable, its
transition rule, the edge weights, and the exact `ℤ[√3]` arithmetic that ties the cell
potential to them.  Two hypotheses remain, and they are precisely the two `note-1061-M4.html`
declares external. -/

/-- **Problem 10.61 at `α = 2 + √3`, modulo the Lebesgue mean and the entropy floor.**

No point of `C(2+√3)` has `(ξ αⁿ)` uniformly distributed modulo one, given

* `hann` — every counterexample measure reproduces the Lebesgue mean `(1/8) log W` of the cell
  potential.  This is immediate from `F_*μ = Leb` and the eight cells having equal measure
  `1/8`, `W = ∏ⱼ wⱼ` being their weight product;
* `hfloor` — M3 Theorem 11's entropy floor `h_min(α) = ½ log α`, which rests on the dimension
  theory of hyperbolic measures ([BPS99], [LY85]) and is far outside Mathlib.

The window modelling lemma — the state observable, its transition rule and the domination of
the cell potential — is discharged here (`stateOf_shiftZ`, `exp_gWin_le`), and the numeric
certificate in `BB61/Pressure.lean` (`certB`, `log_rate_lt_floor`).

`2 + √3` is the smallest `α` of the M0 sweep at which Route A is blind (`A(α) = 1.0526 > 1`),
so this is out of reach of `BB61/RouteA.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_equidistributed_of_mean (P : QuadSetup)
    (hα : P.α = 2 + Real.sqrt 3)
    (hann : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      ∫ ω, gWin P ω ∂μ = Real.log WW / 8)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      Real.log P.α / 2 ≤ entropyRate shiftZ μ coordPartition) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  two_add_sqrt3_not_equidistributed_of_window P hα (measurable_gWin P) (abs_gWin_le P)
    stateOf stateOf_shiftZ (exp_gWin_le P hα) hann hfloor


/-- **Problem 10.61 at `α = 2 + √3`.**  No point of `C(2+√3)` has `(ξ αⁿ)` uniformly
distributed modulo one — given M3 Theorem 11's entropy floor, and nothing else.

Everything else is a theorem of this repository:

* the numeric certificate — `BB61/Pressure.lean`, exact in `ℤ[√3]`: the `64`-state transfer
  operator `certB` and the mean-corrected criterion `log_rate_lt_floor`,
  `log(a/b) - (1/8) log W = 0.600637 < 0.658479 = ½ log(2+√3)`;
* the variational half — `ForMathlib/Dynamics/TopologicalPressure.lean` and
  `BB61/PressureCriterion.lean`: `h_μ(σ,P) + ∫ψ dμ ≤ P(σ,ψ,P)` over the coordinate partition;
* the transfer bridge — `ForMathlib/Dynamics/PressureTransfer.lean`: a potential dominated by a
  finite-state operator has pressure at most the operator's certified growth rate;
* the **window modelling lemma** — this file: `stateOf_shiftZ` and `exp_gWin_le`;
* the **Lebesgue mean** — this file: `integral_gWin`;
* the reduction to invariant measures — `BB61/Saturation.lean`, M1 Corollary 9.

The entropy floor `hfloor` rests on the dimension theory of hyperbolic measures ([BPS99],
[LY85]) and is far outside Mathlib; carrying it as a hypothesis keeps `BB61/` axiom-free and
citation-free.

`2 + √3` is the smallest `α` of the M0 sweep at which Route A is blind (`A(α) = 1.0526 > 1`),
so this is out of reach of `BB61/RouteA.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_add_sqrt3_not_equidistributed (P : QuadSetup) (hα : P.α = 2 + Real.sqrt 3)
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      Real.log P.α / 2 ≤ entropyRate shiftZ μ coordPartition) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n :=
  two_add_sqrt3_not_equidistributed_of_mean P hα
    (fun _ hp hi hm => @integral_gWin P _ hp hi hm) hfloor


/-- `α = 2 + √3`, the root of `X² - 4X + 1`: trace `4`, norm `1`, conjugate `2 - √3 = α⁻¹`.
A witness that the hypothesis `hα` below is satisfiable — the statement is about a genuine
`QuadSetup`, not an empty one. -/
noncomputable def sqrtThree : QuadSetup where
  a := 4
  b := -1
  α := 2 + Real.sqrt 3
  root := by push_cast; linear_combination sq_sqrt3
  one_lt := by linarith [Real.sqrt_nonneg 3]
  conj_lt := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith [one_lt_sqrt3, sqrt3_lt_two]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrtThree_alpha : sqrtThree.α = 2 + Real.sqrt 3 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrtThree_beta : sqrtThree.β = 2 - Real.sqrt 3 := beta_eq _ rfl

/-- **Problem 10.61 at `α = 2 + √3`, stated at the number itself.**  `sqrtThree` is the
`QuadSetup` of `2 + √3`; the only hypothesis is M3 Theorem 11's entropy floor. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_two_add_sqrt3_not_equidistributed
    (hfloor : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      Measure.map sqrtThree.fMap μ = (volume : Measure (AddCircle (1 : ℝ))) →
      Real.log (2 + Real.sqrt 3) / 2 ≤ entropyRate shiftZ μ coordPartition) :
    ∀ ξ ∈ cantorSet (2 + Real.sqrt 3),
      ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * (2 + Real.sqrt 3) ^ n :=
  two_add_sqrt3_not_equidistributed sqrtThree rfl hfloor


end TwoAddSqrt3

end BB61
