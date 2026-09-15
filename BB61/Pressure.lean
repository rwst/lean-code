/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.PathGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A machine-checked pressure certificate at `α = 2 + √3`

Formal companion of `note-1061-M4.html` (milestone M4 of `plans/plan-1061.html`).

M3 replaced the Route-D LP by a **pressure certificate**: 10.61 holds at a Pisot unit `α`
as soon as some potential `ψ = g ∘ F` of Lebesgue mean zero has topological pressure below
the entropy floor `h_min(α) = (1/log α + 1/log(1/ρ))⁻¹`, which for a quadratic unit is
`½ log α`.  M4 observes that `g` need not be continuous — only bounded and Borel, since
`F_*μ = Leb` gives `∫ g∘F dμ = ∫ g dLeb` for any such `g`, and the Jensen half of the
variational principle never used continuity either.  Taking `g` constant on the `B` cells
of an equipartition of the circle makes every weight **rational**, and the window
truncation is absorbed by interval arithmetic instead of a Lipschitz slack.

That is what this file checks, at `α = 2 + √3` — the smallest `α` of the sweep where
Route A is blind (`A(α) = 1.0526 > 1`), so the certificate is not reachable by
`BB61/RouteA.lean`.

## What is checked here

With window `N = M = 3` (states = 6-bit words, so `64` of them) and `B = 8` cells,
everything lives in `ℤ[√3]` exactly:

* `ε = α⁻³ + C_α ρ⁴/(1-ρ) = (2-√3)³ + (2-√3)⁴ = (2-√3)³(3-√3) = 123 - 71√3`;
* the seven window weights are `-1+√3, -5+3√3, -19+11√3, -71+41√3` (past) and
  `-1+√3, -5+3√3, -19+11√3` (future),

so the cell an edge can occupy is decided by an integer comparison, and the transfer
operator has **integer** entries — the eight cell weights being `24, 32, 54, 153, 153,
50, 32, 24` (`BB61/m4_lean_cert.py` produces them and checks the cell tables against the
floating-point machine on all `128` words).

The growth bound itself is `ForMathlib/Combinatorics/PathGrowth.lean`'s vector
certificate (`psum_le_pow`), the elementary Collatz–Wielandt shadow already in the repo:
a positive integer vector `v` and a ratio `a/b` with `b · (M v) ≤ a · v` entrywise.
Here `a = 95035770`, `b = 2²⁰`, and the mean-corrected criterion

`(a/b)^B < W · α^(B/2)`,  `W = ∏ⱼ wⱼ = 37279413043200`,

is the single inequality `ratio_lt_floor`, equivalently `log_rate_lt_floor`:

`log(a/b) - (1/8) log W = 0.600637 < 0.658479 = ½ log(2+√3)`.

## What is *not* checked here

The bridge from this arithmetic to Problem 10.61 is in two pieces, and only one of them is
still open.

*Done.*  The analytic half is `BB61/PressureCriterion.lean`, on top of
`ForMathlib/Dynamics/TopologicalPressure.lean`: `forall_not_equidistributed_of_partitionPressure_lt`
proves that a potential of pressure below the entropy floor forbids every counterexample
measure, hence 10.61 at `α`.  It carries Theorem 11 of `note-1061-M3.html` (the
Ledrappier–Young floor, resting on [LY85]/[BPS99]) as a hypothesis rather than a cited
axiom, so the file stays citation-free.

The identification of `psum` with the partition function `Dynamics.partitionSum` is done too,
in general form: `ForMathlib/Dynamics/PressureTransfer.lean`'s `TransferBound` and
`partitionPressure_le_of_transferBound`.  Feeding it the `Bool`-alphabet restatement `certB`
below, `two_add_sqrt3_not_equidistributed_of_window` reduces 10.61 at `2 + √3` to three
supplied facts, of which only one is arithmetic here.

The **window modelling lemma** is `BB61/Window.lean`: the state observable recording the
`N = M = 3` window, sliding under the shift and dominating the cell potential.  That is the
exact `ℤ[√3]` arithmetic of `BB61/m4_lean_cert.py` — the window value of each of the 128
words, the cell it can occupy, and M1 Lemma 6's truncation bound `ε = 123 - 71√3` — together
with the Lebesgue mean of the cell potential.  With it,
`BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed` proves **10.61 at `2 + √3`** from the
entropy floor alone.

*Open.*  Nothing at this `α`.  The entropy floor (M3 Theorem 11) is the one cited input, and
`BB61/Floor.lean` discharges it from `LY.entropyRate_floor` (`CITED/LedrappierYoung.lean`;
[You82] at `d = 2`, [LY85], [BPS99]), giving the unconditional
`BB61.problem_10_61_two_add_sqrt3`.

So this file remains deliberately **axiom-free and citation-free**, like the rest of
`BB61/`: it proves the finite half of the certificate, in exact arithmetic, and states it
in the form the analytic half consumes.
-/

namespace BB61

open PathGrowth

/-! ## The two-successor window digraph

A window transfer operator is the labelled digraph in which each state has exactly two
outgoing edges, one per appended symbol.  These two lemmas turn `PathGrowth.outEdges`
into the explicit pair, so that the vector certificate becomes one two-term inequality
per state. -/

section Shift

variable {n : ℕ}

/-- The digraph of a window transfer operator: from each state, one edge per symbol. -/
def shiftE (tgt : Fin n → Fin 2 → Fin n) : Finset (Fin n × Fin 2 × Fin n) :=
  Finset.univ.image fun p : Fin n × Fin 2 => (p.1, p.2, tgt p.1 p.2)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem outEdges_shiftE (tgt : Fin n → Fin 2 → Fin n) (s : Fin n) :
    outEdges (shiftE tgt) s = {(s, 0, tgt s 0), (s, 1, tgt s 1)} := by
  ext e
  simp only [outEdges, shiftE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨u, c⟩, rfl⟩, hs⟩
    simp only at hs
    subst hs
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨(s, 0), rfl⟩, rfl⟩
    · exact ⟨⟨(s, 1), rfl⟩, rfl⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sum_outEdges_shiftE (tgt : Fin n → Fin 2 → Fin n)
    (θ : Fin n × Fin 2 × Fin n → ℕ) (v : Fin n → ℕ) (s : Fin n) :
    ∑ e ∈ outEdges (shiftE tgt) s, θ e * v e.2.2
      = θ (s, 0, tgt s 0) * v (tgt s 0) + θ (s, 1, tgt s 1) * v (tgt s 1) := by
  rw [outEdges_shiftE, Finset.sum_pair (by simp)]

end Shift

/-! ## The certificate at `α = 2 + √3` -/

namespace TwoAddSqrt3

/-- A state of the window `N = M = 3`: a six-bit word. -/
abbrev St := Fin 64

/-- Appending the symbol `0` shifts the window. -/
def t0 (s : St) : St := ⟨s.val / 2, by have := s.isLt; omega⟩

/-- Appending the symbol `1` shifts the window and sets the new leading bit. -/
def t1 (s : St) : St := ⟨s.val / 2 + 32, by have := s.isLt; omega⟩

/-- The successor map of the window digraph. -/
def tgt (s : St) : Fin 2 → St := fun c => if c = 0 then t0 s else t1 s

/-- Edge weights for the symbol `0`, i.e. the largest cell weight the window value can
attain; generated by `BB61/m4_lean_cert.py`. -/
def w0L : List ℕ :=
  [24, 24, 24, 24, 32, 32, 54, 54, 50, 50, 32, 32, 24, 24, 24, 24, 50, 50, 32, 32, 24, 24,
   24, 24, 153, 153, 153, 153, 50, 50, 50, 50, 32, 32, 54, 54, 153, 153, 153, 153, 24, 24,
   24, 24, 32, 32, 32, 32, 24, 24, 24, 24, 32, 32, 32, 32, 50, 50, 50, 50, 32, 32, 24, 24]

/-- Edge weights for the symbol `1`. -/
def w1L : List ℕ :=
  [24, 24, 32, 32, 54, 54, 54, 54, 32, 32, 32, 32, 24, 24, 24, 24, 32, 32, 32, 32, 24, 24,
   24, 24, 153, 153, 153, 153, 50, 50, 50, 32, 54, 54, 54, 54, 153, 153, 153, 153, 24, 24,
   24, 24, 32, 32, 54, 54, 24, 24, 24, 24, 32, 32, 54, 54, 50, 50, 50, 32, 24, 24, 24, 24]

/-- The positive integer vector witnessing the growth ratio. -/
def vL : List ℕ :=
  [47262, 47262, 58844, 58844, 118765, 118765, 133049, 133049, 205696, 205696, 182108,
   182108, 140364, 140364, 140364, 140364, 136969, 136969, 96117, 96117, 65842, 65842,
   65842, 65842, 400000, 400000, 400000, 400000, 158534, 158534, 158534, 129339, 131215,
   131215, 164463, 164463, 397014, 397014, 397014, 397014, 66534, 66534, 66534, 66534,
   96584, 96584, 147003, 147003, 139061, 139061, 139061, 139061, 185415, 185415, 207710,
   207710, 125145, 125145, 125145, 111579, 68310, 68310, 46586, 46586]

def w0 (s : St) : ℕ := w0L.getD s.val 0
def w1 (s : St) : ℕ := w1L.getD s.val 0
def vv (s : St) : ℕ := vL.getD s.val 0

/-- The edge weight of the window digraph. -/
def θ : St × Fin 2 × St → ℕ := fun e => if e.2.1 = 0 then w0 e.1 else w1 e.1

/-- Numerator of the certified growth ratio. -/
def aa : ℕ := 95035770

/-- Denominator of the certified growth ratio, `2^20`. -/
def bb : ℕ := 1048576

/-- The product of the eight cell weights: `exp` of `B` times the Lebesgue mean of the
potential, so dividing by `W^(1/B)` is the mean correction the criterion asks for. -/
def WW : ℕ := 37279413043200

/-- The vector certificate, as a closed boolean computation over the 64 states. -/
def certOK : Bool :=
  (List.range 64).all fun i =>
    bb * (w0L.getD i 0 * vL.getD (i / 2) 0 + w1L.getD i 0 * vL.getD (i / 2 + 32) 0)
      ≤ aa * vL.getD i 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem certOK_true : certOK = true := by decide

/-- The Collatz–Wielandt hypothesis, one two-term inequality per state. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cert (s : St) : bb * (w0 s * vv (t0 s) + w1 s * vv (t1 s)) ≤ aa * vv s := by
  have h := certOK_true
  simp only [certOK, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact h s.val s.isLt

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cert_sum (s : St) :
    bb * ∑ e ∈ outEdges (shiftE tgt) s, θ e * vv e.2.2 ≤ aa * vv s := by
  rw [sum_outEdges_shiftE]
  simpa [θ, tgt] using cert s

/-- **The growth bound.**  The weighted path sum of the window digraph — the partition
function of the cell potential — grows no faster than `(a/b)^k`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem psum_le_pow (k : ℕ) (s : St) :
    ((psum (shiftE tgt) θ vv s k : ℕ) : ℝ) ≤ ((aa : ℝ) / bb) ^ k * vv s :=
  PathGrowth.psum_le_pow _ _ _ _ aa bb (by norm_num [bb]) (fun _ => le_refl _) cert_sum k s

/-- `193 < α⁴` for `α = 2 + √3`: the rational floor used by the integer check. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_alpha_pow_four : (193 : ℝ) < (2 + Real.sqrt 3) ^ 4 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlt : (12 / 7 : ℝ) < Real.sqrt 3 := by
    rw [show (12 / 7 : ℝ) = Real.sqrt ((12 / 7) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  nlinarith [Real.sqrt_nonneg 3, h3, hlt]

/-- **The certificate.**  The mean-corrected growth ratio is below the entropy floor:
`(a/b)^8 < W · α⁴`, i.e. `log(a/b) - (1/8) log W < ½ log α = h_min(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ratio_lt_floor :
    ((aa : ℝ) / bb) ^ 8 < (WW : ℝ) * (2 + Real.sqrt 3) ^ 4 := by
  have hint : (aa : ℝ) ^ 8 < (bb : ℝ) ^ 8 * WW * 193 := by
    have : aa ^ 8 < bb ^ 8 * WW * 193 := by norm_num [aa, bb, WW]
    exact_mod_cast this
  have hb : (0 : ℝ) < (bb : ℝ) ^ 8 := by norm_num [bb]
  have hW : (0 : ℝ) < (WW : ℝ) := by norm_num [WW]
  rw [div_pow, div_lt_iff₀ hb]
  calc (aa : ℝ) ^ 8 < (bb : ℝ) ^ 8 * WW * 193 := hint
    _ ≤ (WW : ℝ) * (2 + Real.sqrt 3) ^ 4 * (bb : ℝ) ^ 8 := by
        nlinarith [lt_alpha_pow_four, mul_pos hW hb]

/-- The same statement in the form the criterion of `note-1061-M4.html` uses:
the certified rate lies strictly below `h_min(2+√3) = ½ log(2+√3)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_rate_lt_floor :
    Real.log ((aa : ℝ) / bb) - Real.log WW / 8 < Real.log (2 + Real.sqrt 3) / 2 := by
  have hα : (0 : ℝ) < 2 + Real.sqrt 3 := by positivity
  have hW : (0 : ℝ) < (WW : ℝ) := by norm_num [WW]
  have hr : (0 : ℝ) < (aa : ℝ) / bb := by norm_num [aa, bb]
  have h := Real.log_lt_log (by positivity) ratio_lt_floor
  rw [Real.log_pow, Real.log_mul (ne_of_gt hW) (by positivity), Real.log_pow] at h
  push_cast at h
  linarith


/-! ## The certificate in the alphabet of the shift

`BB61/PressureCriterion.lean` reads symbols through `coordPartition ω = ω 0`, whose alphabet is
`Bool`.  These are the same data with `Fin 2` replaced by `Bool`, and the certificate restated for
`PathGrowth.detE`, the edge set of a deterministic transfer operator. -/

/-- The successor map, with the alphabet spelled as `Bool`. -/
def tgtB (s : St) : Bool → St := fun c => if c then t1 s else t0 s

/-- The edge weights, with the alphabet spelled as `Bool`. -/
def wB (s : St) : Bool → ℕ := fun c => if c then w1 s else w0 s

/-- Every entry of the certificate vector is positive, as a closed boolean computation. -/
def vvPos : Bool := (List.range 64).all fun i => 1 ≤ vL.getD i 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem vvPos_true : vvPos = true := by decide

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_vv (s : St) : 1 ≤ vv s := by
  have h := vvPos_true
  simp only [vvPos, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  exact h s.val s.isLt

/-- The Collatz–Wielandt hypothesis in the form `PathGrowth`'s vector certificate takes it, over
the deterministic edge set `detE tgtB`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem certB (q : St) :
    bb * ∑ e ∈ PathGrowth.outEdges (PathGrowth.detE tgtB) q, wB e.1 e.2.1 * vv e.2.2
      ≤ aa * vv q := by
  rw [PathGrowth.outEdges_detE,
    Finset.sum_image fun c _ c' _ h => by simpa using congrArg (fun e => e.2.1) h]
  rw [Fintype.sum_bool]
  simpa [wB, tgtB, add_comm] using cert q

end TwoAddSqrt3

end BB61
