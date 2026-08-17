/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.MahlerCount
import TShift.Basic
import TShift.ResidueClass
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Mahler failures at an integer multiplier, and what they settle

`BB13/MahlerFrame.lean` covers the failures of `‖δ(p/q)ⁿ‖ < cⁿ` by at most `K(ε(p,c))` lines for
**every** rational multiplier `δ`.  `BB13/MahlerCount.lean` then confines each line's fibre — but
only at `δ = 1`, and its own docstring says why: for `δ ≠ 1` the residue `δpⁿ − mqⁿ` can vanish,
and the confinement runs on `|kₐ| ≥ 1`.

This file closes that gap for a **natural multiplier `D`** and draws the consequence.  The gap is
one line of arithmetic: `k_a = 0` forces `qᵃ ∣ D` (`residMul_ne_zero_of_not_dvd`), which for the
multipliers this corpus cares about — `q = 2` and `D` odd — never happens
(`residMul_odd`).  Everything downstream is the `δ = 1` argument verbatim.

## Contents

* `BB13.residMul` — the residue `kₙ = D·pⁿ − mₙ·qⁿ` at multiplier `D`, with
  `distToNearestIntMul_eq_residMul` and `isFailureMul_iff_residMul` identifying `‖D(p/q)ⁿ‖` and the
  exact-integer failure test `|kₙ| < (cq)ⁿ`.
* `BB13.AdmissibleMul` — the one hypothesis the multiplier layer needs: no residue vanishes past
  `n = 0`.  Two sufficient conditions: `admissibleMul_of_odd` (`q = 2`, `p` and `D` odd — the
  parity clause, which holds at *every* date and *every* size of `D`) and `admissibleMul_of_lt`
  (`D < q`, the `|num δ| < qᵃ` condition `BB13/MahlerCount.lean` conjectured one would need).
* `BB13.sameLineMul_resid`, `sameLineMul_gap`, `sameLineMul_lt_div_fArch` — collinearity ⇒ scaling
  `k_b = p^{b−a}k_a` ⇒ confinement `b < a/f_∞`.  The scaling step is one cross-multiplication; no
  `BB13/Subspace.lean` or `BB13/GapPrinciple.lean` detour is needed, and `D` cancels.
* `BB13.mahler_failures_mul_finite` — **the multiplier form of Mahler's theorem**: for every
  coprime `p > q ≥ 2`, every admissible `D` and every `0 < c < 1`, the set of `n ≥ 1` with
  `‖D(p/q)ⁿ‖ < cⁿ` is finite.
* `BB13.mahler_failures_mul_card_le_of_heightBound` — the conditional count `N + H·K(ε(p,c))`,
  the multiplier analogue of the [BE08] Rem. 7.4-conditional statement of the shipped Problem
  10.13 paper.
* `TShift.isRepelledMul_of_lt_one`, `TShift.tShiftProblem_holds` — the consequence at `(p,q) =
  (3,2)`: **`TShift.TShiftProblem p A` is true for every period and every numerator**, at every
  rate `θ < 1`, hence in particular at some `θ > 2/3`.
* `TShift.t1Prime_holds` — the same collision one weakening down: the residue-class relaxation
  `TShift.T1Prime` of `TShift/ResidueClass.lean` is a theorem as well, by the class `0 mod 1`.
* `TShift.exists_tShiftProblemAt` — the repair this forces on the statement, exercised.  The family
  `TShift.RepelledAt` / `TShift.TShiftProblemAt` (the T-shift problem carried at **fixed numerals**,
  since its existential closure is a theorem) is defined in `TShift/Basic.lean`, beside the
  statement it repairs and with `0` cited axioms, so that every rate theorem can instantiate it.

## What this does and does not settle

`TShiftProblem` as `TShift/Basic.lean` states it is `∃ θ > 2/3, ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, …`.
Every such statement about a fixed rational target is a theorem, by Mahler 1957 at `D = 1` and by
[Sch75]/[PR19] at a general multiplier — and, as
`tShift_forall_ge_one` shows, so is the sharper reading with no burn-in at all (`∀ n ≥ 1`), the
finitely many exceptions being absorbed into `c` by the free 2-adic floor
`TShift.distToNearestInt_mul_ge`.  **Effectivity is a property of the witnesses, not of the
proposition**, so no rephrasing inside `∃` states the open problem.

What is open — and what `TShiftProblemAt` names — is a rate `θ > 2/3` together with **exhibited
numerals** `c` and `n₀`.  The corpus's best effective rate is `0.57434` at every period
(`TShift/HabsiegerTransfer.lean`), i.e. `RepelledAt p A (57434/100000) c n₀` with numerals but with
`θ < 2/3`; `exists_tShiftProblemAt` gives `θ = 3/4` with *no* numeral for `n₀`, because
`Set.Finite.bddAbove` produces none.  Closing the gap between the two is the T-shift problem.

This is not new mathematics, and — since the novelty sweep of 2026-08-13 — the attribution is
known precisely.  [Mah57] itself proves only the `D = 1` case, as does [Bug12] Exercise 3.9.  The
multiplier form is in print twice, both times qualitatively: [Sch75] Thm 1 at `n = 1` gives it for
every positive *algebraic* multiplier (and carries our `AdmissibleMul` side condition as the
explicit hypothesis `0 < ‖·‖`), and [PR19] Thm 5/12 gives it again for every algebraic multiplier,
since no power of `p/q` with `q ≥ 2` is an algebraic integer.  `mahler_failures_mul_finite` is
therefore a reproof, obtained along the quantitative Ridout route so that the number of *lines*
stays effective and explicit — which is what `TShift/DyadicBlocks.lean` needs and what both printed
proofs discard — even though the number of failures per line is not ([BE08] Rem. 7.4, open).  New
here: the formalization, the parity clause that lets the `δ = 1` fibre argument run at `δ = D`, and
the retention of the cover.

## Trust ledger

`std3 + BugeaudEvertse.ridout_line_cover` — the cited axiom already audited for the Problem 10.13
paper, entering through `BB13.mahler_line_cover`.  No `sorry`, no `native_decide`, no new cited
axiom.  The purely elementary layer (everything up to and including `lineFibreMul_finite`) is
`std3` alone.

## References

* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124 (Thm 2 — the `D = 1` case).
* [Sch75] H. P. Schlickewei, *On the fractional parts of the sum of powers of rational numbers*,
  Mathematika **22** (1975), 154–155, Thm 1 (at `n = 1`: every positive algebraic multiplier).
* [PR19] P. Philippon, P. Rath, *On two problems of Hardy and Mahler*, arXiv:1904.00590 (2019),
  Thm 5 and Thm 12 (the Mahler set of algebraic pairs; `αˢ` must be a PV number).
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), Cor. 5.2 and Rem. 7.4.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts in
  Mathematics **193**, 2012 (Problem 10.13).
* `plans/plan-Tshift-S2.html` WP1 (this file), and `plans/note-Tshift-S2-blocks.html` §1.3, §4 —
  the WP0 audit that found F4 and priced this file at four lemmas.
-/

namespace BB13

open scoped Real

/-! ## 1. The residue at a natural multiplier -/

/-- The **signed residue at multiplier `D`**: `kₙ = D·pⁿ − mₙ·qⁿ`, where `mₙ = round(D(p/q)ⁿ)`.
One has `‖D(p/q)ⁿ‖ = |kₙ|/qⁿ` (`distToNearestIntMul_eq_residMul`), so `kₙ` carries the whole
failure test.  At `D = 1` this is `BB13.resid`. -/
noncomputable def residMul (D p q n : ℕ) : ℤ :=
  (D : ℤ) * (p : ℤ) ^ n - MnumMul (D : ℚ) p q n * (q : ℤ) ^ n

@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem residMul_one (p q n : ℕ) : residMul 1 p q n = resid p q n := by
  rw [residMul, resid]
  norm_num [MnumMul_one]

/-- **`‖D(p/q)ⁿ‖ = |kₙ|/qⁿ`** at a natural multiplier — the identity behind both the failure test
and the archimedean condition of the frame.  The `D = 1` case is
`BB13.distToNearestInt_eq_resid`. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem distToNearestIntMul_eq_residMul (D p q n : ℕ) (hq : 0 < q) :
    distToNearestInt ((D : ℝ) * ((p : ℝ) / q) ^ n) = |(residMul D p q n : ℝ)| / (q : ℝ) ^ n := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hround : round ((D : ℝ) * ((p : ℝ) / q) ^ n) = MnumMul (D : ℚ) p q n := by
    rw [MnumMul]; norm_num
  have hkey : (D : ℝ) * ((p : ℝ) / q) ^ n - (MnumMul (D : ℚ) p q n : ℝ)
      = (residMul D p q n : ℝ) / (q : ℝ) ^ n := by
    rw [residMul]; push_cast; rw [div_pow]; field_simp
  rw [distToNearestInt, hround, hkey, abs_div, abs_of_pos hqn]

/-- **The failure test in exact-integer form**: `‖D(p/q)ⁿ‖ < cⁿ ⟺ |kₙ| < (c·q)ⁿ`.  The `D = 1`
case is `BB13.isFailure_iff`. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem isFailureMul_iff_residMul (D p q : ℕ) (c : ℝ) (n : ℕ) (hq : 0 < q) :
    IsFailureMul (D : ℚ) p q c n ↔ (|residMul D p q n| : ℝ) < (c * q) ^ n := by
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hcast : (((D : ℕ) : ℚ) : ℝ) = (D : ℝ) := by push_cast; ring
  rw [IsFailureMul, hcast, distToNearestIntMul_eq_residMul D p q n hq, div_lt_iff₀ hqn,
    ← Int.cast_abs, mul_pow]

/-! ## 2. Non-vanishing: the one hypothesis the `δ = 1` argument was missing -/

/-- The multiplier `D` is **admissible** for the `(p, q)`-frame when no residue vanishes past
`n = 0`.  This is the *whole* of what `BB13/MahlerCount.lean` lacked at `δ ≠ 1`; everything else
in the per-line layer is `D`-free, because `D` cancels out of the scaling identity. -/
def AdmissibleMul (D p q : ℕ) : Prop := ∀ a : ℕ, 1 ≤ a → residMul D p q a ≠ 0

/-- **The residue vanishes only when `qᵃ ∣ D`.**  `D·pᵃ = m·qᵃ` makes `qᵃ` a divisor of `D·pᵃ`, and
`qᵃ` is coprime to `pᵃ`. -/
@[category research solved, AMS 11, ref "Bug12", group "tshift_s2"]
theorem residMul_ne_zero_of_not_dvd {D p q a : ℕ} (hcop : Nat.Coprime p q)
    (hdvd : ¬ (q ^ a ∣ D)) : residMul D p q a ≠ 0 := by
  intro h
  rw [residMul, sub_eq_zero] at h
  have hdvdZ : ((q : ℤ)) ^ a ∣ (D : ℤ) * (p : ℤ) ^ a := ⟨MnumMul (D : ℚ) p q a, by rw [h]; ring⟩
  have hdvdN : q ^ a ∣ D * p ^ a := by exact_mod_cast hdvdZ
  exact hdvd ((Nat.Coprime.pow a a hcop.symm).dvd_of_dvd_mul_right hdvdN)

/-- **The parity clause** — the multiplier case this corpus needs.  For `q = 2` with `p` and `D`
odd, `kₙ = D·pⁿ − mₙ·2ⁿ` is odd for every `n ≥ 1`, hence never `0`: `D·pⁿ` is odd and `mₙ·2ⁿ` is
even.  No size restriction on `D` — this is what makes the cycle denominators `D_p = 3^p − 2^p`
admissible at every period. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem residMul_odd {D p : ℕ} (hD : Odd D) (hp : Odd p) {n : ℕ} (hn : 1 ≤ n) :
    Odd (residMul D p 2 n) := by
  have hD' : Odd (D : ℤ) := (Int.odd_coe_nat D).mpr hD
  have hp' : Odd (p : ℤ) := (Int.odd_coe_nat p).mpr hp
  have h1 : Odd ((D : ℤ) * (p : ℤ) ^ n) := hD'.mul (hp'.pow)
  have h2 : Even (MnumMul (D : ℚ) p 2 n * ((2 : ℕ) : ℤ) ^ n) := by
    refine Even.mul_left ?_ _
    rw [Int.even_pow]
    exact ⟨by decide, by omega⟩
  exact h1.sub_even h2

/-- Odd multipliers are admissible at `q = 2` — for every `D`, at every date. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem admissibleMul_of_odd {D p : ℕ} (hD : Odd D) (hp : Odd p) : AdmissibleMul D p 2 := by
  intro a ha h
  have hodd := residMul_odd hD hp ha
  rw [h, Int.odd_iff] at hodd
  norm_num at hodd

/-- Small multipliers are admissible: `0 < D < q` gives `qᵃ > D` for `a ≥ 1`.  This is the
`|num δ| < qᵃ` condition `BB13/MahlerCount.lean` predicted the confinement would need; the parity
clause above shows it is not necessary. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem admissibleMul_of_lt {D p q : ℕ} (hcop : Nat.Coprime p q) (hD0 : 0 < D) (hDq : D < q) :
    AdmissibleMul D p q := by
  intro a ha
  refine residMul_ne_zero_of_not_dvd hcop (fun hdvd => ?_)
  have hle : q ^ a ≤ D := Nat.le_of_dvd hD0 hdvd
  have : q ≤ q ^ a := Nat.le_self_pow (by omega) q
  omega

/-- `1 ≤ |kₐ|` for an admissible multiplier — the integrality that drives the confinement. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem one_le_abs_residMul {D p q a : ℕ} (hadm : AdmissibleMul D p q) (ha : 1 ≤ a) :
    (1 : ℝ) ≤ |((residMul D p q a : ℤ) : ℝ)| := by
  have h1 : (1 : ℤ) ≤ |residMul D p q a| := Int.one_le_abs (hadm a ha)
  exact_mod_cast h1

/-! ## 3. Confinement on a line

The multiplier disappears here: two frame points are collinear exactly when
`m_a q^a p^b = m_b q^b p^a`, an identity in which `D` does not occur, and cross-multiplying it
against the definition of `kₙ` gives `p^a·k_b = p^a·(p^{b−a}·k_a)`. -/

/-- **Residues scale along a line**: `k_b = p^{b−a}·k_a`, the multiplier cancelling.  One
cross-multiplication — the `δ = 1` route through `BB13/Subspace.lean` and
`BB13/GapPrinciple.lean` is not needed. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem sameLineMul_resid {D p q : ℕ} (hp : 0 < p) {a b : ℕ} (hab : a ≤ b)
    (h : linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q b) :
    residMul D p q b = (p : ℤ) ^ (b - a) * residMul D p q a := by
  have hp0 : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpa : ((p : ℚ)) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpb : ((p : ℚ)) ^ b ≠ 0 := pow_ne_zero _ hp0
  rw [linePointMul, linePointMul, frameXMul, frameXMul] at h
  push_cast at h
  rw [div_eq_div_iff hpa hpb] at h
  have hsplit : (p : ℤ) ^ b = (p : ℤ) ^ a * (p : ℤ) ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  have hZ : (MnumMul (D : ℚ) p q a) * (q : ℤ) ^ a * ((p : ℤ) ^ a * (p : ℤ) ^ (b - a))
      = (MnumMul (D : ℚ) p q b) * (q : ℤ) ^ b * (p : ℤ) ^ a := by
    rw [← hsplit]; exact_mod_cast h
  have hpaZ : ((p : ℤ)) ^ a ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr (by omega))
  have key : (p : ℤ) ^ a * residMul D p q b
      = (p : ℤ) ^ a * ((p : ℤ) ^ (b - a) * residMul D p q a) := by
    simp only [residMul]
    rw [hsplit]
    linear_combination hZ
  exact mul_left_cancel₀ hpaZ key

/-- **The gap principle on a line, at a multiplier**: if `a < b` lie on one line and `b` is a
failure, then `p^{b−a} < (cq)ᵇ`.  The residue `kₐ` is amplified by `p^{b−a}` along the line and
must still fit under the failure bound at `b`, while `|kₐ| ≥ 1` by admissibility. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem sameLineMul_gap {D p q a b : ℕ} {c : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hadm : AdmissibleMul D p q) (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailureMul (D : ℚ) p q c b) (h : linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q b) :
    (p : ℝ) ^ (b - a) < (c * q) ^ b := by
  have hres := sameLineMul_resid hp hab.le h
  have habs : |((residMul D p q b : ℤ) : ℝ)| = (p : ℝ) ^ (b - a) * |((residMul D p q a : ℤ) : ℝ)| := by
    rw [hres]; push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  have h1 : (1 : ℝ) ≤ |((residMul D p q a : ℤ) : ℝ)| := one_le_abs_residMul hadm ha
  have h2 : (|residMul D p q b| : ℝ) < (c * (q : ℝ)) ^ b :=
    (isFailureMul_iff_residMul D p q c b hq).mp hfb
  have hppos : (0 : ℝ) < (p : ℝ) ^ (b - a) :=
    pow_pos (by exact_mod_cast hp : (0 : ℝ) < (p : ℝ)) (b - a)
  have h3 : (p : ℝ) ^ (b - a) ≤ |((residMul D p q b : ℤ) : ℝ)| := by
    rw [habs]; nlinarith
  linarith

/-- **Confinement, in closed form**: a companion `b > a` of `a` on the same line satisfies
`b < a/f_∞`, with `f_∞ = log(p/(cq))/log p` the archimedean exponent of the frame (`BB13.fArch`).
So a line-fibre with least element `a` lives in `[a, a/f_∞)`.  The `D = 1` case is
`BB13.sameLine_lt_div_fArch`. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem sameLineMul_lt_div_fArch {D p q a b : ℕ} {c : ℝ} (hp : 1 < p) (hq : 1 < q) (hqp : q < p)
    (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailureMul (D : ℚ) p q c b)
    (h : linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q b) :
    (b : ℝ) < (a : ℝ) / fArch p q c := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqp' : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
  have hcq : c * (q : ℝ) < (p : ℝ) := by nlinarith
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hF : 0 < fArch p q c := fArch_pos hp (by omega) hc0 hcq
  have hgap := sameLineMul_gap (Nat.zero_lt_of_lt hp) (by omega) hadm ha hab hfb h
  have hlog := Real.log_lt_log (by positivity) hgap
  rw [Real.log_pow, Real.log_pow, Nat.cast_sub hab.le] at hlog
  have hFL := fArch_mul_log hp (by omega : 0 < q) hc0
  have hstep : ((b : ℝ) * fArch p q c) * Real.log p < (a : ℝ) * Real.log p := by
    calc ((b : ℝ) * fArch p q c) * Real.log p
        = (b : ℝ) * (fArch p q c * Real.log p) := by ring
      _ = (b : ℝ) * (Real.log p - Real.log (c * q)) := by rw [hFL]
      _ = (b : ℝ) * Real.log p - (b : ℝ) * Real.log (c * q) := by ring
      _ < (a : ℝ) * Real.log p := by nlinarith [hlog]
  rw [lt_div_iff₀ hF]
  exact lt_of_mul_lt_mul_right hstep hlp.le

/-! ## 4. Every line carries finitely many failures -/

/-- The failures of `‖D(p/q)ⁿ‖ < cⁿ` on the line of slope `r`. -/
def lineFibreMul (D p q : ℕ) (c : ℝ) (r : ℚ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ linePointMul (D : ℚ) p q n = r}

/-- **A single line carries only finitely many failures**, at every admissible multiplier —
elementarily, with no Diophantine input: any member `a` confines the whole fibre below
`a + ⌈a/f_∞⌉`.  Footprint `std3`. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "tshift_s2"]
theorem lineFibreMul_finite {D p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 1 < q) (hqp : q < p)
    (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) (r : ℚ) :
    (lineFibreMul D p q c r).Finite := by
  rcases Set.eq_empty_or_nonempty (lineFibreMul D p q c r) with he | ⟨a, ha⟩
  · rw [he]; exact Set.finite_empty
  · refine Set.Finite.subset (Set.finite_Iic (a + ⌈(a : ℝ) / fArch p q c⌉₊)) ?_
    intro b hb
    rcases le_or_gt b a with hle | hlt
    · exact le_trans hle (by omega)
    · have hlt' := sameLineMul_lt_div_fArch hp hq hqp hadm hc0 hc1 ha.1 hlt hb.2.1
        (ha.2.2.trans hb.2.2.symm)
      have hb2 : b < ⌈(a : ℝ) / fArch p q c⌉₊ := Nat.lt_ceil.mpr hlt'
      exact Set.mem_Iic.mpr (by omega)

/-! ## 5. Finiteness (Theorem C) and the conditional count -/

/-- The failure set of `‖D(p/q)ⁿ‖ < cⁿ`. -/
def failuresMul (D p q : ℕ) (c : ℝ) : Set ℕ := {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n}

/-- The failures beyond an index `N`. -/
def failuresMulFrom (D p q : ℕ) (c : ℝ) (N : ℕ) : Set ℕ :=
  {n : ℕ | N ≤ n ∧ IsFailureMul (D : ℚ) p q c n}

/-- The failures beyond `N` on the line of slope `r` — the fibres whose size is the open per-line
problem ([BE08] Rem. 7.4). -/
def highFibreMul (D p q : ℕ) (c : ℝ) (N : ℕ) (r : ℚ) : Set ℕ :=
  {n : ℕ | N ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ linePointMul (D : ℚ) p q n = r}

/-- The height of a natural multiplier is the multiplier itself (for `D ≥ 1`). -/
@[category API, AMS 11, ref "BE08", group "tshift_s2"]
theorem ratHeight_natCast (D : ℕ) : BugeaudEvertse.ratHeight (D : ℚ) = max D 1 := by
  rw [BugeaudEvertse.ratHeight, Rat.num_natCast, Rat.den_natCast]
  simp

/-- **The height threshold of (5.12) is reached at every multiplier**: for every base `p ≥ 2`,
rate `c < 1` and multiplier `δ` there is an `N ≥ 1` beyond which both `cⁿ < 1/16` and
`pⁿ > 2·H(δ)` hold, so that `mahler_line_cover` applies.  (Both are explicit in `c`, `p`, `δ`;
existence is all the counts need.) -/
@[category API, AMS 11, ref "BE08" "Bug12", group "tshift_s2"]
theorem exists_thresholdMul {p : ℕ} {c : ℝ} (δ : ℚ) (hp : 1 < p) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight δ : ℝ) < (p : ℝ) ^ n := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 16) hc1
  refine ⟨max (N₁ + 1) (2 * BugeaudEvertse.ratHeight δ + 1),
    le_max_of_le_left (Nat.le_add_left 1 N₁), fun n hn => ⟨?_, ?_⟩⟩
  · have hn1 : N₁ ≤ n := le_trans (le_trans (Nat.le_succ N₁) (le_max_left _ _)) hn
    exact lt_of_le_of_lt (pow_le_pow_of_le_one hc0.le hc1.le hn1) hN₁
  · have hn2 : 2 * BugeaudEvertse.ratHeight δ + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have hnat : 2 * BugeaudEvertse.ratHeight δ < 2 ^ n := by omega
    have hcast : (2 * BugeaudEvertse.ratHeight δ : ℕ) < ((2 : ℕ) : ℝ) ^ n := by exact_mod_cast hnat
    have h2p : ((2 : ℕ) : ℝ) ^ n ≤ (p : ℝ) ^ n :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) n
    push_cast at hcast h2p ⊢
    linarith

/-- **The failures beyond the threshold form a finite set** — covered by finitely many lines
(`mahler_line_cover`, already general in the multiplier), each carrying finitely many failures
(`lineFibreMul_finite`). -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem failuresMulFrom_finite {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) {N : ℕ}
    (hthr : ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight (D : ℚ) : ℝ) < (p : ℝ) ^ n)
    (hN : 1 ≤ N) : (failuresMulFrom D p q c N).Finite := by
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨R, -, hR⟩ := mahler_line_cover (D : ℚ) p q c (by omega) hqp hcop hc0 hc1
  refine Set.Finite.subset
    (R.finite_toSet.biUnion (fun r _ => lineFibreMul_finite hp hq hqp hadm hc0 hc1 r)) ?_
  rintro n ⟨hn, hf⟩
  exact Set.mem_biUnion (hR n (hthr n hn).1 (hthr n hn).2 hf) ⟨by omega, hf, rfl⟩

/-- **Mahler's theorem at an integer multiplier, along the quantitative route.**  For every
coprime pair `p > q ≥ 2`, every admissible multiplier `D` and every rate `0 < c < 1`, the set of
`n ≥ 1` with `‖D(p/q)ⁿ‖ < cⁿ` is **finite**.

This is the statement `BB13/MahlerCount.lean` could only make at `D = 1`.  The proof uses no
qualitative Subspace input: the failures split into an initial segment below the explicit height
threshold and a union of at most `K(ε(p,c))` line-fibres, each finite by the elementary gap
principle.  Footprint `std3 + BugeaudEvertse.ridout_line_cover`.

The threshold beyond which the finite set is exhausted is **not** effective: `Set.Finite` records
that finitely many failures exist, and the per-line height that would locate them is the open
problem of [BE08] Rem. 7.4.  See `mahler_failures_mul_card_le_of_heightBound` for what a height
bound would buy.

**Prior art** (novelty sweep, 2026-08-13): the statement itself is in print — [Sch75] Thm 1 at
`n = 1` (every positive algebraic multiplier, 1975) and [PR19] Thm 5/12 (2019).  Both are
qualitative and neither keeps a cover, so neither yields `TShift/DyadicBlocks.lean`'s block count;
that is why the quantitative route is taken here. -/
@[category research solved, AMS 11, ref "Mah57" "Sch75" "PR19" "BE08" "Bug12", group "tshift_s2"]
theorem mahler_failures_mul_finite {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) :
    (failuresMul D p q c).Finite := by
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨N, hN1, hthr⟩ := exists_thresholdMul (D : ℚ) hp hc0 hc1
  refine Set.Finite.subset ((Set.finite_Iio N).union
    (failuresMulFrom_finite hq hqp hcop hadm hc0 hc1 hthr hN1)) ?_
  rintro n ⟨h1, hf⟩
  rcases lt_or_ge n N with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨hge, hf⟩

/-- **`#E(D, p, q, c) ≤ N + H·K(ε(p,c))`.**  If no line carries more than `H` failures beyond the
height threshold `N`, then the total number of `n ≥ 1` with `‖D(p/q)ⁿ‖ < cⁿ` is at most
`N + H·K(ε(p,c))`.

The multiplier form of `BB13.mahler_failures_card_le_of_heightBound`.  As there, the hypothesis
`H` is the open per-line problem ([BE08] Rem. 7.4) — the confinement of
`sameLineMul_lt_div_fArch` bounds each fibre in terms of *its own* least element, not uniformly —
so this is a conditional statement, exactly as in the shipped Problem 10.13 paper.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem mahler_failures_mul_card_le_of_heightBound {D p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) (N H : ℕ)
    (hN : 1 ≤ N)
    (hthr : ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight (D : ℚ) : ℝ) < (p : ℝ) ^ n)
    (hfib : ∀ r : ℚ, (highFibreMul D p q c N r).ncard ≤ H) :
    (failuresMul D p q c).ncard ≤ N + H * BugeaudEvertse.lineBound (epsilon p c) := by
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover (D : ℚ) p q c (by omega) hqp hcop hc0 hc1
  have hfin := failuresMulFrom_finite hq hqp hcop hadm hc0 hc1 hthr hN
  have hfib' : ∀ r : ℚ,
      {n ∈ failuresMulFrom D p q c N | linePointMul (D : ℚ) p q n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ failuresMulFrom D p q c N | linePointMul (D : ℚ) p q n = r}
        = highFibreMul D p q c N r := by
      ext n
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    rw [heq]; exact hfib r
  have himg : linePointMul (D : ℚ) p q '' failuresMulFrom D p q c N ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hf⟩, rfl⟩
    exact hR n (hthr n hn).1 (hthr n hn).2 hf
  have hhigh : (failuresMulFrom D p q c N).ncard ≤ H * BugeaudEvertse.lineBound (epsilon p c) := by
    calc (failuresMulFrom D p q c N).ncard
        ≤ H * (linePointMul (D : ℚ) p q '' failuresMulFrom D p q c N).ncard :=
          Set.ncard_le_mul_ncard_image hfin _ H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound (epsilon p c) := Nat.mul_le_mul (le_refl H) hcard
  have hsub : failuresMul D p q c ⊆ ↑(Finset.range N) ∪ failuresMulFrom D p q c N := by
    rintro n ⟨h1, hf⟩
    rcases lt_or_ge n N with hlt | hge
    · exact Or.inl (by simpa using hlt)
    · exact Or.inr ⟨hge, hf⟩
  calc (failuresMul D p q c).ncard
      ≤ (↑(Finset.range N) ∪ failuresMulFrom D p q c N).ncard :=
        Set.ncard_le_ncard hsub ((Finset.range N).finite_toSet.union hfin)
    _ ≤ (↑(Finset.range N) : Set ℕ).ncard + (failuresMulFrom D p q c N).ncard :=
        Set.ncard_union_le _ _
    _ = N + (failuresMulFrom D p q c N).ncard := by rw [Set.ncard_coe_finset, Finset.card_range]
    _ ≤ N + H * BugeaudEvertse.lineBound (epsilon p c) := by omega

/-! ## 6. Numeric cross-check at `(p, q, c) = (3, 2, 3/4)`

The decidable exact-integer mirror, the general-multiplier form of `BB13.residNat` / `BB13.failNat`.
It certifies in the kernel the failure lists that `TShift/tshift_numerics.py`'s `s2` block reports,
so a drift between the corpus's frame and the harness's fails a build rather than a reading. -/

/-- `|kₙ| = min(D·3ⁿ mod 2ⁿ, 2ⁿ − D·3ⁿ mod 2ⁿ)`, computed on naturals.  At `D = 1` this is
`BB13.residNat`. -/
def residNatMul (D n : ℕ) : ℕ := min (D * 3 ^ n % 2 ^ n) (2 ^ n - D * 3 ^ n % 2 ^ n)

/-- The decidable mirror is `|kₙ|`. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem abs_residMul_eq_residNatMul (D n : ℕ) :
    |residMul D 3 2 n| = (residNatMul D n : ℤ) := by
  have hd : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hden : (((2 : ℕ) : ℝ)) ^ n ≠ 0 := by positivity
  have hrw : (D : ℝ) * (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ n
      = ((D * 3 ^ n : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
    push_cast; rw [div_pow]; ring
  have hpow : ((2 ^ n : ℕ) : ℝ) = ((2 : ℕ) : ℝ) ^ n := by push_cast; ring
  have h1 := distToNearestIntMul_eq_residMul D 3 2 n (by norm_num)
  rw [hrw, distToNearestInt_natCast_div _ _ hd, hpow] at h1
  have h2 : ((residNatMul D n : ℕ) : ℝ) = |((residMul D 3 2 n : ℤ) : ℝ)| := by
    rw [residNatMul]
    field_simp at h1
    exact h1
  have h3 : ((|residMul D 3 2 n| : ℤ) : ℝ) = ((residNatMul D n : ℕ) : ℝ) := by
    rw [Int.cast_abs, h2]
  exact_mod_cast h3

/-- The decidable failure test at rate `3/4`: `|kₙ| < (3/2)ⁿ`, i.e. `2ⁿ·|kₙ| < 3ⁿ`. -/
def failNatMul (D n : ℕ) : Bool := decide (2 ^ n * residNatMul D n < 3 ^ n)

/-- The mirror is faithful: `failNatMul` decides `IsFailureMul (D) 3 2 (3/4)`. -/
@[category API, AMS 11, ref "Bug12", group "tshift_s2"]
theorem failNatMul_iff (D n : ℕ) :
    IsFailureMul (D : ℚ) 3 2 (3 / 4) n ↔ failNatMul D n = true := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [isFailureMul_iff_residMul D 3 2 (3 / 4) n (by norm_num), ← Int.cast_abs,
    abs_residMul_eq_residNatMul, failNatMul, decide_eq_true_eq]
  have key : (((residNatMul D n : ℕ) : ℤ) : ℝ) < ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ n
      ↔ ((2 ^ n * residNatMul D n : ℕ) : ℝ) < ((3 ^ n : ℕ) : ℝ) := by
    push_cast
    rw [show ((3 : ℝ) / 4 * 2) = 3 / 2 by norm_num, div_pow, lt_div_iff₀ h2]
    constructor <;> intro h <;> linarith
  rw [key]
  exact Nat.cast_lt

/-- **The failure lists of `‖D(3/2)ⁿ‖ < (3/4)ⁿ` on `n ≤ 19`**, kernel-certified at the four cycle
denominators `D_p = 1, 5, 19, 65` (`p = 1, 2, 3, 4`) — the genuine failures plus the degenerate
`n = 0`.  These are the initial segments of the `n ≤ 2000` scan reported by the `s2` block of
`TShift/tshift_numerics.py`, and the `D = 1` row is `BB13.failNat_initial_segment`, i.e. the
failure set `{1, 2, 3, 4, 7}` of Bugeaud's Problem 10.13.

Read against `mahler_failures_mul_finite`: the theorem bounds a set that is this small, and every
failure listed lies below the height threshold — the certificate and the phenomenon are `10¹²`
apart, which is the standard shape of a quantitative Ridout statement. -/
@[category test, AMS 11, ref "Bug12", group "tshift_s2"]
theorem failNatMul_initial_segments :
    (List.range 20).filter (failNatMul 1) = [0, 1, 2, 3, 4, 7] ∧
    (List.range 20).filter (failNatMul 5) = [0, 1, 2, 3, 4, 5, 6] ∧
    (List.range 20).filter (failNatMul 19) = [0, 1, 2, 3, 4, 8] ∧
    (List.range 20).filter (failNatMul 65) = [0, 1, 2, 3, 4] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end BB13

/-! # The consequence for the T-shift problem

At `(p, q) = (3, 2)` the cycle denominators `D_p = 3^p − 2^p` are odd, hence admissible at every
period, and the finiteness above says: past an (ineffective) threshold, `‖D_p(3/2)ⁿ‖ ≥ θⁿ` for
**every** `θ < 1`.  That is `TShift.IsRepelledMul`, and through `TShift/Basic.lean`'s reduction it
settles `TShift.TShiftProblem` at every period and every numerator. -/

namespace TShift

open scoped Real

/-! ## 6. Theorem C at base `3/2` -/

/-- The odd multipliers are admissible for the `(3, 2)` frame. -/
@[category API, AMS 11 37, ref "Mah57" "A6plus", group "tshift_s2"]
theorem admissibleMul_three_two {D : ℕ} (hD : Odd D) : BB13.AdmissibleMul D 3 2 :=
  BB13.admissibleMul_of_odd hD (by decide)

/-- **Theorem C at base `3/2`**: for every odd multiplier `D` and every rate `θ < 1`, only
finitely many `n` satisfy `‖D(3/2)ⁿ‖ < θⁿ`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem failuresMul_three_two_finite {D : ℕ} (hD : Odd D) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    (BB13.failuresMul D 3 2 θ).Finite :=
  BB13.mahler_failures_mul_finite (by norm_num) (by norm_num) (by decide)
    (admissibleMul_three_two hD) h0 h1

/-- **Every rate below `1` repels, at every odd multiplier**, past the last failure — with
constant `1`, since a non-failure *is* the bound.

The threshold is **not** effective: it comes from `Set.Finite.bddAbove`, which exhibits no
numeral.  That is the whole distance between this theorem and the T-shift problem. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem exists_pow_le_distToNearestIntMul {D : ℕ} (hD : Odd D) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  obtain ⟨M, hM⟩ := (failuresMul_three_two_finite hD h0 h1).bddAbove
  refine ⟨M + 1, fun n hn => ?_⟩
  have hnot : ¬ BB13.IsFailureMul (D : ℚ) 3 2 θ n := by
    intro hf
    have hmem : n ∈ BB13.failuresMul D 3 2 θ := ⟨by omega, hf⟩
    have := hM hmem
    omega
  simp only [BB13.IsFailureMul, not_lt] at hnot
  simpa using hnot

/-- The `IsRepelledMul` packaging of the previous theorem. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem isRepelledMul_of_lt_one {D : ℕ} (hD : Odd D) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    IsRepelledMul θ D := by
  obtain ⟨n₀, hn₀⟩ := exists_pow_le_distToNearestIntMul hD h0 h1
  exact ⟨1, one_pos, n₀, fun n hn => by simpa using hn₀ n hn⟩

/-- **The T-shift problem, as `TShift/Basic.lean` states it, is a theorem** — at every period `p`
and every numerator `A`.

Take `θ = 3/4 > 2/3`: the multiplier failure set of `D_p` at that rate is finite
(`failuresMul_three_two_finite`), so `‖D_p(3/2)ⁿ‖ ≥ (3/4)ⁿ` past the last exception, and the
reduction `TShift.tShiftProblem_of_isRepelledMul` transports this to every target `A/D_p` at once.

The mathematics is Mahler's (1957); nothing here is new but the formalization.  What the statement
`TShiftProblem` fails to capture — and `TShiftProblemAt` below repairs — is that the witnesses are
ineffective: no numeral `n₀` is produced, at `θ = 3/4` or at any `θ > 2/3`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12" "A6plus", group "tshift_s2"]
theorem tShiftProblem_holds {p : ℕ} (hp : 1 ≤ p) (A : ℤ) : TShiftProblem p A :=
  tShiftProblem_of_isRepelledMul hp A
    ⟨3 / 4, by norm_num,
      isRepelledMul_of_lt_one (Z32.cycleDenom_odd hp) (by norm_num) (by norm_num)⟩

/-- **T1′ is a theorem too** — the same collision, one weakening down.  `TShift.T1Prime p` asks for
a *class-restricted* bound at some rate above `2/3`; the class `0 mod 1` and the rate `3/4` supply
it, through `TShift.t1Prime_of_isRepelledMul`.  So the residue-class relaxation needs the same
repair as the problem it relaxes: what is open there is the version with numerals. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "TshiftS5", group "tshift_s2"]
theorem t1Prime_holds {p : ℕ} (hp : 1 ≤ p) : T1Prime p :=
  t1Prime_of_isRepelledMul
    ⟨3 / 4, by norm_num,
      isRepelledMul_of_lt_one (Z32.cycleDenom_odd hp) (by norm_num) (by norm_num)⟩

/-! ## 7. No existential phrasing escapes

The obvious repair — demand the bound at *every* date, with no burn-in — is also a theorem: the
finitely many exceptions are absorbed into the constant `c`, using the free 2-adic floor
`‖D(3/2)ⁿ‖ ≥ 2⁻ⁿ` (`TShift.distToNearestInt_mul_ge`) rather than any property of the exceptional
set.  With `c = (2/3)^{n₀}`,

  `c·(3/4)ⁿ ≤ (2/3)ⁿ(3/4)ⁿ = 2⁻ⁿ ≤ ‖D(3/2)ⁿ‖`  for `1 ≤ n ≤ n₀`,

while `c ≤ 1` handles `n ≥ n₀`. -/

/-- **The multiplier bound at `θ = 3/4` from the first date on**, no burn-in. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem exists_const_forall_ge_one {D : ℕ} (hD : Odd D) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      c * (3 / 4 : ℝ) ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_pow_le_distToNearestIntMul hD (by norm_num : (0:ℝ) < 3/4) (by norm_num)
  refine ⟨(2 / 3 : ℝ) ^ n₀, by positivity, fun n hn => ?_⟩
  have h34 : (0 : ℝ) < (3 / 4 : ℝ) ^ n := by positivity
  rcases le_or_gt n₀ n with hge | hlt
  · have hc1 : (2 / 3 : ℝ) ^ n₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (2 / 3 : ℝ) ^ n₀ * (3 / 4 : ℝ) ^ n ≤ 1 * (3 / 4 : ℝ) ^ n := by nlinarith
      _ = (3 / 4 : ℝ) ^ n := one_mul _
      _ ≤ _ := hn₀ n hge
  · have hfree : 1 / (2 : ℝ) ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) :=
      distToNearestInt_mul_ge hn hD
    have hmono : (2 / 3 : ℝ) ^ n₀ ≤ (2 / 3 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hprod : (2 / 3 : ℝ) ^ n * (3 / 4 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
      rw [← mul_pow]; norm_num [div_pow, one_div]
    calc (2 / 3 : ℝ) ^ n₀ * (3 / 4 : ℝ) ^ n ≤ (2 / 3 : ℝ) ^ n * (3 / 4 : ℝ) ^ n := by nlinarith
      _ = 1 / (2 : ℝ) ^ n := hprod
      _ ≤ _ := hfree

/-- **Even the `∀ n ≥ 1` phrasing is a theorem.**  There is no burn-in to hide behind: for every
period and every numerator there are a rate `θ > 2/3` and a constant `c > 0` with
`c·θⁿ ≤ ‖(3/2)ⁿ − A/D_p‖` at *every* date `n ≥ 1`.

Consequently no statement of the form `∃ θ > 2/3, ∃ c > 0, ∀ n ≥ …` about a fixed rational target
expresses the T-shift problem: **effectivity is a property of the witnesses, not of the
proposition.**  See `TShiftProblemAt`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem tShift_forall_ge_one {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    ∃ θ > (2 : ℝ) / 3, ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      c * θ ^ n ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / Z32.cycleDenom p) := by
  obtain ⟨c, hc, hall⟩ := exists_const_forall_ge_one (Z32.cycleDenom_odd hp)
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hD
  refine ⟨3 / 4, by norm_num, c / ((Z32.cycleDenom p : ℕ) : ℝ), by positivity, fun n hn => ?_⟩
  have h1 := hall n hn
  have h2 := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  rw [div_mul_eq_mul_div, div_le_iff₀ hDR]
  calc c * (3 / 4 : ℝ) ^ n
      ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ n) := h1
    _ ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := h2
    _ = distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ))
        * ((Z32.cycleDenom p : ℕ) : ℝ) := by ring

/-! ## 8. The repair: the problem as a family at fixed numerals

`TShiftProblem` and every existential variant of it is a theorem (§6, §7).  The open problem is
about *witnesses*, so the numerals have to be parameters — `TShift.RepelledAt` and
`TShift.TShiftProblemAt`, defined in `TShift/Basic.lean` beside the statement they repair (they
need nothing from this file, and putting them there keeps them reachable from the rate theorems,
whose footprints differ).  What belongs here is the only member of the family this file can
supply. -/

/-- **The rate clears `2/3`, but the threshold is not a numeral.**  For every period and numerator
there is an `n₀` with `TShiftProblemAt p A (3/4) (1/D_p) n₀` — this is `tShiftProblem_holds` with
the constants named.  `Set.Finite.bddAbove` supplies `n₀`, and supplies no value for it; producing
one is the open problem. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem exists_tShiftProblemAt {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    ∃ n₀ : ℕ, TShiftProblemAt p A (3 / 4) (1 / (Z32.cycleDenom p : ℚ)) n₀ := by
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hD
  obtain ⟨n₀, hn₀⟩ := exists_pow_le_distToNearestIntMul (Z32.cycleDenom_odd hp)
    (by norm_num : (0:ℝ) < 3/4) (by norm_num)
  refine ⟨n₀, by norm_num, fun n hn => ?_⟩
  have h1 := hn₀ n hn
  have h2 := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  have hcast : ((1 / (Z32.cycleDenom p : ℚ) : ℚ) : ℝ) * ((3 / 4 : ℚ) : ℝ) ^ n
      = (3 / 4 : ℝ) ^ n / ((Z32.cycleDenom p : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, div_le_iff₀ hDR]
  calc (3 / 4 : ℝ) ^ n
      ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ n) := h1
    _ ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := h2
    _ = distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ))
        * ((Z32.cycleDenom p : ℕ) : ℝ) := by ring

end TShift
