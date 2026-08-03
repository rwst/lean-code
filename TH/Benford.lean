/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import BertinPisot.ModOneEquivalence
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The two-scale factorization of `(3/2)ⁿ`, and the Benford harvest (plan-A1+, A17)

Write `(3/2)ⁿ = 2^{nθ}` with `θ = log₂(3/2) = log₂3 − 1`.  This trivial identity separates the
sequence into **two scales that are in completely different states of knowledge**, and this file
makes that separation a theorem rather than a paragraph.

* The **top scale** is the rotation `(nθ mod 1)`.  It is *solved*: `θ` is irrational (because
  `3^q = 2^p` has no solution), so `(nθ)` is uniformly distributed modulo one, and every
  leading-digit statistic of `(3/2)ⁿ` — in any base — follows.  That is the Benford harvest below,
  and it is the corpus's first *solved* distributional theorem about the actual sequence `(3/2)ⁿ`.
* The **bottom scale** is `Int.fract ((3/2)ⁿ)`, the object of the M5–M7 ladder, and it is open.
  `fract_threeHalves_pow_eq` exhibits it as a **depth-`⌊nθ⌋` digit functional** of the very same
  rotation coordinate: `(3/2)ⁿ = 2^{⌊nθ⌋} · mantissa`, so reading the bottom scale means reading
  the binary expansion of `2^{fract(nθ)}` at depth `≈ 0.585·n`, which is precisely where the carry
  channel lives.

The point of stating both is to prevent a category error that costs real time: *a distributional
theorem about `(3/2)ⁿ` is not automatically a rung of the ladder.*  Everything proved here lives on
the solved scale and is recorded as **off-ladder**.  GR4 (no carry-blind argument can work) is
respected in the sharpest possible way — the scale this file solves is exactly the carry-free one,
and `depth_le`/`lt_depth_add_one` locate the wall.

## Main results

* `irrational_logb_of_two_dvd_base` — the workhorse: if `b` is even and `m` is odd, then
  `log_b (m / 2ᵗ)` is irrational.  Instances: `Real.logb 10 3`, `Real.logb 10 (3/2)`,
  `Real.logb 2 3`, and `theta` itself.
* `tendsto_mantissa_density` / `tendsto_leadingDigit_density` — for any base `b ≥ 2` and any real
  `a` with `log_b a` irrational, the mantissa of `aⁿ` equidistributes logarithmically and the
  leading digit `k` has density `log_b (k+1) − log_b k`.
* `benford_threeHalves_pow`, `benford_three_pow` — the decimal instances for `(3/2)ⁿ` and `3ⁿ`;
  `benford_threeHalves_pow_inv_form` gives the familiar `log₁₀(1 + 1/k)`.
* `mantissa_block_threeHalves_pow_base_two` — the binary leading-block instance.
* `threeHalves_pow_factorization`, `mantissa_two_threeHalves_pow`, `fract_threeHalves_pow_eq` —
  the two-scale factorization: solved coordinate times a depth-`⌊nθ⌋` shift.
* `isEquidistributedModuloOne_theta` — the top scale, solved.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`.  The u.d. input is `Bertin.uniformlyDistributedModOne_nα_iff_irrational` chained
through `Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne`; both are axiom-free
since hygiene items H1 and H2 of `plans/plan-A1+.html` §6.3 landed, which is why this angle was
scheduled after them.

## Claim level

Formalization only, and deliberately so.  Benford's law for a geometric sequence with irrational
`log_b a` is classical (Weyl 1916; [KN74] Ch. 1, Ex. 2.4); nothing here is new mathematics.  What is
new is that the corpus can now *state* which scale of `(3/2)ⁿ` is solved and which is open, in one
compiled place, with the boundary between them located.

## References

* `plans/plan-A1+.html` §5, angle A17 (two-scale factorization and the effective Benford harvest);
  §6.3 H1/H2 (the axiom-freeness this file consumes); Table F′ (A17 is graded *off-ladder*).
* [KN74] Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences.* Wiley, 1974, Ch. 1.
* [Ber92] Bertin, M.-J. et al. *Pisot and Salem Numbers.* Birkhäuser, 1992, Theorem 4.3.2 and its
  corollary on `(nα)` — the engine consumed here.
-/

namespace TH

open Filter
open scoped Topology

/-! ## 1. Irrationality of the relevant logarithms

Everything downstream needs exactly one arithmetic fact: `2` and `3` are multiplicatively
independent.  Rather than proving that four times, we isolate the reduction "rational logarithm ⇒
multiplicative dependence" and then apply a single parity argument.
-/

/-- **Reduction step.**  If `log_b a` is *rational* then `a` and `b` are multiplicatively
dependent: `a ^ q = b ^ p` for some `q > 0` and some integer `p`.

This is the only place where the logarithm is unwound; every irrationality statement below is a
purely arithmetic consequence. -/
private theorem exists_pow_eq_of_not_irrational_logb {b : ℕ} {a : ℝ} (hb : 2 ≤ b) (ha : 0 < a)
    (h : ¬ Irrational (Real.logb b a)) :
    ∃ (q : ℕ) (p : ℤ), 0 < q ∧ a ^ q = (b : ℝ) ^ p := by
  obtain ⟨r, hr⟩ := not_not.mp h
  refine ⟨r.den, r.num, r.pos, ?_⟩
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hlogb : Real.log (b : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hbpos (by linarith)
  -- `r.num = r * r.den`, transported to `ℝ`
  have hq0 : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) := (div_eq_iff hq0).mp (Rat.num_div_den r)
  have hnumR : (r.num : ℝ) = (r : ℝ) * (r.den : ℝ) := by exact_mod_cast hnum
  -- `den · log a = num · log b`
  have hlog : (r.den : ℝ) * Real.log a = (r.num : ℝ) * Real.log (b : ℝ) := by
    rw [hnumR, hr, ← Real.log_div_log]
    field_simp
  have hpow : Real.log (a ^ r.den) = Real.log ((b : ℝ) ^ r.num) := by
    rw [Real.log_pow, Real.log_zpow]
    exact_mod_cast hlog
  have hexp := congrArg Real.exp hpow
  rwa [Real.exp_log (pow_pos ha _), Real.exp_log (zpow_pos hbpos _)] at hexp

/-- **The workhorse.**  If the base `b` is even and `m` is odd, then `log_b (m / 2ᵗ)` is
irrational (whenever `m / 2ᵗ > 1`, which is all we ever need).

Reason: rationality would give `m^q = b^{p} · 2^{tq}` with `q, p ≥ 1`, and the right-hand side is
even while `m^q` is odd.  All four logarithms this file needs are instances. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem irrational_logb_of_two_dvd_base {b m t : ℕ} (hb : 2 ≤ b) (hbe : 2 ∣ b)
    (hm : ¬ 2 ∣ m) (h1 : 1 < (m : ℝ) / 2 ^ t) :
    Irrational (Real.logb b ((m : ℝ) / 2 ^ t)) := by
  by_contra hcon
  have ha : (0 : ℝ) < (m : ℝ) / 2 ^ t := lt_trans zero_lt_one h1
  obtain ⟨q, p, hq, heq⟩ := exists_pow_eq_of_not_irrational_logb hb ha hcon
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  have hgt : (1 : ℝ) < ((m : ℝ) / 2 ^ t) ^ q := one_lt_pow₀ h1 hq.ne'
  rw [heq] at hgt
  -- the exponent must be positive
  have hp : 0 < p := by
    by_contra hp
    push Not at hp
    have h0 : (b : ℝ) ^ p ≤ (b : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ hb1.le hp
    rw [zpow_zero] at h0
    linarith
  obtain ⟨p', rfl⟩ : ∃ p' : ℕ, p = (p' : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp.le).symm⟩
  have hp' : 0 < p' := by exact_mod_cast hp
  rw [zpow_natCast, div_pow, ← pow_mul, div_eq_iff (by positivity)] at heq
  have hnat : m ^ q = b ^ p' * 2 ^ (t * q) := by exact_mod_cast heq
  have h2 : 2 ∣ m ^ q := by
    rw [hnat]
    exact Dvd.dvd.mul_right (dvd_pow hbe hp'.ne') _
  exact hm (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)

/-- `log₁₀ 3` is irrational. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem irrational_logb_ten_three : Irrational (Real.logb 10 3) := by
  simpa using irrational_logb_of_two_dvd_base (b := 10) (m := 3) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `log₁₀(3/2)` is irrational. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem irrational_logb_ten_threeHalves : Irrational (Real.logb 10 (3 / 2)) := by
  simpa using irrational_logb_of_two_dvd_base (b := 10) (m := 3) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `log₂ 3` is irrational — the classical `2^p ≠ 3^q`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem irrational_logb_two_three : Irrational (Real.logb 2 3) := by
  simpa using irrational_logb_of_two_dvd_base (b := 2) (m := 3) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## 2. Mantissa and leading digit -/

/-- The **mantissa** (significand) of `x` in base `b`: the element of `[1, b)` obtained by scaling
`x` by a power of `b`.  Defined through the logarithm, which is what makes the distributional
statements below immediate. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
noncomputable def mantissa (b : ℕ) (x : ℝ) : ℝ := (b : ℝ) ^ Int.fract (Real.logb b x)

/-- The **leading digit** of `x` in base `b`. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
noncomputable def leadingDigit (b : ℕ) (x : ℝ) : ℕ := ⌊mantissa b x⌋₊

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem mantissa_pos {b : ℕ} (hb : 2 ≤ b) (x : ℝ) : 0 < mantissa b x := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  exact Real.rpow_pos_of_pos hbpos _

/-- The mantissa lies in `[1, b)`. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem mantissa_mem_Ico {b : ℕ} (hb : 2 ≤ b) (x : ℝ) : mantissa b x ∈ Set.Ico 1 (b : ℝ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  constructor
  · calc (1 : ℝ) = (b : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ mantissa b x := by
          rw [mantissa, Real.rpow_le_rpow_left_iff hb1]; exact Int.fract_nonneg _
  · calc mantissa b x < (b : ℝ) ^ (1 : ℝ) := by
          rw [mantissa, Real.rpow_lt_rpow_left_iff hb1]; exact Int.fract_lt_one _
      _ = (b : ℝ) := Real.rpow_one _

/-- **The dictionary.**  A mantissa window `[c, d)` is exactly a window `[log_b c, log_b d)` of the
fractional part of the logarithm.  This is the whole content of "Benford = equidistribution of
`log_b`". -/
@[category API, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem mantissa_mem_Ico_iff {b : ℕ} (hb : 2 ≤ b) {x c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    mantissa b x ∈ Set.Ico c d ↔
      Int.fract (Real.logb b x) ∈ Set.Ico (Real.logb b c) (Real.logb b d) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  simp only [Set.mem_Ico, mantissa]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Real.logb_le_iff_le_rpow hb1 hc).mpr h1, (Real.lt_logb_iff_rpow_lt hb1 hd).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Real.logb_le_iff_le_rpow hb1 hc).mp h1, (Real.lt_logb_iff_rpow_lt hb1 hd).mp h2⟩

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem leadingDigit_eq_iff {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {k : ℕ} :
    leadingDigit b x = k ↔ mantissa b x ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
  rw [leadingDigit, Set.mem_Ico]
  exact Nat.floor_eq_iff (mantissa_pos hb x).le

/-! ## 3. The Benford harvest

The engine is Bertin's corollary to Weyl's criterion — `(nα)` is u.d. mod 1 iff `α` is irrational —
transported to the `Int.fract` convention by hygiene item H2 and then read through the dictionary.
-/

/-- `(n · log_b a)` is equidistributed modulo one as soon as `log_b a` is irrational.  This is the
one place the u.d. engine enters. -/
@[category API, AMS 11, ref "Ber92", group "th_benford_two_scale"]
theorem isEquidistributedModuloOne_nlogb {b : ℕ} {a : ℝ} (hirr : Irrational (Real.logb b a)) :
    IsEquidistributedModuloOne (fun n : ℕ => (n : ℝ) * Real.logb b a) :=
  (Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne _).mp
    ((Bertin.uniformlyDistributedModOne_nα_iff_irrational _).mpr hirr)

/-- **Logarithmic (Benford) distribution of the mantissa.**  If `log_b a` is irrational then the
mantissa of `aⁿ` in base `b` falls in the window `[c, d) ⊆ [1, b)` with asymptotic density
`log_b d − log_b c`.

No sign condition on `a` is needed: `Real.log` is even, so `mantissa` reads `|a|ⁿ`, and the
hypothesis `Irrational (Real.logb b a)` already rules out the degenerate values. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem tendsto_mantissa_density {b : ℕ} (hb : 2 ≤ b) {a : ℝ}
    (hirr : Irrational (Real.logb b a)) {c d : ℝ} (hc : 1 ≤ c) (hcd : c ≤ d) (hd : d ≤ (b : ℝ)) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => mantissa b (a ^ n) ∈ Set.Ico c d).card : ℝ) / N)
      atTop (𝓝 (Real.logb b d - Real.logb b c)) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (1 : ℕ) < b := by omega
    exact_mod_cast this
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le hc0 hcd
  have hd1 : Real.logb b d ≤ 1 := by
    have h := Real.logb_le_logb_of_le hb1 hd0 hd
    rwa [Real.logb_self_eq_one hb1] at h
  have hcount := (isEquidistributedModuloOne_nlogb (b := b) (a := a) hirr).tendsto_count_Ico
    (Real.logb_nonneg hb1 hc) (Real.logb_le_logb_of_le hb1 hc0 hcd) hd1
  refine hcount.congr fun N => ?_
  have hfil : ((Finset.range N).filter fun n : ℕ =>
        Int.fract ((n : ℝ) * Real.logb b a) ∈ Set.Ico (Real.logb b c) (Real.logb b d))
      = ((Finset.range N).filter fun n : ℕ => mantissa b (a ^ n) ∈ Set.Ico c d) := by
    refine Finset.filter_congr fun n _ => ?_
    rw [mantissa_mem_Ico_iff hb hc0 hd0, Real.logb_pow]
  rw [hfil]

/-- **Benford's law, leading-digit form.**  For a base `b ≥ 2` and `a > 0` with `log_b a`
irrational, the digit `k` leads `aⁿ` with density `log_b (k+1) − log_b k`. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem tendsto_leadingDigit_density {b : ℕ} (hb : 2 ≤ b) {a : ℝ}
    (hirr : Irrational (Real.logb b a)) {k : ℕ} (hk : 1 ≤ k) (hkb : k + 1 ≤ b) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => leadingDigit b (a ^ n) = k).card : ℝ) / N)
      atTop (𝓝 (Real.logb b ((k : ℝ) + 1) - Real.logb b (k : ℝ))) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkb' : (k : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hkb
  have h := tendsto_mantissa_density hb hirr (c := (k : ℝ)) (d := (k : ℝ) + 1)
    hk1 (by linarith) hkb'
  refine h.congr fun N => ?_
  have hfil : ((Finset.range N).filter fun n =>
        mantissa b (a ^ n) ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1))
      = ((Finset.range N).filter fun n => leadingDigit b (a ^ n) = k) := by
    refine Finset.filter_congr fun n _ => ?_
    rw [leadingDigit_eq_iff hb]
  rw [hfil]

/-- **Benford's law for `(3/2)ⁿ`, base 10.**  The first *solved* distributional theorem about the
actual sequence `(3/2)ⁿ` in this corpus — on its solved (top) scale.  Off-ladder: it says nothing
about `Int.fract ((3/2)ⁿ)`. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem benford_threeHalves_pow {k : ℕ} (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => leadingDigit 10 ((3 / 2 : ℝ) ^ n) = k).card : ℝ) / N)
      atTop (𝓝 (Real.logb 10 ((k : ℝ) + 1) - Real.logb 10 (k : ℝ))) := by
  have hirr : Irrational (Real.logb ((10 : ℕ) : ℝ) (3 / 2 : ℝ)) := by
    simpa using irrational_logb_ten_threeHalves
  simpa using tendsto_leadingDigit_density (b := 10) (a := (3 / 2 : ℝ)) (by norm_num)
    hirr hk (by omega)

/-- The familiar shape of Benford's law: density `log₁₀(1 + 1/k)`. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem benford_threeHalves_pow_inv_form {k : ℕ} (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => leadingDigit 10 ((3 / 2 : ℝ) ^ n) = k).card : ℝ) / N)
      atTop (𝓝 (Real.logb 10 (1 + 1 / (k : ℝ)))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hrw : Real.logb 10 (1 + 1 / (k : ℝ))
      = Real.logb 10 ((k : ℝ) + 1) - Real.logb 10 (k : ℝ) := by
    rw [← Real.logb_div (by positivity) hk0.ne']
    congr 1
    field_simp
  rw [hrw]
  exact benford_threeHalves_pow hk hk9

/-- **Benford's law for `3ⁿ`, base 10.** -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem benford_three_pow {k : ℕ} (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => leadingDigit 10 ((3 : ℝ) ^ n) = k).card : ℝ) / N)
      atTop (𝓝 (Real.logb 10 ((k : ℝ) + 1) - Real.logb 10 (k : ℝ))) := by
  have hirr : Irrational (Real.logb ((10 : ℕ) : ℝ) (3 : ℝ)) := by
    simpa using irrational_logb_ten_three
  simpa using tendsto_leadingDigit_density (b := 10) (a := (3 : ℝ)) (by norm_num)
    hirr hk (by omega)

/-- **The binary leading-block statement for `(3/2)ⁿ`.**  In base 2 the leading digit is always
`1`, so the informative statement is the block form: the binary mantissa equidistributes
logarithmically in `[1, 2)`. -/
@[category research solved, AMS 11, ref "A1plus" "KN74", group "th_benford_two_scale"]
theorem mantissa_block_threeHalves_pow_base_two {c d : ℝ} (hc : 1 ≤ c) (hcd : c ≤ d)
    (hd : d ≤ 2) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n =>
          mantissa 2 ((3 / 2 : ℝ) ^ n) ∈ Set.Ico c d).card : ℝ) / N)
      atTop (𝓝 (Real.logb 2 d - Real.logb 2 c)) := by
  have hirr : Irrational (Real.logb ((2 : ℕ) : ℝ) (3 / 2 : ℝ)) := by
    simpa using irrational_logb_of_two_dvd_base (b := 2) (m := 3) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using tendsto_mantissa_density (b := 2) (a := (3 / 2 : ℝ)) (by norm_num)
    hirr hc hcd (by norm_num; linarith)

/-! ## 4. The two-scale factorization

`(3/2)ⁿ = 2^{nθ}`.  The top scale is the rotation by `θ`; the bottom scale is what the M6/M7 ladder
is about, and the factorization says exactly how far apart they sit.
-/

/-- `θ = log₂(3/2) = log₂3 − 1`, the rotation number of the top scale. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
noncomputable def theta : ℝ := Real.logb 2 (3 / 2)

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem theta_eq_logb_two_three_sub_one : theta = Real.logb 2 3 - 1 := by
  rw [theta, Real.logb_div (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num)]

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem theta_pos : 0 < theta := Real.logb_pos (by norm_num) (by norm_num)

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem theta_lt_one : theta < 1 := by
  rw [theta, show (1 : ℝ) = Real.logb 2 2 from (Real.logb_self_eq_one (by norm_num)).symm]
  exact Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)

/-- `θ` is irrational: this is `3^q ≠ 2^p` again. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem irrational_theta : Irrational theta := by
  rw [theta]
  simpa using irrational_logb_of_two_dvd_base (b := 2) (m := 3) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The top scale is solved.**  `(nθ)` is uniformly distributed modulo one. -/
@[category research solved, AMS 11, ref "A1plus" "Ber92", group "th_benford_two_scale"]
theorem isEquidistributedModuloOne_theta :
    IsEquidistributedModuloOne (fun n : ℕ => (n : ℝ) * theta) :=
  (Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne _).mp
    ((Bertin.uniformlyDistributedModOne_nα_iff_irrational _).mpr irrational_theta)

@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem two_rpow_theta : (2 : ℝ) ^ theta = 3 / 2 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- `(3/2)ⁿ = 2^{nθ}` — the identity the whole section rests on. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem threeHalves_pow_eq_rpow (n : ℕ) : (3 / 2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * theta) := by
  rw [← two_rpow_theta, ← Real.rpow_natCast ((2 : ℝ) ^ theta) n, ← Real.rpow_mul (by norm_num),
    mul_comm]

/-- **The two-scale factorization.**  `(3/2)ⁿ` splits as an integer power of two (the *depth*)
times a function of the rotation coordinate alone (the *mantissa*). -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem threeHalves_pow_factorization (n : ℕ) :
    (3 / 2 : ℝ) ^ n
      = (2 : ℝ) ^ (⌊(n : ℝ) * theta⌋ : ℤ) * (2 : ℝ) ^ Int.fract ((n : ℝ) * theta) := by
  have h : ((⌊(n : ℝ) * theta⌋ : ℤ) : ℝ) + Int.fract ((n : ℝ) * theta) = (n : ℝ) * theta :=
    Int.floor_add_fract _
  calc (3 / 2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * theta) := threeHalves_pow_eq_rpow n
    _ = (2 : ℝ) ^ (((⌊(n : ℝ) * theta⌋ : ℤ) : ℝ) + Int.fract ((n : ℝ) * theta)) := by rw [h]
    _ = (2 : ℝ) ^ (((⌊(n : ℝ) * theta⌋ : ℤ) : ℝ)) * (2 : ℝ) ^ Int.fract ((n : ℝ) * theta) :=
        Real.rpow_add (by norm_num) _ _
    _ = (2 : ℝ) ^ (⌊(n : ℝ) * theta⌋ : ℤ) * (2 : ℝ) ^ Int.fract ((n : ℝ) * theta) := by
        rw [Real.rpow_intCast]

/-- **The mantissa is a function of the rotation coordinate alone.**  This is the precise sense in
which the top scale of `(3/2)ⁿ` is the solved rotation `(nθ mod 1)`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem mantissa_two_threeHalves_pow (n : ℕ) :
    mantissa 2 ((3 / 2 : ℝ) ^ n) = (2 : ℝ) ^ Int.fract ((n : ℝ) * theta) := by
  rw [mantissa, Real.logb_pow]
  norm_num [theta]

/-- **The wall.**  The open object `Int.fract ((3/2)ⁿ)` is a *depth-`⌊nθ⌋`* read of the solved
coordinate: shifting the mantissa up by `2^{⌊nθ⌋}` and taking the fractional part.  Since the depth
grows linearly (`depth_le`, `lt_depth_add_one`, with `0 < θ < 1`), the bottom scale asks for binary
digits of `2^{fract(nθ)}` at position `≈ θ·n` — the carry channel, which is exactly what GR4 says
no argument may ignore. -/
@[category research solved, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem fract_threeHalves_pow_eq (n : ℕ) :
    Int.fract ((3 / 2 : ℝ) ^ n)
      = Int.fract ((2 : ℝ) ^ (⌊(n : ℝ) * theta⌋ : ℤ) * mantissa 2 ((3 / 2 : ℝ) ^ n)) := by
  rw [mantissa_two_threeHalves_pow]
  exact congrArg Int.fract (threeHalves_pow_factorization n)

/-- The depth is `nθ + O(1)`, lower half. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem lt_depth_add_one (n : ℕ) : (n : ℝ) * theta - 1 < ((⌊(n : ℝ) * theta⌋ : ℤ) : ℝ) :=
  Int.sub_one_lt_floor _

/-- The depth is `nθ + O(1)`, upper half. -/
@[category API, AMS 11, ref "A1plus", group "th_benford_two_scale"]
theorem depth_le (n : ℕ) : ((⌊(n : ℝ) * theta⌋ : ℤ) : ℝ) ≤ (n : ℝ) * theta :=
  Int.floor_le _

end TH

