/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.MahlerFrame
import BB13.FailureCount

/-!
# Counting the general Mahler failures: confinement, finiteness, conditional counts

The per-line half of the general theory, and what it buys.  `BB13/MahlerFrame.lean` covers the
failures of `‖(p/q)ⁿ‖ < cⁿ` by at most `K(ε(p,c))` lines; here each line is shown to carry only
finitely many of them, elementarily, so that

* the failure set is **finite for every** coprime `p > q ≥ 2` and every `0 < c < 1`
  (`mahler_failures_finite`) — **Mahler's theorem re-derived along the quantitative route**, on
  `std3 + BugeaudEvertse.ridout_line_cover` and with no qualitative Subspace input;
* the count is bounded by `N + H·K(ε(p,c))` once a uniform per-line height `H` above a threshold
  `N` is granted (`mahler_failures_card_le_of_heightBound`) — the general form of
  `BB13.failures_card_le_of_heightBound`.

## The confinement, in general

If two failures `a < b` lie on one line then the collinearity analysis of `BB13/Subspace.lean` and
`BB13/GapPrinciple.lean` — which is already written for general `(p, q)` — gives

`k_b = p^{b−a}·k_a`,  hence  `p^{b−a} ≤ |k_b| < (cq)ᵇ`

because `k_a ≠ 0` (coprimality: `pᵃ` is never a multiple of `qᵃ` for `a ≥ 1`, `q > 1`).  Taking
logarithms and writing `f_∞ = log(p/(cq))/log p` for the archimedean exponent of the frame
(`BB13.fArch`), this reads

`b < a / f_∞`   (`sameLine_lt_div_fArch`),

so a line-fibre with least element `a` is confined to `[a, a/f_∞)`.  At `(3, 2, 3/4)`,
`f_∞ = θ = 0.63093…` and `1/f_∞ = log₂3 = 1.58496…`: the confinement of `BB13/LineTower.lean`,
recovered as a special case.

A free by-product of the same integrality: **if `c·q ≤ 1` there are no failures at all**
(`no_failure_of_mul_le_one`), since `|kₙ| ≥ 1` would have to be `< (cq)ⁿ ≤ 1`.

## What is *not* here

Nothing bounds the per-line height uniformly — that is the open problem [BE08] flags (Rem. 7.4),
open in the general case exactly as in the headline one.  The multiplier `δ` is also absent: for
`δ ≠ 1` the residue `δpᵃ − m qᵃ` can vanish (for the finitely many `a` with `qᵃ ∣ num δ`), so the
confinement would need the extra hypothesis `|num δ| < qᵃ`.  The line cover itself
(`BB13/MahlerFrame.lean`) has no such restriction.

## References

* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124.
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/plan-BB13-generalize.html` (G4); `plans/report-BB13.md` §3, item C.8.
-/

namespace BB13

open scoped Real

/-! ### Lines in the general frame -/

/-- Two indices lie on **one line** of the general `(p, q)` frame. -/
def SameLine (p q a b : ℕ) : Prop := linePointMul 1 p q a = linePointMul 1 p q b

/-- Equal slopes ⟺ collinear frame points — the dictionary to `BB13/Subspace.lean`'s elementary
`CollinearPts` analysis, which is already written for general `(p, q)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameLine_iff_collinear {p : ℕ} (q : ℕ) (hp : 0 < p) (a b : ℕ) :
    SameLine p q a b ↔ CollinearPts (failPoint p q a) (failPoint p q b) := by
  have hp0 : ((p : ℚ)) ≠ 0 := by positivity
  have hpa : ((p : ℚ)) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpb : ((p : ℚ)) ^ b ≠ 0 := pow_ne_zero _ hp0
  rw [SameLine, linePointMul, linePointMul, div_eq_div_iff hpa hpb, frameXMul, frameXMul,
    MnumMul_one, MnumMul_one]
  simp only [CollinearPts, failPoint]
  constructor
  · intro h
    have h' : Mnum p q a * (q : ℤ) ^ a * (p : ℤ) ^ b
        = Mnum p q b * (q : ℤ) ^ b * (p : ℤ) ^ a := by exact_mod_cast h
    linear_combination -h'
  · intro h
    have h' : Mnum p q a * (q : ℤ) ^ a * (p : ℤ) ^ b
        = Mnum p q b * (q : ℤ) ^ b * (p : ℤ) ^ a := by linear_combination -h
    exact_mod_cast h'

/-- **Residues scale along a line**: `k_b = p^{b−a}·k_a`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameLine_resid {p q a b : ℕ} (hp : 0 < p) (hq : 0 < q) (hab : a ≤ b)
    (h : SameLine p q a b) : resid p q b = (p : ℤ) ^ (b - a) * resid p q a :=
  collinear_resid p q a b hp hq hab ((sameLine_iff_collinear q hp a b).mp h)

/-! ### The residue never vanishes -/

/-- `kₐ = pᵃ − mₐqᵃ ≠ 0` for `a ≥ 1`: a power of `p` is never a multiple of `qᵃ` when
`gcd(p, q) = 1` and `q > 1`.  The general form of `BB13.resid_ne_zero`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_ne_zero_gen {p q a : ℕ} (hq : 1 < q) (hcop : Nat.Coprime p q) (ha : 1 ≤ a) :
    resid p q a ≠ 0 := by
  intro h
  rw [resid, sub_eq_zero] at h
  have hdvdZ : (q : ℤ) ∣ (p : ℤ) ^ a := by
    rw [h]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  have hdvd : q ∣ p ^ a := by exact_mod_cast hdvdZ
  have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd (hcop.symm.pow_right a) hdvd
  omega

/-- `1 ≤ |kₐ|` for `a ≥ 1` — the integrality that drives every confinement bound. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem one_le_abs_resid {p q a : ℕ} (hq : 1 < q) (hcop : Nat.Coprime p q) (ha : 1 ≤ a) :
    (1 : ℝ) ≤ |((resid p q a : ℤ) : ℝ)| := by
  have h := resid_ne_zero_gen hq hcop ha
  have h1 : (1 : ℤ) ≤ |resid p q a| := Int.one_le_abs h
  exact_mod_cast h1

/-- **No failures at all when `c·q ≤ 1`.**  A failure is the integer condition `|kₙ| < (cq)ⁿ`, and
`|kₙ| ≥ 1`; a rate that fast is simply unattainable.  (For `(p, q) = (3, 2)`: `‖(3/2)ⁿ‖ < (1/2)ⁿ`
never happens.) -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "bugeaud_10_13"]
theorem no_failure_of_mul_le_one {p q : ℕ} {c : ℝ} {n : ℕ} (hq : 1 < q)
    (hcop : Nat.Coprime p q) (hc0 : 0 ≤ c) (hcq : c * q ≤ 1) (hn : 1 ≤ n) :
    ¬ IsFailure p q c n := by
  intro hf
  have h1 : (1 : ℝ) ≤ |((resid p q n : ℤ) : ℝ)| := one_le_abs_resid hq hcop hn
  have h2 : (c * (q : ℝ)) ^ n ≤ 1 := pow_le_one₀ (by positivity) hcq
  have h3 : (|resid p q n| : ℝ) < (c * (q : ℝ)) ^ n := hf
  linarith

/-! ### Confinement -/

/-- The archimedean exponent is strictly positive as soon as `c·q < p` — automatic for `c < 1`
and `q < p`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem fArch_pos {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c)
    (hcq : c * q < p) : 0 < fArch p q c := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  rw [fArch_eq_log_div hp hq hc0]
  refine div_pos (Real.log_pos ?_) hlp
  rw [lt_div_iff₀ (by positivity)]
  linarith

/-- `f_∞·log p = log p − log(cq)`: the exponent, read as a logarithmic gap. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem fArch_mul_log {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q) (hc0 : 0 < c) :
    fArch p q c * Real.log p = Real.log p - Real.log (c * q) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  rw [fArch_eq_log_div hp hq hc0, div_mul_cancel₀ _ hlp,
    Real.log_div (ne_of_gt hp0) (by positivity)]

/-- **The gap principle on a line**: if `a < b` lie on one line and `b` is a failure, then
`p^{b−a} < (cq)ᵇ`.  The residue `kₐ` is amplified by `p^{b−a}` along the line and must still fit
under the failure bound at `b`, while `|kₐ| ≥ 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameLine_gap {p q a b : ℕ} {c : ℝ} (hp : 0 < p) (hq : 1 < q) (hcop : Nat.Coprime p q)
    (ha : 1 ≤ a) (hab : a < b) (hfb : IsFailure p q c b) (h : SameLine p q a b) :
    (p : ℝ) ^ (b - a) < (c * q) ^ b := by
  have hres := sameLine_resid hp (by omega) hab.le h
  have habs : |((resid p q b : ℤ) : ℝ)| = (p : ℝ) ^ (b - a) * |((resid p q a : ℤ) : ℝ)| := by
    rw [hres]; push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  have h1 : (1 : ℝ) ≤ |((resid p q a : ℤ) : ℝ)| := one_le_abs_resid hq hcop ha
  have h2 : (|resid p q b| : ℝ) < (c * (q : ℝ)) ^ b := hfb
  have hppos : (0 : ℝ) < (p : ℝ) ^ (b - a) :=
    pow_pos (by exact_mod_cast hp : (0 : ℝ) < (p : ℝ)) (b - a)
  have h3 : (p : ℝ) ^ (b - a) ≤ |((resid p q b : ℤ) : ℝ)| := by
    rw [habs]; nlinarith
  linarith

/-- **Confinement, in closed form**: a companion `b > a` of `a` on the same line satisfies
`b < a/f_∞`.  At `(3, 2, 3/4)`, `1/f_∞ = 1/θ = log₂3 = 1.58496…`, so `b < 1.585·a` — the bound of
`BB13/LineTower.lean`, in general form. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "bugeaud_10_13"]
theorem sameLine_lt_div_fArch {p q a b : ℕ} {c : ℝ} (hp : 1 < p) (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure p q c b) (h : SameLine p q a b) :
    (b : ℝ) < (a : ℝ) / fArch p q c := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqp' : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
  have hcq : c * (q : ℝ) < (p : ℝ) := by nlinarith
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hF : 0 < fArch p q c := fArch_pos hp (by omega) hc0 hcq
  have hgap := sameLine_gap (Nat.zero_lt_of_lt hp) hq hcop ha hab hfb h
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

/-! ### Every line carries finitely many failures -/

/-- The failures of `‖(p/q)ⁿ‖ < cⁿ` on the line of slope `r`. -/
def lineFibreGen (p q : ℕ) (c : ℝ) (r : ℚ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ IsFailure p q c n ∧ linePointMul 1 p q n = r}

/-- **A single line carries only finitely many failures**, for every `(p, q, c)` — elementarily,
with no Diophantine input: any member `a` confines the whole fibre below `a + ⌈a/f_∞⌉`. -/
@[category research solved, AMS 11, ref "Mah57" "Bug12", group "bugeaud_10_13"]
theorem lineFibreGen_finite {p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) (r : ℚ) :
    (lineFibreGen p q c r).Finite := by
  rcases Set.eq_empty_or_nonempty (lineFibreGen p q c r) with he | ⟨a, ha⟩
  · rw [he]; exact Set.finite_empty
  · refine Set.Finite.subset (Set.finite_Iic (a + ⌈(a : ℝ) / fArch p q c⌉₊)) ?_
    intro b hb
    rcases le_or_gt b a with hle | hlt
    · exact le_trans hle (by omega)
    · have hlt' := sameLine_lt_div_fArch hp hq hqp hcop hc0 hc1 ha.1 hlt hb.2.1
        (ha.2.2.trans hb.2.2.symm)
      have hb2 : b < ⌈(a : ℝ) / fArch p q c⌉₊ := Nat.lt_ceil.mpr hlt'
      exact Set.mem_Iic.mpr (by omega)

/-! ### Finiteness and the conditional count -/

/-- The failure set of `‖(p/q)ⁿ‖ < cⁿ`. -/
def failuresGen (p q : ℕ) (c : ℝ) : Set ℕ := {n : ℕ | 1 ≤ n ∧ IsFailure p q c n}

/-- The failures beyond an index `N`. -/
def failuresGenFrom (p q : ℕ) (c : ℝ) (N : ℕ) : Set ℕ := {n : ℕ | N ≤ n ∧ IsFailure p q c n}

/-- The failures beyond `N` lying on the line of slope `r` — the fibres whose size is the open
per-line problem. -/
def highFibreGen (p q : ℕ) (c : ℝ) (N : ℕ) (r : ℚ) : Set ℕ :=
  {n : ℕ | N ≤ n ∧ IsFailure p q c n ∧ linePointMul 1 p q n = r}

/-- **The height threshold of (5.12) is reached**: for every base `p ≥ 2` and rate `c < 1` there
is an `N ≥ 2` beyond which both `cⁿ < 1/16` and `pⁿ > 2H(1) = 2` hold, so that
`mahler_line_cover` applies.  (`N` is explicit in `c` and `p` — `⌈4 log 2/log(1/c)⌉` and `2` — but
existence is all the counts need.) -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem exists_threshold {p : ℕ} {c : ℝ} (hp : 1 < p) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight 1 : ℝ) < (p : ℝ) ^ n := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 16) hc1
  refine ⟨max 2 N₁, le_max_left _ _, fun n hn => ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt
      (pow_le_pow_of_le_one hc0.le hc1.le (le_trans (le_max_right _ _) hn)) hN₁
  · rw [BugeaudEvertse.ratHeight_one]
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hchain : (2 : ℝ) ^ 2 ≤ (p : ℝ) ^ n :=
      le_trans (pow_le_pow_right₀ (by norm_num) hn2) (pow_le_pow_left₀ (by norm_num) h2 n)
    norm_num at hchain ⊢
    linarith

/-- **The failures beyond the threshold form a finite set** — covered by finitely many lines
(`mahler_line_cover`), each carrying finitely many failures (`lineFibreGen_finite`). -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "bugeaud_10_13"]
theorem failuresGenFrom_finite {p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) {N : ℕ}
    (hthr : ∀ n, N ≤ n → c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight 1 : ℝ) < (p : ℝ) ^ n)
    (hN : 1 ≤ N) : (failuresGenFrom p q c N).Finite := by
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨R, -, hR⟩ := mahler_line_cover 1 p q c (by omega) hqp hcop hc0 hc1
  refine Set.Finite.subset
    (R.finite_toSet.biUnion (fun r _ => lineFibreGen_finite hp hq hqp hcop hc0 hc1 r)) ?_
  rintro n ⟨hn, hf⟩
  exact Set.mem_biUnion
    (hR n (hthr n hn).1 (hthr n hn).2 ((isFailureMul_one p q c n (by omega)).mpr hf))
    ⟨by omega, hf, rfl⟩

/-- **Mahler's theorem, along the quantitative route.**  For every coprime pair `p > q ≥ 2` and
every rate `0 < c < 1`, the set of `n ≥ 1` with `‖(p/q)ⁿ‖ < cⁿ` is **finite**.

The proof uses no qualitative Subspace input: the failures split into an initial segment below the
explicit height threshold and a union of at most `K(ε(p,c))` line-fibres, each finite by the
elementary gap principle.  Footprint `std3 + BugeaudEvertse.ridout_line_cover`.

This is the general form of `BB13.failures_finite_of_lineCover`, and settles report C.8's
"general effective Mahler count" as far as the literature allows: the *number of lines* is
effective and explicit, the number of failures per line is the open problem. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "bugeaud_10_13"]
theorem mahler_failures_finite {p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) : (failuresGen p q c).Finite := by
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨N, hN2, hthr⟩ := exists_threshold hp hc0 hc1
  refine Set.Finite.subset ((Set.finite_Iio N).union
    (failuresGenFrom_finite hq hqp hcop hc0 hc1 hthr (by omega))) ?_
  rintro n ⟨h1, hf⟩
  rcases lt_or_ge n N with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨hge, hf⟩

/-- **`#E(p, q, c) ≤ N + H·K(ε(p,c))`.**  If no line carries more than `H` failures beyond the
height threshold `N`, then the total number of `n ≥ 1` with `‖(p/q)ⁿ‖ < cⁿ` is at most
`N + H·K(ε(p,c))`.

The general form of `BB13.failures_card_le_of_heightBound`, where `(p, q, c) = (3, 2, 3/4)`,
`N = 257` and the initial segment is replaced by its exact kernel-certified count `5`.  As there,
the hypothesis `H` is the open per-line problem ([BE08] Rem. 7.4) and the confinement of
`sameLine_lt_div_fArch` bounds each fibre in terms of *its own* least element, not uniformly.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "Mah57" "BE08" "Bug12", group "bugeaud_10_13"]
theorem mahler_failures_card_le_of_heightBound {p q : ℕ} {c : ℝ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hc0 : 0 < c) (hc1 : c < 1) (N H : ℕ) (hN : 1 ≤ N)
    (hthr : ∀ n, N ≤ n → c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight 1 : ℝ) < (p : ℝ) ^ n)
    (hfib : ∀ r : ℚ, (highFibreGen p q c N r).ncard ≤ H) :
    (failuresGen p q c).ncard ≤ N + H * BugeaudEvertse.lineBound (epsilon p c) := by
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover 1 p q c (by omega) hqp hcop hc0 hc1
  have hfin := failuresGenFrom_finite hq hqp hcop hc0 hc1 hthr hN
  have hfib' : ∀ r : ℚ,
      {n ∈ failuresGenFrom p q c N | linePointMul 1 p q n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ failuresGenFrom p q c N | linePointMul 1 p q n = r} = highFibreGen p q c N r := by
      ext n
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    rw [heq]; exact hfib r
  have himg : linePointMul 1 p q '' failuresGenFrom p q c N ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hf⟩, rfl⟩
    exact hR n (hthr n hn).1 (hthr n hn).2 ((isFailureMul_one p q c n (by omega)).mpr hf)
  have hhigh : (failuresGenFrom p q c N).ncard ≤ H * BugeaudEvertse.lineBound (epsilon p c) := by
    calc (failuresGenFrom p q c N).ncard
        ≤ H * (linePointMul 1 p q '' failuresGenFrom p q c N).ncard :=
          Set.ncard_le_mul_ncard_image hfin _ H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound (epsilon p c) := Nat.mul_le_mul (le_refl H) hcard
  have hsub : failuresGen p q c ⊆ ↑(Finset.range N) ∪ failuresGenFrom p q c N := by
    rintro n ⟨h1, hf⟩
    rcases lt_or_ge n N with hlt | hge
    · exact Or.inl (by simpa using hlt)
    · exact Or.inr ⟨hge, hf⟩
  calc (failuresGen p q c).ncard
      ≤ (↑(Finset.range N) ∪ failuresGenFrom p q c N).ncard :=
        Set.ncard_le_ncard hsub ((Finset.range N).finite_toSet.union hfin)
    _ ≤ (↑(Finset.range N) : Set ℕ).ncard + (failuresGenFrom p q c N).ncard :=
        Set.ncard_union_le _ _
    _ = N + (failuresGenFrom p q c N).ncard := by rw [Set.ncard_coe_finset, Finset.card_range]
    _ ≤ N + H * BugeaudEvertse.lineBound (epsilon p c) := by omega

end BB13
