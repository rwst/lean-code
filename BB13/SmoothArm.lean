/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.ValuationArm

/-!
# The smooth arm and the cross-line eliminant (B3)

Item **B3** of `plans/report3-BB13.html` (§6, priority 4, rated 15%): *Corvaja–Zannier-style
valuation bounds on the `v` arm*, whose model is the [BCZ03] bound `gcd(2ⁿ − 1, 3ⁿ − 1) < e^{εn}`
(`CITED/BugeaudCorvajaZannier.lean`).  The report proposes to run the C–Z machine on the frame
congruence

`3ᵃ = μ·2^{a + w} + kₐ`,  `w = v₂(mₐ)`, `μ = mₐ/2^w` odd,

and asks for a dichotomy: *either `μ` has a large `{2,3}`-smooth part (C–Z applies, bounds `w`), or
`μ` is multiplicatively rough — then feed the pair of frame relations from two exceptions into
Subspace (the [BE08] elimination, dead within a line, is untested across lines with matched `μ`'s).*

Both branches are carried out here.  The outcome is positive on the first branch, sharply negative
on the second, and in both cases the mechanism turns out to be **not** the C–Z gcd machine:

## The smooth branch: every fixed prime is soft

`prime_valuation_finite`: *for every prime `p` and every `δ > 0` the set
`{a : δ·a ≤ v_p(mₐ)·log p}` is finite* — hence `v_p(mₐ)·log p = o(a)` for each fixed `p`, and by
`smoothPart_finite` the **`S`-smooth part of `mₐ` is `e^{o(a)}` for every fixed finite set of
primes `S`**.  The case `p = 2` is `BB13.valuation_arm_finite` (item B1), so this is the strict
generalization of B1 that B3's first branch asks for.

The mechanism is the [BE08] line cover already cited by the root, run on three frames:

* `p ∉ {2,3}` (`smooth_line_cover`): the frame point `(x, y) = (mₐ2ᵃ, 3ᵃ)` of `BB13/LineCover.lean`
  with `S₁ = {2, p}`, `S₂ = {3}` and budget `(1 − θ) + θ + δ + 1 = 2 + δ` — the whole surplus is
  the new `p`-adic row, the archimedean and `2`-adic rows are the free ones;
* `p = 3` (`three_arm_line_cover`): the numerator's own prime cannot be charged twice, so the
  frame is *reduced*, `(x, y) = ((mₐ/3^{v₃})·2ᵃ, 3^{a − v₃})` — same slope, same budget
  `(1 − θ) + θ(1 + δ) + 1 = 2 + θδ` as B1, with the surplus paid by the drop in height;
* `p = 2` is B1 verbatim.

No Corvaja–Zannier input is used anywhere: **B3's first branch is a Ridout budget, not a gcd
theorem**, and it is available at every place at once.  What C–Z's machine needs and this frame
does not have is *two* independent divisibility relations for the quantity to be bounded (in
[BCZ03], `d ∣ aⁿ − 1` and `d ∣ bⁿ − 1`, which give the two convergent expansions of `1/d` that
the Subspace theorem then compares).  The frame supplies one.

## The free coupling at the place 3, and what it caps

`three_dvd_resid`: `3^{v₃(mₐ)} ∣ kₐ`, because `3^{v₃} ∣ mₐ2ᵃ` and `3^{v₃} ∣ 3ᵃ`.  Hence
`three_fibre_cap`: on a fibre of size `d` over `a`,

`2ᵈ · 3^{v₃(mₐ)} < (3/2)ᵃ`,  i.e.  `d·log 2 + v₃(mₐ)·log 3 < a·log(3/2)`,

**unconditionally**.  This is exactly the shape of the weighted cap that item B2 has to assume a
rate for (`BB13.weighted_fibre_cap`), available here for free — but at the place `3`, where the
weight is idle: `v₃(mₐ)` is `O(1)`-sized in practice (max `9` for `a ≤ 20000`), while the arm that
has to be bounded is `v₂`.  The asymmetry is structural: `3` is the *numerator's* prime, so its
valuation in `mₐ` is forced into `kₐ`, whereas `v₂(mₐ)` is invisible to `kₐ`.

## The rough branch: the cross-line eliminant is the gap principle

For any common divisor `g` of `mₐ` and `m_b`, `b = a + d`, with `ν = mₐ/g`, `ν' = m_b/g`:

`3ᵃ·(ν'2ᵈ − ν3ᵈ) = ν'2ᵈkₐ − νk_b`   (`cross_identity`, pure ring),

and `cross_eq_zero_iff`: the eliminant `Δ = ν'2ᵈ − ν3ᵈ` vanishes **iff** `3ᵈmₐ = 2ᵈm_b`, i.e. iff
`a` and `b` lie on one line (`BB13.SameTower`).  Off a line `Δ` is a nonzero integer, `|Δ| ≥ 1`,
and the identity gives (`cross_gap`, `cross_gap_reach`)

`g·2ᵃ < m_b·2ᵈ + mₐ·(3/2)ᵈ`,  hence  `g·(4/3)ᵃ < 4·3ᵈ`.

At `g = 1` this is the gap principle of `BB13/GapPrinciple.lean` — `d > ε*·a − log₃4`,
`ε* = log(4/3)/log 3` — re-derived from the elimination (`gap_principle_of_cross`).  So the
cross-line elimination the report proposes is **not new machinery**: it is the gap principle, and
its only Diophantine input is `|Δ| ≥ 1`.  The Subspace theorem has nothing to act on, the
eliminated relation having two S-unit terms rather than three.

What matching buys is exactly `log₃ g`: the reach of the gap principle grows from `ε*a` to
`ε*a + log₃ g`.  To gain a *proportion* of `a` one needs `g ≥ 3^{δa}` — an exponentially large
common factor of two numerators.  Measured (`BB13/b3_smooth.py` block [E]): over all `79 800`
pairs `a < b ≤ 400`, the largest `gcd(mₐ, m_b)` off a line is `6799 = 3^{8.03}` (at `(287, 344)`),
the coprime share is `0.66` against the random-integer `6/π² = 0.6079`, and the whole gcd
statistic is the one of random integers.  The full match `g = μ` does occur — on a line, where the
eliminant vanishes identically.  **Matching and information are in exact tension**, which is the
precise form of the report's "dead within a line", now known also across lines.

The one place where the matched configuration does say something is the extreme case `mₐ` and
`m_b` with equal odd parts (`matched_separation`): then `Δ ≠ 0` automatically for `d ≥ 1`, and

`2ᵃ < 8·2^{v₂(mₐ)}·3ᵈ`,  i.e.  `d > (a − v₂(mₐ) − 3)·log 2/log 3`,

so with `v₂(mₐ) = o(a)` (the smooth branch above) two indices with the same odd part are separated
by `d ≥ (0.63 − o(1))·a`: a fixed-`μ` rigidity statement, the multiplicative companion of the
fixed-`k` rigidity of the report's §4 (CB1).  Empirically the only equal-odd-part pairs below
`700` are `(1,2)`, `(1,5)`, `(2,5)` — the three indices whose `mₐ` is a *power of two*, so `μ = 1`;
no pair with `μ > 1` occurs.

## The effective corner

`smooth_effective`: if `mₐ` is *fully* `{2,3}`-smooth, `mₐ = 2^w3^t`, the frame relation collapses
to the two-term form `|3^{a−t} − 2^{a+w}| < 3^{a−t}/2ᵃ`, and any effective rate `‖(3/2)ᴬ‖ > cᴬ`
bounds `a` in terms of `a − t`: `2ᵃ < (3/(2c))^{a−t}`.  With [Zud07]'s `c = 0.5803` that is
`t ≤ 0.2701·a`, **effectively** — against the ineffective `o(a)` of the smooth branch.  This is the
honest content of "the smooth branch is where things become effective", and it is also its limit:
the collapse needs `mₐ` smooth, not merely largely smooth, because a rough cofactor is a
coefficient of unbounded height and no monomial scheme sees it.  Census: `mₐ` is `{2,3}`-smooth
exactly for `a ∈ {1, 2, 3, 5}` in `a ≤ 20000` (`b3_smooth.py` block [B]).

## What is not proved here

No bound on `v₂(mₐ)` beyond B1's `o(a)`; in particular neither of B3's advertised deliverables
(`w = O(a/log a)`, or `w ≤ εa` with an effective exception count).  The two branches of the
report's dichotomy are settled as *branch 1 = a Ridout budget at every fixed place, ineffective*
and *branch 2 = the gap principle, whose extension is priced at `3^{δa}` of matching*.  The rate
hypotheses of `smooth_effective` and the two-log input quoted in the docstring are **hypotheses**,
never axioms: the file's footprint is the root's single cited axiom.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover` — the same single cited axiom as the rest of
the `BB13/` root.  `cross_identity` … `matched_separation`, `three_dvd_resid` …
`three_fibre_cap` and `smooth_effective` are `std3` alone.

## References

* [BCZ03] Y. Bugeaud, P. Corvaja, U. Zannier, *An upper bound for the G.C.D. of `aⁿ − 1` and
  `bⁿ − 1`*, Math. Z. **243** (2003), 79–84 — the model theorem, `CITED/BugeaudCorvajaZannier.lean`.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Cor. 5.2, `CITED/BugeaudEvertseRidout.lean`.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  **193**, 2012 — Problem 10.13.
* [CZ05] P. Corvaja, U. Zannier, *A lower bound for the height of a rational function at `S`-unit
  points*, Monatsh. Math. **144** (2005), 203–224 — the general gcd machine.
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux **19** (2007),
  311–323 — the effective rate quoted in `smooth_effective`.
* `plans/report3-BB13.html` §6 B3 (the strategy item), §4 (the 2-adic reformulation and CB1),
  §7 (the priority grid); `plans/note-BB13-B3.html` (this work).
-/

namespace BB13

open scoped Real

/-! ### The valuation of `mₐ` at a general prime -/

/-- **`v_p(mₐ)`** — the `p`-adic valuation of `mₐ = round((3/2)ᵃ)`.  `vAt 2` is `BB13.vTwo`, the
`v` arm of the per-line problem; `vAt 3` is the one place whose valuation is forced into the
residue (`three_dvd_resid`); every other `vAt p` measures a slice of the smooth part of `mₐ`. -/
noncomputable def vAt (p a : ℕ) : ℕ := padicValInt p (Mnum 3 2 a)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vAt_two (a : ℕ) : vAt 2 a = vTwo a := rfl

/-- `p^{v_p(mₐ)} ∣ mₐ`: the defining property of `vAt`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem pow_vAt_dvd (p a : ℕ) : (p : ℤ) ^ vAt p a ∣ Mnum 3 2 a := padicValInt_dvd _

/-- Maximality of `vAt`: `p^D ∣ mₐ → D ≤ v_p(mₐ)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem le_vAt_of_dvd {p a D : ℕ} (hp : p ≠ 1) (h : (p : ℤ) ^ D ∣ Mnum 3 2 a) : D ≤ vAt p a := by
  rcases (padicValInt_dvd_iff_of_ne_one hp D _).mp h with h0 | hle
  · exact absurd h0 (Mnum_ne_zero a)
  · exact hle

/-! ### Two elementary size bounds on `mₐ` -/

/-- `mₐ ≤ (3/2)ᵃ + 1/2` — the nearest-integer bound, upward. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem Mnum_le_add_half (a : ℕ) : (Mnum 3 2 a : ℝ) ≤ (3 / 2 : ℝ) ^ a + 1 / 2 := by
  have h := abs_sub_round ((((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a)
  have hc : (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a = (3 / 2 : ℝ) ^ a := by norm_num
  rw [hc] at h
  have h2 := abs_le.mp h
  have : ((round ((3 / 2 : ℝ) ^ a) : ℤ) : ℝ) = (Mnum 3 2 a : ℝ) := by
    rw [Mnum, hc]
  linarith [h2.1, this]

/-- `1 ≤ (3/2)ᵃ` — used to absorb the rounding constant on both sides. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem one_le_three_halves_pow (a : ℕ) : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ a :=
  one_le_pow₀ (by norm_num)

/-- `mₐ ≤ 2·(3/2)ᵃ` — the crude upward bound the cross-line estimate runs on. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem Mnum_le_two_mul (a : ℕ) : (Mnum 3 2 a : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ a := by
  have h1 := Mnum_le_add_half a
  have h2 := one_le_three_halves_pow a
  linarith

/-- `(3/2)ᵃ/2 ≤ mₐ` — the crude downward bound. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem half_le_Mnum (a : ℕ) : (3 / 2 : ℝ) ^ a / 2 ≤ (Mnum 3 2 a : ℝ) := by
  have h := abs_sub_round ((((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a)
  have hc : (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a = (3 / 2 : ℝ) ^ a := by norm_num
  rw [hc] at h
  have h2 := abs_le.mp h
  have hval : ((round ((3 / 2 : ℝ) ^ a) : ℤ) : ℝ) = (Mnum 3 2 a : ℝ) := by rw [Mnum, hc]
  have h3 := one_le_three_halves_pow a
  linarith [h2.2, hval]

/-- `v₃(mₐ) ≤ a`: `3^{v₃} ≤ mₐ < 3^{a+1}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vAt_three_le (a : ℕ) : vAt 3 a ≤ a := by
  have hdvd := pow_vAt_dvd 3 a
  have hpos := Mnum_pos a
  have hle : (3 : ℤ) ^ vAt 3 a ≤ Mnum 3 2 a := Int.le_of_dvd hpos hdvd
  have hR : ((3 : ℝ)) ^ vAt 3 a ≤ (Mnum 3 2 a : ℝ) := by exact_mod_cast hle
  have hup : (Mnum 3 2 a : ℝ) < (3 : ℝ) ^ (a + 1) := by
    have h1 := Mnum_le_two_mul a
    have h2 : (3 / 2 : ℝ) ^ a ≤ (3 : ℝ) ^ a := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) a
    have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
    have : (3 : ℝ) ^ (a + 1) = 3 * (3 : ℝ) ^ a := by ring
    rw [this]
    linarith
  by_contra hcon
  have hlt : a + 1 ≤ vAt 3 a := by omega
  have : (3 : ℝ) ^ (a + 1) ≤ (3 : ℝ) ^ vAt 3 a := pow_le_pow_right₀ (by norm_num) hlt
  linarith

/-! ### The `p`-adic row of the frame, at a general prime -/

/-- The comparison `p^{−v} ≤ (3ᵃ)^{−δ}` behind every `p`-adic row: it is `δ·a·log 3 ≤ v·log p`,
exponentiated. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem pow_neg_le_rpow_of_logs {p v a : ℕ} {δ : ℝ} (hp : 1 < p)
    (h : δ * (a : ℝ) * Real.log 3 ≤ (v : ℝ) * Real.log p) :
    (p : ℝ) ^ (-(v : ℝ)) ≤ ((3 : ℝ) ^ a) ^ (-δ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := lt_trans Nat.zero_lt_one hp
    exact_mod_cast this
  have h3a : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos h3a, Real.exp_le_exp, Real.log_pow]
  nlinarith [h]

/-- **The `p`-adic condition at a prime `p ∉ {2,3}`**: if `δ·a·log 3 ≤ v_p(mₐ)·log p` then
`|x|_p ≤ (3ᵃ)^{−δ}` for the frame point `x = mₐ2ᵃ`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_p_adic {p a : ℕ} (hp : p.Prime) {δ : ℝ}
    (h : δ * (a : ℝ) * Real.log 3 ≤ (vAt p a : ℝ) * Real.log p) :
    ((padicNorm p ((frameX a : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ a) ^ (-δ) := by
  have hdvd : (p : ℤ) ^ vAt p a ∣ frameX a := Dvd.dvd.mul_right (pow_vAt_dvd p a) _
  exact le_trans (BugeaudEvertse.padicNorm_le_of_dvd_pow hp hdvd)
    (pow_neg_le_rpow_of_logs hp.one_lt h)

/-! ### The smooth branch at a prime `p ∉ {2, 3}` -/

/-- **The line cover at a third prime.**  For a prime `p ∉ {2,3}` and `δ > 0` there are at most
`K(δ)` slopes carrying the frame point of every large `a` with `δ·a·log 3 ≤ v_p(mₐ)·log p`.

[BE08] Cor. 5.2 on the frame `(f_∞, f₂, f_p, f₃) = (1 − θ, θ, δ, 1)`, whose budget is `2 + δ`:
the archimedean row is the free rounding bound of `BB13.frame_archimedean_trivial`, the `2`-adic
row the free `2ᵃ ∣ x` of `BB13.frame_two_adic`, and the whole surplus is the new `p`-adic row.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem smooth_line_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R : Finset ℚ) (N : ℕ), R.card ≤ BugeaudEvertse.lineBound δ ∧
      ∀ a : ℕ, N ≤ a → δ * (a : ℝ) * Real.log 3 ≤ (vAt p a : ℝ) * Real.log p →
        linePoint a ∈ R := by
  have h2p : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have hdisj : Disjoint ({2, p} : Finset ℕ) ({3} : Finset ℕ) := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨by norm_num, fun h => hp3 h.symm⟩
  have hsum : (1 - theta) + ∑ l ∈ ({2, p} : Finset ℕ) ∪ ({3} : Finset ℕ),
      (fun l => if l = 2 then theta else if l = 3 then (1 : ℝ) else δ) l = 2 + δ := by
    rw [Finset.sum_union hdisj, Finset.sum_pair h2p, Finset.sum_singleton, ite_eq_right hp2, ite_eq_right hp3]
    norm_num
    ring
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover 1 δ (1 - theta) {2, p} {3}
    (fun l => if l = 2 then theta else if l = 3 then (1 : ℝ) else δ)
    (by intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact Nat.prime_two
        · exact hp)
    (by intro l hl; simp only [Finset.mem_singleton] at hl; exact hl ▸ Nat.prime_three)
    hdisj hδ (by linarith [theta_lt_one])
    (by intro l _
        by_cases h1 : l = 2
        · simp only [ite_eq_left h1]; exact theta_pos.le
        · by_cases h2 : l = 3
          · simp only [ite_eq_right h1, ite_eq_left h2]; norm_num
          · simp only [ite_eq_right h1, ite_eq_right h2]; exact hδ.le)
    hsum
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / δ)))
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨R, N, hcard, fun a haN hva => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / δ))
      < ((frameY a : ℤ) : ℝ) := by
    rw [frameY_cast]
    exact lt_of_lt_of_le hN (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) haN)
  refine hR (frameX a) (frameY a) (frameY_pos a) hheight ?_ ?_ ?_
  · simpa using frame_archimedean_trivial a
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simpa using frame_two_adic a
    · simp only [ite_eq_right hp2, ite_eq_right hp3]
      rw [frameY_cast]
      exact frame_p_adic hp hva
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    subst hl
    simpa using frame_three_adic a

/-- **`v_p(mₐ)·log p = o(a)` at every prime `p ∉ {2,3}`**, unconditionally and ineffectively:
for each `δ > 0` only finitely many `a` have `δ·a·log 3 ≤ v_p(mₐ)·log p`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem smooth_arm_finite {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {δ : ℝ} (hδ : 0 < δ) :
    {a : ℕ | δ * (a : ℝ) * Real.log 3 ≤ (vAt p a : ℝ) * Real.log p}.Finite := by
  obtain ⟨R, N, -, hR⟩ := smooth_line_cover hp hp2 hp3 hδ
  refine Set.Finite.subset
    (Set.Finite.union (Set.finite_lt_nat (max N 1))
      (Set.Finite.biUnion R.finite_toSet (fun r _ => linePointFibre_finite r))) ?_
  intro a ha
  rcases lt_or_ge a (max N 1) with hlt | hge
  · exact Or.inl hlt
  · refine Or.inr ?_
    have haN : N ≤ a := le_trans (le_max_left _ _) hge
    have ha1 : 1 ≤ a := le_trans (le_max_right _ _) hge
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hR a haN ha)) ⟨ha1, rfl⟩

/-! ### The smooth branch at `p = 3`: the reduced frame

The numerator's own prime cannot be charged twice — the budget already spends `1` on `|y|₃` — so
the `3`-adic surplus is taken by *reducing* the frame point: `x = (mₐ/3^{v₃})·2ᵃ`, `y = 3^{a−v₃}`.
The slope is unchanged, so the same per-line finiteness applies; the height drops by `3^{v₃}`,
which is where the surplus comes from. -/

/-- `2^{−a} ≤ (3^{a−v})^{−θ(1+δ)}` whenever `δ·a ≤ v` — the `2`-adic row of the reduced frame.
The reduction of the height by `3ᵛ` is what makes the free divisibility `2ᵃ ∣ x` pay the shifted
exponent. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem two_pow_le_rpow_reduced {a v : ℕ} {δ : ℝ} (hv : v ≤ a) (hδ : 0 < δ)
    (h : δ * (a : ℝ) ≤ (v : ℝ)) :
    (1 / 2 : ℝ) ^ a ≤ ((3 : ℝ) ^ (a - v)) ^ (-(theta * (1 + δ))) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (a - v) := by positivity
  have hlhs : (0 : ℝ) < (1 / 2 : ℝ) ^ a := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((a - v : ℕ) : ℝ) = (a : ℝ) - (v : ℝ) := by
    rw [Nat.cast_sub hv]
  rw [Real.rpow_def_of_pos h3, ← Real.exp_log hlhs, Real.exp_le_exp, Real.log_pow, Real.log_pow,
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [← Real.log_inv]; norm_num, hcast]
  have hrhs : ((a : ℝ) - (v : ℝ)) * Real.log 3 * (-(theta * (1 + δ)))
      = -(((a : ℝ) - (v : ℝ)) * (1 + δ) * Real.log 2) := by
    rw [← theta_mul_log_three]; ring
  rw [hrhs]
  have hva : (v : ℝ) ≤ (a : ℝ) := by exact_mod_cast hv
  have hvnn : (0 : ℝ) ≤ (v : ℝ) := Nat.cast_nonneg v
  have hstep : ((a : ℝ) - (v : ℝ)) * (1 + δ) ≤ (a : ℝ) := by
    nlinarith [h, hδ.le, mul_nonneg hvnn hδ.le]
  have hmul : ((a : ℝ) - (v : ℝ)) * (1 + δ) * Real.log 2 ≤ (a : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hstep hl2.le
  linarith

/-- **The line cover at `p = 3`**, on the reduced frame `((mₐ/3^{v₃})2ᵃ, 3^{a−v₃})`: for `δ > 0`
at most `K(θδ)` slopes carry every large `a` with `δ·a ≤ v₃(mₐ)`.

The budget is B1's, `(1 − θ) + θ(1 + δ) + 1 = 2 + θδ` (`BB13.budget_valuation_arm`), but the
surplus is paid differently: not by extra `2`-adic depth, by the drop of the height from `3ᵃ` to
`3^{a−v₃}`.  The slope of the reduced point is the slope of the full one, so `linePointFibre_finite`
still closes the argument.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem three_arm_line_cover {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R : Finset ℚ) (N : ℕ), R.card ≤ BugeaudEvertse.lineBound (theta * δ) ∧
      ∀ a : ℕ, N ≤ a → δ * (a : ℝ) ≤ (vAt 3 a : ℝ) → linePoint a ∈ R := by
  have hθδ : 0 < theta * δ := mul_pos theta_pos hδ
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 (theta * δ) (1 - theta)
    (theta * (1 + δ)) 1 hθδ (by linarith [theta_lt_one])
    (mul_nonneg theta_pos.le (by linarith)) zero_le_one (budget_valuation_arm δ)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (2 * max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / (theta * δ))))
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨R, N, hcard, fun a haN hva => ?_⟩
  -- the reduced frame point
  obtain ⟨μ, hμ⟩ := pow_vAt_dvd 3 a
  set v := vAt 3 a with hvdef
  have hv : v ≤ a := vAt_three_le a
  set x : ℤ := μ * 2 ^ a with hx
  set y : ℤ := 3 ^ (a - v) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyR : ((y : ℤ) : ℝ) = (3 : ℝ) ^ (a - v) := by rw [hy]; push_cast; ring
  have hsplit : (3 : ℤ) ^ (a - v) * 3 ^ v = 3 ^ a := by
    rw [← pow_add, Nat.sub_add_cancel hv]
  -- the slope is unchanged
  have hslope : (x : ℚ) / (y : ℚ) = linePoint a := by
    have hxq : ((x : ℤ) : ℚ) = (μ : ℚ) * 2 ^ a := by rw [hx]; push_cast; ring
    have hyq : ((y : ℤ) : ℚ) = 3 ^ (a - v) := by rw [hy]; push_cast; ring
    have hfx : ((frameX a : ℤ) : ℚ) = (Mnum 3 2 a : ℚ) * 2 ^ a := by
      rw [frameX]; push_cast; ring
    have hfy : ((frameY a : ℤ) : ℚ) = 3 ^ a := by rw [frameY]; push_cast; ring
    have hμq : ((Mnum 3 2 a : ℤ) : ℚ) = 3 ^ v * (μ : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hμ
      push_cast at this
      exact this
    have hsq : (3 : ℚ) ^ (a - v) * 3 ^ v = 3 ^ a := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    have hy0q : ((y : ℤ) : ℚ) ≠ 0 := by rw [hyq]; positivity
    have hfy0 : ((frameY a : ℤ) : ℚ) ≠ 0 := by rw [hfy]; positivity
    rw [linePoint, div_eq_div_iff hy0q hfy0, hxq, hyq, hfx, hfy, hμq]
    linear_combination (-(μ : ℚ) * 2 ^ a) * hsq
  -- the height
  have h3v : ((3 : ℝ)) ^ v ≤ 2 * (3 / 2 : ℝ) ^ a := by
    have hdvd : (3 : ℤ) ^ v ≤ Mnum 3 2 a := Int.le_of_dvd (Mnum_pos a) (pow_vAt_dvd 3 a)
    have : ((3 : ℝ)) ^ v ≤ (Mnum 3 2 a : ℝ) := by exact_mod_cast hdvd
    linarith [Mnum_le_two_mul a]
  have hheightlow : (2 : ℝ) ^ a / 2 ≤ ((y : ℤ) : ℝ) := by
    rw [hyR]
    have hsplitR : (3 : ℝ) ^ (a - v) * 3 ^ v = 3 ^ a := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    have h3vpos : (0 : ℝ) < (3 : ℝ) ^ v := by positivity
    have hkey : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (a - v) * (2 * (3 / 2 : ℝ) ^ a) := by
      calc (3 : ℝ) ^ a = (3 : ℝ) ^ (a - v) * 3 ^ v := hsplitR.symm
        _ ≤ (3 : ℝ) ^ (a - v) * (2 * (3 / 2 : ℝ) ^ a) := by
            have : (0 : ℝ) ≤ (3 : ℝ) ^ (a - v) := by positivity
            exact mul_le_mul_of_nonneg_left h3v this
    have hpow : (3 : ℝ) ^ a = (2 : ℝ) ^ a * (3 / 2 : ℝ) ^ a := by
      rw [← mul_pow]; norm_num
    have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
    rw [hpow] at hkey
    nlinarith [hkey, h32]
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
      ((2 : ℝ) ^ ((4 : ℝ) / (theta * δ))) < ((y : ℤ) : ℝ) := by
    have h2a : 2 * max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
        ((2 : ℝ) ^ ((4 : ℝ) / (theta * δ))) < (2 : ℝ) ^ a :=
      lt_of_lt_of_le hN (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) haN)
    linarith [hheightlow]
  rw [← hslope]
  refine hR x y hy0 hheight ?_ ?_ ?_
  · -- archimedean
    have harch : |(1 : ℝ) - ((linePoint a : ℚ) : ℝ)| ≤ (2 / 3 : ℝ) ^ a := abs_one_sub_linePoint_le a
    have hxyR : ((x : ℤ) : ℝ) / ((y : ℤ) : ℝ) = ((linePoint a : ℚ) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hslope
      push_cast at this
      exact this
    have hstep : (2 / 3 : ℝ) ^ a ≤ ((y : ℤ) : ℝ) ^ (-(1 - theta)) := by
      rw [hyR, rpow_neg_one_sub_theta (a - v)]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le a v)
    have hfinal : |(1 : ℝ) - ((x : ℤ) : ℝ) / ((y : ℤ) : ℝ)| ≤ ((y : ℤ) : ℝ) ^ (-(1 - theta)) :=
      calc |(1 : ℝ) - ((x : ℤ) : ℝ) / ((y : ℤ) : ℝ)|
          = |(1 : ℝ) - ((linePoint a : ℚ) : ℝ)| := by rw [hxyR]
        _ ≤ (2 / 3 : ℝ) ^ a := harch
        _ ≤ ((y : ℤ) : ℝ) ^ (-(1 - theta)) := hstep
    simpa using hfinal
  · -- the 2-adic row
    have hdvd : ((2 ^ a : ℕ) : ℤ) ∣ x := by rw [hx]; push_cast; exact dvd_mul_left _ _
    have h := padicNorm.dvd_iff_norm_le.mp hdvd
    have hcast : (((2 : ℚ) ^ (-(a : ℤ)) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ a := by
      push_cast; rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have hle : ((padicNorm 2 ((x : ℤ) : ℚ) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ a := by
      rw [← hcast]; exact_mod_cast h
    refine le_trans hle ?_
    rw [hyR]
    exact two_pow_le_rpow_reduced hv hδ hva
  · -- the 3-adic row
    have hdvd : ((3 ^ (a - v) : ℕ) : ℤ) ∣ y := by rw [hy]; push_cast; exact dvd_rfl
    have h := padicNorm.dvd_iff_norm_le.mp hdvd
    have hcast : (((3 : ℚ) ^ (-((a - v : ℕ) : ℤ)) : ℚ) : ℝ) = ((3 : ℝ) ^ (a - v))⁻¹ := by
      push_cast; rw [zpow_neg, zpow_natCast]
    rw [hyR, Real.rpow_neg (by positivity), Real.rpow_one, ← hcast]
    exact_mod_cast h

/-- **`v₃(mₐ) = o(a)`**: for every `δ > 0` only finitely many `a` have `δ·a ≤ v₃(mₐ)`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem three_arm_finite {δ : ℝ} (hδ : 0 < δ) : {a : ℕ | δ * (a : ℝ) ≤ (vAt 3 a : ℝ)}.Finite := by
  obtain ⟨R, N, -, hR⟩ := three_arm_line_cover hδ
  refine Set.Finite.subset
    (Set.Finite.union (Set.finite_lt_nat (max N 1))
      (Set.Finite.biUnion R.finite_toSet (fun r _ => linePointFibre_finite r))) ?_
  intro a ha
  rcases lt_or_ge a (max N 1) with hlt | hge
  · exact Or.inl hlt
  · refine Or.inr ?_
    have haN : N ≤ a := le_trans (le_max_left _ _) hge
    have ha1 : 1 ≤ a := le_trans (le_max_right _ _) hge
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hR a haN ha)) ⟨ha1, rfl⟩

/-! ### Every fixed prime, and every fixed finite set of primes -/

/-- **The smooth branch of B3, at one prime**: for every prime `p` and every `δ > 0` the set
`{a : δ·a ≤ v_p(mₐ)·log p}` is finite — hence `v_p(mₐ)·log p = o(a)`.

`p = 2` is `BB13.valuation_arm_finite` (item B1), `p = 3` is `three_arm_finite` on the reduced
frame, and `p ∉ {2,3}` is `smooth_arm_finite`.  Ineffective at every prime, for the same reason
(report §3, remark 1).

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "BCZ03", group "bugeaud_10_13"]
theorem prime_valuation_finite {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    {a : ℕ | δ * (a : ℝ) ≤ (vAt p a : ℝ) * Real.log p}.Finite := by
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rcases eq_or_ne p 2 with rfl | hp2
  · have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    refine Set.Finite.subset (valuation_arm_finite (δ / Real.log 2) (by positivity)) ?_
    intro a ha
    simp only [Set.mem_ofPred_eq, vAt_two] at ha ⊢
    push_cast at ha
    rw [div_mul_eq_mul_div, div_le_iff₀ hl2]
    exact ha
  · rcases eq_or_ne p 3 with rfl | hp3
    · refine Set.Finite.subset (three_arm_finite (δ := δ / Real.log 3) (by positivity)) ?_
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      push_cast at ha
      rw [div_mul_eq_mul_div, div_le_iff₀ hl3]
      exact ha
    · refine Set.Finite.subset
        (smooth_arm_finite hp hp2 hp3 (δ := δ / Real.log 3) (by positivity)) ?_
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      have hrw : δ / Real.log 3 * (a : ℝ) * Real.log 3 = δ * (a : ℝ) := by
        field_simp
      rw [hrw]
      exact ha

/-- **The `S`-smooth part of `mₐ` is `e^{o(a)}`, for every fixed finite set of primes `S`**: for
each `δ > 0` only finitely many `a` have `δ·a ≤ ∑_{p ∈ S} v_p(mₐ)·log p`.

This is B3's first branch in full.  The proof is `prime_valuation_finite` at each `p ∈ S` plus
pigeonhole: a smooth part of size `e^{δa}` gives one prime carrying `δa/|S|`.  Note what is *not*
claimed: nothing about the rough part of `mₐ`, which is where all of its size lives. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "BCZ03", group "bugeaud_10_13"]
theorem smoothPart_finite (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    {a : ℕ | δ * (a : ℝ) ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p}.Finite := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · refine Set.Finite.subset (Set.finite_le_nat 0) ?_
    intro a ha
    simp only [Set.mem_ofPred_eq, Finset.sum_empty] at ha
    have : (a : ℝ) ≤ 0 := by nlinarith [ha, hδ]
    have : a = 0 := by exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le a)
    simp [this]
  · have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    refine Set.Finite.subset
      (Set.Finite.biUnion S.finite_toSet
        (fun p hp => prime_valuation_finite (hS p hp) (δ := δ / S.card) (by positivity))) ?_
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    have hsum : ∑ _p ∈ S, δ / (S.card : ℝ) * (a : ℝ) ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (S.card : ℝ) * (δ / (S.card : ℝ) * (a : ℝ)) = δ * (a : ℝ) := by
            field_simp
        _ ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p := ha
    obtain ⟨p, hpS, hp⟩ := Finset.exists_le_of_sum_le hne hsum
    exact Set.mem_biUnion hpS hp

/-- **`∑_{p ∈ S} v_p(mₐ)·log p = o(a)`** — `smoothPart_finite` in `IsLittleO` form. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem smoothPart_isLittleO (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (fun a : ℕ => ∑ p ∈ S, (vAt p a : ℝ) * Real.log p) =o[Filter.atTop] (fun a : ℕ => (a : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hfin := smoothPart_finite S hS (δ := c) hc
  have hmem : {a : ℕ | c * (a : ℝ) ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p}ᶜ ∈
      Filter.atTop (α := ℕ) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hfin.compl_mem_cofinite
  filter_upwards [hmem] with a ha
  have hnot : ¬ (c * (a : ℝ) ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p) := ha
  have hnn : (0 : ℝ) ≤ ∑ p ∈ S, (vAt p a : ℝ) * Real.log p := by
    refine Finset.sum_nonneg fun p hp => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
  rw [Real.norm_natCast, Real.norm_of_nonneg hnn]
  linarith [not_le.mp hnot]

/-! ### The free coupling at the place `3`

`3` is the numerator's prime, so whatever `3`-adic content `mₐ` has is forced into the residue.
This is an elementary weighted cap of exactly the shape item B2 has to postulate a rate for — and
it is the reason the two places behave differently: `v₂(mₐ)` is invisible to `kₐ`. -/

/-- **`3^{v₃(mₐ)} ∣ kₐ`** — because `3^{v₃} ∣ mₐ2ᵃ` and `3^{v₃} ∣ 3ᵃ` (`v₃(mₐ) ≤ a`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_dvd_resid (a : ℕ) : (3 : ℤ) ^ vAt 3 a ∣ resid 3 2 a := by
  have h1 : (3 : ℤ) ^ vAt 3 a ∣ (3 : ℤ) ^ a := pow_dvd_pow _ (vAt_three_le a)
  have h2 : (3 : ℤ) ^ vAt 3 a ∣ Mnum 3 2 a * 2 ^ a := Dvd.dvd.mul_right (pow_vAt_dvd 3 a) _
  have : resid 3 2 a = (3 : ℤ) ^ a - Mnum 3 2 a * 2 ^ a := by
    rw [resid]; push_cast; ring
  rw [this]
  exact dvd_sub h1 h2

/-- **`3^{v₃(mₐ)} ≤ |kₐ|`** for `a ≥ 1`: the residue is nonzero, so it is at least its divisor. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_pow_le_abs_resid {a : ℕ} (ha : 1 ≤ a) : (3 : ℤ) ^ vAt 3 a ≤ |resid 3 2 a| :=
  Int.le_of_dvd (abs_pos.mpr (resid_ne_zero ha)) (by simpa using three_dvd_resid a)

/-- **The unconditional weighted cap at the place `3`**: if the fibre over `a` reaches `a + d`
(the linkage `3ᵈmₐ = 2ᵈm_{a+d}` with a failure at `a + d`), then

`2ᵈ · 3^{v₃(mₐ)} < (3/2)ᵃ`.

Compare `BB13.weighted_fibre_cap`, which is the same shape at the place `2` and needs a weighted
rate as a hypothesis; here the weight is free, and idle — `v₃(mₐ)` is `O(1)`-sized. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_fibre_cap {a d : ℕ} (ha : 1 ≤ a) (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    (2 : ℝ) ^ d * (3 : ℝ) ^ vAt 3 a < (3 / 2 : ℝ) ^ a := by
  have hq := link_quality 3 2 (3 / 4) hfail hlink
  -- `3ᵈ·|kₐ| < (3/2)^{a+d}`, i.e. `2ᵈ·|kₐ| < (3/2)ᵃ`
  have hcast : ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ (a + d) = (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
    rw [← pow_add]; norm_num
  have h3 : ((3 : ℕ) : ℝ) ^ d = (3 : ℝ) ^ d := by norm_num
  rw [hcast, h3] at hq
  have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hres : (3 : ℝ) ^ vAt 3 a ≤ |((resid 3 2 a : ℤ) : ℝ)| := by
    have := three_pow_le_abs_resid ha
    have hc : ((3 : ℤ) ^ vAt 3 a : ℝ) ≤ ((|resid 3 2 a| : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at hc
    exact_mod_cast hc
  have hstep : (2 : ℝ) ^ d * (3 : ℝ) ^ vAt 3 a ≤ (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| :=
    mul_le_mul_of_nonneg_left hres h2d.le
  refine lt_of_le_of_lt hstep ?_
  -- from `3ᵈ|kₐ| < (3/2)ᵃ(3/2)ᵈ` divide by `(3/2)ᵈ`
  have h32d : (0 : ℝ) < (3 / 2 : ℝ) ^ d := by positivity
  have hpow : (2 : ℝ) ^ d * (3 / 2 : ℝ) ^ d = (3 : ℝ) ^ d := by
    rw [← mul_pow]; norm_num
  have hmul : ((2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)|) * (3 / 2 : ℝ) ^ d
      < (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
    calc ((2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)|) * (3 / 2 : ℝ) ^ d
        = ((2 : ℝ) ^ d * (3 / 2 : ℝ) ^ d) * |((resid 3 2 a : ℤ) : ℝ)| := by ring
      _ = (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by rw [hpow]
      _ < (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := hq
  exact lt_of_mul_lt_mul_right hmul h32d.le

/-! ### The cross-line eliminant

Two frame relations `3ᵃ − kₐ = mₐ2ᵃ`, `3ᵇ − k_b = m_b2ᵇ` sharing a common divisor `g` of the two
numerators.  Eliminating `g` is a two-line computation, and the result is the gap principle. -/

/-- **The elimination identity** (exact, pure ring).  For `mₐ = g·ν`, `m_{a+d} = g·ν'`:

`3ᵃ·(ν'2ᵈ − ν3ᵈ) = ν'2ᵈ·kₐ − ν·k_{a+d}`.

The common divisor `g` cancels; what survives on the left is a *two-term* S-unit expression, which
is why the Subspace theorem has nothing to act on here (contrast the three-term frame relation
itself). -/
@[category research solved, AMS 11, ref "Bug12" "BE08", group "bugeaud_10_13"]
theorem cross_identity {a d : ℕ} {g ν ν' : ℤ} (hν : Mnum 3 2 a = g * ν)
    (hν' : Mnum 3 2 (a + d) = g * ν') :
    (3 : ℤ) ^ a * (ν' * 2 ^ d - ν * 3 ^ d)
      = ν' * 2 ^ d * resid 3 2 a - ν * resid 3 2 (a + d) := by
  simp only [resid, hν, hν']
  push_cast
  ring

/-- **The eliminant vanishes exactly on a line**: `ν'2ᵈ = ν3ᵈ ↔ 3ᵈmₐ = 2ᵈm_{a+d}`, the linkage
relation of `BB13.linkage` (equivalently `BB13.SameTower a (a+d)`).  So the cross-line elimination
carries information *only* off a line — the report's "dead within a line", made exact and now known
also to be the only degeneracy. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem cross_eq_zero_iff {a d : ℕ} {g ν ν' : ℤ} (hg : g ≠ 0) (hν : Mnum 3 2 a = g * ν)
    (hν' : Mnum 3 2 (a + d) = g * ν') :
    ν' * 2 ^ d - ν * 3 ^ d = 0 ↔ (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d) := by
  rw [sub_eq_zero, hν, hν']
  constructor
  · intro h; linear_combination (-g) * h
  · intro h
    have hgc : g * (ν' * 2 ^ d) = g * (ν * 3 ^ d) := by linear_combination -h
    exact mul_left_cancel₀ hg hgc

/-- **The cross-line gap principle.**  If `a` and `a + d` are failures, `g` is a common divisor of
their numerators (`mₐ = gν`, `m_{a+d} = gν'`, `g > 0`) and the pair is *not* on one line, then

`g·2ᵃ < m_{a+d}·2ᵈ + mₐ·(3/2)ᵈ`.

The only Diophantine input is `|Δ| ≥ 1` for the nonzero integer eliminant. -/
@[category research solved, AMS 11, ref "Bug12" "BE08", group "bugeaud_10_13"]
theorem cross_gap {a d : ℕ} {g ν ν' : ℤ} (hg : 0 < g) (hν : Mnum 3 2 a = g * ν)
    (hν' : Mnum 3 2 (a + d) = g * ν') (hfa : IsFailure 3 2 (3 / 4) a)
    (hfb : IsFailure 3 2 (3 / 4) (a + d)) (hne : ν' * 2 ^ d - ν * 3 ^ d ≠ 0) :
    (g : ℝ) * 2 ^ a < (Mnum 3 2 (a + d) : ℝ) * 2 ^ d + (Mnum 3 2 a : ℝ) * (3 / 2 : ℝ) ^ d := by
  -- `ν, ν' > 0`
  have hνpos : 0 < ν := by
    rcases lt_or_ge 0 ν with h | h
    · exact h
    · have hle : Mnum 3 2 a ≤ 0 := by rw [hν]; nlinarith [hg, h]
      linarith [Mnum_pos a]
  have hν'pos : 0 < ν' := by
    rcases lt_or_ge 0 ν' with h | h
    · exact h
    · have hle : Mnum 3 2 (a + d) ≤ 0 := by rw [hν']; nlinarith [hg, h]
      linarith [Mnum_pos (a + d)]
  -- `|Δ| ≥ 1`
  have hΔ : (1 : ℤ) ≤ |ν' * 2 ^ d - ν * 3 ^ d| := Int.one_le_abs (by omega)
  have hΔR : (1 : ℝ) ≤ |((ν' * 2 ^ d - ν * 3 ^ d : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hΔ
  -- the identity, in `ℝ`
  have hid : (3 : ℝ) ^ a * ((ν' : ℝ) * 2 ^ d - (ν : ℝ) * 3 ^ d)
      = (ν' : ℝ) * 2 ^ d * ((resid 3 2 a : ℤ) : ℝ) - (ν : ℝ) * ((resid 3 2 (a + d) : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (cross_identity hν hν')
    push_cast at this
    exact this
  have h3a : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hlow : (3 : ℝ) ^ a ≤ |(3 : ℝ) ^ a * ((ν' : ℝ) * 2 ^ d - (ν : ℝ) * 3 ^ d)| := by
    rw [abs_mul, abs_of_pos h3a]
    have : |((ν' : ℝ) * 2 ^ d - (ν : ℝ) * 3 ^ d)| = |((ν' * 2 ^ d - ν * 3 ^ d : ℤ) : ℝ)| := by
      push_cast; ring_nf
    rw [this]
    nlinarith [hΔR, h3a]
  -- the upper bound
  have hka := abs_resid_lt_of_isFailure hfa
  have hkb := abs_resid_lt_of_isFailure hfb
  have hνR : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hνpos
  have hν'R : (0 : ℝ) < (ν' : ℝ) := by exact_mod_cast hν'pos
  have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hup : |(ν' : ℝ) * 2 ^ d * ((resid 3 2 a : ℤ) : ℝ) - (ν : ℝ) * ((resid 3 2 (a + d) : ℤ) : ℝ)|
      < (ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a + (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d) := by
    calc |(ν' : ℝ) * 2 ^ d * ((resid 3 2 a : ℤ) : ℝ) - (ν : ℝ) * ((resid 3 2 (a + d) : ℤ) : ℝ)|
        ≤ |(ν' : ℝ) * 2 ^ d * ((resid 3 2 a : ℤ) : ℝ)|
          + |(ν : ℝ) * ((resid 3 2 (a + d) : ℤ) : ℝ)| := abs_sub _ _
      _ = (ν' : ℝ) * 2 ^ d * |((resid 3 2 a : ℤ) : ℝ)|
          + (ν : ℝ) * |((resid 3 2 (a + d) : ℤ) : ℝ)| := by
            simp only [abs_mul, abs_of_pos hνR, abs_of_pos hν'R, abs_of_pos h2d]
      _ < (ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a + (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d) := by
            have h1 : (ν' : ℝ) * 2 ^ d * |((resid 3 2 a : ℤ) : ℝ)|
                < (ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a :=
              mul_lt_mul_of_pos_left hka (by positivity)
            have h2 : (ν : ℝ) * |((resid 3 2 (a + d) : ℤ) : ℝ)|
                < (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d) := mul_lt_mul_of_pos_left hkb hνR
            linarith
  -- combine, then multiply by `g` and cancel `(3/2)ᵃ`
  have hcomb : (3 : ℝ) ^ a < (ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a + (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d) := by
    rw [hid] at hlow
    linarith [hlow, hup]
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
  have hma : (Mnum 3 2 a : ℝ) = (g : ℝ) * (ν : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hν
  have hmb : (Mnum 3 2 (a + d) : ℝ) = (g : ℝ) * (ν' : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hν'
  have hsplit : (3 : ℝ) ^ a = (2 : ℝ) ^ a * (3 / 2 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have hpowadd : (3 / 2 : ℝ) ^ (a + d) = (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by rw [pow_add]
  rw [hma, hmb]
  have hscaled : (g : ℝ) * (3 : ℝ) ^ a
      < (g : ℝ) * ((ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a + (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d)) :=
    mul_lt_mul_of_pos_left hcomb hgR
  have hfin : ((g : ℝ) * 2 ^ a) * (3 / 2 : ℝ) ^ a
      < ((g : ℝ) * (ν' : ℝ) * 2 ^ d + (g : ℝ) * (ν : ℝ) * (3 / 2 : ℝ) ^ d) * (3 / 2 : ℝ) ^ a := by
    calc ((g : ℝ) * 2 ^ a) * (3 / 2 : ℝ) ^ a = (g : ℝ) * ((2 : ℝ) ^ a * (3 / 2 : ℝ) ^ a) := by ring
      _ = (g : ℝ) * (3 : ℝ) ^ a := by rw [← hsplit]
      _ < (g : ℝ) * ((ν' : ℝ) * 2 ^ d * (3 / 2 : ℝ) ^ a + (ν : ℝ) * (3 / 2 : ℝ) ^ (a + d)) :=
          hscaled
      _ = ((g : ℝ) * (ν' : ℝ) * 2 ^ d + (g : ℝ) * (ν : ℝ) * (3 / 2 : ℝ) ^ d)
            * (3 / 2 : ℝ) ^ a := by rw [hpowadd]; ring
  exact lt_of_mul_lt_mul_right hfin h32.le

/-- **The reach of the cross-line gap principle**: `g·(4/3)ᵃ < 4·3ᵈ`.  Off a line, a common
divisor `g` of the two numerators pushes the gap threshold from `ε*a` up to `ε*a + log₃ g`
(`ε* = log(4/3)/log 3`, `BB13.epsStar`) — and no further. -/
@[category research solved, AMS 11, ref "Bug12" "BE08", group "bugeaud_10_13"]
theorem cross_gap_reach {a d : ℕ} {g ν ν' : ℤ} (hg : 0 < g) (hν : Mnum 3 2 a = g * ν)
    (hν' : Mnum 3 2 (a + d) = g * ν') (hfa : IsFailure 3 2 (3 / 4) a)
    (hfb : IsFailure 3 2 (3 / 4) (a + d)) (hne : ν' * 2 ^ d - ν * 3 ^ d ≠ 0) :
    (g : ℝ) * (4 / 3 : ℝ) ^ a < 4 * 3 ^ d := by
  have h := cross_gap hg hν hν' hfa hfb hne
  have hma := Mnum_le_two_mul a
  have hmb := Mnum_le_two_mul (a + d)
  have h32a : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
  have h32d : (0 : ℝ) < (3 / 2 : ℝ) ^ d := by positivity
  have h2d : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hpowadd : (3 / 2 : ℝ) ^ (a + d) = (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by rw [pow_add]
  have h3d : (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = (3 : ℝ) ^ d := by
    rw [show (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = ((3 / 2 : ℝ) * 2) ^ d by rw [mul_pow]]
    norm_num
  have hle : (3 / 2 : ℝ) ^ d ≤ (3 : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) d
  -- `g2ᵃ < 4(3/2)ᵃ3ᵈ`
  have hkey : (g : ℝ) * 2 ^ a < 4 * (3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d := by
    have hb : (Mnum 3 2 (a + d) : ℝ) * 2 ^ d ≤ 2 * ((3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d) := by
      rw [hpowadd] at hmb
      calc (Mnum 3 2 (a + d) : ℝ) * 2 ^ d
          ≤ (2 * ((3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d)) * 2 ^ d :=
            mul_le_mul_of_nonneg_right hmb h2d.le
        _ = 2 * ((3 / 2 : ℝ) ^ a * ((3 / 2 : ℝ) ^ d * 2 ^ d)) := by ring
        _ = 2 * ((3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d) := by rw [h3d]
    have ha' : (Mnum 3 2 a : ℝ) * (3 / 2 : ℝ) ^ d ≤ 2 * ((3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d) := by
      calc (Mnum 3 2 a : ℝ) * (3 / 2 : ℝ) ^ d ≤ (2 * (3 / 2 : ℝ) ^ a) * (3 / 2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right hma h32d.le
        _ ≤ (2 * (3 / 2 : ℝ) ^ a) * (3 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 2 * ((3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d) := by ring
    linarith
  have hsplit : (2 : ℝ) ^ a = (4 / 3 : ℝ) ^ a * (3 / 2 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have hfin : ((g : ℝ) * (4 / 3 : ℝ) ^ a) * (3 / 2 : ℝ) ^ a
      < (4 * (3 : ℝ) ^ d) * (3 / 2 : ℝ) ^ a := by
    calc ((g : ℝ) * (4 / 3 : ℝ) ^ a) * (3 / 2 : ℝ) ^ a
        = (g : ℝ) * ((4 / 3 : ℝ) ^ a * (3 / 2 : ℝ) ^ a) := by ring
      _ = (g : ℝ) * (2 : ℝ) ^ a := by rw [← hsplit]
      _ < 4 * (3 / 2 : ℝ) ^ a * (3 : ℝ) ^ d := hkey
      _ = (4 * (3 : ℝ) ^ d) * (3 / 2 : ℝ) ^ a := by ring
  exact lt_of_mul_lt_mul_right hfin h32a.le

/-- **The classical gap principle, re-derived from the eliminant** (`g = ν = ν' = 1`): two
failures `a`, `a + d` off a line satisfy `(4/3)ᵃ < 4·3ᵈ`, i.e. `d > ε*·a − log₃4`.  Compare
`BB13.linkage`, which is the same statement in contrapositive form: this is what the report's
proposed cross-line Subspace elimination actually amounts to. -/
@[category research solved, AMS 11, ref "Bug12" "BE08", group "bugeaud_10_13"]
theorem gap_principle_of_cross {a d : ℕ} (hfa : IsFailure 3 2 (3 / 4) a)
    (hfb : IsFailure 3 2 (3 / 4) (a + d))
    (hne : Mnum 3 2 (a + d) * 2 ^ d - Mnum 3 2 a * 3 ^ d ≠ 0) :
    (4 / 3 : ℝ) ^ a < 4 * 3 ^ d := by
  have h := cross_gap_reach (g := 1) (ν := Mnum 3 2 a) (ν' := Mnum 3 2 (a + d)) zero_lt_one
    (by ring) (by ring) hfa hfb (by simpa using hne)
  simpa using h

/-- **Fixed-`μ` rigidity.**  If `mₐ` and `m_{a+d}` have the same odd part — more generally, if
they share a divisor `g` with `mₐ = g·2ˢ` and `m_{a+d} = g·2^{s'}` — and `d ≥ 1`, then the pair is
automatically off a line and

`2ᵃ < 8·2ˢ·3ᵈ`.

With `s = v₂(mₐ) = o(a)` (`BB13.valuation_arm_finite`) this separates two indices with the same
odd part by `d ≥ (log 2/log 3 − o(1))·a = (0.63 − o(1))·a`: the multiplicative companion of the
fixed-`k` rigidity of report §4 (CB1), where the separation is `2ᵃ ∣ a' − a`.  Empirically the
only equal-odd-part pairs with `a < b ≤ 700` are `(1,2)`, `(1,5)`, `(2,5)`, where `mₐ` is a power
of two and `μ = 1` (`BB13/b3_smooth.py` block [E]). -/
@[category research solved, AMS 11, ref "Bug12" "BE08", group "bugeaud_10_13"]
theorem matched_separation {a d s s' : ℕ} {g : ℤ} (hd : 1 ≤ d) (hg : 0 < g)
    (hν : Mnum 3 2 a = g * 2 ^ s) (hν' : Mnum 3 2 (a + d) = g * 2 ^ s')
    (hfa : IsFailure 3 2 (3 / 4) a) (hfb : IsFailure 3 2 (3 / 4) (a + d)) :
    (2 : ℝ) ^ a < 8 * 2 ^ s * 3 ^ d := by
  -- off a line: `2^{s'+d} = 2ˢ3ᵈ` would force `3ᵈ ∣ 2^{s'+d}`
  have hne : (2 : ℤ) ^ s' * 2 ^ d - 2 ^ s * 3 ^ d ≠ 0 := by
    intro h
    have heq : (2 : ℤ) ^ (s' + d) = 2 ^ s * 3 ^ d := by
      rw [pow_add]; linarith [h]
    have h3 : (3 : ℤ) ∣ 2 ^ (s' + d) := by
      rw [heq]
      exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
    have hno : ¬ ((3 : ℤ) ∣ 2 ^ (s' + d)) := by
      intro hdvd
      have hp3 : Prime (3 : ℤ) := by norm_num
      have := hp3.dvd_of_dvd_pow hdvd
      norm_num at this
    exact hno h3
  have h := cross_gap_reach hg hν hν' hfa hfb hne
  have hlow := half_le_Mnum a
  have hmg : (Mnum 3 2 a : ℝ) = (g : ℝ) * (2 : ℝ) ^ s := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hν
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
  have hgl : (3 / 2 : ℝ) ^ a / 2 ≤ (g : ℝ) * (2 : ℝ) ^ s := by rw [← hmg]; exact hlow
  have hsplit : (2 : ℝ) ^ a = (4 / 3 : ℝ) ^ a * (3 / 2 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have h43 : (0 : ℝ) < (4 / 3 : ℝ) ^ a := by positivity
  have step1 : (2 : ℝ) ^ a ≤ (4 / 3 : ℝ) ^ a * (2 * ((g : ℝ) * (2 : ℝ) ^ s)) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (by linarith [hgl]) h43.le
  have step2 : (4 / 3 : ℝ) ^ a * (2 * ((g : ℝ) * (2 : ℝ) ^ s))
      = 2 * (2 : ℝ) ^ s * ((g : ℝ) * (4 / 3 : ℝ) ^ a) := by ring
  have step3 : 2 * (2 : ℝ) ^ s * ((g : ℝ) * (4 / 3 : ℝ) ^ a)
      < 2 * (2 : ℝ) ^ s * (4 * (3 : ℝ) ^ d) :=
    mul_lt_mul_of_pos_left h (by positivity)
  linarith [step1, step2, step3]

/-! ### The effective corner: a fully smooth numerator collapses to two terms -/

/-- **A `{2,3}`-smooth numerator gives a two-term relation, hence an effective bound.**  If
`mₐ = 2^w·3^t` with `t ≤ a`, then `kₐ = 3^t(3^{a−t} − 2^{a+w})` and a failure at `a` reads

`|3^{a−t} − 2^{a+w}| < 3^{a−t}/2ᵃ`.

Any effective rate for the two-term form — `hrate`, satisfied by `c^{A}2^{A} ≤ |3^A − 2^B|` with
[Zud07]'s `c = 0.5803` — then bounds `a` against `a − t`:

`2ᵃ < (3/(2c))^{a−t}`,  i.e.  `t ≤ (1 − log 2/log(3/(2c)))·a = 0.2701·a` for `c = 0.5803`.

This is the whole of "the smooth branch is effective": it needs `mₐ` *fully* smooth, since a rough
cofactor is a coefficient of unbounded height that no monomial scheme sees.  `mₐ` is `{2,3}`-smooth
exactly for `a ∈ {1,2,3,5}` in `a ≤ 20000` (`BB13/b3_smooth.py` block [B]). -/
@[category research solved, AMS 11, ref "Bug12" "Zud07", group "bugeaud_10_13"]
theorem smooth_effective {a w t : ℕ} {c : ℝ} (hc : 0 < c) (ht : t ≤ a)
    (hm : Mnum 3 2 a = 2 ^ w * 3 ^ t) (hfa : IsFailure 3 2 (3 / 4) a)
    (hrate : c ^ (a - t) * 2 ^ (a - t) ≤ |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)|) :
    (2 : ℝ) ^ a < (3 / (2 * c)) ^ (a - t) := by
  -- `kₐ = 3^t(3^{a−t} − 2^{a+w})`
  have hka : ((resid 3 2 a : ℤ) : ℝ) = (3 : ℝ) ^ t * ((3 : ℝ) ^ (a - t) - 2 ^ (a + w)) := by
    have hsplit3 : (3 : ℝ) ^ t * (3 : ℝ) ^ (a - t) = (3 : ℝ) ^ a := by
      rw [← pow_add, Nat.add_sub_cancel' ht]
    have hsplit2 : (3 : ℝ) ^ t * (2 : ℝ) ^ (a + w) = ((2 : ℝ) ^ w * 3 ^ t) * 2 ^ a := by
      rw [pow_add]; ring
    have hres : ((resid 3 2 a : ℤ) : ℝ) = (3 : ℝ) ^ a - (Mnum 3 2 a : ℝ) * 2 ^ a := by
      rw [resid]; push_cast; ring
    have hmR : (Mnum 3 2 a : ℝ) = (2 : ℝ) ^ w * 3 ^ t := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hm
    rw [hres, hmR]
    nlinarith [hsplit3, hsplit2]
  have hfail := abs_resid_lt_of_isFailure hfa
  rw [hka, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3:ℝ) ^ t)] at hfail
  -- `3^t|3^{a−t} − 2^{a+w}| < (3/2)ᵃ = 3^t·3^{a−t}/2ᵃ`
  have h3t : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hsplit3 : (3 : ℝ) ^ t * (3 : ℝ) ^ (a - t) = (3 : ℝ) ^ a := by
    rw [← pow_add, Nat.add_sub_cancel' ht]
  have h32a : (3 / 2 : ℝ) ^ a * (2 : ℝ) ^ a = (3 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have hupper : |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)| * (2 : ℝ) ^ a < (3 : ℝ) ^ (a - t) := by
    have hmul : (3 : ℝ) ^ t * (|(3 : ℝ) ^ (a - t) - 2 ^ (a + w)| * (2 : ℝ) ^ a)
        < (3 : ℝ) ^ t * (3 : ℝ) ^ (a - t) := by
      calc (3 : ℝ) ^ t * (|(3 : ℝ) ^ (a - t) - 2 ^ (a + w)| * (2 : ℝ) ^ a)
          = ((3 : ℝ) ^ t * |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)|) * (2 : ℝ) ^ a := by ring
        _ < (3 / 2 : ℝ) ^ a * (2 : ℝ) ^ a := mul_lt_mul_of_pos_right hfail h2a
        _ = (3 : ℝ) ^ a := h32a
        _ = (3 : ℝ) ^ t * (3 : ℝ) ^ (a - t) := hsplit3.symm
    exact lt_of_mul_lt_mul_left hmul h3t.le
  -- combine with the rate
  have hcpow : (0 : ℝ) < c ^ (a - t) := by positivity
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (a - t) := by positivity
  have hstep : (2 : ℝ) ^ a * (c ^ (a - t) * 2 ^ (a - t))
      ≤ (2 : ℝ) ^ a * |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)| :=
    mul_le_mul_of_nonneg_left hrate h2a.le
  have hcomm : (2 : ℝ) ^ a * |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)|
      = |(3 : ℝ) ^ (a - t) - 2 ^ (a + w)| * (2 : ℝ) ^ a := by ring
  have hkey : (2 : ℝ) ^ a * (c ^ (a - t) * 2 ^ (a - t)) < (3 : ℝ) ^ (a - t) := by
    linarith [hstep, hupper, hcomm]
  have hcne : (c : ℝ) ^ (a - t) ≠ 0 := ne_of_gt hcpow
  have h2ne : (2 : ℝ) ^ (a - t) ≠ 0 := ne_of_gt h2pow
  have hprod : (3 / (2 * c)) ^ (a - t) * (c ^ (a - t) * 2 ^ (a - t)) = (3 : ℝ) ^ (a - t) := by
    rw [div_pow, mul_pow]
    field_simp
  rw [← hprod] at hkey
  exact lt_of_mul_lt_mul_right hkey (by positivity)

end BB13
