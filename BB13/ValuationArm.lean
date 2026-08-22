/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.SpanStrata
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# The `2`-adic arm is `o(a)`: `v₂(round((3/2)ᵃ)) = o(a)`, unconditionally (B1)

Item **B1** of `plans/report3-BB13.html` (§3, §9 item 1): the first new unconditional row of the
Problem 10.13 table since [Zud07], and the answer to the report's question Q2.1 — *which of the
two arms of the per-line problem is soft?*

## The statement

Write `mₐ = round((3/2)ᵃ)` (`BB13.Mnum 3 2 a`) and `v₂` for the `2`-adic valuation.  Then

> for every `ε > 0` the set `A_ε = {a : v₂(mₐ) ≥ ε·a}` is **finite** — over all of `ℕ`, with no
> exception condition — hence `v₂(mₐ) = o(a)`.

`valuation_arm_finite` is the finiteness, `vTwo_isLittleO` the `o(a)` form.  The result is
**ineffective**: it is the qualitative shadow of a quantitative line count, and effectivizing any
single `ε` would already be an effective Ridout instance.

## The proof, in three lines

The frame point of `a` is `(x, y) = (mₐ2ᵃ, 3ᵃ)` — the point of `BB13/LineCover.lean`, but now
attached to *every* `a`, not only to a failure.  With `ξ = 1`, `S₁ = {2}`, `S₂ = {3}`:

* `|1 − x/y| = |kₐ|/3ᵃ ≤ 2ᵃ⁻¹/3ᵃ ≤ (2/3)ᵃ = y^{−(1−θ)}` — the *nearest-integer* bound
  `|kₐ| ≤ 2ᵃ⁻¹` only, no failure hypothesis (`frame_archimedean_trivial`);
* `|x|₂ = 2^{−(a+v₂(mₐ))} ≤ 2^{−a(1+ε)} = y^{−θ(1+ε)}` — this is where `a ∈ A_ε` is spent
  (`frame_two_adic_of_vTwo`);
* `|y|₃ = 3^{−a} = y^{−1}` (`BB13.frame_three_adic`).

The budget of [BE08] (5.10) is

`(1 − θ) + θ(1 + ε) + 1 = 2 + θε`  (`budget_valuation_arm`),

so Cor. 5.2 applies at the shifted exponent `θε > 0` and confines all high `a ∈ A_ε` to at most
`K(θε)` lines (`valuation_arm_line_cover`).  Finiteness follows because a *single* line carries
only finitely many `a`: the slope `x/y` of the frame point of `a` differs from `1` by at most
`(2/3)ᵃ` and is never equal to `1` (`linePoint_ne_one`), so a fixed slope pins `a` to a bounded
range (`linePointFibre_finite`).  That step plays the role of the elementary confinement of
`BB13/LineTower.lean`, but is proved from the archimedean row rather than from the gap principle,
which is what lets it dispense with the failure hypothesis.

Compare `BB13/LineCover.lean`, where the *failure* pays `θ` at the infinite place and the frame
point pays only the free `θ` at `2`.  Here the trade is reversed: the archimedean side is charged
the trivial `1 − θ = 0.36907…` that every `a` supplies for free, and the whole surplus is taken
`2`-adically.  Both frames spend exactly the same total, and both are exact.

## What it buys, and what it does not

* **New table row.** `o(a)` beats Zudilin's `0.371a + O(1)` in rate and loses in effectivity;
  both are worth having.  It does **not** feed Theorem B of [paper-BB13], which needs `O(1)`.
* **The corridor.** An unbounded fibre sequence must have `v₂(mₐ) ∈ ω(1) ∩ o(a)`: the `v` arm can
  no longer carry a positive proportion of `a`.
* **Every fibre is an interval of length `o(a)`, unconditionally.**  A relation-tower over `a` has
  span at most `v₂(mₐ)` (`sameTower_span_le_vTwo`), so `lineFibre_card_le_vTwo` improves the
  elementary `(lineFibre r).ncard ≤ a` of `BB13.sameTower_card_le_of_min` to `≤ v₂(mₐ) + 1`, and
  `tall_towerBases_finite` says: for every `γ > 0` only finitely many `a` carry a tower of span
  `≥ γ·a`.  That is the unconditional shadow of the span-stratified counts of
  `BB13/SpanStrata.lean`, whose hypothesis `γ·a ≤ b − a` is *exactly* an `A_γ` membership
  (`tall_tower_le_vTwo`) — the "wiring to Theorem D" of the report's §3 remark 3.
* It is **not** a step towards `O(1)`: the route to Problem 2 must be structurally different
  (report §3 remark 1, and the walls of §6.12).

## Back-port

The proof uses nothing about `(3, 2)` beyond coprimality: for coprime `p > q ≥ 2` the same budget
`(1 − θ_{p,q}, θ_{p,q}(1 + ε), 1)` with `θ_{p,q} = log q/log p` gives
`v_q(round((p/q)ᵃ)) = o(a)`.  Only the headline pair is formalized here; the general frame is
available in `BB13/MahlerFrame.lean`.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover` — the same single cited axiom as the rest of
the `BB13/` root.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Cor. 5.2, `CITED/BugeaudEvertseRidout.lean`.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  **193**, 2012 — Problem 10.13.
* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124 — the ineffective finiteness of the exception set.
* [Zud07] W. Zudilin, *A new lower bound for ‖(3/2)ᵏ‖*, J. Théor. Nombres Bordeaux **19** (2007),
  311–323 — the effective row this one beats in rate.
* `plans/report3-BB13.html` §3 (the theorem, verified), §6 B1 (the strategy item), §9 item 1 (the
  Lean statement).
-/

namespace BB13

open scoped Real

/-! ### The `2`-adic valuation of the nearest-integer numerator -/

/-- **`v₂(mₐ)`** — the `2`-adic valuation of `mₐ = round((3/2)ᵃ)`, the `v` arm of the per-line
problem.  The fibre of the line over an exception `a` is the interval
`{a + d : 0 ≤ d ≤ min(v₂(mₐ), D(a))}`, so `vTwo` is one of the two quantities Problem 2 asks to
bound. -/
noncomputable def vTwo (a : ℕ) : ℕ := padicValInt 2 (Mnum 3 2 a)

/-- `mₐ = round((3/2)ᵃ) ≥ 1`: the nearest integer to a real `≥ 1` is positive.  Needed to know
that `vTwo` is a genuine valuation (`vTwo` of `0` would be `0` by convention). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem Mnum_pos (a : ℕ) : 0 < Mnum 3 2 a := by
  have h1 : (1 : ℝ) ≤ (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a :=
    one_le_pow₀ (by norm_num)
  have h2 : (1 : ℤ) ≤ ⌊(((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ a + 1 / 2⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  rw [Mnum, round_eq]
  omega

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem Mnum_ne_zero (a : ℕ) : Mnum 3 2 a ≠ 0 := (Mnum_pos a).ne'

/-- `2^{v₂(mₐ)} ∣ mₐ`: the defining property of `vTwo`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_vTwo_dvd (a : ℕ) : (2 : ℤ) ^ vTwo a ∣ Mnum 3 2 a := by
  have h := padicValInt_dvd (p := 2) (Mnum 3 2 a)
  simpa [vTwo] using h

/-- `2ᴰ ∣ mₐ → D ≤ v₂(mₐ)`: the maximality of `vTwo`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem le_vTwo_of_dvd {a D : ℕ} (h : (2 : ℤ) ^ D ∣ Mnum 3 2 a) : D ≤ vTwo a := by
  have h' : ((2 : ℕ) : ℤ) ^ D ∣ Mnum 3 2 a := by simpa using h
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) D _).mp h' with h0 | hle
  · exact absurd h0 (Mnum_ne_zero a)
  · exact hle

/-- `vTwo` from the two dyadic tests, in the decidable `ℕ` form `mₐ = (2·3ᵃ + 2ᵃ)/2ᵃ⁺¹`
(`BB13.mNat`, `BB13.Mnum_eq_mNat`). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_dvd_Mnum_iff (a D : ℕ) : ((2 : ℤ) ^ D ∣ Mnum 3 2 a) ↔ 2 ^ D ∣ mNat a := by
  rw [Mnum_eq_mNat]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- `2ᴰ ∣ mₐ` and `2ᴰ⁺¹ ∤ mₐ` pin `v₂(mₐ) = D` — the exact-integer test the census runs on. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vTwo_eq_of_mNat {a D : ℕ} (h1 : 2 ^ D ∣ mNat a) (h2 : ¬ (2 ^ (D + 1) ∣ mNat a)) :
    vTwo a = D := by
  have hle : D ≤ vTwo a := le_vTwo_of_dvd ((two_pow_dvd_Mnum_iff a D).mpr h1)
  have hlt : vTwo a < D + 1 := by
    by_contra hcon
    exact h2 ((two_pow_dvd_Mnum_iff a (D + 1)).mp
      (dvd_trans (pow_dvd_pow 2 (not_lt.mp hcon)) (two_pow_vTwo_dvd a)))
  omega

/-- **The `v₂` column of the census**, kernel-checked: on the five exceptions
`𝓔 ∩ [1, 10⁶] = {1, 2, 3, 4, 7}` the valuations are `v₂(mₐ) = 1, 1, 0, 0, 0`.  Together with the
dyadic surpluses `D(a) = 0, 1, 0, 2, 0` (session-verified computation, not formalized) this is the
fibre data `min(v₂(mₐ), D(a)) = 0, 1, 0, 0, 0` of `plans/report3-BB13.html` §1.2: only `a = 2`
carries a companion, the pair `{2, 3}`. -/
@[category test, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem vTwo_census : vTwo 1 = 1 ∧ vTwo 2 = 1 ∧ vTwo 3 = 0 ∧ vTwo 4 = 0 ∧ vTwo 7 = 0 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
   vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
   vTwo_eq_of_mNat (by decide) (by decide)⟩

/-! ### The archimedean side, without a failure hypothesis

The trivial nearest-integer bound `|kₐ| ≤ 2ᵃ/2` buys the exponent `1 − θ` at the infinite place
for **every** `a`.  This is the one place where the frame of this file differs from
`BB13/LineCover.lean`. -/

/-- `θ < 1` — so `1 − θ` is a legitimate (nonnegative) exponent in the budget (5.10). -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem theta_lt_one : theta < 1 := by
  rw [theta, div_lt_one (Real.log_pos (by norm_num))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `(3ᵃ)^{−(1−θ)} = (2/3)ᵃ`: the exponent the trivial rounding bound pays for. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem rpow_neg_one_sub_theta (n : ℕ) : ((3 : ℝ) ^ n) ^ (-(1 - theta)) = (2 / 3 : ℝ) ^ n := by
  have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_natCast (2 / 3 : ℝ) n, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  congr 1
  have e1 : Real.log (2 / 3) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  rw [e1, theta]
  field_simp
  ring

/-- **The nearest-integer bound on the residue**: `|kₐ| ≤ 2ᵃ/2`, for every `a` and with no
Diophantine input — it is `‖(3/2)ᵃ‖ ≤ 1/2` multiplied by `2ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem abs_resid_le (n : ℕ) : |((resid 3 2 n : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n / 2 := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hd := distToNearestInt_eq_resid 3 2 n (by norm_num)
  have hhalf : distToNearestInt ((((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) ^ n) ≤ 1 / 2 :=
    abs_sub_round _
  rw [hd] at hhalf
  have hcast : (((2 : ℕ) : ℝ)) ^ n = (2 : ℝ) ^ n := by norm_num
  rw [hcast, div_le_iff₀ h2n] at hhalf
  linarith

/-- **The archimedean condition, unconditionally**: `|1 − x/y| ≤ (2/3)ᵃ = y^{−(1−θ)}` for the
frame point of *any* `a`.  Contrast `BB13.frame_archimedean`, which needs the failure hypothesis
and buys the larger exponent `θ`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_archimedean_trivial (a : ℕ) :
    |(1 : ℝ) - (frameX a : ℝ) / (frameY a : ℝ)| ≤ ((frameY a : ℤ) : ℝ) ^ (-(1 - theta)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  rw [frame_arch_eq, frameY_cast, rpow_neg_one_sub_theta]
  rw [div_le_iff₀ h3]
  have hpow : (2 / 3 : ℝ) ^ a * (3 : ℝ) ^ a = (2 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have := abs_resid_le a
  rw [hpow]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  linarith

/-! ### The `2`-adic side, charged with the whole surplus -/

/-- **The `2`-adic condition at the shifted exponent**: if `ε·a ≤ v₂(mₐ)` then
`|x|₂ ≤ (3ᵃ)^{−θ(1+ε)}` for the frame point `x = mₐ2ᵃ`.  The `2`-adic depth is
`a + v₂(mₐ) ≥ a(1 + ε)`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_two_adic_of_vTwo {a : ℕ} {ε : ℝ} (h : ε * (a : ℝ) ≤ (vTwo a : ℝ)) :
    ((padicNorm 2 ((frameX a : ℤ) : ℚ) : ℚ) : ℝ) ≤ ((3 : ℝ) ^ a) ^ (-(theta * (1 + ε))) :=
  le_trans (frame_two_adic_sharp (two_pow_vTwo_dvd a)) (two_pow_le_rpow_of_span h)

/-- **The budget identity of the `v`-arm frame**: `(1 − θ) + θ(1 + ε) + 1 = 2 + θε`.  The
Bugeaud–Evertse condition (5.10) is met at the shifted exponent `θε`, exactly.  (Compare
`BB13.theta_add_theta_add_one`, the failure frame's `θ + θ + 1 = 2 + ε*`.) -/
@[category research solved, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem budget_valuation_arm (ε : ℝ) : (1 - theta) + theta * (1 + ε) + 1 = 2 + theta * ε := by
  ring

/-! ### The line cover at the shifted exponent -/

/-- **The quantitative form** (report §3, remark 3): for every `ε > 0` there are a threshold `N`
and at most `K(θε)` slopes carrying the frame point of every `a ≥ N` with `v₂(mₐ) ≥ ε·a`.

This is [BE08] Cor. 5.2 run on the frame `(f_∞, f₂, f₃) = (1 − θ, θ(1 + ε), 1)`, whose budget is
`2 + θε` on the nose (`budget_valuation_arm`).  Note that no failure hypothesis appears: the
archimedean exponent `1 − θ` is paid by rounding alone.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem valuation_arm_line_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ (R : Finset ℚ) (N : ℕ), R.card ≤ BugeaudEvertse.lineBound (theta * ε) ∧
      ∀ a : ℕ, N ≤ a → ε * (a : ℝ) ≤ (vTwo a : ℝ) → linePoint a ∈ R := by
  have hth := theta_pos
  have hθε : 0 < theta * ε := mul_pos hth hε
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 (theta * ε) (1 - theta)
    (theta * (1 + ε)) 1 hθε (by linarith [theta_lt_one]) (by positivity) zero_le_one
    (budget_valuation_arm ε)
  -- the height threshold (5.12) is cleared from some `N` on, since `3ᵃ → ∞`
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
      ((2 : ℝ) ^ ((4 : ℝ) / (theta * ε)))) (by norm_num : (1 : ℝ) < 3)
  refine ⟨R, N, hcard, fun a haN hva => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
      ((2 : ℝ) ^ ((4 : ℝ) / (theta * ε))) < ((frameY a : ℤ) : ℝ) := by
    rw [frameY_cast]
    exact lt_of_lt_of_le hN (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) haN)
  refine hR (frameX a) (frameY a) (frameY_pos a) hheight ?_ ?_ (frame_three_adic a)
  · simpa using frame_archimedean_trivial a
  · rw [frameY_cast]; exact frame_two_adic_of_vTwo hva

/-! ### One line carries only finitely many indices -/

/-- The slope of the frame point of `a ≥ 1` is never `1`: `mₐ2ᵃ` is even and `3ᵃ` is odd. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linePoint_ne_one {a : ℕ} (ha : 1 ≤ a) : linePoint a ≠ 1 := by
  intro h
  have hy : (frameY a : ℚ) ≠ 0 := by
    have := frameY_pos a
    exact_mod_cast this.ne'
  have hxy : (frameX a : ℚ) = (frameY a : ℚ) := by
    rw [linePoint, div_eq_one_iff_eq hy] at h
    exact h
  have hxyZ : frameX a = frameY a := by exact_mod_cast hxy
  have : resid 3 2 a = 0 := by
    rw [resid]
    have hfx : frameX a = Mnum 3 2 a * 2 ^ a := rfl
    have hfy : frameY a = 3 ^ a := rfl
    rw [hfx, hfy] at hxyZ
    push_cast
    omega
  exact resid_ne_zero ha this

/-- The frame point's slope is within `(2/3)ᵃ` of `1` — `frame_archimedean_trivial` read in `ℚ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem abs_one_sub_linePoint_le (a : ℕ) :
    |(1 : ℝ) - ((linePoint a : ℚ) : ℝ)| ≤ (2 / 3 : ℝ) ^ a := by
  have hcast : ((linePoint a : ℚ) : ℝ) = (frameX a : ℝ) / (3 : ℝ) ^ a := by
    rw [linePoint, frameY]; push_cast; ring
  have h := frame_archimedean_trivial a
  rw [frameY_cast, rpow_neg_one_sub_theta] at h
  rw [hcast]
  exact h

/-- **A single slope pins the index to a bounded range** — the counterpart of
`BB13.lineFibre_finite`, proved from the archimedean row instead of the gap principle and so free
of the failure hypothesis.  Since `|1 − linePoint a| ≤ (2/3)ᵃ` and
`linePoint a ≠ 1`, a fixed slope `r` forces `(2/3)ᵃ ≥ |1 − r| > 0`, i.e. `a` bounded. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem linePointFibre_finite (r : ℚ) : {a : ℕ | 1 ≤ a ∧ linePoint a = r}.Finite := by
  rcases Set.eq_empty_or_nonempty {a : ℕ | 1 ≤ a ∧ linePoint a = r} with he | ⟨a₀, ha₀⟩
  · rw [he]; exact Set.finite_empty
  · have hr1 : (r : ℚ) ≠ 1 := ha₀.2 ▸ linePoint_ne_one ha₀.1
    have hc : 0 < |(1 : ℝ) - (r : ℝ)| := by
      refine abs_pos.mpr (sub_ne_zero.mpr ?_)
      intro h
      exact hr1 (by exact_mod_cast h.symm)
    obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (2 / 3 : ℝ) < 1)
    refine Set.Finite.subset (Set.finite_lt_nat n₀) ?_
    intro a ha
    by_contra hcon
    have hle : n₀ ≤ a := not_lt.mp hcon
    have h1 : |(1 : ℝ) - (r : ℝ)| ≤ (2 / 3 : ℝ) ^ a := by
      have := abs_one_sub_linePoint_le a
      rwa [ha.2] at this
    have h2 : (2 / 3 : ℝ) ^ a ≤ (2 / 3 : ℝ) ^ n₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    linarith

/-! ### The theorem -/

/-- **`v₂(mₐ) = o(a)`, unconditionally** ([BE08] Cor. 5.2 at the shifted budget; report §3).

For every `ε > 0` the set `A_ε = {a : ε·a ≤ v₂(round((3/2)ᵃ))}` is **finite** — over all of `ℕ`,
with no exception condition.

The proof is the frame of `valuation_arm_line_cover` plus `linePointFibre_finite`: the high `a`
of `A_ε` are spread over at most `K(θε)` slopes, and each slope carries finitely many `a` because
the frame point's slope approaches `1` at the rate `(2/3)ᵃ` without ever reaching it.

**Ineffective**, and necessarily so: an effective bound on `A_ε` for a single `ε` would be an
effective Ridout instance.  What the theorem settles is *structural* — the `v` arm of Problem 2 is
Subspace-soft, while the `D` arm is the fifty-year rate problem in a mask, so an unbounded fibre
sequence must have `v₂(mₐ)` in the corridor `ω(1) ∩ o(a)`.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Mah57", group "bugeaud_10_13"]
theorem valuation_arm_finite (ε : ℝ) (hε : 0 < ε) :
    {a : ℕ | ε * (a : ℝ) ≤ (vTwo a : ℝ)}.Finite := by
  obtain ⟨R, N, -, hR⟩ := valuation_arm_line_cover ε hε
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

/-- **`v₂(mₐ) = o(a)` in `IsLittleO` form** — `valuation_arm_finite` transposed along
`Nat.cofinite_eq_atTop`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem vTwo_isLittleO :
    (fun a : ℕ => (vTwo a : ℝ)) =o[Filter.atTop] (fun a : ℕ => (a : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hfin := valuation_arm_finite c hc
  have hmem : {a : ℕ | c * (a : ℝ) ≤ (vTwo a : ℝ)}ᶜ ∈ Filter.atTop (α := ℕ) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hfin.compl_mem_cofinite
  filter_upwards [hmem] with a ha
  have : ¬ (c * (a : ℝ) ≤ (vTwo a : ℝ)) := ha
  rw [Real.norm_natCast, Real.norm_natCast]
  linarith [not_le.mp this]

/-- **`v₂(mₐ) < ε·a` eventually** — the `∀ᶠ` form of `valuation_arm_finite`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem vTwo_eventually_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℕ in Filter.atTop, (vTwo a : ℝ) < ε * (a : ℝ) := by
  have hmem : {a : ℕ | ε * (a : ℝ) ≤ (vTwo a : ℝ)}ᶜ ∈ Filter.atTop (α := ℕ) := by
    rw [← Nat.cofinite_eq_atTop]
    exact (valuation_arm_finite ε hε).compl_mem_cofinite
  filter_upwards [hmem] with a ha
  exact not_le.mp ha

/-! ### Consequence: every fibre is an interval of length `o(a)` -/

/-- **The span of a relation-tower is at most `v₂` of its base**: if `a ≤ b` lie on one line then
`2ᵇ⁻ᵃ ∣ mₐ` (`BB13.sameTower_dvd`), hence `b − a ≤ v₂(mₐ)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_span_le_vTwo {a b : ℕ} (hab : a ≤ b) (h : SameTower a b) : b - a ≤ vTwo a :=
  le_vTwo_of_dvd (sameTower_dvd hab h)

/-- **The wiring to the span-stratified counts** (`BB13/SpanStrata.lean`): the hypothesis
`γ·a ≤ b − a` of `BB13.tall_towers_line_cover` implies `a ∈ A_γ`.  So the tall-tower strata are
*subsets* of the sets this file proves finite — the stratified line counts and the `o(a)` theorem
measure the same surplus, the first quantitatively at fixed `γ`, the second qualitatively for all
`γ`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_tower_le_vTwo {γ : ℝ} {a b : ℕ} (hab : a ≤ b) (h : SameTower a b)
    (hspan : γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ)) : γ * (a : ℝ) ≤ (vTwo a : ℝ) :=
  le_trans hspan (by exact_mod_cast sameTower_span_le_vTwo hab h)

/-- **Only finitely many indices carry a tall relation-tower**, for every `γ > 0` and with no
failure hypothesis: the unconditional shadow of `BB13.tall_towerBases_card_le`, which bounds the
number of *lines* at fixed `γ` but not the number of bases. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_towerBases_finite (γ : ℝ) (hγ : 0 < γ) :
    {a : ℕ | ∃ b : ℕ, a ≤ b ∧ SameTower a b ∧ γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ)}.Finite := by
  refine Set.Finite.subset (valuation_arm_finite γ hγ) ?_
  rintro a ⟨b, hab, hsame, hspan⟩
  exact tall_tower_le_vTwo hab hsame hspan

/-- **Every fibre is an interval of length `o(a)`, unconditionally**: the failures on the line of
slope `r` number at most `v₂(mₐ) + 1`, where `a` is the least of them.  With
`valuation_arm_finite` this is `o(a)`, improving the elementary
`BB13.sameTower_card_le_of_min` (`≤ a`) — though it is still not the `O(1)` that Problem 2 asks
for, since the `min` with the dyadic surplus `D(a)` is what would have to be bounded. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineFibre_card_le_vTwo {r : ℚ} {a : ℕ} (ha : a ∈ lineFibre r)
    (hmin : ∀ b ∈ lineFibre r, a ≤ b) : (lineFibre r).ncard ≤ vTwo a + 1 := by
  have hsub : lineFibre r ⊆ ↑(Finset.Icc a (a + vTwo a)) := by
    intro b hb
    have hab : a ≤ b := hmin b hb
    have hsame : SameTower a b := ha.2.2.trans hb.2.2.symm
    have := sameTower_span_le_vTwo hab hsame
    rw [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨hab, by omega⟩
  calc (lineFibre r).ncard
      ≤ (↑(Finset.Icc a (a + vTwo a)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.Icc a (a + vTwo a)).finite_toSet
    _ = (Finset.Icc a (a + vTwo a)).card := Set.ncard_coe_finset _
    _ = vTwo a + 1 := by rw [Nat.card_Icc]; omega

end BB13
