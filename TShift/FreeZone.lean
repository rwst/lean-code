/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.GeneralBase
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The free zone: `κ_b`, Proposition D, and the free-zone theorem

`TShift/GeneralBase.lean` built the arithmetic of the `ξ = 1` orbit at a general rational base
`p/q` — a `q`-adic floor, a divisibility cascade, a growth ceiling and a shadowing identity.  This
file is the `κ` layer on top: it turns each of those into a *linear sojourn cap*, states the
dichotomy that decides which cap is the useful one, and assembles **Theorem C** of
`plans/plan-Tshift-S1314.html` (report `report-Tshift.html` S14, idea N3).

## The two slopes, and Proposition D

  `κ_b = log q / log(p/q)`   (`kappaFloor`)  — route (a), the `q`-adic floor,
  `κ_casc = log(p/q) / log q` (`kappaCasc`)  — route (b), the divisibility cascade.

They are **exact reciprocals** (`kappaFloor_mul_kappaCasc`), and

  `κ_b < 1 ↔ q² < p`   (`freeZone_iff`, Proposition D),
  `κ_casc < 1 ↔ p < q²` (`cascZone_iff`, its companion).

Since coprimality excludes `p = q²` (`ne_sq_of_coprime`), `min(κ_b, κ_casc) < 1` at **every**
coprime `p > q ≥ 2` (`min_kappa_lt_one`).  The dichotomy therefore selects the route, it does not
gate the conclusion — finding **F7** of `plans/note-Tshift-S1314-WP0.html` §3.  Both sides are
witnessed at base `3/2`: `kappaFloor 3 2 = kappa (1/2) = 1.70951 > 1` (the hard band, floor route
useless) and `kappaCasc 3 2 = logb 2 (3/2) = 0.58496 < 1` (the cascade, which is exactly
`TShift.free_sojourn_cap`'s slope `κ_free`).  Their product is `1`
(`kappa_half_mul_free_kappa`), which is the reciprocity as a single identity.

## The two caps

* **(i) Route (a), the free-zone cap** — `free_zone_cap`.  An `m`-periodic block of the carry word
  of length `L` at date `n ≥ 1` obeys
  `L ≤ κ_b·n + m + log(2·D_m)/log(p/q)`, `D_m = p^m − q^m`.
  Ingredients: the `q`-adic floor `‖yₙ − A_w/D_m‖ ≥ 1/(D_m·qⁿ)` against the block shadow
  `((p/q)^{Jm} − 1)·|yₙ − A_w/D_m| ≤ 1`.  This is the only place `ξ = 1` is consumed, and it is the
  distinctively S14 ingredient: a genuine per-`n` rate `θ = 1/q`, which no cited paper supplies
  above `q²` and which the cascade cannot supply there.
* **(ii′) Route (b), the cascade cap** — `periodic_block_cap_casc`, the log form of
  `TShift.periodic_block_pow_le`: `L ≤ κ_casc·n + m·log p/log q`, past the growth threshold
  `q ≤ mₙ`, which `intPartB_ge_of_mul_le` reaches uniformly at `n ≥ q(q−1)` (at `q = 2`: `n ≥ 2`,
  reproducing `free_sojourn_cap`'s numeral).  This route is **formalize-the-known** — [GY26]
  Thm 1.2 proves it for every real `ξ ≠ 0` at every rational base, and [Dub09] Thm 3 runs the same
  count in complexity clothing.

The `log 2` in (i)'s constant is not in the plan's §1.4 D3 arithmetic: see the note under
`free_zone_cap`.

## The payoff: breaks in every dyadic block

A date `n` is an **`m`-break** when `s_{n+m} ≠ sₙ` (`IsBreakB`).  Break dates are infinite at every
base and for every `ξ ≠ 0` — that is [Dub09AA] Lemma 2, in corpus as
`Z32.not_isEventuallyPeriodic_carry`, and `exists_break_ge` is its two-line corollary.  A *cap*
upgrades infinitude to a rate: consecutive breaks satisfy `b_{k+1} ≤ (1+κ)·b_k + (κ + C)`
(`breakSeq_recursion`), and once `κ < 1` this is `b_{k+1} < 2·b_k` past an explicit date, so every
dyadic block `[2^j, 2^{j+1})` past an explicit `j₀` contains a break
(`exists_break_dyadic_of_cap`, through `TShift.dyadic_block_visit`).  The accounting is generic in
`(κ, C, n₀)`, which is what lets the same machinery run on either route, and hence gives the
all-bases corollary `exists_break_dyadic_all_bases`.

## κ-discipline (report §9)

Route (a)'s `κ_b` is `< 1` exactly in the free zone `p > q²`; base `3/2` is **not** in it, and
route (a) is vacuous there — the `q`-adic rate is `1/q = 1/2`, below the `2/3` threshold
(`TShift.kappa_lt_one_iff`, `TShift.one_lt_kappa_half`).  What base `3/2` gets is route (b), at
`κ_casc = 0.58496 < 1`, which is `TShift.free_sojourn_cap` and is *not* a per-`n` floor.  **No
instance of the T-shift problem (T0–T4) is proven or approached here**, and nothing in this file
gets nearer to a per-`n` floor at `3/2` above `2/3`, which remains the whole of T1.

## Scope

`ξ = 1`, `ν = 0` throughout, as in `TShift/GeneralBase.lean`.  For a general real `ξ` route (a) is
provably unavailable in this regime: [Aki08] Thms 2.4/2.5 build `ξ` whose orbit stays confined
precisely when `p > q²`.  Route (b) and break infinitude hold for every `ξ ≠ 0`; only the `ξ = 1`
instances are stated here, because that is the orbit `TShift/GeneralBase.lean` fixes.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide` on `ℚ` or `ℝ`.

## References

* `plans/plan-Tshift-S1314.html` §1.4 (D2, D3, D4), §2 (Proposition D, Theorem C), §3.1 (file map),
  WP5; `plans/note-Tshift-S1314-WP0.html` §3 (F7).
* `report-Tshift.html` S14, N3, §1.5, correction C20.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239 — Lemma 2 (aperiodicity of the carry word).
* [Aki08] S. Akiyama, *Mahler's `Z`-number and `3/2` number systems*, Unif. Distrib. Theory **3**
  (2008), 3–17, Thms 2.4/2.5 — confined orbits for `p > q²`; the `ξ = 1` scope warning.
* [GY26] X. Gao, C. H. Yip, *On the fractional parts of certain sequences of `ξαⁿ`*,
  arXiv:2408.02972v2 (23 May 2026), Thm 1.2 — route (b) in print, every real `ξ`, every base.
* [Dub09] A. Dubickas, *On integer sequences generated by linear maps*, Glasgow Math. J. **51**
  (2009), 243–252, Thm 3 — in corpus as `RB/DubickasFloor.lean`.
-/

namespace TShift

variable {p q : ℕ}

/-! ## 1. The sojourn slope at a general base

`TShift.kappa` is the slope of `TShift.sojourn_cap_kappa`, hard-wired to the contraction `2/3` of
base `3/2`.  Everything below needs the same bookkeeping at contraction `q/p`, so the two-parameter
`kappaB` comes first and `kappa` becomes its `b = 3/2` instance. -/

/-- `κ_b(b, θ) = log(1/θ)/log b`, the sojourn-cap slope at expansion factor `b` and repulsion rate
`θ`.  `TShift.kappa` is the instance `b = 3/2`. -/
noncomputable def kappaB (b θ : ℝ) : ℝ := -Real.log θ / Real.log b

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaB_three_halves (θ : ℝ) : kappaB (3 / 2) θ = kappa θ := rfl

/-- **The threshold at a general base.**  `κ_b(b, θ) < 1` exactly when `θ > 1/b`: the repulsion
rate must beat the contraction.  At `b = 3/2` this is `TShift.kappa_lt_one_iff`'s `θ > 2/3`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaB_lt_one_iff {b θ : ℝ} (hb : 1 < b) (hθ : 0 < θ) : kappaB b θ < 1 ↔ 1 / b < θ := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have hlb : 0 < Real.log b := Real.log_pos hb
  rw [kappaB, div_lt_one hlb]
  constructor
  · intro h
    have h1 : Real.log (1 / b) < Real.log θ := by
      rw [one_div, Real.log_inv]; linarith
    exact (Real.log_lt_log_iff (by positivity) hθ).mp h1
  · intro h
    have h1 : Real.log (1 / b) < Real.log θ := Real.log_lt_log (by positivity) h
    rw [one_div, Real.log_inv] at h1
    linarith

/-- The `2/3 ↦ 1/b` generalization of `TShift.sojourn_cap_kappa`: repulsion at rate `θ` against a
shadowing bound `(1/b)^L` caps `L` linearly in the date, with slope `kappaB b θ`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem sojourn_cap_base {b c θ d : ℝ} {n L : ℕ} (hb : 1 < b) (hc : 0 < c) (hθ : 0 < θ)
    (hrep : c * θ ^ n ≤ d) (hshadow : d ≤ (1 / b) ^ L) :
    (L : ℝ) ≤ kappaB b θ * n + (-Real.log c) / Real.log b := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hpos : 0 < c * θ ^ n := by positivity
  have hle : c * θ ^ n ≤ (1 / b) ^ L := le_trans hrep hshadow
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [show Real.log (1 / b) = -Real.log b by rw [one_div, Real.log_inv]] at hlog
  rw [kappaB, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hlb]
  linarith

/-- `TShift.sojourn_cap_kappa` is the `b = 3/2` instance, contraction `2/3` and all.  Checked so
that the generalization is machine-verified rather than asserted. -/
example {c θ d : ℝ} {n L : ℕ} (hc : 0 < c) (hθ : 0 < θ)
    (hrep : c * θ ^ n ≤ d) (hshadow : d ≤ (2 / 3 : ℝ) ^ L) :
    (L : ℝ) ≤ kappa θ * n + (-Real.log c) / Real.log (3 / 2) := by
  have h := sojourn_cap_base (b := (3 : ℝ) / 2) (by norm_num) hc hθ hrep
    (by rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num]; exact hshadow)
  rwa [kappaB_three_halves] at h

/-! ## 2. The two route slopes and Proposition D -/

/-- `κ_b = log q/log(p/q)`, the slope route (a) — the `q`-adic floor — buys. -/
noncomputable def kappaFloor (p q : ℕ) : ℝ := Real.log q / Real.log ((p : ℝ) / q)

/-- `κ_casc = log(p/q)/log q`, the slope route (b) — the divisibility cascade — buys. -/
noncomputable def kappaCasc (p q : ℕ) : ℝ := Real.log ((p : ℝ) / q) / Real.log q

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem log_base_pos (hq : 1 ≤ q) (hpq : q < p) : 0 < Real.log ((p : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlt : (q : ℝ) < p := by exact_mod_cast hpq
  refine Real.log_pos ?_
  rw [lt_div_iff₀ hqR]
  linarith

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem log_nat_pos (hq : 2 ≤ q) : 0 < Real.log (q : ℝ) :=
  Real.log_pos (by exact_mod_cast hq)

/-- `κ_b` is `kappaB` at the `q`-adic rate: the floor route's `θ` is `1/q`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaFloor_eq_kappaB : kappaFloor p q = kappaB ((p : ℝ) / q) (1 / (q : ℝ)) := by
  rw [kappaFloor, kappaB, one_div, Real.log_inv, neg_neg]

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaFloor_nonneg (hq : 1 ≤ q) (hpq : q < p) : 0 ≤ kappaFloor p q := by
  refine div_nonneg (Real.log_nonneg ?_) (le_of_lt (log_base_pos hq hpq))
  exact_mod_cast hq

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaCasc_pos (hq : 2 ≤ q) (hpq : q < p) : 0 < kappaCasc p q :=
  div_pos (log_base_pos (by omega) hpq) (log_nat_pos hq)

/-- **The reciprocity.**  `κ_b·κ_casc = 1` — an identity, not a numerical coincidence: this is why
the two routes tile the base space instead of overlapping. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaFloor_mul_kappaCasc (hq : 2 ≤ q) (hpq : q < p) :
    kappaFloor p q * kappaCasc p q = 1 := by
  have h1 : Real.log (q : ℝ) ≠ 0 := ne_of_gt (log_nat_pos hq)
  have h2 : Real.log ((p : ℝ) / q) ≠ 0 := ne_of_gt (log_base_pos (by omega) hpq)
  rw [kappaFloor, kappaCasc]
  field_simp

/-- **Proposition D.**  `κ_b < 1 ↔ q² < p`: the floor route delivers a sublinear cap exactly in the
free zone.  At `q = 2` the hard band `q < p < q²` contains the single base `3/2`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem freeZone_iff (hq : 1 ≤ q) (hpq : q < p) : kappaFloor p q < 1 ↔ q * q < p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlb := log_base_pos hq hpq
  rw [kappaFloor, div_lt_one hlb]
  constructor
  · intro h
    have hlt : (q : ℝ) < (p : ℝ) / q := (Real.log_lt_log_iff hqR (by positivity)).mp h
    rw [lt_div_iff₀ hqR] at hlt
    exact_mod_cast hlt
  · intro h
    have hlt : (q : ℝ) < (p : ℝ) / q := by
      rw [lt_div_iff₀ hqR]
      exact_mod_cast h
    exact Real.log_lt_log hqR hlt

/-- **Proposition D's companion.**  `κ_casc < 1 ↔ p < q²`: the cascade route delivers a sublinear
cap exactly in the hard band. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cascZone_iff (hq : 2 ≤ q) (hpq : q < p) : kappaCasc p q < 1 ↔ p < q * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [kappaCasc, div_lt_one (log_nat_pos hq)]
  constructor
  · intro h
    have hlt : (p : ℝ) / q < q := (Real.log_lt_log_iff (by positivity) hqR).mp h
    rw [div_lt_iff₀ hqR] at hlt
    exact_mod_cast hlt
  · intro h
    have hlt : (p : ℝ) / q < q := by
      rw [div_lt_iff₀ hqR]
      exact_mod_cast h
    exact Real.log_lt_log (by positivity) hlt

/-- Coprimality excludes the boundary `p = q²`, so the two zones really do tile. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem ne_sq_of_coprime (hq : 2 ≤ q) (hcop : Nat.Coprime p q) : p ≠ q * q := by
  intro hEq
  have hdvd : q ∣ p := hEq ▸ Dvd.intro q rfl
  have : q = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
  omega

/-- **The tiling (finding F7).**  At *every* coprime `p > q ≥ 2` one of the two routes has slope
`< 1`.  The dichotomy `p ≷ q²` selects the route; it does not gate the conclusion. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem min_kappa_lt_one (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q) :
    min (kappaFloor p q) (kappaCasc p q) < 1 := by
  rcases lt_or_gt_of_ne (ne_sq_of_coprime hq hcop) with h | h
  · exact lt_of_le_of_lt (min_le_right _ _) ((cascZone_iff hq hpq).mpr h)
  · exact lt_of_le_of_lt (min_le_left _ _) ((freeZone_iff (by omega) hpq).mpr h)

/-! ### Both sides witnessed at base `3/2` -/

/-- The hard-band witness: at `(3, 2)` the floor route's slope is `TShift.kappa (1/2) = 1.70951`,
which `TShift.one_lt_kappa_half` puts above `1`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaFloor_three_two : kappaFloor 3 2 = kappa (1 / 2) := by
  have h : -Real.log ((1 : ℝ) / 2) = Real.log 2 := by rw [one_div, Real.log_inv, neg_neg]
  simp only [kappaFloor, kappa, h]
  norm_num

/-- The free-zone side is empty at `(3, 2)`: `2² = 4 > 3`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem not_freeZone_three_two : ¬ (kappaFloor 3 2 < 1) := by
  rw [freeZone_iff (by norm_num) (by norm_num)]
  norm_num

/-- The cascade witness: at `(3, 2)` the cascade slope is `κ_free = log₂(3/2) = 0.58496`, i.e.
exactly the slope of `TShift.free_sojourn_cap`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappaCasc_three_two : kappaCasc 3 2 = Real.logb 2 (3 / 2) := by
  simp only [kappaCasc, Real.logb]
  norm_num

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem cascZone_three_two : kappaCasc 3 2 < 1 :=
  (cascZone_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- **The reciprocity, in base-`3/2` currency.**  `κ(1/2)·κ_free = 1`.  The `θ = 1/2` sojourn rung
of report §1.5 and the free carry-word rung are the *same* statement read from the two sides, which
is why `plan-Tshift-S1314`'s D4 could print them as separate rows only by mistake (F6). -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappa_half_mul_free_kappa : kappa (1 / 2) * Real.logb 2 (3 / 2) = 1 := by
  rw [← kappaFloor_three_two, ← kappaCasc_three_two]
  exact kappaFloor_mul_kappaCasc (by norm_num) (by norm_num)

/-! ## 3. The growth threshold, uniform in the base

Route (b)'s cap needs `q ≤ mₙ` (`TShift.intPartB_ge_iff`).  Bernoulli turns that into an explicit
burn-in valid at every base: `n ≥ q(q−1)`.  At `q = 2` it reads `n ≥ 2`, which is
`TShift.free_sojourn_cap`'s numeral. -/

/-- **The uniform growth threshold.**  `q ≤ ⌊(p/q)ⁿ⌋` for every `n ≥ q(q−1)`, at every base
`p > q ≥ 2`.  By finding **F9** the *sharp* threshold is `q^{n+1} ≤ pⁿ`, which in the free zone is
already met at `n = 1`; `q(q−1)` is the base-independent bound that covers the hard band too. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem intPartB_ge_of_mul_le (hq : 2 ≤ q) (hpq : q < p) {n : ℕ} (hn : q * (q - 1) ≤ n) :
    (q : ℤ) ≤ intPartB p q n := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hinv : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hstep : (1 : ℝ) + (q : ℝ)⁻¹ ≤ (p : ℝ) / q := by
    have hp1 : ((q : ℝ) + 1) ≤ p := by exact_mod_cast (by omega : q + 1 ≤ p)
    rw [show (1 : ℝ) + (q : ℝ)⁻¹ = ((q : ℝ) + 1) / q by field_simp]
    gcongr
  have hbern : (1 : ℝ) + (n : ℝ) * (q : ℝ)⁻¹ ≤ (1 + (q : ℝ)⁻¹) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hmono : ((1 : ℝ) + (q : ℝ)⁻¹) ^ n ≤ ((p : ℝ) / q) ^ n :=
    pow_le_pow_left₀ (by positivity) hstep n
  have hnq : (q : ℝ) * ((q : ℝ) - 1) ≤ (n : ℝ) := by
    have hcast : ((q * (q - 1) : ℕ) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
      have h1 : (1 : ℕ) ≤ q := by omega
      push_cast [Nat.cast_sub h1]
      ring
    have h2 := (Nat.cast_le (α := ℝ)).mpr hn
    rw [hcast] at h2
    linarith
  have hlow : (q : ℝ) ≤ 1 + (n : ℝ) * (q : ℝ)⁻¹ := by
    have h1 : ((q : ℝ) * ((q : ℝ) - 1)) * (q : ℝ)⁻¹ ≤ (n : ℝ) * (q : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hnq hinv
    have h2 : ((q : ℝ) * ((q : ℝ) - 1)) * (q : ℝ)⁻¹ = (q : ℝ) - 1 := by
      field_simp
    rw [h2] at h1
    linarith
  have hqle : (q : ℝ) ≤ ((p : ℝ) / q) ^ n := by linarith
  rw [intPartB_eq]
  exact Int.le_floor.mpr (by exact_mod_cast hqle)

/-! ## 4. Route (b): the cascade cap in logarithmic form -/

/-- **Theorem C (ii′), the cascade cap.**  An `m`-periodic block of the carry word of length `L` at
a date `n ≥ q(q−1)` obeys `L ≤ κ_casc·n + m·log p/log q`, at every coprime `p > q ≥ 2`.  The
integer form is `TShift.periodic_block_pow_le`; at `(3, 2)` the whole statement is
`TShift.free_sojourn_cap`.  **Formalize-the-known**: [GY26] Thm 1.2 has this for every real
`ξ ≠ 0`, and [Dub09] Thm 3 in complexity clothing. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "GY26", group "tshift_s14"]
theorem periodic_block_cap_casc (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {n L m : ℕ} (hn : q * (q - 1) ≤ n) (hm : 1 ≤ m) (hmL : m ≤ L)
    (h : IsPeriodicBlockB p q n L m) :
    (L : ℝ) ≤ kappaCasc p q * n + m * (Real.log p / Real.log q) := by
  have hlq : 0 < Real.log (q : ℝ) := log_nat_pos hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hint := periodic_block_pow_le (by omega : 1 ≤ q) hpq hcop
    (intPartB_ge_of_mul_le hq hpq hn) hm hmL h
  have hreal : (q : ℝ) ^ (L + n) ≤ (p : ℝ) ^ (n + m) := by exact_mod_cast hint
  have hlog : ((L : ℝ) + n) * Real.log q ≤ ((n : ℝ) + m) * Real.log p := by
    have h1 : Real.log ((q : ℝ) ^ (L + n)) ≤ Real.log ((p : ℝ) ^ (n + m)) :=
      Real.log_le_log (by positivity) hreal
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hdiv : Real.log ((p : ℝ) / q) = Real.log p - Real.log q :=
    Real.log_div (ne_of_gt hpR) (ne_of_gt hqR)
  have hgoal : kappaCasc p q * n + (m : ℝ) * (Real.log p / Real.log q)
      = ((n : ℝ) * (Real.log p - Real.log q) + (m : ℝ) * Real.log p) / Real.log q := by
    rw [kappaCasc, hdiv]
    field_simp
  rw [hgoal, le_div_iff₀ hlq]
  linarith

/-! ## 5. Route (a): the free-zone cap

The `q`-adic floor of `TShift/GeneralBase.lean` §3 against the block shadow of §8.  The floor is
applied at the cycle target `A_w/D_m`, which `cycleDenomB_coprime` licenses. -/

/-- **The contest, in exact form.**  Along `J` windows of an `m`-periodic block at date `n ≥ 1`,
`(p/q)^{Jm} ≤ 1 + D_m·qⁿ`.  Nothing is discarded here: `D_m·qⁿ` is the reciprocal of the `q`-adic
floor and `(p/q)^{Jm} − 1` is the exact shadow factor. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem free_zone_cap_pow (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {n L m J : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hJ : J * m ≤ L)
    (h : IsPeriodicBlockB p q n L m) :
    ((p : ℝ) / q) ^ (J * m) ≤ 1 + (cycleDenomB p q m : ℝ) * (q : ℝ) ^ n := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpqR : (q : ℝ) < p := by exact_mod_cast hpq
  have hratio : (1 : ℝ) < (p : ℝ) / q := by rw [lt_div_iff₀ hqR]; linarith
  have hD0 : 0 < cycleDenomB p q m := cycleDenomB_pos hpq hm
  have hDR : (0 : ℝ) < (cycleDenomB p q m : ℝ) := by exact_mod_cast hD0
  have hDcop : Nat.Coprime (cycleDenomB p q m) q := cycleDenomB_coprime hcop (le_of_lt hpq) hm
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  set A : ℤ := carrySumB p q n m with hA
  set ρ : ℝ := (A : ℝ) / ((cycleDenomB p q m : ℕ) : ℝ) with hρ
  -- the `q`-adic floor at the cycle target
  have hfloor : 1 / ((cycleDenomB p q m : ℝ) * (q : ℝ) ^ n) ≤ |fracB p q n - ρ| := by
    have h1 := distToNearestInt_ge_of_coprime_denom (p := p) (q := q) hq hcop hDcop hD0 hn A
    have h2 := distToNearestInt_fracB_sub (p := p) (q := q) n ρ
    have h3 : distToNearestInt (fracB p q n - ρ) ≤ |fracB p q n - ρ| := by
      simpa using distToNearestInt_le_abs_sub_intCast (fracB p q n - ρ) 0
    rw [hρ]
    rw [hρ] at h2
    linarith [h1, h2, h3]
  -- the block shadow
  have hshadow := block_shadow (p := p) (q := q) hq1 hpq hm hJ h
  have hR1 : (1 : ℝ) ≤ ((p : ℝ) / q) ^ (J * m) := one_le_pow₀ (le_of_lt hratio)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((p : ℝ) / q) ^ (J * m) - 1)] at hshadow
  have hstep : (((p : ℝ) / q) ^ (J * m) - 1) * (1 / ((cycleDenomB p q m : ℝ) * (q : ℝ) ^ n))
      ≤ (((p : ℝ) / q) ^ (J * m) - 1) * |fracB p q n - ρ| :=
    mul_le_mul_of_nonneg_left hfloor (by linarith)
  have hchain : (((p : ℝ) / q) ^ (J * m) - 1) / ((cycleDenomB p q m : ℝ) * (q : ℝ) ^ n) ≤ 1 := by
    rw [div_eq_mul_one_div]
    linarith [hstep, hshadow]
  have := (div_le_one (by positivity)).mp hchain
  linarith

/-- **Theorem C (i), the free-zone cap.**  An `m`-periodic block of the carry word of `(p/q)ⁿ`,
`ξ = 1`, of length `L` at a date `n ≥ 1` obeys

  `L ≤ κ_b·n + m + log(2·D_m)/log(p/q)`,  `κ_b = log q/log(p/q)`,  `D_m = p^m − q^m`.

By `freeZone_iff` the slope is `< 1` exactly when `p > q²`, and there this is a genuinely
sublinear cap resting on a per-`n` rate `θ = 1/q` — the ingredient no cited paper supplies in the
free zone, and the only place `ξ = 1` is consumed.

**Small print.**  `plan-Tshift-S1314` §1.4 D3 predicts the constant `m + log D_m/log(p/q)`.  The
extra `log 2/log(p/q)` is the price of the shadowing variant that is actually available: the plan's
arithmetic assumes `|z_J − ρ_w| ≤ 1` at the far end of the block, which needs the cycle point to
sit within `1` of a fractional part and is not proved anywhere.  What *is* free is the endpoint
spread `|z_J − z_0| ≤ 1` (`TShift.abs_sub_fixed_mul_le_block`), and it yields `(p/q)^{Jm} ≤ 1 +
D_m qⁿ` rather than `≤ D_m qⁿ`.  The slope, and hence Proposition D, is untouched. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem free_zone_cap (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {n L m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h : IsPeriodicBlockB p q n L m) :
    (L : ℝ) ≤ kappaFloor p q * n
      + ((m : ℝ) + Real.log (2 * (cycleDenomB p q m : ℝ)) / Real.log ((p : ℝ) / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlb := log_base_pos (by omega : 1 ≤ q) hpq
  have hD0 : 0 < cycleDenomB p q m := cycleDenomB_pos hpq hm
  have hDR : (0 : ℝ) < (cycleDenomB p q m : ℝ) := by exact_mod_cast hD0
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hDq : (1 : ℝ) ≤ (cycleDenomB p q m : ℝ) * (q : ℝ) ^ n := by
    have h1 : (1 : ℝ) ≤ (cycleDenomB p q m : ℝ) := by exact_mod_cast hD0
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q))
    nlinarith
  set J : ℕ := L / m with hJdef
  have hJ : J * m ≤ L := Nat.div_mul_le_self L m
  have hLlt : L < J * m + m := by
    have h1 : m * J + L % m = L := by rw [hJdef]; exact Nat.div_add_mod L m
    have h2 : L % m < m := Nat.mod_lt _ (by omega)
    calc L = m * J + L % m := h1.symm
      _ < m * J + m := Nat.add_lt_add_left h2 _
      _ = J * m + m := by ring
  have hpow := free_zone_cap_pow hq hpq hcop hn hm hJ h
  have hbound : ((p : ℝ) / q) ^ (J * m) ≤ 2 * (cycleDenomB p q m : ℝ) * (q : ℝ) ^ n := by
    nlinarith [hpow, hDq]
  have hlog : ((J * m : ℕ) : ℝ) * Real.log ((p : ℝ) / q)
      ≤ Real.log (2 * (cycleDenomB p q m : ℝ)) + (n : ℝ) * Real.log q := by
    have h1 : Real.log (((p : ℝ) / q) ^ (J * m))
        ≤ Real.log (2 * (cycleDenomB p q m : ℝ) * (q : ℝ) ^ n) :=
      Real.log_le_log (by positivity) hbound
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    exact h1
  have hJm : ((J * m : ℕ) : ℝ)
      ≤ kappaFloor p q * n + Real.log (2 * (cycleDenomB p q m : ℝ)) / Real.log ((p : ℝ) / q) := by
    rw [kappaFloor, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hlb]
    linarith
  have hLR : (L : ℝ) ≤ ((J * m : ℕ) : ℝ) + m := by
    have : (L : ℝ) < ((J * m : ℕ) : ℝ) + m := by exact_mod_cast hLlt
    linarith
  linarith

/-! ## 6. Break dates: infinitude, the recursion, and the dyadic payoff

Everything in this section is generic in the cap `(κ, C, n₀)`, so it runs on either route. -/

/-- Date `n` is an **`m`-break** of the carry word: `s_{n+m} ≠ sₙ`. -/
def IsBreakB (p q m n : ℕ) : Prop := carryB p q (n + m) ≠ carryB p q n

/-- **Break infinitude, at every base.**  Two lines from [Dub09AA] Lemma 2
(`Z32.not_isEventuallyPeriodic_carry`): a last `m`-break would make the word eventually
`m`-periodic. -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem exists_break_ge (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) {m : ℕ} (hm : 1 ≤ m)
    (N : ℕ) : ∃ n, N ≤ n ∧ IsBreakB p q m n := by
  by_contra hcon
  push Not at hcon
  refine carryB_not_isEventuallyPeriodic hq hpq hcop ⟨N, m, by omega, ?_⟩
  intro k hk
  have := hcon k hk
  rwa [IsBreakB, not_ne_iff] at this

@[category research solved, AMS 11 37, ref "TshiftS1314" "Dub09AA", group "tshift_s14"]
theorem breaks_infinite (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) {m : ℕ} (hm : 1 ≤ m) :
    {n : ℕ | IsBreakB p q m n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨n, hn, hbr⟩ := exists_break_ge hq hpq hcop hm (b + 1)
  have := hb (show n ∈ {n : ℕ | IsBreakB p q m n} from hbr)
  omega

/-- The `m`-break dates, enumerated from `n₀` on. -/
noncomputable def breakSeq (p q m n₀ : ℕ) : ℕ → ℕ
  | 0 => sInf {n : ℕ | n₀ ≤ n ∧ IsBreakB p q m n}
  | k + 1 => sInf {n : ℕ | breakSeq p q m n₀ k + 1 ≤ n ∧ IsBreakB p q m n}

variable {m n₀ : ℕ}

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_spec (hbr : ∀ N, ∃ n, N ≤ n ∧ IsBreakB p q m n) (k : ℕ) :
    n₀ ≤ breakSeq p q m n₀ k ∧ IsBreakB p q m (breakSeq p q m n₀ k) := by
  induction k with
  | zero =>
      obtain ⟨n, hn, hb⟩ := hbr n₀
      have hne : {n : ℕ | n₀ ≤ n ∧ IsBreakB p q m n}.Nonempty := ⟨n, hn, hb⟩
      simpa [breakSeq, Set.mem_setOf_eq] using Nat.sInf_mem hne
  | succ k ih =>
      obtain ⟨n, hn, hb⟩ := hbr (breakSeq p q m n₀ k + 1)
      have hne : {n : ℕ | breakSeq p q m n₀ k + 1 ≤ n ∧ IsBreakB p q m n}.Nonempty := ⟨n, hn, hb⟩
      have h : breakSeq p q m n₀ k + 1 ≤ breakSeq p q m n₀ (k + 1)
          ∧ IsBreakB p q m (breakSeq p q m n₀ (k + 1)) := by
        simpa [breakSeq, Set.mem_setOf_eq] using Nat.sInf_mem hne
      exact ⟨by omega, h.2⟩

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_lt (hbr : ∀ N, ∃ n, N ≤ n ∧ IsBreakB p q m n) (k : ℕ) :
    breakSeq p q m n₀ k < breakSeq p q m n₀ (k + 1) := by
  obtain ⟨n, hn, hb⟩ := hbr (breakSeq p q m n₀ k + 1)
  have hne : {n : ℕ | breakSeq p q m n₀ k + 1 ≤ n ∧ IsBreakB p q m n}.Nonempty := ⟨n, hn, hb⟩
  have h : breakSeq p q m n₀ k + 1 ≤ breakSeq p q m n₀ (k + 1)
      ∧ IsBreakB p q m (breakSeq p q m n₀ (k + 1)) := by
    simpa [breakSeq, Set.mem_setOf_eq] using Nat.sInf_mem hne
  omega

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_strictMono (hbr : ∀ N, ∃ n, N ≤ n ∧ IsBreakB p q m n) :
    StrictMono (breakSeq p q m n₀) :=
  strictMono_nat_of_lt_succ (breakSeq_lt hbr)

@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_ge (hbr : ∀ N, ∃ n, N ≤ n ∧ IsBreakB p q m n) (k : ℕ) :
    k ≤ breakSeq p q m n₀ k := by
  induction k with
  | zero => omega
  | succ k ih => have := breakSeq_lt (p := p) (q := q) (m := m) (n₀ := n₀) hbr k; omega

/-- Between consecutive enumerated breaks there is no break: `breakSeq` enumerates *all* of
them. -/
@[category API, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_gap {k j : ℕ} (h1 : breakSeq p q m n₀ k < j)
    (h2 : j < breakSeq p q m n₀ (k + 1)) : ¬ IsBreakB p q m j := by
  intro hcon
  have hmem : j ∈ {n : ℕ | breakSeq p q m n₀ k + 1 ≤ n ∧ IsBreakB p q m n} := ⟨by omega, hcon⟩
  have hle := Nat.sInf_le hmem
  simp only [breakSeq] at h2
  omega

/-- Hence the word is `m`-periodic on the whole gap: an `m`-periodic block of length
`b_{k+1} − b_k − 1 + m` at date `b_k + 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_isPeriodicBlock (k : ℕ) :
    IsPeriodicBlockB p q (breakSeq p q m n₀ k + 1)
      (breakSeq p q m n₀ (k + 1) - breakSeq p q m n₀ k - 1 + m) m := by
  intro i hi
  have hnb := breakSeq_gap (p := p) (q := q) (m := m) (n₀ := n₀) (k := k)
    (j := breakSeq p q m n₀ k + 1 + i) (by omega) (by omega)
  rw [IsBreakB, not_ne_iff] at hnb
  rw [show breakSeq p q m n₀ k + 1 + m + i = breakSeq p q m n₀ k + 1 + i + m by ring]
  exact hnb.symm

/-- **The break recursion.**  Any linear cap `L ≤ κ·n + C` on `m`-periodic blocks past `n₀`
propagates to the break dates: `b_{k+1} ≤ (1+κ)·b_k + (κ + C)`.  The base-`3/2` instance of this
shape is `TShift.escapeSeq_recursion`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem breakSeq_recursion (hbr : ∀ N, ∃ n, N ≤ n ∧ IsBreakB p q m n) (hm : 1 ≤ m)
    {κ C : ℝ} (hcap : ∀ n L : ℕ, n₀ ≤ n → m ≤ L → IsPeriodicBlockB p q n L m →
      (L : ℝ) ≤ κ * n + C) (k : ℕ) :
    (breakSeq p q m n₀ (k + 1) : ℝ) ≤ (1 + κ) * breakSeq p q m n₀ k + (κ + C) := by
  set b := breakSeq p q m n₀ k with hb
  set b1 := breakSeq p q m n₀ (k + 1) with hb1
  have hlt : b < b1 := breakSeq_lt hbr k
  have hn₀ : n₀ ≤ b := (breakSeq_spec hbr k).1
  have hblock := breakSeq_isPeriodicBlock (p := p) (q := q) (m := m) (n₀ := n₀) k
  have hL := hcap (b + 1) (b1 - b - 1 + m) (by omega) (by omega) hblock
  have hcast : ((b1 - b - 1 + m : ℕ) : ℝ) = (b1 : ℝ) + m - b - 1 := by
    have hsum : (b1 - b - 1 + m) + (b + 1) = b1 + m := by omega
    have h := congrArg (fun t : ℕ => (t : ℝ)) hsum
    push_cast at h ⊢
    linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hcast] at hL
  push_cast at hL
  linarith

/-- **The dyadic payoff, generic in the cap.**  A linear cap of slope `κ < 1` on `m`-periodic
blocks puts an `m`-break in *every* dyadic block `[2^j, 2^{j+1})` past an explicit `j₀`.  Through
`TShift.lt_two_mul_of_lt_two` and `TShift.dyadic_block_visit`, exactly as at base `3/2`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem exists_break_dyadic_of_cap (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hm : 1 ≤ m) {κ C : ℝ} (hκ1 : κ < 1)
    (hcap : ∀ n L : ℕ, n₀ ≤ n → m ≤ L → IsPeriodicBlockB p q n L m → (L : ℝ) ≤ κ * n + C) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ n : ℕ, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ IsBreakB p q m n := by
  have hbr := exists_break_ge (p := p) (q := q) (m := m) hq hpq hcop hm
  have hmonoN : StrictMono (breakSeq p q m n₀) := breakSeq_strictMono hbr
  have hmono : StrictMono (fun k => (breakSeq p q m n₀ k : ℝ)) := fun a b hab =>
    show ((breakSeq p q m n₀ a : ℕ) : ℝ) < ((breakSeq p q m n₀ b : ℕ) : ℝ) by
      exact_mod_cast hmonoN hab
  have hrec := breakSeq_recursion (p := p) (q := q) (m := m) (n₀ := n₀) hbr hm hcap
  have hge : ∀ k : ℕ, (k : ℝ) ≤ (breakSeq p q m n₀ k : ℝ) := fun k => by
    exact_mod_cast breakSeq_ge (p := p) (q := q) (m := m) (n₀ := n₀) hbr k
  have hunb : ∀ M : ℝ, ∃ k, M ≤ (breakSeq p q m n₀ k : ℝ) := fun M =>
    ⟨⌈M⌉₊, le_trans (Nat.le_ceil M) (hge ⌈M⌉₊)⟩
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((κ + C) / (2 - (1 + κ)))
  have hstep : ∀ k : ℕ, k₀ ≤ k →
      (breakSeq p q m n₀ (k + 1) : ℝ) < 2 * (breakSeq p q m n₀ k : ℝ) := by
    intro k hk
    refine lt_two_mul_of_lt_two (by linarith) (hrec k) ?_
    have h1 : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2 := hge k
    linarith
  refine ⟨breakSeq p q m n₀ k₀, fun j hj => ?_⟩
  have hj2 : (breakSeq p q m n₀ k₀ : ℝ) ≤ 2 ^ j := by
    have h1 : breakSeq p q m n₀ k₀ < 2 ^ (breakSeq p q m n₀ k₀) := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ (breakSeq p q m n₀ k₀) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have h3 : breakSeq p q m n₀ k₀ ≤ 2 ^ j := by omega
    calc (breakSeq p q m n₀ k₀ : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h3
      _ = 2 ^ j := by push_cast; ring
  obtain ⟨k, hk1, hk2⟩ := dyadic_block_visit hmono hstep hunb hj2
  refine ⟨breakSeq p q m n₀ k, ?_, ?_, (breakSeq_spec hbr k).2⟩
  · have hc : ((2 ^ j : ℕ) : ℝ) ≤ (breakSeq p q m n₀ k : ℝ) := by push_cast; exact hk1
    exact_mod_cast hc
  · have hc : (breakSeq p q m n₀ k : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by push_cast; exact hk2
    exact_mod_cast hc

/-! ## 7. Theorem C -/

/-- **Theorem C (ii): the free-zone payoff.**  For coprime `p > q²`, `q ≥ 2`, `ξ = 1` and every
period `m ≥ 1`: every dyadic block of dates past an explicit `j₀(m)` contains an `m`-periodicity
break of the carry word.  Driven by route (a), `κ_b < 1`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem exists_break_dyadic_free_zone (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hfree : q * q < p) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ n : ℕ, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ IsBreakB p q m n :=
  exists_break_dyadic_of_cap (n₀ := 1) (by omega) hpq hcop hm
    ((freeZone_iff (by omega) hpq).mpr hfree)
    (fun n L hn _ h => free_zone_cap hq hpq hcop hn hm h)

/-- **Theorem C (ii′): the cascade payoff.**  The same conclusion in the hard band `p < q²`,
driven by route (b), `κ_casc < 1`.  Formalize-the-known ([GY26] Thm 1.2). -/
@[category research solved, AMS 11 37, ref "TshiftS1314" "GY26", group "tshift_s14"]
theorem exists_break_dyadic_casc (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hband : p < q * q) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ n : ℕ, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ IsBreakB p q m n :=
  exists_break_dyadic_of_cap (n₀ := q * (q - 1)) (by omega) hpq hcop hm
    ((cascZone_iff hq hpq).mpr hband)
    (fun n L hn hmL h => periodic_block_cap_casc hq hpq hcop hn hm hmL h)

/-- **Theorem C (iii): the all-bases corollary — the capstone.**  At *every* coprime `p > q ≥ 2`,
with `ξ = 1` and every period `m ≥ 1`, the carry word of `(p/q)ⁿ` has an `m`-periodicity break in
every dyadic block `[2^j, 2^{j+1})` past an explicit `j₀(m)`.

This needs both routes and the reciprocity `κ_b·κ_casc = 1`: `p ≷ q²` decides which of the two
slopes is `< 1`, and coprimality rules out the boundary `p = q²`.  At `(3, 2)` the route taken is
(b), where the statement is `TShift.free_sojourn_cap`'s payoff; in the free zone it is route (a),
whose `q`-adic floor is the distinctively new ingredient.  `κ = min(κ_b, κ_casc) < 1`
(`min_kappa_lt_one`); this is a *symbolic* statement about the carry word, not a per-`n` floor, and
it approaches no instance of the T-shift problem. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem exists_break_dyadic_all_bases (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ n : ℕ, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ IsBreakB p q m n := by
  rcases lt_or_gt_of_ne (ne_sq_of_coprime hq hcop) with h | h
  · exact exists_break_dyadic_casc hq hpq hcop h hm
  · exact exists_break_dyadic_free_zone hq hpq hcop h hm

/-! ## 8. The instance: base `5/2`

The smallest free-zone base (`2² = 4 < 5`), and the one `plan-Tshift-S1314` D4 pins.
`κ_b(5/2) = log 2/log(5/2) = 0.756468…`, `D₁ = 3`, `D₂ = 21`. -/

@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem freeZone_five_two : kappaFloor 5 2 < 1 :=
  (freeZone_iff (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Theorem C (i) at `(5, 2)`, `m = 1`: `L ≤ 0.756468·n + (1 + log 6/log(5/2))`, the second
constant being `1 + 1.955445 = 2.955445`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem free_zone_cap_five_two {n L : ℕ} (hn : 1 ≤ n) (h : IsPeriodicBlockB 5 2 n L 1) :
    (L : ℝ) ≤ kappaFloor 5 2 * n + (1 + Real.log 6 / Real.log ((5 : ℝ) / 2)) := by
  have hcap := free_zone_cap (p := 5) (q := 2) (by norm_num) (by norm_num) (by norm_num) hn
    (by norm_num : (1 : ℕ) ≤ 1) h
  have hD : ((cycleDenomB 5 2 1 : ℕ) : ℝ) = 3 := by norm_num [cycleDenomB]
  rw [hD] at hcap
  norm_num at hcap ⊢
  convert hcap using 3

/-- Theorem C (ii) at `(5, 2)`: every dyadic block past an explicit `j₀(m)` carries an
`m`-periodicity break of the carry word of `(5/2)ⁿ`. -/
@[category research solved, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem exists_break_dyadic_five_two {m : ℕ} (hm : 1 ≤ m) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ n : ℕ, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ IsBreakB 5 2 m n :=
  exists_break_dyadic_free_zone (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm

/-! ## 9. Sanity -/

/-- The growth threshold `q(q−1)` reproduces the base-`3/2` numeral `2`, and at `(5, 2)` the sharp
threshold (finding F9) is already met at `n = 1`. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem growth_threshold_sanity :
    (2 : ℤ) ≤ intPartB 3 2 (2 * (2 - 1)) ∧ (2 : ℤ) ≤ intPartB 5 2 1 :=
  ⟨intPartB_ge_of_mul_le (by norm_num) (by norm_num) (le_refl _),
    (intPartB_one_ge_iff (by norm_num)).mpr (by norm_num)⟩

/-- The `κ` grid of `plan-Tshift-S1314` D4, in exact form: at `(3, 2)` the floor route is above the
threshold and the cascade route below it, and the two are reciprocal. -/
@[category test, AMS 11 37, ref "TshiftS1314", group "tshift_s14"]
theorem kappa_grid_sanity :
    1 < kappaFloor 3 2 ∧ kappaCasc 3 2 < 1 ∧ kappaFloor 5 2 < 1 ∧
      kappaFloor 3 2 * kappaCasc 3 2 = 1 :=
  ⟨kappaFloor_three_two ▸ one_lt_kappa_half, cascZone_three_two, freeZone_five_two,
    kappaFloor_mul_kappaCasc (by norm_num) (by norm_num)⟩

end TShift
