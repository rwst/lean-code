/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.MultiplierTransfer
import TShift.FreeSojourn
import TShift.DeterminantCap
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Minkowski-critical box, and the escape window

Two elementary chapters about the auxiliary forms behind `‖D·(3/2)ⁿ‖`, and about the dates at which
that quantity is *large*.  The forms are the points of the lattice

  `L_n = {(b, a·2ⁿ + b·3ⁿ) : a, b ∈ ℤ}`,   `det L_n = 2ⁿ`,

and the elimination step of the Padé method (`TShift.multiplier_transfer`) turns two independent
small points of `L_n` into a lower bound for `‖D·(3/2)ⁿ‖`.

## 1. The critical box, and the equivalence it carries

The demand a Padé construction has to meet — auxiliary forms with `|ℓᵢ| ≤ Λ`, `|bᵢ| ≤ B` and
`B < (3/2)^{n(1−ε)}` — is the rate `θ > 2/3`; and at `θ = 2/3` the demanded pair is

  `(Λ, B) = ((4/3)ⁿ, (3/2)ⁿ)`,   with   `Λ·B = 2ⁿ = det L_n`   (`critical_box_exact`),

because `log₂(4/3) + log₂(3/2) = 1`.  The box sits *on* the Minkowski boundary; so the ask "certify
two independent forms in that box" is an exact **restatement** of the uniform multiplier floor at
`θ = 2/3`, not a weakening of it.  Both directions are proved here, with explicit constants and
without any geometry-of-numbers machinery:

* **one form is free** (`exists_form_in_box`): Dirichlet's pigeonhole puts a form with `0 < b ≤ N`
  and `|ℓ| ≤ X/(N+1)` in the box at every date, whatever the columns.  Hence also
  `floor_le_critical`: no uniform floor can exceed `X/B`, so the critical box is where the floor
  hypothesis stops being contradictory;
* **the floor buys the second form** (`forms_of_floor`): if every form with `0 < |b| ≤ B` has
  `|ℓ| ≥ S`, then two **independent** forms exist, with `|ℓᵢ| ≤ X/B` and `|bᵢ| ≤ X/S + 1`.  The
  proof is a Bézout reduction: were the two pigeonhole forms dependent, their gcd combination would
  be a form with `0 < b ≤ B` strictly below the floor.  Note the shape of the conclusion — the
  blow-up is **only in the coefficient slot**, where Minkowski's second theorem blows up both;
* **two forms buy the floor back** (`uniformFloor_of_twoFormsInBox`): Proposition 1 at content `1`;
* and the round trip closes, as an equivalence of the two *uniform-in-`n`* statements
  (`floor_iff_forms`).  At a single date both sides are trivially true, so uniformity in `n` is the
  whole content — which is what "the uniform floor" means.

The `ε`-slack in that equivalence is one factor, and it is unavoidable: the floor is stated with a
range factor `β > 1` in the coefficient slot, the forms with a size factor `η < 1`.  The two
directions pull in opposite directions on the box volume — the converse needs `vol ≥ det` (else the
pigeonhole point leaves the box), the forward direction needs `vol ≤ det` (else the transfer's
`X − |b|·Λ` term is nonpositive and the bound is vacuous) — so the critical box is the unique place
where both are free.  That is a second reason, independent of `log₂(4/3) + log₂(3/2) = 1`, that this
is the right box.

`lambda_one_ge_half` is the lower Minkowski bound in the same currency: two forms in the critical
box force `λ₁ ≥ 1/2`, i.e. certification in the box and a record-low approximation at the same date
exclude each other, quantitatively.  It is proved from the determinant cap (`TShift.det_cap`), and
one thing is worth recording: it is *the same inequality* as the transfer at content `1`.  The
Minkowski bound `λ₁λ₂ ≥ 1/2` and Proposition 1 at `P = 1` are two readings of the one Cramer
identity, so this clause adds a statement, not an estimate.

## κ-discipline

Everything in §1–§4 lives **at** `θ = 2/3`, where `TShift.kappa` equals `1`
(`TShift.kappa_two_thirds`).  `le_distToNearestInt_of_uniformFloor` says this out loud: the uniform
floor gives `‖D·(3/2)ⁿ‖ ≥ c·(2/3)ⁿ` for every multiplier `D ≤ β(3/2)ⁿ` — the boundary rate, not a
rate `> 2/3`.  So even a complete proof of the two-form ask would not settle
`TShift.TShiftProblem`; it would settle the uniform floor, which is the same problem in other words.
And nothing here constructs a form at any date beyond the free one: `forms_of_floor` is conditional,
and its hypothesis is the open statement.

## 2. The escape window

The second chapter is unconditional.  If `‖D(3/2)ⁿ‖ < 1/5` at two consecutive dates then
`2m_{n+1} = 3m_n` exactly (`TShift.cascade_step`), so a run of such dates forces
`2^{run} ∣ m_{n₀}` (`TShift.cascade_dvd`) — both imported from `TShift/FreeSojourn.lean`, at general
multiplier `D`, and not restated here.  With `m_{n₀} ≥ 1` (`mD_pos`) that divisibility is a
**window**:

  `escape_of_not_two_pow_dvd` — `2^k ∤ m_{n₀}` gives a date in `[n₀, n₀+k]` with `‖D(3/2)ⁿ‖ ≥ 1/5`;
  `escape_in_window`         — the first escape date `e(n₀)` obeys `e(n₀) ≤ n₀ + v₂(m_{n₀}) + 1`;
  `escape_in_window_logb`    — hence `e(n₀) ≤ (1 + log₂(3/2))·n₀ + log₂D + 2`.

The `v₂` form is exact and integral; the logarithmic form is the one the report quotes, and the
`O(1)` in it is `2`.  `escape_sanity` shows the `v₂` bound is attained: at `D = 5`, `n₀ = 3` the
nearest integer is `17`, so `v₂ = 0` and the window is `[3, 4]` — and indeed `‖5(3/2)³‖ = 1/8 < 1/5`
while `‖5(3/2)⁴‖ = 5/16 ≥ 1/5`.

`no_all_dates_smallness` is the ceiling this puts on single-hypothesis routes: for every `θ₀ < 1`
and every constant, `‖D(3/2)ⁿ‖ > c·θ₀ⁿ` at infinitely many dates.  So "smallness at all dates" is
not merely incompatible with `2/3` — it is incompatible with every geometric rate, for free.  In
κ-terms this is a *limsup* statement and therefore no step at all towards the problem, which asks
for a floor at every date; it is recorded here precisely so that limsup-shaped proposals can be
priced against something free.

## What is not claimed

No general Minkowski second theorem and no geometry-of-numbers layer: `forms_of_floor` is a bespoke
two-dimensional argument, and the only Minkowski input is the determinant cap already in the corpus.
No holonomy bound and no cited axiom of any kind.  The threshold `1/5` is not claimed optimal: the
sharp height for the same mechanism is Dubickas's `limsup ≥ (3 − T(2/3))/12 = 0.238117…` ([Dub06]),
which is a *height*, not a rate, and is not formalized here — nor is it to be confused with
`log²(3/2)/log 2 = 0.237182`, the exponent behind `TShift.thetaFree` (report N-note: adjacent to
three decimals, conceptually unrelated).  Nothing here proves an instance of the T-shift problem.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide` on `ℚ`/`ℝ` (the sanity instance goes through `norm_num`).

## Claim level

Formalization.  §1's equivalence is the plan's D1 made machine-checkable, and its two constants are
new only in the sense that no one had reason to write them down; the escape window of §2 is, as far
as the plan's sweeps found, the first effective form of the cascade's consequence in print or in
this corpus (the neighbouring statements are `RB/DubickasFloor.lean`'s word-complexity floors and
`TShift/FreeSojourn.lean`'s sojourn cap, both disjoint from a multiplier-native window).

## References

* `plans/plan-Tshift-S10.html` §1.4 (D1, D2), §2.2 (targets T1–T3, T6–T8), §3 (this file).
* `plans/note-Tshift-S10-WP0.html` §1 (Minkowski's second theorem verified as
  `λ₁λ₂ ∈ [1/2, 1]` at every date `n ≤ 20 000`; two forms in the unblown box at 21.2% of dates),
  §4 (the `v₂` window, verified at every `n₀ ≤ 20 000` for `D ∈ {1, 5, 19}`).
* `plans/note-Tshift-S10-WPC.html` §1 (what the family lane can pay for the box: the within-family
  ceiling `θ ∈ [0.4964, 0.5366]`, below the free `1/2`).
* `report-Tshift.html` §1.5–1.6 (the free rung, the rate-free branch), S10, N3 (the free zone
  `p > q²`, re-derived here as `critical_box_base`/`critical_box_base_le_one`).
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308 — the construction whose forms live in this box.
* [Dub06] A. Dubickas, *Arithmetical properties of powers of algebraic numbers*, Bull. London Math.
  Soc. **38** (2006), 70–80 — the sharp limsup `0.238117…`, not claimed here.
-/

namespace TShift

open Real

/-! ## 1. The critical box

`Λ` is the size of the forms and `B` the size of their second coefficients, exactly as in
`TShift.MultiplierTransfer`; `X = 2ⁿ`, `Y = 3ⁿ` are the columns. -/

/-- **T1 — the criticality certificate.**  At the `2/3`-critical parameters the box volume is the
determinant:

`(4/3)ⁿ · (3/2)ⁿ = 2ⁿ = det L_n`,

which is `log₂(4/3) + log₂(3/2) = 1` written multiplicatively.  Everything §1 proves is a reading of
this one identity: the demand box of a Padé construction at `θ = 2/3` is exactly Minkowski-critical,
so neither direction of the two-form ⇔ floor equivalence has room to hide a loss. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem critical_box_exact (n : ℕ) : ((4 : ℚ) / 3) ^ n * ((3 : ℚ) / 2) ^ n = 2 ^ n := by
  rw [← mul_pow]; norm_num

/-- The critical-box identity over `ℝ`, the form the estimates below consume. -/
@[category API, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem critical_box_real (n : ℕ) : ((4 : ℝ) / 3) ^ n * ((3 : ℝ) / 2) ^ n = 2 ^ n := by
  rw [← mul_pow]; norm_num

/-- **The critical box at a general base.**  For columns `X = qⁿ`, `Y = pⁿ` the lattice has
determinant `qⁿ` and the box demanded at the threshold rate is `(Λ, B) = ((q²/p)ⁿ, (p/q)ⁿ)`, again
of volume exactly the determinant. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem critical_box_base {p q : ℚ} (hp : 0 < p) (n : ℕ) :
    (q ^ 2 / p) ^ n * (p / q) ^ n = q ^ n := by
  rw [← mul_pow, show q ^ 2 / p * (p / q) = q by field_simp]

/-- **The free zone** (report N3, from the height side): the critical *size* slot is bounded, so the
second form costs nothing, exactly when `q² ≤ p`.  At `p/q = 3/2` it is not (`9 > 3`), which is why
`(3/2)ⁿ` is hard and, say, `(5/2)ⁿ` is not. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem critical_box_base_le_one {p q : ℚ} (hp : 0 < p) (h : q ^ 2 ≤ p) (n : ℕ) :
    (q ^ 2 / p) ^ n ≤ 1 :=
  pow_le_one₀ (by positivity) (by rw [div_le_one hp]; exact h)

/-! ## 2. One form is free; the floor buys the second -/

/-- **The first form costs nothing.**  Dirichlet's pigeonhole, read in two columns: for every
`N ≥ 1` there is a form `ℓ = a·X + b·Y` with `0 < b ≤ N` and `|ℓ| ≤ X/(N+1)`.  At `N = ⌊B⌋` and
`Λ·B = X` this is a nonzero point of the critical box — Minkowski's *first* theorem for this box,
with no hypothesis on the columns beyond `X > 0`. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem exists_form_in_box {X Y : ℤ} (hX : 0 < X) {N : ℕ} (hN : 0 < N) :
    ∃ a b : ℤ, 0 < b ∧ b ≤ (N : ℤ) ∧
      |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| ≤ (X : ℝ) / ((N : ℝ) + 1) := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  obtain ⟨j, k, hk0, hkN, hle⟩ := Real.exists_int_int_abs_mul_sub_le ((Y : ℝ) / (X : ℝ)) hN
  refine ⟨-j, k, hk0, hkN, ?_⟩
  have hid : (((-j : ℤ)) : ℝ) * (X : ℝ) + (k : ℝ) * (Y : ℝ)
      = ((k : ℝ) * ((Y : ℝ) / (X : ℝ)) - (j : ℝ)) * (X : ℝ) := by
    field_simp
    push_cast
    ring
  rw [hid, abs_mul, abs_of_pos hXR]
  calc |(k : ℝ) * ((Y : ℝ) / (X : ℝ)) - (j : ℝ)| * (X : ℝ)
      ≤ (1 / ((N : ℝ) + 1)) * (X : ℝ) := mul_le_mul_of_nonneg_right hle hXR.le
    _ = (X : ℝ) / ((N : ℝ) + 1) := by ring

/-- **No floor above the critical box.**  A uniform floor `S` over the coefficient range `B` forces
`S < X/B`: the free form of `exists_form_in_box` is itself below `X/B`.  So the critical box is not
one choice among many — it is where the floor hypothesis becomes consistent, and `S = c·X/B` with
`c ≤ 1` is the only shape a floor can have. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem floor_le_critical {X Y : ℤ} (hX : 0 < X) {B S : ℝ} (hB : 1 ≤ B)
    (hfloor : ∀ a b : ℤ, b ≠ 0 → |(b : ℝ)| ≤ B →
      S ≤ |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|) :
    S < (X : ℝ) / B := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB
  obtain ⟨a, b, hbpos, hbN, hsize⟩ := exists_form_in_box (Y := Y) hX (Nat.floor_pos.mpr hB)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hbB : |(b : ℝ)| ≤ B := by
    rw [abs_of_pos hbR]
    calc (b : ℝ) ≤ ((⌊B⌋₊ : ℤ) : ℝ) := by exact_mod_cast hbN
      _ = (⌊B⌋₊ : ℝ) := by push_cast; ring
      _ ≤ B := Nat.floor_le hB0.le
  have h1 := hfloor a b hbpos.ne' hbB
  have h2 : (X : ℝ) / ((⌊B⌋₊ : ℝ) + 1) < (X : ℝ) / B := by
    apply div_lt_div_of_pos_left hXR hB0
    exact Nat.lt_floor_add_one B
  linarith [hsize]

/-- **T2 — the converse of the transfer: a uniform floor produces the second form.**  Suppose every
form with `0 < |b| ≤ B` has `|ℓ| ≥ S`.  Then there are **two independent** forms with

`|ℓᵢ| ≤ X/B`   and   `|bᵢ| ≤ X/S + 1`,

i.e. the critical box blown up by `1/c` in the coefficient slot alone, where `S = c·X/B`.  Two
pigeonhole forms do the job: one at `N₁ = ⌊B⌋`, which lands in the box, and one at `N₂ = ⌈X/S⌉`,
which lands strictly *below* the floor.  Independence is then forced arithmetically — if the two
were dependent, the Bézout combination `s·u + t·v` would be a form whose coefficient is
`gcd(b₁, b₂) ≤ b₁ ≤ B` and whose size is at most `|ℓ₂| < S`, contradicting the floor.  No convexity,
no reduction theory, and the blow-up is one-sided, which Minkowski's second theorem does not
give. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem forms_of_floor {X Y : ℤ} (hX : 0 < X) {B S : ℝ} (hB : 1 ≤ B) (hS : 0 < S)
    (hfloor : ∀ a b : ℤ, b ≠ 0 → |(b : ℝ)| ≤ B →
      S ≤ |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|) :
    Nonempty (TwoForms X Y 1 ((X : ℝ) / B) ((X : ℝ) / S + 1)) := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB
  have hSB : S < (X : ℝ) / B := floor_le_critical hX hB hfloor
  have hBS : B < (X : ℝ) / S := by
    rw [lt_div_iff₀ hS]
    rw [lt_div_iff₀ hB0] at hSB
    linarith
  -- the first form: Dirichlet at `N₁ = ⌊B⌋`
  obtain ⟨a₁, b₁, hb₁pos, hb₁N, hsize₁⟩ := exists_form_in_box (Y := Y) hX (Nat.floor_pos.mpr hB)
  have hb₁R : (0 : ℝ) < (b₁ : ℝ) := by exact_mod_cast hb₁pos
  have hb₁B : |(b₁ : ℝ)| ≤ B := by
    rw [abs_of_pos hb₁R]
    calc (b₁ : ℝ) ≤ ((⌊B⌋₊ : ℤ) : ℝ) := by exact_mod_cast hb₁N
      _ = (⌊B⌋₊ : ℝ) := by push_cast; ring
      _ ≤ B := Nat.floor_le hB0.le
  have hℓ₁ : |(a₁ : ℝ) * (X : ℝ) + (b₁ : ℝ) * (Y : ℝ)| ≤ (X : ℝ) / B := by
    refine hsize₁.trans ?_
    apply div_le_div_of_nonneg_left hXR.le hB0
    exact (Nat.lt_floor_add_one B).le
  -- the second form: Dirichlet at `N₂ = ⌈X/S⌉`, which lands strictly below the floor
  have hXS : (0 : ℝ) < (X : ℝ) / S := by positivity
  obtain ⟨a₂, b₂, hb₂pos, hb₂N, hsize₂⟩ := exists_form_in_box (Y := Y) hX (Nat.ceil_pos.mpr hXS)
  have hb₂R : (0 : ℝ) < (b₂ : ℝ) := by exact_mod_cast hb₂pos
  have hℓ₂ : |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| < S := by
    refine hsize₂.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have h1 : (X : ℝ) / S ≤ (⌈(X : ℝ) / S⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hS] at h1
    nlinarith
  have hb₂B : |(b₂ : ℝ)| ≤ (X : ℝ) / S + 1 := by
    rw [abs_of_pos hb₂R]
    calc (b₂ : ℝ) ≤ ((⌈(X : ℝ) / S⌉₊ : ℤ) : ℝ) := by exact_mod_cast hb₂N
      _ = (⌈(X : ℝ) / S⌉₊ : ℝ) := by push_cast; ring
      _ ≤ (X : ℝ) / S + 1 := (Nat.ceil_lt_add_one hXS.le).le
  -- independence: a Bézout combination of two dependent forms would break the floor
  have hdet : a₁ * b₂ ≠ a₂ * b₁ := by
    intro hdep
    have hcross : b₁ * (a₂ * X + b₂ * Y) = b₂ * (a₁ * X + b₁ * Y) := by
      linear_combination (-X) * hdep
    set g : ℤ := (Int.gcd b₁ b₂ : ℤ) with hgdef
    have hgpos : 0 < g := by
      rw [hgdef]
      exact_mod_cast Int.gcd_pos_iff.mpr (Or.inl hb₁pos.ne')
    have hbez : g = b₁ * Int.gcdA b₁ b₂ + b₂ * Int.gcdB b₁ b₂ := Int.gcd_eq_gcd_ab b₁ b₂
    set s : ℤ := Int.gcdA b₁ b₂ with hs
    set t : ℤ := Int.gcdB b₁ b₂ with ht
    set a₃ : ℤ := s * a₁ + t * a₂ with ha₃
    have hℓ₃ : a₃ * X + g * Y = s * (a₁ * X + b₁ * Y) + t * (a₂ * X + b₂ * Y) := by
      rw [ha₃, hbez]; ring
    have hkey : b₂ * (a₃ * X + g * Y) = g * (a₂ * X + b₂ * Y) := by
      rw [hℓ₃, hbez]
      linear_combination (-s) * hcross
    have hg_le_b₁ : g ≤ b₁ := Int.le_of_dvd hb₁pos (by rw [hgdef]; exact Int.gcd_dvd_left _ _)
    have hg_le_b₂ : g ≤ b₂ := Int.le_of_dvd hb₂pos (by rw [hgdef]; exact Int.gcd_dvd_right _ _)
    have habs : |a₃ * X + g * Y| ≤ |a₂ * X + b₂ * Y| := by
      have h1 : b₂ * |a₃ * X + g * Y| = g * |a₂ * X + b₂ * Y| := by
        have hc := congrArg (fun z : ℤ => |z|) hkey
        simp only [abs_mul, abs_of_pos hb₂pos, abs_of_pos hgpos] at hc
        exact hc
      have h2 : g * |a₂ * X + b₂ * Y| ≤ b₂ * |a₂ * X + b₂ * Y| :=
        mul_le_mul_of_nonneg_right hg_le_b₂ (abs_nonneg _)
      exact le_of_mul_le_mul_left (by linarith) hb₂pos
    have hfl := hfloor a₃ g hgpos.ne' (by
      rw [abs_of_pos (by exact_mod_cast hgpos : (0 : ℝ) < (g : ℝ))]
      calc (g : ℝ) ≤ (b₁ : ℝ) := by exact_mod_cast hg_le_b₁
        _ ≤ |(b₁ : ℝ)| := le_abs_self _
        _ ≤ B := hb₁B)
    have hcast : |(a₃ : ℝ) * (X : ℝ) + (g : ℝ) * (Y : ℝ)|
        ≤ |(a₂ : ℝ) * (X : ℝ) + (b₂ : ℝ) * (Y : ℝ)| := by
      have h1 : ((|a₃ * X + g * Y| : ℤ) : ℝ) ≤ ((|a₂ * X + b₂ * Y| : ℤ) : ℝ) := by
        exact_mod_cast habs
      rw [Int.cast_abs, Int.cast_abs] at h1
      push_cast at h1
      exact h1
    linarith
  exact ⟨{ a₁ := a₁, b₁ := b₁, Γ₁ := 1, a₂ := a₂, b₂ := b₂, Γ₂ := 1
           det := hdet
           dvd_a₁ := one_dvd _, dvd_b₁ := one_dvd _, dvd_a₂ := one_dvd _, dvd_b₂ := one_dvd _
           le_content₁ := by norm_num, le_content₂ := by norm_num
           size₁ := hℓ₁
           size₂ := hℓ₂.le.trans hSB.le
           coeff₁ := hb₁B.trans (by linarith)
           coeff₂ := hb₂B }⟩

/-! ## 3. The equivalence

The two statements the plan's D1 relates, each along the whole critical family `n ↦ (2ⁿ, 3ⁿ)`, and
each with one constant.  At a *single* date both are trivially true — a lattice has a shortest
vector, and two independent points exist in a big enough box — so the equivalence is a statement
about uniformity in `n`, which is what the word "uniform" in "uniform multiplier floor" carries. -/

/-- Weakening the box: a `TwoForms` witness survives enlarging the size and coefficient slots and
lowering the content bound.  (The box parameters occur only in `≤`-fields; this is bookkeeping.) -/
@[category API, AMS 11, ref "TshiftS10", group "tshift_s10"]
def TwoForms.mono {X Y : ℤ} {P Λ B P' Λ' B' : ℝ} (hP : P' ≤ P) (hΛ : Λ ≤ Λ') (hB : B ≤ B')
    (F : TwoForms X Y P Λ B) : TwoForms X Y P' Λ' B' :=
  { F with
    le_content₁ := hP.trans F.le_content₁
    le_content₂ := hP.trans F.le_content₂
    size₁ := F.size₁.trans hΛ
    size₂ := F.size₂.trans hΛ
    coeff₁ := F.coeff₁.trans hB
    coeff₂ := F.coeff₂.trans hB }

/-- **The uniform multiplier floor at `θ = 2/3`**, with constant `c` and coefficient-range factor
`β`: at every date, every form `a·2ⁿ + b·3ⁿ` with `0 < |b| ≤ β(3/2)ⁿ` has size at least `c(4/3)ⁿ`.
This is the T-shift statement made uniform over multipliers — see
`le_distToNearestInt_of_uniformFloor` — and it is open. -/
def UniformFloor (c β : ℝ) : Prop :=
  ∀ n : ℕ, ∀ a b : ℤ, b ≠ 0 → |(b : ℝ)| ≤ β * (3 / 2) ^ n →
    c * (4 / 3) ^ n ≤ |(a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n|

/-- **Two independent forms in the critical box** at every date, the box scaled by `η` in the size
slot and by `K` in the coefficient slot.  This is what S10's "concrete project" asks a holonomy
bound to certify. -/
def TwoFormsInBox (η K : ℝ) : Prop :=
  ∀ n : ℕ, Nonempty (TwoForms ((2 : ℤ) ^ n) ((3 : ℤ) ^ n) 1 (η * (4 / 3) ^ n) (K * (3 / 2) ^ n))

/-- **The floor produces the forms** (T2 along the critical family).  A floor with constant `c` and
range factor `β` gives two independent forms with sizes `≤ (1/β)·(4/3)ⁿ` and coefficients
`≤ (1/c + 1)·(3/2)ⁿ`: the size slot even *shrinks* by `1/β`, and the whole cost of the converse is
the factor `1/c + 1` on the coefficients. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem twoFormsInBox_of_uniformFloor {c β : ℝ} (hc : 0 < c) (hβ : 1 ≤ β) (h : UniformFloor c β) :
    TwoFormsInBox (1 / β) (1 / c + 1) := by
  intro n
  have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hcast2 : (((2 : ℤ) ^ n : ℤ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  obtain ⟨F⟩ := forms_of_floor (X := (2 : ℤ) ^ n) (Y := (3 : ℤ) ^ n)
      (B := β * (3 / 2) ^ n) (S := c * (4 / 3) ^ n) (by positivity)
      (by nlinarith) (by positivity)
      (fun a b hb hbB => by
        have hfl := h n a b hb hbB
        push_cast
        exact hfl)
  have hΛ : (((2 : ℤ) ^ n : ℤ) : ℝ) / (β * (3 / 2) ^ n) = 1 / β * (4 / 3) ^ n := by
    rw [hcast2, div_eq_iff (by positivity : β * (3 / 2 : ℝ) ^ n ≠ 0),
      show 1 / β * (4 / 3 : ℝ) ^ n * (β * (3 / 2) ^ n)
        = β / β * ((4 / 3 : ℝ) ^ n * (3 / 2) ^ n) by ring,
      div_self hβ0.ne', one_mul, critical_box_real]
  have hB2 : (((2 : ℤ) ^ n : ℤ) : ℝ) / (c * (4 / 3) ^ n) = 1 / c * (3 / 2) ^ n := by
    rw [hcast2, div_eq_iff (by positivity : c * (4 / 3 : ℝ) ^ n ≠ 0),
      show 1 / c * (3 / 2 : ℝ) ^ n * (c * (4 / 3) ^ n)
        = c / c * ((4 / 3 : ℝ) ^ n * (3 / 2) ^ n) by ring,
      div_self hc.ne', one_mul, critical_box_real]
  refine ⟨F.mono le_rfl (le_of_eq hΛ) ?_⟩
  rw [hB2]
  nlinarith [one_div_pos.mpr hc]

/-- **The forms produce the floor** (Proposition 1 at content `1`).  Two forms in the box scaled by
`(η, K)` give the floor with constant `(1 − ηβ)/K` at range factor `β` — positive exactly when
`ηβ < 1`, which is the `ε`-slack: the coefficient range times the form size must stay below the
determinant, or the transfer's `X − |b|·Λ` term dies. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem uniformFloor_of_twoFormsInBox {η K β : ℝ} (hK : 0 < K) (h : TwoFormsInBox η K) :
    UniformFloor ((1 - η * β) / K) β := by
  intro n a b hb hbB
  obtain ⟨F⟩ := h n
  have hη0 : 0 ≤ η := by
    by_contra hcon
    push Not at hcon
    have hsz := F.size₁
    have h43 : (0 : ℝ) < (4 / 3 : ℝ) ^ n := by positivity
    have hnn := abs_nonneg ((F.a₁ : ℝ) * (((2 : ℤ) ^ n : ℤ) : ℝ)
      + (F.b₁ : ℝ) * (((3 : ℤ) ^ n : ℤ) : ℝ))
    nlinarith
  have hcrit : (4 / 3 : ℝ) ^ n * (3 / 2 : ℝ) ^ n = 2 ^ n := critical_box_real n
  have h32pos : (0 : ℝ) < (3 / 2 : ℝ) ^ n := by positivity
  have ht := F.transfer (c := b) (by positivity) hb (-a)
  have habs : |(b : ℝ) * (((3 : ℤ) ^ n : ℤ) : ℝ) - (((-a : ℤ)) : ℝ) * (((2 : ℤ) ^ n : ℤ) : ℝ)|
      = |(a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n| := by
    push_cast
    rw [show (b : ℝ) * 3 ^ n - -(a : ℝ) * 2 ^ n = (a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n by ring]
  rw [habs] at ht
  have hcast2 : (((2 : ℤ) ^ n : ℤ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast2, one_mul] at ht
  have hb' : |(b : ℝ)| * (η * (4 / 3) ^ n) ≤ η * β * 2 ^ n :=
    calc |(b : ℝ)| * (η * (4 / 3) ^ n) ≤ (β * (3 / 2) ^ n) * (η * (4 / 3) ^ n) :=
          mul_le_mul_of_nonneg_right hbB (by positivity)
      _ = η * β * ((4 / 3) ^ n * (3 / 2) ^ n) := by ring
      _ = η * β * 2 ^ n := by rw [hcrit]
  have hkey : (1 - η * β) * (2 : ℝ) ^ n
      ≤ K * (3 / 2) ^ n * |(a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n| := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  refine le_of_mul_le_mul_right ?_ h32pos
  calc (1 - η * β) * (4 / 3 : ℝ) ^ n * (3 / 2) ^ n
      = (1 - η * β) * ((4 / 3 : ℝ) ^ n * (3 / 2) ^ n) := by ring
    _ = (1 - η * β) * (2 : ℝ) ^ n := by rw [hcrit]
    _ ≤ K * (3 / 2) ^ n * |(a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n| := hkey
    _ = |(a : ℝ) * 2 ^ n + (b : ℝ) * 3 ^ n| * K * (3 / 2) ^ n := by ring

/-- **T3 — the packaged equivalence.**  A uniform floor with some positive constant and some range
factor `β > 1` exists **iff** two independent forms exist at every date in the critical box scaled
by some `η < 1` in the size slot and some `K` in the coefficient slot.

This is D1 machine-checked: S10's two-form ask is a restatement of the uniform multiplier floor at
`θ = 2/3`, with no exponential loss in either direction — the transported constants are `η = 1/β`,
`K = 1/c + 1` one way and `c = (1 − ηβ)/K`, `β = (1 + 1/η)/2` the other.  The `ε`-slack is the
single factor `β > 1` versus `η < 1`, and it is forced: the converse needs box volume `≥ det`, the
forward direction needs `≤ det`.  Nothing about the reformulation is easier than the floor; what it
buys is vocabulary — a *rank* statement about one lattice per date. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem floor_iff_forms :
    (∃ c β : ℝ, 0 < c ∧ 1 < β ∧ UniformFloor c β) ↔
      (∃ η K : ℝ, 0 < η ∧ η < 1 ∧ 0 < K ∧ TwoFormsInBox η K) := by
  constructor
  · rintro ⟨c, β, hc, hβ, h⟩
    refine ⟨1 / β, 1 / c + 1, by positivity, ?_, by positivity,
      twoFormsInBox_of_uniformFloor hc hβ.le h⟩
    rw [div_lt_one (by linarith)]
    exact hβ
  · rintro ⟨η, K, hη, hη1, hK, h⟩
    have hinv : 1 < 1 / η := by rw [lt_div_iff₀ hη]; linarith
    have hηβ : η * ((1 + 1 / η) / 2) = (η + 1) / 2 := by
      have h1 : η * (1 / η) = 1 := by field_simp
      linear_combination h1 / 2
    refine ⟨(1 - η * ((1 + 1 / η) / 2)) / K, (1 + 1 / η) / 2, ?_, by linarith,
      uniformFloor_of_twoFormsInBox hK h⟩
    rw [hηβ]
    exact div_pos (by linarith) hK

/-! ## 4. What the floor says about the orbit, and the lower Minkowski bound -/

/-- **The floor, in the orbit's language.**  A uniform floor with constant `c` gives

`‖D·(3/2)ⁿ‖ ≥ c·(2/3)ⁿ`

at every date and for every multiplier `D ≤ β(3/2)ⁿ` — the rate `2/3` **exactly**.  Since
`TShift.kappa (2/3) = 1`, this is the boundary of `TShift.TShiftProblem`'s demand `θ > 2/3` and not
inside it: the critical box is calibrated to the threshold, so §1's equivalence relates two forms of
the *same* open problem rather than reducing it. -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem le_distToNearestInt_of_uniformFloor {c β : ℝ} (h : UniformFloor c β) {D : ℕ} (hD : 0 < D)
    {n : ℕ} (hDn : (D : ℝ) ≤ β * (3 / 2) ^ n) :
    c * (2 / 3) ^ n ≤ distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hDne : ((D : ℤ)) ≠ 0 := by exact_mod_cast hD.ne'
  have hfl := h n (-round ((D : ℝ) * (3 / 2) ^ n)) (D : ℤ) hDne (by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((D : ℤ) : ℝ))]
    push_cast
    exact hDn)
  have hid : ((-round ((D : ℝ) * (3 / 2) ^ n) : ℤ) : ℝ) * 2 ^ n + ((D : ℤ) : ℝ) * 3 ^ n
      = (2 : ℝ) ^ n * ((D : ℝ) * (3 / 2) ^ n - round ((D : ℝ) * (3 / 2) ^ n)) := by
    push_cast
    rw [div_pow]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos h2] at hfl
  rw [distToNearestInt]
  refine le_of_mul_le_mul_right ?_ h2
  calc c * (2 / 3 : ℝ) ^ n * 2 ^ n = c * (4 / 3 : ℝ) ^ n := by
        rw [mul_assoc c, ← mul_pow]
        norm_num
    _ ≤ (2 : ℝ) ^ n * |(D : ℝ) * (3 / 2) ^ n - round ((D : ℝ) * (3 / 2) ^ n)| := hfl
    _ = |(D : ℝ) * (3 / 2) ^ n - round ((D : ℝ) * (3 / 2) ^ n)| * 2 ^ n := by ring

/-- **The lower Minkowski bound** (`λ₁λ₂ ≥ 1/2` in the critical norm).  If two independent forms sit
in the critical box `Λ·B = X`, then no form with `0 < |b| ≤ B/2` has size below `Λ/2`: certifying
two forms at a date and holding a record-low approximation at the same date are mutually exclusive.

Proof: the pair `(a, b)` is independent from at least one of the two forms, and the determinant cap
`TShift.det_cap` applied to that pair reads `X ≤ |b'|·|ℓ| + |b|·|ℓ'| ≤ B·|ℓ| + (B/2)·Λ`, i.e.
`|ℓ| ≥ Λ/2` after `Λ·B = X`.  Note that this is the transfer's own inequality at content `1` — the
Minkowski bound and Proposition 1 with `P = 1` are two readings of the same Cramer identity — so
what is new here is the reading, not the estimate. -/
@[category research solved, AMS 11, ref "TshiftS10", group "tshift_s10"]
theorem lambda_one_ge_half {X Y : ℤ} (hX : 0 < X) {Λ B : ℝ} (hB : 0 < B)
    (hcrit : Λ * B = (X : ℝ)) (F : TwoForms X Y 1 Λ B) {a b : ℤ} (hb : b ≠ 0)
    (hbB : |(b : ℝ)| ≤ B / 2) :
    Λ / 2 ≤ |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  -- at least one of the two forms is independent from `(a, b)`
  have hind : a * F.b₁ ≠ F.a₁ * b ∨ a * F.b₂ ≠ F.a₂ * b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine F.det ?_
    have hz : b * (F.a₁ * F.b₂ - F.a₂ * F.b₁) = 0 := by
      linear_combination (-F.b₂) * h1 + F.b₁ * h2
    have h3 := (mul_eq_zero.mp hz).resolve_left hb
    linarith [sub_eq_zero.mp h3]
  -- the determinant cap, at the pair that is independent
  have main : ∀ a' b' : ℤ, a * b' ≠ a' * b → |(b' : ℝ)| ≤ B →
      |(a' : ℝ) * (X : ℝ) + (b' : ℝ) * (Y : ℝ)| ≤ Λ →
      Λ / 2 ≤ |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| := by
    intro a' b' hdet hb'B hΛ'
    have hone : (1 : ℝ) ≤ |(a : ℝ) * (b' : ℝ) - (a' : ℝ) * (b : ℝ)| := by
      have hne : a * b' - a' * b ≠ 0 := sub_ne_zero.mpr hdet
      have h0 : (1 : ℤ) ≤ |a * b' - a' * b| := Int.one_le_abs hne
      have hc : ((1 : ℤ) : ℝ) ≤ ((|a * b' - a' * b| : ℤ) : ℝ) := by exact_mod_cast h0
      rw [Int.cast_abs] at hc
      push_cast at hc
      exact hc
    have hcap : |(a : ℝ) * (b' : ℝ) - (a' : ℝ) * (b : ℝ)| * (X : ℝ)
        ≤ |(b' : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|
          + |(b : ℝ)| * |(a' : ℝ) * (X : ℝ) + (b' : ℝ) * (Y : ℝ)| := by
      have h1 := det_cap X Y a b a' b'
      have h2 : ((|a * b' - a' * b| * |X| : ℤ) : ℝ)
          ≤ ((|b'| * |a * X + b * Y| + |b| * |a' * X + b' * Y| : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast [Int.cast_abs] at h2
      rwa [abs_of_pos hXR] at h2
    have hL : (0 : ℝ) ≤ |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| := abs_nonneg _
    have hL' : (0 : ℝ) ≤ |(a' : ℝ) * (X : ℝ) + (b' : ℝ) * (Y : ℝ)| := abs_nonneg _
    have h2 : |(b' : ℝ)| * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)|
        ≤ B * |(a : ℝ) * (X : ℝ) + (b : ℝ) * (Y : ℝ)| := mul_le_mul_of_nonneg_right hb'B hL
    have h3 : |(b : ℝ)| * |(a' : ℝ) * (X : ℝ) + (b' : ℝ) * (Y : ℝ)| ≤ B / 2 * Λ :=
      mul_le_mul hbB hΛ' hL' (by linarith)
    have h4 : (X : ℝ) ≤ |(a : ℝ) * (b' : ℝ) - (a' : ℝ) * (b : ℝ)| * (X : ℝ) := by
      nlinarith
    refine le_of_mul_le_mul_left ?_ hB
    rw [← hcrit] at h4
    nlinarith
  rcases hind with h | h
  · exact main F.a₁ F.b₁ h (F.coeff₁) F.size₁
  · exact main F.a₂ F.b₂ h (F.coeff₂) F.size₂

/-! ## 5. The escape window

Unconditional, and the one place where this file says something about specific dates.  The cascade
`TShift.cascade_step`/`TShift.cascade_dvd` is imported from `TShift/FreeSojourn.lean` at general
multiplier `D`; all that is added here is the positivity of `m_n(D)` and the reading of the
divisibility as a window. -/

/-- `m_n(D) = round(D(3/2)ⁿ) ≥ 1` for every `D ≥ 1`: the integer the cascade divides is nonzero,
which is the only extra ingredient the window needs. -/
@[category API, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem mD_pos {D : ℕ} (hD : 0 < D) (n : ℕ) : 0 < mD D n := by
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h1 : (1 : ℝ) ≤ (D : ℝ) * (3 / 2) ^ n := by nlinarith
  have h2 : (1 : ℤ) ≤ mD D n := by
    rw [mD, round_eq]
    refine Int.le_floor.mpr ?_
    push_cast
    linarith
  omega

/-- **The window, in divisibility form.**  If `2^k` does not divide `m_{n₀}(D)`, some date in
`[n₀, n₀+k]` has `‖D(3/2)ⁿ‖ ≥ 1/5`: otherwise the cascade would force `2^k ∣ m_{n₀}(D)`. -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem escape_of_not_two_pow_dvd {D n₀ k : ℕ} (h : ¬ ((2 : ℤ) ^ k ∣ mD D n₀)) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + k ∧ 1 / 5 ≤ distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  have hdvd := cascade_dvd (D := D) (a := n₀) (b := n₀ + k) (by omega)
    (fun j hj1 hj2 => by
      rw [abs_deltaD_eq_dist]
      exact hcon j hj1 hj2)
  simpa using hdvd

/-- **T6 — the escape window.**  The first date `e(n₀) ≥ n₀` with `‖D(3/2)ⁿ‖ ≥ 1/5` satisfies

`e(n₀) ≤ n₀ + v₂(m_{n₀}(D)) + 1`,

so the named window is `[n₀, n₀ + v₂(m_{n₀}) + 1]`.  Exact, integral, and with no `O(1)` to pin
down: the escape is forced by the 2-adic valuation of one nearest integer.  Verified numerically at
every `n₀ ≤ 20 000` for `D ∈ {1, 5, 19}` (`note-Tshift-S10-WP0.html` §4), where the measured worst
sojourn is `10` against valuations that never exceed `17`; `escape_sanity` gives a date where the
bound is attained.  The `1/5` is the cascade's threshold, not the sharp one — see the module
docstring on [Dub06]. -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem escape_in_window {D : ℕ} (hD : 0 < D) (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ n ≤ n₀ + padicValInt 2 (mD D n₀) + 1 ∧
      1 / 5 ≤ distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  refine escape_of_not_two_pow_dvd (k := padicValInt 2 (mD D n₀) + 1) (fun hdvd => ?_)
  have hne : mD D n₀ ≠ 0 := (mD_pos hD n₀).ne'
  have h2 : ((2 : ℕ) : ℤ) ^ (padicValInt 2 (mD D n₀) + 1) ∣ mD D n₀ := by
    push_cast
    exact hdvd
  rcases (padicValInt_dvd_iff_of_ne_one (p := 2) (by norm_num) _ _).mp h2 with h | h
  · exact hne h
  · omega

/-- **The window in the logarithmic form the report quotes**, with the `O(1)` named:

`e(n₀) ≤ (1 + log₂(3/2))·n₀ + log₂ D + 2`,

i.e. a slope `1 + κ_free = 1.5849625…` and an additive constant `2`.  It follows from the `v₂` form
because `2^{v₂(m)} ≤ m ≤ 2·D(3/2)^{n₀}`. -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem escape_in_window_logb {D : ℕ} (hD : 0 < D) (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ (n : ℝ) ≤ (1 + Real.logb 2 (3 / 2)) * n₀ + Real.logb 2 D + 2 ∧
      1 / 5 ≤ distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  obtain ⟨n, hn1, hn2, hn3⟩ := escape_in_window hD n₀
  refine ⟨n, hn1, ?_, hn3⟩
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n₀ := one_le_pow₀ (by norm_num)
  have hmpos := mD_pos hD n₀
  have hdvd : (2 : ℤ) ^ padicValInt 2 (mD D n₀) ∣ mD D n₀ := by
    have h := padicValInt_dvd (p := 2) (mD D n₀)
    push_cast at h
    exact h
  have h1 : ((2 : ℝ)) ^ padicValInt 2 (mD D n₀) ≤ (mD D n₀ : ℝ) := by
    have h := Int.le_of_dvd hmpos hdvd
    exact_mod_cast h
  have hround : (mD D n₀ : ℝ) ≤ (D : ℝ) * (3 / 2) ^ n₀ + 1 / 2 := by
    have h := abs_le.mp (abs_sub_round ((D : ℝ) * (3 / 2) ^ n₀))
    rw [mD]
    linarith [h.1]
  have h2 : ((2 : ℝ)) ^ padicValInt 2 (mD D n₀) ≤ 2 * ((D : ℝ) * (3 / 2) ^ n₀) := by
    nlinarith
  have hlog : (padicValInt 2 (mD D n₀) : ℝ)
      ≤ 1 + Real.logb 2 D + n₀ * Real.logb 2 (3 / 2) := by
    have hb : (1 : ℝ) < 2 := by norm_num
    have h3 := Real.logb_le_logb_of_le hb (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at h3
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one hb] at h3
    linarith
  have hn2' : (n : ℝ) ≤ (n₀ : ℝ) + (padicValInt 2 (mD D n₀) : ℝ) + 1 := by
    exact_mod_cast hn2
  linarith

/-! ## 6. The ceiling of the single-hypothesis routes -/

/-- Infinitely many escape dates, at every multiplier: the window applies from every `n₀`. -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem escape_frequently {D : ℕ} (hD : 0 < D) :
    ∃ᶠ n in Filter.atTop, 1 / 5 ≤ distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  rw [Filter.frequently_atTop]
  intro n₀
  obtain ⟨n, hn1, _, hn3⟩ := escape_in_window hD n₀
  exact ⟨n, hn1, hn3⟩

/-- **T7 — the death of all-dates smallness, at every rate.**  For every `θ₀ < 1` and every constant
`c`, `‖D(3/2)ⁿ‖ > c·θ₀ⁿ` at infinitely many dates.  So a hypothesis of the form "`‖D(3/2)ⁿ‖ ≤ c θ₀ⁿ`
from some date on" is absurd for *every* geometric rate, not just below `2/3` — which is the theorem
side of the report's `θₙ → 1`.

κ-discipline: this is a `limsup`-shaped statement and therefore *no* progress on
`TShift.TShiftProblem`, which asks for a floor at every date; it is the yardstick against which
limsup-, run-cap- and exception-count-shaped proposals must be priced (plan D4, class `(β)`). -/
@[category research solved, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem no_all_dates_smallness {D : ℕ} (hD : 0 < D) {θ₀ c : ℝ} (hθ₀ : 0 ≤ θ₀) (hθ₁ : θ₀ < 1) :
    ∃ᶠ n in Filter.atTop, c * θ₀ ^ n < distToNearestInt ((D : ℝ) * (3 / 2) ^ n) := by
  have hten : Filter.Tendsto (fun n : ℕ => c * θ₀ ^ n) Filter.atTop (nhds (c * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ₀ hθ₁).const_mul c
  rw [mul_zero] at hten
  have hev : ∀ᶠ n : ℕ in Filter.atTop, c * θ₀ ^ n < 1 / 5 :=
    hten.eventually_lt_const (by norm_num)
  exact (escape_frequently hD).mp (hev.mono fun n hn h => lt_of_lt_of_le hn h)

/-! ## 7. Orientation check -/

/-- **T8 — the window is attained.**  At the period-2 multiplier `D₂ = 3² − 2² = 5` and `n₀ = 3`:
the nearest integer is `m₃(5) = 17`, odd, so `v₂ = 0` and `escape_in_window` promises an escape date
in `[3, 4]`.  And indeed `‖5(3/2)³‖ = 1/8 < 1/5` while `‖5(3/2)⁴‖ = 5/16 ≥ 1/5` — the bound is
tight, and the direction of the inequality is the one claimed. -/
@[category test, AMS 11 37, ref "TshiftS10", group "tshift_s10"]
theorem escape_sanity :
    mD 5 3 = 17 ∧ padicValInt 2 (mD 5 3) = 0 ∧
      distToNearestInt ((5 : ℝ) * (3 / 2) ^ 3) = 1 / 8 ∧
      distToNearestInt ((5 : ℝ) * (3 / 2) ^ 4) = 5 / 16 := by
  have hm : mD 5 3 = 17 := by
    rw [mD, round_eq, show ((5 : ℕ) : ℝ) * (3 / 2) ^ 3 + 1 / 2 = 139 / 8 by norm_num,
      Int.floor_eq_iff]
    norm_num
  have h17 : ((17 : ℤ)).natAbs = 17 := by norm_num
  refine ⟨hm, ?_, ?_, ?_⟩
  · rw [hm, padicValInt, h17]
    exact padicValNat.eq_zero_of_not_dvd (by norm_num)
  · rw [distToNearestInt, show ((5 : ℝ)) * (3 / 2) ^ 3 = 135 / 8 by norm_num,
      show round ((135 : ℝ) / 8) = 17 by
        rw [round_eq, show (135 : ℝ) / 8 + 1 / 2 = 139 / 8 by norm_num, Int.floor_eq_iff]
        norm_num]
    norm_num
  · rw [distToNearestInt, show ((5 : ℝ)) * (3 / 2) ^ 4 = 405 / 16 by norm_num,
      show round ((405 : ℝ) / 16) = 25 by
        rw [round_eq, show (405 : ℝ) / 16 + 1 / 2 = 413 / 16 by norm_num, Int.floor_eq_iff]
        norm_num]
    norm_num

end TShift
