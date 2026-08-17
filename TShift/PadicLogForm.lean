/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.Basic
import CITED.BugeaudLaurent
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# S3 — the 2-adic linear form in two logarithms

Strategy **S3** of `plans/report-Tshift.html`: the one route to `‖D(3/2)ⁿ‖` that the Pollington
obstruction (§1.7(2) of the report) *requires*, because it uses the integrality of `ξ = 1` beyond
the trivial "nonzero integer `≥ 1`".  Both strengths of the row are proved here, at every odd
multiplier `D` — in particular at every cycle denominator `D_p = 3^p − 2^p`:

* **(i) the sub-exponential gain** (`TShift.dist_ge_subexp`)
  `‖D(3/2)ⁿ‖ ≥ exp(n/(289(log n + 12)²))/(2D·2ⁿ)` — an unconditional improvement of the free
  2-adic floor `2^{-n}` (Lemma 2 of the report) by a factor `exp(cn/(log n)²)`.  The rate is
  still `θ = 1/2`.
* **(ii) a T0-type rate** (`TShift.dist_ge_theta`, `TShift.isRepelledMul_padic`,
  `TShift.repelledAt_padic`)
  `‖D(3/2)ⁿ‖ ≥ (1/2D)·θⁿ` with **`θ = 1000001/2000000 > 1/2`**, effective, every numeral
  exhibited, for all `n ≥ D + 6`.  In the report's parametrization `θ = 2^{−(1−η)}` this is
  `η ≥ 1.44·10⁻⁶`.

## The chain

Write `N_n = D·3ⁿ − 2ⁿ·round(D(3/2)ⁿ)` (`TShift.defect`), so that `‖D(3/2)ⁿ‖ = |N_n|/2ⁿ`
(`TShift.abs_defect_eq`).  Then

1. `N_n` is **odd** and `2ⁿ ∣ D·3ⁿ − N_n` (`TShift.defect_odd`, `TShift.two_pow_dvd_sub_defect`)
   — by construction.  This is the whole arithmetic input, and it is exactly where `ξ = 1` enters.
2. Hence the two-term form `Λ = 3ⁿ − N_n/D` has `v₂(Λ) ≥ n` (`TShift.le_padicValRat_form`).
3. `3` and `N_n/D` are **multiplicatively independent** once `4(n + D) < 2ⁿ`
   (`TShift.mulIndep_three_defect`): degeneracy would make `|N_n|` and `D` differ by a power of
   `3`, and the congruence of step 1 would then force `2ⁿ ∣ 3^t ∓ 1` with `1 ≤ t ≤ n + D`, hence
   `2ⁿ ≤ 4t` by the 2-adic order of `3` (`TShift.two_pow_le_of_dvd_three_pow_sub`, lifting the
   exponent at `2` for even `t` and `3^t ≡ 3 (mod 8)` for odd `t`).
4. The Bugeaud–Laurent two-log engine at `p = 2` (`CITED/BugeaudLaurent.lean`, Corollary 1) then
   bounds `v₂(Λ)` from above, giving **the master inequality** (`TShift.master`)
   `n ≤ 289·(max{log(n/L + 1) + 1, 10})²·L`, `L = log A₂` the clamped height of `N_n/D`.
5. `b'` depends on `n` **only through `u = n/L`**, so the master inequality bounds `u` outright:
   `u ≤ 289(log u + 2)² < 300(log u + 2)² < u` for `u ≥ 10⁶` (`TShift.log_sq_lt_self`), whence
   `L ≥ n/10⁶` (`TShift.le_defectLogA`).
6. `L ≤ log(2|N_n|D)` (`TShift.defectLogA_le`) turns that into `|N_n| ≥ exp(n/10⁶)/(2D)`, i.e.
   rung (ii); and reading step 4 with the crude `T ≤ log n + 12` instead gives rung (i).

## Two things this build settles about the strategy row

* **The row's two strengths are one inequality.**  The report presents (i) as cheap and (ii) as
  requiring the Baker–Coates `B'`-refinement, a separate 1975 device.  In the modern engine the
  refinement *is* the definition of `b'`, and the substitution `u = n/L` of step 5 extracts (ii)
  from the same line that gives (i).  No iteration and no second device are needed.
* **The row's `η ≈ 10⁻⁶⁴` is enormously pessimistic.**  The engine's own ceiling here is
  `η = 6.2·10⁻⁵` (Corollary 1; `7.8·10⁻⁵` with Théorème 4's tuned table) — see
  `TShift/tshift_numerics.py s3`.  The Lean constant `η = 1.44·10⁻⁶` is that ceiling rounded down
  to a threshold `u ≤ 10⁶` at which the numeric lemma is provable without any calculus, and it is
  still `1.4·10⁵⁸` times the row's figure.

## What is *not* claimed

The rate `θ = 0.5000005` is **far weaker than S1's transported `0.57434`**
(`TShift/HabsiegerTransfer.lean`) and does not approach `2/3`
(`TShift.theta_padic_lt_two_thirds`, `TShift.not_tShiftProblemAt_padic`): the T-shift problem is
untouched.  The value of the item is methodological — this is a **second, disjoint** proof of T0
at every multiplier, and the only route in this corpus whose engine contains no Padé
approximation (contrast `CITED/HabsiegerPade.lean`, `CITED/ZudilinPade.lean`) and no Ridout
counting (contrast `CITED/BugeaudEvertseRidout.lean`).  Nothing here bears on T3: the gain is
`exp(cn/(log n)²)` against a demand of `exp(−cn^β)`.

## Trust ledger

`std3` throughout, plus **one** cited axiom on the six theorems downstream of the engine
(`master`, `le_defectLogA`, `dist_ge_subexp`, `dist_ge_theta`, `isRepelledMul_padic`,
`repelledAt_padic`): `BugeaudLaurent.padicDist_lt` ([BL96p] Corollary 1), which was already in
the corpus — `plan-formalize-logforms.html` gap G-a, modernized 2026-07-11 — so the report's
§9 forecast "S3(i) needs one new cited axiom" is discharged with **no new axiom written**.  The
other 33 declarations carry `std3` alone.  No `sorry`, no `native_decide`, no `decide` on `ℚ`
or `ℝ`.

## Claim level

Formalization of a route the report proposes, with two findings about it (above).  The
Bugeaud–Laurent estimate itself is cited, not re-derived.

## References

* `plans/report-Tshift.html` §6 S3 (the strategy row), §1.3 (Lemma 2, the free bound), §1.7(2)
  (the Pollington obstruction), §9 item 5 (the forecast).
* [BL96p] Y. Bugeaud, M. Laurent, *Minoration effective de la distance p-adique entre puissances
  de nombres algébriques*, J. Number Theory **61** (1996), 311–342 — `CITED/BugeaudLaurent.lean`.
* [BC75] A. Baker, J. Coates, *Fractional parts of powers of rationals*, Math. Proc. Cambridge
  Philos. Soc. **77** (1975), 269–279 — the `B'`-refinement the row invokes; superseded here by
  the `b'` of [BL96p].
* [Hab03]/[Zud07] the Padé routes that S3 is disjoint from (`TShift/HabsiegerTransfer.lean`,
  `TShift/ZudilinTransfer.lean`).
-/

namespace TShift

open Real

/-! ## 1. The defect -/

/-- **The defect** `N_n = D·3ⁿ − 2ⁿ·round(D(3/2)ⁿ)`: the signed numerator of the distance from
`D(3/2)ⁿ` to the nearest integer, so that `‖D(3/2)ⁿ‖ = |N_n|/2ⁿ`.  It is odd (for `n ≥ 1` and odd
`D`) and congruent to `D·3ⁿ` mod `2ⁿ` by construction — the two facts the 2-adic engine needs. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
noncomputable def defect (D n : ℕ) : ℤ :=
  (D : ℤ) * 3 ^ n - 2 ^ n * round ((D : ℝ) * ((3 : ℝ) / 2) ^ n)

/-- `|N_n| = 2ⁿ·‖D(3/2)ⁿ‖`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem abs_defect_eq (D n : ℕ) :
    |((defect D n : ℤ) : ℝ)| = 2 ^ n * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have key : ((defect D n : ℤ) : ℝ)
      = 2 ^ n * ((D : ℝ) * ((3 : ℝ) / 2) ^ n - (round ((D : ℝ) * ((3 : ℝ) / 2) ^ n) : ℝ)) := by
    simp only [defect]
    push_cast
    rw [div_pow]
    field_simp
  rw [key, abs_mul, abs_of_pos h2, distToNearestInt]

/-- `2|N_n| ≤ 2ⁿ`, since `‖·‖ ≤ 1/2`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_mul_abs_defect_le (D n : ℕ) : 2 * |defect D n| ≤ 2 ^ n := by
  have hR : (2 : ℝ) * |((defect D n : ℤ) : ℝ)| ≤ 2 ^ n := by
    rw [abs_defect_eq]
    have h := abs_sub_round ((D : ℝ) * ((3 : ℝ) / 2) ^ n)
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [distToNearestInt]
    nlinarith
  have : ((2 * |defect D n| : ℤ) : ℝ) ≤ ((2 ^ n : ℤ) : ℝ) := by push_cast; simpa using hR
  exact_mod_cast this

/-- The defect is **odd**: `D·3ⁿ` is odd and `2ⁿ·round(·)` is even for `n ≥ 1`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem defect_odd {D n : ℕ} (hD : Odd D) (hn : 1 ≤ n) : ¬ (2 : ℤ) ∣ defect D n := by
  intro hdvd
  have hodd : Odd ((D : ℤ) * 3 ^ n) := by
    refine Odd.mul ?_ (Odd.pow (by decide))
    exact_mod_cast hD
  have heven : (2 : ℤ) ∣ 2 ^ n * round ((D : ℝ) * ((3 : ℝ) / 2) ^ n) :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hdvd' : (2 : ℤ) ∣ (D : ℤ) * 3 ^ n := by
    have := dvd_add hdvd heven
    simpa [defect] using this
  obtain ⟨c, hc⟩ := hdvd'
  obtain ⟨d, hd⟩ := hodd
  omega

/-- The defect is nonzero — the orbit never hits an integer. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem defect_ne_zero {D n : ℕ} (hD : Odd D) (hn : 1 ≤ n) : defect D n ≠ 0 := by
  intro h
  exact defect_odd hD hn (h ▸ dvd_zero 2)

/-- **The 2-adic congruence.**  `2ⁿ ∣ D·3ⁿ − N_n`, by the definition of `N_n`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_pow_dvd_sub_defect (D n : ℕ) : (2 : ℤ) ^ n ∣ (D : ℤ) * 3 ^ n - defect D n :=
  ⟨round ((D : ℝ) * ((3 : ℝ) / 2) ^ n), by simp [defect]⟩

/-- `|N_n| < D·3ⁿ`: the defect is far smaller than the number it is a defect of. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem abs_defect_lt {D n : ℕ} (hD : 0 < D) : |defect D n| < (D : ℤ) * 3 ^ n := by
  have h1 : 2 * |defect D n| ≤ 2 ^ n := two_mul_abs_defect_le D n
  have h2 : (2 : ℤ) ^ n ≤ 3 ^ n := by gcongr; norm_num
  have h3 : (3 : ℤ) ^ n ≤ (D : ℤ) * 3 ^ n := by
    have : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
    nlinarith [pow_pos (by norm_num : (0:ℤ) < 3) n]
  have h4 : (0 : ℤ) < (D : ℤ) * 3 ^ n := by
    have : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
    positivity
  linarith [abs_nonneg (defect D n)]

/-! ## 2. The 2-adic order of `3` -/

/-- `3^t ≡ 3 (mod 8)` for odd `t`, `≡ 1` for even `t`: `9 ≡ 1 (mod 8)`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem three_pow_emod_eight (t : ℕ) :
    (3 : ℤ) ^ t % 8 = if t % 2 = 0 then 1 else 3 := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd t
  · subst hk
    have h9 : (3 : ℤ) ^ (k + k) = 9 ^ k := by rw [← two_mul, pow_mul]; norm_num
    have h1 : (9 : ℤ) ^ k % 8 = 1 := by
      have : (9 : ℤ) ^ k ≡ 1 ^ k [ZMOD 8] := Int.ModEq.pow k (by decide)
      simpa [Int.ModEq] using this
    rw [if_pos (by omega), h9]
    exact h1
  · have h9 : (3 : ℤ) ^ t = 9 ^ k * 3 := by rw [hk, pow_add, pow_mul]; norm_num
    have h1 : (9 : ℤ) ^ k ≡ 1 [ZMOD 8] := by
      have : (9 : ℤ) ^ k ≡ 1 ^ k [ZMOD 8] := Int.ModEq.pow k (by decide)
      simpa using this
    have : (9 : ℤ) ^ k * 3 ≡ 1 * 3 [ZMOD 8] := h1.mul_right 3
    rw [h9]
    have ht : t % 2 = 1 := by omega
    simp only [ht]
    simpa [Int.ModEq] using this

/-- If `2^s ∣ 3^t − 1` with `t ≥ 1` then `2^s ≤ 4t`.  Even `t`: lifting the exponent at `2`
(`padicValNat.pow_two_sub_one`) gives `v₂(3^t − 1) = 2 + v₂(t)`.  Odd `t`: `3^t − 1 ≡ 2 (mod 8)`,
so `s ≤ 2`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_pow_le_of_dvd_three_pow_sub_one {s t : ℕ} (ht : 1 ≤ t)
    (h : (2 : ℤ) ^ s ∣ 3 ^ t - 1) : 2 ^ s ≤ 4 * t := by
  rcases Nat.even_or_odd t with he | ho
  · -- lifting the exponent
    have h13 : 1 ≤ 3 ^ t := Nat.one_le_pow _ _ (by norm_num)
    have h33 : 3 ≤ 3 ^ t := by
      calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have hN : (2 : ℕ) ^ s ∣ 3 ^ t - 1 := by
      have hcast : ((3 ^ t - 1 : ℕ) : ℤ) = (3 : ℤ) ^ t - 1 := by
        push_cast [h13]
        ring
      have : ((2 : ℕ) ^ s : ℤ) ∣ ((3 ^ t - 1 : ℕ) : ℤ) := by rw [hcast]; exact_mod_cast h
      exact_mod_cast this
    have hne : 3 ^ t - 1 ≠ 0 := by omega
    have hv := padicValNat.pow_two_sub_one (x := 3) (n := t) (by norm_num) (by decide)
      (by omega) he
    have h4 : padicValNat 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
    have hs : s ≤ padicValNat 2 (3 ^ t - 1) := (padicValNat_dvd_iff_le hne).mp hN
    have hvt : padicValNat 2 (3 ^ t - 1) = 2 + padicValNat 2 t := by
      norm_num [h4, h2] at hv
      omega
    have hdvd : 2 ^ padicValNat 2 t ∣ t := pow_padicValNat_dvd
    have hle : 2 ^ padicValNat 2 t ≤ t := Nat.le_of_dvd (by omega) hdvd
    calc 2 ^ s ≤ 2 ^ (2 + padicValNat 2 t) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 2 ^ padicValNat 2 t := by rw [pow_add]; norm_num
      _ ≤ 4 * t := by omega
  · -- `3^t − 1 ≡ 2 (mod 8)`
    have hs2 : s ≤ 2 := by
      by_contra hgt
      have h8 : (8 : ℤ) ∣ (3 : ℤ) ^ t - 1 := by
        refine dvd_trans ?_ h
        have : (8 : ℤ) = 2 ^ 3 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega)
      have hmod := three_pow_emod_eight t
      have ht1 : t % 2 = 1 := Nat.odd_iff.mp ho
      rw [if_neg (by omega)] at hmod
      omega
    calc 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hs2
      _ = 4 := by norm_num
      _ ≤ 4 * t := by omega

/-- If `2^s ∣ 3^t + 1` then `2^s ≤ 4`: `3^t + 1` is `2` or `4` mod `8`, never `0`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_pow_le_of_dvd_three_pow_add_one {s t : ℕ} (h : (2 : ℤ) ^ s ∣ 3 ^ t + 1) :
    2 ^ s ≤ 4 := by
  have hs2 : s ≤ 2 := by
    by_contra hgt
    have h8 : (8 : ℤ) ∣ (3 : ℤ) ^ t + 1 := by
      refine dvd_trans ?_ h
      have : (8 : ℤ) = 2 ^ 3 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    have hmod := three_pow_emod_eight t
    rcases Nat.even_or_odd t with he | ho
    · rw [if_pos (Nat.even_iff.mp he)] at hmod
      omega
    · rw [if_neg (by omega : ¬ t % 2 = 0)] at hmod
      omega
  calc 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hs2
    _ = 4 := by norm_num

/-- The two cases together: `2^s ∣ 3^t ∓ 1` with `t ≥ 1` forces `2^s ≤ 4t`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_pow_le_of_dvd_three_pow_sub {s t : ℕ} (ht : 1 ≤ t) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : (2 : ℤ) ^ s ∣ 3 ^ t - ε) : 2 ^ s ≤ 4 * t := by
  rcases hε with rfl | rfl
  · exact two_pow_le_of_dvd_three_pow_sub_one ht h
  · have h' : (2 : ℤ) ^ s ∣ 3 ^ t + 1 := by simpa using h
    calc 2 ^ s ≤ 4 := two_pow_le_of_dvd_three_pow_add_one h'
      _ ≤ 4 * t := by omega

/-! ## 3. Non-degeneracy: `3` and `N_n/D` are multiplicatively independent -/

/-- Odd factors cancel from powers of two: `2ᵏ ∣ M·X` with `M` odd gives `2ᵏ ∣ X`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem two_pow_dvd_of_dvd_mul_odd {k : ℕ} {M X : ℤ} (hM : ¬ (2 : ℤ) ∣ M)
    (h : (2 : ℤ) ^ k ∣ M * X) : (2 : ℤ) ^ k ∣ X :=
  (((Int.prime_two.coprime_iff_not_dvd).mpr hM).pow_left).dvd_of_dvd_mul_left h

/-- `D·3^j` is odd. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem not_two_dvd_mul_three_pow {D : ℕ} (hD : Odd D) (j : ℕ) :
    ¬ (2 : ℤ) ∣ (D : ℤ) * 3 ^ j := by
  intro h
  have hodd : Odd ((D : ℤ) * 3 ^ j) := by
    refine Odd.mul ?_ (Odd.pow (by decide))
    exact_mod_cast hD
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := hodd
  omega

/-- Under the burn-in `4(n + D) < 2ⁿ`, the date `n` is at least `1`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem one_le_of_burnin {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) : 1 ≤ n := by
  have hDpos : 0 < D := hD.pos
  by_contra h
  have hn0 : n = 0 := by omega
  rw [hn0] at hbig
  norm_num at hbig
  omega

/-- **The defect is never `±D·3^j`.**  For `j ≥ n` this is a size contradiction (`|N_n| < D·3ⁿ`);
for `j < n` the 2-adic congruence `2ⁿ ∣ D·3ⁿ − N_n` would force `2ⁿ ∣ 3^{n−j} ∓ 1`, hence
`2ⁿ ≤ 4(n−j) ≤ 4n`, against the burn-in. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem abs_defect_ne_mul_three_pow {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n)
    (j : ℕ) : |defect D n| ≠ (D : ℤ) * 3 ^ j := by
  intro heq
  have hDpos : 0 < D := hD.pos
  have hlt := abs_defect_lt (D := D) (n := n) hDpos
  rcases le_or_gt n j with hj | hj
  · -- size
    have h3 : (3 : ℤ) ^ n ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have hD1 : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hDpos
    nlinarith
  · -- 2-adic
    have hsplit : (3 : ℤ) ^ n = 3 ^ j * 3 ^ (n - j) := by
      rw [← pow_add]
      congr 1
      omega
    have hdvd0 := two_pow_dvd_sub_defect D n
    have hodd := not_two_dvd_mul_three_pow hD j
    rcases abs_choice (defect D n) with hs | hs
    · have hN : defect D n = (D : ℤ) * 3 ^ j := by rw [← hs, heq]
      have hkey : (D : ℤ) * 3 ^ n - defect D n = ((D : ℤ) * 3 ^ j) * (3 ^ (n - j) - 1) := by
        rw [hN, hsplit]; ring
      rw [hkey] at hdvd0
      have := two_pow_le_of_dvd_three_pow_sub_one (t := n - j) (by omega)
        (two_pow_dvd_of_dvd_mul_odd hodd hdvd0)
      omega
    · have hN : defect D n = -((D : ℤ) * 3 ^ j) := by
        have : -defect D n = (D : ℤ) * 3 ^ j := by rw [← hs, heq]
        linarith
      have hkey : (D : ℤ) * 3 ^ n - defect D n = ((D : ℤ) * 3 ^ j) * (3 ^ (n - j) + 1) := by
        rw [hN, hsplit]; ring
      rw [hkey] at hdvd0
      have := two_pow_le_of_dvd_three_pow_add_one (t := n - j)
        (two_pow_dvd_of_dvd_mul_odd hodd hdvd0)
      omega

/-- **`D` is never `±N_n·3^j` either** (`j ≥ 1`): multiplying the congruence by `3^j` gives
`2ⁿ ∣ 3^{n+j} ∓ 1`, hence `2ⁿ ≤ 4(n+j) ≤ 4(n+D)`, against the burn-in. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem abs_defect_mul_three_pow_ne {D n j : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n)
    (hj : 1 ≤ j) : |defect D n| * 3 ^ j ≠ (D : ℤ) := by
  intro heq
  have hDpos : 0 < D := hD.pos
  have hn1 : 1 ≤ n := one_le_of_burnin hD hbig
  have hNne : defect D n ≠ 0 := defect_ne_zero hD hn1
  have hpos : (1 : ℤ) ≤ |defect D n| := by
    rcases abs_pos.mpr hNne with h
    omega
  -- `3^j ≤ D`, hence `j ≤ D`
  have hjD : (j : ℤ) ≤ (D : ℤ) := by
    have h1 : (3 : ℤ) ^ j ≤ (D : ℤ) := by nlinarith [pow_pos (by norm_num : (0:ℤ) < 3) j]
    have h2 : (j : ℤ) < 3 ^ j := by
      have := j.lt_pow_self (by norm_num : 1 < 3)
      exact_mod_cast this
    omega
  have hdvd0 := two_pow_dvd_sub_defect D n
  have hdvd1 : (2 : ℤ) ^ n ∣ (3 : ℤ) ^ j * ((D : ℤ) * 3 ^ n - defect D n) := Dvd.dvd.mul_left hdvd0 _
  have hoddD : ¬ (2 : ℤ) ∣ (D : ℤ) := by
    have := not_two_dvd_mul_three_pow hD 0
    simpa using this
  rcases abs_choice (defect D n) with hs | hs
  · have hN : (3 : ℤ) ^ j * defect D n = (D : ℤ) := by rw [← heq, hs]; ring
    have hkey : (3 : ℤ) ^ j * ((D : ℤ) * 3 ^ n - defect D n)
        = (D : ℤ) * (3 ^ (n + j) - 1) := by
      rw [pow_add]
      linear_combination (-(1 : ℤ)) * hN
    rw [hkey] at hdvd1
    have := two_pow_le_of_dvd_three_pow_sub_one (t := n + j) (by omega)
      (two_pow_dvd_of_dvd_mul_odd hoddD hdvd1)
    omega
  · have hN : (3 : ℤ) ^ j * defect D n = -(D : ℤ) := by rw [← heq, hs]; ring
    have hkey : (3 : ℤ) ^ j * ((D : ℤ) * 3 ^ n - defect D n)
        = (D : ℤ) * (3 ^ (n + j) + 1) := by
      rw [pow_add]
      linear_combination -hN
    rw [hkey] at hdvd1
    have := two_pow_le_of_dvd_three_pow_add_one (t := n + j)
      (two_pow_dvd_of_dvd_mul_odd hoddD hdvd1)
    omega

/-- **The `hindep` side condition of the engine, discharged.**  `3` and `N_n/D` are
multiplicatively independent in `ℚ` as soon as `4(n + D) < 2ⁿ`.  The 3-adic valuation forces
`a = −bw` with `w = v₃(N_n/D)`, and then `(N_n/(D·3^w))^b = 1` forces `|N_n| = D·3^w` — which the
two preceding theorems exclude. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem mulIndep_three_defect {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) :
    ∀ a b : ℤ, (3 : ℚ) ^ a * ((defect D n : ℚ) / (D : ℚ)) ^ b = 1 → a = 0 ∧ b = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro a b hab
  have hDpos : 0 < D := hD.pos
  have hn1 : 1 ≤ n := one_le_of_burnin hD hbig
  have hNne : defect D n ≠ 0 := defect_ne_zero hD hn1
  have hDQ : ((D : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  have hNQ : ((defect D n : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hNne
  set q : ℚ := (defect D n : ℚ) / (D : ℚ) with hqdef
  have hq0 : q ≠ 0 := div_ne_zero hNQ hDQ
  set w : ℤ := padicValRat 3 q with hwdef
  have h3val : padicValRat 3 (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num]
    exact padicValRat.self (by norm_num)
  have hval : a + b * w = 0 := by
    have h1 : padicValRat 3 ((3 : ℚ) ^ a * q ^ b) = 0 := by rw [hab]; simp
    rw [padicValRat.mul (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hq0),
      padicValRat.zpow, padicValRat.zpow, h3val] at h1
    linarith
  rcases eq_or_ne b 0 with rfl | hb
  · refine ⟨?_, rfl⟩
    simpa using hval
  -- `b ≠ 0` is impossible
  exfalso
  set x : ℚ := q * (3 : ℚ) ^ (-w) with hxdef
  have hxb : x ^ b = 1 := by
    have h3ne : (3 : ℚ) ≠ 0 := by norm_num
    have haw : a = -(b * w) := by linarith
    have hqb : q ^ b = (3 : ℚ) ^ (b * w) := by
      have h0 : (3 : ℚ) ^ (-(b * w)) * q ^ b = 1 := haw ▸ hab
      have h1 : (3 : ℚ) ^ (b * w) * ((3 : ℚ) ^ (-(b * w)) * q ^ b) = (3 : ℚ) ^ (b * w) := by
        rw [h0, mul_one]
      rw [← mul_assoc, ← zpow_add₀ h3ne] at h1
      simpa using h1
    rw [hxdef, mul_zpow, ← zpow_mul, hqb, ← zpow_add₀ h3ne,
      show b * w + -w * b = 0 by ring, zpow_zero]
  have habs : |x| = 1 := by
    by_contra hne
    exact hb ((zpow_eq_one_iff_right₀ (abs_nonneg x) hne).mp
      (by rw [← abs_zpow, hxb, abs_one]))
  -- `|q| = 3^w`
  have hq3 : |q| = (3 : ℚ) ^ w := by
    have h1 : |q| * (3 : ℚ) ^ (-w) = 1 := by
      rw [← habs, hxdef, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (3 : ℚ) ^ (-w))]
    field_simp at h1
    rw [zpow_neg] at h1
    field_simp at h1
    exact h1
  have hqabs : |q| = |(defect D n : ℚ)| / (D : ℚ) := by
    rw [hqdef, abs_div, abs_of_pos (by positivity : (0 : ℚ) < (D : ℚ))]
  have hmain : |(defect D n : ℚ)| = (D : ℚ) * (3 : ℚ) ^ w := by
    have h := hq3
    rw [hqabs, div_eq_iff hDQ] at h
    linear_combination h
  rcases le_or_gt 0 w with hw0 | hw0
  · -- `w ≥ 0`: `|N| = D·3^j`
    obtain ⟨j, hjw⟩ := Int.eq_ofNat_of_zero_le hw0
    rw [hjw, zpow_natCast] at hmain
    have hZ : |defect D n| = (D : ℤ) * 3 ^ j := by
      have hcast : ((|defect D n| : ℤ) : ℚ) = (((D : ℤ) * 3 ^ j : ℤ) : ℚ) := by
        push_cast [Int.cast_abs]
        linear_combination hmain
      exact_mod_cast hcast
    exact abs_defect_ne_mul_three_pow hD hbig j hZ
  · -- `w < 0`: `|N|·3^j = D`
    obtain ⟨j, hjw⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -w)
    have hj1 : 1 ≤ j := by omega
    rw [show w = -(j : ℤ) by omega, zpow_neg, zpow_natCast] at hmain
    have hZ : |defect D n| * 3 ^ j = (D : ℤ) := by
      have h3pos : (0 : ℚ) < (3 : ℚ) ^ j := by positivity
      have hcast : ((|defect D n| * 3 ^ j : ℤ) : ℚ) = (((D : ℤ) : ℤ) : ℚ) := by
        push_cast [Int.cast_abs]
        field_simp at hmain
        linear_combination hmain
      exact_mod_cast hcast
    exact abs_defect_mul_three_pow_ne hD hbig hj1 hZ

/-! ## 4. The engine instance: `n` against the height of the defect -/

/-- Three elementary numeric facts about `log 2` and `log 3`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9
  linarith

@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem one_le_log_three : 1 ≤ Real.log 3 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 := Real.log_lt_log (Real.exp_pos 1) h
  rw [Real.log_exp] at h2
  linarith

@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem log_three_le_two_log_two : Real.log 3 ≤ 2 * Real.log 2 := by
  have h : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- The engine's clamped log-height at `α₂ = N_n/D`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
noncomputable def defectLogA (D n : ℕ) : ℝ :=
  BugeaudLaurent.logA 2 ((defect D n : ℚ) / (D : ℚ))

@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem log_two_le_defectLogA (D n : ℕ) : Real.log 2 ≤ defectLogA D n := by
  have h : Real.log ((2 : ℕ) : ℝ) ≤ defectLogA D n := le_max_right _ _
  simpa using h

@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem defectLogA_pos (D n : ℕ) : 0 < defectLogA D n :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_defectLogA D n)

/-- The `log A₂` of the engine at `α₁ = 3`: the `log p` floor does **not** bite (`log 2 < log 3`). -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem logA_two_three : BugeaudLaurent.logA 2 (3 : ℚ) = Real.log 3 := by
  rw [BugeaudLaurent.logA, Rat.logHeight₁_eq_log_max, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
  norm_num
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- **The height of the defect is at most `log(2|N_n|D)`.**  The numerator and denominator of
`N_n/D` in lowest terms divide `N_n` and `D`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem defectLogA_le {D n : ℕ} (hD : Odd D) (hn : 1 ≤ n) :
    defectLogA D n ≤ Real.log (2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ)) := by
  have hDpos : 0 < D := hD.pos
  have hNne : defect D n ≠ 0 := defect_ne_zero hD hn
  have hD0 : ((D : ℤ)) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hNabs : 1 ≤ (defect D n).natAbs := Int.natAbs_pos.mpr hNne
  rw [defectLogA, BugeaudLaurent.logA]
  set q : ℚ := (defect D n : ℚ) / (D : ℚ) with hqdef
  have hq : q = Rat.divInt (defect D n) (D : ℤ) := by
    rw [hqdef, Rat.divInt_eq_div]
    norm_num
  have hnum : q.num.natAbs ≤ (defect D n).natAbs := by
    have h1 : q.num ∣ defect D n := by rw [hq]; exact Rat.num_dvd _ hD0
    exact Nat.le_of_dvd hNabs (Int.natAbs_dvd_natAbs.mpr h1)
  have hden : q.den ≤ D := by
    have h1 : ((q.den : ℤ)) ∣ (D : ℤ) := by rw [hq]; exact Rat.den_dvd _ _
    exact Nat.le_of_dvd hDpos (Int.ofNat_dvd.mp h1)
  have hmaxN : max q.num.natAbs q.den ≤ 2 * ((defect D n).natAbs * D) := by
    have h1 : q.num.natAbs ≤ (defect D n).natAbs * D :=
      le_trans hnum (Nat.le_mul_of_pos_right _ hDpos)
    have h2 : q.den ≤ (defect D n).natAbs * D :=
      le_trans hden (Nat.le_mul_of_pos_left _ hNabs)
    omega
  have hnc : (((defect D n).natAbs : ℕ) : ℝ) = |((defect D n : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcast : ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) := by
    have h : ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ ((2 * ((defect D n).natAbs * D) : ℕ) : ℝ) := by
      exact_mod_cast hmaxN
    refine h.trans (le_of_eq ?_)
    push_cast [hnc]
    ring
  have hNone : (1 : ℝ) ≤ |((defect D n : ℤ) : ℝ)| := by
    rw [← hnc]
    exact_mod_cast hNabs
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDpos
  have hmaxpos : 0 < max q.num.natAbs q.den := lt_of_lt_of_le q.den_pos (le_max_right _ _)
  refine max_le ?_ ?_
  · rw [Rat.logHeight₁_eq_log_max]
    exact Real.log_le_log (by exact_mod_cast hmaxpos) hcast
  · refine Real.log_le_log (by norm_num) ?_
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    nlinarith

/-- **The 2-adic valuation of the form.**  `Λ = 3ⁿ − N_n/D = (D·3ⁿ − N_n)/D` and `2ⁿ ∣ D·3ⁿ − N_n`,
so `v₂(Λ) ≥ n` — this is the whole arithmetic input, and it is where `ξ = 1` (the integrality of
the multiplier) enters. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem le_padicValRat_form {D n : ℕ} (hD : Odd D) (_hn : 1 ≤ n) :
    (n : ℤ) ≤ padicValRat 2 ((3 : ℚ) ^ n - (defect D n : ℚ) / (D : ℚ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDpos : 0 < D := hD.pos
  have hDQ : ((D : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  set M : ℤ := (D : ℤ) * 3 ^ n - defect D n with hM
  have hMne : M ≠ 0 := by
    have := abs_defect_lt (D := D) (n := n) hDpos
    have h2 := abs_nonneg (defect D n)
    have h3 : -(|defect D n|) ≤ defect D n := neg_abs_le _
    have h4 : defect D n ≤ |defect D n| := le_abs_self _
    omega
  have hform : (3 : ℚ) ^ n - (defect D n : ℚ) / (D : ℚ) = (M : ℚ) / (D : ℚ) := by
    rw [hM]
    push_cast
    field_simp
  have hMQ : ((M : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hMne
  have hvD : padicValRat 2 ((D : ℚ)) = 0 := by
    rw [show ((D : ℚ)) = ((D : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
    have : ¬ ((2 : ℤ)) ∣ (D : ℤ) := by
      have := not_two_dvd_mul_three_pow hD 0
      simpa using this
    simp [padicValInt.eq_zero_of_not_dvd this]
  have hvM : (n : ℤ) ≤ padicValRat 2 ((M : ℤ) : ℚ) := by
    rw [padicValRat.of_int]
    have hdvd : ((2 : ℤ)) ^ n ∣ M := two_pow_dvd_sub_defect D n
    have := (padicValInt_dvd_iff (p := 2) n M).mp (by exact_mod_cast hdvd)
    rcases this with h | h
    · exact absurd h hMne
    · exact_mod_cast h
  rw [hform, padicValRat.div hMQ hDQ, hvD, sub_zero]
  exact hvM

/-- **The master inequality.**  Feeding the two-log engine [BL96p] at `p = 2` with
`α₁ = 3, b₁ = n` and `α₂ = N_n/D, b₂ = 1`, and reading its conclusion against `v₂(Λ) ≥ n`:
`n ≤ 289·(max{log(n/L + 1) + 1, 10})²·L`, where `L = log A₂` is the clamped height of the
defect.  Every constant here is explicit, and `L` is the *only* unknown. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem master {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) :
    (n : ℝ) ≤ 289 * (max (Real.log ((n : ℝ) / defectLogA D n + 1) + 1) 10) ^ 2
      * defectLogA D n := by
  have hn1 : 1 ≤ n := one_le_of_burnin hD hbig
  have hDpos : 0 < D := hD.pos
  have hNne : defect D n ≠ 0 := defect_ne_zero hD hn1
  have hDQ : ((D : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hDpos.ne'
  set q : ℚ := (defect D n : ℚ) / (D : ℚ) with hqdef
  have hq0 : q ≠ 0 := div_ne_zero (Int.cast_ne_zero.mpr hNne) hDQ
  set L := defectLogA D n with hLdef
  have hLpos : 0 < L := defectLogA_pos D n
  have hform : (n : ℤ) ≤ padicValRat 2 ((3 : ℚ) ^ n - q) := le_padicValRat_form hD hn1
  -- side conditions of the engine
  have hu1 : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)]
  have hu2 : padicValRat 2 q = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hvN : padicValRat 2 ((defect D n : ℤ) : ℚ) = 0 := by
      rw [padicValRat.of_int]
      simp [padicValInt.eq_zero_of_not_dvd (defect_odd hD hn1)]
    have hvD : padicValRat 2 ((D : ℚ)) = 0 := by
      rw [show ((D : ℚ)) = ((D : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
      have hnd : ¬ ((2 : ℤ)) ∣ (D : ℤ) := by
        have := not_two_dvd_mul_three_pow hD 0
        simpa using this
      simp [padicValInt.eq_zero_of_not_dvd hnd]
    rw [hqdef, padicValRat.div (Int.cast_ne_zero.mpr hNne) hDQ, hvN, hvD, sub_zero]
  have hΛ : (3 : ℚ) ^ n - q ^ 1 ≠ 0 := by
    rw [pow_one]
    intro h
    rw [h, padicValRat.zero] at hform
    omega
  have key := BugeaudLaurent.padicDist_lt 2 (by norm_num) 3 q (by norm_num) hq0 hu1 hu2
    (mulIndep_three_defect hD hbig) n 1 (by omega) one_pos hΛ
  rw [logA_two_three, pow_one] at key
  have hlhs : (n : ℝ) ≤ ((padicValRat 2 ((3 : ℚ) ^ n - q) : ℤ) : ℝ) := by
    have h2 : (((n : ℤ)) : ℝ) ≤ ((padicValRat 2 ((3 : ℚ) ^ n - q) : ℤ) : ℝ) := Int.cast_le.mpr hform
    simpa using h2
  -- the right-hand side
  set T : ℝ := max (Real.log ((n : ℝ) / L + 1) + 1) 10 with hTdef
  have hT10 : (10 : ℝ) ≤ T := le_max_right _ _
  have hTpos : (0 : ℝ) < T := by linarith
  have hbp : BugeaudLaurent.bPrime n 1 (Real.log 3) L ≤ (n : ℝ) / L + 1 := by
    rw [BugeaudLaurent.bPrime]
    have h1 : (1 : ℝ) / Real.log 3 ≤ 1 := by
      rw [div_le_one (by linarith [one_le_log_three])]
      exact one_le_log_three
    push_cast
    linarith
  have hbppos : (0 : ℝ) < BugeaudLaurent.bPrime n 1 (Real.log 3) L := by
    rw [BugeaudLaurent.bPrime]
    have h3 : (0 : ℝ) < Real.log 3 := by linarith [one_le_log_three]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    positivity
  set T' : ℝ := max (Real.log (BugeaudLaurent.bPrime n 1 (Real.log 3) L)
      + Real.log (Real.log ((2 : ℕ) : ℝ)) + 0.4)
    (max (10 * Real.log ((2 : ℕ) : ℝ)) 10) with hT'def
  have hT'0 : (0 : ℝ) ≤ T' := le_trans (by positivity) (le_max_right _ _)
  have hmax : T' ≤ T := by
    have h2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [hT'def, h2]
    refine max_le ?_ ?_
    · refine le_trans ?_ (le_max_left _ _)
      have hlog := Real.log_le_log hbppos hbp
      have hneg : Real.log (Real.log 2) < 0 :=
        Real.log_neg (Real.log_pos (by norm_num)) log_two_lt_one
      linarith
    · refine max_le ?_ hT10
      have := Real.log_two_lt_d9
      linarith
  have hsq : T' ^ 2 ≤ T ^ 2 := by
    gcongr
  -- the constant
  have hcst : (24 : ℝ) * ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)
      / ((((2 : ℕ) : ℝ) - 1) * Real.log ((2 : ℕ) : ℝ) ^ 4) * Real.log 3 ≤ 289 := by
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h0 : (0 : ℝ) < Real.log 2 := by linarith
    have hpos : (0 : ℝ) < Real.log 2 ^ 4 := by positivity
    have h3 : Real.log 3 ≤ 2 * Real.log 2 := log_three_le_two_log_two
    have hsq2 : (0.4804 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith
    have hcube : (0.3329 : ℝ) ≤ Real.log 2 ^ 3 := by nlinarith
    have hquart : (96.2 : ℝ) * Real.log 2 ≤ 289 * Real.log 2 ^ 4 := by nlinarith
    rw [show (24 : ℝ) * 2 * (2 - 1) / ((2 - 1) * Real.log 2 ^ 4) = 48 / Real.log 2 ^ 4 by
      norm_num]
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  have hAnn : (0 : ℝ) ≤ (24 : ℝ) * ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)
      / ((((2 : ℕ) : ℝ) - 1) * Real.log ((2 : ℕ) : ℝ) ^ 4) := by
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have general : ∀ A : ℝ, 0 ≤ A → A * Real.log 3 ≤ 289 →
      A * T' ^ 2 * Real.log 3 * L ≤ 289 * T ^ 2 * L := by
    intro A hA hAc
    have h2 : A * T' ^ 2 * Real.log 3 * L = (A * Real.log 3) * (T' ^ 2 * L) := by ring
    rw [h2]
    calc (A * Real.log 3) * (T' ^ 2 * L)
        ≤ 289 * (T' ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hAc (mul_nonneg (sq_nonneg _) hLpos.le)
      _ ≤ 289 * (T ^ 2 * L) := by
          have := mul_le_mul_of_nonneg_right hsq hLpos.le
          linarith
      _ = 289 * T ^ 2 * L := by ring
  calc (n : ℝ) ≤ ((padicValRat 2 ((3 : ℚ) ^ n - q) : ℤ) : ℝ) := hlhs
    _ ≤ BugeaudLaurent.bound 24 2 (((2 : ℕ) : ℝ) - 1) 10 10 (Real.log 3) L
        (BugeaudLaurent.bPrime n 1 (Real.log 3) L) := key
    _ ≤ 289 * T ^ 2 * L := by
        rw [BugeaudLaurent.bound, ← hT'def]
        exact general _ hAnn hcst

/-! ## 5. The self-improvement: `u = n/L` is bounded outright -/

/-- **The numeric lemma.**  `300(log u + 2)² < u` for `u ≥ 10⁶`.  Substituting `y = u^{1/8}`
(written as `exp(log u/8)`, so that no `rpow` is needed) turns the transcendental inequality into
a polynomial one: `log u = 8 log y ≤ 8(y − 1)` and `y ≥ 5.6`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem log_sq_lt_self {u : ℝ} (hu : (10 : ℝ) ^ 6 ≤ u) : 300 * (Real.log u + 2) ^ 2 < u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu
  set y : ℝ := Real.exp (Real.log u / 8) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy8 : y ^ 8 = u := by
    rw [hy, ← Real.exp_nat_mul,
      show ((8 : ℕ) : ℝ) * (Real.log u / 8) = Real.log u by push_cast; ring]
    exact Real.exp_log hu0
  have hlogy : Real.log y = Real.log u / 8 := Real.log_exp _
  have hly : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have hlogu : Real.log u ≤ 8 * (y - 1) := by rw [hlogy] at hly; linarith
  have hlogpos : 0 < Real.log u := Real.log_pos (lt_of_lt_of_le (by norm_num) hu)
  have hy56 : (5.6 : ℝ) ≤ y := by
    by_contra hcon
    push Not at hcon
    have h1 : y ^ 8 < (5.6 : ℝ) ^ 8 := by gcongr
    rw [hy8] at h1
    norm_num at h1
    linarith
  have h66 : (30840 : ℝ) ≤ y ^ 6 := by
    have h1 : (5.6 : ℝ) ^ 6 ≤ y ^ 6 := by gcongr
    norm_num at h1
    linarith
  have h6 : 30840 * y ^ 2 ≤ y ^ 8 := by
    have he : y ^ 8 = y ^ 6 * y ^ 2 := by ring
    rw [he]
    nlinarith [sq_nonneg y]
  have hL2 : Real.log u + 2 ≤ 8 * y - 6 := by linarith
  have hsq : (Real.log u + 2) ^ 2 ≤ (8 * y - 6) ^ 2 := by nlinarith
  nlinarith [h6, hy56, hsq, hy8]

/-- `exp 8 ≤ 10⁶`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem exp_eight_le : Real.exp 8 ≤ 10 ^ 6 := by
  have h1 : Real.exp 8 = (Real.exp 1) ^ 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h1]
  calc (Real.exp 1) ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 := by
        gcongr
        exact Real.exp_one_lt_d9.le
    _ ≤ 10 ^ 6 := by norm_num

/-- **The self-improvement.**  `L = log A₂ ≥ n/10⁶` — the master inequality is *self-defeating*
below that height, because `b'` depends on `n` only through `u = n/L`, so the same inequality
bounds `u` outright.  This is the whole of S3(ii): the "`B'`-refinement" is not a second device,
it is the substitution `u = n/L` in the first one. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem le_defectLogA {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) :
    (n : ℝ) / 10 ^ 6 ≤ defectLogA D n := by
  set L := defectLogA D n with hLdef
  have hLpos : 0 < L := defectLogA_pos D n
  by_contra hcon
  push Not at hcon
  have hnL : 10 ^ 6 * L < (n : ℝ) := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)] at hcon
    linarith
  set u : ℝ := (n : ℝ) / L with hudef
  have hu6 : (10 : ℝ) ^ 6 ≤ u := by
    rw [hudef, le_div_iff₀ hLpos]
    linarith
  have hu1 : (1 : ℝ) ≤ u := le_trans (by norm_num) hu6
  have hupos : (0 : ℝ) < u := by linarith
  have hlogu8 : (8 : ℝ) ≤ Real.log u :=
    (Real.le_log_iff_exp_le hupos).mpr (le_trans exp_eight_le hu6)
  -- `T ≤ log u + 2`
  have hT : max (Real.log (u + 1) + 1) 10 ≤ Real.log u + 2 := by
    refine max_le ?_ (by linarith)
    have h1 : Real.log (u + 1) ≤ Real.log (2 * u) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * u) = Real.log 2 + Real.log u :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 2 < 1 := log_two_lt_one
    linarith
  have hmas := master hD hbig
  rw [← hLdef, ← hudef] at hmas
  have hTnn : (0 : ℝ) ≤ max (Real.log (u + 1) + 1) 10 := le_trans (by norm_num) (le_max_right _ _)
  have hsq : (max (Real.log (u + 1) + 1) 10) ^ 2 ≤ (Real.log u + 2) ^ 2 := by gcongr
  have hstep : u ≤ 289 * (Real.log u + 2) ^ 2 := by
    rw [hudef, div_le_iff₀ hLpos]
    nlinarith [hmas, hsq, hLpos, sq_nonneg (Real.log u + 2)]
  have := log_sq_lt_self hu6
  nlinarith [sq_nonneg (Real.log u + 2)]

/-! ## 6. The two rungs of S3 -/

/-- `8n < 2ⁿ` for `n ≥ 6`. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem eight_mul_lt_two_pow {n : ℕ} (hn : 6 ≤ n) : 8 * n < 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · have : k = 5 := by omega
      subst this
      norm_num
    · have h1 := ih (by omega)
      have h2 : (8 : ℕ) ≤ 2 ^ k := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 8 * (k + 1) = 8 * k + 8 := by ring
        _ < 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring

/-- **The burn-in.**  `4(n + D) < 2ⁿ` holds from `n = D + 6` on. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem burnin_of_le {D n : ℕ} (h : D + 6 ≤ n) : 4 * (n + D) < 2 ^ n := by
  have h1 : 8 * n < 2 ^ n := eight_mul_lt_two_pow (by omega)
  omega

/-- **S3(i): the sub-exponential gain.**  `‖D(3/2)ⁿ‖ ≥ exp(n/(289(log n + 12)²))/(2D·2ⁿ)` —
an unconditional improvement of the free 2-adic floor `2^{-n}` at every odd multiplier, with the
gain `exp(cn/(log n)²)` announced by the strategy row.  The rate is still `θ = 1/2`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem dist_ge_subexp {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) :
    Real.exp ((n : ℝ) / (289 * (Real.log n + 12) ^ 2)) / (2 * (D : ℝ) * 2 ^ n)
      ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  have hn1 : 1 ≤ n := one_le_of_burnin hD hbig
  have hDpos : 0 < D := hD.pos
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
  set L := defectLogA D n with hLdef
  have hLpos : 0 < L := defectLogA_pos D n
  have hL2 : Real.log 2 ≤ L := log_two_le_defectLogA D n
  -- `T ≤ log n + 12`
  have hbnd : (n : ℝ) / L + 1 ≤ 3 * n := by
    have h1 : (n : ℝ) / L ≤ (n : ℝ) / Real.log 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (Real.log_pos (by norm_num)) hL2
    have h2 : (n : ℝ) / Real.log 2 ≤ 2 * n := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hT : max (Real.log ((n : ℝ) / L + 1) + 1) 10 ≤ Real.log n + 12 := by
    refine max_le ?_ (by linarith)
    have h1 : Real.log ((n : ℝ) / L + 1) ≤ Real.log (3 * n) :=
      Real.log_le_log (by positivity) hbnd
    have h2 : Real.log (3 * n) = Real.log 3 + Real.log n :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 3 ≤ 2 * Real.log 2 := log_three_le_two_log_two
    have h4 : Real.log 2 < 1 := log_two_lt_one
    linarith
  have hmas := master hD hbig
  rw [← hLdef] at hmas
  have hTnn : (0 : ℝ) ≤ max (Real.log ((n : ℝ) / L + 1) + 1) 10 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hsq : (max (Real.log ((n : ℝ) / L + 1) + 1) 10) ^ 2 ≤ (Real.log n + 12) ^ 2 := by gcongr
  have hLlow : (n : ℝ) / (289 * (Real.log n + 12) ^ 2) ≤ L := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hmas, hsq, hLpos, sq_nonneg (Real.log n + 12)]
  -- transport to the defect
  have hXpos : (0 : ℝ) < 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) := by
    have hNne : defect D n ≠ 0 := defect_ne_zero hD hn1
    have h1 : (0 : ℝ) < |((defect D n : ℤ) : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast hNne)
    positivity
  have hexp : Real.exp ((n : ℝ) / (289 * (Real.log n + 12) ^ 2))
      ≤ 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) :=
    (Real.le_log_iff_exp_le hXpos).mp (le_trans hLlow (defectLogA_le hD hn1))
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hdist : distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)
      = |((defect D n : ℤ) : ℝ)| / 2 ^ n := by
    rw [abs_defect_eq]
    field_simp
  rw [hdist, div_le_div_iff₀ (by positivity) h2n]
  nlinarith [hexp, h2n.le, hDR]

/-- **S3(ii): a T0-type rate, methodologically disjoint from S1.**  `‖D(3/2)ⁿ‖ ≥ (1/2D)·θⁿ` with
`θ = 1000001/2000000 > 1/2`, at every odd multiplier `D`, for every `n` past the burn-in — proved
from the 2-adic two-log engine alone, with no Padé approximation anywhere in the chain. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem dist_ge_theta {D n : ℕ} (hD : Odd D) (hbig : 4 * (n + D) < 2 ^ n) :
    1 / (2 * (D : ℝ)) * ((1000001 : ℝ) / 2000000) ^ n
      ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := by
  have hn1 : 1 ≤ n := one_le_of_burnin hD hbig
  have hDpos : 0 < D := hD.pos
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hXpos : (0 : ℝ) < 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) := by
    have hNne : defect D n ≠ 0 := defect_ne_zero hD hn1
    have h1 : (0 : ℝ) < |((defect D n : ℤ) : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast hNne)
    positivity
  have hexp : Real.exp ((n : ℝ) / 10 ^ 6) ≤ 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) :=
    (Real.le_log_iff_exp_le hXpos).mp (le_trans (le_defectLogA hD hbig) (defectLogA_le hD hn1))
  have hgeom : ((1000001 : ℝ) / 1000000) ^ n ≤ Real.exp ((n : ℝ) / 10 ^ 6) := by
    have h1 : (1000001 : ℝ) / 1000000 ≤ Real.exp (1 / 10 ^ 6) := by
      have h2 := Real.add_one_le_exp ((1 : ℝ) / 10 ^ 6)
      norm_num at h2 ⊢
      linarith
    calc ((1000001 : ℝ) / 1000000) ^ n ≤ (Real.exp (1 / 10 ^ 6)) ^ n := by
          gcongr
      _ = Real.exp ((n : ℝ) * (1 / 10 ^ 6)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp ((n : ℝ) / 10 ^ 6) := by ring_nf
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hdist : distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)
      = |((defect D n : ℤ) : ℝ)| / 2 ^ n := by
    rw [abs_defect_eq]
    field_simp
  have hpow : ((1000001 : ℝ) / 2000000) ^ n * 2 ^ n = ((1000001 : ℝ) / 1000000) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [hdist, le_div_iff₀ h2n]
  have hkey : ((1000001 : ℝ) / 1000000) ^ n ≤ 2 * |((defect D n : ℤ) : ℝ)| * (D : ℝ) :=
    le_trans hgeom hexp
  have hrw : 1 / (2 * (D : ℝ)) * ((1000001 : ℝ) / 2000000) ^ n * 2 ^ n
      = ((1000001 : ℝ) / 1000000) ^ n / (2 * (D : ℝ)) := by
    rw [mul_assoc, hpow]
    ring
  rw [hrw, div_le_iff₀ (by positivity)]
  nlinarith [hkey, hDR]

/-- The rate clears the free `1/2` — the point of the item. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem theta_padic_gt_half : (1 : ℝ) / 2 < (1000001 : ℝ) / 2000000 := by norm_num

/-- …and does not clear `2/3`, so this is a T0 rung and not a solution of the T-shift problem. -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem theta_padic_lt_two_thirds : (1000001 : ℝ) / 2000000 < 2 / 3 := by norm_num

/-- **The multiplier form.**  `IsRepelledMul θ D` at `θ = 1000001/2000000` for every odd `D`. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem isRepelledMul_padic {D : ℕ} (hD : Odd D) :
    IsRepelledMul ((1000001 : ℝ) / 2000000) D := by
  have hDpos : 0 < D := hD.pos
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  refine ⟨1 / (2 * (D : ℝ)), by positivity, D + 6, fun n hn => ?_⟩
  exact dist_ge_theta hD (burnin_of_le hn)

/-- **At every cycle target**, with every numeral exhibited: `‖(3/2)ⁿ − A/D_p‖ ≥ c·θⁿ` for
`n ≥ D_p + 6`, with `θ = 1000001/2000000` and `c = 1/(2D_p²)`.  Compare `TShift.repelledAt_half`
(the free `1/2`) and `TShift.repelledAt_habsieger` (the transported `0.57434`): this rate is far
weaker than the latter, and its interest is that its engine is disjoint from both. -/
@[category research solved, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem repelledAt_padic {p : ℕ} (hp : 1 ≤ p) (A : ℤ) :
    RepelledAt p A (1000001 / 2000000) (1 / (2 * (Z32.cycleDenom p : ℚ) ^ 2))
      (Z32.cycleDenom p + 6) := by
  intro n hn
  have hDodd : Odd (Z32.cycleDenom p) := Z32.cycleDenom_odd hp
  have hDpos : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hDpos
  have hmul := dist_ge_theta hDodd (burnin_of_le hn)
  have hred := distToNearestInt_mul_le hDpos (((3 : ℝ) / 2) ^ n) A
  have hcast : ((1 / (2 * (Z32.cycleDenom p : ℚ) ^ 2) : ℚ) : ℝ)
      * ((1000001 / 2000000 : ℚ) : ℝ) ^ n
      = (1 / (2 * ((Z32.cycleDenom p : ℕ) : ℝ) ^ 2)) * ((1000001 : ℝ) / 2000000) ^ n := by
    push_cast
    ring
  rw [hcast]
  have h1 : 1 / (2 * ((Z32.cycleDenom p : ℕ) : ℝ)) * ((1000001 : ℝ) / 2000000) ^ n
      ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) :=
    le_trans hmul hred
  have h2 : ((1000001 : ℝ) / 2000000) ^ n
      ≤ 2 * ((Z32.cycleDenom p : ℕ) : ℝ) ^ 2
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := by
    calc ((1000001 : ℝ) / 2000000) ^ n
        = (2 * ((Z32.cycleDenom p : ℕ) : ℝ))
          * (1 / (2 * ((Z32.cycleDenom p : ℕ) : ℝ)) * ((1000001 : ℝ) / 2000000) ^ n) := by
          field_simp
      _ ≤ (2 * ((Z32.cycleDenom p : ℕ) : ℝ))
          * (((Z32.cycleDenom p : ℕ) : ℝ)
            * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * ((Z32.cycleDenom p : ℕ) : ℝ) ^ 2
          * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith [h2]

/-- The S3 rate is not a solution of the effective problem (`θ < 2/3`). -/
@[category API, AMS 11, ref "TshiftS3", group "tshift_s3"]
theorem not_tShiftProblemAt_padic {p : ℕ} {A : ℤ} {c : ℚ} {n₀ : ℕ} :
    ¬ TShiftProblemAt p A (1000001 / 2000000) c n₀ := by
  rintro ⟨h, -⟩
  norm_num at h

end TShift
