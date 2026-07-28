/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import ForMathlib.NumberTheory.PadicValAdd
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exact 2-adic toolkit for the (3/2)ⁿ program (A5, T1)

The bottom `O(log n)` bits of `3ⁿ` are *exactly periodic*, and everything about them is
governed by lifting-the-exponent at `p = 2` — not by estimates.  This file is the exact,
unconditional, axiom-free layer that plan A5 (`plans/plan-A5.html`) calls T1.

Writing `v₂ = padicValNat 2` (and `padicValInt 2` on `ℤ`), the headline is

  `v₂(3^e − 1) = 2 + v₂(e)` for even `e`,   `= 1` for odd `e`,

sharp at `e = 2^(N-2)`, whence the multiplicative order `ord(3 mod 2^k) = 2^(k-2)` for
`k ≥ 3` and the window criterion `2^k ∣ 3^e − 1 ↔ 2^(k-2) ∣ e` consumed by
`TH.WindowSeparation`.  On the orbit side the relevant quantities are *odd*
(`odd_three_pow_sub_two_pow`, `padicValInt_three_pow_sub_three_pow_mul_two_pow`), and the
second differences `(3^d − 2^d) − (3^d' − 2^d')` have exactly computable valuations
(`v2_second_difference`, with the diagonal case `v2_second_difference_diagonal`).

## The difficulty map: a trichotomy of bit regimes ([A5] T5)

The `(3/2)ⁿ` programme is, quite literally, a statement about `3ⁿ mod 2ⁿ`.  Since
`m_n = round((3/2)ⁿ)`, the numerator `R_n = 3ⁿ − 2ⁿ·m_n` of `TH.Basic` satisfies
`|R_n| < 2^(n-1)`, so **`R_n` is the centered residue of `3ⁿ` modulo `2ⁿ`**.  Read that way
the bits of `3ⁿ` fall into three regimes, and it is worth being explicit about which engine
owns which:

* **Bottom `O(log n)` bits — exactly periodic.**  `n ↦ 3ⁿ mod 2^N` has period exactly
  `2^(N-2)` (`orderOf_three_zmod`), so at *fixed* `N` the bottom word is purely periodic and
  everything about it is an identity.  This file and `TH.WindowSeparation` own this regime,
  and own it exactly.
* **Top `O(n)` bits — archimedean.**  Governed by growth: TH's repetition layer
  (`repetition_pow_le`, the `(2/3)^k` contraction) and, past it, the Diophantine kernel with
  its Subspace-grade input (`CITED/CorvajaZannier.lean`, `Subspace.evertseSchlickewei`).
* **The middle band — the hard regime.**  Owned by Stewart-type digit bounds and the A4+/M4
  machinery (`TH/StewartDigits.lean`, `TH/ComplexityLower.lean`).

The boundary matters here because A5's regime is *inert* where the programme needs it.  W1
governs the bottom `N` bits at **fixed** `N`; once `N` grows with `n` — which is exactly the
case `R_n mod 2ⁿ` presents — the period `2^(n-2)` vastly exceeds `n` and the periodicity says
nothing about the finitely many `n` in range.  That is not a defect of the tools; it is why
A5 stops at the regime boundary by design, and why the middle band belongs to plan A4+.

## Where elementary ends, and the do-not-wire note ([A5] T5, §2.2)

Two-term forms over `Γ = ⟨2,3⟩` at the place `2` are the *whole* of what elementary
technology gives, and they give it exactly.  The reason is structural: `ℤ₂ˣ = {±1} × (1+4ℤ₂)`
with `−3 ≡ 5 (mod 8)` generating the procyclic factor, so the only `2`-adic units in `Γ` are
`±3^m` and `v₂(3^m ∓ 1)` is the identity proved below — not an estimate that some deeper
theorem might sharpen.  Genuine hardness starts at **three**-term forms
(`3^a − 3^b − 2^c`-shaped, or window agreements with a bounded but unstructured remainder):
those reduce to `v₂(3^b u − 1)` with `u` of height growing like `3^a`, which is Subspace
territory (already represented in the corpus by CZ04/NKR25) — or else the "middle-window
agreement" reading, `3ⁿ mod 2^V` landing in a short interval, which *is* the distribution
problem and so is circular as an input.

**Consequently `CITED/YuPadicForms.lean` must not be wired into the `p = 2` layer of this
programme.**  That file supplies `Yu.padicVal2_prod_sub_one_lt`, a general effective `p`-adic
linear-forms bound; it carries `group "three_halves_m4"` — this programme's own group — and
its `p = 2` instance is docstring-advertised as "the effective flat-window prime of the
`(3/2)ⁿ` program", so it sits exactly where a future reader would reach for it.  It would
lose information twice over: at two terms because LTE is an identity, and at three terms
because Yu's bound is linear in `h(u)`, i.e. `≫ a`, against the *trivial* size bound
`v₂ ≤ log₂|Λ| ≈ 1.585 a`.

This is a scoped exclusion, not a dismissal: the file is correctly stated and Yu genuinely
earns its keep at other primes, over number fields, and in that file's sharp `𝔭 = 3` line
(`Yu.ord3_prod_sub_one_lt_sharp`).  The exclusion is to `p = 2` on `Γ = ⟨2,3⟩` alone.

## Contents

* `v2_three_pow_sub_one` — the LTE closed form; `v2_three_pow_sub_one_sharp` — sharpness.
* `two_pow_dvd_three_pow_sub_one_iff` — `2^k ∣ 3^e − 1 ↔ 2^(k-2) ∣ e` (`k ≥ 3`).
* `orderOf_three_zmod` — `ord(3 mod 2^k) = 2^(k-2)` (`k ≥ 3`).
* `odd_three_pow_sub_two_pow`, `padicValInt_three_pow_sub_three_pow_mul_two_pow` — the
  oddness facts behind the trivial repulsion floor of `TH.Basic`.
* `v2_second_difference`, `v2_second_difference_diagonal` — the second-difference
  trichotomy `v₂((3^d − 2^d) − (3^d' − 2^d')) = min(v₂(3^{d-d'} − 1), d')`.

## References

* [A5] `plans/plan-A5.html` (this repository, 2026-07): §2.1 (the exact 2-adic structure),
  §2.2 and §0.1 Finding 5 (why Yu dissolves here), WP1.
* [M4A3] `plans/plan-M4A3.html`: the ambient program.
* Lifting-the-exponent at `p = 2` is classical; the Mathlib entry point is
  `padicValNat.pow_two_sub_one`, completed for odd exponents by
  `padicValNat.pow_two_sub_one_of_odd` in `ForMathlib.NumberTheory.PadicValAdd`.
-/

namespace TH

/-! ## `2`-adic valuation helpers on `ℤ` -/

/-- An odd integer has `2`-adic valuation `0`. -/
private lemma padicValInt_two_of_odd {z : ℤ} (hz : Odd z) : padicValInt 2 z = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  intro h
  rw [Int.odd_iff] at hz
  omega

/-- `v₂(2^c · z) = c` for odd `z`. -/
private lemma padicValInt_two_pow_mul {c : ℕ} {z : ℤ} (hz : Odd z) :
    padicValInt 2 ((2 : ℤ) ^ c * z) = c := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  rw [padicValInt.mul (by positivity) hz0, padicValInt_two_of_odd hz, add_zero,
    show ((2 : ℤ) ^ c) = (((2 ^ c : ℕ) : ℤ)) by push_cast; ring, padicValInt.of_nat,
    padicValNat.prime_pow]

/-! ## The lifting-the-exponent closed form -/

/-- **The exact 2-adic valuation of `3^e − 1`** ([A5] §2.1, T1 headline).  Since `−3 ≡ 5
(mod 8)` topologically generates `1 + 4ℤ₂`,

  `v₂(3^e − 1) = 2 + v₂(e)` for even `e ≠ 0`,   `v₂(3^e − 1) = 1` for odd `e`.

The even branch is lifting-the-exponent (`padicValNat.pow_two_sub_one` at `x = 3`, where
`v₂(4) + v₂(2) = 3`); the odd branch needs no lifting at all
(`padicValNat.pow_two_sub_one_of_odd`, `v₂(3 − 1) = 1`). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem v2_three_pow_sub_one {e : ℕ} (he : e ≠ 0) :
    padicValNat 2 (3 ^ e - 1) = if Even e then 2 + padicValNat 2 e else 1 := by
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  rcases Nat.even_or_odd e with hev | hod
  · rw [if_pos hev]
    have := padicValNat.pow_two_sub_one (x := 3) (n := e) (by norm_num) (by norm_num) he hev
    norm_num [h4, h2] at this
    omega
  · rw [if_neg (by simpa [Nat.not_even_iff_odd] using hod),
      padicValNat.pow_two_sub_one_of_odd (by norm_num) (by norm_num) hod]
    norm_num [h2]

/-- **Sharpness** of `v2_three_pow_sub_one`: at `e = 2^(N-2)` the valuation is exactly `N`,
so the closed form cannot be improved — an `N`-bit bottom window really does survive a gap
of `2^(N-2)`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem v2_three_pow_sub_one_sharp {N : ℕ} (hN : 3 ≤ N) :
    padicValNat 2 (3 ^ (2 ^ (N - 2)) - 1) = N := by
  have hne : (2 : ℕ) ^ (N - 2) ≠ 0 := by positivity
  rw [v2_three_pow_sub_one hne, if_pos, padicValNat.prime_pow]
  · omega
  · exact (Nat.even_pow' (by omega)).mpr (by decide)

/-- **Window criterion** ([A5] W1): for `k ≥ 3`, the bottom `k` bits of `3^e` agree with
those of `1` exactly when `2^(k-2)` divides `e`.  This is the divisibility face of
`orderOf_three_zmod`, and the form `TH.WindowSeparation` consumes. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem two_pow_dvd_three_pow_sub_one_iff {k e : ℕ} (hk : 3 ≤ k) :
    (2 : ℕ) ^ k ∣ 3 ^ e - 1 ↔ 2 ^ (k - 2) ∣ e := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have h3 : 3 ≤ (3 : ℕ) ^ e :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega) : (3 : ℕ) ^ 1 ≤ 3 ^ e)
  have hne : (3 : ℕ) ^ e - 1 ≠ 0 := by omega
  rw [padicValNat_dvd_iff_le hne, v2_three_pow_sub_one he, padicValNat_dvd_iff_le he]
  rcases Nat.even_or_odd e with hev | hod
  · rw [if_pos hev]; omega
  · rw [if_neg (by simpa [Nat.not_even_iff_odd] using hod)]
    have hmod : e % 2 = 1 := Nat.odd_iff.mp hod
    refine ⟨by omega, fun h => ?_⟩
    have h1 : 1 ≤ padicValNat 2 e := by omega
    rw [← padicValNat_dvd_iff_le he] at h1
    simp only [pow_one] at h1
    omega

/-- Bridge to `ZMod (2^k)`: `3^e = 1` there exactly when `2^k ∣ 3^e − 1` in `ℕ`. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
lemma three_pow_zmod_eq_one_iff (k e : ℕ) :
    (3 : ZMod (2 ^ k)) ^ e = 1 ↔ (2 : ℕ) ^ k ∣ 3 ^ e - 1 := by
  have h1 : ((3 : ℕ) : ZMod (2 ^ k)) ^ e = 1 ↔ 3 ^ e ≡ 1 [MOD 2 ^ k] := by
    rw [← Nat.cast_pow, Nat.ModEq, ← ZMod.natCast_eq_natCast_iff']
    push_cast
    simp
  have hge : 1 ≤ (3 : ℕ) ^ e := Nat.one_le_pow _ _ (by norm_num)
  rw [show ((3 : ZMod (2 ^ k))) = ((3 : ℕ) : ZMod (2 ^ k)) by push_cast; ring, h1]
  exact ⟨fun h => (Nat.modEq_iff_dvd' hge).mp h.symm,
    fun h => ((Nat.modEq_iff_dvd' hge).mpr h).symm⟩

/-- **The multiplicative order of `3` mod `2^k`** ([A5] §2.1): `ord(3 mod 2^k) = 2^(k-2)`
for `k ≥ 3`.  Equivalently, `⟨3⟩` has index `2` in `(ℤ/2^k)ˣ` — the exact periodicity of
the bottom `k` bits of `3ⁿ`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem orderOf_three_zmod {k : ℕ} (hk : 3 ≤ k) :
    orderOf (3 : ZMod (2 ^ k)) = 2 ^ (k - 2) := by
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
  · rw [three_pow_zmod_eq_one_iff, two_pow_dvd_three_pow_sub_one_iff hk]
  · rw [← two_pow_dvd_three_pow_sub_one_iff hk, ← three_pow_zmod_eq_one_iff]
    exact pow_orderOf_eq_one _

/-! ## Oddness on the orbit side -/

/-- `3^d − 2^d` is odd for `d ≥ 1` — the numerator fact behind the trivial `2^{-c}`
repulsion floor `TH.one_le_two_pow_mul_distToNearestInt_orbit` of `TH.Basic`. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
lemma odd_three_pow_sub_two_pow {d : ℕ} (hd : 1 ≤ d) : Odd ((3 : ℤ) ^ d - 2 ^ d) := by
  obtain ⟨w, hw⟩ : (2 : ℤ) ∣ (2 : ℤ) ^ d := dvd_pow_self 2 (by omega)
  have h3 : (3 : ℤ) ^ d % 2 = 1 := Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  exact Int.odd_iff.mpr (by omega)

/-- The report's literal `v₂(3^a − 3^b·2^c)` target is trivial: for `c ≥ 1` the quantity is
odd minus even, so its valuation is `0` ([A5] §2.1 — a symptom of the mislabeling that
plan A5 corrects). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem padicValInt_three_pow_sub_three_pow_mul_two_pow {a b c : ℕ} (hc : 1 ≤ c) :
    padicValInt 2 ((3 : ℤ) ^ a - 3 ^ b * 2 ^ c) = 0 := by
  refine padicValInt_two_of_odd (Int.odd_iff.mpr ?_)
  have h3 : (3 : ℤ) ^ a % 2 = 1 := Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  obtain ⟨w, hw⟩ : (2 : ℤ) ∣ (2 : ℤ) ^ c := dvd_pow_self 2 (by omega)
  have heven : (3 : ℤ) ^ b * 2 ^ c = 2 * ((3 : ℤ) ^ b * w) := by rw [hw]; ring
  rw [heven]
  omega

/-! ## Second differences -/

/-- **Second-difference valuation** ([A5] §2.1, T1): for `d' < d` and
`e = d − d'`, the identity `(3^d − 2^d) − (3^{d'} − 2^{d'}) = 3^{d'}(3^e − 1) −
2^{d'}(2^e − 1)` has an odd cofactor on each side, so off the diagonal
`v₂(3^e − 1) ≠ d'` the ultrametric equality gives the valuation exactly:

  `v₂((3^d − 2^d) − (3^{d'} − 2^{d'})) = min(v₂(3^e − 1), d')`.

Combined with `v2_three_pow_sub_one`, both entries are closed-form computable — the
elementary substrate for coarse-scale pair counting ([A5] T3). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem v2_second_difference {d d' : ℕ} (hlt : d' < d)
    (hne : padicValNat 2 (3 ^ (d - d') - 1) ≠ d') :
    padicValInt 2 (((3 : ℤ) ^ d - 2 ^ d) - ((3 : ℤ) ^ d' - 2 ^ d'))
      = min (padicValNat 2 (3 ^ (d - d') - 1)) d' := by
  obtain ⟨e, rfl⟩ : ∃ e, d = d' + e := ⟨d - d', by omega⟩
  have he1 : 1 ≤ e := by omega
  simp only [show d' + e - d' = e by omega] at hne ⊢
  have h3ge : (3 : ℕ) ≤ 3 ^ e :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he1 : (3 : ℕ) ^ 1 ≤ 3 ^ e)
  have hcast : ((3 : ℤ) ^ e - 1) = ((3 ^ e - 1 : ℕ) : ℤ) := by
    push_cast [Nat.one_le_pow e 3 (by norm_num)]; ring
  have h3ne : ((3 : ℤ) ^ e - 1) ≠ 0 := by
    rw [hcast]; exact_mod_cast (by omega : (3 ^ e - 1 : ℕ) ≠ 0)
  set X : ℤ := (3 : ℤ) ^ d' * ((3 : ℤ) ^ e - 1) with hXdef
  set Y : ℤ := -((2 : ℤ) ^ d' * ((2 : ℤ) ^ e - 1)) with hYdef
  have hXv : padicValInt 2 X = padicValNat 2 (3 ^ e - 1) := by
    rw [hXdef, padicValInt.mul (by positivity) h3ne,
      padicValInt_two_of_odd ((Int.odd_iff.mpr (by norm_num)).pow), zero_add,
      hcast, padicValInt.of_nat]
  have h2e : (2 : ℤ) ∣ (2 : ℤ) ^ e := dvd_pow_self 2 (by omega)
  have hYodd : Odd (-((2 : ℤ) ^ e - 1)) := by
    obtain ⟨w, hw⟩ := h2e; exact Int.odd_iff.mpr (by omega)
  have hYv : padicValInt 2 Y = d' := by
    rw [hYdef, show -((2 : ℤ) ^ d' * ((2 : ℤ) ^ e - 1)) = (2 : ℤ) ^ d' * (-((2 : ℤ) ^ e - 1))
      by ring]
    exact padicValInt_two_pow_mul hYodd
  have hXne : X ≠ 0 := by rw [hXdef]; positivity
  have hYne : Y ≠ 0 := by
    rw [hYdef]
    have h1 : ((2 : ℤ) ^ e - 1) ≠ 0 := by
      have : (2 : ℤ) ≤ 2 ^ e :=
        le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) he1 : (2 : ℤ) ^ 1 ≤ 2 ^ e)
      omega
    simp [h1]
  have hvne : padicValInt 2 X ≠ padicValInt 2 Y := by rw [hXv, hYv]; exact hne
  have hsum : X + Y ≠ 0 := by
    intro h
    have hYX : Y = -X := by linarith
    rw [hYX, padicValInt_neg] at hvne
    exact hvne rfl
  have hsplit : ((3 : ℤ) ^ (d' + e) - 2 ^ (d' + e)) - ((3 : ℤ) ^ d' - 2 ^ d') = X + Y := by
    rw [hXdef, hYdef]; ring
  rw [hsplit, padicValInt_add_eq_min hsum hXne hYne hvne, hXv, hYv]

/-- **The diagonal case** ([A5] §2.1): when `v₂(3^{d-d'} − 1) = d'` the two terms have
equal valuation and the leading digits cancel, so the valuation jumps to at least `d' + 1`
(the exact value is resolved one level deeper). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem v2_second_difference_diagonal {d d' : ℕ} (hlt : d' < d)
    (hdiag : padicValNat 2 (3 ^ (d - d') - 1) = d') :
    (2 : ℤ) ^ (d' + 1) ∣ ((3 : ℤ) ^ d - 2 ^ d) - ((3 : ℤ) ^ d' - 2 ^ d') := by
  obtain ⟨e, rfl⟩ : ∃ e, d = d' + e := ⟨d - d', by omega⟩
  have he1 : 1 ≤ e := by omega
  simp only [show d' + e - d' = e by omega] at hdiag
  have h3ge : (3 : ℕ) ≤ 3 ^ e :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he1 : (3 : ℕ) ^ 1 ≤ 3 ^ e)
  have hne : (3 : ℕ) ^ e - 1 ≠ 0 := by omega
  -- write `3^e − 1 = 2^{d'}·u` with `u` odd, using that `d'` is exactly the valuation
  obtain ⟨u, hu⟩ : (2 : ℕ) ^ d' ∣ 3 ^ e - 1 := by
    rw [padicValNat_dvd_iff_le hne, hdiag]
  have huodd : ¬ 2 ∣ u := by
    intro ⟨v, hv⟩
    have : (2 : ℕ) ^ (d' + 1) ∣ 3 ^ e - 1 := ⟨v, by rw [hu, hv]; ring⟩
    rw [padicValNat_dvd_iff_le hne, hdiag] at this
    omega
  -- transport to `ℤ`
  have hcast : ((3 : ℤ) ^ e - 1) = (2 : ℤ) ^ d' * (u : ℤ) := by
    have : (((3 ^ e - 1 : ℕ)) : ℤ) = ((2 ^ d' * u : ℕ) : ℤ) := by rw [hu]
    push_cast [Nat.one_le_pow e 3 (by norm_num)] at this
    linarith
  obtain ⟨w, hw⟩ : (2 : ℤ) ∣ (2 : ℤ) ^ e := dvd_pow_self 2 (by omega)
  -- `3^{d'}·u` and `2^e − 1` are both odd, so their difference is `2s`
  have h3d : (3 : ℤ) ^ d' % 2 = 1 := Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (3 : ℤ) ^ d' * (u : ℤ) - ((2 : ℤ) ^ e - 1) = 2 * s := by
    have hum : (u : ℤ) % 2 = 1 := by
      have h : u % 2 = 1 := by omega
      omega
    have hprod : ((3 : ℤ) ^ d' * (u : ℤ)) % 2 = 1 := by
      rw [Int.mul_emod, h3d, hum]; norm_num
    exact ⟨((3 : ℤ) ^ d' * (u : ℤ) - ((2 : ℤ) ^ e - 1)) / 2, by omega⟩
  refine ⟨s, ?_⟩
  have hsplit : ((3 : ℤ) ^ (d' + e) - 2 ^ (d' + e)) - ((3 : ℤ) ^ d' - 2 ^ d')
      = (3 : ℤ) ^ d' * ((3 : ℤ) ^ e - 1) - (2 : ℤ) ^ d' * ((2 : ℤ) ^ e - 1) := by ring
  rw [hsplit, hcast]
  calc (3 : ℤ) ^ d' * ((2 : ℤ) ^ d' * (u : ℤ)) - (2 : ℤ) ^ d' * ((2 : ℤ) ^ e - 1)
      = (2 : ℤ) ^ d' * ((3 : ℤ) ^ d' * (u : ℤ) - ((2 : ℤ) ^ e - 1)) := by ring
    _ = (2 : ℤ) ^ d' * (2 * s) := by rw [hs]
    _ = 2 ^ (d' + 1) * s := by ring

end TH
