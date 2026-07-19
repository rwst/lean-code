/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.ScaledKernel
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The effective slice of the kernel (plan-B1E2, referee round: S14)

**For `θ < 1/2` the whole violator set `RB.scaledViolators δ θ` is finite *effectively* and
axiom-free** (`scaledViolators_finite_of_lt_half`, std3 — no Subspace Theorem): outside the
degeneracy box `c < |δ.num|`, the quantity `δ·((3/2)^c − (3/2)^a)` is a non-integral rational
that `δ.den·2^c` clears to an integer, so the explicit **Liouville floor**

  `‖δ·((3/2)^c − (3/2)^a)‖ ≥ 1/(δ.den·2^c)`   (`one_le_den_mul_two_pow_mul_dist`)

holds, and a violator at scale `θ` must satisfy the checkable certificate
`δ.den·(2θ)^c ≥ 1` (`violator_certificate`).  Explicit constants: for ANY `N` with
`δ.den·(2θ)^N < 1` and `N ≥ |δ.num|`, every violator has `c < N`
(`violator_lt_of_certificate`); `effectiveSlice_sanity` instantiates one such certificate.

## What survives of the referee's S14, and what does not

The referee proposed effectivizing the *bounded-gap* slice via linear forms in two
logarithms.  Working it out:

* **The effective region is `θ < 1/2`, and it is GAP-UNIFORM** — nothing is gained by fixing
  the gap `s₀ = c − a`; the floor covers the whole kernel at once, which is *stronger* than
  the bounded-gap promise in this regime.
* **The two-log route is VOID.**  The nearest integer is a free third term: the relevant
  integer form is `δ.num·3^a(3^{c−a} − 2^{c−a}) − n·δ.den·2^c` with `n` unconstrained.  A
  two-logarithm bound must absorb `n` into a composite algebraic number of height `≍ c·log(3/2)`,
  so beating the trivial floor would need a two-log constant below
  `log 2/(log 3 · log(3/2)) ≈ 1.56` — an order of magnitude beyond anything proved
  (Laurent-type constants are ≥ 17).  This is the archimedean twin of the Yu-weaker-than-trivial
  verdict on three-term forms (plan-A5 / plan-formalize-logforms).  Do not re-propose.
* **Beyond `1/2` lies the Padé frontier, multiplier-1 only**: Beukers `‖(3/2)^n‖ ≥ 2^{−0.9n}`
  (`n ≥ 5000`, Math. Proc. CPS 90 (1981)), Zudilin `‖(3/2)^n‖ ≥ 0.5803^n` (JTNB 19 (2007)).
  No comparably strong bound is known with a general rational multiplier `δ`; a CITED/ entry
  is warranted only when a consumer materializes ([[cited-no-consumer-gate]] would allow it).
* **Beyond `0.5803` nothing effective exists**, and the complexity application
  (`RB.superlinear_of_K_rat`) needs `θ → 1`: the ineffectivity of
  `RB.scaledViolators_finite` is essential there, not an artifact.

## The coherence: the effective region is the empty region

The boundary `θ = 1/2` is `RB/NoStammeringRoute.lean`'s ledger in disguise: the floor
`≈ 2^{−c}` beats the repetition contraction `(2/3)^k` exactly when `k/c > log 2/log(3/2) =
1.7095…` (the DEMAND line), while actual repetitions of `wmin` obey `k/c ≤ 0.585` (the
CEILING, `RB.repetition_linear_bound`).  So the kernel is effective precisely in the region
the word never enters — the same 2-adic repulsion, seen from the approximation side.

## Contents

* **`RB.one_le_den_mul_two_pow_mul_dist`** — the explicit Liouville floor (certificate form).
* `RB.violator_certificate` — membership at scale `θ` forces `δ.den·(2θ)^c ≥ 1`.
* `RB.violator_lt_of_certificate` — explicit bound `c < N` from a checkable certificate.
* **`RB.scaledViolators_finite_of_lt_half`** — the axiom-free effective twin of
  `RB.scaledViolators_finite`, for `θ < 1/2`.
* `RB.effectiveSlice_sanity` — a worked certificate (`δ = 5/3`, `θ = 1/3`: all violators
  have `c < 5`).

## References

* [B1E2] `plans/plan-B1E2.html`; `review-B1E2.md` item S14; `plans/report2-B1E2.html`.
* [Beu81] F. Beukers. *Fractional parts of powers of rationals.* Math. Proc. Cambridge
  Philos. Soc. **90** (1981), 13–20.
* [Zud07] W. Zudilin. *A new lower bound for `‖(3/2)^k‖`.* J. Théor. Nombres Bordeaux
  **19** (2007), 311–323.
-/

namespace RB

/-- `(3/2)^c − (3/2)^a = 3^a(3^{c−a} − 2^{c−a}) / 2^c`.  (The `ScaledKernel` copy is
private, so it is re-derived here.) -/
private lemma orbit_diff_eq' {a c : ℕ} (hac : a < c) :
    (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a
      = ((3 ^ a * (3 ^ (c - a) - 2 ^ (c - a)) : ℤ) : ℚ) / (2 : ℚ) ^ c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
  rw [show a + d - a = d from by omega]
  push_cast
  simp only [div_pow]
  rw [pow_add]
  field_simp
  ring

/-- `δ.den · 2^c` clears the kernel quantity to an integer. -/
private lemma exists_int_eq (δ : ℚ) {a c : ℕ} (hac : a < c) :
    ∃ z : ℤ, (z : ℚ)
      = ((δ.den * 2 ^ c : ℤ) : ℚ) * (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) := by
  refine ⟨δ.num * (3 ^ a * (3 ^ (c - a) - 2 ^ (c - a))), ?_⟩
  have hden : ((δ.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr δ.den_nz
  have hnum : (δ.num : ℚ) = δ * (δ.den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den δ)
  rw [orbit_diff_eq' hac]
  push_cast
  rw [hnum]
  have h2c : ((2 : ℚ) ^ c) ≠ 0 := by positivity
  field_simp

/-! ## The explicit Liouville floor -/

/-- **The Liouville floor of the kernel** ([B1E2] referee, S14): outside the degeneracy box,
`‖δ·((3/2)^c − (3/2)^a)‖ ≥ 1/(δ.den·2^c)`, in the integer-certificate form.  Explicit,
axiom-free, and uniform in the gap `c − a`.  Everything effective about the kernel flows from
this floor; see the module doc for why nothing stronger is available. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem one_le_den_mul_two_pow_mul_dist {δ : ℚ} (hδ : δ ≠ 0) {a c : ℕ} (hac : a < c)
    (hc : δ.num.natAbs ≤ c) :
    1 ≤ (δ.den : ℚ) * 2 ^ c
      * (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt := by
  obtain ⟨z, hz⟩ := exists_int_eq δ hac
  have hD : (0 : ℤ) < δ.den * 2 ^ c := by positivity
  have h := Rat.one_le_mul_distToNearestInt hD hz (dist_pos_of_num_le hδ hac hc)
  calc (1 : ℚ)
      ≤ ((δ.den * 2 ^ c : ℤ) : ℚ)
        * (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt := h
    _ = (δ.den : ℚ) * 2 ^ c
        * (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt := by push_cast; ring

/-- **The violator certificate**: membership in `scaledViolators δ θ` outside the degeneracy
box forces `δ.den·(2θ)^c ≥ 1` — a checkable inequality that fails for all large `c` as soon
as `θ < 1/2`. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem violator_certificate {δ θ : ℚ} (hδ : δ ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ scaledViolators δ θ) (hc : δ.num.natAbs ≤ p.2) :
    1 ≤ (δ.den : ℚ) * (2 * θ) ^ p.2 := by
  obtain ⟨-, hac, hdist⟩ := hp
  have hfloor := one_le_den_mul_two_pow_mul_dist hδ hac hc
  have hden : (0 : ℚ) ≤ (δ.den : ℚ) := by positivity
  calc (1 : ℚ)
      ≤ (δ.den : ℚ) * 2 ^ p.2
        * (δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1)).distToNearestInt := hfloor
    _ ≤ (δ.den : ℚ) * 2 ^ p.2 * θ ^ p.2 := by
        apply mul_le_mul_of_nonneg_left hdist
        positivity
    _ = (δ.den : ℚ) * (2 * θ) ^ p.2 := by rw [mul_pow]; ring

/-! ## Effective finiteness for `θ < 1/2` -/

/-- **Explicit constants** ([B1E2] referee, S14): any `N` past the degeneracy box with
`δ.den·(2θ)^N < 1` bounds every violator, `c < N`.  The hypotheses are decidable rational
inequalities — a certificate one exhibits, not an existence statement. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem violator_lt_of_certificate {δ θ : ℚ} (hδ : δ ≠ 0) (hθ0 : 0 ≤ θ)
    (hθ1 : 2 * θ ≤ 1) {N : ℕ} (hbox : δ.num.natAbs ≤ N)
    (hN : (δ.den : ℚ) * (2 * θ) ^ N < 1) :
    ∀ p ∈ scaledViolators δ θ, p.2 < N := by
  intro p hp
  by_contra hge
  push Not at hge
  have hcert := violator_certificate hδ hp (le_trans hbox hge)
  have hmono : (2 * θ) ^ p.2 ≤ (2 * θ) ^ N :=
    pow_le_pow_of_le_one (by positivity) hθ1 hge
  have hden : (0 : ℚ) ≤ (δ.den : ℚ) := by positivity
  nlinarith [hcert, hN, mul_le_mul_of_nonneg_left hmono hden]

/-- **The effective slice** ([B1E2] referee, S14): for `θ < 1/2` the violator set is finite
with NO Diophantine input — std3, no Subspace axiom — and uniformly in the gap.  The
axiom-free effective twin of `RB.scaledViolators_finite`, on exactly the sub-half slice;
the module doc delimits why the slice cannot grow. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem scaledViolators_finite_of_lt_half {δ θ : ℚ} (hδ : δ ≠ 0) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1 / 2) : (scaledViolators δ θ).Finite := by
  have h2θ0 : (0 : ℚ) ≤ 2 * θ := by positivity
  have h2θ1 : 2 * θ < 1 := by linarith
  have hεpos : (0 : ℚ) < 1 / (δ.den : ℚ) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hεpos h2θ1
  set N := max n δ.num.natAbs with hNdef
  have hbox : δ.num.natAbs ≤ N := le_max_right _ _
  have hcertN : (δ.den : ℚ) * (2 * θ) ^ N < 1 := by
    have hmono : (2 * θ) ^ N ≤ (2 * θ) ^ n :=
      pow_le_pow_of_le_one h2θ0 (le_of_lt h2θ1) (le_max_left _ _)
    have hden : (0 : ℚ) < (δ.den : ℚ) := by positivity
    calc (δ.den : ℚ) * (2 * θ) ^ N ≤ (δ.den : ℚ) * (2 * θ) ^ n :=
          mul_le_mul_of_nonneg_left hmono hden.le
      _ < (δ.den : ℚ) * (1 / (δ.den : ℚ)) := mul_lt_mul_of_pos_left hn hden
      _ = 1 := by field_simp
  have hbound := violator_lt_of_certificate hδ hθ0 (le_of_lt h2θ1) hbox hcertN
  apply Set.Finite.subset ((Set.finite_Iio N).prod (Set.finite_Iio N))
  intro p hp
  have h2 : p.2 < N := hbound p hp
  exact ⟨lt_trans hp.2.1 h2, h2⟩

/-- A worked certificate: at `δ = 5/3`, `θ = 1/3` every violator has `c < 5` — the
degeneracy box ends at `|num| = 5` and `3·(2/3)^5 = 32/81 < 1`.  All hypotheses discharge by
computation. -/
@[category research solved, AMS 11, ref "B1E2", group "rb_rational_base"]
theorem effectiveSlice_sanity :
    ∀ p ∈ scaledViolators (5 / 3) (1 / 3), p.2 < 5 := by
  have hnum : (5 / 3 : ℚ).num.natAbs = 5 := by norm_num [Rat.num]
  refine violator_lt_of_certificate (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnum]) ?_
  have hden : (5 / 3 : ℚ).den = 3 := by norm_num [Rat.den]
  rw [hden]
  norm_num

end RB
