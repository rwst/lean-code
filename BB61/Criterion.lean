/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Covering
import BB61.RouteAConstants
import BB61.Confinement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Corollary 5: Route A fires whenever the exponent `A(α)` is below one

`BB61/Covering.lean` gives the covering engine in *finite* form: at truncation depths
`(M, M')` the orbit of fractional parts lies within `δ(M,M') = α^{-M} + (1+ρ)ρ^{M'}/(1-ρ)`
of at most `2^M · 2^{M'} · (2K+1)` candidate points (`ρ := |β|`), and if the numeric
certificate `card · 2δ < 1` holds then some open subinterval of `(0,1)` is missed by every
orbit at every time (`exists_avoided_interval`).  That is a *test*, discharged at
`α = 2+√5` in `BB61/RouteA.lean`.

This file turns the test into a **criterion**: it says exactly which `α` the test
eventually passes.  Writing

`A(α) := log 2 / log α + log 2 / log (1/ρ)`   (`routeAExponent`),

the certificate is satisfiable at some depth as soon as `A(α) < 1`
(`exists_avoided_interval_of_routeAExponent_lt_one`), hence

* `not_denseModuloOne_of_routeAExponent_lt_one`,
* `not_equidistributed_of_routeAExponent_lt_one` — **Problem 10.61 holds at every `α`
  with `A(α) < 1`**,
* `confCircle_ne_univ_of_routeAExponent_lt_one` — the same, read as M1 Proposition 4.

`A(α)` is the sum of the two box dimensions of M1 Corollary 5,
`dim_B C(α) = log2/log α` (Lemma 1(iii)) and `dim_B K ≤ log2/log(1/ρ)` (Lemma 3), and the
statement here is Corollary 5's conclusion `Leb(X(α)) = 0 ⇒ 10.61 at α` with the dimension
theory removed: the covering counts that *define* those dimensions are the engine's own
`card` and `δ`, so the asymptotics can be done directly on the certificate.
`ForMathlib/Topology/MetricSpace/BoxDimension.lean` supplies the dimensions themselves,
for the statement of Lemma 1(iii) and Lemma 3 rather than for this proof.

## The mechanism

Run the engine along the ray `(M, M') = (p·n, q·n)`.  The certificate value factors as a
sum of two geometric sequences,

`card · 2δ = (4K+2) · ( x^n + c · y^n )`,  `x = 2^{p+q} α^{-p}`, `y = 2^{p+q} ρ^{q}`,

so it tends to `0` — and is eventually `< 1` — as soon as both ratios are `< 1`
(`exists_avoided_interval_of_geom`).  Taking logarithms, `x < 1` and `y < 1` say

`(p+q)/p < log₂ α`  and  `(p+q)/q < log₂ (1/ρ)`,

and a ratio `p/(p+q)` strictly between `log2/log α` and `1 - log2/log(1/ρ)` exists exactly
when `A(α) < 1`.  This is M2's normal form `(L-1)(R-1) > 1` with `L = log₂ α`,
`R = log₂(1/ρ)`: the two are the same inequality, since
`1/L + 1/R < 1 ⟺ (L-1)(R-1) > 1` for `L, R > 1`.

`exists_avoided_interval_of_geom` is also the practical form: at a concrete `α` a small
pair `(p, q)` is a certificate checkable by `norm_num`, with no logarithms.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M1.html` Corollary 5 (the Route A ceiling), `note-1061-M2.html` §3.
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The integer-part bound -/

/-- A concrete admissible value of the engine's integer-part bound `K`. -/
noncomputable def intBound : ℕ := ⌈(1 + |P.β|) / (1 - |P.β|) + 1⌉₊

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem intBound_spec : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (P.intBound : ℝ) := Nat.le_ceil _

/-! ## The engine along a ray -/

/-- **The certificate value along the ray `(M, M') = (p·n, q·n)`.**  It is a constant times
`x^n + c·y^n` with `x = 2^{p+q} α^{-p}` and `y = 2^{p+q} ρ^q`: two geometric sequences. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cert_ray (p q K n : ℕ) :
    ((2 ^ (p * n) * 2 ^ (q * n) * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta (p * n) (q * n))
      = (2 * (2 * K + 1)) *
          ((2 ^ (p + q) * (P.α⁻¹) ^ p) ^ n
            + (1 + |P.β|) / (1 - |P.β|) * ((2 : ℝ) ^ (p + q) * |P.β| ^ q) ^ n) := by
  have hpow : ((2 : ℝ) ^ (p * n) * 2 ^ (q * n)) = ((2 : ℝ) ^ (p + q)) ^ n := by
    rw [pow_add, mul_pow, pow_mul, pow_mul]
  rw [delta]
  push_cast
  rw [mul_pow, mul_pow, pow_mul, pow_mul]
  field_simp
  ring

/-- **The engine as a geometric criterion.**  If both ratios `2^{p+q} α^{-p}` and
`2^{p+q} ρ^q` are below one, the certificate holds at some depth along the ray, so an open
subinterval of `(0,1)` is missed by every orbit at every time. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_avoided_interval_of_geom {p q : ℕ}
    (hA : (2 : ℝ) ^ (p + q) * (P.α⁻¹) ^ p < 1) (hB : (2 : ℝ) ^ (p + q) * |P.β| ^ q < 1) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  set K := P.intBound with hKdef
  set x : ℝ := 2 ^ (p + q) * (P.α⁻¹) ^ p with hxdef
  set y : ℝ := 2 ^ (p + q) * |P.β| ^ q with hydef
  set c : ℝ := (1 + |P.β|) / (1 - |P.β|) with hcdef
  have hx0 : 0 ≤ x :=
    mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr P.alpha_pos.le) p)
  have hy0 : 0 ≤ y := by positivity
  have hlim : Filter.Tendsto
      (fun n : ℕ => (2 * ((2 : ℝ) * K + 1)) * (x ^ n + c * y ^ n)) Filter.atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hA
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hy0 hB
    have := ((h1.add (h2.const_mul c)).const_mul (2 * ((2 : ℝ) * K + 1)))
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  refine P.exists_avoided_interval (p * n) (q * n) K P.intBound_spec ?_
  rw [P.cert_ray p q K n]
  exact hn

/-! ## The exponent `A(α)` -/

/-- **M1 Corollary 5, the effective half.**  If `A(α) < 1` then the covering certificate
holds at some depth, so an open subinterval of `(0,1)` is missed by every orbit at every
time.  The hypothesis `β ≠ 0` excludes the degenerate integer case, where `ρ = 0` and the
second summand of `A(α)` is not the intended `0` but Lean's junk value. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_avoided_interval_of_routeAExponent_lt_one
    (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  have hb0 : 0 < |P.β| := abs_pos.mpr hβ
  have hb1 : |P.β| < 1 := P.abs_beta_lt_one
  have hla : 0 < Real.log P.α := Real.log_pos P.one_lt
  have hlb : 0 < Real.log |P.β|⁻¹ := by
    rw [Real.log_inv]; exact neg_pos.mpr (Real.log_neg hb0 hb1)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set s : ℝ := Real.log 2 / Real.log P.α with hsdef
  set t : ℝ := Real.log 2 / Real.log |P.β|⁻¹ with htdef
  have hs0 : 0 < s := div_pos hl2 hla
  have ht0 : 0 < t := div_pos hl2 hlb
  have hst : s < 1 - t := by rw [routeAExponent] at h; linarith
  obtain ⟨w, hsw, hw1⟩ := exists_rat_btwn hst
  -- turn the rational `w` into a pair of positive naturals with `p / (p+q) = w`
  have hden : (0 : ℝ) < (w.den : ℝ) := by exact_mod_cast w.pos
  have hcast : (w : ℝ) = (w.num : ℝ) / (w.den : ℝ) := by rw [Rat.cast_def]
  have hw0 : (0 : ℝ) < (w : ℝ) := hs0.trans hsw
  have hwlt : (w : ℝ) < 1 := by linarith
  have hnum0 : (0 : ℤ) < w.num := by
    by_contra hcon
    push Not at hcon
    have : (w.num : ℝ) ≤ 0 := by exact_mod_cast hcon
    rw [hcast] at hw0
    nlinarith [div_nonpos_of_nonpos_of_nonneg this hden.le]
  have hnumden : w.num < (w.den : ℤ) := by
    have : (w.num : ℝ) < (w.den : ℝ) := by
      rw [hcast, div_lt_one hden] at hwlt; exact hwlt
    exact_mod_cast this
  set p : ℕ := w.num.toNat with hpdef
  have hpnum : (p : ℤ) = w.num := Int.toNat_of_nonneg hnum0.le
  have hp0 : 0 < p := by omega
  have hpd : p < w.den := by omega
  set q : ℕ := w.den - p with hqdef
  have hpq : p + q = w.den := by omega
  have hq0 : 0 < q := by omega
  have hpqR : ((p : ℝ) + (q : ℝ)) = (w.den : ℝ) := by exact_mod_cast hpq
  have hpR : (p : ℝ) = (w.num : ℝ) := by exact_mod_cast hpnum
  have hpqpos : (0 : ℝ) < (p : ℝ) + (q : ℝ) := by rw [hpqR]; exact hden
  have hwp : (w : ℝ) = (p : ℝ) / ((p : ℝ) + (q : ℝ)) := by rw [hcast, hpqR, hpR]
  -- the two geometric ratios
  have hAlog : ((p : ℝ) + q) * Real.log 2 < (p : ℝ) * Real.log P.α := by
    rw [hwp] at hsw
    rw [hsdef, div_lt_div_iff₀ hla hpqpos] at hsw
    linarith
  have hBlog : ((p : ℝ) + q) * Real.log 2 < (q : ℝ) * Real.log |P.β|⁻¹ := by
    have hp' : (p : ℝ) < (1 - t) * ((p : ℝ) + (q : ℝ)) := by
      rw [hwp] at hw1; exact (div_lt_iff₀ hpqpos).mp hw1
    have hkey : t * ((p : ℝ) + (q : ℝ)) < (q : ℝ) := by nlinarith [hp']
    have htl : t * Real.log |P.β|⁻¹ = Real.log 2 := by
      rw [htdef]; exact div_mul_cancel₀ _ hlb.ne'
    calc ((p : ℝ) + q) * Real.log 2
        = t * ((p : ℝ) + (q : ℝ)) * Real.log |P.β|⁻¹ := by rw [← htl]; ring
      _ < (q : ℝ) * Real.log |P.β|⁻¹ := mul_lt_mul_of_pos_right hkey hlb
  have hA : (2 : ℝ) ^ (p + q) * (P.α⁻¹) ^ p < 1 := by
    have hpow2 : (0 : ℝ) < 2 ^ (p + q) := by positivity
    have hpowα : (0 : ℝ) < P.α ^ p := pow_pos P.alpha_pos p
    have hlt : (2 : ℝ) ^ (p + q) < P.α ^ p := by
      rw [← Real.log_lt_log_iff hpow2 hpowα, Real.log_pow, Real.log_pow]
      push_cast
      linarith
    rw [inv_pow, ← div_eq_mul_inv, div_lt_one hpowα]
    exact hlt
  have hB : (2 : ℝ) ^ (p + q) * |P.β| ^ q < 1 := by
    have hpow2 : (0 : ℝ) < 2 ^ (p + q) := by positivity
    have hpowβ : (0 : ℝ) < |P.β| ^ q := pow_pos hb0 q
    have hinv : (0 : ℝ) < (|P.β|⁻¹) ^ q := pow_pos (inv_pos.mpr hb0) q
    have hlt : (2 : ℝ) ^ (p + q) < (|P.β|⁻¹) ^ q := by
      rw [← Real.log_lt_log_iff hpow2 hinv, Real.log_pow, Real.log_pow]
      push_cast
      linarith
    rw [inv_pow] at hlt
    calc (2 : ℝ) ^ (p + q) * |P.β| ^ q
        < (|P.β| ^ q)⁻¹ * |P.β| ^ q := by
          exact mul_lt_mul_of_pos_right hlt hpowβ
      _ = 1 := inv_mul_cancel₀ hpowβ.ne'
  exact P.exists_avoided_interval_of_geom hA hB

/-! ## Problem 10.61 under the criterion -/

/-- **M1 Corollary 5, dense form.**  If `A(α) < 1` then no `(ξ αⁿ)` with `ξ ∈ C(α)` is even
dense modulo one. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_denseModuloOne_of_routeAExponent_lt_one
    (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsDenseModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_of_routeAExponent_lt_one hβ h
  rintro ξ ⟨ε, rfl⟩
  exact not_denseModuloOne_of_avoided hr hsub (havoid ε)

/-- **Problem 10.61 holds at every quadratic setup with `A(α) < 1`.**  This is M1 Corollary 5,
the Route A ceiling in effective form, **at degree two**: the note states Theorem C(i) for a
Pisot number of any degree `d ≥ 2`, and this quadratic case is the only one proved here — every
consumer of the covering criterion, `BB61/RouteAFamily.lean` included, goes through a
`QuadSetup`.  Together with the ceiling `A(α) ≥ d·log2/log α` of the note — so that a firing of
degree `d` needs `α > 2^d` — it delimits Route A exactly. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_routeAExponent_lt_one
    (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_of_routeAExponent_lt_one hβ h
  rintro ξ ⟨ε, rfl⟩
  exact not_equidistributed_of_avoided hr hsub (havoid ε)

/-- **M1 Corollary 5, read as Proposition 4.**  `A(α) < 1` forces the confinement set
`X(α) = (C(α) - K) mod 1` to be a proper subset of the circle.  In the note this is the
step `A(α) < 1 ⇒ Leb(X(α)) = 0 ⇒ X(α) ≠ 𝕋`; here the measure-zero statement is bypassed,
the covering counts being the engine's own. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem confCircle_ne_univ_of_routeAExponent_lt_one
    (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) : P.confCircle ≠ Set.univ := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_of_routeAExponent_lt_one hβ h
  exact P.confCircle_ne_univ_of_avoided hr hsub havoid

end QuadSetup

end BB61
