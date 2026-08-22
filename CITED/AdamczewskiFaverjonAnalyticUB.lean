/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonTheta
import CITED.AdamczewskiFaverjonAuxiliary
import CITED.AdamczewskiFaverjonProof
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3.3 Step (UB), instantiated: from the auxiliary function to `e^{-c₂δ₁δ₂q^k}`

The second half of plan-formalize-AF17's **WP11**.  `CITED/AdamczewskiFaverjonUpperBound` proves
the *structural* form of Step (UB) — maximum modulus over a circle, a tail bound for a power
series with a zero of order `p`, and the conversion `(t^Q/s)^p ≤ e^{-γQp}`.
`CITED/AdamczewskiFaverjonTheta` builds the functions those estimates are to be applied to.  This
file applies them, and lands exactly on the hypothesis `AF.key_lemma_of_auxiliary` asks for:

  `∀ᶠ k, ‖φ(E(A_k(α), α^{q^k}))‖ ≤ exp(-(c₂δ₁δ₂q^k))`.

## The chain

1. **The value.**  `AF.formVal_evalMat_iterMatrix_eq_zero` is [AF22] (2.7): the linear form
   vanishes at every `(A_k(α), α^{q^k})`, which is (2.5) transported along (2.6).  Hence the
   auxiliary function `𝔈 = ∑_{j≥v₀} P_j F^{j-v₀}` takes the value `P_{v₀}(A_k(α),α^{q^k})` there —
   the algebraic number that Step (LB) bounds from below.
2. **The circle.**  `AF.norm_le_of_tail_on_sphere'` is the estimate of
   `CITED/AdamczewskiFaverjonUpperBound` with **`z`-dependent** coefficients: the coefficients of
   the auxiliary series in `z^{q^{k-k₀}}` are polynomials in the entries of `Θ_k(z)`, so they do
   vary along the circle, and only a *uniform majorant* is available.  That is all the argument
   needs.
3. **The majorant.**  `AF.norm_auxCoeff_le` bounds those coefficients by
   `(∑_ν ‖E_ν,n‖)·B^d` where `B` bounds the entries of `Θ_k` on the circle and `d` is the total
   degree — and `B ≤ C^k` by `AF.norm_evalMat_iterMatrix_le`, geometrically in `k`.
4. **The absorption.**  `AF.eventually_le_exp_of_pow_div`: a bound
   `M·D^k/m·(t^{q^{k-k₀}}/s)^p` is `≤ e^{-γq^k}` for all large `k`, because `q^k` outgrows `k`.
   The geometric factor `D^k` of step 3 disappears here, which is why no Taylor coefficient of
   `Θ_k` ever has to be estimated ([AF22] (2.30)).

## The interface, and why it is one

Three inputs are hypotheses rather than theorems, and each is a place where the corpus's *abstract*
objects have to be read as *functions*:

* **(the dictionary)** `hreal` — the formal auxiliary series `E ∈ K⟦z⟧[Y]` of
  `AF.exists_auxiliary` is the Taylor expansion in `z` of the analytic auxiliary function.  This is
  the formal-to-analytic dictionary at the top level, and what it needs beyond Stage 1's
  `AF.IsSumOnBall` (`CITED/AdamczewskiFaverjonProof`, imported here, and one `rfl` away by
  `AF.isSeriesSumOn_of_isSumOnBall`) is a **Cauchy product**, which that dictionary explicitly
  avoids.  **Proved in `CITED/AdamczewskiFaverjonDictionary`** (WP12(a)):
  `AF.hasSum_auxCoeff_bigSeries`, with `hsum`, `hmaj` and — granted `hEp` — `htail` alongside it,
  so that `AF.eventually_norm_evalAt_le_exp_of_vanishing` is this file's estimate with all four
  of those hypotheses discharged.
* **(Lemma 2.7, transported)** `hEp` — the truncated auxiliary function vanishes along the analytic
  branch, `E_p(Θ_k(z), z^{q^{k-k₀}}) = 0`.  In [AF22] this is Lemma 2.12 combined with Lemma 2.7,
  an identity in the ambient field of algebraic functions; the corpus's ambient field is abstract
  (`CITED/AdamczewskiFaverjonPrimitive`), so transporting it needs the realization of that field
  as germs of analytic functions at `ξ`.  **Proved in `CITED/AdamczewskiFaverjonGerm`** (WP12(b)):
  `AF.mvEvalC_theta_eq_zero_of_branch`, from `AF.IsBranchRealization` — the realization is the one
  thing that stays a hypothesis, and `AF.exists_isBranchRealization_ratFunc` shows it is not a
  vacuous one.
* **(Lemma 2.8, at one good `k₀`)** the analyticity of the relation matrix `Φ` near `ξ` and
  `a·Φ(ξ) = A_{k₀}(α)`.  [AF22] get these «for `k ≫ 1`» from «an algebraic function has finitely
  many singularities and zeros»; Mathlib has no vanishing criterion for the resultant, so this is
  carried as a hypothesis on one `k₀` — exactly how [AF22] use it.  Plan risk **R14**.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.3.3, Step (UB) ((2.13)–(2.19)) and Step (NV).
* [AF17f] `plans/plan-formalize-AF17.html`: WP11, risk R14, milestone M4.
-/

open Filter Metric Topology MvPolynomial

open scoped Polynomial

namespace AF

/-! ## Two elementary estimates -/

/-- **Absolute convergence strictly inside the disc of convergence.**  If `∑ cₙ s'ⁿ` converges and
`0 ≤ s < s'`, then `∑ ‖cₙ‖sⁿ` converges. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
theorem summable_norm_mul_pow_of_summable {c : ℕ → ℂ} {s s' : ℝ} (hs0 : 0 ≤ s) (hss' : s < s')
    (h : Summable fun n => c n * (s' : ℂ) ^ n) : Summable fun n => ‖c n‖ * s ^ n := by
  have hs'0 : 0 < s' := lt_of_le_of_lt hs0 hss'
  have hratio : s / s' < 1 := (div_lt_one hs'0).2 hss'
  have hr0 : 0 ≤ s / s' := div_nonneg hs0 hs'0.le
  have htend : Tendsto (fun n => ‖c n * (s' : ℂ) ^ n‖) atTop (nhds 0) := by
    simpa using h.tendsto_atTop_zero.norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually_le_const (by norm_num : (0:ℝ) < 1))
  refine (summable_nat_add_iff N).1 ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hratio)
  have hbound : ‖c (n + N)‖ * s' ^ (n + N) ≤ 1 := by
    have h1 := hN (n + N) (Nat.le_add_left N n)
    simpa [norm_mul, norm_pow, abs_of_pos hs'0] using h1
  have hs'ne : s' ≠ 0 := ne_of_gt hs'0
  have hsplit : ‖c (n + N)‖ * s ^ (n + N)
      = (‖c (n + N)‖ * s' ^ (n + N)) * (s / s') ^ (n + N) := by
    rw [div_pow]
    field_simp
  rw [hsplit]
  calc (‖c (n + N)‖ * s' ^ (n + N)) * (s / s') ^ (n + N)
      ≤ 1 * (s / s') ^ (n + N) := by
        exact mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (s / s') ^ (n + N) := one_mul _
    _ ≤ (s / s') ^ n := pow_le_pow_of_le_one hr0 hratio.le (Nat.le_add_right n N)

/-- `a + bk ≤ γqᵏ` for all large `k`: exponentials outgrow linear functions. -/
@[category API, AMS 26, ref "AF22", group "af_mahler_alternative"]
theorem eventually_add_mul_le_pow {q : ℕ} (hq : 2 ≤ q) {a b γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ k : ℕ in atTop, a + b * k ≤ γ * (q : ℝ) ^ k := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.trans_lt' one_lt_two
  set r : ℝ := 1 / q with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hq0]; exact hq1
  have h1 : Tendsto (fun k : ℕ => a * r ^ k) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul a
  have h2 : Tendsto (fun k : ℕ => b * ((k : ℝ) * r ^ k)) atTop (nhds 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).const_mul b
  have h3 : Tendsto (fun k : ℕ => (a + b * k) * r ^ k) atTop (nhds 0) := by
    have := h1.add h2
    simpa [add_mul, mul_assoc] using this
  filter_upwards [h3.eventually_le_const hγ] with k hk
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hrk : r ^ k = ((q : ℝ) ^ k)⁻¹ := by
    rw [hr, div_pow, one_pow, inv_eq_one_div, one_div]
  rw [hrk, ← div_eq_mul_inv, div_le_iff₀ hqk] at hk
  linarith

/-- **The absorption of the geometric factor.**  A bound `M·Dᵏ/m·(t^{q^{k-k₀}}/s)^p` is at most
`e^{-γqᵏ}` for all large `k`, as soon as `2γq^{k₀} ≤ p·log(1/t)`.

This is where `Θ_k`'s geometric growth `Dᵏ` is harmless: `qᵏ` outgrows `k`.  [AF22] never state
this because their route bounds Taylor coefficients by `e^{γq^k}`, where it would *not* have
been. -/
@[category research solved, AMS 26 30, ref "AF22", group "af_mahler_alternative"]
theorem eventually_le_exp_of_pow_div {q k₀ p : ℕ} (hq : 2 ≤ q) {t s M m D γ : ℝ}
    (ht0 : 0 < t) (hs0 : 0 < s) (hM0 : 0 < M) (hm0 : 0 < m) (hD1 : 1 ≤ D)
    (hγ0 : 0 < γ) (hγ : 2 * γ * (q : ℝ) ^ k₀ ≤ p * Real.log (1 / t)) {g : ℕ → ℝ}
    (hg : ∀ᶠ k in atTop, g k ≤ M * D ^ k / m * (t ^ q ^ (k - k₀) / s) ^ p) :
    ∀ᶠ k in atTop, g k ≤ Real.exp (-(γ * (q : ℝ) ^ k)) := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hlogt : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have habs := eventually_add_mul_le_pow (q := q) hq (a := Real.log M - Real.log m - p * Real.log s)
    (b := Real.log D) hγ0
  filter_upwards [hg, habs, eventually_ge_atTop k₀] with k hk habsk hk₀
  refine hk.trans ?_
  have hpos : 0 < M * D ^ k / m * (t ^ q ^ (k - k₀) / s) ^ p := by
    have : (0:ℝ) < D := lt_of_lt_of_le one_pos hD1
    positivity
  rw [← Real.exp_log hpos, Real.exp_le_exp]
  have hlog : Real.log (M * D ^ k / m * (t ^ q ^ (k - k₀) / s) ^ p)
      = Real.log M + k * Real.log D - Real.log m
        + p * (((q : ℝ) ^ (k - k₀)) * Real.log t - Real.log s) := by
    have hD0 : (0:ℝ) < D := lt_of_lt_of_le one_pos hD1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hlog]
  have hqsplit : ((q : ℝ) ^ (k - k₀)) * (q : ℝ) ^ k₀ = (q : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk₀]
  have hqk₀ : (0 : ℝ) < (q : ℝ) ^ k₀ := by positivity
  have hstep : (p : ℝ) * (((q : ℝ) ^ (k - k₀)) * Real.log t) ≤ -(2 * γ * (q : ℝ) ^ k) := by
    have h1 : (p : ℝ) * Real.log t ≤ -(2 * γ * (q : ℝ) ^ k₀) := by
      rw [hlogt] at hγ
      linarith
    have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (k - k₀) := by positivity
    calc (p : ℝ) * (((q : ℝ) ^ (k - k₀)) * Real.log t)
        = ((q : ℝ) ^ (k - k₀)) * ((p : ℝ) * Real.log t) := by ring
      _ ≤ ((q : ℝ) ^ (k - k₀)) * (-(2 * γ * (q : ℝ) ^ k₀)) := by
          exact mul_le_mul_of_nonneg_left h1 h2
      _ = -(2 * γ * ((q : ℝ) ^ (k - k₀) * (q : ℝ) ^ k₀)) := by ring
      _ = -(2 * γ * (q : ℝ) ^ k) := by rw [hqsplit]
  nlinarith [hstep, habsk]

/-! ## The maximum-modulus estimate with varying coefficients -/

/-- **[AF22] (2.14), with `z`-dependent coefficients.**  The estimate of
`AF.norm_le_of_tail_on_sphere`, except that the coefficients of the power series in `w(z)` are
allowed to vary with `z` — which they do, being polynomials in the entries of `Θ_k(z)` — and only
a uniform majorant `M` for `∑ₙ‖cₙ(z)‖sⁿ` on the circle is required. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_le_of_tail_on_sphere' {ξ : ℂ} {ρ s r : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hr0 : 0 ≤ r)
    (hrs : r ≤ s) {g f w : ℂ → ℂ} (hg : DiffContOnCl ℂ g (ball ξ ρ)) {m M : ℝ} (hm : 0 < m)
    (hf : ∀ z ∈ sphere ξ ρ, m ≤ ‖f z‖) {c : ℕ → ℂ → ℂ} {p : ℕ}
    (hsum : ∀ z ∈ sphere ξ ρ, Summable fun n => ‖c n z‖ * s ^ n)
    (hM : ∀ z ∈ sphere ξ ρ, ∑' n : ℕ, ‖c n z‖ * s ^ n ≤ M)
    (hw : ∀ z ∈ sphere ξ ρ, ‖w z‖ ≤ r)
    (hmul : ∀ z ∈ sphere ξ ρ, g z * f z = ∑' n : ℕ, c (n + p) z * (w z) ^ (n + p)) :
    ‖g ξ‖ ≤ M / m * (r / s) ^ p := by
  have hbd : ∀ z ∈ sphere ξ ρ, ‖(fun z => ∑' n : ℕ, c (n + p) z * (w z) ^ (n + p)) z‖ ≤
      M * (r / s) ^ p := by
    intro z hz
    refine le_trans (norm_tsum_tail_le hs (hsum z hz) p (le_trans (hw z hz) hrs)) ?_
    have h1 : (∑' n : ℕ, ‖c n z‖ * s ^ n) * (‖w z‖ / s) ^ p ≤
        (∑' n : ℕ, ‖c n z‖ * s ^ n) * (r / s) ^ p := by
      refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun n => by positivity)
      refine pow_le_pow_left₀ (by positivity) ?_ p
      gcongr
      exact hw z hz
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (hM z hz) (by positivity)
  have := norm_le_div_of_mul_eq_on_sphere hρ hg hm hf hmul hbd
  rwa [mul_div_right_comm] at this

/-! ## The auxiliary series, read as a function -/

section Realization

variable {K : Type*} [Field K] {σ : Type*}

/-- The value `Y^ν` of a monomial. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def monoVal (Y : σ → ℂ) (ν : σ →₀ ℕ) : ℂ := ν.prod fun s e => Y s ^ e

/-- Evaluation of a polynomial in `Y` with polynomial coefficients, at a complex point. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def mvEvalC (u : ℂ) (Y : σ → ℂ) : MvPolynomial σ ℂ[X] →+* ℂ :=
  eval₂Hom (Polynomial.evalRingHom u) Y

@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem mvEvalC_eq (u : ℂ) (Y : σ → ℂ) (Q : MvPolynomial σ ℂ[X]) :
    mvEvalC u Y Q = ∑ ν ∈ Q.support, (Q.coeff ν).eval u * monoVal Y ν :=
  MvPolynomial.eval₂_eq _ _ _

/-- **The `n`-th Taylor coefficient of the auxiliary function**, as a polynomial in the point:
`eₙ(Y) = ∑_ν φ(coeffₙ E_ν)·Y^ν`.  These are the coefficients that vary along the circle in
`AF.norm_le_of_tail_on_sphere'`, `Y` being the entries of `Θ_k(z)`. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def auxCoeff (φ : K →+* ℂ) (E : MvPolynomial σ (PowerSeries K)) (n : ℕ)
    (Y : σ → ℂ) : ℂ :=
  ∑ ν ∈ E.support, φ (PowerSeries.coeff n (E.coeff ν)) * monoVal Y ν

/-- **The realization of a formal power series over `K` by an analytic function on a disc.**  The
dictionary of `CITED/AdamczewskiFaverjonProof` (`AF.IsSumOnBall`) with the coefficient map given
as an explicit ring homomorphism rather than by an `Algebra K ℂ` instance — which is how the
embedding `φ` of a number field into `ℂ` reaches Step (UB) and Step (LB) everywhere else in
`CITED/`.  The two agree on the nose: `AF.isSeriesSumOn_of_isSumOnBall`. -/
@[category API, AMS 30 40, ref "AF22", group "af_mahler_alternative"]
def IsSeriesSumOn (r : ℝ) (φ : K →+* ℂ) (g : PowerSeries K) (H : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, ‖u‖ < r → HasSum (fun n => φ (PowerSeries.coeff n g) * u ^ n) (H u)

/-- Stage 1's dictionary is this one, along the structure map.  Both files may now be imported
together: what `CITED/AdamczewskiFaverjonProof` used to declare as `AF.substPow` — the
substitution `z ↦ z^q` on *power series* — is `AF.substPowSeries`, and the `§2.2` chain's
`AF.substPow`, the same substitution on *polynomials*, keeps the name. -/
@[category API, AMS 30 40, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem isSeriesSumOn_of_isSumOnBall [Algebra K ℂ] {r : ℝ} {g : PowerSeries K} {H : ℂ → ℂ}
    (h : IsSumOnBall r g H) : IsSeriesSumOn r (algebraMap K ℂ) g H := h

/-- The realization of a polynomial in `Y` with power-series coefficients. -/
@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def mvSum (E : MvPolynomial σ (PowerSeries K)) (Hc : (σ →₀ ℕ) → ℂ → ℂ)
    (Y : σ → ℂ) (u : ℂ) : ℂ :=
  ∑ ν ∈ E.support, Hc ν u * monoVal Y ν

/-- **Regrouping by powers of `z`.**  If each coefficient series of `E` is summed on the disc by
`Hc ν`, then the realization of `E` is the sum of the series whose coefficients are the polynomial
functions `AF.auxCoeff`.  This is the only rearrangement the argument needs, and it is finite: the
`Y`-support of `E` is a finite set. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem hasSum_auxCoeff {r : ℝ} {φ : K →+* ℂ} {E : MvPolynomial σ (PowerSeries K)}
    {Hc : (σ →₀ ℕ) → ℂ → ℂ} (hE : ∀ ν ∈ E.support, IsSeriesSumOn r φ (E.coeff ν) (Hc ν))
    (Y : σ → ℂ) {u : ℂ} (hu : ‖u‖ < r) :
    HasSum (fun n => auxCoeff φ E n Y * u ^ n) (mvSum E Hc Y u) := by
  have h := hasSum_sum (f := fun ν n => φ (PowerSeries.coeff n (E.coeff ν)) * u ^ n * monoVal Y ν)
    (a := fun ν => Hc ν u * monoVal Y ν) (s := E.support)
    fun ν hν => (hE ν hν u hu).mul_right _
  have key : ∀ n : ℕ,
      ∑ ν ∈ E.support, φ (PowerSeries.coeff n (E.coeff ν)) * u ^ n * monoVal Y ν
        = auxCoeff φ E n Y * u ^ n := by
    intro n
    rw [auxCoeff, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ν _ => by ring
  simpa only [key, mvSum] using h

/-- The value of a truncated power series, transported to `ℂ`. -/
@[category API, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem eval_map_trunc (φ : K →+* ℂ) (p : ℕ) (g : PowerSeries K) (u : ℂ) :
    ((PowerSeries.trunc p g).map φ).eval u
      = ∑ n ∈ Finset.range p, φ (PowerSeries.coeff n g) * u ^ n := by
  cases p with
  | zero =>
      have h0 : PowerSeries.trunc 0 g = 0 := by
        ext m
        simp
      simp [h0]
  | succ m =>
      have hdeg : ((PowerSeries.trunc (m + 1) g).map φ).natDegree < m + 1 :=
        lt_of_le_of_lt Polynomial.natDegree_map_le (PowerSeries.natDegree_trunc_lt g m)
      rw [Polynomial.eval_eq_sum_range' hdeg]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Polynomial.coeff_map, PowerSeries.coeff_trunc, ite_eq_left (Finset.mem_range.1 hn)]

/-- **The truncation, read as a function**: `E_p(Y,u) = ∑_{n<p} eₙ(Y)uⁿ`. -/
@[category research solved, AMS 13, ref "AF22", group "af_mahler_alternative"]
theorem mvEvalC_truncMv [Fintype σ] [DecidableEq σ] (φ : K →+* ℂ)
    (E : MvPolynomial σ (PowerSeries K)) (p : ℕ) (Y : σ → ℂ) (u : ℂ) :
    mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (truncMv K σ p E))
      = ∑ n ∈ Finset.range p, auxCoeff φ E n Y * u ^ n := by
  classical
  have hcoeff : ∀ ν : σ →₀ ℕ,
      ((MvPolynomial.map (Polynomial.mapRingHom φ) (truncMv K σ p E)).coeff ν).eval u
        = ∑ n ∈ Finset.range p, φ (PowerSeries.coeff n (E.coeff ν)) * u ^ n := by
    intro ν
    rw [MvPolynomial.coeff_map, coeff_truncMv]
    exact eval_map_trunc φ p (E.coeff ν) u
  have hsub : (MvPolynomial.map (Polynomial.mapRingHom φ) (truncMv K σ p E)).support ⊆
      E.support :=
    subset_trans (MvPolynomial.support_map_subset _ _) (support_truncMv_subset p E)
  rw [mvEvalC_eq, Finset.sum_subset hsub fun ν _ hν => by
    rw [MvPolynomial.notMem_support_iff.1 hν, Polynomial.eval_zero, zero_mul]]
  calc ∑ ν ∈ E.support,
        ((MvPolynomial.map (Polynomial.mapRingHom φ) (truncMv K σ p E)).coeff ν).eval u *
          monoVal Y ν
      = ∑ ν ∈ E.support, ∑ n ∈ Finset.range p,
          φ (PowerSeries.coeff n (E.coeff ν)) * u ^ n * monoVal Y ν := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [hcoeff ν, Finset.sum_mul]
    _ = ∑ n ∈ Finset.range p, ∑ ν ∈ E.support,
          φ (PowerSeries.coeff n (E.coeff ν)) * u ^ n * monoVal Y ν := Finset.sum_comm
    _ = ∑ n ∈ Finset.range p, auxCoeff φ E n Y * u ^ n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [auxCoeff, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring

end Realization

/-! ## The auxiliary function along the analytic branch -/

section AuxFun

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (φ : K →+* ℂ) (P : ℕ → MvPolynomial (ι × ι) K[X]) (τ : ι → ℂ) (fs : ι → ℂ → ℂ)

/-- **`E(Y,u) = ∑_{j<N} P_j(Y,u)F(Y,u)^j`** — the series of [AF22] Lemma 2.12, read as a
function. -/
@[category API, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def bigAux (N : ℕ) (Y : Matrix ι ι ℂ) (u : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    mvEvalC u (fun s => Y s.1 s.2) (MvPolynomial.map (Polynomial.mapRingHom φ) (P j)) *
      formVal τ fs Y u ^ j

/-- **`𝓔(Y,u) = ∑_{j<N} P_{j+v₀}(Y,u)F(Y,u)^j`** — [AF22]'s auxiliary function proper, the one
whose value at `(A_k(α),α^{q^k})` Steps (UB) and (LB) estimate. -/
@[category API, AMS 11 13 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def auxFun (v₀ N : ℕ) (Y : Matrix ι ι ℂ) (u : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    mvEvalC u (fun s => Y s.1 s.2) (MvPolynomial.map (Polynomial.mapRingHom φ) (P (j + v₀))) *
      formVal τ fs Y u ^ j

omit [DecidableEq ι] in
/-- **[AF22] (2.13)**: `𝓔·F^{v₀} = E`, `v₀` being the least index with `P_{v₀} ≠ 0`.  The
hypothesis `v₀ ≤ N` is not needed: above `N` the range is empty on both sides. -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem bigAux_eq_auxFun_mul {v₀ N : ℕ} (hP : ∀ j, j < v₀ → P j = 0)
    (Y : Matrix ι ι ℂ) (u : ℂ) :
    bigAux φ P τ fs N Y u = auxFun φ P τ fs v₀ (N - v₀) Y u * formVal τ fs Y u ^ v₀ := by
  have hzero : ∀ j ∈ Finset.range N, j ∉ Finset.Ico v₀ N →
      mvEvalC u (fun s => Y s.1 s.2) (MvPolynomial.map (Polynomial.mapRingHom φ) (P j)) *
        formVal τ fs Y u ^ j = 0 := by
    intro j hj hj'
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ico] at hj'
    rw [hP j (by omega), map_zero, map_zero, zero_mul]
  have hsub : Finset.Ico v₀ N ⊆ Finset.range N := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
  rw [bigAux, ← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range, auxFun,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm v₀ i, pow_add, ← mul_assoc]

omit [DecidableEq ι] in
/-- **The value of the auxiliary function where the linear form vanishes.**  [AF22]'s «by
construction of our auxiliary function, `𝓔(A_k(α),α^{q^k}) = P_{v₀}(A_k(α),α^{q^k})`». -/
@[category research solved, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem auxFun_of_formVal_eq_zero {v₀ N : ℕ} (hN : 0 < N) {Y : Matrix ι ι ℂ} {u : ℂ}
    (h0 : formVal τ fs Y u = 0) :
    auxFun φ P τ fs v₀ N Y u =
      mvEvalC u (fun s => Y s.1 s.2) (MvPolynomial.map (Polynomial.mapRingHom φ) (P v₀)) := by
  rw [auxFun, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [h0, zero_pow hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hN) h

/-- **[AF22] (2.7)**: the linear form vanishes at every `(A_k(α), α^{q^k})`.  This is (2.5)
transported along (2.6), and it is what makes the auxiliary function collapse to `P_{v₀}` at the
points where Step (LB) works. -/
@[category research solved, AMS 11 39, ref "AF22", group "af_mahler_alternative"]
theorem formVal_evalMat_iterMatrix_eq_zero {q : ℕ} {A : Matrix ι ι ℂ[X]} {S : Set ℂ}
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hf : IsMahlerSolution q A fs S) {α : ℂ} (hα : α ∈ S)
    (hL : formVal τ fs 1 α = 0) (k : ℕ) :
    formVal τ fs (evalMat α (iterMatrix q A k)) (α ^ q ^ k) = 0 := by
  have h := formVal_mul_evalMat_iterMatrix hS hf τ 1 k hα
  rw [one_mul] at h
  rw [h, hL]

end AuxFun

/-! ## Analyticity of the composite -/

section Analytic

variable {σ : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

@[category API, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem analyticAt_mvEvalC {W : ℂ → ℂ} {Y : ℂ → σ → ℂ} {z₀ : ℂ} (hW : AnalyticAt ℂ W z₀)
    (hY : ∀ s, AnalyticAt ℂ (fun z => Y z s) z₀) (Q : MvPolynomial σ ℂ[X]) :
    AnalyticAt ℂ (fun z => mvEvalC (W z) (Y z) Q) z₀ := by
  simp only [mvEvalC_eq, monoVal, Finsupp.prod]
  refine Finset.analyticAt_fun_sum _ fun ν _ => AnalyticAt.mul ?_ ?_
  · simpa using hW.aeval_polynomial (Q.coeff ν)
  · exact Finset.analyticAt_fun_prod _ fun s _ => (hY s).pow _

omit [DecidableEq ι] in
@[category API, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem analyticAt_formVal {W : ℂ → ℂ} {Y : ℂ → Matrix ι ι ℂ} {z₀ : ℂ} (τ : ι → ℂ)
    (fs : ι → ℂ → ℂ) (hW : AnalyticAt ℂ W z₀) (hY : ∀ i j, AnalyticAt ℂ (fun z => Y z i j) z₀)
    (hfs : ∀ i, AnalyticAt ℂ (fs i) (W z₀)) :
    AnalyticAt ℂ (fun z => formVal τ fs (Y z) (W z)) z₀ := by
  simp only [formVal]
  refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact (analyticAt_const.mul (hY i j)).mul ((hfs j).comp hW)

variable {K : Type*} [Field K]

omit [DecidableEq ι] in
/-- The auxiliary function, composed with the analytic branch, is analytic. -/
@[category research solved, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem analyticAt_auxFun {φ : K →+* ℂ} {P : ℕ → MvPolynomial (ι × ι) K[X]} {τ : ι → ℂ}
    {fs : ι → ℂ → ℂ} {v₀ N : ℕ} {W : ℂ → ℂ} {Y : ℂ → Matrix ι ι ℂ} {z₀ : ℂ}
    (hW : AnalyticAt ℂ W z₀) (hY : ∀ i j, AnalyticAt ℂ (fun z => Y z i j) z₀)
    (hfs : ∀ i, AnalyticAt ℂ (fs i) (W z₀)) :
    AnalyticAt ℂ (fun z => auxFun φ P τ fs v₀ N (Y z) (W z)) z₀ := by
  simp only [auxFun]
  refine Finset.analyticAt_fun_sum _ fun j _ => AnalyticAt.mul ?_ ?_
  · exact analyticAt_mvEvalC (σ := ι × ι) (Y := fun z (s : ι × ι) => Y z s.1 s.2) hW
      (fun s => hY s.1 s.2) _
  · exact (analyticAt_formVal τ fs hW hY hfs).pow _

end Analytic

/-! ## The majorant on the circle -/

section Majorant

variable {K : Type*} [Field K] {σ : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The tail of the auxiliary series.**  If the auxiliary series is summed on the disc by `G`
and its truncation vanishes at the point, then `G` *is* the tail from `p` on.  This is [AF22]
(2.20) — the one place where Lemma 2.12 enters Step (UB). -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tail_of_realization {φ : K →+* ℂ} {E : MvPolynomial σ (PowerSeries K)} {G : ℂ}
    {Y : σ → ℂ} {u : ℂ} {p : ℕ} (hre : HasSum (fun n => auxCoeff φ E n Y * u ^ n) G)
    (hEp : ∑ n ∈ Finset.range p, auxCoeff φ E n Y * u ^ n = 0) :
    G = ∑' n : ℕ, auxCoeff φ E (n + p) Y * u ^ (n + p) := by
  have h := hre.summable.sum_add_tsum_nat_add p
  rw [hre.tsum_eq, hEp, zero_add] at h
  exact h.symm

/-- The same, with the truncation written as [AF22] and `AF.exists_auxiliary` write it. -/
@[category research solved, AMS 13 30 40, ref "AF22", group "af_mahler_alternative"]
theorem tail_of_realization_truncMv [Fintype σ] [DecidableEq σ] {φ : K →+* ℂ}
    {E : MvPolynomial σ (PowerSeries K)} {G : ℂ} {Y : σ → ℂ} {u : ℂ} {p : ℕ}
    (hre : HasSum (fun n => auxCoeff φ E n Y * u ^ n) G)
    (hEp : mvEvalC u Y (MvPolynomial.map (Polynomial.mapRingHom φ) (truncMv K σ p E)) = 0) :
    G = ∑' n : ℕ, auxCoeff φ E (n + p) Y * u ^ (n + p) :=
  tail_of_realization hre (by rwa [mvEvalC_truncMv] at hEp)

/-- **The majorant.**  The `n`-th coefficient of the auxiliary function is bounded, on a set where
the point has entries of modulus at most `B ≥ 1`, by `(∑_ν ‖E_{ν,n}‖)·B^{deg E}` — a bound whose
dependence on the point is only through `B`, which is what makes it uniform along the circle. -/
@[category research solved, AMS 13 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_auxCoeff_le {φ : K →+* ℂ} {E : MvPolynomial σ (PowerSeries K)} {B : ℝ} (hB : 1 ≤ B)
    {Y : σ → ℂ} (hY : ∀ s, ‖Y s‖ ≤ B) (n : ℕ) :
    ‖auxCoeff φ E n Y‖ ≤
      (∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * B ^ E.totalDegree := by
  have hB0 : (0:ℝ) ≤ B := le_trans zero_le_one hB
  have hmono : ∀ ν ∈ E.support, ‖monoVal Y ν‖ ≤ B ^ E.totalDegree := by
    intro ν hν
    have h1 : ‖monoVal Y ν‖ ≤ B ^ (ν.sum fun _ e => e) := by
      rw [monoVal, Finsupp.prod, norm_prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun s _ => by positivity) fun s _ => ?_
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hY s) _
    refine h1.trans (pow_le_pow_right₀ hB ?_)
    exact MvPolynomial.le_totalDegree hν
  calc ‖auxCoeff φ E n Y‖
      ≤ ∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν)) * monoVal Y ν‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖ * B ^ E.totalDegree := by
        refine Finset.sum_le_sum fun ν hν => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono ν hν) (norm_nonneg _)
    _ = (∑ ν ∈ E.support, ‖φ (PowerSeries.coeff n (E.coeff ν))‖) * B ^ E.totalDegree :=
        (Finset.sum_mul _ _ _).symm

/-- **The entries of `Θ_k` on a disc of radius `≤ 1` grow geometrically.**  The quantitative form
of [AF22] Remark 2.10, and the `D^k` that `AF.eventually_le_exp_of_pow_div` absorbs. -/
@[category research solved, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem norm_theta_le {q k₀ k : ℕ} (hq : 1 ≤ q) {A : Matrix ι ι ℂ[X]} {a : Matrix ι ι ℂ}
    {Φ : ℂ → Matrix ι ι ℂ} {t C B₀ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC1 : 1 ≤ C) (hB₀ : 0 ≤ B₀)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(A i j).eval z‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ t)
    (haΦ : ∀ i j, ‖(a * Φ z) i j‖ ≤ B₀) (i j : ι) :
    ‖theta q k₀ A a Φ k z i j‖ ≤
      (Fintype.card ι : ℝ) * B₀ * ((Fintype.card ι : ℝ) * C) ^ (k - k₀) := by
  have hgrow := norm_evalMat_iterMatrix_le hq ht0 ht1 hC1 hA (k - k₀) z hz
  rw [theta, Matrix.mul_apply]
  calc ‖∑ l, (a * Φ z) i l * evalMat z (iterMatrix q A (k - k₀)) l j‖
      ≤ ∑ l : ι, ‖(a * Φ z) i l * evalMat z (iterMatrix q A (k - k₀)) l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : ι, B₀ * ((Fintype.card ι : ℝ) * C) ^ (k - k₀) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_mul (haΦ i l) (hgrow l j) (norm_nonneg _) hB₀
    _ = (Fintype.card ι : ℝ) * B₀ * ((Fintype.card ι : ℝ) * C) ^ (k - k₀) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]

end Majorant

/-! ## Step (UB), assembled -/

section Assembly

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The value of the analytic auxiliary function at the centre of the disc.**  [AF22] (2.7),
(2.9) and «by construction of our auxiliary function» in one: at `z = ξ` the auxiliary function
takes the value `P_{v₀}(A_k(α), α^{q^k})` — the image under `φ` of an algebraic number of `K`,
which is what Step (LB) bounds from below. -/
@[category research solved, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
theorem auxFun_theta_center {q k₀ k v₀ N : ℕ} (hk : k₀ ≤ k) (hN : 0 < N) {A : Matrix ι ι K[X]}
    {α : K} (φ : K →+* ℂ) {a : Matrix ι ι ℂ} {Φ : ℂ → Matrix ι ι ℂ} {ξ : ℂ}
    (hξ : ξ = φ α ^ q ^ k₀) (ha : a * Φ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    {fs : ι → ℂ → ℂ} {S : Set ℂ} (hS : ∀ z ∈ S, z ^ q ∈ S)
    (hf : IsMahlerSolution q (mapMat φ A) fs S) (τ : ι → ℂ) (hα : φ α ∈ S)
    (hL : formVal τ fs 1 (φ α) = 0) (P : ℕ → MvPolynomial (ι × ι) K[X]) :
    auxFun φ P τ fs v₀ N (theta q k₀ (mapMat φ A) a Φ k ξ) (ξ ^ q ^ (k - k₀))
      = φ (evalAt (fun k => α ^ q ^ k) (fun k s => (iterMatrix q A k s.1 s.2).eval α) k
          (P v₀)) := by
  have hpt : ξ ^ q ^ (k - k₀) = φ α ^ q ^ k := by
    rw [hξ, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]
  have hth : theta q k₀ (mapMat φ A) a Φ k ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k) :=
    theta_center hk hξ ha
  have h0 : formVal τ fs (theta q k₀ (mapMat φ A) a Φ k ξ) (ξ ^ q ^ (k - k₀)) = 0 := by
    rw [hth, hpt]
    exact formVal_evalMat_iterMatrix_eq_zero τ fs hS hf hα hL k
  rw [auxFun_of_formVal_eq_zero φ P τ fs hN h0]
  exact eval_theta_center hk φ hξ ha (P v₀)

/-- **[AF22] Step (UB), instantiated.**  The maximum-modulus estimate, the tail bound and the
absorption of the geometric factor, applied to the analytic auxiliary function along the branch:
the algebraic number `P_{v₀}(A_k(α),α^{q^k})` — which Step (LB) bounds below by `e^{-(C+c₃q^kδ₂)}`
— is bounded above by `e^{-γq^k}` for all large `k`.

This is exactly the hypothesis `AF.key_lemma_of_auxiliary` asks of Step (UB), with
`γ = c₂δ₁δ₂` once `p ≥ 2γq^{k₀}/log(1/t)`, which is [AF22]'s `p = ⌊m²δ₁δ₂/2⌋ + 2`.

The hypotheses are the three of the file's interface (`hgan`, `hgval` and `htail` come from
`AF.analyticAt_auxFun`, `AF.auxFun_theta_center` and the realization of the auxiliary series),
plus the geometry of the circle: `|z| ≤ t < 1` on it, and `|𝔉| ≥ m > 0` there, the latter from
`AF.exists_radius_norm_pos` applied to the `k`-independent function `F(Θ_{k₀}(z),z)^{v₀}`. -/
@[category research solved, AMS 11 30, ref "AF22", group "af_mahler_alternative"]
theorem eventually_norm_evalAt_le_exp {q k₀ p : ℕ} (hq : 2 ≤ q) {A : Matrix ι ι K[X]} {α : K}
    (φ : K →+* ℂ) {Pv : MvPolynomial (ι × ι) K[X]} {gk : ℕ → ℂ → ℂ} {Ff : ℂ → ℂ}
    {c : ℕ → ℕ → ℂ → ℂ} {ξ : ℂ} {ρ t s m M D γ : ℝ} (hρ : 0 < ρ) (hs0 : 0 < s) (ht0 : 0 < t)
    (hm : 0 < m) (hM0 : 0 < M) (hD1 : 1 ≤ D) (hγ0 : 0 < γ)
    (hγ : 2 * γ * (q : ℝ) ^ k₀ ≤ p * Real.log (1 / t))
    (hsph : ∀ z ∈ sphere ξ ρ, ‖z‖ ≤ t) (hFf : ∀ z ∈ sphere ξ ρ, m ≤ ‖Ff z‖)
    (hgan : ∀ k, k₀ ≤ k → DiffContOnCl ℂ (gk k) (ball ξ ρ))
    (hgval : ∀ k, k₀ ≤ k → gk k ξ = φ (evalAt (fun k => α ^ q ^ k)
      (fun k s => (iterMatrix q A k s.1 s.2).eval α) k Pv))
    (hsum : ∀ k, k₀ ≤ k → ∀ z ∈ sphere ξ ρ, Summable fun n => ‖c k n z‖ * s ^ n)
    (hmaj : ∀ k, k₀ ≤ k → ∀ z ∈ sphere ξ ρ, ∑' n : ℕ, ‖c k n z‖ * s ^ n ≤ M * D ^ k)
    (htail : ∀ k, k₀ ≤ k → ∀ z ∈ sphere ξ ρ,
      gk k z * Ff z = ∑' n : ℕ, c k (n + p) z * (z ^ q ^ (k - k₀)) ^ (n + p)) :
    ∀ᶠ k in atTop, ‖φ (evalAt (fun k => α ^ q ^ k)
      (fun k s => (iterMatrix q A k s.1 s.2).eval α) k Pv)‖ ≤ Real.exp (-(γ * (q : ℝ) ^ k)) := by
  have hpos : 0 < (p : ℝ) * Real.log (1 / t) := lt_of_lt_of_le (by positivity) hγ
  have hlogpos : 0 < Real.log (1 / t) := by
    by_contra h
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith [hpos, not_lt.1 h]
  have ht1 : t < 1 := by
    have h1 : 1 < 1 / t := (Real.log_pos_iff (by positivity)).1 hlogpos
    exact (one_lt_div ht0).1 h1
  have hev : ∀ᶠ k : ℕ in atTop, t ^ q ^ (k - k₀) ≤ s := by
    have hpow : Tendsto (fun k : ℕ => q ^ (k - k₀)) atTop atTop := by
      refine tendsto_atTop_mono (fun k => ?_) (tendsto_sub_atTop_nat k₀)
      exact le_of_lt (Nat.lt_pow_self (by omega))
    have hcomp := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1).comp hpow
    exact hcomp.eventually_le_const hs0
  refine eventually_le_exp_of_pow_div hq ht0 hs0 hM0 hm hD1 hγ0 hγ ?_
  filter_upwards [hev, eventually_ge_atTop k₀] with k hks hk
  rw [← hgval k hk]
  refine norm_le_of_tail_on_sphere' hρ hs0 (by positivity) hks (hgan k hk) hm hFf
    (hsum k hk) (hmaj k hk) ?_ (htail k hk)
  intro z hz
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) (hsph z hz) _

end Assembly

end AF
