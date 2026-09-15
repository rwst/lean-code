/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.LimitLaw
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Corollary 6: the multiplier version

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §5,
quadratic case.

> **Corollary 6.**  Let `α > 2` be a Pisot *unit*, `λ ∈ ℤ[α] \ {0}`, `p ∈ (0,1)`, and `ε`
> Bernoulli(`p`)-generic.  Then `(λ π(ε) αⁿ)` is not u.d. mod one, with limit law `F^λ_*μ_p`
> and an explicit non-zero Fourier coefficient at every `h ≠ 0`.

[BM97] p. 188 asserts this extension of [BM86] Th. XIV with « une légère modification de la
preuve montrerait ».  Here is the modification.

## The twist

At degree two the multiplier is `λ = l₁ + l₂ α` and its conjugate `λ' = l₁ + l₂ β`, and the
whole of Corollary 6 is one observation: since `λ A_n ∈ ℤ[α]` has trace `λ A_n + λ' S_n ∈ ℤ`,

`{λ ξ αⁿ} = {λ t_n - λ' S_n}`,

so the twisted coding `F^λ(ω) = λ t(ω⁺) - λ' S(ω⁻)` differs from `F` only in that the two
halves are scaled by *different* constants.  `lamR_aPart_add_lamC_sPart` is that trace, with
the integer named; `fMapL_iterate_padZ` is the orbit identity that follows.

Everything else is quoted rather than re-proved:

* **Theorem 1** is quoted through `Coding`, the abstraction `BB61/LimitLaw.lean` carries: a
  continuous map to the circle with a null padding modulus.  `codingL` verifies the four
  fields for `F^λ` — only the padding modulus changes, from `padErr L` to `|λ'| padErr L`.
* **Theorem 2** is quoted through `futProdC` and `pastProdC`, which
  `BB61/ProductFormula.lean` already defines at an *arbitrary* real frequency.  The twisted
  ladder is the untwisted one at the two frequencies `hλ` (future) and `hλ'` (past), so
  `weylCL l p h = futProdC p (hλ) · pastProdC p (hλ')` and the two-sided reindexing needs
  only the two-parameter `freq2`.

## The arithmetic, and what the unit hypothesis buys

Theorem 3's case analysis collapses at a unit.  `IsIntComb x` says `x = u + vα` with
`u, v ∈ ℤ`; `cos_pi_ne_zero_of_isIntComb` says such an `x` is never in `½ + ℤ`, because
`2u + 2vα = 2n+1` forces `α ∈ ℚ` if `v ≠ 0` and `2u = 2n+1` if `v = 0`.  Both twisted ladders
lie in `ℤ[α]`: the past one always (`β ∈ ℤ[α]`), the future one exactly because `α` is a unit
(`α⁻¹ = b(α - a) ∈ ℤ[α]` when `b² = 1`).  So:

* **`α > 2` is spent nowhere in Corollary 6.**  The note spends it once, in Theorem 3(iii),
  on the future factors of a *non-unit*; at a unit Theorem 3(v) subsumes (iii), and this file
  is the sharp form of that remark.  What replaces `α > 2` is `Irrational α`.
* **`λ ≠ 0` is not needed either**, at degree two: at `λ = 0` every ladder entry is `0`, every
  factor is `φ_p(0) = 1`, and the limit law is `δ₀ ≠ Leb` — the conclusion holds for the
  degenerate reason.  The hypothesis is kept out of the statements rather than assumed.
* **`p ∈ (0,1)` is not needed**: for `p ≠ 1/2` no factor can vanish at all
  (`phi_ne_zero_of_ne_half`, the note's Theorem 3(ii)), and `p ∈ {0,1}` is such a `p`.

## What comes out

* `fMapL_iterate_padZ` — the twisted orbit identity `F^λ(σⁿ ε̃) = {λ ξ αⁿ}`.
* `tendsto_emp_of_generic_mul` — **Theorem 1 for `F^λ`**: the orbit of `λξ` has limit law
  `F^λ_*ν̂` at any `ν`-generic word.
* `integral_fourier_map_fMapL` — **Theorem 2 for `F^λ`**: `G^λ_p(h)` is a Fourier coefficient
  of `F^λ_*μ_p`.
* `weylCL_ne_zero` — **Theorem 3 for `F^λ`**: no factor of either twisted ladder vanishes.
* `tendsto_weylSum_bern_mul` — **Corollary 6 with the constant**: at a Bernoulli(`p`)-generic
  word, `N⁻¹∑ e(hλξαⁿ) → G^λ_p(h) ≠ 0`.
* `not_equidistributed_of_bern_generic_mul` — **Corollary 6**; `ae_…` and
  `measure_…_eq_zero` are its a.e. and null-set forms, and `…_twoAddSqrt3` the instance at
  the unit `α = 2 + √3` (`b = -1`, i.e. `N(α) = +1`).
-/

namespace BB61

open MeasureTheory Filter Topology

namespace QuadSetup

variable (P : QuadSetup)

/-! ## `ℤ[α]` at degree two -/

/-- `x ∈ ℤ[α]`, spelled out in the `ℤ`-basis `{1, α}`: the only form of algebraic integrality
this file needs. -/
def IsIntComb (x : ℝ) : Prop := ∃ u v : ℤ, x = (u : ℝ) + (v : ℝ) * P.α

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_intCast (k : ℤ) : P.IsIntComb (k : ℝ) := ⟨k, 0, by push_cast; ring⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_one : P.IsIntComb 1 := ⟨1, 0, by push_cast; ring⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_alpha : P.IsIntComb P.α := ⟨0, 1, by push_cast; ring⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_add {x y : ℝ} (hx : P.IsIntComb x) (hy : P.IsIntComb y) :
    P.IsIntComb (x + y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  exact ⟨u + u', v + v', by push_cast; ring⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_neg {x : ℝ} (hx : P.IsIntComb x) : P.IsIntComb (-x) := by
  obtain ⟨u, v, rfl⟩ := hx
  exact ⟨-u, -v, by push_cast; ring⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_sub {x y : ℝ} (hx : P.IsIntComb x) (hy : P.IsIntComb y) :
    P.IsIntComb (x - y) := by
  rw [sub_eq_add_neg]
  exact P.isIntComb_add hx (P.isIntComb_neg hy)

/-- `ℤ[α]` is closed under multiplication — the one place the root identity `α² = aα + b`
is used. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_mul {x y : ℝ} (hx : P.IsIntComb x) (hy : P.IsIntComb y) :
    P.IsIntComb (x * y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  refine ⟨u * u' + P.b * (v * v'), u * v' + v * u' + P.a * (v * v'), ?_⟩
  have hroot := P.root
  push_cast
  linear_combination ((v : ℝ) * (v' : ℝ)) * hroot

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_pow {x : ℝ} (hx : P.IsIntComb x) (n : ℕ) : P.IsIntComb (x ^ n) := by
  induction n with
  | zero => simpa using P.isIntComb_one
  | succ n ih => rw [pow_succ]; exact P.isIntComb_mul ih hx

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_beta : P.IsIntComb P.β := ⟨P.a, -1, by rw [QuadSetup.β]; push_cast; ring⟩

/-- **Where the unit hypothesis is spent.**  If `b² = 1`, i.e. `N(α) = -b = ∓1`, then
`α⁻¹ = b(α - a) ∈ ℤ[α]`, and the *future* ladder joins the past one inside `ℤ[α]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_inv_alpha (hb : P.b * P.b = 1) : P.IsIntComb P.α⁻¹ := by
  refine ⟨-(P.b * P.a), P.b, ?_⟩
  refine inv_eq_of_mul_eq_one_right ?_
  have hroot := P.root
  have hbb : ((P.b : ℝ)) * (P.b : ℝ) = 1 := by exact_mod_cast hb
  push_cast
  linear_combination (P.b : ℝ) * hroot + hbb

/-! ## No element of `ℤ[α]` is a half-integer -/

/-- **Theorem 3(i), in its sharpest form.**  For irrational `α`, no element of `ℤ[α]` lies in
`½ + ℤ`: if `v ≠ 0` the equation `2u + 2vα = 2n+1` makes `α` rational, and if `v = 0` it makes
an even integer odd.  This one lemma replaces the whole of the note's Theorem 3 for a unit —
both the trace argument (i) and the interval argument (iii). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_pi_ne_zero_of_isIntComb (hirr : Irrational P.α) {x : ℝ} (hx : P.IsIntComb x) :
    Real.cos (Real.pi * x) ≠ 0 := by
  obtain ⟨u, v, rfl⟩ := hx
  rw [Ne, Real.cos_eq_zero_iff]
  rintro ⟨n, hn⟩
  have hpi := Real.pi_pos
  have hx2 : (u : ℝ) + (v : ℝ) * P.α = (n : ℝ) + 1 / 2 := by
    have h : Real.pi * ((u : ℝ) + (v : ℝ) * P.α) = Real.pi * ((n : ℝ) + 1 / 2) := by
      rw [hn]; ring
    exact mul_left_cancel₀ (ne_of_gt hpi) h
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv] at hx2
    have hcast : ((2 * u : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast at hx2 ⊢; linarith
    have hz : (2 * u : ℤ) = 2 * n + 1 := by exact_mod_cast hcast
    omega
  · have hirr' : Irrational (((2 * v : ℤ) : ℝ) * P.α) := hirr.intCast_mul (by omega)
    refine hirr'.ne_int (2 * n + 1 - 2 * u) ?_
    push_cast
    linarith

/-! ## No factor of the twisted Erdős product vanishes -/

/-- **Theorem 3(ii).**  Away from the fair coin no factor can vanish at all: `|φ_p| ≥ |1-2p|`,
here in the sharp form "`φ_p(x) = 0` forces `p = 1/2`". -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_ne_zero_of_ne_half {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p ≠ 1 / 2) (x : ℝ) :
    phi p x ≠ 0 := by
  intro hcon
  have hmul : ((p : ℝ) : ℂ) * cexp1 x = -(((1 - p : ℝ)) : ℂ) := by
    rw [phi] at hcon
    linear_combination hcon
  have hnorm := congrArg norm hmul
  rw [norm_mul, norm_cexp1, mul_one, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)] at hnorm
  exact hp (by linarith)

/-- **Theorem 3 for the twisted ladder.**  At any `p ∈ [0,1]` and any frequency in `ℤ[α]`, the
one-digit characteristic function is non-zero: off the fair coin by `phi_ne_zero_of_ne_half`,
at the fair coin by `cos_pi_ne_zero_of_isIntComb`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_ne_zero_of_isIntComb {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hirr : Irrational P.α)
    {x : ℝ} (hx : P.IsIntComb x) : phi p x ≠ 0 := by
  rcases eq_or_ne p (1 / 2) with hp | hp
  · subst hp
    rw [← norm_ne_zero_iff, norm_phi_half, ncos, abs_ne_zero]
    exact P.cos_pi_ne_zero_of_isIntComb hirr hx
  · exact phi_ne_zero_of_ne_half h0 h1 hp x

/-! ## The multiplier and its conjugate -/

/-- The multiplier `λ = l₁ + l₂ α ∈ ℤ[α]`. -/
noncomputable def lamR (l : ℤ × ℤ) : ℝ := (l.1 : ℝ) + (l.2 : ℝ) * P.α

/-- Its conjugate `λ' = σ₂(λ) = l₁ + l₂ β`. -/
noncomputable def lamC (l : ℤ × ℤ) : ℝ := (l.1 : ℝ) + (l.2 : ℝ) * P.β

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_lamR (l : ℤ × ℤ) : P.IsIntComb (P.lamR l) := ⟨l.1, l.2, rfl⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_lamC (l : ℤ × ℤ) : P.IsIntComb (P.lamC l) :=
  P.isIntComb_add (P.isIntComb_intCast l.1)
    (P.isIntComb_mul (P.isIntComb_intCast l.2) P.isIntComb_beta)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lamR_one : P.lamR (1, 0) = 1 := by simp [lamR]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lamC_one : P.lamC (1, 0) = 1 := by simp [lamC]

/-! ## The twisted coding `F^λ` -/

/-- The twisted coding before reduction mod one: `λ t(ω⁺) - λ' S(ω⁻)`.  The two halves of `F`
are scaled by *different* constants — that, and nothing else, is the twist. -/
noncomputable def fRawL (l : ℤ × ℤ) (ω : Shift) : ℝ :=
  P.lamR l * piVal P.α (futures ω) - P.lamC l * P.wVal (pasts ω)

/-- **The twisted factor map** `F^λ : {0,1}^ℤ → 𝕋`. -/
noncomputable def fMapL (l : ℤ × ℤ) (ω : Shift) : AddCircle (1 : ℝ) :=
  ((P.fRawL l ω : ℝ) : AddCircle (1 : ℝ))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fRawL_one (ω : Shift) : P.fRawL (1, 0) ω = P.fRaw ω := by
  rw [fRawL, fRaw, P.lamR_one, P.lamC_one, one_mul, one_mul]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_fRawL (l : ℤ × ℤ) : Continuous (P.fRawL l) :=
  (continuous_const.mul (continuous_piVal_futures P.one_lt)).sub
    (continuous_const.mul P.continuous_wVal_pasts)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_fMapL (l : ℤ × ℤ) : Continuous (P.fMapL l) :=
  QuotientAddGroup.continuous_mk.comp (P.continuous_fRawL l)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_fMapL (l : ℤ × ℤ) : Measurable (P.fMapL l) := (P.continuous_fMapL l).measurable

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_fMapL_le (l : ℤ × ℤ) (a b : Shift) :
    dist (P.fMapL l a) (P.fMapL l b) ≤ |P.fRawL l a - P.fRawL l b| := by
  rw [dist_eq_norm]
  have h : P.fMapL l a - P.fMapL l b
      = ((P.fRawL l a - P.fRawL l b : ℝ) : AddCircle (1 : ℝ)) := by
    simp [QuadSetup.fMapL]
  rw [h]
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))
      (m := P.fRawL l a - P.fRawL l b))

/-! ## The twisted padding modulus -/

/-- The padding modulus of `F^λ`: only the past half of the coding is disturbed by
zero-padding, and it carries the constant `λ'`. -/
noncomputable def padErrL (l : ℤ × ℤ) (L : ℕ) : ℝ := |P.lamC l| * P.padErr L

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem padErrL_nonneg (l : ℤ × ℤ) (L : ℕ) : 0 ≤ P.padErrL l L :=
  mul_nonneg (abs_nonneg _) (P.padErr_nonneg L)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_padErrL (l : ℤ × ℤ) : Tendsto (P.padErrL l) atTop (𝓝 0) := by
  have h := P.tendsto_padErr.const_mul |P.lamC l|
  rw [mul_zero] at h
  exact h

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fRawL_sub_padZ_le (l : ℤ × ℤ) (ω : Shift) (L : ℕ) :
    |P.fRawL l (shiftZ^[L + 1] (padZ (futures ω))) - P.fRawL l (shiftZ^[L + 1] ω)|
      ≤ P.padErrL l L := by
  have hfut := futures_iterate_padZ_futures ω (L + 1)
  have key : P.fRawL l (shiftZ^[L + 1] (padZ (futures ω))) - P.fRawL l (shiftZ^[L + 1] ω)
      = P.lamC l * (P.wVal (pasts (shiftZ^[L + 1] ω))
          - P.wVal (pasts (shiftZ^[L + 1] (padZ (futures ω))))) := by
    simp only [fRawL, hfut]; ring
  rw [key, abs_mul]
  show |P.lamC l| * |P.wVal (pasts (shiftZ^[L + 1] ω))
      - P.wVal (pasts (shiftZ^[L + 1] (padZ (futures ω))))| ≤ |P.lamC l| * P.padErr L
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_sub_comm]
  exact P.abs_wVal_sub_le_of_agree fun m hm => pasts_iterate_padZ_agree ω L hm

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dist_fMapL_padZ_futures (l : ℤ × ℤ) (ω : Shift) (L : ℕ) :
    dist (P.fMapL l (shiftZ^[L + 1] (padZ (futures ω)))) (P.fMapL l (shiftZ^[L + 1] ω))
      ≤ P.padErrL l L :=
  (P.dist_fMapL_le l _ _).trans (P.abs_fRawL_sub_padZ_le l ω L)

/-- **`F^λ` is a coding.**  All four fields are the twisted analogues of `QuadSetup.coding`'s;
this is what lets Theorem 1 be quoted rather than re-run. -/
noncomputable def codingL (l : ℤ × ℤ) : Coding where
  toFun := P.fMapL l
  continuous := P.continuous_fMapL l
  err := P.padErrL l
  err_nonneg := P.padErrL_nonneg l
  tendsto_err := P.tendsto_padErrL l
  dist_padZ_le := P.dist_fMapL_padZ_futures l

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codingL_toFun (l : ℤ × ℤ) : (P.codingL l).toFun = P.fMapL l := rfl

/-! ## The twisted trace, and the orbit identity -/

/-- The trace `Tr(λ A_n) = λ A_n + λ' S_n ∈ ℤ`, evaluated on the integer pair recursion:
`2l₁u_n + a(l₁v_n + l₂u_n) + l₂v_n(a² + 2b)`, from `α + β = a` and `α² + β² = a² + 2b`. -/
def traceMulZ (l : ℤ × ℤ) (ε : ℕ → Bool) (n : ℕ) : ℤ :=
  2 * l.1 * (P.uv ε n).1 + P.a * (l.1 * (P.uv ε n).2 + l.2 * (P.uv ε n).1)
    + l.2 * (P.uv ε n).2 * (P.a ^ 2 + 2 * P.b)

/-- **The twisted trace identity.**  `λ A_n + λ' S_n ∈ ℤ`: the whole of Corollary 6 in one
line, with no number field in sight. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lamR_aPart_add_lamC_sPart (l : ℤ × ℤ) (ε : ℕ → Bool) (n : ℕ) :
    P.lamR l * P.aPart ε n + P.lamC l * P.sPart ε n = ((P.traceMulZ l ε n : ℤ) : ℝ) := by
  have hroot := P.root
  have hbeta := P.beta_root
  have hsum := P.alpha_add_beta
  simp only [lamR, lamC, aPart, sPart, traceMulZ]
  push_cast
  linear_combination ((l.2 : ℝ) * (((P.uv ε n).2 : ℤ) : ℝ)) * hroot
    + ((l.2 : ℝ) * (((P.uv ε n).2 : ℤ) : ℝ)) * hbeta
    + ((l.1 : ℝ) * (((P.uv ε n).2 : ℤ) : ℝ) + (l.2 : ℝ) * (((P.uv ε n).1 : ℤ) : ℝ)
        + (P.a : ℝ) * (l.2 : ℝ) * (((P.uv ε n).2 : ℤ) : ℝ)) * hsum

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fRawL_iterate_padZ (l : ℤ × ℤ) (ε : ℕ → Bool) (n : ℕ) :
    P.fRawL l (shiftZ^[n] (padZ ε))
      = P.lamR l * tPart P.α ε n - P.lamC l * P.sPart ε n := by
  rw [fRawL, futures_iterate_padZ, pasts_iterate_padZ, P.wVal_padWord, tPart]

/-- **The twisted orbit identity.**  `F^λ(σⁿ ε̃) = {λ ξ αⁿ}`: the orbit of the *multiplied*
point is the `F^λ`-image of the same shift orbit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fMapL_iterate_padZ (l : ℤ × ℤ) (ε : ℕ → Bool) (n : ℕ) :
    P.fMapL l (shiftZ^[n] (padZ ε))
      = ((P.lamR l * (piVal P.α ε * P.α ^ n) : ℝ) : AddCircle (1 : ℝ)) := by
  rw [fMapL, P.fRawL_iterate_padZ]
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-(P.traceMulZ l ε n), ?_⟩
  have h1 := P.xi_mul_pow ε n
  have h2 := P.lamR_aPart_add_lamC_sPart l ε n
  simp only [zsmul_eq_mul, mul_one]
  push_cast
  linear_combination (P.lamR l) * h1 + h2

/-! ## Theorem 1 for `F^λ` -/

/-- **M5 Theorem 1 for the twisted coding.**  At a `ν`-generic word the orbit of `λ ξ` has
limit law `F^λ_*ν̂`.  Quoted from `Coding.tendsto_emp_of_generic`: nothing in that proof knew
which coding it was reading. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_emp_of_generic_mul (l : ℤ × ℤ) {ν : ProbabilityMeasure (ℕ → Bool)}
    {μ : ProbabilityMeasure Shift} (hne : IsNaturalExtension ν μ)
    {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) :
    Tendsto (fun N => emp
        (fun n => ((P.lamR l * (piVal P.α ε * P.α ^ n) : ℝ) : AddCircle (1 : ℝ))) N)
      atTop (𝓝 (pmap (P.measurable_fMapL l) μ)) :=
  (P.codingL l).tendsto_emp_of_generic hne hgen (P.fMapL_iterate_padZ l ε)

/-- **Theorem 1 for `F^λ`, the "in particular".** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem equidistributed_iff_map_eq_haarT_mul (l : ℤ × ℤ)
    {ν : ProbabilityMeasure (ℕ → Bool)} {μ : ProbabilityMeasure Shift}
    (hne : IsNaturalExtension ν μ) {ε : ℕ → Bool} (hgen : IsGenericFor ν ε) :
    IsEquidistributedModuloOne (fun n : ℕ => P.lamR l * (piVal P.α ε * P.α ^ n))
      ↔ pmap (P.measurable_fMapL l) μ = haarT :=
  (P.codingL l).equidistributed_iff_map_eq_haarT hne hgen (P.fMapL_iterate_padZ l ε)

/-! ## The two-parameter ladder, and Theorem 2 for `F^λ` -/

/-- The two-sided ladder at *two* frequencies: `hf` on the future, `hp` on the past.  The
untwisted `freq h` is `freq2 h h`; the twisted one is `freq2 (hλ) (hλ')`. -/
noncomputable def freq2 (hf hp : ℝ) : ℤ → ℝ := fun k =>
  if 1 ≤ k then hf * (P.α - 1) / P.α ^ k.toNat else -(hp * P.cCoef (-k).toNat)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem freq2_eq_freq (h : ℝ) : P.freq2 h h = P.freq h := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem freq2_inl (hf hp : ℝ) (j : ℕ) :
    P.freq2 hf hp (zsplit (Sum.inl j)) = hf * (P.α - 1) / P.α ^ (j + 1) := by
  rw [zsplit_inl]
  unfold freq2
  split_ifs with hh
  · rw [show ((j : ℤ) + 1).toNat = j + 1 by omega]
  · exact absurd (by omega : (1 : ℤ) ≤ (j : ℤ) + 1) hh

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem freq2_inr (hf hp : ℝ) (m : ℕ) :
    P.freq2 hf hp (zsplit (Sum.inr m)) = -(hp * P.cCoef m) := by
  rw [zsplit_inr]
  unfold freq2
  split_ifs with hh
  · exact absurd hh (by omega)
  · rw [show (-(-(m : ℤ))).toNat = m by omega]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_freq2 (hf hp : ℝ) : Summable fun k : ℤ => |P.freq2 hf hp k| := by
  rw [← zsplit.summable_iff]
  refine Summable.sum _ ?_ ?_
  · refine (P.summable_abs_freq_inl hf).congr fun j => ?_
    simp only [Function.comp_apply, P.freq2_inl hf hp j]
  · refine (P.summable_abs_freq_inr hp).congr fun m => ?_
    simp only [Function.comp_apply, P.freq2_inr hf hp m]

/-- `G^λ_p(h)`, the `h`-th Fourier coefficient of `F^λ_*μ_p`: the two one-sided Erdős products
of `BB61/ProductFormula.lean`, evaluated at the two twisted frequencies. -/
noncomputable def weylCL (l : ℤ × ℤ) (p h : ℝ) : ℂ :=
  P.futProdC p (h * P.lamR l) * P.pastProdC p (h * P.lamC l)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylCL_one (p h : ℝ) : P.weylCL (1, 0) p h = P.weylC p h := by
  rw [weylCL, P.lamR_one, P.lamC_one, mul_one, weylC]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tprod_phi_freq2 {p : ℝ} (h0 : 0 ≤ p) (hf hp : ℝ) :
    ∏' k : ℤ, phi p (P.freq2 hf hp k) = P.futProdC p hf * P.pastProdC p hp := by
  have hinl : ∀ j : ℕ, phi p (P.freq2 hf hp (zsplit (Sum.inl j)))
      = phi p (hf * (P.α - 1) / P.α ^ (j + 1)) := fun j => by rw [P.freq2_inl hf hp j]
  have hinr : ∀ m : ℕ, phi p (P.freq2 hf hp (zsplit (Sum.inr m))) = phi p (-(hp * P.cCoef m)) :=
    fun m => by rw [P.freq2_inr hf hp m]
  calc ∏' k : ℤ, phi p (P.freq2 hf hp k)
      = ∏' i : ℕ ⊕ ℕ, phi p (P.freq2 hf hp (zsplit i)) :=
        (zsplit.tprod_eq fun k : ℤ => phi p (P.freq2 hf hp k)).symm
    _ = (∏' j : ℕ, phi p (P.freq2 hf hp (zsplit (Sum.inl j))))
        * ∏' m : ℕ, phi p (P.freq2 hf hp (zsplit (Sum.inr m))) :=
        Multipliable.tprod_sum
          ((P.multipliable_futProdC h0 hf).congr fun j => (hinl j).symm)
          ((P.multipliable_pastProdC h0 hp).congr fun m => (hinr m).symm)
    _ = P.futProdC p hf * P.pastProdC p hp := by
        rw [futProdC, pastProdC, tprod_congr hinl, tprod_congr hinr]

/-- **The twisted ladder computes the twisted coding**: `h · F^λ(ω) = ∑_{k∈ℤ} y_k ω_k`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_freq2_mul_bitR (hf hp : ℝ) (ω : Shift) :
    ∑' k : ℤ, P.freq2 hf hp k * bitR (ω k)
      = hf * piVal P.α (futures ω) - hp * P.wVal (pasts ω) := by
  have hinl : ∀ j : ℕ, P.freq2 hf hp (zsplit (Sum.inl j)) * bitR (ω (zsplit (Sum.inl j)))
      = (hf * (P.α - 1) / P.α ^ (j + 1)) * dR (futures ω) j := by
    intro j
    rw [P.freq2_inl hf hp j, show bitR (ω (zsplit (Sum.inl j))) = dR (futures ω) j from rfl]
  have hinr : ∀ m : ℕ, P.freq2 hf hp (zsplit (Sum.inr m)) * bitR (ω (zsplit (Sum.inr m)))
      = (-(hp * P.cCoef m)) * dR (pasts ω) m := by
    intro m
    rw [P.freq2_inr hf hp m, show bitR (ω (zsplit (Sum.inr m))) = dR (pasts ω) m from rfl]
  calc ∑' k : ℤ, P.freq2 hf hp k * bitR (ω k)
      = ∑' i : ℕ ⊕ ℕ, P.freq2 hf hp (zsplit i) * bitR (ω (zsplit i)) :=
        (zsplit.tsum_eq fun k : ℤ => P.freq2 hf hp k * bitR (ω k)).symm
    _ = (∑' j : ℕ, P.freq2 hf hp (zsplit (Sum.inl j)) * bitR (ω (zsplit (Sum.inl j))))
        + ∑' m : ℕ, P.freq2 hf hp (zsplit (Sum.inr m)) * bitR (ω (zsplit (Sum.inr m))) :=
        Summable.tsum_sum ((P.summable_future hf (futures ω)).congr fun j => (hinl j).symm)
          ((P.summable_past hp (pasts ω)).congr fun m => (hinr m).symm)
    _ = hf * piVal P.α (futures ω) + -(hp * P.wVal (pasts ω)) := by
        rw [tsum_congr hinl, tsum_congr hinr, P.tsum_future hf (futures ω),
          P.tsum_past hp (pasts ω)]
    _ = hf * piVal P.α (futures ω) - hp * P.wVal (pasts ω) := by ring

/-- **M5 Theorem 2 for `F^λ`.**  Under the Bernoulli(`p`) measure the expectation of
`e(h F^λ(ω))` is the twisted doubly infinite Erdős product `G^λ_p(h)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cexp1_fRawL {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ) (h : ℝ) :
    ∫ ω, cexp1 (h * P.fRawL l ω) ∂(bernZ p) = P.weylCL l p h := by
  calc ∫ ω, cexp1 (h * P.fRawL l ω) ∂(bernZ p)
      = ∫ ω, cexp1 (∑' k : ℤ, P.freq2 (h * P.lamR l) (h * P.lamC l) k * bitR (ω k))
          ∂(bernZ p) := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        show cexp1 (h * P.fRawL l ω)
          = cexp1 (∑' k : ℤ, P.freq2 (h * P.lamR l) (h * P.lamC l) k * bitR (ω k))
        rw [P.tsum_freq2_mul_bitR, fRawL]
        congr 1
        ring
    _ = ∏' k : ℤ, phi p (P.freq2 (h * P.lamR l) (h * P.lamC l) k) :=
        integral_bernZ_cexp1_tsum h0 h1 (P.summable_abs_freq2 _ _)
    _ = P.weylCL l p h := P.tprod_phi_freq2 h0 _ _

/-- **M5 Theorem 2 for `F^λ`, in Fourier form.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourier_map_fMapL {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ) (n : ℤ) :
    ∫ z, fourier n z ∂(Measure.map (P.fMapL l) (bernZ p)) = P.weylCL l p (n : ℝ) := by
  rw [integral_map (P.measurable_fMapL l).aemeasurable
      (map_continuous (fourier n)).aestronglyMeasurable,
    ← P.integral_cexp1_fRawL h0 h1 l (n : ℝ)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show fourier n (P.fMapL l ω) = cexp1 ((n : ℝ) * P.fRawL l ω)
  rw [fMapL, fourier_coe_apply, cexp1]
  congr 1
  push_cast
  ring

/-! ## `G^λ_p(h) ≠ 0` -/

/-- Every future frequency of the twisted ladder lies in `ℤ[α]` — **here, and only here, is
the unit hypothesis spent**. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_futArg (hb : P.b * P.b = 1) (l : ℤ × ℤ) (k : ℤ) (j : ℕ) :
    P.IsIntComb (((k : ℝ) * P.lamR l) * (P.α - 1) / P.α ^ (j + 1)) := by
  have hrw : ((k : ℝ) * P.lamR l) * (P.α - 1) / P.α ^ (j + 1)
      = ((k : ℝ) * P.lamR l) * (P.α - 1) * (P.α⁻¹) ^ (j + 1) := by
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  exact P.isIntComb_mul
    (P.isIntComb_mul (P.isIntComb_mul (P.isIntComb_intCast k) (P.isIntComb_lamR l))
      (P.isIntComb_sub P.isIntComb_alpha P.isIntComb_one))
    (P.isIntComb_pow (P.isIntComb_inv_alpha hb) (j + 1))

/-- Every past frequency of the twisted ladder lies in `ℤ[α]` — no unit hypothesis needed,
because `β = a - α` is there for free. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntComb_pastArg (l : ℤ × ℤ) (k : ℤ) (m : ℕ) :
    P.IsIntComb (-(((k : ℝ) * P.lamC l) * P.cCoef m)) := by
  simp only [cCoef]
  exact P.isIntComb_neg
    (P.isIntComb_mul (P.isIntComb_mul (P.isIntComb_intCast k) (P.isIntComb_lamC l))
      (P.isIntComb_mul (P.isIntComb_sub P.isIntComb_beta P.isIntComb_one)
        (P.isIntComb_pow P.isIntComb_beta m)))

/-- **M5 Theorem 3 for the twisted product.**  At a quadratic *unit* with irrational `α`, no
factor of `G^λ_p(h)` vanishes, for any `p ∈ [0,1]`, any `λ ∈ ℤ[α]` and any integer frequency —
`α > 2` is spent nowhere. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylCL_ne_zero (hb : P.b * P.b = 1) (hirr : Irrational P.α) {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p ≤ 1) (l : ℤ × ℤ) (k : ℤ) : P.weylCL l p (k : ℝ) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · rw [futProdC]
    exact tprod_phi_ne_zero h0 (P.summable_abs_freq_inl _) fun j =>
      P.phi_ne_zero_of_isIntComb h0 h1 hirr (P.isIntComb_futArg hb l k j)
  · rw [pastProdC]
    exact tprod_phi_ne_zero h0 (P.summable_abs_freq_inr _) fun m =>
      P.phi_ne_zero_of_isIntComb h0 h1 hirr (P.isIntComb_pastArg l k m)

/-- **`F^λ_*μ_p ≠ Leb`.**  The twisted coding measure is never Lebesgue at a quadratic unit
with irrational `α`: its first Fourier coefficient is `G^λ_p(1) ≠ 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_fMapL_bernZ_ne_volume (hb : P.b * P.b = 1) (hirr : Irrational P.α) {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ) :
    Measure.map (P.fMapL l) (bernZ p) ≠ (volume : Measure (AddCircle (1 : ℝ))) := by
  intro hcon
  have hf := P.integral_fourier_map_fMapL h0 h1 l 1
  rw [hcon, ← haarAddCircle_eq_volume, integral_fourier_eq_zero one_ne_zero] at hf
  exact P.weylCL_ne_zero hb hirr h0 h1 l 1 (by simpa using hf.symm)

/-! ## Corollary 6 -/

/-- **M5 Corollary 6, with the constant.**  At a Bernoulli(`p`)-generic digit word the Weyl
sums of the *multiplied* orbit `(λ ξ αⁿ)` converge to the twisted Erdős product `G^λ_p(h)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylSum_bern_mul {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ)
    {ε : ℕ → Bool} (hgen : IsGenericFor (bernNP h0 h1) ε) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
        cexp1 ((k : ℝ) * (P.lamR l * (piVal P.α ε * P.α ^ n)))) / ((N : ℂ) + 1))
      atTop (𝓝 (P.weylCL l p (k : ℝ))) := by
  have h := (P.codingL l).tendsto_weylSum_of_generic (isNaturalExtension_bern h0 h1) hgen
    (P.fMapL_iterate_padZ l ε) k
  rwa [show ((bernZP h0 h1 : ProbabilityMeasure Shift) : Measure Shift) = bernZ p from rfl,
    show (P.codingL l).toFun = P.fMapL l from rfl,
    P.integral_fourier_map_fMapL h0 h1 l k] at h

/-- **M5 Corollary 6 — the multiplier version, discharging the [BM97] conditional.**  Let `α`
be a quadratic Pisot *unit* with `α` irrational, `λ = l₁ + l₂α ∈ ℤ[α]`, `p ∈ [0,1]`, and let
`ε` be Bernoulli(`p`)-generic.  Then `(λ π(ε) αⁿ)` is **not** uniformly distributed modulo
one: its limit law is `F^λ_*μ_p`, whose Fourier coefficients are all non-zero.

[BM97] p. 188 asserts exactly this with « une légère modification de la preuve montrerait ».
The modification is one word — `(α-1)` becomes `λ(α-1)` — and it is `fMapL`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_bern_generic_mul (hb : P.b * P.b = 1) (hirr : Irrational P.α)
    {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ)
    {ε : ℕ → Bool} (hgen : IsGenericFor (bernNP h0 h1) ε) :
    ¬ IsEquidistributedModuloOne (fun n : ℕ => P.lamR l * (piVal P.α ε * P.α ^ n)) := by
  intro hud
  have hmap := (P.equidistributed_iff_map_eq_haarT_mul l
    (isNaturalExtension_bern h0 h1) hgen).mp hud
  have hh := congrArg (fun ρ : ProbabilityMeasure (AddCircle (1 : ℝ)) =>
    (ρ : Measure (AddCircle (1 : ℝ)))) hmap
  rw [toMeasure_pmap, toMeasure_haarT,
    show ((bernZP h0 h1 : ProbabilityMeasure Shift) : Measure Shift) = bernZ p from rfl] at hh
  exact P.map_fMapL_bernZ_ne_volume hb hirr h0 h1 l hh

/-- **Corollary 6, a.e. form.**  For every multiplier at once: the set of digit words whose
multiplied orbit is u.d. is `μ_p`-null. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_not_equidistributed_bern_mul (hb : P.b * P.b = 1) (hirr : Irrational P.α)
    {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ) :
    ∀ᵐ ε ∂(bernN p),
      ¬ IsEquidistributedModuloOne (fun n : ℕ => P.lamR l * (piVal P.α ε * P.α ^ n)) := by
  filter_upwards [ae_isGenericFor_bern h0 h1] with ε hε
  exact P.not_equidistributed_of_bern_generic_mul hb hirr h0 h1 l hε

/-- Corollary 6 as a null-set statement. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measure_equidistributed_bern_mul_eq_zero (hb : P.b * P.b = 1) (hirr : Irrational P.α)
    {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (l : ℤ × ℤ) :
    bernN p {ε : ℕ → Bool |
        IsEquidistributedModuloOne fun n : ℕ => P.lamR l * (piVal P.α ε * P.α ^ n)} = 0 := by
  have h := P.ae_not_equidistributed_bern_mul hb hirr h0 h1 l
  rw [ae_iff] at h
  simpa using h

end QuadSetup

/-! ## The instance `α = 2 + √3` -/

open QuadSetup

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_b_sq : twoAddSqrt3.b * twoAddSqrt3.b = 1 := by decide

/-- **Corollary 6 at `α = 2 + √3`**, a quadratic Pisot unit of norm `+1`: for every
`λ ∈ ℤ[2+√3]`, no fair-coin generic word gives an equidistributed multiplied orbit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_bern_half_generic_mul_twoAddSqrt3 (l : ℤ × ℤ) {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)) ε) :
    ¬ IsEquidistributedModuloOne
      (fun n : ℕ => twoAddSqrt3.lamR l * (piVal twoAddSqrt3.α ε * twoAddSqrt3.α ^ n)) :=
  twoAddSqrt3.not_equidistributed_of_bern_generic_mul twoAddSqrt3_b_sq irrational_twoAddSqrt3
    (by norm_num) (by norm_num) l hgen

/-- Corollary 6 at `α = 2 + √3`, a.e. form. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ae_not_equidistributed_bern_half_mul_twoAddSqrt3 (l : ℤ × ℤ) :
    ∀ᵐ ε ∂(bernN (1 / 2)), ¬ IsEquidistributedModuloOne
      (fun n : ℕ => twoAddSqrt3.lamR l * (piVal twoAddSqrt3.α ε * twoAddSqrt3.α ^ n)) :=
  twoAddSqrt3.ae_not_equidistributed_bern_mul twoAddSqrt3_b_sq irrational_twoAddSqrt3
    (by norm_num) (by norm_num) l

end BB61
