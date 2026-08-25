/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import SZ.DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The square-root slice: the cover game at a general base and a general modulus

Sections 3–5 of `paper-dubD1O5.tex`, uniformly in the base `m` **and** in the modulus `p`.
This is the engine `SZ/CoverGame.lean` runs at `m = 3`, rebuilt so that the four remaining
cells `m ∈ {5,6,7,8}` of Theorem B (`SZ/Cells.lean`, `p = 2`) and Theorem C
(`SZ/ThmC.lean`, arbitrary `p`) can both be instantiated from it.

## The data

A `Slice` packages a base `m ≥ 3`, a modulus `p ≥ 2`, the largest digit `e` of the
alphabet `Ev = {0, p, 2p, …, e}`, and the window `U = M(1+√m)`, `M = e/(m-1)`, subject to
the two **gap conditions** of the paper's Theorem 4.1,

`p ≤ U`   and   `p√m - e ≤ U`,

which are exactly what makes the `(e/p+1)²` offsets `c = a + b√m`, `a, b ∈ Ev`, cover
`[0, mU]` in windows of length `U`.

## The rule

The selection rule is the paper's (4.3), in closed form:

`b = min e (p⌊w/(p√m)⌋)`,   `a = p max(0, ⌈(w - b√m - U)/p⌉)`,

i.e. take the largest multiple `b ≤ e` of `p` with `b√m ≤ w`, then the smallest multiple
`a ≥ 0` of `p` that brings the residual into `[0, U]`.  Two things fall out of the formula
that the abstract description — *smallest admissible `a`, then largest `b`* (paper
Remark 5.1) — has to work for: admissibility is a two-case computation, and
`b = 0 ↔ w < p√m` (paper (5.2), `bsel_eq_zero_iff` below) is definitional, which is what
removed an induction on `a_*/p` from the paper's Section 5.1.

## What is here

* `Slice.pick_adm` — the covering induction, Theorem 4.1 of the paper;
* `Slice.digitReal_translate` — the greedy solves `x + √m y'' = σ` in the restricted-digit
  Cantor set `K` (Section 4);
* `Slice.digitReal_compl'` — `M - K = K`, the digitwise complement `b ↦ e - b`;
* `Slice.exists_translate` — the paper's Lemma 3.3: a lattice point `σ ∈ (0, U)` exists,
  because the progression has step `p ≤ U` and its endpoints are irrational;
* `Slice.dvd_floor_of_hygiene` — the reduction, Proposition 3.2: with tail hygiene
  \eqref{eq:L1} the greedy's streams give a `ξ > 0` with `p ∣ ⌊ξ √mⁿ⌋` for all `n ≥ 1`;
* `Slice.dvd_floor_of_e_le` — the case `e ≤ m - 2`, where hygiene is free (Remark 2.2);
* `Slice.mem_MahlerZ_of_hygiene`, `Slice.mem_MahlerZ_of_e_le` — the same two statements at
  `p = 2`, where divisibility is parity and the conclusion is `√m ∈ 𝒵`.

Tail hygiene at `e = m - 1` is `SZ/SliceHygiene.lean`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
* [Utz51] W. R. Utz, *The distance set for the Cantor discontinuum*, Amer. Math. Monthly
  **58** (1951), 407–408.
-/

namespace SZ

open Filter Topology

/-- `Nat.sqrt` does not reduce in the kernel, so the `DecidablePred (IsSquare : ℕ → Prop)`
instance is useless to `decide`; this reduces the check to a bounded search, which
`decide` does handle. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem not_isSquare_of_bounded {n : ℕ} (hn : 0 < n) (h : ∀ r, r ≤ n → r * r ≠ n) :
    ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by
    by_contra hgt
    push Not at hgt
    nlinarith
  exact h r hle hr.symm

/-- The data of one cell of the square-root slice: the base `m`, the modulus `p`, the
largest digit `e` of the alphabet `{0, p, …, e}`, and the window `U = M(1+√m)` with
`M = e/(m-1)`, together with the two gap conditions of the covering induction. -/
structure Slice where
  /-- the base -/
  m : ℕ
  /-- the modulus: the digit alphabet is the multiples of `p` up to `e` -/
  p : ℤ
  /-- the largest digit -/
  e : ℤ
  /-- the window `M(1+√m)` -/
  U : ℝ
  three_le : 3 ≤ m
  not_square : ¬ IsSquare m
  two_le_p : 2 ≤ p
  p_le_e : p ≤ e
  p_dvd_e : p ∣ e
  e_le : e ≤ (m : ℤ) - 1
  U_def : ((m : ℝ) - 1) * U = (e : ℝ) * (1 + Real.sqrt m)
  p_le_U : (p : ℝ) ≤ U
  gap : (p : ℝ) * Real.sqrt m - (e : ℝ) ≤ U

namespace Slice

variable (S : Slice)

/-! ## Basic arithmetic of the base and the modulus -/

/-- `√m`. -/
noncomputable def sq : ℝ := Real.sqrt S.m

theorem sq_nonneg : 0 ≤ S.sq := Real.sqrt_nonneg _

/-- The window equation, phrased with `S.sq`. -/
theorem U_def' : ((S.m : ℝ) - 1) * S.U = (S.e : ℝ) * (1 + S.sq) := S.U_def

/-- The second gap condition, phrased with `S.sq`. -/
theorem gap' : (S.p : ℝ) * S.sq - (S.e : ℝ) ≤ S.U := S.gap

theorem one_lt_sq : 1 < S.sq := by
  have h1 : (1 : ℝ) < (S.m : ℝ) := by
    have := S.three_le
    have : (3 : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast this
    linarith
  have h : Real.sqrt 1 < Real.sqrt S.m := Real.sqrt_lt_sqrt (by norm_num) h1
  rwa [Real.sqrt_one] at h

theorem sq_pos : 0 < S.sq := lt_trans zero_lt_one S.one_lt_sq

theorem sq_sq : S.sq ^ 2 = (S.m : ℝ) :=
  Real.sq_sqrt (by positivity)

theorem irrational_sq : Irrational S.sq :=
  irrational_sqrt_natCast_iff.mpr S.not_square

theorem p_pos : 0 < S.p := lt_of_lt_of_le two_pos S.two_le_p

theorem p_cast_pos : (0 : ℝ) < (S.p : ℝ) := by exact_mod_cast S.p_pos

theorem p_cast_ne : (S.p : ℝ) ≠ 0 := ne_of_gt S.p_cast_pos

theorem p_sq_pos : (0 : ℝ) < (S.p : ℝ) * S.sq := mul_pos S.p_cast_pos S.sq_pos

/-- `ℤ[√m]` is free on `1, √m`: the coordinates of a state are well defined. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem val_inj {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * S.sq = (p' : ℝ) + (q' : ℝ) * S.sq) : p = p' ∧ q = q' := by
  have hq : q = q' := by
    by_contra hne
    have hd : (q - q' : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have he : ((q - q' : ℤ) : ℝ) * S.sq = ((p' - p : ℤ) : ℝ) := by push_cast; linarith
    exact (S.irrational_sq.intCast_mul hd).ne_int (p' - p) he
  refine ⟨?_, hq⟩
  subst hq
  have : (p : ℝ) = (p' : ℝ) := by linarith
  exact_mod_cast this

theorem three_le_cast : (3 : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast S.three_le

theorem U_pos : 0 < S.U := lt_of_lt_of_le S.p_cast_pos S.p_le_U

theorem e_pos : 0 < S.e := lt_of_lt_of_le S.p_pos S.p_le_e

theorem e_cast_le : (S.e : ℝ) ≤ (S.m : ℝ) - 1 := by
  have := S.e_le
  have : ((S.e : ℤ) : ℝ) ≤ (((S.m : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at this
  linarith

/-- The maximum `M = e/(m-1)` of the restricted-digit Cantor set `K`. -/
noncomputable def M : ℝ := (S.e : ℝ) / ((S.m : ℝ) - 1)

theorem m_sub_one_ne : ((S.m : ℝ) - 1) ≠ 0 := by
  have := S.three_le_cast; intro h; linarith

theorem m_sub_one_pos : (0 : ℝ) < (S.m : ℝ) - 1 := by have := S.three_le_cast; linarith

theorem M_mul : ((S.m : ℝ) - 1) * S.M = (S.e : ℝ) := by
  have h := S.m_sub_one_ne
  rw [M, mul_comm, div_mul_cancel₀ _ h]

theorem M_le_one : S.M ≤ 1 := by
  have h := S.M_mul
  have h2 := S.e_cast_le
  have h3 := S.m_sub_one_pos
  nlinarith

theorem M_pos : 0 < S.M := div_pos (by exact_mod_cast S.e_pos) S.m_sub_one_pos

theorem U_eq : S.U = S.M * (1 + S.sq) := by
  refine mul_left_cancel₀ S.m_sub_one_ne ?_
  rw [S.U_def', ← S.M_mul]
  ring

/-! ## The digit alphabet -/

/-- The digit alphabet `Ev = {0, p, …, e}`. -/
def PDigit (d : ℤ) : Prop := S.p ∣ d ∧ 0 ≤ d ∧ d ≤ S.e

/-- The real value `a + b√m` of an offset. -/
noncomputable def val (c : ℤ × ℤ) : ℝ := (c.1 : ℝ) + (c.2 : ℝ) * S.sq

/-! ## The selection rule -/

/-- The `b`-digit: the largest multiple `b ≤ e` of `p` with `b√m ≤ w`. -/
noncomputable def bsel (w : ℝ) : ℤ := min S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋)

/-- The `a`-digit: the smallest multiple `a ≥ 0` of `p` with `w - a - b√m ≤ U`. -/
noncomputable def asel (w : ℝ) : ℤ :=
  S.p * max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉

/-- The offset the rule selects at state value `w`. -/
noncomputable def pick (w : ℝ) : ℤ × ℤ := (S.asel w, S.bsel w)

theorem bsel_le (w : ℝ) : S.bsel w ≤ S.e := min_le_left _ _

theorem bsel_dvd (w : ℝ) : S.p ∣ S.bsel w := by
  rcases min_cases S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [bsel, h]
  · exact S.p_dvd_e
  · exact dvd_mul_right _ _

theorem asel_dvd (w : ℝ) : S.p ∣ S.asel w := dvd_mul_right _ _

theorem bsel_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ S.bsel w := by
  have h1 : (0 : ℤ) ≤ ⌊w / ((S.p : ℝ) * S.sq)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg hw S.p_sq_pos.le)
  exact le_min S.e_pos.le (mul_nonneg S.p_pos.le h1)

theorem bsel_mul_le (w : ℝ) : (S.bsel w : ℝ) * S.sq ≤ w := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  have hne : ((S.p : ℝ) * S.sq) ≠ 0 := ne_of_gt hs
  have hcancel : ((S.p : ℝ) * S.sq) * (w / ((S.p : ℝ) * S.sq)) = w := by
    rw [mul_comm, div_mul_cancel₀ _ hne]
  have h1 : ((S.p : ℝ) * S.sq) * (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) ≤ w := by
    have := mul_le_mul_of_nonneg_left (Int.floor_le (w / ((S.p : ℝ) * S.sq))) hs.le
    rw [hcancel] at this
    exact this
  have h2 : (S.bsel w : ℝ) ≤ ((S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ : ℤ) : ℝ) := by
    have : S.bsel w ≤ S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ := min_le_right _ _
    exact_mod_cast this
  push_cast at h2
  nlinarith [S.sq_pos]

theorem lt_bsel_add {w : ℝ} (h : S.bsel w < S.e) :
    w < ((S.bsel w : ℝ) + (S.p : ℝ)) * S.sq := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  have hb : S.bsel w = S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ := by
    rcases min_cases S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋) with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [bsel, h1] at h; omega
    · rw [bsel, h1]
  have hf : w / ((S.p : ℝ) * S.sq) < (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hw := (div_lt_iff₀ hs).mp hf
  have hid : ((⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + 1) * ((S.p : ℝ) * S.sq)
      = ((S.p : ℝ) * (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + (S.p : ℝ)) * S.sq := by ring
  rw [hb]
  push_cast
  linarith [hid ▸ hw]

/-- `b = 0` exactly on `L = [0, p√m)` — the paper's (5.2), immediate from the formula. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem bsel_eq_zero_iff {w : ℝ} (h0 : 0 ≤ w) : S.bsel w = 0 ↔ w < (S.p : ℝ) * S.sq := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ w / ((S.p : ℝ) * S.sq) := (le_div_iff₀ hs).mpr (by linarith)
    have h2 : (1 : ℤ) ≤ ⌊w / ((S.p : ℝ) * S.sq)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
    have h3 : S.p ≤ S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ :=
      le_mul_of_one_le_right S.p_pos.le h2
    have h4 := S.p_le_e
    have h5 := S.p_pos
    rw [bsel] at h
    set t : ℤ := S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋
    omega
  · intro h
    have h1 : w / ((S.p : ℝ) * S.sq) < 1 := (div_lt_one hs).mpr h
    have h2 : ⌊w / ((S.p : ℝ) * S.sq)⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨div_nonneg h0 hs.le, h1⟩
    rw [bsel, h2, mul_zero]
    exact min_eq_right S.e_pos.le

/-- Below the window the rule takes `a = 0`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem asel_eq_zero {w : ℝ} (h : w - (S.bsel w : ℝ) * S.sq ≤ S.U) : S.asel w = 0 := by
  have hdiv : (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) ≤ 0 :=
    (div_le_iff₀ S.p_cast_pos).mpr (by linarith)
  have hc : ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ ≤ 0 :=
    Int.ceil_le.mpr (by push_cast; exact hdiv)
  rw [asel, max_eq_left hc, mul_zero]

/-- Above the window the rule takes the least admissible `a`: `a < v - U + p`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem asel_lt {w : ℝ} (h : S.U < w - (S.bsel w : ℝ) * S.sq) :
    (S.asel w : ℝ) < w - (S.bsel w : ℝ) * S.sq - S.U + (S.p : ℝ) := by
  have hp := S.p_cast_pos
  have hpos : (0 : ℝ) < (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) :=
    div_pos (by linarith) hp
  have hc : (0 : ℤ) < ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ :=
    Int.lt_ceil.mpr (by push_cast; exact hpos)
  have hmax : max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉
      = ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ := max_eq_right (le_of_lt hc)
  have hlt : (⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ : ℝ)
      < (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) + 1 := Int.ceil_lt_add_one _
  have hmul := mul_lt_mul_of_pos_left hlt hp
  have hcancel : (S.p : ℝ) * ((w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) + 1)
      = w - (S.bsel w : ℝ) * S.sq - S.U + (S.p : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  rw [asel, hmax]
  push_cast
  linarith

/-- The rule never overshoots: `v - U ≤ a`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem le_asel (w : ℝ) : w - (S.bsel w : ℝ) * S.sq - S.U ≤ (S.asel w : ℝ) := by
  have hp := S.p_cast_pos
  have hge : (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)
      ≤ ((max 0 ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ : ℤ) : ℝ) := by
    refine le_trans (Int.le_ceil _) ?_
    exact_mod_cast le_max_right (0 : ℤ) ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉
  have hmul := mul_le_mul_of_nonneg_left hge hp.le
  have hcancel : (S.p : ℝ) * ((w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ))
      = w - (S.bsel w : ℝ) * S.sq - S.U := by field_simp
  rw [hcancel] at hmul
  rw [asel]
  push_cast at hmul ⊢
  linarith

/-! ## The covering induction (paper Theorem 4.1) -/

/-- **The cover lemma.**  At every `w ∈ [0, mU]` the selected offset is admissible: both
digits lie in `Ev` and the residual `w - a - b√m` lies in `[0, U]`.  This is the paper's
Theorem 4.1, and at `p = 2`, `m = 3` it is Utz's theorem. -/
@[category research solved, AMS 11, ref "Utz51", group "dub06_slice"]
theorem pick_adm {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ (S.m : ℝ) * S.U) :
    S.PDigit (S.pick w).1 ∧ S.PDigit (S.pick w).2 ∧
      0 ≤ w - S.val (S.pick w) ∧ w - S.val (S.pick w) ≤ S.U := by
  set v : ℝ := w - (S.bsel w : ℝ) * S.sq with hv
  have hv0 : 0 ≤ v := by have := S.bsel_mul_le w; linarith
  have hval : w - S.val (S.pick w) = v - (S.asel w : ℝ) := by
    simp only [val, pick]
    rw [hv]; ring
  -- the two cases of the rule
  have hcase : (v ≤ S.U ∧ S.asel w = 0) ∨
      (S.U < v ∧ v - S.U ≤ (S.asel w : ℝ) ∧ (S.asel w : ℝ) < v - S.U + (S.p : ℝ)) := by
    rcases le_or_gt v S.U with hle | hlt
    · exact Or.inl ⟨hle, S.asel_eq_zero (by rw [← hv]; exact hle)⟩
    · refine Or.inr ⟨hlt, ?_, ?_⟩
      · have := S.le_asel w; rw [← hv] at this; linarith
      · have := S.asel_lt (by rw [← hv]; exact hlt); rw [← hv] at this; linarith
  -- the residual
  have hres : 0 ≤ w - S.val (S.pick w) ∧ w - S.val (S.pick w) ≤ S.U := by
    rw [hval]
    rcases hcase with ⟨hle, hz⟩ | ⟨hlt, hlo, hhi⟩
    · rw [hz]; push_cast; constructor <;> linarith
    · have := S.p_le_U; constructor <;> linarith
  -- the `a` digit lies in `Ev`
  have hadvd : S.p ∣ S.asel w := S.asel_dvd w
  have hanonneg : 0 ≤ S.asel w :=
    mul_nonneg S.p_pos.le (le_max_left _ _)
  have hale : S.asel w ≤ S.e := by
    rcases hcase with ⟨-, hz⟩ | ⟨hlt, -, hhi⟩
    · rw [hz]; exact le_of_lt S.e_pos
    · -- `a < v - U + p`, and `v` is bounded either by maximality of `b` or by `w ≤ mU`
      have hvb : v ≤ (S.e : ℝ) + S.U := by
        rcases lt_or_eq_of_le (S.bsel_le w) with hb | hb
        · have hlt' := S.lt_bsel_add hb
          have hexp : ((S.bsel w : ℝ) + (S.p : ℝ)) * S.sq
              = (S.bsel w : ℝ) * S.sq + (S.p : ℝ) * S.sq := by ring
          rw [hexp] at hlt'
          have hgap := S.gap'
          rw [hv]
          linarith
        · have hbe : (S.bsel w : ℝ) = (S.e : ℝ) := by rw [hb]
          have hexp : (S.e : ℝ) * (1 + S.sq) = (S.e : ℝ) + (S.e : ℝ) * S.sq := by ring
          have hU := S.U_def'
          rw [hexp] at hU
          have hmU : (S.m : ℝ) * S.U - S.U = (S.e : ℝ) + (S.e : ℝ) * S.sq := by
            rw [← hU]; ring
          rw [hv, hbe]
          linarith
      have h2 : (S.asel w : ℝ) < (S.e : ℝ) + (S.p : ℝ) := by linarith
      have h3 : S.asel w < S.e + S.p := by exact_mod_cast h2
      obtain ⟨r, hr⟩ := hadvd
      obtain ⟨t, ht⟩ := S.p_dvd_e
      have h4 : S.p * r < S.p * (t + 1) := by
        calc S.p * r < S.e + S.p := by rw [← hr]; exact h3
          _ = S.p * t + S.p := by rw [ht]
          _ = S.p * (t + 1) := by ring
      have h5 : r < t + 1 := lt_of_mul_lt_mul_left h4 S.p_pos.le
      calc S.asel w = S.p * r := hr
        _ ≤ S.p * t := mul_le_mul_of_nonneg_left (by omega) S.p_pos.le
        _ = S.e := ht.symm
  exact ⟨⟨hadvd, hanonneg, hale⟩, ⟨S.bsel_dvd w, S.bsel_nonneg h0, S.bsel_le w⟩, hres⟩

/-! ## The greedy -/

/-- The state of the greedy, rescaled by `m^{k+1}`: `W (k+1) = m (W k - c_k)`. -/
noncomputable def W (S : Slice) (w₀ : ℝ) : ℕ → ℝ
  | 0 => w₀
  | k + 1 => (S.m : ℝ) * (W S w₀ k - S.val (S.pick (W S w₀ k)))

theorem W_zero (w₀ : ℝ) : S.W w₀ 0 = w₀ := rfl

theorem W_succ (w₀ : ℝ) (k : ℕ) :
    S.W w₀ (k + 1) = (S.m : ℝ) * (S.W w₀ k - S.val (S.pick (S.W w₀ k))) := rfl

/-- The `a`-stream of the greedy. -/
noncomputable def dA (S : Slice) (w₀ : ℝ) (k : ℕ) : ℤ := S.asel (S.W w₀ k)

/-- The `b`-stream of the greedy. -/
noncomputable def dB (S : Slice) (w₀ : ℝ) (k : ℕ) : ℤ := S.bsel (S.W w₀ k)

theorem dA_eq (w₀ : ℝ) (k : ℕ) : S.dA w₀ k = S.asel (S.W w₀ k) := rfl

theorem dB_eq (w₀ : ℝ) (k : ℕ) : S.dB w₀ k = S.bsel (S.W w₀ k) := rfl

theorem val_pick_W (w₀ : ℝ) (k : ℕ) :
    S.val (S.pick (S.W w₀ k)) = (S.dA w₀ k : ℝ) + (S.dB w₀ k : ℝ) * S.sq := rfl

variable {S}

/-- The greedy never leaves `[0, mU]`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem W_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    0 ≤ S.W w₀ k ∧ S.W w₀ k ≤ (S.m : ℝ) * S.U := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨-, -, hlo, hhi⟩ := S.pick_adm ih.1 ih.2
    have hm : (0 : ℝ) ≤ (S.m : ℝ) := by positivity
    rw [W_succ]
    constructor
    · exact mul_nonneg hm hlo
    · exact mul_le_mul_of_nonneg_left hhi hm

theorem dA_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    S.PDigit (S.dA w₀ k) :=
  ((S.pick_adm (W_mem h0 h1 k).1 (W_mem h0 h1 k).2).1)

theorem dB_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    S.PDigit (S.dB w₀ k) :=
  ((S.pick_adm (W_mem h0 h1 k).1 (W_mem h0 h1 k).2).2.1)

theorem isDigits_dA {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) :
    IsDigits S.m (S.dA w₀) :=
  { two_le := by have := S.three_le; omega
    nonneg := fun i => (dA_mem h0 h1 i).2.1
    le_sub_one := fun i => le_trans (dA_mem h0 h1 i).2.2 S.e_le }

theorem isDigits_dB {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) :
    IsDigits S.m (S.dB w₀) :=
  { two_le := by have := S.three_le; omega
    nonneg := fun i => (dB_mem h0 h1 i).2.1
    le_sub_one := fun i => le_trans (dB_mem h0 h1 i).2.2 S.e_le }

/-! ## The greedy solves the translate equation -/

/-- The residual identity: `W k = m^{k+1} (σ - ⟨a⟩_k - √m ⟨b⟩_k)`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem W_eq_residual (S : Slice) (σ : ℝ) (k : ℕ) :
    S.W ((S.m : ℝ) * σ) k = (S.m : ℝ) ^ (k + 1) *
      (σ - digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
         - S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  induction k with
  | zero => rw [W_zero, digitSum_zero, digitSum_zero]; ring
  | succ k ih =>
    rw [W_succ, val_pick_W, ih, digitSum_succ, digitSum_succ]
    have hne : ((S.m : ℝ)) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- **The greedy converges to a solution of `x + √m y = σ`** in the restricted-digit
Cantor set `K` — the constructive form of the cover lemma. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem digitReal_translate (S : Slice) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ S.U) :
    digitReal S.m (S.dA ((S.m : ℝ) * σ)) + S.sq * digitReal S.m (S.dB ((S.m : ℝ) * σ)) = σ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ (S.m : ℝ) * σ := mul_nonneg hm.le h0
  have hw1 : (S.m : ℝ) * σ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  have hA := isDigits_dA hw0 hw1
  have hB := isDigits_dB hw0 hw1
  have hlim : Tendsto (fun k => digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) atTop
      (𝓝 (digitReal S.m (S.dA ((S.m : ℝ) * σ)) + S.sq * digitReal S.m (S.dB ((S.m : ℝ) * σ)))) :=
    (digitSum_tendsto hA).add (tendsto_const_nhds.mul (digitSum_tendsto hB))
  have hzero : Tendsto (fun k : ℕ => σ - (digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => ((S.m : ℝ) * S.U) / (S.m : ℝ) ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (W_mem hw0 hw1 k).1
      rw [W_eq_residual S σ k] at h
      have hp : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := by positivity
      nlinarith
    · have h := (W_mem hw0 hw1 k).2
      rw [W_eq_residual S σ k] at h
      have hp : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hg : Tendsto (fun k : ℕ => (1 / (S.m : ℝ)) ^ (k + 1)) atTop (𝓝 0) := by
        have h0' := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / (S.m : ℝ)))
          (by positivity) ((div_lt_one hm).mpr hm1)
        exact h0'.comp (Filter.tendsto_add_atTop_nat 1)
      have hmain : Tendsto (fun k : ℕ => ((S.m : ℝ) * S.U) * (1 / (S.m : ℝ)) ^ (k + 1))
          atTop (𝓝 0) := by simpa using hg.const_mul ((S.m : ℝ) * S.U)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) atTop (𝓝 σ) := by
    have h := (tendsto_const_nhds (x := σ) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2

/-! ## The complement stream (`M - K = K`) -/

/-- **`M - K = K`.**  The digitwise complement `d ↦ e - d` realises `M - ⟨d⟩`, where
`M = e/(m-1)` is the maximum of the restricted-digit Cantor set.  At `e = m - 1` this is
`SZ.digitReal_compl`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem digitReal_compl' (S : Slice) {d : ℕ → ℤ} (h : IsDigits S.m d) (hd : ∀ i, d i ≤ S.e) :
    digitReal S.m (fun i => S.e - d i) = S.M - digitReal S.m d := by
  have hm1 : (0 : ℝ) < (S.m : ℝ) - 1 := by have := S.three_le_cast; linarith
  have hc : IsDigits S.m (fun i => S.e - d i) :=
    { two_le := h.two_le
      nonneg := fun i => by have := hd i; omega
      le_sub_one := fun i => by have := h.nonneg i; have := S.e_le; omega }
  have hpartial : ∀ k, digitSum S.m (fun i => S.e - d i) k
      = S.M * (1 - 1 / (S.m : ℝ) ^ k) - digitSum S.m d k := by
    intro k
    induction k with
    | zero => simp [digitSum]
    | succ k ih =>
      rw [digitSum_succ, digitSum_succ, ih, M]
      have hp : (0 : ℝ) < (S.m : ℝ) ^ k := h.pow_pos' _
      have hp1 : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := h.pow_pos' _
      push_cast
      field_simp
      ring
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (S.m : ℝ) ^ k) atTop (𝓝 0) := by
    have hpow : ∀ k : ℕ, (1 : ℝ) / (S.m : ℝ) ^ k = (1 / (S.m : ℝ)) ^ k := fun k => by
      rw [div_pow, one_pow]
    simp only [hpow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one h.cast_pos).mpr h.one_lt_cast)
  have hlim : Tendsto (digitSum S.m (fun i => S.e - d i)) atTop (𝓝 (S.M - digitReal S.m d)) := by
    have hfun : digitSum S.m (fun i => S.e - d i)
        = fun k => S.M * (1 - 1 / (S.m : ℝ) ^ k) - digitSum S.m d k := funext hpartial
    rw [hfun]
    have hone : S.M - digitReal S.m d = S.M * (1 - 0) - digitReal S.m d := by ring
    rw [hone]
    exact ((tendsto_const_nhds (x := S.M)).mul
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0)).sub (digitSum_tendsto h)
  exact tendsto_nhds_unique (digitSum_tendsto hc) hlim

/-! ## The translate (paper Lemma 3.3) -/

/-- The target `σ = (p k₀ + M)√m - p j` of the translate equation. -/
noncomputable def sigma (S : Slice) (j k₀ : ℤ) : ℝ :=
  ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq - (S.p : ℝ) * (j : ℝ)

/-- The starting state `m σ` of the greedy. -/
noncomputable def w0 (S : Slice) (j k₀ : ℤ) : ℝ := (S.m : ℝ) * S.sigma j k₀

theorem w0_def (S : Slice) (j k₀ : ℤ) : S.w0 j k₀ = (S.m : ℝ) * S.sigma j k₀ := rfl

/-- **Lemma 3.3 (translate).**  As `j` runs through `ℤ`, `σ = (p k₀ + M)√m - p j` runs
through an arithmetic progression of step `p ≤ U`, so some value lands in the window;
neither endpoint can be hit, since `√m` is irrational.  The realising `j` is `≥ 1`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem exists_translate (S : Slice) {k₀ : ℤ} (hk : 1 ≤ k₀) :
    ∃ j : ℤ, 1 ≤ j ∧ 0 < S.sigma j k₀ ∧ S.sigma j k₀ < S.U := by
  have hp := S.p_cast_pos
  have hsq := S.sq_pos
  have h1sq := S.one_lt_sq
  have hM1 := S.M_le_one
  have hMpos := S.M_pos
  have hk1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
  set T : ℝ := ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq with hT
  -- `T - U = p k₀ √m - M`
  have hTU : T - S.U = (S.p : ℝ) * (k₀ : ℝ) * S.sq - S.M := by
    rw [hT, S.U_eq]; ring
  have hp2 : (2 : ℝ) ≤ (S.p : ℝ) := by exact_mod_cast S.two_le_p
  have hTUpos : 0 < T - S.U := by
    rw [hTU]
    have hkpos : (0 : ℝ) < (k₀ : ℝ) := by linarith
    have hpk : (2 : ℝ) ≤ (S.p : ℝ) * (k₀ : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (S.p : ℝ) - 2)
        (by linarith : (0:ℝ) ≤ (k₀ : ℝ) - 1)]
    nlinarith
  refine ⟨⌈(T - S.U) / (S.p : ℝ)⌉, ?_, ?_, ?_⟩
  · -- `j > (T-U)/p > 0`
    have h := Int.le_ceil ((T - S.U) / (S.p : ℝ))
    have hdiv : 0 < (T - S.U) / (S.p : ℝ) := div_pos hTUpos hp
    have : (0 : ℝ) < (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) := lt_of_lt_of_le hdiv h
    have h0 : (0 : ℤ) < ⌈(T - S.U) / (S.p : ℝ)⌉ := by exact_mod_cast this
    omega
  · -- `p j < T`, since `⌈x⌉ < x + 1` and `(T-U)/p + 1 ≤ T/p`
    have hlt : (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) < (T - S.U) / (S.p : ℝ) + 1 :=
      Int.ceil_lt_add_one _
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hcancel : (S.p : ℝ) * ((T - S.U) / (S.p : ℝ) + 1) = T - S.U + (S.p : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    have hU := S.p_le_U
    rw [sigma, ← hT]
    linarith
  · -- `p j > T - U`: `⌈x⌉ ≥ x`, and equality is impossible by irrationality
    have hge : (T - S.U) / (S.p : ℝ) ≤ (⌈(T - S.U) / (S.p : ℝ)⌉ : ℝ) := Int.le_ceil _
    have hmul := mul_le_mul_of_nonneg_left hge hp.le
    have hcancel : (S.p : ℝ) * ((T - S.U) / (S.p : ℝ)) = T - S.U := by field_simp
    rw [hcancel] at hmul
    rcases lt_or_eq_of_le hmul with hlt | heq
    · rw [sigma, ← hT]; linarith
    · -- `p j = p k₀ √m - M` would make `√m` rational
      exfalso
      set j : ℤ := ⌈(T - S.U) / (S.p : ℝ)⌉
      have hMval : ((S.m : ℝ) - 1) * S.M = (S.e : ℝ) := S.M_mul
      have hkey : (((S.m : ℤ) - 1) * S.p * k₀ : ℤ) * S.sq
          = (((S.m : ℤ) - 1) * S.p * j + S.e : ℤ) := by
        have hexp : ((S.m : ℝ) - 1) * ((S.p : ℝ) * (j : ℝ))
            = ((S.m : ℝ) - 1) * ((S.p : ℝ) * (k₀ : ℝ) * S.sq - S.M) := by
          rw [← hTU]; rw [heq]
        push_cast
        nlinarith [hMval, hexp]
      have hne : (((S.m : ℤ) - 1) * S.p * k₀ : ℤ) ≠ 0 := by
        have hm3 : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
        have hp0 := S.p_pos
        exact mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      exact (S.irrational_sq.intCast_mul hne).ne_int _ hkey

/-! ## The reduction (paper Proposition 3.2) -/

/-- **The reduction.**  If the translate `σ` lies in the window and the greedy's streams
satisfy the tail hygiene \eqref{eq:L1}, then `ξ = (p j + ⟨a⟩)/m` is a positive real with
`p ∣ ⌊ξ √mⁿ⌋` for every `n ≥ 1`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem dvd_floor_of_hygiene (S : Slice) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hm.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  have hdA := isDigits_dA hw0 hw1
  have hdB := isDigits_dB hw0 hw1
  have hdY : IsDigits S.m (fun i => S.e - S.dB (S.w0 j k₀) i) :=
    { two_le := hdB.two_le
      nonneg := fun i => by have := (dB_mem hw0 hw1 i).2.2; omega
      le_sub_one := fun i => by
        have := (dB_mem hw0 hw1 i).2.1; have := S.e_le; omega }
  set x : ℝ := digitReal S.m (S.dA (S.w0 j k₀)) with hxdef
  set y'' : ℝ := digitReal S.m (S.dB (S.w0 j k₀)) with hy''def
  set y : ℝ := digitReal S.m (fun i => S.e - S.dB (S.w0 j k₀) i) with hydef
  have htrans : x + S.sq * y'' = S.sigma j k₀ := digitReal_translate S h0 h1
  have hcompl : y = S.M - y'' :=
    digitReal_compl' S hdB (fun i => (dB_mem hw0 hw1 i).2.2)
  have htrans' : x + S.sq * y''
      = ((S.p : ℝ) * (k₀ : ℝ) + S.M) * S.sq - (S.p : ℝ) * (j : ℝ) := htrans
  have hcoup : (S.p : ℝ) * (j : ℝ) + x = S.sq * ((S.p : ℝ) * (k₀ : ℝ) + y) := by
    rw [hcompl]
    linear_combination htrans'
  have hxnn : 0 ≤ x := digitReal_nonneg hdA
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hppos := S.p_cast_pos
  have hxpos : 0 < (S.p : ℝ) * (j : ℝ) + x := by nlinarith
  have hξpos : 0 < ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) := div_pos hxpos hm
  -- the even exponents
  have heven : ∀ t : ℕ,
      S.p ∣ ⌊((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * (t + 1))⌋ := by
    intro t
    obtain ⟨i₀, hi₀, hsmall⟩ := hA t
    have hval : ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * (t + 1))
        = (((S.p * j : ℤ) : ℝ) + x) * (S.m : ℝ) ^ t := by
      rw [pow_mul, Real.sq_sqrt hm.le]
      push_cast
      field_simp
      ring
    rw [hval]
    exact dvd_floor_add_digitReal_mul_pow hdA (dvd_mul_right S.p j)
      (fun i => (dA_mem hw0 hw1 i).1) t hi₀ hsmall
  -- the odd exponents
  have hodd : ∀ t : ℕ,
      S.p ∣ ⌊((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * t + 1)⌋ := by
    intro t
    obtain ⟨i₀, hi₀, hsmall⟩ := hB t
    have hydvd : ∀ i, S.p ∣ (S.e - S.dB (S.w0 j k₀) i) := fun i =>
      dvd_sub S.p_dvd_e (dB_mem hw0 hw1 i).1
    have hval : ((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ) * Real.sqrt S.m ^ (2 * t + 1)
        = (((S.p * k₀ : ℤ) : ℝ) + y) * (S.m : ℝ) ^ t := by
      have hs2 : Real.sqrt S.m * Real.sqrt S.m = (S.m : ℝ) := Real.mul_self_sqrt hm.le
      have hcoup' : (S.p : ℝ) * (j : ℝ) + x
          = Real.sqrt S.m * ((S.p : ℝ) * (k₀ : ℝ) + y) := hcoup
      have hpow : Real.sqrt S.m ^ (2 * t + 1) = (S.m : ℝ) ^ t * Real.sqrt S.m := by
        rw [pow_succ, pow_mul, Real.sq_sqrt hm.le]
      rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt hm), hpow, hcoup']
      push_cast
      linear_combination (((S.p : ℝ) * (k₀ : ℝ) + y) * (S.m : ℝ) ^ t) * hs2
    rw [hval]
    exact dvd_floor_add_digitReal_mul_pow hdY (dvd_mul_right S.p k₀) hydvd t hi₀ hsmall
  refine ⟨((S.p : ℝ) * (j : ℝ) + x) / (S.m : ℝ), hξpos, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht1 : 1 ≤ t := by omega
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have hn2 : n = 2 * (u + 1) := by omega
    rw [hn2]
    exact heven u
  · obtain ⟨t, rfl⟩ := ho
    exact hodd t

/-- **The free case `e ≤ m - 2`** (paper Remark 2.2): every digit is already canonical, so
the translate alone gives the witness. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem dvd_floor_of_e_le (S : Slice) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hm.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  refine dvd_floor_of_hygiene S hj h0 h1 (fun N => ⟨N, le_refl N, ?_⟩)
    (fun N => ⟨N, le_refl N, ?_⟩)
  · exact le_trans (dA_mem hw0 hw1 N).2.2 he
  · have := (dB_mem hw0 hw1 N).2.1
    omega

/-! ## The modulus `p = 2`: membership in `𝒵` -/

/-- At `p = 2` divisibility is parity, so a witness of the reduction places `√m` in `𝒵`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem mem_MahlerZ_of_dvd (S : Slice) (hp : S.p = 2)
    (h : ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋) :
    Real.sqrt S.m ∈ MahlerZ := by
  obtain ⟨ξ, hξ, hdvd⟩ := h
  refine ⟨S.one_lt_sq, ξ, ne_of_gt hξ, fun n hn => ?_⟩
  have := hdvd n hn
  rw [hp] at this
  exact even_iff_two_dvd.mpr this

/-- **The reduction at `p = 2`** (paper Proposition 3.2): with tail hygiene the greedy's
streams give `√m ∈ 𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem mem_MahlerZ_of_hygiene (S : Slice) (hp : S.p = 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_hygiene S hj h0 h1 hA hB)

/-- **The free case at `p = 2`.**  `e ≤ m - 2` — for `p = 2` exactly the even bases — needs
no hygiene, so the translate alone gives `√m ∈ 𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_slice"]
theorem mem_MahlerZ_of_e_le (S : Slice) (hp : S.p = 2) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ}
    (hj : 1 ≤ j) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ :=
  mem_MahlerZ_of_dvd S hp (dvd_floor_of_e_le S he hj h0 h1)

end Slice

end SZ
