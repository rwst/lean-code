/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Cantor
import BB61.Splitting
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Proposition 14: every `{0,1}`-word is admissible for the `α`-shift

Formal companion of `note-1061-M1.html` §5, Proposition 14 — the *licence* for citing the
`θ`-shift literature ([BM86], [BM85]) at `C(α)` at all.  It is the third of the three jobs
the hypothesis `α > 2` does in Problem 10.61 (use **U3** of the note's §5 table; U1 is
`gap_pos_iff` and U2 is the entropy deficit).

> **Proposition 14.** For `α > 2` every sequence in `{0,1}^ℕ` is admissible for the
> `α`-shift, i.e. `{0,1}^ℕ ⊆ S_α`.  Hence `C(α)` — up to the `(α-1)` normalisation — is the
> image of a subshift of the `α`-shift.

## What is proved here, and how it differs from the note

The note argues through **Parry's criterion**: `a` is admissible iff `σᵏ a <_lex d*(1,α)`
for every `k`, and the comparison is decided at the first letter because `d*(1,α)` begins
with `⌊α⌋ ≥ 2` while every letter of a `{0,1}`-word is `0` or `1`.  That route needs the
quasi-greedy expansion `d*(1,α)` and Parry's theorem, neither of which is in Mathlib.

Here the **definition** of admissibility is used directly, which is both cheaper and
stronger: `IsAdmissible α a` means `a` *is* the greedy Rényi–Parry `α`-expansion of a point
of `[0,1)`, and `greedyExp_boolVal` exhibits that point explicitly — it is the value of the
word itself,
`boolVal α ε = ∑_{k≥0} ε_k α^{-(k+1)} = π(ε)/(α-1)`.
So one does not merely learn that `{0,1}`-words are admissible; one learns *which* points
they expand, and the `(α-1)` of the note's "up to the normalisation" becomes an identity
(`piVal_eq_boolVal`).

**Where `α > 2` enters** is a single inequality: the greedy algorithm reproduces the word
iff every tail value stays below `1`, and `sup_ε boolVal α ε = boolVal α 1^∞ = (α-1)⁻¹`,
which is `< 1` **iff** `α > 2` (`boolVal_const_true_lt_one_iff`).  At `α = 2` the word
`1^∞` has value `1`, leaves `[0,1)`, and the coding stops being a restriction of the
`α`-expansion coding — exactly the note's "what breaks at `α ≤ 2`" for U3.

## Main results

* `greedyExp_boolVal` — the greedy expansion of `boolVal α ε` is `ε` itself, for `α > 2`;
* `isAdmissible_bitZ` — **Proposition 14**: every `{0,1}`-word is admissible;
* `range_bitZ_subset_closure_admissible` — the note's inclusion `{0,1}^ℕ ⊆ S_α` verbatim,
  `S_α` being the closure of the admissible set;
* `greedy_tsum` — the converse direction: a point of `[0,1)` is the sum of its own greedy
  expansion, so `greedyExp α` is injective there (`injOn_greedyExp`);
* `cantorSet_eq_image_boolCoded` — **the "hence"**: `C(α) = (α-1)·B(α)`, where `B(α)` is
  *exactly* the set of points of `[0,1)` whose `α`-expansion is a `{0,1}`-word.  The
  inclusion `⊆` is Proposition 14; the reverse is `greedy_tsum`.

`greedyDigit_one`, `two_le_floor` and `bitZ_lt_floor` record the note's own first-letter
count (`d(1,α)` begins with `⌊α⌋ ≥ 2`, every letter of a `{0,1}`-word is `< 2`), including
the integer case `d*(1,α) = (⌊α⌋-1)^∞` of the note's parenthesis
(`two_le_floor_sub_one`).  They are not used by the proof above; they are what a reader
comparing this file with the note's argument will look for.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, CUP 2012,
  Problem 10.61.
* `note-1061-M1.html` §5 (uses of `α > 2`; Proposition 14) and §8 (the concordance table,
  where Proposition 14 is "ours (trivially) — but it is the licence for every [BM86]
  citation").  Numerical check: `BB61/m1_verify.py`, row **P14**.
* A. Rényi, *Representations for real numbers and their ergodic properties*, Acta Math.
  Acad. Sci. Hungar. 8 (1957); W. Parry, *On the β-expansions of real numbers*, ibid. 11
  (1960) — the greedy algorithm and the admissibility criterion.
-/

namespace BB61

open QuadSetup (bitZ bitZ_cast shift_zero)

variable {α : ℝ}

/-! ## The Rényi–Parry `β`-transformation and the greedy expansion -/

/-- The Rényi–Parry transformation `T_α x = α x mod 1`, on all of `ℝ`; its values always
lie in `[0,1)`, so no domain hypothesis is ever needed. -/
noncomputable def betaT (α x : ℝ) : ℝ := Int.fract (α * x)

/-- The greedy digit `⌊α x⌋` — the first letter of the `α`-expansion of `x`. -/
noncomputable def greedyDigit (α x : ℝ) : ℤ := ⌊α * x⌋

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_nonneg (α x : ℝ) : 0 ≤ betaT α x := Int.fract_nonneg _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_lt_one (α x : ℝ) : betaT α x < 1 := Int.fract_lt_one _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_mem_Ico (α x : ℝ) : betaT α x ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨betaT_nonneg α x, betaT_lt_one α x⟩

/-- The defining identity of the algorithm: `α x = a(x) + T_α x`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyDigit_add_betaT (α x : ℝ) : (greedyDigit α x : ℝ) + betaT α x = α * x :=
  Int.floor_add_fract _

/-- The greedy (Rényi–Parry) `α`-expansion of `x`, zero-indexed: `greedyExp α x k` is the
note's digit `a_{k+1} = ⌊α T_α^k x⌋`. -/
noncomputable def greedyExp (α x : ℝ) (k : ℕ) : ℤ := greedyDigit α ((betaT α)^[k] x)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyExp_zero (α x : ℝ) : greedyExp α x 0 = greedyDigit α x := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyExp_succ (α x : ℝ) (k : ℕ) :
    greedyExp α x (k + 1) = greedyExp α (betaT α x) k := by
  unfold greedyExp
  rw [Function.iterate_succ_apply]

/-- **Admissibility**, in the sense of Rényi and Parry: `a` is admissible for the
`α`-shift if it is the greedy `α`-expansion of a point of `[0,1)`.  The note's `S_α` is the
*closure* of this set; Proposition 14 lands inside the set itself, which is the stronger
statement (see `range_bitZ_subset_closure_admissible`). -/
def IsAdmissible (α : ℝ) (a : ℕ → ℤ) : Prop := ∃ x ∈ Set.Ico (0 : ℝ) 1, greedyExp α x = a

/-! ## The `{0,1}`-coding, un-normalised -/

/-- The un-normalised coding `boolVal α ε = ∑_{k≥0} ε_k α^{-(k+1)}`, of which `piVal` is
the `(α-1)`-normalised version.  This is the note's "`(α-1)` normalisation", made an
identity by `piVal_eq_boolVal`. -/
noncomputable def boolVal (α : ℝ) (ε : ℕ → Bool) : ℝ := ∑' k : ℕ, dR ε k * (α⁻¹) ^ (k + 1)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_eq_boolVal (α : ℝ) (ε : ℕ → Bool) : piVal α ε = (α - 1) * boolVal α ε := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_nonneg (hα : 1 < α) (ε : ℕ → Bool) : 0 ≤ boolVal α ε :=
  tsum_nonneg fun k =>
    mul_nonneg (dR_nonneg ε k) (pow_nonneg (inv_pos_of_one_lt hα).le _)

/-- `boolVal α ε ≤ (α-1)⁻¹`, the value of `1^∞`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_le_inv (hα : 1 < α) (ε : ℕ → Bool) : boolVal α ε ≤ (α - 1)⁻¹ := by
  have hpos : (0 : ℝ) < α - 1 := by linarith
  have h := piVal_le_one hα ε
  rw [piVal_eq_boolVal] at h
  rw [← one_div, le_div_iff₀ hpos]
  calc boolVal α ε * (α - 1) = (α - 1) * boolVal α ε := mul_comm _ _
    _ ≤ 1 := h

/-- `boolVal α 1^∞ = (α-1)⁻¹`: the supremum of the coding is attained at the all-ones word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_const_true (hα : 1 < α) : boolVal α (fun _ => true) = (α - 1)⁻¹ := by
  have : ∀ k : ℕ, dR (fun _ => true) k * (α⁻¹ : ℝ) ^ (k + 1) = (α⁻¹) ^ (k + 1) := by
    intro k; simp [dR]
  rw [boolVal]
  simp only [this]
  exact tsum_inv_pow_succ hα

/-- **Where `α > 2` enters Proposition 14**, and nowhere else: the coding stays inside the
domain `[0,1)` of the `α`-expansion **iff** `α > 2`.  At `α = 2` the word `1^∞` has value
`1` and leaves it. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_const_true_lt_one_iff (hα : 1 < α) :
    boolVal α (fun _ => true) < 1 ↔ 2 < α := by
  rw [boolVal_const_true hα, inv_lt_one₀ (by linarith : (0 : ℝ) < α - 1)]
  constructor <;> intro h <;> linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_lt_one (h2 : 2 < α) (ε : ℕ → Bool) : boolVal α ε < 1 := by
  have hα : (1 : ℝ) < α := by linarith
  refine lt_of_le_of_lt (boolVal_le_inv hα ε) ?_
  rw [inv_lt_one₀ (by linarith : (0 : ℝ) < α - 1)]
  linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolVal_mem_Ico (h2 : 2 < α) (ε : ℕ → Bool) : boolVal α ε ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨boolVal_nonneg (by linarith) ε, boolVal_lt_one h2 ε⟩

/-- The one-step recursion of the coding, `α · boolVal ε = ε₀ + boolVal (σ ε)`: this is
`alpha_mul_tPart` (M1 Lemma 1(v)) with the `(α-1)` divided out. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_boolVal (hα : 1 < α) (ε : ℕ → Bool) :
    α * boolVal α ε = dR ε 0 + boolVal α (shift ε 1) := by
  refine mul_left_cancel₀ (sub_ne_zero.mpr hα.ne') ?_
  calc (α - 1) * (α * boolVal α ε) = α * piVal α ε := by rw [piVal_eq_boolVal]; ring
    _ = (α - 1) * dR ε 0 + piVal α (shift ε 1) := by
        have h := alpha_mul_tPart hα ε 0
        rwa [tPart, tPart, shift_zero, Nat.zero_add] at h
    _ = (α - 1) * (dR ε 0 + boolVal α (shift ε 1)) := by rw [piVal_eq_boolVal]; ring

/-! ## The coding is the greedy algorithm -/

/-- The first greedy digit of `boolVal α ε` is `ε₀`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyDigit_boolVal (h2 : 2 < α) (ε : ℕ → Bool) :
    greedyDigit α (boolVal α ε) = bitZ ε 0 := by
  have hα : (1 : ℝ) < α := by linarith
  have hfr : ⌊boolVal α (shift ε 1)⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr (boolVal_mem_Ico h2 _)
  unfold greedyDigit
  rw [alpha_mul_boolVal hα ε, ← bitZ_cast ε 0, Int.floor_intCast_add, hfr, add_zero]

/-- One step of the greedy algorithm on `boolVal α ε` is one shift of the word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_boolVal (h2 : 2 < α) (ε : ℕ → Bool) :
    betaT α (boolVal α ε) = boolVal α (shift ε 1) := by
  have hα : (1 : ℝ) < α := by linarith
  unfold betaT
  rw [alpha_mul_boolVal hα ε, ← bitZ_cast ε 0, Int.fract_intCast_add]
  exact Int.fract_eq_self.mpr (boolVal_mem_Ico h2 _)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shift_shift (ε : ℕ → Bool) (m n : ℕ) : shift (shift ε m) n = shift ε (m + n) := by
  funext k
  simp only [shift]
  congr 1
  omega

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_iterate_boolVal (h2 : 2 < α) (ε : ℕ → Bool) (n : ℕ) :
    (betaT α)^[n] (boolVal α ε) = boolVal α (shift ε n) := by
  induction n generalizing ε with
  | zero => rw [Function.iterate_zero_apply, shift_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply, betaT_boolVal h2, ih, shift_shift, Nat.add_comm]

/-- **The coding is greedy**: for `α > 2` the Rényi–Parry `α`-expansion of the value of a
`{0,1}`-word is that word.  This is Proposition 14 with the witness made explicit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyExp_boolVal (h2 : 2 < α) (ε : ℕ → Bool) :
    greedyExp α (boolVal α ε) = bitZ ε := by
  funext k
  rw [greedyExp, betaT_iterate_boolVal h2, greedyDigit_boolVal h2]
  simp [bitZ, shift]

/-! ## Proposition 14 -/

/-- **M1 Proposition 14** (admissibility).  For `α > 2` every `{0,1}`-word is admissible for
the `α`-shift: it is the greedy Rényi–Parry `α`-expansion of the point
`boolVal α ε = π(ε)/(α-1) ∈ [0,1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isAdmissible_bitZ (h2 : 2 < α) (ε : ℕ → Bool) : IsAdmissible α (bitZ ε) :=
  ⟨boolVal α ε, boolVal_mem_Ico h2 ε, greedyExp_boolVal h2 ε⟩

/-- **M1 Proposition 14** as a set inclusion: `{0,1}^ℕ` sits inside the admissible
sequences. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem range_bitZ_subset_admissible (h2 : 2 < α) :
    Set.range bitZ ⊆ {a : ℕ → ℤ | IsAdmissible α a} := by
  rintro a ⟨ε, rfl⟩
  exact isAdmissible_bitZ h2 ε

/-- **M1 Proposition 14** verbatim: `{0,1}^ℕ ⊆ S_α`, where `S_α` is the closure of the set
of Rényi–Parry `α`-expansions. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem range_bitZ_subset_closure_admissible (h2 : 2 < α) :
    Set.range bitZ ⊆ closure {a : ℕ → ℤ | IsAdmissible α a} :=
  (range_bitZ_subset_admissible h2).trans subset_closure

/-! ## The note's own first-letter count

Not used above; recorded because it is the argument the note gives.  Parry's criterion
compares `σᵏ a` with the quasi-greedy expansion `d*(1,α)` lexicographically, and the
comparison is decided at the first letter: `d(1,α)` begins with `⌊α⌋ ≥ 2` (and in the
integer case `d*(1,α) = (⌊α⌋-1)^∞` with `⌊α⌋-1 ≥ 2`), while every letter of a `{0,1}`-word
is `0` or `1`. -/

/-- `d(1,α)` begins with `⌊α⌋`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyDigit_one (α : ℝ) : greedyDigit α 1 = ⌊α⌋ := by
  rw [greedyDigit, mul_one]

/-- The note's form of use **U3** of the hypothesis: `⌊α⌋ ≥ 2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_le_floor (h2 : 2 < α) : 2 ≤ ⌊α⌋ :=
  Int.le_floor.mpr (by push_cast; linarith)

/-- The integer case of the note's parenthesis: if `α > 2` is an integer then `d*(1,α)`
is `(⌊α⌋-1)^∞`, whose letter is still `≥ 2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_le_floor_sub_one (h2 : 2 < α) (hint : ((⌊α⌋ : ℤ) : ℝ) = α) : 2 ≤ ⌊α⌋ - 1 := by
  have : (2 : ℝ) < ((⌊α⌋ : ℤ) : ℝ) := by rw [hint]; exact h2
  have h3 : (2 : ℤ) < ⌊α⌋ := by exact_mod_cast this
  omega

/-- Every letter of a `{0,1}`-word is below the first letter of `d*(1,α)`, so the
lexicographic comparison in Parry's criterion is decided at the first letter — for the word
and for every one of its shifts, `{0,1}^ℕ` being shift-invariant. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bitZ_lt_floor (h2 : 2 < α) (ε : ℕ → Bool) (n : ℕ) : bitZ ε n < ⌊α⌋ := by
  have h := two_le_floor h2
  simp only [bitZ]
  split <;> omega

/-- `{0,1}^ℕ` is shift-invariant: the shift of a `{0,1}`-word is a `{0,1}`-word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bitZ_shift (ε : ℕ → Bool) (n : ℕ) : bitZ (shift ε n) = fun k => bitZ ε (n + k) := rfl

/-! ## The converse: a point is the sum of its own expansion

Everything above is the inclusion `{0,1}^ℕ ⊆` admissible.  What makes the note's "hence
`C(α)` is the image of a subshift" an *equality* rather than an inclusion is the reverse
direction: on `[0,1)` the greedy algorithm loses nothing, so a point whose expansion happens
to be a `{0,1}`-word is the value of that word.  This part needs no hypothesis beyond
`α > 1`. -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem betaT_iterate_mem_Ico (α : ℝ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    (betaT α)^[n] x ∈ Set.Ico (0 : ℝ) 1 := by
  cases n with
  | zero => simpa using hx
  | succ n =>
      rw [Function.iterate_succ_apply']
      exact betaT_mem_Ico α _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyExp_nonneg (hα : 1 < α) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    0 ≤ greedyExp α x k :=
  Int.le_floor.mpr <| by
    push_cast
    exact mul_nonneg (by linarith) (betaT_iterate_mem_Ico α hx k).1

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedyExp_le (hα : 1 < α) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (k : ℕ) :
    (greedyExp α x k : ℝ) ≤ α := by
  refine le_trans (Int.floor_le _) ?_
  have h1 : α * (betaT α)^[k] x ≤ α * 1 :=
    mul_le_mul_of_nonneg_left (betaT_iterate_mem_Ico α hx k).2.le (by linarith)
  rwa [mul_one] at h1

/-- The greedy algorithm run for `n` steps: `x = ∑_{k<n} a_k α^{-(k+1)} + α^{-n} T_α^n x`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedy_partial (hα : 1 < α) (x : ℝ) (n : ℕ) :
    x = (∑ k ∈ Finset.range n, (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1))
        + (α⁻¹) ^ n * (betaT α)^[n] x := by
  have hne : (α : ℝ) ≠ 0 := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
      have hkey : (greedyExp α x n : ℝ) + (betaT α)^[n + 1] x = α * (betaT α)^[n] x := by
        rw [Function.iterate_succ_apply']
        exact greedyDigit_add_betaT α _
      have hstep : (α⁻¹ : ℝ) ^ n * (betaT α)^[n] x
          = (greedyExp α x n : ℝ) * (α⁻¹) ^ (n + 1)
            + (α⁻¹) ^ (n + 1) * (betaT α)^[n + 1] x := by
        have hinv : (α⁻¹ : ℝ) * α = 1 := inv_mul_cancel₀ hne
        calc (α⁻¹ : ℝ) ^ n * (betaT α)^[n] x
            = (α⁻¹) ^ n * (α⁻¹ * α) * (betaT α)^[n] x := by rw [hinv, mul_one]
          _ = (α⁻¹) ^ (n + 1) * (α * (betaT α)^[n] x) := by rw [pow_succ]; ring
          _ = (α⁻¹) ^ (n + 1) * ((greedyExp α x n : ℝ) + (betaT α)^[n + 1] x) := by rw [hkey]
          _ = (greedyExp α x n : ℝ) * (α⁻¹) ^ (n + 1)
                + (α⁻¹) ^ (n + 1) * (betaT α)^[n + 1] x := by ring
      rw [Finset.sum_range_succ, add_assoc, ← hstep]
      exact ih

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_greedyExp (hα : 1 < α) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    Summable fun k : ℕ => (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1) := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have hne : (α : ℝ) ≠ 0 := by linarith
  refine summable_of_le_geom hr0 (inv_lt_one_of_one_lt hα) (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (by exact_mod_cast greedyExp_nonneg hα hx k) (pow_nonneg hr0 _)
  · calc (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1) ≤ α * (α⁻¹) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (greedyExp_le hα hx k) (pow_nonneg hr0 _)
      _ = (α⁻¹) ^ k := by rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **A point of `[0,1)` is the sum of its own `α`-expansion.**  The remainder
`α^{-n} T_α^n x` is squeezed between `0` and `α^{-n}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem greedy_tsum (hα : 1 < α) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    x = ∑' k : ℕ, (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1) := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have h1 := (summable_greedyExp hα hx).hasSum.tendsto_sum_nat
  have hrem : Filter.Tendsto (fun n : ℕ => (α⁻¹ : ℝ) ^ n * (betaT α)^[n] x)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => mul_nonneg (pow_nonneg hr0 _)
      (betaT_iterate_mem_Ico α hx n).1) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 (inv_lt_one_of_one_lt hα))
    calc (α⁻¹ : ℝ) ^ n * (betaT α)^[n] x ≤ (α⁻¹) ^ n * 1 :=
          mul_le_mul_of_nonneg_left (betaT_iterate_mem_Ico α hx n).2.le (pow_nonneg hr0 _)
      _ = (α⁻¹) ^ n := mul_one _
  have h2 : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1)) Filter.atTop (nhds x) := by
    have heq : ∀ n : ℕ, (∑ k ∈ Finset.range n, (greedyExp α x k : ℝ) * (α⁻¹) ^ (k + 1))
        = x - (α⁻¹) ^ n * (betaT α)^[n] x := fun n => by
      have := greedy_partial hα x n; linarith
    simp only [heq]
    simpa using (tendsto_const_nhds (x := x) (f := Filter.atTop (α := ℕ))).sub hrem
  exact tendsto_nhds_unique h2 h1

/-- The `α`-expansion determines the point: `greedyExp α` is injective on `[0,1)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem injOn_greedyExp (hα : 1 < α) : Set.InjOn (greedyExp α) (Set.Ico (0 : ℝ) 1) := by
  intro x hx y hy h
  rw [greedy_tsum hα hx, greedy_tsum hα hy, h]

/-- If the `α`-expansion of `x ∈ [0,1)` is a `{0,1}`-word, then `x` is that word's value. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eq_boolVal_of_greedyExp (hα : 1 < α) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    {ε : ℕ → Bool} (h : greedyExp α x = bitZ ε) : x = boolVal α ε := by
  rw [greedy_tsum hα hx, boolVal]
  refine tsum_congr fun k => ?_
  rw [h, bitZ_cast]

/-! ## `C(α)` is the `α`-shift picture of a subshift -/

/-- `B(α)`: the points of `[0,1)` whose Rényi–Parry `α`-expansion is a `{0,1}`-word. -/
def boolCoded (α : ℝ) : Set ℝ :=
  {x ∈ Set.Ico (0 : ℝ) 1 | ∃ ε : ℕ → Bool, greedyExp α x = bitZ ε}

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem boolCoded_eq_range (h2 : 2 < α) : boolCoded α = Set.range (boolVal α) := by
  have hα : (1 : ℝ) < α := by linarith
  ext x
  constructor
  · rintro ⟨hx, ε, hε⟩
    exact ⟨ε, (eq_boolVal_of_greedyExp hα hx hε).symm⟩
  · rintro ⟨ε, rfl⟩
    exact ⟨boolVal_mem_Ico h2 ε, ε, greedyExp_boolVal h2 ε⟩

/-- **The "hence" of Proposition 14**: `C(α) = (α-1)·B(α)` — the Cantor set is, up to the
`(α-1)` normalisation, *exactly* the set of points of `[0,1)` whose Rényi–Parry
`α`-expansion is a `{0,1}`-word, i.e. the image of a subshift of the `α`-shift.  The
inclusion `⊇` is Proposition 14, the inclusion `⊆` is `greedy_tsum`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_eq_image_boolCoded (h2 : 2 < α) :
    cantorSet α = (fun x => (α - 1) * x) '' boolCoded α := by
  rw [boolCoded_eq_range h2, cantorSet, ← Set.range_comp]
  rfl

end BB61
