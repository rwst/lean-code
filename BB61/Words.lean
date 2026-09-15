/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Factor
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The staged word: combinatorics of block concatenation

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Proposition 8(ii) — *saturation*: every `σ`-invariant measure of the full `2`-shift has a
generic point, so **every** invariant measure is realized by a point of `C(α)`, not only the
ergodic ones.

This file carries the purely combinatorial half of the construction: a digit word built by
concatenating blocks, and the statement that deep inside a block the two-sided word
`padZ (staged word)` agrees with the block's source on a long central window.  No measure
theory, no `QuadSetup`.

## The construction

The data is a `StageData`: for each *stage* `j` an atom length `NN j`, an atom count `AA j`,
and a sequence of sources `om j : ℕ → {0,1}^ℤ`.  Stage `j` occupies the positions
`[T j, T (j+1))` with `T (j+1) = T j + AA j * NN j`, and inside it the digits are read off the
sources in blocks of length `NN j`:

`word (T j + NN j * l + r) = om j l (r+1)`,  `l < AA j`, `r < NN j`.

The offset `r+1` is the one the padding of `BB61/Factor.lean` wants: `padZ ε` puts `ε 0` at
coordinate `1`, so the digit at distance `r` into an atom must be coordinate `r+1` of the
source, and then time `T j + NN j * l + r` of the padded word sees the same central window as
time `r` of the source.  That is `agree_shift`, and `abs_fRaw_sub_le_agree` is what
`BB61/Factor.lean`'s modulus makes of it.

The window costs a boundary: the agreement needs `R + 1 ≤ r` (the source's past must already
be inside the atom) and `r + R ≤ NN j` (its future too), so `2R` of the `NN j` positions of
each atom are lost.  That is the only error the construction pays per atom.
-/

namespace BB61

/-- The combinatorial data of a staged word: atom length `NN j` and atom count `AA j` at
stage `j`, and the sources `om j l` the atoms are read off. -/
structure StageData where
  /-- the length of an atom of stage `j` -/
  NN : ℕ → ℕ
  /-- the number of atoms of stage `j` -/
  AA : ℕ → ℕ
  /-- `om j l` is the two-sided word the `l`-th atom of stage `j` is copied from -/
  om : ℕ → ℕ → Shift
  /-- atoms are nonempty -/
  NN_pos : ∀ j, 0 < NN j
  /-- stages are nonempty -/
  AA_pos : ∀ j, 0 < AA j

namespace StageData

variable (S : StageData)

/-- The number of digits stage `j` occupies. -/
def stgLen (j : ℕ) : ℕ := S.AA j * S.NN j

/-- The first position of stage `j`. -/
def T (S : StageData) : ℕ → ℕ
  | 0 => 0
  | j + 1 => S.T j + S.stgLen j

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem stgLen_pos (j : ℕ) : 0 < S.stgLen j := Nat.mul_pos (S.AA_pos j) (S.NN_pos j)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_zero : S.T 0 = 0 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_succ (j : ℕ) : S.T (j + 1) = S.T j + S.stgLen j := by rw [T]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_lt_T_succ (j : ℕ) : S.T j < S.T (j + 1) := by
  rw [T_succ]; exact Nat.lt_add_of_pos_right (S.stgLen_pos j)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_strictMono : StrictMono S.T := strictMono_nat_of_lt_succ S.T_lt_T_succ

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_mono : Monotone S.T := S.T_strictMono.monotone

/-- Stages advance by at least one digit, so `T` outruns the index. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_T (j : ℕ) : j ≤ S.T j := S.T_strictMono.le_apply

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_stage (n : ℕ) : ∃ j, n < S.T (j + 1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (S.le_T (n + 1))⟩

/-- The stage a position belongs to. -/
noncomputable def stg (n : ℕ) : ℕ := Nat.find (S.exists_stage n)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_T_stg_succ (n : ℕ) : n < S.T (S.stg n + 1) := Nat.find_spec (S.exists_stage n)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem T_stg_le (n : ℕ) : S.T (S.stg n) ≤ n := by
  unfold stg
  rcases Nat.eq_zero_or_pos (Nat.find (S.exists_stage n)) with h | h
  · rw [h, T_zero]; exact Nat.zero_le n
  · set k := Nat.find (S.exists_stage n) - 1 with hkdef
    have hk : Nat.find (S.exists_stage n) = k + 1 := by omega
    have hmin := Nat.find_min (S.exists_stage n) (m := k) (by omega)
    rw [hk]
    omega

/-- The stage is characterised by the interval it indexes. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem stg_eq {n j : ℕ} (h1 : S.T j ≤ n) (h2 : n < S.T (j + 1)) : S.stg n = j := by
  unfold stg
  refine Nat.find_eq_iff _ |>.mpr ⟨h2, fun i hi => ?_⟩
  have : S.T (i + 1) ≤ S.T j := S.T_mono (by omega)
  omega

/-- The stages tile the line. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sum_stgLen (J : ℕ) : ∑ j ∈ Finset.range J, S.stgLen j = S.T J := by
  induction J with
  | zero => simp [T_zero]
  | succ J ih => rw [Finset.sum_range_succ, ih, T_succ]

/-- **The staged word.**  Stage `j` fills `[T j, T (j+1))` with `AA j` atoms of length `NN j`,
the `l`-th copied off the source `om j l`. -/
noncomputable def word (n : ℕ) : Bool :=
  S.om (S.stg n) ((n - S.T (S.stg n)) / S.NN (S.stg n))
    ((((n - S.T (S.stg n)) % S.NN (S.stg n) : ℕ) : ℤ) + 1)

/-- The digit at distance `r` into the `l`-th atom of stage `j`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem word_eq {j l r : ℕ} (hl : l < S.AA j) (hr : r < S.NN j) :
    S.word (S.T j + S.NN j * l + r) = S.om j l ((r : ℤ) + 1) := by
  have hlt : S.NN j * l + r < S.stgLen j := by
    have : S.NN j * l + r < S.NN j * l + S.NN j := by omega
    have h2 : S.NN j * l + S.NN j = S.NN j * (l + 1) := by ring
    calc S.NN j * l + r < S.NN j * (l + 1) := by omega
    _ ≤ S.NN j * S.AA j := Nat.mul_le_mul_left _ (by omega)
    _ = S.stgLen j := by rw [stgLen]; ring
  have hstg : S.stg (S.T j + S.NN j * l + r) = j := by
    refine S.stg_eq (by omega) ?_
    rw [T_succ]
    omega
  have hsub : S.T j + S.NN j * l + r - S.T j = S.NN j * l + r := by omega
  rw [word, hstg, hsub, Nat.mul_add_div (S.NN_pos j), Nat.mul_add_mod,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, Nat.add_zero]

/-! ## The window agreement -/

/-- **Deep inside an atom the staged word is the source.**  If the position `r` inside the
`l`-th atom of stage `j` is at distance more than `R` from both ends, then the padded staged
word at time `T j + NN j * l + r` and the source at time `r` agree on the whole central
window `[-R, R]`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem agree_shift {j l r R : ℕ} (hl : l < S.AA j) (hr1 : R + 1 ≤ r)
    (hr2 : r + R ≤ S.NN j) {k : ℤ} (hk : |k| ≤ (R : ℤ)) :
    shiftZ^[S.T j + S.NN j * l + r] (padZ S.word) k = shiftZ^[r] (S.om j l) k := by
  obtain ⟨hk1, hk2⟩ := abs_le.mp hk
  set r' : ℕ := (r + k - 1).toNat with hr'def
  have hr'cast : (r' : ℤ) = (r : ℤ) + k - 1 := by rw [hr'def]; omega
  have hr'lt : r' < S.NN j := by omega
  have hK : (1 : ℤ) ≤ k + ((S.T j + S.NN j * l + r : ℕ) : ℤ) := by
    rw [Nat.cast_add]; omega
  have hidx : (k + ((S.T j + S.NN j * l + r : ℕ) : ℤ) - 1).toNat = S.T j + S.NN j * l + r' := by
    rw [Nat.cast_add]; omega
  rw [shiftZ_iterate, shiftZ_iterate]
  simp only [padZ]
  split_ifs
  rw [hidx, S.word_eq hl hr'lt]
  congr 1
  omega

end StageData

namespace QuadSetup

variable (P : QuadSetup) (S : StageData)

/-- **The atom estimate.**  Deep inside an atom, the factor map of the staged word and of the
source differ by at most `BB61/Factor.lean`'s window modulus. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_fRaw_sub_le_agree {j l r R : ℕ} (hl : l < S.AA j) (hr1 : R + 1 ≤ r)
    (hr2 : r + R ≤ S.NN j) :
    |P.fRaw (shiftZ^[S.T j + S.NN j * l + r] (padZ S.word)) - P.fRaw (shiftZ^[r] (S.om j l))|
      ≤ (P.α⁻¹) ^ R + (1 + |P.β|) * |P.β| ^ (R + 1) / (1 - |P.β|) :=
  P.abs_fRaw_sub_le_of_agree fun _ hk => S.agree_shift hl hr1 hr2 hk

end QuadSetup

end BB61
