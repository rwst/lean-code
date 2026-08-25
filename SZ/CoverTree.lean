/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The witness set for `√3` has the cardinality of the continuum

`SZ/CoverGame.lean` runs *one* cover greedy, pinned by the selection rule
*prefer `a = 0`, then `b = 2`*, and `SZ/SqrtThree.lean` turns its output into the single
witness `witXi`.  This file runs *all* admissible plays of the same game and shows that
uncountably many of them give distinct witnesses.  It is Theorem 9.1 of
`paper-dubD1O5.tex`:

> The set `W = {ξ > 0 : ⌊ξ √3ⁿ⌋ ∈ 2ℤ for all n ≥ 1}` has cardinality `2^ℵ₀`, and already
> `W ∩ [4/3, 5/3]` does.  Hence all but countably many witnesses for `√3` are
> transcendental; in particular [Dub06EO] Problem 3 has a transcendental witness.

## Why the game branches

Admissibility of an offset `c = a + b√3` at a state `w` is `0 ≤ w - c ≤ U`, `U = 1 + √3`,
so the four offsets `0, 2, 2√3, 2+2√3` are admissible on the four intervals `[c, c+U]`.
Consecutive intervals overlap and non-consecutive ones do not, so `w` has **two** choices
exactly on

`O = [2, 1+√3] ∪ [2√3, 3+√3] ∪ [2+2√3, 1+3√3]`,

and there the two choices always differ in their `a`-part (`InO`, `branchDigit`).  Off `O`
the play is forced, and the forced dynamics cannot run forever: its four zones
`Z₁ = [0,2)`, `Z₂ = (U, 2√3)`, `Z₃ = (3+√3, 2+2√3)`, `Z₄ = (1+3√3, 3U]` satisfy
`Z₂ → Z₂`, `Z₃ → Z₃`, `Z₁ ↛ Z₄`, `Z₄ ↛ Z₁`, so an orbit avoiding `O` is eventually
confined to one zone, hence sits at that zone's fixed point (`eq_fixed_of_trapped`) — one
of `0`, `3`, `3√3`, `3+3√3`, all with `√3`-coordinate `≤ 3`, which the growth of the
state's `√3`-coordinate excludes.  That is `gExists_inO`.

## The tree

Hygiene (lemma L1: infinitely many `aᵢ = 0` and `bᵢ = 2`) is *not* automatic along an
arbitrary play — a play that always takes `a = 2` is admissible — so it is scheduled.  A
`Node` carries the state, two flags recording whether an `a = 0` and a `b = 2` have been
emitted since the last branching, and a counter of consumed bits; it follows the rule until
both flags are set and the state lies in `O`, and only then branches on the next bit of
`β : ℕ → Bool`.  Both waits are finite by `gExists_fst_eq_zero`, `gExists_snd_eq_two` and
`gExists_inO`, generalisations to an arbitrary start of `SZ/CoverGame.lean`'s
`exists_digitA_eq_zero`, `exists_digitB_eq_two`.

Distinct `β` consume their first differing bit at the same branching, where the two offsets
differ in `a`; so the `a`-streams differ, and `digitReal_injOn` separates the witnesses.
-/

namespace SZ

open Filter Topology

/-! ## `√3` numerics -/

private theorem t3_nonneg : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3

private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private theorem t3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h

/-! ## States, offsets, plays -/

/-- The real value `p + q√3` of a state `(p, q) ∈ ℤ[√3]`. -/
noncomputable def valS (s : ℤ × ℤ) : ℝ := (s.1 : ℝ) + (s.2 : ℝ) * Real.sqrt 3

/-- One move of the cover game: subtract the offset and rescale by `m = 3`. -/
def stepS (s d : ℤ × ℤ) : ℤ × ℤ := (3 * (s.1 - d.1), 3 * (s.2 - d.2))

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem valS_stepS (s d : ℤ × ℤ) : valS (stepS s d) = 3 * (valS s - valS d) := by
  simp only [valS, stepS]; push_cast; ring

/-- The alphabet: both coordinates of an offset lie in `Ev₃ = {0, 2}`. -/
def EvenDigit (d : ℤ × ℤ) : Prop := (d.1 = 0 ∨ d.1 = 2) ∧ (d.2 = 0 ∨ d.2 = 2)

/-- **Admissibility** of the offset `d` at the state `s`: the residual stays in `[0, U]`. -/
def Adm (s d : ℤ × ℤ) : Prop :=
  EvenDigit d ∧ 0 ≤ valS s - valS d ∧ valS s - valS d ≤ 1 + Real.sqrt 3

/-- The states of the play `d` started at `s₀`. -/
def runState (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => s₀
  | k + 1 => stepS (runState s₀ d k) (d k)

/-- A play is a sequence of offsets, each admissible at the state it is played from. -/
def IsRun (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) : Prop := ∀ k, Adm (runState s₀ d k) (d k)

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runState_succ (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) (k : ℕ) :
    runState s₀ d (k + 1) = stepS (runState s₀ d k) (d k) := rfl

/-- **The invariant** along any play: the state never leaves `[0, 3U]`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runVal_mem {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d)
    (h0 : 0 ≤ valS s₀) (h1 : valS s₀ ≤ 3 + 3 * Real.sqrt 3) (k : ℕ) :
    0 ≤ valS (runState s₀ d k) ∧ valS (runState s₀ d k) ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    obtain ⟨-, hlo, hhi⟩ := hrun k
    rw [runState_succ, valS_stepS]
    constructor <;> linarith

/-- **Growth of the `√3`-coordinate** along any play: only `bᵢ ≤ 2` is used, so this holds
for every admissible play and not merely for the rule's own orbit. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runState_snd_lower {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (k : ℕ) :
    3 ^ k * (s₀.2 - 3) + 3 ≤ (runState s₀ d k).2 := by
  induction k with
  | zero => simp [runState]
  | succ k ih =>
    have hb : (d k).2 ≤ 2 := by rcases (hrun k).1.2 with h | h <;> omega
    have h3 : (3 : ℤ) ^ (k + 1) * (s₀.2 - 3) = 3 * (3 ^ k * (s₀.2 - 3)) := by ring
    rw [runState_succ, stepS]
    simp only
    rw [h3]
    linarith

/-- Consequence: no state of a play started with `s₀.2 ≥ 4` is one of the trap fixed
points `0`, `3`, `3√3`, `3 + 3√3` — all of which have `√3`-coordinate at most `3`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runVal_ne {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) (hq : 4 ≤ s₀.2)
    (k : ℕ) {p q : ℤ} (hqle : q ≤ 3) :
    valS (runState s₀ d k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  intro h
  have hb := runState_snd_lower hrun k
  have h1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (runState s₀ d k).2 = q := (val_inj h).2
  have h4 : (1 : ℤ) ≤ s₀.2 - 3 := by omega
  have h5 : (1 : ℤ) * 1 ≤ 3 ^ k * (s₀.2 - 3) :=
    mul_le_mul h1 h4 zero_le_one (by positivity)
  omega

/-! ## The rule, started anywhere

`SZ/CoverGame.lean` fixes the start `(-12, 9)`.  The tree needs the same greedy from every
state it can reach, so it is re-run here with the start as a parameter; `gState (-12,9)` is
`coverState`. -/

/-- The greedy orbit of the selection rule `pick`, started at `s`. -/
noncomputable def gState (s : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => s
  | k + 1 => stepS (gState s k) (pick (valS (gState s k)))

/-- The offset the rule plays at step `k` from the start `s`. -/
noncomputable def gDigit (s : ℤ × ℤ) (k : ℕ) : ℤ × ℤ := pick (valS (gState s k))

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gState_succ (s : ℤ × ℤ) (k : ℕ) :
    gState s (k + 1) = stepS (gState s k) (gDigit s k) := rfl

/-- The rule is a semigroup: restarting at a reached state resumes the same orbit. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gState_add (s : ℤ × ℤ) (N k : ℕ) : gState s (N + k) = gState (gState s N) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, gState_succ, gState_succ]
    simp only [gDigit, ih]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem evenDigit_pick (w : ℝ) : EvenDigit (pick w) := ⟨pick_fst_mem w, pick_snd_mem w⟩

/-- The states a play may start from: inside the invariant window, and past the trap
fixed points in the `√3`-coordinate. -/
def GStart (s : ℤ × ℤ) : Prop :=
  0 ≤ valS s ∧ valS s ≤ 3 + 3 * Real.sqrt 3 ∧ 4 ≤ s.2

/-- **The invariant for the rule from an arbitrary start** (Cover Lemma, by induction). -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_mem {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    0 ≤ valS (gState s k) ∧ valS (gState s k) ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero => exact ⟨h.1, h.2.1⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := pick_residual_mem ih.1 ih.2
    have key : valS (gState s (k + 1)) = 3 * (valS (gState s k)
        - (((pick (valS (gState s k))).1 : ℝ)
            + ((pick (valS (gState s k))).2 : ℝ) * Real.sqrt 3)) := by
      rw [gState_succ, valS_stepS]; rfl
    rw [key]
    constructor <;> linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runState_gDigit (s : ℤ × ℤ) (k : ℕ) : runState s (gDigit s) k = gState s k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runState_succ, ih, gState_succ]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gIsRun {s : ℤ × ℤ} (h : GStart s) : IsRun s (gDigit s) := by
  intro k
  rw [runState_gDigit]
  obtain ⟨hlo, hhi⟩ := pick_residual_mem (gVal_mem h k).1 (gVal_mem h k).2
  exact ⟨evenDigit_pick _, hlo, hhi⟩

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gState_snd_lower {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    3 ^ k * (s.2 - 3) + 3 ≤ (gState s k).2 := by
  have := runState_snd_lower (gIsRun h) k
  rwa [runState_gDigit] at this

/-- A reached state is again a legitimate start: this is what lets the tree recurse. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gStart_gState {s : ℤ × ℤ} (h : GStart s) (N : ℕ) : GStart (gState s N) := by
  refine ⟨(gVal_mem h N).1, (gVal_mem h N).2, ?_⟩
  have hb := gState_snd_lower h N
  have h1 : (1 : ℤ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
  have h4 : (1 : ℤ) ≤ s.2 - 3 := by have := h.2.2; omega
  have h5 : (1 : ℤ) * 1 ≤ 3 ^ N * (s.2 - 3) := mul_le_mul h1 h4 zero_le_one (by positivity)
  omega

/-- No state of the rule's orbit is a trap fixed point. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_ne {s : ℤ × ℤ} (h : GStart s) (k : ℕ) {p q : ℤ} (hq : q ≤ 3) :
    valS (gState s k) ≠ (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  have := runVal_ne (gIsRun h) h.2.2 k (p := p) (q := q) hq
  rwa [runState_gDigit] at this

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_ne_zero {s : ℤ × ℤ} (h : GStart s) (k : ℕ) : valS (gState s k) ≠ 0 := by
  have := gVal_ne h k (p := 0) (q := 0) (by norm_num); simpa using this

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_pos {s : ℤ × ℤ} (h : GStart s) (k : ℕ) : 0 < valS (gState s k) :=
  lt_of_le_of_ne (gVal_mem h k).1 (Ne.symm (gVal_ne_zero h k))

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_ne_three {s : ℤ × ℤ} (h : GStart s) (k : ℕ) : valS (gState s k) ≠ 3 := by
  have := gVal_ne h k (p := 3) (q := 0) (by norm_num); simpa using this

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_ne_top {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    valS (gState s k) ≠ 3 + 3 * Real.sqrt 3 := by
  have := gVal_ne h k (p := 3) (q := 3) (by norm_num); simpa using this

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_ne_threeRoot {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    valS (gState s k) ≠ 3 * Real.sqrt 3 := by
  have := gVal_ne h k (p := 0) (q := 3) (by norm_num); simpa using this

/-- The value of the rule's state at step `k + 1`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gVal_succ (s : ℤ × ℤ) (k : ℕ) :
    valS (gState s (k + 1)) = 3 * (valS (gState s k)
      - (((pick (valS (gState s k))).1 : ℝ)
          + ((pick (valS (gState s k))).2 : ℝ) * Real.sqrt 3)) := by
  rw [gState_succ, valS_stepS]; rfl

/-- The fourth branch of `pick`, missing from `SZ/CoverGame.lean` because the greedy there
never needs it in this form. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem pick_eq_02 {w : ℝ} (h1 : 2 * Real.sqrt 3 ≤ w) (h2 : w ≤ 1 + 3 * Real.sqrt 3) :
    pick w = (0, 2) := by
  have hne : ¬ (w ≤ 1 + Real.sqrt 3) := by intro hx; linarith [t3_lb]
  unfold pick
  rw [ite_eq_right hne, ite_eq_right (not_lt.mpr h1), ite_eq_left h2]

/-! ## L1 for the rule from an arbitrary start -/

/-- **L1(b), from any start.**  Generalises `SZ.exists_digitB_eq_two`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gExists_snd_eq_two {s : ℤ × ℤ} (h : GStart s) : ∃ k, (gDigit s k).2 = 2 := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ k, valS (gState s k) < 2 * Real.sqrt 3 := by
    intro k
    by_contra hx
    exact hcon k ((pick_snd_eq_two_iff _).mpr (not_lt.mp hx))
  have claim1 : ∀ k, valS (gState s k) ≤ 1 + Real.sqrt 3 →
      valS (gState s k) < 2 * Real.sqrt 3 / 3 := by
    intro k hle
    have hp : pick (valS (gState s k)) = (0, 0) := pick_eq_00 hle
    have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) := by
      rw [gVal_succ, hp]; push_cast; ring
    have h2 := hlt (k + 1)
    rw [hs] at h2
    linarith
  have claim2 : ∀ k, 1 + Real.sqrt 3 < valS (gState s k) →
      valS (gState s k) < 2 + 2 * Real.sqrt 3 / 3 := by
    intro k hgt
    have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 hgt (hlt k)
    have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
      rw [gVal_succ, hp]; push_cast; ring
    have h2 := hlt (k + 1)
    rw [hs] at h2
    linarith
  by_cases hex : ∃ j, 1 + Real.sqrt 3 < valS (gState s j)
  · obtain ⟨j, hj⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 + 2 * Real.sqrt 3 / 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj, claim2 j hj⟩
      | succ k hk ih =>
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 ih.1 (hlt k)
        have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
          rw [gVal_succ, hp]; push_cast; ring
        have hgt : 1 + Real.sqrt 3 < valS (gState s (k + 1)) := by
          by_contra hle
          have h3 := claim1 (k + 1) (not_lt.mp hle)
          rw [hs] at h3
          linarith [t3_lb, ih.1]
        exact ⟨hgt, claim2 (k + 1) hgt⟩
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 (habs k hk).1 (hlt k)
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  · push Not at hex
    have htriple : ∀ n : ℕ, valS (gState s n) = 3 ^ n * valS (gState s 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hp : pick (valS (gState s n)) = (0, 0) := pick_eq_00 (hex n)
        rw [gVal_succ, hp]
        push_cast
        rw [ih, pow_succ]
        ring
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + Real.sqrt 3) / valS (gState s 0))
      (by norm_num : (1:ℝ) < 3)
    have hb := hex n
    rw [htriple n] at hb
    have hlt2 := (div_lt_iff₀ (gVal_pos h 0)).mp hn
    linarith

/-- **L1(a), from any start.**  Generalises `SZ.exists_digitA_eq_zero`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gExists_fst_eq_zero {s : ℤ × ℤ} (h : GStart s) : ∃ k, (gDigit s k).1 = 0 := by
  by_contra hcon
  push Not at hcon
  have htwo : ∀ k, (pick (valS (gState s k))).1 = 2 := by
    intro k
    rcases pick_fst_mem (valS (gState s k)) with hx | hx
    · exact absurd hx (hcon k)
    · exact hx
  have hA : ∀ k, (1 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 * Real.sqrt 3)
      ∨ 1 + 3 * Real.sqrt 3 < valS (gState s k) := fun k =>
    (pick_fst_eq_two_iff _).mp (htwo k)
  by_cases hex : ∃ j, 1 + Real.sqrt 3 < valS (gState s j) ∧ valS (gState s j) < 2 * Real.sqrt 3
  · obtain ⟨j, hj1, hj2⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 ih.1 ih.2
        have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
          rw [gVal_succ, hp]; push_cast; ring
        rcases hA (k + 1) with hx | hx
        · exact hx
        · exfalso; rw [hs] at hx; linarith [t3_lb, t3_ub, ih.2]
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 (habs k hk).1 (habs k hk).2
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  · push Not at hex
    have hA2 : ∀ k, 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
      intro k
      rcases hA k with ⟨h1, h2⟩ | hx
      · exact absurd h2 (not_lt.mpr (hex k h1))
      · exact hx
    have hfix : valS (gState s 0) = (6 + 6 * Real.sqrt 3) / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6 + 6 * Real.sqrt 3)
        (D := 2) (K := 0) (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3)
        have hp : pick (valS (gState s k)) = (2, 2) := pick_eq_22 (hA2 k)
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - (6 + 6 * Real.sqrt 3) / 2| ≤ 2
        have h1 := hA2 k
        have h2 := (gVal_mem h k).2
        rw [abs_le]
        constructor <;> linarith
    exact gVal_ne_top h 0 (by rw [hfix]; ring)

/-! ## The overlap set, and why the forced play cannot run forever -/

/-- **The overlap set `O`**: the states carrying two admissible offsets.  The four
admissibility windows `[c, c+U]` are `[0,1+√3]`, `[2,3+√3]`, `[2√3,1+3√3]`,
`[2+2√3,3+3√3]`; consecutive ones meet in these three intervals and non-consecutive ones
are disjoint. -/
def InO (w : ℝ) : Prop :=
  (2 ≤ w ∧ w ≤ 1 + Real.sqrt 3) ∨
  (2 * Real.sqrt 3 ≤ w ∧ w ≤ 3 + Real.sqrt 3) ∨
  (2 + 2 * Real.sqrt 3 ≤ w ∧ w ≤ 1 + 3 * Real.sqrt 3)

/-- Off `O` the window `[0, 3U]` splits into the four forced zones. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem zones_of_not_InO {w : ℝ} (hO : ¬ InO w) :
    w < 2 ∨ (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨
      (3 + Real.sqrt 3 < w ∧ w < 2 + 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w := by
  rw [InO] at hO
  push Not at hO
  obtain ⟨hA, hB, hC⟩ := hO
  rcases lt_or_ge w 2 with hx | hx
  · exact Or.inl hx
  · have h2 : 1 + Real.sqrt 3 < w := hA hx
    rcases lt_or_ge w (2 * Real.sqrt 3) with hy | hy
    · exact Or.inr (Or.inl ⟨h2, hy⟩)
    · have h4 : 3 + Real.sqrt 3 < w := hB hy
      rcases lt_or_ge w (2 + 2 * Real.sqrt 3) with hz | hz
      · exact Or.inr (Or.inr (Or.inl ⟨h4, hz⟩))
      · exact Or.inr (Or.inr (Or.inr (hC hz)))

/-- **The play always reaches a branch point.**  Off `O` the offset is forced, and the
zone graph is `Z₂ → Z₂`, `Z₃ → Z₃`, `Z₁ ↛ Z₄`, `Z₄ ↛ Z₁`; so an orbit avoiding `O` is
eventually confined to a single zone and sits at its fixed point — `3`, `3√3`, `3 + 3√3`
or `0` — each excluded by the growth of the `√3`-coordinate. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem gExists_inO {s : ℤ × ℤ} (h : GStart s) : ∃ k, InO (valS (gState s k)) := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ k, valS (gState s k) < 2 ∨
      (1 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 * Real.sqrt 3) ∨
      (3 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 + 2 * Real.sqrt 3) ∨
      1 + 3 * Real.sqrt 3 < valS (gState s k) := fun k =>
    zones_of_not_InO (hcon k)
  -- the four forced steps
  have step1 : ∀ k, valS (gState s k) < 2 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) := by
    intro k hk
    have hp : pick (valS (gState s k)) = (0, 0) := pick_eq_00 (by linarith [t3_lb])
    rw [gVal_succ, hp]; push_cast; ring
  have step2 : ∀ k, 1 + Real.sqrt 3 < valS (gState s k) → valS (gState s k) < 2 * Real.sqrt 3 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
    intro k h1 h2
    have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 h1 h2
    rw [gVal_succ, hp]; push_cast; ring
  have step3 : ∀ k, 3 + Real.sqrt 3 < valS (gState s k) →
      valS (gState s k) < 2 + 2 * Real.sqrt 3 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 * Real.sqrt 3 := by
    intro k h1 h2
    have hp : pick (valS (gState s k)) = (0, 2) :=
      pick_eq_02 (by linarith [t3_lb, t3_ub]) (by linarith [t3_lb])
    rw [gVal_succ, hp]; push_cast; ring
  have step4 : ∀ k, 1 + 3 * Real.sqrt 3 < valS (gState s k) →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3) := by
    intro k hk
    have hp : pick (valS (gState s k)) = (2, 2) := pick_eq_22 hk
    rw [gVal_succ, hp]; push_cast; ring
  -- Z₂ is absorbing
  by_cases hZ2 : ∃ j, 1 + Real.sqrt 3 < valS (gState s j) ∧ valS (gState s j) < 2 * Real.sqrt 3
  · obtain ⟨j, hj1, hj2⟩ := hZ2
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hs := step2 k ih.1 ih.2
        rcases hz (k + 1) with hx | hx | hx | hx <;> rw [hs] at hx ⊢
        · exact absurd hx (by push Not; linarith [t3_lb, ih.1])
        · exact hx
        · exact absurd hx.1 (by push Not; linarith [t3_ub, ih.2])
        · exact absurd hx (by push Not; linarith [t3_ub, ih.2])
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        exact step2 k (habs k hk).1 (habs k hk).2
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]; constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  -- Z₃ is absorbing
  · push Not at hZ2
    by_cases hZ3 : ∃ j, 3 + Real.sqrt 3 < valS (gState s j) ∧
        valS (gState s j) < 2 + 2 * Real.sqrt 3
    · obtain ⟨j, hj1, hj2⟩ := hZ3
      have habs : ∀ k, j ≤ k → 3 + Real.sqrt 3 < valS (gState s k) ∧
          valS (gState s k) < 2 + 2 * Real.sqrt 3 := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact ⟨hj1, hj2⟩
        | succ k hk ih =>
          have hs := step3 k ih.1 ih.2
          rcases hz (k + 1) with hx | hx | hx | hx <;> rw [hs] at hx ⊢
          · exact absurd hx (by push Not; linarith [t3_ub, ih.1])
          · exact absurd hx.2 (by push Not; linarith [t3_ub, ih.1])
          · exact hx
          · exact absurd hx (by push Not; linarith [t3_lb, ih.2])
      have hfix : valS (gState s j) = 6 * Real.sqrt 3 / 2 := by
        refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6 * Real.sqrt 3)
          (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
        · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 * Real.sqrt 3
          exact step3 k (habs k hk).1 (habs k hk).2
        · show |valS (gState s k) - 6 * Real.sqrt 3 / 2| ≤ 1
          obtain ⟨ha, hb⟩ := habs k hk
          rw [abs_le]; constructor <;> linarith [t3_lb, t3_ub]
      exact gVal_ne_threeRoot h j (by rw [hfix]; ring)
    -- only Z₁ and Z₄ remain, and neither leads to the other
    · push Not at hZ3
      have hz14 : ∀ k, valS (gState s k) < 2 ∨ 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
        intro k
        rcases hz k with hx | hx | hx | hx
        · exact Or.inl hx
        · exact absurd hx.2 (not_lt.mpr (hZ2 k hx.1))
        · exact absurd hx.2 (not_lt.mpr (hZ3 k hx.1))
        · exact Or.inr hx
      by_cases hZ4 : ∃ j, 1 + 3 * Real.sqrt 3 < valS (gState s j)
      · obtain ⟨j, hj⟩ := hZ4
        have habs : ∀ k, j ≤ k → 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => exact hj
          | succ k hk ih =>
            have hs := step4 k ih
            rcases hz14 (k + 1) with hx | hx
            · exfalso; rw [hs] at hx; linarith [t3_lb]
            · exact hx
        have hfix : valS (gState s j) = (6 + 6 * Real.sqrt 3) / 2 := by
          refine eq_fixed_of_trapped (f := fun k => valS (gState s k))
            (c := 6 + 6 * Real.sqrt 3) (D := 2) (K := j) (fun k hk => ?_) (fun k hk => ?_)
          · show valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3)
            exact step4 k (habs k hk)
          · show |valS (gState s k) - (6 + 6 * Real.sqrt 3) / 2| ≤ 2
            have h1 := habs k hk
            have h2 := (gVal_mem h k).2
            rw [abs_le]; constructor <;> linarith
        exact gVal_ne_top h j (by rw [hfix]; ring)
      · push Not at hZ4
        have hone : ∀ k, valS (gState s k) < 2 := by
          intro k
          rcases hz14 k with hx | hx
          · exact hx
          · exact absurd hx (not_lt.mpr (hZ4 k))
        have htriple : ∀ n : ℕ, valS (gState s n) = 3 ^ n * valS (gState s 0) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [step1 n (hone n), ih, pow_succ]; ring
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / valS (gState s 0))
          (by norm_num : (1:ℝ) < 3)
        have hb := hone n
        rw [htriple n] at hb
        have hlt2 := (div_lt_iff₀ (gVal_pos h 0)).mp hn
        linarith

/-! ## The two offsets at a branch point -/

private theorem valS_00 : valS ((0 : ℤ), (0 : ℤ)) = 0 := by norm_num [valS]
private theorem valS_20 : valS ((2 : ℤ), (0 : ℤ)) = 2 := by norm_num [valS]
private theorem valS_02 : valS ((0 : ℤ), (2 : ℤ)) = 2 * Real.sqrt 3 := by norm_num [valS]
private theorem valS_22 : valS ((2 : ℤ), (2 : ℤ)) = 2 + 2 * Real.sqrt 3 := by norm_num [valS]

/-- At a branch point, the bit `b` selects between the two admissible offsets: `true` takes
the one with `a = 2`, `false` the one with `a = 0`. -/
noncomputable def branchDigit (w : ℝ) (b : Bool) : ℤ × ℤ :=
  if w ≤ 1 + Real.sqrt 3 then cond b (2, 0) (0, 0)
  else if w ≤ 3 + Real.sqrt 3 then cond b (2, 0) (0, 2)
  else cond b (2, 2) (0, 2)

/-- **The two offsets differ in their `a`-part** — this is what separates the witnesses. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem branchDigit_fst (w : ℝ) (b : Bool) : (branchDigit w b).1 = cond b 2 0 := by
  unfold branchDigit; split_ifs <;> cases b <;> rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem branchDigit_fst_ne {w w' : ℝ} {b b' : Bool} (hb : b ≠ b') :
    (branchDigit w b).1 ≠ (branchDigit w' b').1 := by
  rw [branchDigit_fst, branchDigit_fst]
  cases b <;> cases b' <;> simp_all

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem branchDigit_even (w : ℝ) (b : Bool) : EvenDigit (branchDigit w b) := by
  unfold branchDigit EvenDigit; split_ifs <;> cases b <;> simp

/-- Both offsets are admissible on `O`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem branchDigit_adm {w : ℝ} (h : InO w) (b : Bool) :
    0 ≤ w - valS (branchDigit w b) ∧ w - valS (branchDigit w b) ≤ 1 + Real.sqrt 3 := by
  have e1 : w ≤ 1 + Real.sqrt 3 → branchDigit w b = cond b (2, 0) (0, 0) := by
    intro hw; unfold branchDigit; rw [ite_eq_left hw]
  have e2 : ¬ (w ≤ 1 + Real.sqrt 3) → w ≤ 3 + Real.sqrt 3 →
      branchDigit w b = cond b (2, 0) (0, 2) := by
    intro h1 h2; unfold branchDigit; rw [ite_eq_right h1, ite_eq_left h2]
  have e3 : ¬ (w ≤ 1 + Real.sqrt 3) → ¬ (w ≤ 3 + Real.sqrt 3) →
      branchDigit w b = cond b (2, 2) (0, 2) := by
    intro h1 h2; unfold branchDigit; rw [ite_eq_right h1, ite_eq_right h2]
  rcases h with hx | hx | hx
  · rw [e1 hx.2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_00, valS_20] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]
  · have h1 : ¬ (w ≤ 1 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    rw [e2 h1 hx.2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_02, valS_20] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]
  · have h1 : ¬ (w ≤ 1 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    have h2 : ¬ (w ≤ 3 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    rw [e3 h1 h2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_02, valS_22] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]

/-! ## The tree of plays -/

/-- A node of the tree: the state, flags recording whether an `a = 0` and a `b = 2` have
been emitted since the last branching, and the number of bits consumed so far. -/
structure Node where
  /-- the cover state -/
  st : ℤ × ℤ
  /-- an `a = 0` has been emitted since the last branching -/
  g0 : Bool
  /-- a `b = 2` has been emitted since the last branching -/
  g2 : Bool
  /-- bits of `β` consumed so far -/
  used : ℕ

/-- A node branches when hygiene is banked and the state offers a choice. -/
def Branching (n : Node) : Prop := n.g0 = true ∧ n.g2 = true ∧ InO (valS n.st)

open Classical in
/-- The offset played at a node. -/
noncomputable def nodeDigit (β : ℕ → Bool) (n : Node) : ℤ × ℤ :=
  if Branching n then branchDigit (valS n.st) (β n.used) else pick (valS n.st)

open Classical in
/-- The successor node: branch and reset the flags, or follow the rule and bank. -/
noncomputable def nodeNext (β : ℕ → Bool) (n : Node) : Node :=
  if Branching n then
    { st := stepS n.st (nodeDigit β n),
      g0 := decide ((nodeDigit β n).1 = 0),
      g2 := decide ((nodeDigit β n).2 = 2),
      used := n.used + 1 }
  else
    { st := stepS n.st (nodeDigit β n),
      g0 := n.g0 || decide ((nodeDigit β n).1 = 0),
      g2 := n.g2 || decide ((nodeDigit β n).2 = 2),
      used := n.used }

/-- The play encoded by `β`, as a sequence of nodes from the seed `3σ = -12 + 9√3`. -/
noncomputable def node (β : ℕ → Bool) (k : ℕ) : Node :=
  (nodeNext β)^[k] { st := (-12, 9), g0 := false, g2 := false, used := 0 }

/-- The offset stream of the play encoded by `β`. -/
noncomputable def treeDigit (β : ℕ → Bool) (k : ℕ) : ℤ × ℤ := nodeDigit β (node β k)

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_succ (β : ℕ → Bool) (k : ℕ) : node β (k + 1) = nodeNext β (node β k) :=
  Function.iterate_succ_apply' _ _ _

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_st_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).st = stepS (node β k).st (treeDigit β k) := by
  rw [node_succ, nodeNext, treeDigit]
  split_ifs <;> rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_st_zero (β : ℕ → Bool) : (node β 0).st = (-12, 9) := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_st_eq_runState (β : ℕ → Bool) (k : ℕ) :
    (node β k).st = runState (-12, 9) (treeDigit β) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [node_st_succ, runState_succ, ih]

/-- Whatever the node does, the offset it plays is admissible. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem nodeDigit_adm (β : ℕ → Bool) (n : Node) (h0 : 0 ≤ valS n.st)
    (h1 : valS n.st ≤ 3 + 3 * Real.sqrt 3) : Adm n.st (nodeDigit β n) := by
  unfold nodeDigit
  split_ifs with hb
  · exact ⟨branchDigit_even _ _, branchDigit_adm hb.2.2 _⟩
  · exact ⟨evenDigit_pick _, pick_residual_mem h0 h1⟩

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_val_mem (β : ℕ → Bool) (k : ℕ) :
    0 ≤ valS (node β k).st ∧ valS (node β k).st ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero =>
    rw [node_st_zero, valS]
    norm_num
    constructor <;> linarith [t3_lb, t3_ub]
  | succ k ih =>
    obtain ⟨-, hlo, hhi⟩ := nodeDigit_adm β (node β k) ih.1 ih.2
    rw [node_st_succ, valS_stepS, treeDigit]
    constructor <;> linarith

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_isRun (β : ℕ → Bool) : IsRun (-12, 9) (treeDigit β) := by
  intro k
  rw [← node_st_eq_runState]
  exact nodeDigit_adm β (node β k) (tree_val_mem β k).1 (tree_val_mem β k).2

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_gStart (β : ℕ → Bool) (k : ℕ) : GStart (node β k).st := by
  refine ⟨(tree_val_mem β k).1, (tree_val_mem β k).2, ?_⟩
  have hb := runState_snd_lower (tree_isRun β) k
  have h1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  rw [← node_st_eq_runState] at hb
  simp only at hb
  nlinarith [hb, h1]

/-! ## Branchings happen infinitely often, and hygiene survives -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeDigit_of_not_branching (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    treeDigit β k = pick (valS (node β k).st) := by
  rw [treeDigit, nodeDigit, ite_eq_right h]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeDigit_of_branching (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    treeDigit β k = branchDigit (valS (node β k).st) (β (node β k).used) := by
  rw [treeDigit, nodeDigit, ite_eq_left h]

/-- In a stretch without branchings the play is exactly the rule's orbit. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_st_of_not_branching (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    (node β (N + j)).st = gState (node β N).st j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e : N + (j + 1) = (N + j) + 1 := by omega
    rw [e, node_st_succ, treeDigit_of_not_branching β (hno j), ih, gState_succ]
    rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeDigit_of_not_branching' (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    treeDigit β (N + j) = gDigit (node β N).st j := by
  rw [treeDigit_of_not_branching β (hno j), node_st_of_not_branching β hno j, gDigit]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_g0_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).g0 = true → (node β k).g0 = true ∨ (treeDigit β k).1 = 0 := by
  rw [node_succ, nodeNext]
  split_ifs with hb <;> simp only [treeDigit] <;> intro h
  · exact Or.inr (of_decide_eq_true h)
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (of_decide_eq_true h')

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_g2_succ (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).g2 = true → (node β k).g2 = true ∨ (treeDigit β k).2 = 2 := by
  rw [node_succ, nodeNext]
  split_ifs with hb <;> simp only [treeDigit] <;> intro h
  · exact Or.inr (of_decide_eq_true h)
  · rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (of_decide_eq_true h')

/-- A flag that is set was set by a digit actually emitted in the meantime. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem g0_true_witness (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g0 = true) :
    (node β j).g0 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).1 = 0 := by
  induction k, hjk using Nat.le_induction with
  | base => exact Or.inl h
  | succ k hk ih =>
    rcases node_g0_succ β k h with h' | h'
    · rcases ih h' with hx | ⟨i, hi1, hi2, hi3⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi1, by omega, hi3⟩
    · exact Or.inr ⟨k, hk, by omega, h'⟩

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem g2_true_witness (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) (h : (node β k).g2 = true) :
    (node β j).g2 = true ∨ ∃ i, j ≤ i ∧ i < k ∧ (treeDigit β i).2 = 2 := by
  induction k, hjk using Nat.le_induction with
  | base => exact Or.inl h
  | succ k hk ih =>
    rcases node_g2_succ β k h with h' | h'
    · rcases ih h' with hx | ⟨i, hi1, hi2, hi3⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi1, by omega, hi3⟩
    · exact Or.inr ⟨k, hk, by omega, h'⟩

/-- Without branchings the flags only ever go up. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_g0_mono (β : ℕ → Bool) {N : ℕ} (hno : ∀ i, ¬ Branching (node β (N + i)))
    {j k : ℕ} (hjk : j ≤ k) (h0 : (node β (N + j)).g0 = true) :
    (node β (N + k)).g0 = true := by
  induction k, hjk using Nat.le_induction with
  | base => exact h0
  | succ k hk ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, node_succ, nodeNext, ite_eq_right (hno k)]
    simp [ih]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_g2_mono (β : ℕ → Bool) {N : ℕ} (hno : ∀ i, ¬ Branching (node β (N + i)))
    {j k : ℕ} (hjk : j ≤ k) (h2 : (node β (N + j)).g2 = true) :
    (node β (N + k)).g2 = true := by
  induction k, hjk using Nat.le_induction with
  | base => exact h2
  | succ k hk ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, node_succ, nodeNext, ite_eq_right (hno k)]
    simp [ih]

/-- **Every play branches infinitely often.**  Otherwise its tail is the rule's orbit, which
banks an `a = 0` and a `b = 2` (`gExists_fst_eq_zero`, `gExists_snd_eq_two`) and then meets
`O` (`gExists_inO`) — at which point the node branches. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_exists_branching (β : ℕ → Bool) (N : ℕ) : ∃ k, N ≤ k ∧ Branching (node β k) := by
  by_contra hcon
  push Not at hcon
  have hno : ∀ i, ¬ Branching (node β (N + i)) := fun i => hcon _ (Nat.le_add_right _ _)
  have hstart : GStart (node β N).st := tree_gStart β N
  obtain ⟨k0, hk0⟩ := gExists_fst_eq_zero hstart
  obtain ⟨k2, hk2⟩ := gExists_snd_eq_two hstart
  have hd0 : (treeDigit β (N + k0)).1 = 0 := by
    rw [treeDigit_of_not_branching' β hno k0]; exact hk0
  have hd2 : (treeDigit β (N + k2)).2 = 2 := by
    rw [treeDigit_of_not_branching' β hno k2]; exact hk2
  have hset0 : (node β (N + (k0 + 1))).g0 = true := by
    have e : N + (k0 + 1) = (N + k0) + 1 := by omega
    rw [e, node_succ, nodeNext, ite_eq_right (hno k0)]
    show ((node β (N + k0)).g0 || decide ((treeDigit β (N + k0)).1 = 0)) = true
    simp [hd0]
  have hset2 : (node β (N + (k2 + 1))).g2 = true := by
    have e : N + (k2 + 1) = (N + k2) + 1 := by omega
    rw [e, node_succ, nodeNext, ite_eq_right (hno k2)]
    show ((node β (N + k2)).g2 || decide ((treeDigit β (N + k2)).2 = 2)) = true
    simp [hd2]
  obtain ⟨k3, hk3⟩ := gExists_inO (gStart_gState hstart (max (k0 + 1) (k2 + 1)))
  set t := max (k0 + 1) (k2 + 1) with ht
  refine hno (t + k3) ⟨node_g0_mono β hno (show k0 + 1 ≤ t + k3 by omega) hset0,
    node_g2_mono β hno (show k2 + 1 ≤ t + k3 by omega) hset2, ?_⟩
  rw [node_st_of_not_branching β hno, gState_add]
  exact hk3

/-! ## L1 for every play in the tree -/

/-- Between two branchings an `a = 0` is emitted: the flag is reset at the first and set at
the second. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_exists_fst_eq_zero (β : ℕ → Bool) (N : ℕ) :
    ∃ k, N ≤ k ∧ (treeDigit β k).1 = 0 := by
  obtain ⟨k₁, hk₁N, hk₁⟩ := tree_exists_branching β N
  obtain ⟨k₂, hk₂, hk₂b⟩ := tree_exists_branching β (k₁ + 1)
  by_cases hd : (treeDigit β k₁).1 = 0
  · exact ⟨k₁, hk₁N, hd⟩
  · have hg : (node β (k₁ + 1)).g0 = false := by
      rw [node_succ, nodeNext, ite_eq_left hk₁]
      show decide ((treeDigit β k₁).1 = 0) = false
      simp [hd]
    rcases g0_true_witness β hk₂ hk₂b.1 with h | ⟨i, hi1, hi2, hi3⟩
    · rw [hg] at h; exact absurd h (by simp)
    · exact ⟨i, by omega, hi3⟩

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem tree_exists_snd_eq_two (β : ℕ → Bool) (N : ℕ) :
    ∃ k, N ≤ k ∧ (treeDigit β k).2 = 2 := by
  obtain ⟨k₁, hk₁N, hk₁⟩ := tree_exists_branching β N
  obtain ⟨k₂, hk₂, hk₂b⟩ := tree_exists_branching β (k₁ + 1)
  by_cases hd : (treeDigit β k₁).2 = 2
  · exact ⟨k₁, hk₁N, hd⟩
  · have hg : (node β (k₁ + 1)).g2 = false := by
      rw [node_succ, nodeNext, ite_eq_left hk₁]
      show decide ((treeDigit β k₁).2 = 2) = false
      simp [hd]
    rcases g2_true_witness β hk₂ hk₂b.2.1 with h | ⟨i, hi1, hi2, hi3⟩
    · rw [hg] at h; exact absurd h (by simp)
    · exact ⟨i, by omega, hi3⟩

/-! ## Every play solves the translate equation

Generalisations of `SZ.W_eq_residual` and `SZ.digitReal_translate` from the rule's orbit to
an arbitrary play. -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runVal_eq_residual (d : ℕ → ℤ × ℤ) (k : ℕ) :
    valS (runState (-12, 9) d k) = 3 ^ (k + 1) * ((3 * Real.sqrt 3 - 4)
      - digitSum 3 (fun i => (d i).1) k
      - Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) := by
  induction k with
  | zero =>
    rw [show runState ((-12 : ℤ), (9 : ℤ)) d 0 = ((-12 : ℤ), (9 : ℤ)) from rfl, valS,
      digitSum_zero, digitSum_zero]
    push_cast
    ring
  | succ k ih =>
    rw [runState_succ, valS_stepS, ih]
    simp only [digitSum_succ]
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3, valS]
    have hne : (3 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem isDigits_run_fst {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).1) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.1 with h | h <;> omega
    le_sub_one := fun i => by rcases (hrun i).1.1 with h | h <;> omega }

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem isDigits_run_snd {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (fun i => (d i).2) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.2 with h | h <;> omega
    le_sub_one := fun i => by rcases (hrun i).1.2 with h | h <;> omega }

/-- **Every admissible play converges to a solution of the translate equation.** -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem run_translate {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    digitReal 3 (fun i => (d i).1) + Real.sqrt 3 * digitReal 3 (fun i => (d i).2)
      = 3 * Real.sqrt 3 - 4 := by
  have h0 : (0 : ℝ) ≤ valS ((-12 : ℤ), (9 : ℤ)) := by
    rw [valS]; push_cast; linarith [t3_lb]
  have h1 : valS ((-12 : ℤ), (9 : ℤ)) ≤ 3 + 3 * Real.sqrt 3 := by
    rw [valS]; push_cast; linarith [t3_ub]
  have hlim : Tendsto (fun k => digitSum 3 (fun i => (d i).1) k
      + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) atTop
      (𝓝 (digitReal 3 (fun i => (d i).1) + Real.sqrt 3 * digitReal 3 (fun i => (d i).2))) :=
    (digitSum_tendsto (isDigits_run_fst hrun)).add
      (tendsto_const_nhds.mul (digitSum_tendsto (isDigits_run_snd hrun)))
  have hzero : Tendsto (fun k : ℕ => (3 * Real.sqrt 3 - 4)
      - (digitSum 3 (fun i => (d i).1) k
          + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => (3 + 3 * Real.sqrt 3) / 3 ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (runVal_mem hrun h0 h1 k).1
      rw [runVal_eq_residual d k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      nlinarith
    · have h := (runVal_mem hrun h0 h1 k).2
      rw [runVal_eq_residual d k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hmain : Tendsto (fun k : ℕ => (3 + 3 * Real.sqrt 3) * (1 / 3 : ℝ) ^ (k + 1))
          atTop (𝓝 0) := by
        have hg : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
          have h0' := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/3 : ℝ))
            (by norm_num) (by norm_num)
          exact h0'.comp (Filter.tendsto_add_atTop_nat 1)
        simpa using hg.const_mul (3 + 3 * Real.sqrt 3)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum 3 (fun i => (d i).1) k
      + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) atTop (𝓝 (3 * Real.sqrt 3 - 4)) := by
    have h := (tendsto_const_nhds (x := (3 * Real.sqrt 3 - 4)) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2

/-! ## The witness attached to a play -/

/-- The `y`-stream of a play: the digitwise complement `2 - bᵢ`. -/
def runY (d : ℕ → ℤ × ℤ) (i : ℕ) : ℤ := 2 - (d i).2

/-- **The witness of a play**, `ξ = (4 + x)/3` with `x = ∑ aᵢ 3^{-i}`. -/
noncomputable def runXi (d : ℕ → ℤ × ℤ) : ℝ := (4 + digitReal 3 (fun i => (d i).1)) / 3

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem isDigits_runY {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    IsDigits 3 (runY d) :=
  { two_le := by norm_num
    nonneg := fun i => by rcases (hrun i).1.2 with h | h <;> simp [runY, h]
    le_sub_one := fun i => by rcases (hrun i).1.2 with h | h <;> simp [runY, h] }

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem digitReal_runY {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    digitReal 3 (runY d) = 1 - digitReal 3 (fun i => (d i).2) := by
  have hfun : (fun i => ((3 : ℕ) : ℤ) - 1 - (d i).2) = runY d := by
    funext i; simp only [runY]; norm_num
  rw [← hfun, digitReal_compl (isDigits_run_snd hrun)]

/-- The coupling `u = 4 + x = √3 (2 + y)`, for every play. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem run_coupling {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    4 + digitReal 3 (fun i => (d i).1) = Real.sqrt 3 * (2 + digitReal 3 (runY d)) := by
  have h := run_translate hrun
  rw [digitReal_runY hrun]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h, hs]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runXi_mem {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) :
    4 / 3 ≤ runXi d ∧ runXi d ≤ 5 / 3 := by
  have h0 := digitReal_nonneg (isDigits_run_fst hrun)
  have h1 := digitReal_le_one (isDigits_run_fst hrun)
  constructor <;> · rw [runXi]; linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runXi_pos {s₀ : ℤ × ℤ} {d : ℕ → ℤ × ℤ} (hrun : IsRun s₀ d) : 0 < runXi d :=
  lt_of_lt_of_le (by norm_num) (runXi_mem hrun).1

/-- **Every hygienic play is a witness for `√3`.**  The two hypotheses are lemma L1. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem run_even_floor {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d)
    (hA : ∀ N, ∃ k, N ≤ k ∧ (d k).1 = 0) (hB : ∀ N, ∃ k, N ≤ k ∧ (d k).2 = 2)
    {n : ℕ} (hn : 1 ≤ n) : Even ⌊runXi d * Real.sqrt 3 ^ n⌋ := by
  have heven : ∀ i, Even (d i).1 := fun i => by
    rcases (hrun i).1.1 with h | h <;> rw [h] <;> decide
  have hevenY : ∀ i, Even (runY d i) := fun i => by
    rcases (hrun i).1.2 with h | h <;> simp only [runY, h] <;> decide
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    obtain ⟨s, rfl⟩ : ∃ s, n = 2 * (s + 1) := ⟨t - 1, by omega⟩
    obtain ⟨i₀, hi₀, hz⟩ := hA s
    have hval : runXi d * Real.sqrt 3 ^ (2 * (s + 1))
        = (((4 : ℤ) : ℝ) + digitReal 3 (fun i => (d i).1)) * ((3 : ℕ) : ℝ) ^ s := by
      rw [pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), runXi]
      push_cast
      rw [pow_succ]
      ring
    rw [hval]
    exact even_floor_add_digitReal_mul_pow (isDigits_run_fst hrun) (by decide) heven s hi₀
      (show (d i₀).1 ≤ ((3 : ℕ) : ℤ) - 2 by rw [hz]; norm_num)
  · obtain ⟨s, rfl⟩ := ho
    obtain ⟨i₀, hi₀, hz⟩ := hB s
    have hsmall : runY d i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [runY, hz]
    have hval : runXi d * Real.sqrt 3 ^ (2 * s + 1)
        = (((2 : ℤ) : ℝ) + digitReal 3 (runY d)) * ((3 : ℕ) : ℝ) ^ s := by
      rw [pow_succ, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), runXi,
        show (4 : ℝ) + digitReal 3 (fun i => (d i).1)
          = Real.sqrt 3 * (2 + digitReal 3 (runY d)) from run_coupling hrun]
      push_cast
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    rw [hval]
    exact even_floor_add_digitReal_mul_pow (isDigits_runY hrun) (by decide) hevenY s hi₀ hsmall

/-! ## Distinct digit streams give distinct reals

These belong with `SZ/DigitParity.lean`; they are kept here to leave that file untouched. -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem digitSum_congr {m : ℕ} {d d' : ℕ → ℤ} {k : ℕ} (h : ∀ j, j < k → d j = d' j) :
    digitSum m d k = digitSum m d' k := by
  unfold digitSum
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem digitReal_le_digitSum_add {m : ℕ} {d : ℕ → ℤ} (h : IsDigits m d) (k : ℕ) :
    digitReal m d ≤ digitSum m d k + 1 / (m : ℝ) ^ k := by
  refine ciSup_le fun j => ?_
  rcases le_or_gt k j with hj | hj
  · have hb := digitSum_le_of_le h hj
    have hp : (0:ℝ) < 1 / (m : ℝ) ^ j := one_div_pos.mpr (h.pow_pos' j)
    linarith
  · have hb := digitSum_monotone h hj.le
    have hp : (0:ℝ) < 1 / (m : ℝ) ^ k := one_div_pos.mpr (h.pow_pos' k)
    linarith

/-- A `0` where the other stream has a `2`, with the streams agreeing before, puts the reals
a full `3^{-(i+1)}` apart. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem digitReal_lt_of_zero_two {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (h0 : d i = 0) (h2 : d' i = 2) :
    digitReal 3 d < digitReal 3 d' := by
  have hp : (0:ℝ) < ((3:ℕ) : ℝ) ^ (i + 1) := h.pow_pos' _
  have hsum : digitSum 3 d i = digitSum 3 d' i := digitSum_congr hagree
  have hd : digitSum 3 d (i + 1) = digitSum 3 d i := by
    rw [digitSum_succ, h0]; norm_num
  have hd' : digitSum 3 d' (i + 1) = digitSum 3 d i + 2 / ((3:ℕ) : ℝ) ^ (i + 1) := by
    rw [digitSum_succ, h2, hsum]; norm_num
  have hup : digitReal 3 d ≤ digitSum 3 d (i + 1) + 1 / ((3:ℕ) : ℝ) ^ (i + 1) :=
    digitReal_le_digitSum_add h (i + 1)
  have hlo : digitSum 3 d' (i + 1) ≤ digitReal 3 d' := digitSum_le_digitReal h' (i + 1)
  rw [hd] at hup
  rw [hd'] at hlo
  have hhalf : 1 / ((3:ℕ) : ℝ) ^ (i + 1) < 2 / ((3:ℕ) : ℝ) ^ (i + 1) := by
    rw [div_lt_div_iff_of_pos_right hp]; norm_num
  linarith

/-- Two `{0,2}`-streams that first differ at index `i` give different reals. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem digitReal_ne {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    (hd : ∀ j, d j = 0 ∨ d j = 2) (hd' : ∀ j, d' j = 0 ∨ d' j = 2)
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (hne : d i ≠ d' i) :
    digitReal 3 d ≠ digitReal 3 d' := by
  rcases hd i with h0 | h0 <;> rcases hd' i with h0' | h0'
  · exact absurd (h0.trans h0'.symm) hne
  · exact ne_of_lt (digitReal_lt_of_zero_two h h' hagree h0 h0')
  · exact ne_of_gt (digitReal_lt_of_zero_two h' h (fun j hj => (hagree j hj).symm) h0' h0)
  · exact absurd (h0.trans h0'.symm) hne

/-! ## The bit counter -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_used_zero (β : ℕ → Bool) : (node β 0).used = 0 := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_used_succ_branch (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used + 1 := by
  rw [node_succ, nodeNext, ite_eq_left h]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_used_succ_not (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used := by
  rw [node_succ, nodeNext, ite_eq_right h]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_used_mono (β : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) :
    (node β j).used ≤ (node β k).used := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    by_cases hb : Branching (node β k)
    · rw [node_used_succ_branch β hb]; omega
    · rw [node_used_succ_not β hb]; exact ih

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_used_unbounded (β : ℕ → Bool) (n : ℕ) : ∃ k, n < (node β k).used := by
  induction n with
  | zero =>
    obtain ⟨k, -, hk⟩ := tree_exists_branching β 0
    exact ⟨k + 1, by rw [node_used_succ_branch β hk]; omega⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨k, hkK, hk⟩ := tree_exists_branching β K
    have := node_used_mono β hkK
    exact ⟨k + 1, by rw [node_used_succ_branch β hk]; omega⟩

/-- The `n`-th bit is consumed at a genuine branching. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem exists_branch_at_used (β : ℕ → Bool) (n : ℕ) :
    ∃ k, (node β k).used = n ∧ Branching (node β k) := by
  classical
  have hex : ∃ k, n < (node β k).used := node_used_unbounded β n
  have h1 : n < (node β (Nat.find hex)).used := Nat.find_spec hex
  have h2 : Nat.find hex ≠ 0 := by
    intro hz
    rw [hz, node_used_zero] at h1
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have h3 : ¬ (n < (node β k).used) := Nat.find_min hex (by omega)
  rw [hk] at h1
  by_cases hb : Branching (node β k)
  · rw [node_used_succ_branch β hb] at h1
    exact ⟨k, by omega, hb⟩
  · rw [node_used_succ_not β hb] at h1
    omega

/-! ## Distinct bit streams, distinct witnesses -/

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem node_congr {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i) :
    ∀ k, (node β k).used ≤ n → node β k = node β' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hle
    have hk : (node β k).used ≤ n := le_trans (node_used_mono β (Nat.le_succ k)) hle
    have heq : node β k = node β' k := ih hk
    rw [node_succ, node_succ, ← heq, nodeNext, nodeNext]
    by_cases hb : Branching (node β k)
    · rw [ite_eq_left hb, ite_eq_left hb]
      have hu : (node β k).used < n := by
        rw [node_used_succ_branch β hb] at hle; omega
      have hbit : β (node β k).used = β' (node β k).used := hagree _ hu
      simp only [nodeDigit, ite_eq_left hb, hbit]
    · rw [ite_eq_right hb, ite_eq_right hb]
      simp only [nodeDigit, ite_eq_right hb]

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeDigit_congr {β β' : ℕ → Bool} {n : ℕ} (hagree : ∀ i, i < n → β i = β' i)
    {k : ℕ} (hle : (node β (k + 1)).used ≤ n) : treeDigit β k = treeDigit β' k := by
  have hk : (node β k).used ≤ n := le_trans (node_used_mono β (Nat.le_succ k)) hle
  have heq : node β k = node β' k := node_congr hagree k hk
  rw [treeDigit, treeDigit, ← heq, nodeDigit, nodeDigit]
  by_cases hb : Branching (node β k)
  · rw [ite_eq_left hb, ite_eq_left hb]
    have hu : (node β k).used < n := by
      rw [node_used_succ_branch β hb] at hle; omega
    rw [hagree _ hu]
  · rw [ite_eq_right hb, ite_eq_right hb]

/-- **The tree is faithful**: different bit streams give different witnesses. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem runXi_treeDigit_injective :
    Function.Injective (fun β : ℕ → Bool => runXi (treeDigit β)) := by
  classical
  intro β β' heq
  by_contra hne
  have hex : ∃ i, β i ≠ β' i := by
    by_contra hx
    push Not at hx
    exact hne (funext hx)
  set n := Nat.find hex with hn
  have hbit : β n ≠ β' n := Nat.find_spec hex
  have hagree : ∀ i, i < n → β i = β' i := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  obtain ⟨k, hku, hkb⟩ := exists_branch_at_used β n
  -- the two plays agree before step `k` and differ there
  have hbefore : ∀ j, j < k → (treeDigit β j).1 = (treeDigit β' j).1 := by
    intro j hj
    have : (node β (j + 1)).used ≤ n := by
      rw [← hku]; exact node_used_mono β (by omega)
    rw [treeDigit_congr hagree this]
  have hdiff : (treeDigit β k).1 ≠ (treeDigit β' k).1 := by
    have heqn : node β k = node β' k := node_congr hagree k (by omega)
    rw [treeDigit_of_branching β hkb,
      treeDigit_of_branching β' (by rw [← heqn]; exact hkb), ← heqn, hku]
    exact branchDigit_fst_ne hbit
  -- so the `a`-streams differ, hence the witnesses do
  have hx : digitReal 3 (fun i => (treeDigit β i).1) ≠ digitReal 3 (fun i => (treeDigit β' i).1) :=
    digitReal_ne (isDigits_run_fst (tree_isRun β)) (isDigits_run_fst (tree_isRun β'))
      (fun j => (tree_isRun β j).1.1) (fun j => (tree_isRun β' j).1.1) hbefore hdiff
  have := heq
  simp only [runXi] at this
  exact hx (by linarith [this])

/-! ## Theorem 9.1 -/

/-- **The witness set for `√3`**: the `ξ > 0` all of whose integral parts
`⌊ξ √3ⁿ⌋`, `n ≥ 1`, are even.  `SZ.witXi` is one of its points. -/
def witnessSet : Set ℝ := {ξ : ℝ | 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋}

/-- The witness produced by the bit stream `β`. -/
noncomputable def treeXi (β : ℕ → Bool) : ℝ := runXi (treeDigit β)

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeXi_mem (β : ℕ → Bool) : treeXi β ∈ witnessSet :=
  ⟨runXi_pos (tree_isRun β), fun _ hn =>
    run_even_floor (tree_isRun β) (tree_exists_fst_eq_zero β) (tree_exists_snd_eq_two β) hn⟩

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeXi_mem_Icc (β : ℕ → Bool) : 4 / 3 ≤ treeXi β ∧ treeXi β ≤ 5 / 3 :=
  runXi_mem (tree_isRun β)

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem treeXi_injective : Function.Injective treeXi := runXi_treeDigit_injective

@[category API, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem mk_nat_arrow_bool : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp [Cardinal.two_power_aleph0]

/-- **Theorem 9.1, cardinality half.**  The witness set has the cardinality of the
continuum — already inside `[4/3, 5/3]`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem continuum_le_mk_witnessSet :
    Cardinal.continuum ≤ Cardinal.mk witnessSet := by
  have hinj : Function.Injective
      (fun β : ℕ → Bool => (⟨treeXi β, treeXi_mem β⟩ : witnessSet)) := by
    intro β β' h
    exact treeXi_injective (congrArg Subtype.val h)
  have h := Cardinal.mk_le_of_injective hinj
  rwa [mk_nat_arrow_bool] at h

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem not_countable_witnessSet : ¬ witnessSet.Countable := by
  intro hc
  have h1 : Cardinal.mk witnessSet ≤ Cardinal.aleph0 :=
    Cardinal.le_aleph0_iff_set_countable.mpr hc
  exact absurd (continuum_le_mk_witnessSet.trans h1) (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- **Theorem 9.1.**  All but countably many witnesses for `√3` are transcendental; in
particular [Dub06EO] Problem 3 has a transcendental witness. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem exists_transcendental_mem_witnessSet :
    ∃ ξ ∈ witnessSet, Transcendental ℚ ξ := by
  by_contra hcon
  push Not at hcon
  have hsub : witnessSet ⊆ {x : ℝ | IsAlgebraic ℚ x} := fun ξ hξ => not_not.mp (hcon ξ hξ)
  exact not_countable_witnessSet ((Algebraic.countable ℚ ℝ).mono hsub)

/-- **[Dub06EO] Problem 3 has a transcendental witness.**  The statement of
`SZ.sqrtThree_mem_MahlerZ` with `ξ` transcendental over `ℚ`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_witness_tree"]
theorem exists_transcendental_witness_sqrtThree :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ Transcendental ℚ ξ ∧
      ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋ := by
  obtain ⟨ξ, ⟨hpos, hfloor⟩, htr⟩ := exists_transcendental_mem_witnessSet
  exact ⟨ξ, ne_of_gt hpos, htr, hfloor⟩

end SZ
