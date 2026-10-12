/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.List.Count
import Mathlib.Data.Finset.Range
import ForMathlib.Combinatorics.NatDensity
import EVG25.UniformCorrespondence
import EVG25.Answer
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Question 17 of Eliahou–Verger-Gaugry: is the Collatz conjecture a density statement in base 3/2?

[EVG25] (S. Eliahou, J.-L. Verger-Gaugry, *The number system in rational base 3/2 and the
3x + 1 problem*, C. R. Math. **363** (2025), 329–336; arXiv:2504.13716) reads the Collatz map
through the rational base 3/2 number system of Akiyama–Frougny–Sakarovitch [AFS08].  What the
note *proves* about that link sits in `EVG25/Base3div2Basics.lean` and
`EVG25/UniformCorrespondence.lean` (namespaces `CC.Base3div2` and `CC`), which this file builds
on:

* `CC.conjecture_2_4_iff_2_5` — Proposition 6: the Collatz conjecture is *equivalent* to "the
  proportion of even numbers among the iterates `T^k(n₀)` tends to 1/2", for every `n₀ ≥ 1`;
* `CC.Base3div2.digits₃₂_U` — Proposition 15: `⟨U n⟩ = ⟨n⟩1` when `n` is odd and `⟨n⟩2` when `n`
  is even, so a `U`-orbit *writes* an infinite word over `{1, 2}`; for `n₀ = 0` that word is the
  saturated word `⟨sat(∞)⟩`;
* `CC.conjecture_4_2` and `CC.conjecture_U_orbit_density` — Conjecture 18 and the density
  statement of Question 17, as `Prop` definitions in parity form.

This file states what the note leaves **open**, in the idiom of the `formal-conjectures`
project: `answer(sorry)` (see `EVG25/Answer.lean`) marks the unknown answer of a yes/no
question, and elaborates to `True` — so `P ↔ answer(sorry)` is the assertion "the answer to
`P`? is yes", carrying a `sorry` because nobody knows.

The open statements are:

* Question 17, "for instance" clause: is it true that, from **any** `n₀`, the proportion of
  digits `1` in `⟨U^k(n₀)⟩` tends to 1/2?  (`question_17.parts.i`)
* Question 17, the equivalence it actually asks about: is that behaviour of `U` *equivalent* to
  the Collatz conjecture?  (`question_17.parts.ii`, and the two one-way forms
  `question_17.variants.collatz_imp_density`, `question_17.variants.density_imp_collatz`)
* The question following Conjecture 18: is Conjecture 18 — the `n₀ = 0` case, about the
  saturated word — equivalent to the Collatz conjecture?  (`conjecture_18.variants.iff_collatz`)

Following the standing convention of this corpus, the 3x+1 conjecture is *not* given a
definition of its own: it is inlined as `∀ n ≥ 1, ∃ k ≥ 1, T_iter k n = 1`, in the same words
as `CC.conjecture_2_4_iff_2_5`.

The sorry-free layer added here is the note's *word* form of the density.  `CC` counts odd
values along the `U`-orbit; [EVG25] counts digits `1` in the word `⟨U^k(n₀)⟩`, whose length
grows from `|⟨n₀⟩|`, not from `0`.  `digitOneDensity_iff_U_orbit_density` shows the two agree —
`⟨n₀⟩` contributes only a bounded prefix, the digit-`0` count never moves
(`numZeros_U_iter`, the note's remark that "the number of digits 0 remains constant along the
trajectory of `n₀`"), and each further step appends a `1` exactly when the current value is
odd.  `numOnes_sat` identifies `CC.numOnesSat` with the honest digit count of `⟨sat k⟩`, so
`CC.conjecture_4_2` really is Conjecture 18.

All three statements are, verbatim, assertions that a set of naturals has density 1/2; the
section "The conjectures as density statements" reads them through
`ForMathlib/Combinatorics/NatDensity.lean`'s `HasNatDensity`, including Proposition 6 itself
(`collatz_iff_hasNatDensity_even`).

The vagueness in Question 17's first sentence ("equivalent to *some* behaviour of the iteration
of `U`") is not formalizable as stated — every conjecture is equivalent to some behaviour of
anything — so only the concrete instance the note proposes is stated here.
-/

open Filter Topology CC CC.Base3div2

namespace EVG25

/-! ## `U`-orbits never cycle

Unlike a `T`-orbit, a `U`-orbit is strictly increasing.  The collapse to the cycle `1, 2` that
proves the easy half of Proposition 6 therefore has no counterpart for `U`. -/

theorem lt_U (n : ℕ) : n < U n := by unfold U; split <;> omega

theorem add_le_U_iter (k n : ℕ) : n + k ≤ U_iter k n := by
  induction k with
  | zero => simp
  | succ k ih => have := lt_U (U_iter k n); rw [U_iter_succ]; omega

/-! ## Counting digits along a `U`-orbit -/

/-- The number of digits `1` in the base-3/2 word of `n`. -/
def numOnes (n : ℕ) : ℕ := (digits₃₂ n).count 1

/-- The number of digits `0` in the base-3/2 word of `n`. -/
def numZeros (n : ℕ) : ℕ := (digits₃₂ n).count 0

@[simp] theorem numOnes_zero : numOnes 0 = 0 := by simp [numOnes, digits₃₂_zero]

theorem numOddU_succ (k n₀ : ℕ) :
    numOddU (k + 1) n₀ = numOddU k n₀ + if U_iter k n₀ % 2 = 1 then 1 else 0 := by
  unfold numOddU
  rw [Finset.range_add_one, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- The word `⟨U^k(n₀)⟩` is `⟨n₀⟩` with `k` further digits. -/
theorem length_digits₃₂_U_iter (k n₀ : ℕ) :
    (digits₃₂ (U_iter k n₀)).length = (digits₃₂ n₀).length + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [U_iter_succ, digits₃₂_U]; simp [ih]; omega

/-- `⟨sat k⟩` has length `k` ([EVG25] Notation 10). -/
theorem length_digits₃₂_sat (k : ℕ) : (digits₃₂ (sat k)).length = k := by
  simpa [sat, digits₃₂_zero] using length_digits₃₂_U_iter k 0

/-- [EVG25] Question 17: "the number of digits 0 remains constant along the trajectory of `n₀`". -/
theorem numZeros_U_iter (k n₀ : ℕ) : numZeros (U_iter k n₀) = numZeros n₀ := by
  simp only [numZeros]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [U_iter_succ, digits₃₂_U, List.count_cons, ih]
    split_ifs <;> simp_all

/-- The digits `1` of `⟨U^k(n₀)⟩` are those of `⟨n₀⟩` plus one per odd step. -/
theorem numOnes_U_iter (k n₀ : ℕ) : numOnes (U_iter k n₀) = numOnes n₀ + numOddU k n₀ := by
  simp only [numOnes]
  induction k with
  | zero => simp [numOddU]
  | succ k ih =>
    rw [U_iter_succ, digits₃₂_U, List.count_cons, ih, numOddU_succ]
    by_cases hodd : U_iter k n₀ % 2 = 1 <;> simp [hodd, Nat.add_assoc]

/-- `CC.numOnesSat` is the honest count of digits `1` in the word `⟨sat k⟩`, so
`CC.conjecture_4_2` is [EVG25] Conjecture 18 as stated there. -/
theorem numOnes_sat (k : ℕ) : numOnes (sat k) = numOnesSat k := by
  have h : numOnes (U_iter k 0) = numOnes 0 + numOddU k 0 := numOnes_U_iter k 0
  rw [numOnes_zero, Nat.zero_add] at h
  exact h

/-! ## Question 17's density, in the note's own words -/

/-- The quantity Question 17 is about: the proportion of digits `1` in the word `⟨U^k(n₀)⟩`. -/
def digitOneRatio (n₀ k : ℕ) : ℚ :=
  (numOnes (U_iter k n₀) : ℚ) / ((digits₃₂ (U_iter k n₀)).length : ℚ)

/-- **Question 17's density**, for a fixed starting point: the proportion of digits `1` in
`⟨U^k(n₀)⟩` tends to `1/2`. -/
def DigitOneDensity (n₀ : ℕ) : Prop :=
  Tendsto (digitOneRatio n₀) atTop (𝓝 (1 / 2 : ℚ))

theorem digitOneRatio_zero (k : ℕ) : digitOneRatio 0 k = (numOnes (sat k) : ℚ) / (k : ℚ) := by
  rw [digitOneRatio, show U_iter k 0 = sat k from rfl, length_digits₃₂_sat]

/-- Shifting numerator and denominator of a ratio of naturals by constants does not change
whether it converges, nor the limit. -/
theorem tendsto_shift_ratio_iff {a : ℕ → ℕ} {c d : ℕ} {L : ℚ} :
    Tendsto (fun k => ((c + a k : ℕ) : ℚ) / ((d + k : ℕ) : ℚ)) atTop (𝓝 L) ↔
      Tendsto (fun k => (a k : ℚ) / (k : ℚ)) atTop (𝓝 L) := by
  have hk : Tendsto (fun k : ℕ => (k : ℚ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hkd : Tendsto (fun k : ℕ => (k : ℚ) + (d : ℚ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hk
  have hcd : Tendsto (fun k : ℕ => (c : ℚ) / ((k : ℚ) + (d : ℚ))) atTop (𝓝 0) :=
    hkd.const_div_atTop _
  have hdk : Tendsto (fun k : ℕ => (d : ℚ) / (k : ℚ)) atTop (𝓝 0) := hk.const_div_atTop _
  have hck : Tendsto (fun k : ℕ => (c : ℚ) / (k : ℚ)) atTop (𝓝 0) := hk.const_div_atTop _
  -- `(k + d)/k → 1` and `k/(k + d) → 1`
  have h1 : Tendsto (fun k : ℕ => ((k : ℚ) + (d : ℚ)) / (k : ℚ)) atTop (𝓝 1) := by
    have := hdk.const_add (1 : ℚ)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk0
    have : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    field_simp
  have h2 : Tendsto (fun k : ℕ => (k : ℚ) / ((k : ℚ) + (d : ℚ))) atTop (𝓝 1) := by
    have hsub : Tendsto (fun k : ℕ => 1 - (d : ℚ) / ((k : ℚ) + (d : ℚ))) atTop (𝓝 1) := by
      have hd : Tendsto (fun k : ℕ => (d : ℚ) / ((k : ℚ) + (d : ℚ))) atTop (𝓝 0) :=
        hkd.const_div_atTop _
      simpa using hd.const_sub (1 : ℚ)
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk0
    have hne : (k : ℚ) + (d : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  constructor
  · intro H
    have key : Tendsto (fun k : ℕ =>
        ((c : ℚ) + (a k : ℚ)) / ((k : ℚ) + (d : ℚ)) * (((k : ℚ) + (d : ℚ)) / (k : ℚ))
          - (c : ℚ) / (k : ℚ)) atTop (𝓝 (L * 1 - 0)) := by
      refine ((H.congr ?_).mul h1).sub hck
      intro k; push_cast; ring_nf
    rw [mul_one, sub_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk0
    have hkne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    have hne : (k : ℚ) + (d : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  · intro H
    have key : Tendsto (fun k : ℕ =>
        (a k : ℚ) / (k : ℚ) * ((k : ℚ) / ((k : ℚ) + (d : ℚ)))
          + (c : ℚ) / ((k : ℚ) + (d : ℚ))) atTop (𝓝 (L * 1 + 0)) :=
      (H.mul h2).add hcd
    rw [mul_one, add_zero] at key
    refine (key.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with k hk0
    have hkne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    have hne : (k : ℚ) + (d : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The note's *word* form of the density and the parity form `CC.U_orbit_density` agree:
`⟨n₀⟩` contributes only a bounded prefix, and by Proposition 15 each further step appends a `1`
exactly when the current value is odd.  So Question 17 is a statement of the same shape as
Proposition 6, with `U` in place of `T` and "odd" in place of "even". -/
theorem digitOneDensity_iff_U_orbit_density (n₀ : ℕ) :
    DigitOneDensity n₀ ↔ U_orbit_density n₀ := by
  have h : digitOneRatio n₀ = fun k =>
      ((numOnes n₀ + numOddU k n₀ : ℕ) : ℚ) / (((digits₃₂ n₀).length + k : ℕ) : ℚ) := by
    funext k
    rw [digitOneRatio, numOnes_U_iter, length_digits₃₂_U_iter]
  unfold DigitOneDensity U_orbit_density
  rw [h]
  exact tendsto_shift_ratio_iff

/-- Question 17's density statement, in the note's words, is `CC.conjecture_U_orbit_density`. -/
theorem forall_digitOneDensity_iff :
    (∀ n₀ : ℕ, DigitOneDensity n₀) ↔ conjecture_U_orbit_density := by
  unfold conjecture_U_orbit_density
  exact forall_congr' fun n₀ => digitOneDensity_iff_U_orbit_density n₀

/-- Conjecture 18, in the note's words — the proportion of digits `1` in the length-`k` word
`⟨sat(k)⟩` — is `CC.conjecture_4_2`. -/
theorem digitOneDensity_zero_iff_conjecture_4_2 : DigitOneDensity 0 ↔ conjecture_4_2 :=
  (digitOneDensity_iff_U_orbit_density 0).trans conjecture_4_2_eq_U_orbit_zero.symm

/-! ## The conjectures as density statements

"The proportion of `1`s tends to `1/2`" is, verbatim, "the set of positions carrying a `1` has
natural density `1/2`".  `ForMathlib/Combinatorics/NatDensity.lean` supplies `HasNatDensity`
(Mathlib has only Schnirelmann density), and this section reads all three statements of [EVG25]
through it. -/

theorem numOddU_eq_natDensityCount (k n₀ : ℕ) :
    numOddU k n₀ = natDensityCount {j | U_iter j n₀ % 2 = 1} k := rfl

/-- Question 17's density at a fixed starting point: the odd steps of the `U`-orbit of `n₀` —
equivalently, by `digitOneDensity_iff_U_orbit_density`, the positions of the digit `1` in the
word written by that orbit — have density `1/2`. -/
theorem U_orbit_density_iff_hasNatDensity (n₀ : ℕ) :
    U_orbit_density n₀ ↔ HasNatDensity {j | U_iter j n₀ % 2 = 1} (1 / 2) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num, hasNatDensity_iff_ratCast]
  rfl

/-- **Question 17** as a density statement. -/
theorem conjecture_U_orbit_density_iff_hasNatDensity :
    conjecture_U_orbit_density ↔ ∀ n₀ : ℕ, HasNatDensity {j | U_iter j n₀ % 2 = 1} (1 / 2) := by
  unfold conjecture_U_orbit_density
  exact forall_congr' fun n₀ => U_orbit_density_iff_hasNatDensity n₀

/-- **Conjecture 18** as a density statement: the digits `1` of the saturated word
`⟨sat(∞)⟩` sit at a set of positions of density `1/2` — i.e. `⟨sat(∞)⟩` is *simply normal*, the
length-one case of the normality asserted by Conjecture 19 (`CC.conjecture_4_3`). -/
theorem conjecture_4_2_iff_hasNatDensity :
    conjecture_4_2 ↔ HasNatDensity {j | sat j % 2 = 1} (1 / 2) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num, hasNatDensity_iff_ratCast]
  rfl

/-- The note's word form of Question 17, through the density. -/
theorem digitOneDensity_iff_hasNatDensity (n₀ : ℕ) :
    DigitOneDensity n₀ ↔ HasNatDensity {j | U_iter j n₀ % 2 = 1} (1 / 2) :=
  (digitOneDensity_iff_U_orbit_density n₀).trans (U_orbit_density_iff_hasNatDensity n₀)

/-- `CC.num_odd_steps` counts the odd iterates of `T` below `k`. -/
theorem num_odd_steps_eq_natDensityCount (k n : ℕ) :
    num_odd_steps k n = natDensityCount {j | T_iter j n % 2 = 1} k := by
  unfold num_odd_steps natDensityCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (T_iter i n) with h | h
  · simp [X_even h, h]
  · simp [X_odd h, h]

theorem natDensityCount_even_add_num_odd_steps (k n : ℕ) :
    natDensityCount {j | T_iter j n % 2 = 0} k + num_odd_steps k n = k := by
  rw [num_odd_steps_eq_natDensityCount]
  unfold natDensityCount
  have h : ({a ∈ Finset.range k | a ∈ {j | T_iter j n % 2 = 1}} : Finset ℕ)
      = {a ∈ Finset.range k | ¬ a ∈ {j | T_iter j n % 2 = 0}} :=
    Finset.filter_congr fun a _ => by simp only [Set.mem_ofPred_eq]; omega
  rw [h]
  simpa using
    Finset.card_filter_add_card_filter_not (s := Finset.range k)
      (p := (· ∈ {j | T_iter j n % 2 = 0}))

/-- [EVG25] Conjecture 5, at a fixed starting point, as a density statement. -/
theorem tendsto_even_ratio_iff_hasNatDensity (n : ℕ) :
    Tendsto (fun k => ((k - num_odd_steps k n : ℕ) : ℚ) / (k : ℚ)) atTop (𝓝 (1 / 2 : ℚ)) ↔
      HasNatDensity {j | T_iter j n % 2 = 0} (1 / 2) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num, hasNatDensity_iff_ratCast]
  have h : ∀ k, k - num_odd_steps k n = natDensityCount {j | T_iter j n % 2 = 0} k := by
    intro k; have := natDensityCount_even_add_num_odd_steps k n; omega
  simp only [h]

/-- **[EVG25] Proposition 6** as a density statement: the Collatz conjecture is equivalent to
"for every `n ≥ 1`, the even iterates of `T` from `n` have density `1/2`".  This is `CC`'s
`conjecture_2_4_iff_2_5` read through `HasNatDensity`. -/
theorem collatz_iff_hasNatDensity_even :
    (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1) ↔
      ∀ n : ℕ, n ≥ 1 → HasNatDensity {j | T_iter j n % 2 = 0} (1 / 2) := by
  rw [conjecture_2_4_iff_2_5]
  exact forall_congr' fun n => imp_congr_right fun _ => tendsto_even_ratio_iff_hasNatDensity n

/-! ## Sanity checks -/

/-- `⟨5⟩ = 2101` ([EVG25] Table 1), written here least significant digit first — a word with a
digit `0`, which no `U`-step ever adds. -/
@[category test, AMS 11]
theorem digits₃₂_five : digits₃₂ 5 = [1, 0, 1, 2] := by
  rw [digits₃₂_pos 5 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 3 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 2 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 1 (by norm_num)]; norm_num [lsd, parent, digits₃₂_zero]

/-- `⟨26⟩ = 2122111` ([EVG25] Table 2, `k = 7`), written here least significant digit first. -/
@[category test, AMS 11]
theorem digits₃₂_sat_seven : digits₃₂ (sat 7) = [1, 1, 1, 2, 2, 1, 2] := by
  rw [sat_seven]
  rw [digits₃₂_pos 26 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 17 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 11 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 7 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 4 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 2 (by norm_num)]; norm_num [lsd, parent]
  rw [digits₃₂_pos 1 (by norm_num)]; norm_num [lsd, parent, digits₃₂_zero]

/-! ## The open questions -/

/--
**Question 17** of [EVG25], the concrete instance it proposes: *starting with any `n₀ ∈ ℕ`, is it
true that the proportion of `1`'s in `⟨U^{(k)}(n₀)⟩` tends to `1/2` as `k` goes to infinity, as
supported by numerical evidence?*  (`forall_digitOneDensity_iff` is the note's own phrasing of
`conjecture_U_orbit_density`, in digits of the word.)

Numerical evidence in the note: for `n₀ = 0` and `k = 2^20`, the word `⟨sat(2^20)⟩` has 525,067
digits `1` against 523,509 digits `2`.
-/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_q17"]
theorem question_17.parts.i : conjecture_U_orbit_density ↔ answer(sorry) := by
  sorry

/--
**Question 17** of [EVG25], the equivalence it asks about: *is the Collatz conjecture equivalent
to some behaviour of the iteration of the function `U`?* — stated for the concrete behaviour the
note proposes.  (The note's own comment, after Conjecture 18, is that the question "arises from
the close relationship between the functions `T` and `U`, Remark 14" — `U n ≡ T n + n + 1
[MOD 2]`, `CC.Base3div2.U_mod_two` — "and the analogy with Conjecture 5", and that "even if not
equivalent to Conjecture 5, Conjecture 18 might well be of the same order of difficulty".)
-/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_q17"]
theorem question_17.parts.ii :
    (conjecture_U_orbit_density ↔ (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1)) ↔
      answer(sorry) := by
  sorry

/-- One half of `question_17.parts.ii`: does the Collatz conjecture imply the density statement
for `U`?  Note that no `U`-orbit is eventually periodic (`lt_U`), so the collapse to the cycle
`1, 2` that proves the easy half of Proposition 6 has no counterpart here. -/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_q17"]
theorem question_17.variants.collatz_imp_density :
    ((∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1) → conjecture_U_orbit_density) ↔
      answer(sorry) := by
  sorry

/-- The other half of `question_17.parts.ii`: does the density statement for `U` imply the
Collatz conjecture? -/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_q17"]
theorem question_17.variants.density_imp_collatz :
    (conjecture_U_orbit_density → (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1)) ↔
      answer(sorry) := by
  sorry

/--
The question [EVG25] asks immediately after **Conjecture 18**: *is Conjecture 18 equivalent to
the Collatz conjecture?*  Conjecture 18 is the `n₀ = 0` case of Question 17, about the digits of
the saturated word `⟨sat(∞)⟩` (`digitOneDensity_zero_iff_conjecture_4_2`).
-/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_c18"]
theorem conjecture_18.variants.iff_collatz :
    (conjecture_4_2 ↔ (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1)) ↔ answer(sorry) := by
  sorry

/-- One half of `conjecture_18.variants.iff_collatz`: does Conjecture 18 imply the Collatz
conjecture?  (Formally weaker than `question_17.variants.density_imp_collatz`, whose hypothesis
is the density at *every* starting point rather than at `0` alone.) -/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_c18"]
theorem conjecture_18.variants.imp_collatz :
    (conjecture_4_2 → (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1)) ↔ answer(sorry) := by
  sorry

/-- The other half: does the Collatz conjecture imply Conjecture 18?  (Formally weaker than
`question_17.variants.collatz_imp_density`, whose conclusion is the density at every starting
point.) -/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_c18"]
theorem conjecture_18.variants.collatz_imp :
    ((∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1) → conjecture_4_2) ↔ answer(sorry) := by
  sorry

/-- Conjecture 18 itself is open as well. -/
@[category research open, AMS 11 68, ref "EVG25", group "evg25_c18"]
theorem conjecture_18 : conjecture_4_2 ↔ answer(sorry) := by
  sorry

end EVG25
