/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Basic

/-!
# Proposition C(1)–(2): under (H) the expansion is eventually confined to a proper SFT

Under the standing hypothesis (H) of Problem 10.47 — `u` not eventually periodic with
`p_∞(n, u) = n + 1` — the word is eventually trapped in an explicit *proper subshift of finite
type*:

* **(1)** exactly two letters occur infinitely often, so past the horizon `s_1` the word uses only
  those two and the remaining `#α - 2` letters are **eventually omitted**
  (`BB47.eventually_two_letters`, `BB47.ncard_omitted`, `BB47.exists_omitted_letter`).  In base
  `b ≥ 3` this is "the expansion eventually omits `b - 2` digits".
* **(2)** of the two letters `a`, `b` one satisfies: past the horizon `s_2` the block `aa` never
  occurs (`BB47.exists_pair_forbidden_square`).  In base `2` this is "the tail avoids `11`, or it
  avoids `00`" — the tail lies in the **golden-mean subshift of finite type**.

Together with `BB47/TheoremZ.lean` this places Problem 10.47 below Mahler's missing-digit
problem: if no algebraic irrational has an expansion eventually confined to a proper subshift of
finite type, then no algebraic irrational satisfies (H), in any base.

## What the proof needs, and what it does not

Only `p_∞(1) = 2` for (1), and `p_∞(2) = 3` together with aperiodicity for (2) — and by the
rigidity lemma `BB47.pInf_eq_succ_of_le` the second hypothesis implies the first, so (2) is stated
with `pInf u 2 = 3` alone.

The note `BB47/af.md` §2.2, and after it `plans/plan2-1047.html` §3.2, derived (2) from
`p_∞(2) = 3` *plus balance* ([M3, Cor. 4.2]), i.e. through the Theorem-B chain, which is not
formalized.  **That detour is unnecessary.**  `p_∞(2) = 3` leaves exactly one non-recurrent
`2`-block among `aa`, `ab`, `ba`, `bb`, and it cannot be one of the two *mixed* blocks: if `ab`
recurred only finitely often then, past the last occurrence and past `s_1`, no `a` could ever be
followed by a `b`, so an `a` occurring there would be followed by `a` forever and otherwise the
word would be `b` forever — eventually periodic either way
(`BB47.isEventuallyPeriodic_of_no_transition`).  So the missing block is `aa` or `bb`, which is
the golden-mean statement.  The whole argument is `p_∞` and the horizon; no Rauzy graph, no
balance, no structure theorem.

## Main results

* `BB47.recLetters` — the set of letters occurring infinitely often, and
  `BB47.ncard_recLetters` : `#(recLetters u) = p_∞(1, u)`.
* `BB47.eventually_two_letters` — **Proposition C(1)**: `p_∞(1) = 2` gives two distinct letters
  carrying the word past `s_1`, and every other letter is eventually omitted.
* `BB47.ncard_omitted`, `BB47.exists_omitted_letter` — the count `#α - 2` of omitted letters, and
  the existence of one when `#α ≥ 3`.
* `BB47.isEventuallyPeriodic_of_no_transition` — the engine of (2).
* `BB47.exists_forbidden_square` — **Proposition C(2)**: some recurrent letter `c` has `cc`
  non-recurrent.
* `BB47.exists_pair_forbidden_square`, `BB47.exists_pair_forbidden_square_of_frequently` — (1) and
  (2) packaged: two letters `a ≠ b` with `u i ∈ {a, b}` past `s_1` and no `aa` past `s_2`.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, CUP 2012 — Problem 10.47, p. 221.
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, *On the irrationality exponent of real numbers with
  low complexity expansion*, arXiv:2510.17177 — §2.2 (the non-recurrent prefix).
* [M3] `BB47/M3.tex` (this repository, 2026-09) — the standing hypothesis (H), Lem. 3.1.
* [M5] `BB47/M5.tex` (this repository, 2026-09) — Prop. 4.6, of which this file is items (1)
  and (2); item (3), the nested self-similar sets, is not formalized.
* [af] `BB47/af.md` §2.2, merged as `plans/plan2-1047.html` §3.2 — the statement, with the
  superfluous balance hypothesis corrected here.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {α : Type*} [Finite α]

/-! ## The letters that recur -/

/-- The set of letters occurring at arbitrarily late positions of `u`, i.e. infinitely often.
Under (H) this set has exactly two elements. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
def recLetters (u : ℕ → α) : Set α := {a | ∀ N, ∃ i, N ≤ i ∧ u i = a}

omit [Finite α] in
@[simp, category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma mem_recLetters {u : ℕ → α} {a : α} :
    a ∈ recLetters u ↔ ∀ N, ∃ i, N ≤ i ∧ u i = a := Iff.rfl

omit [Finite α] in
/-- A length-`1` block is the constant function at the letter it reads. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma factor_one_eq {u : ℕ → α} {i : ℕ} : factor u 1 i = fun _ => u i := by
  funext s; simp [factor]

omit [Finite α] in
/-- A length-`2` block is the pair of letters it reads. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma factor_two_eq_iff {u : ℕ → α} {i : ℕ} {x y : α} :
    factor u 2 i = ![x, y] ↔ u i = x ∧ u (i + 1) = y := by
  constructor
  · intro h
    exact ⟨by simpa [factor] using congrFun h 0, by simpa [factor] using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext s
    fin_cases s <;> simp [factor, h0, h1]

omit [Finite α] in
/-- Recurrence of a letter is recurrence of the corresponding length-`1` block. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma recurrent_one_iff {u : ℕ → α} {a : α} :
    Recurrent u 1 (fun _ => a) ↔ a ∈ recLetters u := by
  constructor
  · intro h N
    obtain ⟨i, hi, hfi⟩ := h N
    exact ⟨i, hi, by simpa [factor_one_eq] using congrFun hfi 0⟩
  · intro h N
    obtain ⟨i, hi, hui⟩ := h N
    exact ⟨i, hi, by rw [factor_one_eq, hui]⟩

omit [Finite α] in
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma recFactorSet_one (u : ℕ → α) :
    recFactorSet u 1 = (fun a : α => (fun _ => a : Fin 1 → α)) '' recLetters u := by
  ext v
  constructor
  · intro hv
    refine ⟨v 0, ?_, ?_⟩
    · rw [← recurrent_one_iff]
      have h : (fun _ => v 0 : Fin 1 → α) = v := by funext s; rw [Subsingleton.elim s 0]
      rwa [h]
    · funext s; rw [Subsingleton.elim s 0]
  · rintro ⟨a, ha, rfl⟩
    exact recurrent_one_iff.mpr ha

/-- `p_∞(1, u)` **is** the number of letters occurring infinitely often. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem ncard_recLetters (u : ℕ → α) : (recLetters u).ncard = pInf u 1 := by
  rw [pInf, recFactorSet_one, Set.ncard_image_of_injective _ (fun _ _ h => congrFun h 0)]

/-- Past the horizon `s_1` every letter read is a recurrent one. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem mem_recLetters_of_horizon_le {u : ℕ → α} {i : ℕ} (h : horizon u 1 ≤ i) :
    u i ∈ recLetters u := by
  have h2 := recurrent_of_horizon_le (u := u) (n := 1) h
  rw [factor_one_eq] at h2
  exact recurrent_one_iff.mp h2

omit [Finite α] in
/-- A letter that does not recur is *eventually omitted*. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma not_mem_recLetters_iff {u : ℕ → α} {a : α} :
    a ∉ recLetters u ↔ ∃ N, ∀ i, N ≤ i → u i ≠ a := by
  simp only [recLetters, Set.mem_ofPred_eq, not_forall, not_exists, not_and]

@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
lemma eq_or_eq_of_horizon_le {u : ℕ → α} {a b : α} (hab : recLetters u = {a, b}) {i : ℕ}
    (hi : horizon u 1 ≤ i) : u i = a ∨ u i = b := by
  have hmem := mem_recLetters_of_horizon_le (u := u) (i := i) hi
  rw [hab] at hmem
  simpa using hmem

/-! ## Proposition C(1): the expansion is eventually two-letter -/

/-- **Proposition C(1)** [M5, Prop. 4.6(1)].  If exactly two letters recur — which is `p_∞(1) = 2`,
hence a consequence of (H) — then past the horizon `s_1` the word reads only those two letters,
and every other letter of the alphabet is omitted from that point on.

For the `b`-ary expansion of an irrational satisfying (H) this says that the expansion is
*eventually two-digit*: in base `b ≥ 3` it eventually omits `b - 2` of the digits. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem eventually_two_letters {u : ℕ → α} (h1 : pInf u 1 = 2) :
    ∃ a b : α, a ≠ b ∧ (∀ i, horizon u 1 ≤ i → u i = a ∨ u i = b) ∧
      ∀ c : α, c ≠ a → c ≠ b → ∀ i, horizon u 1 ≤ i → u i ≠ c := by
  obtain ⟨a, b, hne, hab⟩ :=
    Set.ncard_eq_two.mp (show (recLetters u).ncard = 2 by rw [ncard_recLetters, h1])
  refine ⟨a, b, hne, fun i hi => eq_or_eq_of_horizon_le hab hi, fun c hca hcb i hi hui => ?_⟩
  rcases eq_or_eq_of_horizon_le hab hi with h | h
  · exact hca (hui ▸ h)
  · exact hcb (hui ▸ h)

/-- The omitted letters are counted exactly: `#α - 2` of them. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem ncard_omitted {u : ℕ → α} (h1 : pInf u 1 = 2) :
    {c : α | ∃ N, ∀ i, N ≤ i → u i ≠ c}.ncard = Nat.card α - 2 := by
  have hcompl : {c : α | ∃ N, ∀ i, N ≤ i → u i ≠ c} = (recLetters u)ᶜ := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, recLetters, not_forall, not_exists, not_and]
  have hsum := Set.ncard_add_ncard_compl (recLetters u)
  rw [ncard_recLetters, h1] at hsum
  rw [hcompl]
  omega

/-- In base `b ≥ 3`: some digit is omitted from the horizon on. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem exists_omitted_letter {u : ℕ → α} (h1 : pInf u 1 = 2) (hcard : 3 ≤ Nat.card α) :
    ∃ c : α, ∀ i, horizon u 1 ≤ i → u i ≠ c := by
  have hsum := Set.ncard_add_ncard_compl (recLetters u)
  rw [ncard_recLetters, h1] at hsum
  obtain ⟨c, hc⟩ : (recLetters u)ᶜ.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  exact ⟨c, fun i hi hui => hc (hui ▸ mem_recLetters_of_horizon_le hi)⟩

/-! ## Proposition C(2): the tail avoids a square -/

omit [Finite α] in
/-- **The engine of Proposition C(2).**  If, from some position on, the word reads only `a` and
`b` and never reads `a` followed by `b`, then it is eventually periodic: an `a` occurring there is
followed by `a` forever, and if no `a` occurs the word is `b` forever.

This is what forbids a *mixed* block from being the non-recurrent one, and it is the only place
aperiodicity is used. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem isEventuallyPeriodic_of_no_transition {u : ℕ → α} {a b : α} {N : ℕ}
    (htwo : ∀ i, N ≤ i → u i = a ∨ u i = b)
    (hno : ∀ i, N ≤ i → ¬(u i = a ∧ u (i + 1) = b)) : IsEventuallyPeriodic u := by
  by_cases hex : ∃ i, N ≤ i ∧ u i = a
  · obtain ⟨i₀, hi₀, hu₀⟩ := hex
    have key : ∀ k, u (i₀ + k) = a := by
      intro k
      induction k with
      | zero => simpa using hu₀
      | succ k ih =>
        have hik : N ≤ i₀ + k := le_trans hi₀ (Nat.le_add_right _ _)
        have hne : u (i₀ + k + 1) ≠ b := fun hb => hno (i₀ + k) hik ⟨ih, hb⟩
        rcases htwo (i₀ + k + 1) (by omega) with h | h
        · rw [show i₀ + (k + 1) = i₀ + k + 1 by omega]; exact h
        · exact absurd h hne
    refine ⟨i₀, 1, one_pos, fun k hk => ?_⟩
    have h1 : u k = a := by
      have := key (k - i₀); rwa [show i₀ + (k - i₀) = k by omega] at this
    have h2 : u (k + 1) = a := by
      have := key (k + 1 - i₀); rwa [show i₀ + (k + 1 - i₀) = k + 1 by omega] at this
    rw [h1, h2]
  · push Not at hex
    refine ⟨N, 1, one_pos, fun k hk => ?_⟩
    have h1 : u k = b := by
      rcases htwo k hk with h | h
      · exact absurd h (hex k hk)
      · exact h
    have h2 : u (k + 1) = b := by
      rcases htwo (k + 1) (by omega) with h | h
      · exact absurd h (hex _ (by omega))
      · exact h
    rw [h1, h2]

/-- Both **mixed** blocks recur: `ab` is recurrent whenever `a`, `b` are the two recurrent letters
of a word that is not eventually periodic. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem recurrent_two_of_pair {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) {a b : α}
    (hab : recLetters u = {a, b}) : Recurrent u 2 ![a, b] := by
  by_contra hcon
  rw [Recurrent] at hcon
  push Not at hcon
  obtain ⟨N₀, hN₀⟩ := hcon
  refine hu (isEventuallyPeriodic_of_no_transition (a := a) (b := b)
    (N := max N₀ (horizon u 1)) ?_ ?_)
  · intro i hi
    exact eq_or_eq_of_horizon_le hab (le_trans (le_max_right _ _) hi)
  · intro i hi hcc
    exact hN₀ i (le_trans (le_max_left _ _) hi) (factor_two_eq_iff.mpr hcc)

omit [Finite α] in
/-- Both letters of a recurrent length-`2` block recur. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma recurrent_two_mem {u : ℕ → α} {v : Fin 2 → α} (h : Recurrent u 2 v) :
    v 0 ∈ recLetters u ∧ v 1 ∈ recLetters u := by
  refine ⟨fun N => ?_, fun N => ?_⟩
  · obtain ⟨i, hi, hfi⟩ := h N
    exact ⟨i, hi, by simpa [factor] using congrFun hfi 0⟩
  · obtain ⟨i, hi, hfi⟩ := h N
    exact ⟨i + 1, by omega, by simpa [factor] using congrFun hfi 1⟩

omit [Finite α] in
/-- With only two recurrent letters there are at most four recurrent `2`-blocks. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
lemma recFactorSet_two_subset {u : ℕ → α} {a b : α} (hab : recLetters u = {a, b}) :
    recFactorSet u 2 ⊆ {![a, a], ![a, b], ![b, a], ![b, b]} := by
  intro v hv
  obtain ⟨h0, h1⟩ := recurrent_two_mem hv
  rw [hab] at h0 h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1
  have hveta : v = ![v 0, v 1] := by funext s; fin_cases s <;> simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [hveta, h0, h1] <;> tauto

/-- **Proposition C(2)** [M5, Prop. 4.6(2)].  If `p_∞(2, u) = 3` and `u` is not eventually
periodic, then one of the two recurrent letters `c` has its square `cc` **non-recurrent**.

Only three of the four blocks `aa`, `ab`, `ba`, `bb` recur, and the two mixed ones must be among
them by `recurrent_two_of_pair`; so the missing one is a square. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem exists_forbidden_square {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (h2 : pInf u 2 = 3) :
    ∃ c : α, c ∈ recLetters u ∧ ¬ Recurrent u 2 ![c, c] := by
  have h1 : pInf u 1 = 2 := pInf_eq_succ_of_le hu (show pInf u 2 = 2 + 1 by omega) (by omega)
  obtain ⟨a, b, hne, hab⟩ :=
    Set.ncard_eq_two.mp (show (recLetters u).ncard = 2 by rw [ncard_recLetters, h1])
  by_contra hcon
  push Not at hcon
  have ha : a ∈ recLetters u := by rw [hab]; exact Set.mem_insert _ _
  have hb : b ∈ recLetters u := by rw [hab]; exact Set.mem_insert_of_mem _ rfl
  have hAA : Recurrent u 2 ![a, a] := hcon a ha
  have hBB : Recurrent u 2 ![b, b] := hcon b hb
  have hAB : Recurrent u 2 ![a, b] := recurrent_two_of_pair hu hab
  have hBA : Recurrent u 2 ![b, a] := recurrent_two_of_pair hu (hab.trans (Set.pair_comm a b))
  have hsup : ({![a, a], ![a, b], ![b, a], ![b, b]} : Set (Fin 2 → α)) ⊆ recFactorSet u 2 := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    exacts [hAA, hAB, hBA, hBB]
  have heq : recFactorSet u 2 = {![a, a], ![a, b], ![b, a], ![b, b]} :=
    Set.Subset.antisymm (recFactorSet_two_subset hab) hsup
  have h4 : pInf u 2 = 4 := by
    rw [pInf, heq,
      Set.ncard_insert_of_notMem (by simp [Matrix.vecCons_inj, hne]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [Matrix.vecCons_inj, hne]) (Set.toFinite _),
      Set.ncard_pair (by simp [Matrix.vecCons_inj, hne])]
  omega

/-- A non-recurrent square is **avoided past the horizon** `s_2`: this is the subshift-of-finite-
type statement. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem not_square_of_horizon_le {u : ℕ → α} {c : α} (h : ¬ Recurrent u 2 ![c, c]) {i : ℕ}
    (hi : horizon u 2 ≤ i) : ¬ (u i = c ∧ u (i + 1) = c) := by
  intro hcc
  have hrec := recurrent_of_horizon_le (u := u) (n := 2) hi
  rw [factor_two_eq_iff.mpr hcc] at hrec
  exact h hrec

/-- **Proposition C(1)–(2) packaged.**  For a word that is not eventually periodic with
`p_∞(2) = 3` there are two distinct letters `a ≠ b` such that

* past the horizon `s_1` every letter read is `a` or `b`, and
* past the horizon `s_2` the block `aa` never occurs.

In base `2` this is exactly "the tail lies in the golden-mean subshift of finite type"; in base
`b ≥ 3` the first clause already confines the tail to a two-letter subalphabet. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem exists_pair_forbidden_square {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u)
    (h2 : pInf u 2 = 3) :
    ∃ a b : α, a ≠ b ∧ recLetters u = {a, b} ∧
      (∀ i, horizon u 1 ≤ i → u i = a ∨ u i = b) ∧
      (∀ i, horizon u 2 ≤ i → ¬(u i = a ∧ u (i + 1) = a)) := by
  have h1 : pInf u 1 = 2 := pInf_eq_succ_of_le hu (show pInf u 2 = 2 + 1 by omega) (by omega)
  obtain ⟨c, hc, hcc⟩ := exists_forbidden_square hu h2
  obtain ⟨a, b, hne, hab⟩ :=
    Set.ncard_eq_two.mp (show (recLetters u).ncard = 2 by rw [ncard_recLetters, h1])
  rw [hab] at hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact ⟨c, b, hne, hab, fun i hi => eq_or_eq_of_horizon_le hab hi,
      fun i hi => not_square_of_horizon_le hcc hi⟩
  · refine ⟨c, a, hne.symm, ?_, ?_, fun i hi => not_square_of_horizon_le hcc hi⟩
    · rw [hab]; exact Set.pair_comm a c
    · intro i hi
      rcases eq_or_eq_of_horizon_le hab hi with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- The same under the hypothesis as [M3] states it: `p_∞(n) = n + 1` for **infinitely many** `n`.
-/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem exists_pair_forbidden_square_of_frequently {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u)
    (h : ∀ N, ∃ n, N ≤ n ∧ pInf u n = n + 1) :
    ∃ a b : α, a ≠ b ∧ recLetters u = {a, b} ∧
      (∀ i, horizon u 1 ≤ i → u i = a ∨ u i = b) ∧
      (∀ i, horizon u 2 ≤ i → ¬(u i = a ∧ u (i + 1) = a)) :=
  exists_pair_forbidden_square hu (by have := pInf_eq_succ_of_frequently hu h 2; omega)

end BB47
