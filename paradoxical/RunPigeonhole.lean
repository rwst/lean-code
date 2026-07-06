/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import paradoxical.Defs
import paradoxical.ExcursionBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The run-length pigeonhole — discharging `hpigeon`

Assembles the excursion lower bound `2^{j/(2R)} - 1 ≤ Exc` (hypothesis `hpigeon`
of `Paradoxical.finite_of_pigeonhole`) for the `R`-circuit paradoxical slice.

Given a shape `S` (a `List (ℕ × ℕ)` of circuits, `R = S.length`) with `n`'s
length-`j` parity word equal to the shape word (`pbits (wlen S) n = wordOfShape S`,
`j = wlen S`):

* `burst_odd_run` / `gap_even_run` — each circuit's burst / gap is a genuine run
  of odd / even orbit steps at its position in the word (via `pbits_getElem?`);
* `exists_ge_avg` — pigeonhole: some part of the shape is `≥` the average
  `wlen S / (2R)`;
* `shape_excursion_bound` — combining with the value bounds of `ExcursionBounds`,
  some orbit term `Tᵖ(n)` (`p ≤ j`) satisfies `2^L - 1 ≤ Tᵖ(n)` with `2R·L ≥ j`;
* `excWin` — the windowed excursion `maxₖ≤ⱼ Tᵏ(n)` (a `ℕ`, hence a real);
* `pigeonhole_hyp` — the real inequality `(2:ℝ)^{j/(2R)} - 1 ≤ excWin j n`, exactly
  `hpigeon` with `Exc j n := excWin j n`.

This discharges one of the two open hypotheses of `finite_of_pigeonhole` (the other,
`hmH : m ≤ C·j^{14.3}`, is discharged by the Rhin polynomial bound in `RhinPolyBound.lean`).

`sorry`-free (`propext, Classical.choice, Quot.sound`).
-/

namespace Paradoxical

open CC

/-! ### Each circuit's burst / gap is a run of odd / even steps -/

/-- Circuit `i`'s burst is a run of `aᵢ` odd steps starting at `wlen (S.take i)`. -/
lemma burst_odd_run (S : List (ℕ × ℕ)) (n i : ℕ) (hi : i < S.length)
    (hshape : pbits (wlen S) n = wordOfShape S) :
    ∀ k, k < (S[i]'hi).1 → T_iter (wlen (S.take i) + k) n % 2 = 1 := by
  intro k hk
  have hAlen : (wordOfShape (S.take i)).length = wlen (S.take i) := wordOfShape_length _
  refine odd_of_word_bit_one S n _ hshape ?_
  rw [wordOfShape_split S i hi, List.getElem?_append_right (by rw [hAlen]; omega), hAlen,
    show wlen (S.take i) + k - wlen (S.take i) = k by omega,
    List.getElem?_append_left (by rw [List.length_replicate]; exact hk), List.getElem?_replicate]
  simp [hk]

/-- Circuit `i`'s gap is a run of `eᵢ` even steps starting at `wlen (S.take i) + aᵢ`. -/
lemma gap_even_run (S : List (ℕ × ℕ)) (n i : ℕ) (hi : i < S.length)
    (hshape : pbits (wlen S) n = wordOfShape S) :
    ∀ k, k < (S[i]'hi).2 → T_iter (wlen (S.take i) + (S[i]'hi).1 + k) n % 2 = 0 := by
  intro k hk
  have hAlen : (wordOfShape (S.take i)).length = wlen (S.take i) := wordOfShape_length _
  refine even_of_word_bit_zero S n _ hshape ?_
  rw [wordOfShape_split S i hi, List.getElem?_append_right (by rw [hAlen]; omega), hAlen,
    show wlen (S.take i) + (S[i]'hi).1 + k - wlen (S.take i) = (S[i]'hi).1 + k by omega,
    List.getElem?_append_right (by rw [List.length_replicate]; omega), List.length_replicate,
    show (S[i]'hi).1 + k - (S[i]'hi).1 = k by omega,
    List.getElem?_append_left (by rw [List.length_replicate]; exact hk), List.getElem?_replicate]
  simp [hk]

/-! ### Pigeonhole and the excursion bound -/

/-- Some element of a nonempty `ℕ`-list is at least the average. -/
lemma exists_ge_avg (l : List ℕ) (hl : l ≠ []) : ∃ x ∈ l, l.sum ≤ l.length * x := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
      by_cases ht : t = []
      · subst ht; exact ⟨a, by simp, by simp⟩
      · obtain ⟨x, hx_mem, hx⟩ := ih ht
        refine ⟨max a x, ?_, ?_⟩
        · rcases le_total a x with h | h
          · rw [max_eq_right h]; exact List.mem_cons_of_mem _ hx_mem
          · rw [max_eq_left h]; exact List.mem_cons_self ..
        · rw [List.sum_cons, List.length_cons]
          have h2 : t.length * x ≤ t.length * max a x := Nat.mul_le_mul_left _ (le_max_right a x)
          nlinarith [hx, le_max_left a x, h2]

/-- **Run-length pigeonhole ⟹ excursion.** Some orbit term `Tᵖ(n)` with `p ≤ wlen S`
satisfies `2^L - 1 ≤ Tᵖ(n)` for a run length `L` with `wlen S ≤ 2·(S.length)·L`. -/
theorem shape_excursion_bound (S : List (ℕ × ℕ)) (n : ℕ) (hn : 1 ≤ n) (hS : S ≠ [])
    (hshape : pbits (wlen S) n = wordOfShape S) :
    ∃ L p : ℕ, wlen S ≤ 2 * S.length * L ∧ p ≤ wlen S ∧ 2 ^ L - 1 ≤ T_iter p n := by
  obtain ⟨x, hx_mem, hx_le⟩ :=
    exists_ge_avg (S.map (fun p => p.1 + p.2)) (by simp only [ne_eq, List.map_eq_nil_iff]; exact hS)
  rw [List.mem_map] at hx_mem
  obtain ⟨p, hp_mem, hp_eq⟩ := hx_mem
  obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hp_mem
  have hsum : (S.map (fun p => p.1 + p.2)).sum = wlen S := rfl
  have hlen : (S.map (fun p => p.1 + p.2)).length = S.length := by simp
  rw [hsum, hlen, ← hp_eq] at hx_le
  -- `wlen` splits at the prefix, bounding the two run positions
  have hsplit_wlen : wlen S = wlen (S.take i) + wlen (S.drop i) := by
    conv_lhs => rw [← List.take_append_drop i S]
    rw [wlen_append]
  have hburst_le : wlen (S.take i) ≤ wlen S := by omega
  have hgap_le : wlen (S.take i) + p.1 ≤ wlen S := by
    have h2 : p.1 ≤ wlen (S.drop i) := by
      rw [List.drop_eq_getElem_cons hi, wlen_cons, hi_eq]; omega
    omega
  rcases le_total p.1 p.2 with h | h
  · -- the gap `p.2` is the larger part
    refine ⟨p.2, wlen (S.take i) + p.1, ?_, hgap_le, ?_⟩
    · calc wlen S ≤ S.length * (p.1 + p.2) := hx_le
        _ ≤ S.length * (2 * p.2) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * S.length * p.2 := by ring
    · have hdvd : 2 ^ p.2 ∣ T_iter (wlen (S.take i) + p.1) n :=
        hi_eq ▸ two_pow_dvd_of_even_run n (S[i]'hi).2 (wlen (S.take i) + (S[i]'hi).1)
          (gap_even_run S n i hi hshape)
      have := Nat.le_of_dvd (T_iter_pos hn _) hdvd
      omega
  · -- the burst `p.1` is the larger part
    refine ⟨p.1, wlen (S.take i), ?_, hburst_le, ?_⟩
    · calc wlen S ≤ S.length * (p.1 + p.2) := hx_le
        _ ≤ S.length * (2 * p.1) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * S.length * p.1 := by ring
    · have hdvd : 2 ^ p.1 ∣ (T_iter (wlen (S.take i)) n + 1) :=
        hi_eq ▸ two_pow_dvd_succ_of_odd_run n (S[i]'hi).1 (wlen (S.take i))
          (burst_odd_run S n i hi hshape)
      have := Nat.le_of_dvd (by positivity) hdvd
      omega

/-- The windowed excursion `maxₖ≤ⱼ Tᵏ(n)` (a natural number). -/
def excWin (j n : ℕ) : ℕ := (Finset.range (j + 1)).sup (fun k => T_iter k n)

/-- **`hpigeon`, discharged.** For the `R`-circuit slice (`R = S.length`, `j = wlen S`,
`pbits j n = wordOfShape S`), the excursion satisfies `(2:ℝ)^{j/(2R)} - 1 ≤ excWin j n`. -/
theorem pigeonhole_hyp (S : List (ℕ × ℕ)) (n : ℕ) (hn : 1 ≤ n) (hS : S ≠ [])
    (hshape : pbits (wlen S) n = wordOfShape S) :
    (2 : ℝ) ^ ((wlen S : ℝ) / (2 * S.length)) - 1 ≤ (excWin (wlen S) n : ℝ) := by
  obtain ⟨L, p, hL, hp_le, hterm⟩ := shape_excursion_bound S n hn hS hshape
  have hSlen : 0 < S.length := by cases S with | nil => exact absurd rfl hS | cons _ _ => simp
  have hRpos : 0 < (S.length : ℝ) := by exact_mod_cast hSlen
  -- exponent step: (2:ℝ)^{wlen/(2R)} ≤ (2:ℝ)^L
  have hexp : (2 : ℝ) ^ ((wlen S : ℝ) / (2 * S.length)) ≤ (2 : ℝ) ^ (L : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have : (wlen S : ℝ) ≤ 2 * S.length * L := by exact_mod_cast hL
    nlinarith [this]
  have hcast : (2 : ℝ) ^ (L : ℝ) = ((2 ^ L : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
  -- term step: 2^L - 1 ≤ Tᵖ(n) ≤ excWin
  have hle_win : T_iter p n ≤ excWin (wlen S) n := by
    unfold excWin
    exact Finset.le_sup (f := fun k => T_iter k n) (b := p) (Finset.mem_range.mpr (by omega))
  have hterm_win : ((2 ^ L - 1 : ℕ) : ℝ) ≤ (excWin (wlen S) n : ℝ) := by
    exact_mod_cast le_trans hterm hle_win
  have hcast2 : ((2 ^ L - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (L : ℝ) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, hcast]; push_cast; ring
  calc (2 : ℝ) ^ ((wlen S : ℝ) / (2 * S.length)) - 1
      ≤ (2 : ℝ) ^ (L : ℝ) - 1 := by linarith [hexp]
    _ = ((2 ^ L - 1 : ℕ) : ℝ) := hcast2.symm
    _ ≤ (excWin (wlen S) n : ℝ) := hterm_win

end Paradoxical
