/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineTower
import BB13.M0Verify

/-!
# Counting the failures: kernel segment + line cover (W4 of plan2-BB13)

The repaired quantitative statements for Bugeaud's Problem 10.13.  Three ingredients meet here,
each proved elsewhere and each doing what it can honestly do:

* the **certified segment** — `E ∩ [1, 256] = {1, 2, 3, 4, 7}`, five failures, kernel-verified
  against the real definition (`BB13/M0Verify.lean`, axiom-free);
* the **line cover** — the failures `n ≥ 10` lie on at most `K(ε*) = 1 856 360 182 227` lines
  (`BB13/LineCover.lean`, on the cited [BE08] Cor. 5.2);
* the **confinement** — one line carries finitely many failures, at most `a` of them over its
  least element `a` (`BB13/LineTower.lean`, elementary).

## What comes out

* `failures_high_finite` and `failures_finite_of_lineCover` — the failure set is **finite**, with
  the line cover in place of the qualitative Subspace theorem.  This is Mahler's finiteness
  re-derived along the quantitative route: the cover is a finite union, each fibre is finite by
  the elementary gap principle.  Footprint `std3 + BugeaudEvertse.ridout_line_cover` — the
  independent proof of `BB13.failures_finite` (footprint `std3 + Subspace.evertseSchlickewei`).
* `failures_card_le_of_heightBound` — **`#E ≤ 5 + H·K(ε*)`** for any `H` bounding the number of
  failures `n ≥ 257` on a single line.  The kernel segment is spliced in, so the hypothesis is
  only about the range where nothing is known; `H = 1` is what the data show
  (`BB13/m0_failures.py`: no failure at all beyond `n = 7` up to `10⁶`).
* `practical_bound_min` — the `min` of that arm and the elementary `O(log N)` tower arm.

**What is deliberately absent** is an unconditional constant.  The first version of this
development carried one, `#E ≤ C = 2.7·10¹³`, on a cited axiom that asserted an effective bound on
the number of *solutions*; [BE08] Cor. 5.2 bounds the number of *lines*, and the passage between
them is the open per-line problem.  The axiom was retired on 2026-07-21 (see
`CITED/BugeaudEvertseRidout.lean`); everything below is what survives, plus what the repair gains:
the sharp exponent `ε*` in place of `ε*/2`, hence a constant `14.6` times smaller, and the kernel
segment now carrying its own weight.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* [DD90] Delmer–Deshouillers, Math. Comp. **54** (1990) — the exact-integer scan.
* `plans/plan2-BB13.html` (W4, W7).
-/

namespace BB13

open scoped Real

/-! ### The failures above the certified range -/

/-- The failures beyond the kernel-certified segment `[1, 256]`. -/
def failuresHigh : Set ℕ := {n : ℕ | 257 ≤ n ∧ IsFailure 3 2 (3 / 4) n}

/-- The failures beyond the kernel range lying on the line of slope `r` — the fibres whose size
is the open per-line problem. -/
def highFibre (r : ℚ) : Set ℕ := {n : ℕ | 257 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem highFibre_subset_lineFibre (r : ℚ) : highFibre r ⊆ lineFibre r := by
  rintro n ⟨hn, hnf, hr⟩; exact ⟨by omega, hnf, hr⟩

/-- **The failures above the kernel range form a finite set** — with no qualitative Subspace
input: they are covered by finitely many lines (`failures_line_cover`), and each line carries
finitely many failures (`lineFibre_finite`).  Footprint `std3 + ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_high_finite : failuresHigh.Finite := by
  obtain ⟨R, -, hR⟩ := failures_line_cover
  apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => lineFibre_finite r))
  rintro n ⟨hn, hnf⟩
  exact Set.mem_biUnion (hR n (by omega) hnf) ⟨by omega, hnf, rfl⟩

/-- **The failure set is finite, via the line cover.**  A second proof of `BB13.failures_finite`
resting on the *quantitative* Ridout theorem instead of the qualitative Subspace theorem: the
failures split into the certified segment `[1, 256]` and a finite union of finite line-fibres.
Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_finite_of_lineCover : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.Finite := by
  apply Set.Finite.subset ((failuresUpTo_finite 256).union failures_high_finite)
  rintro n ⟨h1, hf⟩
  rcases le_or_gt n 256 with h | h
  · exact Or.inl ⟨h1, h, hf⟩
  · exact Or.inr ⟨by omega, hf⟩

/-! ### The conditional count -/

/-- **`#E ≤ 5 + H·K(ε*)`.**  If no line carries more than `H` failures beyond the certified range,
then the total number of `n ≥ 1` with `‖(3/2)ⁿ‖ < (3/4)ⁿ` is at most

`5 + H · 1 856 360 182 227`,

the `5` being the certified failures `{1, 2, 3, 4, 7}` of `[1, 256]` and the second term the line
count of [BE08] Cor. 5.2 at the sharp exponent `ε*`.  The hypothesis `H` is the open per-line
problem ([BE08] Rem. 7.4); the elementary confinement of `BB13/LineTower.lean` bounds each fibre
in terms of *its own* base but not uniformly.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`: no Subspace axiom is needed, since a cover
by finitely many finite fibres is finite outright. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_card_le_of_heightBound (H : ℕ) (hfib : ∀ r : ℚ, (highFibre r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard
      ≤ 5 + H * BugeaudEvertse.lineBound epsStar := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover
  have hfin := failures_high_finite
  have hfib' : ∀ r : ℚ, {n ∈ failuresHigh | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ failuresHigh | linePoint n = r} = highFibre r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' failuresHigh ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnf⟩, rfl⟩; exact hR n (by omega) hnf
  have hhigh : failuresHigh.ncard ≤ H * BugeaudEvertse.lineBound epsStar := by
    calc failuresHigh.ncard
        ≤ H * (linePoint '' failuresHigh).ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound epsStar := Nat.mul_le_mul (le_refl H) hcard
  have hsub : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n} ⊆ failuresUpTo 256 ∪ failuresHigh := by
    rintro n ⟨h1, hf⟩
    rcases le_or_gt n 256 with h | h
    · exact Or.inl ⟨h1, h, hf⟩
    · exact Or.inr ⟨by omega, hf⟩
  calc {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard
      ≤ (failuresUpTo 256 ∪ failuresHigh).ncard :=
        Set.ncard_le_ncard hsub ((failuresUpTo_finite 256).union hfin)
    _ ≤ (failuresUpTo 256).ncard + failuresHigh.ncard := Set.ncard_union_le _ _
    _ = 5 + failuresHigh.ncard := by rw [failuresUpTo_256_ncard]
    _ ≤ 5 + H * BugeaudEvertse.lineBound epsStar := by omega

/-- **The practical bound** (D4, repaired): the minimum of the Diophantine arm
`5 + H·K(ε*)` (conditional on the relation-tower height `H`) and the elementary tower arm
`H_thr · #towers(N)` (conditional on the threshold-tower height `H_thr`).  Both arms are honest;
neither is unconditional. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem practical_bound_min (N H Hthr : ℕ) (hrel : ∀ r : ℚ, (highFibre r).ncard ≤ H)
    (hthr : ∀ b, {n ∈ failuresUpTo N | assignedBase n = b}.ncard ≤ Hthr) :
    (failuresUpTo N).ncard
      ≤ min (5 + H * BugeaudEvertse.lineBound epsStar) (Hthr * (towerBasesUpTo N).ncard) := by
  refine le_min ?_ (failuresUpTo_card_le_towers N Hthr hthr)
  refine le_trans (Set.ncard_le_ncard ?_ failures_finite_of_lineCover)
    (failures_card_le_of_heightBound H hrel)
  rintro n ⟨h1, -, hf⟩
  exact ⟨h1, hf⟩

end BB13
