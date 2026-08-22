/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.CensusSweep

/-!
# The exception count, re-anchored on the certified census

`BB13/FailureCount.lean` proves `#𝓔 ≤ 5 + H·K(ε*)` — Theorem B of [paper-BB13] — where `H` bounds
the fibres of the slope map **above the certified segment**, i.e. over `BB13.highFibre`, which is
cut at `257` because `BB13.failuresUpTo_256_ncard` was the reach of the kernel at the time.

`BB13/CensusSweep.lean` moved that reach by a factor `391`: `failuresUpTo_100000_eq` certifies
`𝓔 ∩ [1, 10⁵] = {1,2,3,4,7}` against the real `IsFailure`, by kernel `decide` on the incremental
sweep.  The count re-anchors on it verbatim, and the improvement is **free in both directions**:

* the additive constant is unchanged — the certified segment still holds exactly five exceptions,
  so the `5` is the same `5`;
* the hypothesis becomes **strictly weaker** — `highFibre' r ⊆ highFibre r`
  (`highFibre'_subset_highFibre`), so any `H` that bounds the fibres above `257` bounds the fibres
  above `100001` (`heightBound_of_heightBound`), while the converse fails: a line carrying many
  exceptions in `[257, 10⁵]` no longer has to be counted, and by the census no such line exists.

In short, the same conclusion is now conditional on less.  What the cutoff cannot do is vanish:
the fibres of the slope map over `𝓔` are the open per-line problem at every cutoff, and moving it
to `10⁵` narrows the range the hypothesis speaks about without touching its difficulty.

## Why a separate file

`highFibre` and `failuresHigh` are cut at `257` inside `BB13/FailureCount.lean`, which sits
upstream of almost the whole root (`Waring ← FailureCount`, `Constants ← Waring`,
`SpanStrata ← Constants`, … , `CensusSweep ← ThinSets ← … ← ValuationArm ← SpanStrata`).  Editing
the cutoff there is not merely expensive, it is **circular**: the witness it would need,
`failures_up_to_100000`, lives in `CensusSweep.lean`, downstream of `FailureCount.lean`.  So the
re-anchored count is stated here, as a leaf, and the `257` row stands — superseded, not deleted.
The same holds for `BB13/DicksonSweep.lean` on the Waring side.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover`, identical to the `257` row.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count; Rem. 7.4 — the
  per-line problem the hypothesis `H` names.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/report3-BB13.html` §10.6, first item.
-/

namespace BB13

open scoped Real

/-! ### The failures above the certified census -/

/-- The exceptions beyond the kernel-certified segment `[1, 10⁵]`. -/
def failuresHigh' : Set ℕ := {n : ℕ | 100001 ≤ n ∧ IsFailure 3 2 (3 / 4) n}

/-- The exceptions beyond the certified census lying on the line of slope `r` — the fibres whose
size is the open per-line problem, now asked about `n ≥ 100001` rather than `n ≥ 257`. -/
def highFibre' (r : ℚ) : Set ℕ := {n : ℕ | 100001 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem highFibre'_subset_highFibre (r : ℚ) : highFibre' r ⊆ highFibre r := by
  rintro n ⟨hn, hnf, hr⟩; exact ⟨by omega, hnf, hr⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem highFibre'_subset_lineFibre (r : ℚ) : highFibre' r ⊆ lineFibre r := by
  rintro n ⟨hn, hnf, hr⟩; exact ⟨by omega, hnf, hr⟩

/-- **The re-anchored hypothesis is weaker.**  A per-line bound above `257` is a per-line bound
above `100001`; this is the precise sense in which Theorem B is improved for free. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem heightBound_of_heightBound {H : ℕ} (h : ∀ r : ℚ, (highFibre r).ncard ≤ H) :
    ∀ r : ℚ, (highFibre' r).ncard ≤ H := fun r =>
  le_trans (Set.ncard_le_ncard (highFibre'_subset_highFibre r)
    ((lineFibre_finite r).subset (highFibre_subset_lineFibre r))) (h r)

/-- **The exceptions above the certified census form a finite set** — no qualitative Subspace
input: finitely many lines (`failures_line_cover`), each carrying finitely many exceptions
(`lineFibre_finite`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failuresHigh'_finite : failuresHigh'.Finite := by
  obtain ⟨R, -, hR⟩ := failures_line_cover
  apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => lineFibre_finite r))
  rintro n ⟨hn, hnf⟩
  exact Set.mem_biUnion (hR n (by omega) hnf) ⟨by omega, hnf, rfl⟩

/-! ### `F(10⁵) = 5` -/

/-- **`F(10⁵) = 5`:** the five certified exceptions `{1,2,3,4,7}` — the additive constant of the
re-anchored count, and the same `5` as `BB13.failuresUpTo_256_ncard`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem failuresUpTo_100000_ncard : (failuresUpTo 100000).ncard = 5 := by
  rw [failuresUpTo_100000_eq,
    show ({1, 2, 3, 4, 7} : Set ℕ) = ↑({1, 2, 3, 4, 7} : Finset ℕ) by simp, Set.ncard_coe_finset]
  decide

/-! ### The re-anchored conditional count -/

/-- **`#𝓔 ≤ 5 + H·K(ε*)`, conditional on the fibres above `10⁵`.**  Theorem B of [paper-BB13]
with the certified segment extended from `[1,256]` to `[1,10⁵]`: same conclusion, same constant,
same additive `5`, but the per-line hypothesis now concerns only `n ≥ 100001`.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_card_le_of_heightBound' (H : ℕ) (hfib : ∀ r : ℚ, (highFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard
      ≤ 5 + H * BugeaudEvertse.lineBound epsStar := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover
  have hfin := failuresHigh'_finite
  have hfib' : ∀ r : ℚ, {n ∈ failuresHigh' | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ failuresHigh' | linePoint n = r} = highFibre' r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' failuresHigh' ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnf⟩, rfl⟩; exact hR n (by omega) hnf
  have hhigh : failuresHigh'.ncard ≤ H * BugeaudEvertse.lineBound epsStar := by
    calc failuresHigh'.ncard
        ≤ H * (linePoint '' failuresHigh').ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound epsStar := Nat.mul_le_mul (le_refl H) hcard
  have hsub : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n} ⊆ failuresUpTo 100000 ∪ failuresHigh' := by
    rintro n ⟨h1, hf⟩
    rcases le_or_gt n 100000 with h | h
    · exact Or.inl ⟨h1, h, hf⟩
    · exact Or.inr ⟨by omega, hf⟩
  calc {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard
      ≤ (failuresUpTo 100000 ∪ failuresHigh').ncard :=
        Set.ncard_le_ncard hsub ((failuresUpTo_finite 100000).union hfin)
    _ ≤ (failuresUpTo 100000).ncard + failuresHigh'.ncard := Set.ncard_union_le _ _
    _ = 5 + failuresHigh'.ncard := by rw [failuresUpTo_100000_ncard]
    _ ≤ 5 + H * BugeaudEvertse.lineBound epsStar := by omega

/-- **`#𝓔 ≤ 5 + H · 1.86·10¹²`** — the re-anchored count with the certified constant. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_card_le_decimal' (H : ℕ) (hfib : ∀ r : ℚ, (highFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard ≤ 5 + H * 1860000000000 :=
  le_trans (failures_card_le_of_heightBound' H hfib)
    (Nat.add_le_add_left (Nat.mul_le_mul (le_refl H) lineBound_epsStar_le) 5)

/-- **The practical bound, re-anchored.**  `BB13.practical_bound_min` with the per-line
hypothesis moved to `n ≥ 100001`: the minimum of the Diophantine arm `5 + H·K(ε*)` and the
elementary tower arm `H_thr · #towers(N)`.  Both arms remain conditional; only the range the
first one asks about has shrunk. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem practical_bound_min' (N H Hthr : ℕ) (hrel : ∀ r : ℚ, (highFibre' r).ncard ≤ H)
    (hthr : ∀ b, {n ∈ failuresUpTo N | assignedBase n = b}.ncard ≤ Hthr) :
    (failuresUpTo N).ncard
      ≤ min (5 + H * BugeaudEvertse.lineBound epsStar) (Hthr * (towerBasesUpTo N).ncard) := by
  refine le_min ?_ (failuresUpTo_card_le_towers N Hthr hthr)
  refine le_trans (Set.ncard_le_ncard ?_ failures_finite_of_lineCover)
    (failures_card_le_of_heightBound' H hrel)
  rintro n ⟨h1, -, hf⟩
  exact ⟨h1, hf⟩

end BB13
