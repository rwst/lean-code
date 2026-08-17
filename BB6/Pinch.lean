/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Readings
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem D₀ — the pinch

A universally densifying sequence cannot be lacunary.  The proof is a dimension count and it is
already half in the corpus: `BB6.dimH_exceptional_eq_zero` says a UD sequence has exceptional set
`⊆ ℚ`, hence of Hausdorff dimension `0`, while the Pollington–de Mathan theorem
(`Bugeaud06.pollington_de_mathan`, [Pol79, Cor.] / [Mat80, Cor. 1]) gives dimension `1` for a
lacunary one.

The consequence for Problem 10.6 is the **pinch**.  Under the ratio-floor reading R3 an answering
sequence must satisfy two conditions that pull in opposite directions:

* eventually `mₙ₊₁/mₙ ≥ 1 + c/log n` — a floor under every ratio (R3);
* infinitely often `mₙ₊₁/mₙ ≤ 1 + ε`, for every `ε > 0` — the ratios return to `1` along a
  subsequence (Theorem D₀, since UD forbids lacunarity).

There is no contradiction here, and that is the point: the two conditions are compatible exactly
because the floor decays.  Any answer to Problem 10.6 under R3 must live in this gap.

## Contents

* `BB6.not_isLacunary_of_universallyDensifying_of` — Theorem D₀ conditional on the cited axiom,
  hence `std3`;
* `BB6.not_isLacunary_of_universallyDensifying` — Theorem D₀, drawing `pollington_de_mathan`;
* `BB6.frequently_ratio_le_of_not_isLacunary` — non-lacunarity in ratio form, `std3`;
* `BB6.theorem_D0` — the package;
* `BB6.pinch`, `BB6.r3_answer_profile` — what an R3 answer to Problem 10.6 must look like;
* `BB6.exceptional_tail_subset`, `BB6.dimH_exceptional_eq_one_of_always` — the fidelity lemma
  showing that the axiom's *eventual* lacunarity hypothesis is no stronger than the *always* form
  proved in [Pol79]/[Mat80]/[Khi26].

## What is *not* here

The [Kat01, Claim 2] strengthening (D₀⁺: a UD sequence has `sup_n #(A ∩ [Lⁿ, Lⁿ⁺¹]) = ∞` for every
`L > 1`, so the pinch is about *local clustering* rather than about ratios) is stated in the note as
a citation and is deliberately not formalized — see the WP4 box of the plan for the reasons.

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
  - [Pol79] Pollington, A. D. "On the density of sequence `{nₖξ}`." Illinois J. Math. 23 (1979).
  - [Mat80] de Mathan, B. "Numbers contravening a condition in density modulo 1."
    Acta Math. Hungar. 36 (1980).
  - [Kat01] Katznelson, Y. "Chromatic numbers of Cayley graphs on ℤ and recurrence."
    Combinatorica 21 (2001).
-/

namespace BB6

open Filter

/-! ## Theorem D₀ -/

/-- **Theorem D₀, conditional form.**  A universally densifying sequence of positive integers is
not lacunary — assuming the Pollington–de Mathan theorem as a hypothesis, so that this declaration
itself is `std3`.  The whole content is that `0 ≠ 1` in `ℝ≥0∞`: UD pins the exceptional set inside
`ℚ` (`BB6.dimH_exceptional_eq_zero`), lacunarity blows it up to full dimension. -/
@[category research solved, AMS 11, ref "Bug12" "Pol79" "Mat80", group "bugeaud_10_6",
  formal_uses dimH_exceptional_eq_zero]
theorem not_isLacunary_of_universallyDensifying_of
    (hPdM : type_of% Bugeaud06.pollington_de_mathan)
    {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n) (h : UniversallyDensifying m) : ¬ IsLacunary m := by
  intro hlac
  have h1 := hPdM m hpos hlac
  rw [dimH_exceptional_eq_zero h] at h1
  exact zero_ne_one h1

/-- **Theorem D₀.**  Every universally densifying sequence of positive integers is non-lacunary.
This is the one statement of the note that draws on the cited axiom
`Bugeaud06.pollington_de_mathan`. -/
@[category research solved, AMS 11, ref "Bug12" "Pol79" "Mat80", group "bugeaud_10_6",
  solved_by "Pollington" 1979, solved_by "de Mathan" 1980,
  formal_uses Bugeaud06.pollington_de_mathan not_isLacunary_of_universallyDensifying_of]
theorem not_isLacunary_of_universallyDensifying {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n)
    (h : UniversallyDensifying m) : ¬ IsLacunary m :=
  not_isLacunary_of_universallyDensifying_of Bugeaud06.pollington_de_mathan hpos h

/-! ## Non-lacunarity in ratio form -/

/-- Non-lacunarity, unfolded: for every `ε > 0` the ratio `mₙ₊₁/mₙ` drops to `≤ 1 + ε` infinitely
often.  Equivalently `liminf mₙ₊₁/mₙ ≤ 1`, and `≥ 1` is automatic for an increasing sequence, so
the ratios really do return to `1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem frequently_ratio_le_of_not_isLacunary {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n)
    (h : ¬ IsLacunary m) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (m (n + 1) : ℝ) / m n ≤ 1 + ε := by
  have h1 : ¬ (∀ᶠ k : ℕ in atTop, (1 + ε) * m k < m (k + 1)) := fun hc =>
    h ⟨1 + ε, by linarith, hc⟩
  rw [Filter.not_eventually] at h1
  refine h1.mono fun k hk => ?_
  push Not at hk
  rw [div_le_iff₀ (by exact_mod_cast hpos k)]
  linarith

/-- **Theorem D₀, packaged.**  A UD sequence is non-lacunary, and its ratios return to `1`. -/
@[category research solved, AMS 11, ref "Bug12" "Pol79" "Mat80", group "bugeaud_10_6",
  formal_uses not_isLacunary_of_universallyDensifying frequently_ratio_le_of_not_isLacunary]
theorem theorem_D0 {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n) (h : UniversallyDensifying m) :
    ¬ IsLacunary m ∧
      ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, (m (n + 1) : ℝ) / m n ≤ 1 + ε :=
  ⟨not_isLacunary_of_universallyDensifying hpos h,
    fun _ hε => frequently_ratio_le_of_not_isLacunary hpos
      (not_isLacunary_of_universallyDensifying hpos h) hε⟩

/-! ## The eventual form of the lacunarity hypothesis is free

[Pol79], [Mat80] and [Khi26] all assume the ratio bound `m_{n+1}/m_n ≥ c > 1` for **every** `n`,
whereas `ForMathlib.IsLacunary` — and so the cited axiom `Bugeaud06.pollington_de_mathan` — asks
only for the eventual form.  The gap costs nothing, and this is the lemma that says so: dropping
an initial segment removes finitely many points from the orbit, and a finite set cannot fill an
interval, so the exceptional set of a tail is contained in that of the whole sequence. -/

/-- The unit circle has more than one point.  Needed only to see that it has no isolated points
(`PerfectSpace`, from `T1Space` + `ConnectedSpace` + `Nontrivial`), which Mathlib does not
provide for `AddCircle` directly. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem nontrivial_unitAddCircle : Nontrivial (AddCircle (1 : ℝ)) := by
  refine ⟨((1 / 2 : ℝ) : AddCircle (1 : ℝ)), 0, fun h => ?_⟩
  have h0 : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = 0 := by rw [h, norm_zero]
  rw [UnitAddCircle.norm_eq] at h0
  norm_num [round_eq] at h0

/-- **Dropping an initial segment does not shrink the exceptional set.**  The orbit of the tail
differs from the orbit of the whole sequence by finitely many points, and the circle has no
isolated points, so a dense orbit stays dense after they are removed. -/
@[category API, AMS 11, ref "Pol79" "Mat80" "Khi26", group "bugeaud_10_6"]
theorem exceptional_tail_subset (m : ℕ → ℕ) (N : ℕ) :
    {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m (N + n)) : AddCircle (1 : ℝ)))} ⊆
      {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} := by
  haveI := nontrivial_unitAddCircle
  intro ξ hξ hdense
  refine hξ (Dense.mono ?_ (hdense.sdiff_finite
    ((Set.finite_Iio N).image fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))))
  rintro y ⟨⟨i, rfl⟩, hy⟩
  rcases Nat.lt_or_ge i N with hi | hi
  · exact absurd (Set.mem_image_of_mem _ (Set.mem_Iio.2 hi)) hy
  · exact ⟨i - N, by dsimp only; rw [show N + (i - N) = i from by omega]⟩

/-- **The `IsLacunary` hypothesis may be taken in its eventual form at no cost.**  Granted the
literature's statement — the ratio bound holding for *every* index — the same conclusion follows
for a sequence that is only eventually lacunary, by applying it to a tail and pushing the
exceptional set forward along `BB6.exceptional_tail_subset`.  So
`Bugeaud06.pollington_de_mathan`, which is stated with `ForMathlib.IsLacunary`, records exactly
what [Pol79]/[Mat80] prove and nothing more.  `std3`. -/
@[category research solved, AMS 11, ref "Pol79" "Mat80" "Khi26", group "bugeaud_10_6",
  formal_uses exceptional_tail_subset]
theorem dimH_exceptional_eq_one_of_always
    (halways : ∀ m : ℕ → ℕ, (∀ n, 0 < m n) → (∃ c > (1 : ℝ), ∀ k, c * m k < m (k + 1)) →
      dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1)
    {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1 := by
  obtain ⟨c, hc, hev⟩ := hlac
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have htail := halways (fun n => m (N + n)) (fun n => hpos _)
    ⟨c, hc, fun k => hN (N + k) (by omega)⟩
  have hge : 1 ≤ dimH {ξ : ℝ | ¬ Dense (Set.range fun n =>
      (↑(ξ * m n) : AddCircle (1 : ℝ)))} := by
    rw [← htail]
    exact dimH_mono (exceptional_tail_subset m N)
  have hle : dimH {ξ : ℝ | ¬ Dense (Set.range fun n =>
      (↑(ξ * m n) : AddCircle (1 : ℝ)))} ≤ 1 := by
    have huniv : dimH (Set.univ : Set ℝ) = 1 := by
      simpa using Real.dimH_of_mem_nhds (x := (0 : ℝ)) (s := (Set.univ : Set ℝ)) Filter.univ_mem
    rw [← huniv]
    exact dimH_mono (Set.subset_univ _)
  exact le_antisymm hle hge

/-! ## The pinch -/

/-- **The pinch.**  A sequence answering Problem 10.6 under reading R3 has a decaying floor under
*every* ratio and yet returns arbitrarily close to ratio `1` infinitely often.  The two are
compatible only because `c/log n → 0`: with a *constant* floor the second clause would already be
lacunarity, which Theorem D₀ forbids.  So R3 is exactly as strong as a reading can be here, and it
is why the "avoidance width" results of the literature — which produce constant gauges — cannot
refute a positive answer. -/
@[category research solved, AMS 11, ref "Bug12" "Pol79" "Mat80", group "bugeaud_10_6",
  formal_uses theorem_D0]
theorem pinch {m : ℕ → ℕ} (hpos : ∀ n, 0 < m n) (hud : UniversallyDensifying m)
    (hr3 : Bugeaud06.IsGenuinelySublacunary m) :
    (∃ c > 0, ∀ᶠ n : ℕ in atTop, (1 + c / Real.log n) ≤ (m (n + 1) : ℝ) / m n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, (m (n + 1) : ℝ) / m n ≤ 1 + ε) :=
  ⟨hr3, (theorem_D0 hpos hud).2⟩

/-- **The profile of an R3 answer.**  Combining the pinch with Proposition C: a strictly increasing
UD sequence with a `c/log n` ratio floor is non-lacunary, has ratios returning to `1`, grows faster
than `exp (nᵅ)` for every `α < 1`, and is sparser than `C log N log log N`.  This is the complete
list of what OP1 demands of a candidate, and none of the four clauses is in conflict with the
others — which is why the problem is open rather than dead. -/
@[category research open, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses theorem_D0 hasIntermediateGrowth_of_r3 countingFn_of_r3]
theorem r3_answer_profile {m : ℕ → ℕ} (hm : StrictMono m) (hpos : ∀ n, 0 < m n)
    (hud : UniversallyDensifying m) (hr3 : Bugeaud06.IsGenuinelySublacunary m) :
    ¬ IsLacunary m ∧
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, (m (n + 1) : ℝ) / m n ≤ 1 + ε) ∧
      (∀ α : ℝ, 0 < α → α < 1 → Bugeaud06.HasIntermediateGrowth α m) ∧
      (∃ C > 0, ∀ᶠ N : ℕ in atTop,
        (countingFn m N : ℝ) ≤ C * Real.log N * Real.log (Real.log N)) :=
  ⟨(theorem_D0 hpos hud).1, (theorem_D0 hpos hud).2,
    fun _ hα0 hα1 => hasIntermediateGrowth_of_r3 hr3 hα0 hα1, countingFn_of_r3 hm hr3⟩

end BB6
