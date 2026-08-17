/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Basic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Lemma R — runs force universal density

**Lemma R.** If `A = {mₙ}` contains arbitrarily long runs of consecutive integers, then `m` is
universally densifying.

The proof is the folklore one: inside a run the sequence is an arithmetic progression of
difference one, `m(a+j) = m a + j`, so the orbit points `ξ m(a+j) = ξ m a + jξ` are a translate of
an initial segment of the orbit of the irrational rotation by `ξ`, and translation is an isometry
of the circle.

One step deserves attention, because it is the step the informal proof glosses over.  A run is
**finite**, so it is not enough to know that the forward orbit `{jξ : j ∈ ℕ}` is dense: we need a
bound `J(ε)` such that the *initial segment* `{jξ : j ≤ J}` is already `ε`-dense, and only then may
we ask for a run longer than `J`.  Density supplies no such bound.  Compactness of the circle does
(`exists_bound_of_irrational`), and that is the whole content of the finite subcover below.

## Contents

* `BB6.exists_bound_of_irrational` — the uniform `ε`-density of an initial segment of the orbit;
* `BB6.isDenseModuloOne_of_circle` — transport from the circle norm to `Int.fract`;
* `BB6.universallyDensifying_of_hasLongRuns` — **Lemma R**;
* `BB6.isDenseModuloOne_of_universallyDensifying` — the `ForMathlib` reading of the conclusion.

Lemma R is folklore; the note claims no priority for it.  What is new is the use made of it in
`BB6/Vacuity.lean`.
-/

namespace BB6

open Filter Set

/-! ## The rotation input -/

/-- For irrational `ξ` and every `ε > 0` there is a bound `J` such that the **initial segment**
`{j • ξ : j ≤ J}` of the forward orbit is already `ε`-dense in the circle.

Two Mathlib facts do the work: `AddCircle.denseRange_zsmul_coe_iff` (the `ℤ`-orbit of an
irrational rotation is dense) and `denseRange_zsmul_iff_nsmul` (in a *compact* topological group
the `ℤ`-orbit is dense iff the `ℕ`-orbit is).  The uniformity is then a finite subcover. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem exists_bound_of_irrational (ξ : ℝ) (h : Irrational ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ c : AddCircle (1 : ℝ), ∃ j ≤ J, ‖(j • (ξ : AddCircle (1 : ℝ))) - c‖ < ε := by
  have hz : DenseRange (· • ξ : ℤ → AddCircle (1 : ℝ)) :=
    AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using h)
  have hn : DenseRange (fun n : ℕ => (n • (ξ : AddCircle (1 : ℝ)))) :=
    denseRange_zsmul_iff_nsmul.1 hz
  have hcover : (univ : Set (AddCircle (1 : ℝ))) ⊆
      ⋃ j : ℕ, Metric.ball (j • (ξ : AddCircle (1 : ℝ))) ε := by
    intro c _
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hn c ε hε
    exact mem_iUnion.2 ⟨j, by simpa [Metric.mem_ball, dist_comm] using hj⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun j : ℕ => Metric.isOpen_ball) hcover
  refine ⟨t.sup id, fun c => ?_⟩
  obtain ⟨j, hjt, hj⟩ := mem_iUnion₂.1 (ht (mem_univ c))
  refine ⟨j, Finset.le_sup (f := id) hjt, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hj

/-- Transport from the circle to `ForMathlib`'s `Int.fract`-based `IsDenseModuloOne`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem isDenseModuloOne_of_circle (s : ℕ → ℝ)
    (h : ∀ (x : ℝ) (ε : ℝ), 0 < ε → ∃ n, ‖((s n - x : ℝ) : AddCircle (1 : ℝ))‖ < ε) :
    IsDenseModuloOne s := by
  intro c d hcd hsub
  have hc0 : (0 : ℝ) ≤ c := (hsub (left_mem_Icc.2 hcd.le)).1
  have hd1 : d ≤ 1 := (hsub (right_mem_Icc.2 hcd.le)).2
  obtain ⟨n, hn⟩ := h ((c + d) / 2) ((d - c) / 2) (by linarith)
  rw [UnitAddCircle.norm_eq] at hn
  set k : ℤ := round (s n - (c + d) / 2) with hk
  have hmem : c ≤ s n - (k : ℝ) ∧ s n - (k : ℝ) < d := by
    rw [abs_lt] at hn; constructor <;> linarith [hn.1, hn.2]
  have hfract : Int.fract (s n) = s n - (k : ℝ) := by
    rw [← Int.fract_sub_intCast (s n) k]
    exact Int.fract_eq_self.2 ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  exact ⟨n, by rw [hfract]; exact ⟨hmem.1, hmem.2.le⟩⟩

/-! ## Lemma R -/

/-- **Lemma R.** A sequence with arbitrarily long runs of consecutive integers is universally
densifying.

Given `ξ` irrational, a target `x` on the circle and `ε > 0`, take the bound `J = J(ε, ξ)` of
`exists_bound_of_irrational`, then a run `m(a+j) = m a + j` of length at least `J`.  The map
`j ↦ ξ m(a+j) = ξ m a + jξ` is the initial segment `{jξ : j ≤ J}` translated by `ξ m a`, and
translation is an isometry, so it hits the `ε`-ball around `x`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses exists_bound_of_irrational]
theorem universallyDensifying_of_hasLongRuns {m : ℕ → ℕ} (h : HasLongRuns m) :
    UniversallyDensifying m := by
  intro ξ hξ
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨J, hJ⟩ := exists_bound_of_irrational ξ hξ hε
  obtain ⟨a, ha⟩ := h J
  obtain ⟨j, hjJ, hj⟩ := hJ (x - ((ξ * m a : ℝ) : AddCircle (1 : ℝ)))
  refine ⟨(↑(ξ * m (a + j)) : AddCircle (1 : ℝ)), ?_, ⟨a + j, rfl⟩⟩
  have hval : ((ξ * m (a + j) : ℝ) : AddCircle (1 : ℝ))
      = ((ξ * m a : ℝ) : AddCircle (1 : ℝ)) + j • ((ξ : ℝ) : AddCircle (1 : ℝ)) := by
    rw [ha j hjJ]
    have : (ξ * ((m a + j : ℕ) : ℝ)) = ξ * m a + (j : ℕ) • ξ := by
      push_cast; rw [nsmul_eq_mul]; ring
    rw [this, AddCircle.coe_add, AddCircle.coe_nsmul]
  rw [Metric.mem_ball, dist_eq_norm, hval]
  have hrw : ((ξ * m a : ℝ) : AddCircle (1 : ℝ)) + j • ((ξ : ℝ) : AddCircle (1 : ℝ)) - x
      = j • ((ξ : ℝ) : AddCircle (1 : ℝ)) - (x - ((ξ * m a : ℝ) : AddCircle (1 : ℝ))) := by
    abel
  rw [hrw]
  exact hj

/-- The conclusion of Lemma R in `ForMathlib`'s `Int.fract` coordinates: for a universally
densifying `m` and irrational `ξ`, the sequence `(ξ mₙ)` is dense modulo one in the sense of
`IsDenseModuloOne`.  (Note that `Dense (Set.range fun n => Int.fract (ξ * m n))` in `ℝ` would be
*false* — the fractional parts lie in `[0,1)`.  Density is in `[0,1]`.) -/
@[category API, AMS 11, group "bugeaud_10_6",
  formal_uses isDenseModuloOne_of_circle]
theorem isDenseModuloOne_of_universallyDensifying {m : ℕ → ℕ} (h : UniversallyDensifying m)
    (ξ : ℝ) (hξ : Irrational ξ) : IsDenseModuloOne (fun n => ξ * m n) := by
  refine isDenseModuloOne_of_circle _ (fun x ε hε => ?_)
  obtain ⟨y, hy₁, n, rfl⟩ := Metric.dense_iff.1 (h ξ hξ) ((x : AddCircle (1 : ℝ))) ε hε
  rw [Metric.mem_ball, dist_eq_norm, ← AddCircle.coe_sub] at hy₁
  exact ⟨n, hy₁⟩

end BB6
