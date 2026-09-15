/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.FineWilf
import ForMathlib.Dynamics.SymbolicDynamics.OmegaLimit
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.Common

/-!
# Periodic points, their orbits, and the separation of two periodic orbits

A configuration `x : ℤ → α` is periodic when some non-zero shift fixes it.  Its orbit is then
finite, hence closed, hence a subshift in its own right — the smallest one containing `x`.  This
file sets up that vocabulary and proves the two statements the structure theory of low-complexity
subshifts consumes:

* a subshift is finite **iff** its points share a common period, and
* two periodic points either lie on the **same orbit** or their orbits have **disjoint languages**
  at level `p + q`, the sum of the two periods.

The second is the theorem of Fine and Wilf, transported from one-sided words to two-sided
configurations.  The transport is the only work: `eq_of_forall_natCast_eq` says that a periodic
point is determined by its positive ray, so a statement about `ℕ → α` is a statement about
`ℤ → α`.

## Main definitions

* `IsPeriodicPoint x p` — `x (m + p) = x m` for all `m : ℤ`, i.e. `Function.Periodic x (p : ℤ)`.
  Periods are natural numbers: it is the shift by a *positive* amount that one wants to name, and
  `0` is allowed so that the predicate is closed under the operations below.
* `orbit x` — the shift orbit `{shift g x | g : ℤ}` of a configuration.  For a periodic point it is
  finite, and `orbitClosure x` (`OmegaLimit.lean`) is then the orbit itself, bundled as a subshift.

## Main results

* `eq_of_forall_natCast_eq` — **a periodic point is determined by its positive ray**.  This is the
  transport lemma: everything proved for one-sided words applies to periodic configurations.
* `eq_shift_of_isPeriodicPoint_of_block_eq` — **Fine–Wilf for two-sided points**: if `x` has period
  `p > 0`, `y` has period `q > 0` and one block of length `p + q` occurs in both, then `x` is a
  shift of `y`.  The length `p + q` cannot be lowered — `exists_periodic_not_shift` in
  `ForMathlib/Combinatorics/FineWilf.lean` exhibits the counterexample one letter short.
* `orbit_eq_or_disjoint_language` — the dichotomy: two periodic points have the same orbit, or
  their orbits share no block of length `p + q`.  This is the word-combinatorial half of
  [M3, Lem. 3.3]; the other half counts the two disjoint sets of blocks inside a Rauzy graph.
* `IsPeriodicPoint.finite_orbit`, `IsPeriodicPoint.coe_orbitClosure` — a periodic orbit is finite,
  and closed for free, so it *is* its own orbit closure.
* `Subshift.exists_common_period`, `Subshift.finite_iff_exists_common_period` — **a subshift over a
  finite alphabet is finite iff all its points share a period.**  Neither direction needs
  complexity; the Morse–Hedlund equivalence with `p(n) ≤ n` is `Complexity.lean`.

## Implementation notes

`IsPeriodicPoint x p` is *definitionally* `Function.Periodic x (p : ℤ)`, so Mathlib's periodicity
API applies to it directly (`IsPeriodicPoint.periodic` is the coercion, used here to get
`Function.Periodic.int_mul`).  It is kept as a separate name because the dynamical reading — `x` is
a fixed point of `shift p`, `isPeriodicPoint_iff_shift_eq` — is the one under which the orbit and
the subshift statements are natural.

The period common to all points of a finite subshift is obtained without any complexity argument:
the maps `σ^m|_Y` live in the finite set `Y → Y`, so two of them agree *pointwise*, and the
difference of their exponents is a period of every point at once.  No permutation order and no
surjectivity are needed.

## References

* [FW65] N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math.
  Soc. **16** (1965), 109–114 — `ForMathlib/Combinatorics/FineWilf.lean`.
* [Lot02] M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, Prop. 1.3.5 and §1.3.
* [BK26] Y. Bugeaud, D. H. Kim, *On the b-ary expansion of a real number whose irrationality
  exponent is close to 2*, arXiv:2510.02059, Lem. 2.3 — the same appeal to Fine and Wilf, used
  there to separate two periodic orbits of an `ω`-limit set.
* M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866.
-/

namespace SymbolicDynamics.FullShift

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Periodic points -/

/-- The configuration `x : ℤ → α` is a **periodic point of period `p`**: `x (m + p) = x m` for
every position `m`.  Definitionally `Function.Periodic x (p : ℤ)`; equivalently, `x` is a fixed
point of `shift p` (`isPeriodicPoint_iff_shift_eq`). -/
def IsPeriodicPoint (x : ℤ → α) (p : ℕ) : Prop := Function.Periodic x (p : ℤ)

lemma isPeriodicPoint_iff {x : ℤ → α} {p : ℕ} :
    IsPeriodicPoint x p ↔ ∀ m : ℤ, x (m + p) = x m := Iff.rfl

/-- The coercion to Mathlib's periodicity predicate, which carries its API. -/
lemma IsPeriodicPoint.periodic {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) :
    Function.Periodic x (p : ℤ) := h

lemma isPeriodicPoint_zero (x : ℤ → α) : IsPeriodicPoint x 0 := by
  intro m; simp

/-- **A periodic point is a fixed point of the shift by its period.**  This is the dynamical
reading of `IsPeriodicPoint`, and the form in which the orbit statements below are used. -/
lemma isPeriodicPoint_iff_shift_eq {x : ℤ → α} {p : ℕ} :
    IsPeriodicPoint x p ↔ shift (p : ℤ) x = x := by
  constructor
  · intro h
    funext m
    show x ((p : ℤ) + m) = x m
    rw [add_comm]
    exact h m
  · intro h m
    have hm : x ((p : ℤ) + m) = x m := congrFun h m
    rwa [add_comm m]

/-- A period propagates to all of its integer multiples. -/
lemma IsPeriodicPoint.apply_add_mul {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) (k m : ℤ) :
    x (m + p * k) = x m := by
  simpa [mul_comm] using h.periodic.int_mul k m

/-- Positions differing by a multiple of a period carry the same letter. -/
lemma IsPeriodicPoint.apply_eq {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) {i j k : ℤ}
    (hk : i = j + p * k) : x i = x j := by
  subst hk
  exact h.apply_add_mul k j

/-- Every multiple of a period is a period. -/
lemma IsPeriodicPoint.of_dvd {x : ℤ → α} {p q : ℕ} (h : IsPeriodicPoint x p) (hpq : p ∣ q) :
    IsPeriodicPoint x q := by
  obtain ⟨k, rfl⟩ := hpq
  intro m
  rw [Nat.cast_mul]
  exact h.apply_add_mul (k : ℤ) m

/-- Blocks read at positions differing by a multiple of a period agree. -/
lemma IsPeriodicPoint.block_eq {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) (n : ℕ) {i j k : ℤ}
    (hk : i = j + p * k) : block x n i = block x n j := by
  subst hk
  funext s
  simp only [block_apply]
  exact h.apply_eq (k := k) (by ring)

/-- Shifting by a multiple of a period does nothing. -/
lemma IsPeriodicPoint.shift_eq {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) {g j k : ℤ}
    (hk : g = j + p * k) : shift g x = shift j x := by
  funext m
  show x (g + m) = x (j + m)
  exact h.apply_eq (k := k) (by rw [hk]; ring)

/-- Every point of the orbit of a periodic point is periodic, with the same period.  (Stated
outside the `IsPeriodicPoint` namespace: inside it, `shift` would resolve to this lemma.) -/
lemma isPeriodicPoint_shift {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) (g : ℤ) :
    IsPeriodicPoint (shift g x) p := by
  intro m
  show x (g + (m + (p : ℤ))) = x (g + m)
  exact h.apply_eq (k := 1) (by ring)

/-! ## Transport: a periodic point is its positive ray -/

/-- The positive ray of a periodic point, read from any base point, is a periodic one-sided
word. -/
lemma IsPeriodicPoint.periodic_ray {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) (a : ℤ) :
    Function.Periodic (fun k : ℕ => x (a + k)) p := by
  intro k
  show x (a + ((k + p : ℕ) : ℤ)) = x (a + k)
  rw [Nat.cast_add]
  exact h.apply_eq (k := 1) (by ring)

/-- Factors of the positive ray are blocks of the point. -/
lemma factor_ray (x : ℤ → α) (a : ℤ) (n j : ℕ) :
    factor (fun k : ℕ => x (a + k)) n j = block x n (a + j) := by
  funext s
  simp only [factor, block_apply]
  congr 1
  push_cast
  ring

/-- **A periodic point is determined by its positive ray.**  Two points of a common period that
agree at every natural number are equal — which is what makes every statement about one-sided
periodic words a statement about periodic configurations. -/
theorem eq_of_forall_natCast_eq {x y : ℤ → α} {p : ℕ} (hp : 0 < p) (hx : IsPeriodicPoint x p)
    (hy : IsPeriodicPoint y p) (h : ∀ k : ℕ, x k = y k) : x = y := by
  funext m
  have hp' : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have h1 : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by omega)
  have hx' : x m = x (m % (p : ℤ)) := hx.apply_eq (Int.emod_add_mul_ediv m (p : ℤ)).symm
  have hy' : y m = y (m % (p : ℤ)) := hy.apply_eq (Int.emod_add_mul_ediv m (p : ℤ)).symm
  rw [hx', hy', ← Int.toNat_of_nonneg h1]
  exact h _

/-- **The theorem of Fine and Wilf for two-sided points.**  If `x` has period `p > 0`, `y` has
period `q > 0`, and one block of length `p + q` occurs in both — at position `a` in `x` and at
position `b` in `y` — then `x` is the shift of `y` by `b - a`.

The hypothesis cannot be weakened by one letter: `exists_periodic_not_shift` produces, for every
`p ≥ 2`, a `p`-periodic and a `(p+1)`-periodic word sharing a block of length `2p - 1` and lying on
different orbits. -/
theorem eq_shift_of_isPeriodicPoint_of_block_eq {x y : ℤ → α} {p q : ℕ} {a b : ℤ} (hp : 0 < p)
    (hq : 0 < q) (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q)
    (hb : block x (p + q) a = block y (p + q) b) : x = shift (b - a) y := by
  -- the two rays, read from the shared block
  have hu : Function.Periodic (fun k : ℕ => x (a + k)) p := hx.periodic_ray a
  have hv : Function.Periodic (fun k : ℕ => y (b + k)) q := hy.periodic_ray b
  have hagree : ∀ i, i < p + q →
      (fun k : ℕ => x (a + k)) (0 + i) = (fun k : ℕ => y (b + k)) (0 + i) := by
    intro i hi
    simpa using congrFun hb ⟨i, hi⟩
  obtain ⟨hall, -, -⟩ := eq_shift_of_periodic_of_factor_eq hp hq hu hv hagree
  -- both rays agree, and both points have the common period `p * q`
  have hP : 0 < p * q := Nat.mul_pos hp hq
  have hX : IsPeriodicPoint (shift a x) (p * q) := isPeriodicPoint_shift (hx.of_dvd ⟨q, rfl⟩) a
  have hY : IsPeriodicPoint (shift b y) (p * q) := isPeriodicPoint_shift (hy.of_dvd ⟨p, mul_comm p q⟩) b
  have hxy : shift a x = shift b y := by
    refine eq_of_forall_natCast_eq hP hX hY fun k => ?_
    show x (a + (k : ℤ)) = y (b + (k : ℤ))
    simpa using hall k
  -- undo the shift by `a`
  have e1 : shift (-a) (shift a x) = x := by
    rw [← shift_add, add_neg_cancel, shift_zero]
  have e2 : shift (-a) (shift b y) = shift (b - a) y := by
    rw [← shift_add, sub_eq_add_neg]
  rw [← e1, hxy, e2]

/-! ## Orbits -/

/-- The **orbit** of a configuration under the shift.  `orbitClosure x` (`OmegaLimit.lean`) is its
closure, and for a periodic point the two coincide (`IsPeriodicPoint.coe_orbitClosure`). -/
def orbit (x : ℤ → α) : Set (ℤ → α) := Set.range fun g : ℤ => shift g x

@[simp] lemma mem_orbit {x y : ℤ → α} : y ∈ orbit x ↔ ∃ g : ℤ, shift g x = y := Iff.rfl

lemma self_mem_orbit (x : ℤ → α) : x ∈ orbit x := ⟨0, shift_zero x⟩

lemma shift_mem_orbit (x : ℤ → α) (g : ℤ) : shift g x ∈ orbit x := ⟨g, rfl⟩

lemma coe_orbitClosure_eq_closure_orbit [TopologicalSpace α] (x : ℤ → α) :
    (orbitClosure x : Set (ℤ → α)) = closure (orbit x) := rfl

/-- The orbit of a shifted point is the orbit of the point: `orbit` is constant on orbits. -/
lemma orbit_shift (x : ℤ → α) (g : ℤ) : orbit (shift g x) = orbit x := by
  ext z
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨g + h, shift_add g h x⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h - g, ?_⟩
    show shift (h - g) (shift g x) = shift h x
    rw [← shift_add, show g + (h - g) = h by ring]

lemma orbit_eq_of_mem_orbit {x y : ℤ → α} (h : y ∈ orbit x) : orbit y = orbit x := by
  obtain ⟨g, rfl⟩ := h
  exact orbit_shift x g

/-- The language of a single configuration: its blocks, at every position. -/
lemma language_singleton (x : ℤ → α) (n : ℕ) :
    language ({x} : Set (ℤ → α)) n = {v | ∃ i : ℤ, block x n i = v} := by
  ext v
  constructor
  · rintro ⟨y, rfl, i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨x, rfl, i, hi⟩

/-- **An orbit has the same language as the point that generates it**: shifting a configuration
moves its blocks around but creates none. -/
lemma language_orbit (x : ℤ → α) (n : ℕ) :
    language (orbit x) n = {v | ∃ i : ℤ, block x n i = v} := by
  ext v
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, i, rfl⟩
    exact ⟨g + i, (block_shift x g n i).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨x, self_mem_orbit x, i, hi⟩

lemma language_orbitClosure_eq [TopologicalSpace α] [DiscreteTopology α] (x : ℤ → α) (n : ℕ) :
    (orbitClosure x).language n = language (orbit x) n := by
  rw [language_orbitClosure, language_orbit]

/-! ## Periodic orbits -/

/-- **The orbit of a periodic point is finite**, with at most `p` points. -/
lemma IsPeriodicPoint.finite_orbit {x : ℤ → α} {p : ℕ} (h : IsPeriodicPoint x p) (hp : 0 < p) :
    (orbit x).Finite := by
  have hsub : orbit x ⊆ Set.range fun k : Fin p => shift ((k : ℕ) : ℤ) x := by
    rintro _ ⟨g, rfl⟩
    have hp' : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    have h1 : 0 ≤ g % (p : ℤ) := Int.emod_nonneg g (by omega)
    have h2 : g % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos g hp'
    refine ⟨⟨(g % (p : ℤ)).toNat, by omega⟩, ?_⟩
    show shift (((g % (p : ℤ)).toNat : ℕ) : ℤ) x = shift g x
    rw [Int.toNat_of_nonneg h1]
    exact (h.shift_eq (Int.emod_add_mul_ediv g (p : ℤ)).symm).symm
  exact Set.Finite.subset (Set.finite_range _) hsub

/-- **A periodic orbit is closed**, so it is its own orbit closure: `orbitClosure x` is the
periodic orbit of `x`, bundled as a subshift. -/
theorem IsPeriodicPoint.coe_orbitClosure [TopologicalSpace α] [T1Space α] {x : ℤ → α} {p : ℕ}
    (h : IsPeriodicPoint x p) (hp : 0 < p) : (orbitClosure x : Set (ℤ → α)) = orbit x := by
  rw [coe_orbitClosure_eq_closure_orbit, (h.finite_orbit hp).isClosed.closure_eq]

/-! ## Two periodic orbits are equal or separated -/

/-- **[M3, Lem. 3.3], the Fine–Wilf half.**  Two periodic points either lie on the same orbit, or
no block of length `p + q` occurs in both orbits.

Against a Rauzy graph at level `p + q` the second alternative says that the two orbits sweep out
two *vertex-disjoint* cycles, which is how the dichotomy is used: a subshift whose graph has no
room for two disjoint cycles contains at most one periodic orbit. -/
theorem orbit_eq_or_disjoint_language {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q) :
    orbit x = orbit y ∨
      Disjoint (language (orbit x) (p + q)) (language (orbit y) (p + q)) := by
  rw [or_iff_not_imp_right]
  intro hdis
  obtain ⟨v, hvx, hvy⟩ := Set.not_disjoint_iff.mp hdis
  rw [language_orbit] at hvx hvy
  obtain ⟨a, hax⟩ := hvx
  obtain ⟨b, hby⟩ := hvy
  have hb : block x (p + q) a = block y (p + q) b := by rw [hax, hby]
  rw [eq_shift_of_isPeriodicPoint_of_block_eq hp hq hx hy hb, orbit_shift]

/-- **Distinct periodic orbits are separated at level `p + q`.**  The contrapositive form, which is
the one [M3, Lem. 3.3] consumes. -/
theorem disjoint_language_of_orbit_ne {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q) (hne : orbit x ≠ orbit y) :
    Disjoint (language (orbit x) (p + q)) (language (orbit y) (p + q)) :=
  (orbit_eq_or_disjoint_language hp hq hx hy).resolve_left hne

section Subshift

variable [TopologicalSpace α]

/-! ## Periodic points of a subshift -/

lemma orbit_subset_of_mem {Y : Subshift α ℤ} {x : ℤ → α} (hx : x ∈ Y) :
    orbit x ⊆ (Y : Set (ℤ → α)) := by
  rintro _ ⟨g, rfl⟩
  exact shift_mem Y g hx

/-- Every subshift is the union of the orbits of its points.  For a *finite* subshift this is a
finite union of finite periodic orbits (`Subshift.exists_common_period`). -/
lemma Subshift.coe_eq_biUnion_orbit (Y : Subshift α ℤ) :
    (Y : Set (ℤ → α)) = ⋃ x ∈ (Y : Set (ℤ → α)), orbit x := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_biUnion hx (self_mem_orbit x)
  · exact Set.iUnion₂_subset fun _ hx => orbit_subset_of_mem hx

lemma language_orbit_subset {Y : Subshift α ℤ} {x : ℤ → α} (hx : x ∈ Y) (n : ℕ) :
    language (orbit x) n ⊆ Y.language n :=
  language_mono (orbit_subset_of_mem hx) n

/-- **A finite subshift has a common period.**  The shift acts on the finite set `Y`, so two of its
powers agree there, and the difference of their exponents is a period of every point at once. -/
theorem Subshift.exists_common_period {Y : Subshift α ℤ} (hfin : (Y : Set (ℤ → α)).Finite) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ x ∈ Y, IsPeriodicPoint x Q := by
  have : Finite ↥(Y : Set (ℤ → α)) := hfin.to_subtype
  obtain ⟨a, b, hab, hF⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun m : ℕ => fun z : ↥(Y : Set (ℤ → α)) =>
      (⟨shift (m : ℤ) (z : ℤ → α), shift_mem Y _ z.2⟩ : ↥(Y : Set (ℤ → α))))
  have key : ∀ c d : ℕ, c < d →
      (fun z : ↥(Y : Set (ℤ → α)) => (⟨shift (c : ℤ) (z : ℤ → α), shift_mem Y _ z.2⟩ :
        ↥(Y : Set (ℤ → α)))) =
      (fun z : ↥(Y : Set (ℤ → α)) => (⟨shift (d : ℤ) (z : ℤ → α), shift_mem Y _ z.2⟩ :
        ↥(Y : Set (ℤ → α)))) →
      ∃ Q : ℕ, 0 < Q ∧ ∀ x ∈ Y, IsPeriodicPoint x Q := by
    intro c d hcd hcd'
    refine ⟨d - c, by omega, fun x hx m => ?_⟩
    have hz := congrFun hcd' ⟨x, hx⟩
    have hz' : shift (c : ℤ) x = shift (d : ℤ) x := congrArg Subtype.val hz
    have h0 := congrFun hz' (m - c)
    simp only [shift] at h0
    rw [show (((d - c : ℕ) : ℤ)) = (d : ℤ) - (c : ℤ) by omega,
      show m + ((d : ℤ) - (c : ℤ)) = (d : ℤ) + (m - (c : ℤ)) by ring, ← h0]
    congr 1
    ring
  rcases hab.lt_or_gt with hlt | hlt
  · exact key a b hlt hF
  · exact key b a hlt hF.symm

/-- Every point of a finite subshift is periodic. -/
theorem Subshift.exists_period_of_finite {Y : Subshift α ℤ} (hfin : (Y : Set (ℤ → α)).Finite)
    {x : ℤ → α} (hx : x ∈ Y) : ∃ p : ℕ, 0 < p ∧ IsPeriodicPoint x p := by
  obtain ⟨Q, hQ, hper⟩ := Subshift.exists_common_period hfin
  exact ⟨Q, hQ, hper x hx⟩

/-- **A subshift over a finite alphabet is finite iff its points share a period.**  One direction
is the pigeonhole above; the other is that a point with period `Q` is determined by the single
block it reads on `[0, Q)`, and there are only finitely many such blocks.

No complexity argument is involved.  The equivalence with `p(n) ≤ n` — Morse–Hedlund proper — is
`Subshift.finite_iff_exists_complexity_le` in `Complexity.lean`. -/
theorem Subshift.finite_iff_exists_common_period [Finite α] {Y : Subshift α ℤ} :
    (Y : Set (ℤ → α)).Finite ↔ ∃ Q : ℕ, 0 < Q ∧ ∀ x ∈ Y, IsPeriodicPoint x Q := by
  refine ⟨Subshift.exists_common_period, fun ⟨Q, hQ, hper⟩ => ?_⟩
  have hinj : Set.InjOn (fun x : ℤ → α => block x Q 0) (Y : Set (ℤ → α)) := by
    intro x hx y hy hb
    funext m
    have hQ' : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
    have h1 : 0 ≤ m % (Q : ℤ) := Int.emod_nonneg m (by omega)
    have h2 : m % (Q : ℤ) < (Q : ℤ) := Int.emod_lt_of_pos m hQ'
    have hx' : x m = x (m % (Q : ℤ)) :=
      (hper x hx).apply_eq (Int.emod_add_mul_ediv m (Q : ℤ)).symm
    have hy' : y m = y (m % (Q : ℤ)) :=
      (hper y hy).apply_eq (Int.emod_add_mul_ediv m (Q : ℤ)).symm
    have hb' := congrFun hb ⟨(m % (Q : ℤ)).toNat, by omega⟩
    simp only [block_apply, zero_add] at hb'
    rw [Int.toNat_of_nonneg h1] at hb'
    rw [hx', hy', hb']
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

end Subshift

end SymbolicDynamics.FullShift
