/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonProof
import RB.MahlerExamples
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Projection
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Repairing a Mahler system: `det A ≠ 0` for free — gate G4 of plan-formalize-AF17

[AF17]'s theorems — and so `AF.corollaire_1_8`, and so this corpus's `RB/` capstones — start from
a **linear Mahler system** `F(z) = A(z)F(z^q)` whose matrix is *invertible*.  The corpus produces
systems from the `k`-kernel of an automatic sequence (`RB.mahlerMatrix`,
`RB.IsKernelModel.mahlerSystem`), and those may well be **singular**: for the parity sequence
`n ↦ n % 2`, `RB.det_mahlerMatrix_paritySigma` says `det M = 0` identically.  Closing that gap is
gate G4 of `plans/plan-formalize-AF17.html`.

## What the literature gives, and why it is not enough to cite

* [Ran92] Thm 3.1 — `u` is `p`-regular **iff** its generating series is a coordinate of a system
  `G = T·G(z^p)` with `T ∈ Mat(A[z])`.  Polynomial, but with **no determinant condition**; this
  is exactly what the corpus already proves for itself, so it buys nothing new.
* [Bec94] Thm 1 — a `k`-regular power series satisfies a **scalar** equation
  `∑ᵢ aᵢ(z)f(z^{k^i}) = 0` with `a₀aₘ ≠ 0`, `aᵢ ∈ F[z]`.  Its proof passes through a matrix
  `M ∈ Mat(F(z))` that is invertible *because the `gᵢ` are a basis* — over the field of rational
  functions.  Turning the scalar equation into a system gives a companion matrix whose first row
  is `−aᵢ/a₀`: **rational**, not polynomial.  Dumas's operator calculus [Dum93, ch. 3] likewise
  lives in `K(z)[M]`.

So *«automatic ⇒ an invertible **polynomial** system»* — the shape `AF.theoreme_2_1` consumes —
is in none of the sources verbatim.  Axiomatising it would be asserting more than the citation
supports (the risk that `NKR.sUnit_pair_integrality` realised elsewhere in this corpus), so it is
**proved** here instead, and gate G4 costs the programme no axiom at all.

## The repair

Fix any polynomial system `f = A·f(z^q)` (`f` a vector of formal power series) and let
`gⱼ := fⱼ(z^q)`.  Adding to row `i` any relation `∑ⱼ ρⱼ gⱼ = 0` leaves the system intact, so the
matrix is only determined modulo the relation module.  Write `Ψ v := v ᵥ* A` and `W := rel g`:

1. `rel f = Ψ⁻¹(rel g)` — the system, read backwards (`hcomap` in the proof).
2. `dim (rel f) ≤ dim (rel g)`: a `K(z)`-independent family of *polynomial* relations stays
   independent after `z ↦ z^q` (`RB.linearIndependent_expand`), which is the base-`q`
   decomposition of the coefficients (`RB.sect`, `RB.sum_sect`) and nothing else.
3. Hence `range Ψ ⊔ rel g = ⊤`, by counting: `dim(U ⊔ W) + dim(rel f) = n + dim(rel g)`.
4. So there is a `Θ` with `range Θ ≤ rel g` and `Ψ + Θ` injective: lift a basis of the quotient
   `K(z)^n / range Ψ` into `rel g` (possible by 3) and let `Θ` be that lift composed with a
   projection onto `ker Ψ` (the two have the same dimension).  `Θ` is the matrix correction.
5. `Θ`'s matrix `N` is rational; `D·N` is polynomial for a common denominator `D`, and
   `s ↦ det(A + s·N₀)` is a nonzero polynomial in one variable over the infinite domain `K[z]`
   (it is nonzero at `s = D⁻¹`), so **some `s ∈ K[z]` works**.

Nothing in this changes the solution vector — only the matrix — which is what makes the analytic
side free later: the difference of two rows is a formal relation, and `AF.eval_of_relation_formal`
turns formal relations into functional ones on the disc.

## Landmines

* `Algebra (RatFunc K) (LaurentSeries K)` is `RatFunc.liftAlgebra`, a **scoped** instance:
  without `open scoped RatFunc` the ambient field of this file does not typecheck.
* `det A ≠ 0` is **not** a property one can hope to prove of the kernel-model matrix itself:
  `RB.exists_nonsingular_paritySeq` exhibits a genuine kernel model (of a genuinely automatic
  sequence) whose matrix is singular, next to the nonsingular system the repair produces.
* The transfer lemma is *not* symmetric-by-triviality: `f` dependent ⇒ `f(z^q)` dependent is a
  ring-hom fact, but the direction used here needs the sections `sect q r`.

## Contents

* `RB.sect`, `RB.coeff_sect`, `RB.sum_sect`, `RB.eq_zero_of_sum_expand_eq_zero` — base-`q`
  sections of a polynomial.
* `RB.substPowSeries_eq_expand` — WP4's `AF.substPowSeries` is `PowerSeries.expand`.
* `RB.relForm`, `RB.rel`, `RB.mem_rel_iff_poly`, `RB.exists_common_denom` — relations over `K(z)`.
* **`RB.linearIndependent_expand`**, **`RB.finrank_rel_le_expand`** — the transfer lemma.
* **`RB.exists_det_ne_zero_of_mahlerSystem`** — the repair theorem.
* `RB.genSeries`, `RB.mahlerMatrixOver`, **`RB.mahlerSystem_formal`** — the formal (as opposed to
  analytic) Mahler system of a kernel model.
* **`RB.exists_nonsingular_mahlerSystem`** — gate G4: automatic ⇒ a *nonsingular* polynomial
  system with the generating series among its coordinates.
* `RB.exists_nonsingular_paritySeq` — the repair is not vacuous.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. LMS **115** (2017), 55–90.  (§1: the systems (1.2)
  and their `GL_n(ℚ̄(z))` hypothesis.)
* [Bec94] P.-G. Becker. *`k`-regular power series and Mahler-type functional equations.*
  J. Number Theory **49** (1994), 269–286.  (Thm 1 and its proof, read here in §"What the
  literature gives".)
* [Ran92] B. Randé. *Équations fonctionnelles de Mahler et applications aux suites `p`-régulières.*
  Thèse, Université Bordeaux I, 1992.  (Thm 3.1.)
* [Dum93] P. Dumas. *Récurrences mahlériennes, suites automatiques, études asymptotiques.*
  Thèse, Université Bordeaux I, 1993.  (Ch. 3: the operator algebra `K(z)[M]`.)
* [AS03] J.-P. Allouche, J. Shallit. *Automatic Sequences.* CUP 2003.  (The `k`-kernel.)
* [B1E2b] `plans/plan-B1E2b.html`: WP9, the parity counterexample.
* `plans/plan-formalize-AF17.html` (rev. 3): gate G4, and WP5 which consumes this file.
-/

namespace RB

/-! ## Base-`q` sections of a polynomial -/

section Sections

variable {K : Type*} [Field K] {q : ℕ}

/-- The `r`-th **base-`q` section** of a polynomial: the `n`-th coefficient of `sect q r c` is
the `(q·n+r)`-th coefficient of `c`. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
noncomputable def sect (q r : ℕ) (c : Polynomial K) : Polynomial K :=
  ∑ n ∈ Finset.range (c.natDegree + 1), Polynomial.monomial n (c.coeff (q * n + r))

@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma coeff_sect (hq : 2 ≤ q) (r : ℕ) (c : Polynomial K) (n : ℕ) :
    (sect q r c).coeff n = c.coeff (q * n + r) := by
  rw [sect, Polynomial.finsetSum_coeff]
  by_cases hn : n ≤ c.natDegree
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_monomial, ite_eq_right hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · push Not at hn
    have hz : ∀ b ∈ Finset.range (c.natDegree + 1),
        (Polynomial.monomial b (c.coeff (q * b + r))).coeff n = 0 := by
      intro b hb
      rw [Polynomial.coeff_monomial, ite_eq_right]
      simp only [Finset.mem_range] at hb
      omega
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    symm
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    have : n ≤ q * n := Nat.le_mul_of_pos_left n (by omega)
    omega

/-- The base-`q` decomposition of a polynomial: `c = ∑_{r<q} zʳ · (sect q r c)(z^q)`. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma sum_sect (hq : 2 ≤ q) (c : Polynomial K) :
    ∑ r ∈ Finset.range q, Polynomial.X ^ r * Polynomial.expand K q (sect q r c) = c := by
  have hq0 : 0 < q := by omega
  ext m
  have hdm : q * (m / q) + m % q = m := Nat.div_add_mod m q
  have hsub : m - m % q = q * (m / q) := by omega
  have hdiv : (m - m % q) / q = m / q := by rw [hsub]; exact Nat.mul_div_cancel_left _ hq0
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (m % q)]
  · rw [Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.mod_le m q),
      Polynomial.coeff_expand hq0, ite_eq_left ⟨m / q, hsub⟩, hdiv, coeff_sect hq]
    congr 1
  · intro b hb hbm
    simp only [Finset.mem_range] at hb
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hbm'
    · rw [Polynomial.coeff_expand hq0, ite_eq_right]
      rintro ⟨t, ht⟩
      have hmb : m = q * t + b := by omega
      have hb' : m % q = b := by rw [hmb, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      exact hbm hb'.symm
    · rfl
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.mod_lt m hq0)) h

/-- If `∑_{r<q} zʳ·hᵣ(z^q) = 0` then every `hᵣ` vanishes: the sections are independent. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma eq_zero_of_sum_expand_eq_zero (hq : 2 ≤ q) (h : ℕ → Polynomial K)
    (H : ∑ r ∈ Finset.range q, Polynomial.X ^ r * Polynomial.expand K q (h r) = 0)
    {r : ℕ} (hr : r < q) : h r = 0 := by
  have hq0 : 0 < q := by omega
  ext n
  have hsub : q * n + r - r = q * n := by omega
  have hcoeff := congrArg (fun p => Polynomial.coeff p (q * n + r)) H
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single r] at hcoeff
  · rw [Polynomial.coeff_X_pow_mul', ite_eq_left (by omega), hsub, Polynomial.coeff_expand hq0,
      ite_eq_left ⟨n, rfl⟩, Nat.mul_div_cancel_left n hq0] at hcoeff
    rw [Polynomial.coeff_zero]
    exact hcoeff
  · intro b hb hbr
    simp only [Finset.mem_range] at hb
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hble
    · rw [Polynomial.coeff_expand hq0, ite_eq_right]
      rintro ⟨t, ht⟩
      have h1 : q * n + r = q * t + b := by omega
      have h2 : (q * n + r) % q = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      have h3 : (q * t + b) % q = b := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      exact hbr (by rw [← h2, h1, h3])
    · rfl
  · intro hcon
    exact absurd (Finset.mem_range.mpr hr) hcon

end Sections

/-! ## `K(z)`-linear relations between power series -/

section Relations

-- `RatFunc.liftAlgebra` — the embedding `K(z) ↪ K⸨z⸩` — is a *scoped* instance.
open scoped RatFunc

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {q : ℕ}

/-- Substitution `z ↦ z^q` commutes with the inclusion of polynomials into power series. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma coe_polyExpand (hq0 : q ≠ 0) (p : Polynomial K) :
    ((Polynomial.expand K q p : Polynomial K) : PowerSeries K)
      = PowerSeries.expand q hq0 (p : PowerSeries K) := by
  ext n
  rw [Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.pos_of_ne_zero hq0),
    PowerSeries.coeff_expand]
  split_ifs
  · rw [Polynomial.coeff_coe]
  · rfl

omit [Fintype ι] in
/-- WP4's `AF.substPowSeries` *is* Mathlib's `PowerSeries.expand` — the bridge the corpus needs in
order to feed the systems built here to `AF.corollaire_1_8`. -/
@[category API, AMS 11 12, ref "AF17", group "rb_mahler_nonsingular"]
lemma substPowSeries_eq_expand (hq0 : q ≠ 0) (f : PowerSeries K) :
    AF.substPowSeries q f = PowerSeries.expand q hq0 f := by
  ext n
  rw [AF.substPowSeries, PowerSeries.coeff_mk, PowerSeries.coeff_expand]

/-- Polynomials sit inside Laurent series in only one way. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma algebraMap_poly_laurent (p : Polynomial K) :
    algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) p)
      = HahnSeries.ofPowerSeries ℤ K (p : PowerSeries K) := by
  rw [← IsScalarTower.algebraMap_apply]
  rfl

/-- The `K(z)`-linear form `v ↦ ∑ᵢ vᵢ·fᵢ` on `ι → K(z)`, with values in the field of Laurent
series.  Its kernel is the space of `K(z)`-linear relations between the `fᵢ`. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
noncomputable def relForm (f : ι → PowerSeries K) :
    (ι → RatFunc K) →ₗ[RatFunc K] LaurentSeries K :=
  ∑ i, (LinearMap.proj i).smulRight (HahnSeries.ofPowerSeries ℤ K (f i))

@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma relForm_apply (f : ι → PowerSeries K) (v : ι → RatFunc K) :
    relForm f v = ∑ i, v i • (HahnSeries.ofPowerSeries ℤ K (f i)) := by
  simp [relForm]

/-- **The relation space**: all `K(z)`-linear relations between the coordinates of `f`. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
noncomputable def rel (f : ι → PowerSeries K) : Submodule (RatFunc K) (ι → RatFunc K) :=
  LinearMap.ker (relForm f)

/-- A vector of **polynomials** lies in the relation space exactly when it is a relation of
formal power series.  This is the only bridge between the two worlds that is needed. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma mem_rel_iff_poly (f : ι → PowerSeries K) (ρ : ι → Polynomial K) :
    (fun i => algebraMap (Polynomial K) (RatFunc K) (ρ i)) ∈ rel f ↔
      ∑ i, ((ρ i : Polynomial K) : PowerSeries K) * f i = 0 := by
  rw [rel, LinearMap.mem_ker, relForm_apply]
  have hterm : ∀ i, (algebraMap (Polynomial K) (RatFunc K) (ρ i)) •
      (HahnSeries.ofPowerSeries ℤ K (f i))
      = HahnSeries.ofPowerSeries ℤ K (((ρ i : Polynomial K) : PowerSeries K) * f i) := by
    intro i
    rw [Algebra.smul_def, algebraMap_poly_laurent, map_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
  constructor
  · intro h
    refine HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

/-- Clearing denominators in a finite family of rational functions. -/
@[category API, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma exists_common_denom {σ : Type*} [Fintype σ] (v : σ → RatFunc K) :
    ∃ (d : Polynomial K) (ρ : σ → Polynomial K), d ≠ 0 ∧
      ∀ i, algebraMap (Polynomial K) (RatFunc K) (ρ i)
        = algebraMap (Polynomial K) (RatFunc K) d * v i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (S := RatFunc K) (nonZeroDivisors (Polynomial K)) v
  have hb0 : (b : Polynomial K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hmem : ∀ i, ∃ y : Polynomial K,
      algebraMap (Polynomial K) (RatFunc K) y = (b : Polynomial K) • v i := hb
  choose ρ hρ using hmem
  exact ⟨b, ρ, hb0, fun i => by rw [hρ i, Algebra.smul_def]⟩

omit [Fintype ι] in
/-- **The transfer lemma.**  Substituting `z ↦ z^q` preserves `K(z)`-linear independence of
vectors of polynomials.  (The converse direction is trivial; this one is the base-`q`
decomposition of the coefficients.) -/
@[category research solved, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma linearIndependent_expand (hq : 2 ≤ q) {n : ℕ} {ρ : Fin n → ι → Polynomial K}
    (h : LinearIndependent (RatFunc K)
      fun t => (fun i => algebraMap (Polynomial K) (RatFunc K) (ρ t i))) :
    LinearIndependent (RatFunc K) fun t =>
      (fun i => algebraMap (Polynomial K) (RatFunc K) (Polynomial.expand K q (ρ t i))) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc t
  obtain ⟨d, γ, hd, hγ⟩ := exists_common_denom c
  have hd' : algebraMap (Polynomial K) (RatFunc K) d ≠ 0 := fun hcon =>
    hd ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp hcon)
  -- the relation, cleared of denominators, over `K[z]`
  have hpoly : ∀ i, ∑ t, γ t * Polynomial.expand K q (ρ t i) = 0 := by
    intro i
    have h1 := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 : ∑ t, algebraMap (Polynomial K) (RatFunc K) (γ t) *
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.expand K q (ρ t i)) = 0 := by
      have : ∀ t, algebraMap (Polynomial K) (RatFunc K) (γ t) *
          algebraMap (Polynomial K) (RatFunc K) (Polynomial.expand K q (ρ t i))
          = algebraMap (Polynomial K) (RatFunc K) d *
            (c t * algebraMap (Polynomial K) (RatFunc K) (Polynomial.expand K q (ρ t i))) := by
        intro t; rw [hγ t]; ring
      rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.mul_sum, h1, mul_zero]
    have h3 : algebraMap (Polynomial K) (RatFunc K) (∑ t, γ t * Polynomial.expand K q (ρ t i))
        = 0 := by
      rw [map_sum]
      simpa using h2
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp h3
  -- decompose each `γ t` in base `q` and read off the sections
  have hsections : ∀ (r : ℕ), r < q → ∀ i, ∑ t, sect q r (γ t) * ρ t i = 0 := by
    intro r hr i
    refine eq_zero_of_sum_expand_eq_zero hq (fun r => ∑ t, sect q r (γ t) * ρ t i) ?_ hr
    calc ∑ r ∈ Finset.range q, Polynomial.X ^ r *
            Polynomial.expand K q (∑ t, sect q r (γ t) * ρ t i)
        = ∑ r ∈ Finset.range q, ∑ t, Polynomial.X ^ r *
            (Polynomial.expand K q (sect q r (γ t)) * Polynomial.expand K q (ρ t i)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [map_mul]
      _ = ∑ t, ∑ r ∈ Finset.range q, (Polynomial.X ^ r *
            Polynomial.expand K q (sect q r (γ t))) * Polynomial.expand K q (ρ t i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ =>
            Finset.sum_congr rfl fun r _ => (mul_assoc _ _ _).symm
      _ = ∑ t, (∑ r ∈ Finset.range q, Polynomial.X ^ r *
            Polynomial.expand K q (sect q r (γ t))) * Polynomial.expand K q (ρ t i) :=
          Finset.sum_congr rfl fun t _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ t, γ t * Polynomial.expand K q (ρ t i) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [sum_sect hq]
      _ = 0 := hpoly i
  -- independence of the `ρ t` kills every section of every `γ t`
  have hγzero : ∀ (r : ℕ), r < q → ∀ t, sect q r (γ t) = 0 := by
    intro r hr t
    have := h (fun t => algebraMap (Polynomial K) (RatFunc K) (sect q r (γ t))) ?_ t
    · exact (map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp this
    · funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← map_mul,
        ← map_sum]
      rw [hsections r hr i, map_zero]
  have hγ0 : ∀ t, γ t = 0 := by
    intro t
    rw [← sum_sect hq (γ t)]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [hγzero r (Finset.mem_range.mp hr) t, map_zero, mul_zero]
  have := hγ t
  rw [hγ0 t, map_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hd'

/-- **Dimension does not drop under `z ↦ z^q`**: the relation space of the substituted family is
at least as big as the relation space of the original one.  (In fact they have equal dimension,
but only this inequality is used.) -/
@[category research solved, AMS 11 12, ref "Bec94", group "rb_mahler_nonsingular"]
lemma finrank_rel_le_expand (hq : 2 ≤ q) (hq0 : q ≠ 0) (f : ι → PowerSeries K) :
    Module.finrank (RatFunc K) ↥(rel f)
      ≤ Module.finrank (RatFunc K) ↥(rel fun j => PowerSeries.expand q hq0 (f j)) := by
  classical
  set g : ι → PowerSeries K := fun j => PowerSeries.expand q hq0 (f j) with hgdef
  set d := Module.finrank (RatFunc K) ↥(rel f) with hddef
  set b := Module.finBasis (RatFunc K) ↥(rel f) with hbdef
  have hv : LinearIndependent (RatFunc K) fun t => ((b t : ι → RatFunc K)) :=
    b.linearIndependent.map' (rel f).subtype (Submodule.ker_subtype _)
  obtain ⟨D, P, hD, hP⟩ := exists_common_denom fun p : Fin d × ι => (b p.1 : ι → RatFunc K) p.2
  have hD' : algebraMap (Polynomial K) (RatFunc K) D ≠ 0 := fun hcon =>
    hD ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp hcon)
  -- the scaled family: polynomial vectors, still independent, still relations
  have hscale : ∀ t, (fun i => algebraMap (Polynomial K) (RatFunc K) (P (t, i)))
      = (algebraMap (Polynomial K) (RatFunc K) D) • ((b t : ι → RatFunc K)) := by
    intro t; funext i; rw [hP (t, i)]; rfl
  have hindep : LinearIndependent (RatFunc K)
      fun t => (fun i => algebraMap (Polynomial K) (RatFunc K) (P (t, i))) := by
    rw [funext hscale]
    exact hv.units_smul fun _ : Fin d => Units.mk0 _ hD'
  have hmemf : ∀ t, ∑ i, ((P (t, i) : Polynomial K) : PowerSeries K) * f i = 0 := by
    intro t
    rw [← mem_rel_iff_poly, hscale t]
    exact Submodule.smul_mem _ _ (b t).2
  -- transport along `z ↦ z^q`
  have hmemg : ∀ t, (fun i =>
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.expand K q (P (t, i)))) ∈ rel g := by
    intro t
    rw [mem_rel_iff_poly]
    have := congrArg (PowerSeries.expand q hq0) (hmemf t)
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, coe_polyExpand hq0]
  have hindepg : LinearIndependent (RatFunc K)
      fun t => (⟨_, hmemg t⟩ : ↥(rel g)) := by
    refine LinearIndependent.of_comp (rel g).subtype ?_
    exact linearIndependent_expand hq hindep
  simpa using hindepg.fintype_card_le_finrank

end Relations

/-! ## Repairing a singular Mahler matrix -/

section Repair

open scoped RatFunc Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- **The repair theorem.**  A linear Mahler system with polynomial matrix `A` whose determinant
happens to vanish can always be rewritten, *with the same solution vector*, over a matrix `A'`
with `det A' ≠ 0`: add to each row a relation between the coordinates of `F(z^q)`.

This is what makes the hypothesis `det A ≠ 0` of [AF17]'s theorems harmless: it costs nothing to
assume it, because the kernel-model matrix of an automatic sequence (`RB.mahlerMatrix`) may well
be singular (`RB.det_mahlerMatrix_paritySigma`) and yet the system it satisfies can be repaired. -/
@[category research solved, AMS 11 12 39, ref "Bec94" "Ran92", group "rb_mahler_nonsingular"]
theorem exists_det_ne_zero_of_mahlerSystem (hq : 2 ≤ q) (hq0 : q ≠ 0)
    {f : ι → PowerSeries K} {A : Matrix ι ι (Polynomial K)}
    (hsys : ∀ i, f i = ∑ j, ((A i j : Polynomial K) : PowerSeries K) *
      PowerSeries.expand q hq0 (f j)) :
    ∃ A' : Matrix ι ι (Polynomial K), A'.det ≠ 0 ∧
      ∀ i, f i = ∑ j, ((A' i j : Polynomial K) : PowerSeries K) *
        PowerSeries.expand q hq0 (f j) := by
  classical
  set g : ι → PowerSeries K := fun j => PowerSeries.expand q hq0 (f j) with hgdef
  set Â : Matrix ι ι (RatFunc K) := A.map (algebraMap (Polynomial K) (RatFunc K)) with hAdef
  set Ψ : (ι → RatFunc K) →ₗ[RatFunc K] (ι → RatFunc K) := Â.vecMulLinear with hΨdef
  -- ### The relation spaces are related by `Ψ`
  have hrow : ∀ i, ∑ j, (Â i j) • (HahnSeries.ofPowerSeries ℤ K (g j))
      = HahnSeries.ofPowerSeries ℤ K (f i) := by
    intro i
    have hj : ∀ j, (Â i j) • (HahnSeries.ofPowerSeries ℤ K (g j))
        = HahnSeries.ofPowerSeries ℤ K (((A i j : Polynomial K) : PowerSeries K) * g j) := by
      intro j
      rw [hAdef, Matrix.map_apply, Algebra.smul_def, algebraMap_poly_laurent, map_mul]
    rw [Finset.sum_congr rfl fun j _ => hj j, ← map_sum, ← hsys i]
  have hcomp : (relForm g).comp Ψ = relForm f := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, relForm_apply, relForm_apply, hΨdef, Matrix.vecMulLinear_apply]
    calc ∑ j, (v ᵥ* Â) j • (HahnSeries.ofPowerSeries ℤ K (g j))
        = ∑ j, ∑ i, (v i * Â i j) • (HahnSeries.ofPowerSeries ℤ K (g j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
      _ = ∑ i, ∑ j, v i • ((Â i j) • (HahnSeries.ofPowerSeries ℤ K (g j))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => by rw [mul_smul]
      _ = ∑ i, v i • (HahnSeries.ofPowerSeries ℤ K (f i)) := by
          exact Finset.sum_congr rfl fun i _ => by rw [← Finset.smul_sum, hrow i]
  have hcomap : rel f = Submodule.comap Ψ (rel g) := by
    rw [rel, rel, ← hcomp, LinearMap.ker_comp]
  have hkerle : LinearMap.ker Ψ ≤ rel f := by
    intro v hv
    rw [hcomap, Submodule.mem_comap, LinearMap.mem_ker.mp hv]
    exact Submodule.zero_mem _
  -- ### `range Ψ ⊔ rel g = ⊤`
  have hle : Module.finrank (RatFunc K) ↥(rel f) ≤ Module.finrank (RatFunc K) ↥(rel g) :=
    finrank_rel_le_expand hq hq0 f
  have hinter : LinearMap.range Ψ ⊓ rel g = Submodule.map Ψ (rel f) := by
    rw [hcomap, Submodule.map_comap_eq]
  have hmapker : Module.finrank (RatFunc K) ↥(Submodule.map Ψ (rel f))
      + Module.finrank (RatFunc K) ↥(LinearMap.ker Ψ)
      = Module.finrank (RatFunc K) ↥(rel f) := by
    have h := LinearMap.finrank_range_add_finrank_ker (Ψ.domRestrict (rel f))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      (Submodule.comapSubtypeEquivOfLe hkerle).finrank_eq] at h
    exact h
  have hcard : Module.finrank (RatFunc K) (ι → RatFunc K) = Fintype.card ι := Module.finrank_pi _
  have htop : LinearMap.range Ψ ⊔ rel g = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Ψ) (rel g)
    have h3 := LinearMap.finrank_range_add_finrank_ker Ψ
    have h4 : Module.finrank (RatFunc K) ↥(LinearMap.range Ψ ⊔ rel g) ≤ Fintype.card ι := by
      rw [← hcard]; exact Submodule.finrank_le _
    rw [hinter] at h2
    rw [hcard] at h3 ⊢
    omega
  -- ### A linear map `Θ` into `rel g` making `Ψ + Θ` injective
  have hQrank : Module.finrank (RatFunc K) ((ι → RatFunc K) ⧸ LinearMap.range Ψ)
      = Module.finrank (RatFunc K) ↥(LinearMap.ker Ψ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range Ψ)
    have h2 := LinearMap.finrank_range_add_finrank_ker Ψ
    omega
  set k := Module.finrank (RatFunc K) ↥(LinearMap.ker Ψ) with hkdef
  set bκ := Module.finBasis (RatFunc K) ↥(LinearMap.ker Ψ) with hbκ
  set bQ := (Module.finBasis (RatFunc K) ((ι → RatFunc K) ⧸ LinearMap.range Ψ)).reindex
    (finCongr hQrank) with hbQ
  have hsurj : ∀ x : (ι → RatFunc K) ⧸ LinearMap.range Ψ,
      ∃ w : ι → RatFunc K, w ∈ rel g ∧ Submodule.Quotient.mk w = x := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ (⊤ : Submodule (RatFunc K) (ι → RatFunc K)) := trivial
    rw [← htop, Submodule.mem_sup] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
    refine ⟨y₂, hy₂, ?_⟩
    rw [Submodule.Quotient.eq]
    have : y₂ - (y₁ + y₂) = -y₁ := by abel
    rw [this]
    exact neg_mem hy₁
  choose z hzmem hzmk using fun t : Fin k => hsurj (bQ t)
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker Ψ)
  set π := Submodule.projectionOnto _ C hC with hπ
  set Θ := (bκ.constr (RatFunc K) z).comp π with hΘ
  have hΘrange : ∀ v, Θ v ∈ rel g := by
    intro v
    rw [hΘ, LinearMap.comp_apply, Module.Basis.constr_apply_fintype]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hzmem t)
  have hinj : ∀ v : ι → RatFunc K, Ψ v + Θ v = 0 → v = 0 := by
    intro v hv
    have h1 : Θ v ∈ LinearMap.range Ψ := by
      have : Θ v = -(Ψ v) := by linear_combination (norm := module) hv
      rw [this]
      exact neg_mem ⟨v, rfl⟩
    have h2 : Θ v = ∑ t, (bκ.equivFun (π v) t) • z t := by
      rw [hΘ, LinearMap.comp_apply, Module.Basis.constr_apply_fintype]
    have h3 : ∑ t, (bκ.equivFun (π v) t) • bQ t = 0 := by
      have hmk := congrArg (Submodule.Quotient.mk (p := LinearMap.range Ψ)) h2
      rw [(Submodule.Quotient.mk_eq_zero _).mpr h1] at hmk
      rw [hmk, ← Submodule.mkQ_apply, map_sum]
      exact Finset.sum_congr rfl fun t _ => by
        rw [Submodule.mkQ_apply, ← hzmk t, Submodule.Quotient.mk_smul]
    have h4 : ∀ t, bκ.equivFun (π v) t = 0 :=
      Fintype.linearIndependent_iff.mp bQ.linearIndependent _ h3
    have h5 : π v = 0 := by
      have hz0 : bκ.equivFun (π v) = 0 := by funext t; exact h4 t
      simpa using congrArg bκ.equivFun.symm hz0
    have h6 : Θ v = 0 := by rw [hΘ, LinearMap.comp_apply, h5, map_zero]
    have h7 : Ψ v = 0 := by rw [h6, add_zero] at hv; exact hv
    have h8 : (⟨v, h7⟩ : ↥(LinearMap.ker Ψ)) = 0 :=
      (Submodule.projectionOnto_apply_left hC ⟨v, h7⟩).symm.trans h5
    exact congrArg Subtype.val h8
  -- ### The correction matrix over `K(z)`, and its polynomial multiple
  set N : Matrix ι ι (RatFunc K) := Matrix.of fun i j => Θ (Pi.single i 1) j with hNdef
  have hN : ∀ v : ι → RatFunc K, v ᵥ* N = Θ v := by
    intro v
    funext j
    have hexp : v = ∑ i, v i • (Pi.single i (1 : RatFunc K)) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [Matrix.vecMul, dotProduct]
    conv_rhs => rw [hexp]
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hNdef, Matrix.of_apply]
  have hdet : (Â + N).det ≠ 0 := by
    intro hcon
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hcon
    refine hv0 (hinj v ?_)
    rw [Matrix.vecMul_add, hN] at hv
    exact hv
  obtain ⟨D, P, hD, hP⟩ := exists_common_denom fun p : ι × ι => N p.1 p.2
  have hD' : algebraMap (Polynomial K) (RatFunc K) D ≠ 0 := fun hcon =>
    hD ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp hcon)
  set N₀ : Matrix ι ι (Polynomial K) := Matrix.of fun i j => P (i, j) with hN₀def
  have hN₀rel : ∀ i, ∑ j, ((N₀ i j : Polynomial K) : PowerSeries K) * g j = 0 := by
    intro i
    rw [← mem_rel_iff_poly]
    have he : (fun j => algebraMap (Polynomial K) (RatFunc K) (N₀ i j))
        = (algebraMap (Polynomial K) (RatFunc K) D) • (fun j => N i j) := by
      funext j; rw [hN₀def, Matrix.of_apply, hP (i, j)]; rfl
    rw [he]
    exact Submodule.smul_mem _ _ (by simpa [hNdef] using hΘrange (Pi.single i 1))
  -- ### One parameter is enough
  set B : Matrix ι ι (Polynomial (RatFunc K)) := Matrix.of fun i j =>
    Polynomial.C (algebraMap (Polynomial K) (RatFunc K) (A i j)) +
      Polynomial.X * Polynomial.C (algebraMap (Polynomial K) (RatFunc K) (N₀ i j)) with hBdef
  have hBeval : ∀ s : RatFunc K, Polynomial.eval s B.det
      = (Matrix.of fun i j => algebraMap (Polynomial K) (RatFunc K) (A i j)
          + s * algebraMap (Polynomial K) (RatFunc K) (N₀ i j)).det := by
    intro s
    have h := RingHom.map_det (Polynomial.evalRingHom s) B
    rw [RingHom.mapMatrix_apply] at h
    rw [show Polynomial.eval s B.det = Polynomial.evalRingHom s B.det from rfl, h]
    congr 1
    funext i j
    simp only [hBdef, Matrix.map_apply, Matrix.of_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hB0 : B.det ≠ 0 := by
    intro hcon
    refine hdet ?_
    have h := hBeval (algebraMap (Polynomial K) (RatFunc K) D)⁻¹
    rw [hcon, Polynomial.eval_zero] at h
    have hmat : Â + N = Matrix.of fun i j => algebraMap (Polynomial K) (RatFunc K) (A i j)
        + (algebraMap (Polynomial K) (RatFunc K) D)⁻¹ *
          algebraMap (Polynomial K) (RatFunc K) (N₀ i j) := by
      funext i j
      rw [hAdef, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, hN₀def, Matrix.of_apply,
        hP (i, j), ← mul_assoc, inv_mul_cancel₀ hD', one_mul]
    rw [hmat]
    exact h.symm
  obtain ⟨x, hx1, hx2⟩ :=
    ((Set.infinite_range_of_injective
      (IsFractionRing.injective (Polynomial K) (RatFunc K))).sdiff
      (Polynomial.finite_setOfPred_isRoot hB0)).nonempty
  obtain ⟨s, rfl⟩ := hx1
  set A' : Matrix ι ι (Polynomial K) := Matrix.of fun i j => A i j + s * N₀ i j with hA'def
  have hA'entry : ∀ i j, A' i j = A i j + s * N₀ i j := fun i j => rfl
  refine ⟨A', ?_, ?_⟩
  · intro hcon
    refine hx2 ?_
    show Polynomial.IsRoot B.det _
    rw [Polynomial.IsRoot, hBeval]
    have hmap := RingHom.map_det (algebraMap (Polynomial K) (RatFunc K)) A'
    rw [RingHom.mapMatrix_apply] at hmap
    have hmat : (Matrix.of fun i j => algebraMap (Polynomial K) (RatFunc K) (A i j)
        + algebraMap (Polynomial K) (RatFunc K) s *
          algebraMap (Polynomial K) (RatFunc K) (N₀ i j))
        = A'.map (algebraMap (Polynomial K) (RatFunc K)) := by
      funext i j
      rw [Matrix.of_apply, Matrix.map_apply, hA'entry i j, map_add, map_mul]
    rw [hmat, ← hmap, hcon, map_zero]
  · intro i
    have h1 : ∀ j, ((A' i j : Polynomial K) : PowerSeries K) * g j
        = ((A i j : Polynomial K) : PowerSeries K) * g j
          + ((s : Polynomial K) : PowerSeries K) *
            (((N₀ i j : Polynomial K) : PowerSeries K) * g j) := by
      intro j
      rw [hA'entry i j]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, ← Finset.mul_sum,
      hN₀rel i, mul_zero, add_zero, ← hsys i]

end Repair

/-! ## Gate G4: an automatic sequence has a *nonsingular* Mahler system -/

section Automatic

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The generating power series of a sequence of naturals, with coefficients in `K`. -/
@[category API, AMS 11 12 39, ref "Ran92", group "rb_mahler_nonsingular"]
noncomputable def genSeries (s : ℕ → ℕ) : PowerSeries K := PowerSeries.mk fun n => (s n : K)

/-- `RB.mahlerMatrix`, with its coefficients pushed from `ℤ` into `K`. -/
@[category API, AMS 11 12 39, ref "Ran92", group "rb_mahler_nonsingular"]
noncomputable def mahlerMatrixOver (k : ℕ) (σ : ι → Fin k → ι) : Matrix ι ι (Polynomial K) :=
  (mahlerMatrix k σ).map (Polynomial.map (Int.castRingHom K))

omit [Fintype ι] in
@[category API, AMS 11 12 39, ref "Ran92", group "rb_mahler_nonsingular"]
lemma mahlerMatrixOver_apply (k : ℕ) (σ : ι → Fin k → ι) (i j : ι) :
    mahlerMatrixOver (K := K) k σ i j
      = ∑ r : Fin k, if σ i r = j then (Polynomial.X : Polynomial K) ^ (r : ℕ) else 0 := by
  rw [mahlerMatrixOver, Matrix.map_apply, mahlerMatrix, Matrix.of_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · rw [Polynomial.map_pow, Polynomial.map_X]
  · rw [Polynomial.map_zero]

/-- **The formal Mahler system of a kernel model.**  The decimation identity
`φ (σ i r) n = φ i (k·n+r)` *is* the coefficient form of `F(z) = M(z)·F(z^q)`; this is that
identity read as an equation of formal power series over `K`.

The analytic counterpart, over `ℝ` or `ℂ` and for `‖z‖ < 1`, is `RB.IsKernelModel.mahlerSystem`. -/
@[category research solved, AMS 11 12 39, ref "Ran92" "AS03", group "rb_mahler_nonsingular"]
theorem mahlerSystem_formal {k : ℕ} (hk : 2 ≤ k) {a : ℕ → ℕ} {φ : ι → ℕ → ℕ} {σ : ι → Fin k → ι}
    (h : IsKernelModel k a φ σ) (i : ι) :
    (genSeries (φ i) : PowerSeries K)
      = ∑ j, ((mahlerMatrixOver k σ i j : Polynomial K) : PowerSeries K) *
          PowerSeries.expand k (by omega) (genSeries (φ j)) := by
  have hk0 : 0 < k := by omega
  have hrow : ∀ j : ι, ((mahlerMatrixOver (K := K) k σ i j : Polynomial K) : PowerSeries K) *
      PowerSeries.expand k (by omega) (genSeries (φ j))
      = ∑ r : Fin k, (if σ i r = j then (PowerSeries.X : PowerSeries K) ^ (r : ℕ) else 0) *
          PowerSeries.expand k (by omega) (genSeries (φ j)) := by
    intro j
    have hcoe : ((mahlerMatrixOver (K := K) k σ i j : Polynomial K) : PowerSeries K)
        = ∑ r : Fin k, (if σ i r = j then (PowerSeries.X : PowerSeries K) ^ (r : ℕ) else 0) := by
      rw [mahlerMatrixOver_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Polynomial.coeToPowerSeries.ringHom_apply]
      split_ifs
      · rw [Polynomial.coe_pow, Polynomial.coe_X]
      · rw [Polynomial.coe_zero]
    rw [hcoe, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun j _ => hrow j, Finset.sum_comm]
  have hcol : ∀ r : Fin k, ∑ j, (if σ i r = j then (PowerSeries.X : PowerSeries K) ^ (r : ℕ)
      else 0) * PowerSeries.expand k (by omega) (genSeries (φ j))
      = (PowerSeries.X : PowerSeries K) ^ (r : ℕ) *
        PowerSeries.expand k (by omega) (genSeries (φ (σ i r))) := by
    intro r
    rw [Finset.sum_eq_single (σ i r)]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right (Ne.symm hb), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [Finset.sum_congr rfl fun r _ => hcol r]
  ext m
  have hdm : k * (m / k) + m % k = m := Nat.div_add_mod m k
  have hlt : m % k < k := Nat.mod_lt m hk0
  have hsub : m - m % k = k * (m / k) := by omega
  rw [map_sum]
  rw [Finset.sum_eq_single (⟨m % k, hlt⟩ : Fin k)]
  · rw [PowerSeries.coeff_X_pow_mul', ite_eq_left (Nat.mod_le m k), PowerSeries.coeff_expand,
      ite_eq_left ⟨m / k, hsub⟩]
    rw [hsub, Nat.mul_div_cancel_left _ hk0]
    rw [genSeries, genSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, h.2.2 i ⟨m % k, hlt⟩]
    congr 2
    simpa using hdm.symm
  · intro b _ hb
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hble
    · rw [PowerSeries.coeff_expand, ite_eq_right]
      rintro ⟨t, ht⟩
      have h1 : m = k * t + (b : ℕ) := by omega
      have h2 : m % k = (b : ℕ) := by rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt b.2]
      exact hb (Fin.ext h2.symm)
    · rfl
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **Gate G4, executed.**  For any automatic sequence — presented, as the corpus presents it, by
a kernel model — the generating series is a coordinate of a linear Mahler system over `K[z]` whose
matrix has **nonzero determinant**.  No cited input is used: the system itself is the decimation
identity (`RB.mahlerSystem_formal`), and nonsingularity is bought by the repair theorem
(`RB.exists_det_ne_zero_of_mahlerSystem`).

This is the hypothesis `det A ≠ 0` of `AF.corollaire_1_8`, discharged. -/
@[category research solved, AMS 11 12 39, ref "Bec94" "Ran92", group "rb_mahler_nonsingular"]
theorem exists_nonsingular_mahlerSystem {k : ℕ} (hk : 2 ≤ k) {a : ℕ → ℕ} {φ : ι → ℕ → ℕ}
    {σ : ι → Fin k → ι} (h : IsKernelModel k a φ σ) :
    ∃ A : Matrix ι ι (Polynomial K), A.det ≠ 0 ∧
      ∀ i, (genSeries (φ i) : PowerSeries K)
        = ∑ j, ((A i j : Polynomial K) : PowerSeries K) *
            PowerSeries.expand k (by omega) (genSeries (φ j)) :=
  exists_det_ne_zero_of_mahlerSystem hk (by omega) (mahlerSystem_formal hk h)

/-- **The repair is not vacuous.**  The parity sequence `n ↦ n % 2` is `2`-automatic and the
determinant of *its* kernel-model matrix vanishes identically
(`RB.det_mahlerMatrix_paritySigma`) — yet its generating series is a coordinate of a system with
`det ≠ 0`.  Without the repair theorem, `AF.corollaire_1_8` would simply not apply to it. -/
@[category test, AMS 11 12 39, ref "B1E2b", group "rb_mahler_nonsingular"]
theorem exists_nonsingular_paritySeq :
    (mahlerMatrixOver (K := ℚ) 2 paritySigma).det = 0 ∧
      ∃ A : Matrix (Fin 3) (Fin 3) (Polynomial ℚ), A.det ≠ 0 ∧
        ∀ i, (genSeries (parityPhi i) : PowerSeries ℚ)
          = ∑ j, ((A i j : Polynomial ℚ) : PowerSeries ℚ) *
              PowerSeries.expand 2 (by omega) (genSeries (parityPhi j)) := by
  refine ⟨?_, exists_nonsingular_mahlerSystem (by norm_num) paritySeq_isKernelModel⟩
  have h := RingHom.map_det (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (mahlerMatrix 2 paritySigma)
  rw [RingHom.mapMatrix_apply, Polynomial.coe_mapRingHom] at h
  rw [mahlerMatrixOver, ← h, det_mahlerMatrix_paritySigma, Polynomial.map_zero]

end Automatic

end RB
