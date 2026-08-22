/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.MvPolynomial
public import ForMathlib.NumberTheory.RatHeight

@[expose] public section

/-!
# Heights under extension of the base field: rational points of a number field

Mathlib's `Height.mulHeight` is the *relative* height: it is built from the absolute values of
one field `K`, normalized so that the product formula holds on `K`.  For a number field `K` of
degree `D = [K : ℚ]` this makes the height of a rational point `D`-th-power larger than its
height over `ℚ` — the familiar `H_K(x) = H_ℚ(x)^{[K:ℚ]}`, equivalently `h_K = D · h_ℚ`.

Mathlib has no base-change lemmas at all (the TODO in `Mathlib/NumberTheory/Height/Basic.lean`
lists `AdmissibleAbsValues` instances for finite extensions as future work), so a Diophantine
argument that instantiates a Subspace-type theorem over a number field `K` and feeds it
*rational* points has no way to convert the resulting height inequality into the naive height of
the rational data.  This file supplies that conversion in the case that matters for such
applications — the base field is `ℚ`:

* `NumberField.mulHeight_ratCast` : `H_K(x) = H_ℚ(x)^{[K:ℚ]}` for a tuple `x : ι → ℚ`, with
  `NumberField.mulHeight_algebraMap_rat` / `NumberField.mulHeight₁_algebraMap_rat` the same
  statements phrased with the `ℚ`-algebra structure map instead of the coercion;
* `NumberField.logHeight_ratCast` : `h_K(x) = [K:ℚ] · h_ℚ(x)`;
* `NumberField.mulHeight₁_ratCast`, `NumberField.logHeight₁_ratCast` : the same for a single
  rational number, together with the explicit evaluations
  `NumberField.mulHeight₁_ratCast_eq_max` (`max |num| den` to the `D`-th power),
  `NumberField.mulHeight₁_intCast`, `NumberField.logHeight₁_intCast` and
  `NumberField.mulHeight₁_natCast`.

## The route

The heart of the matter is a *primitive* (coprime integer) tuple, for which both sides are the
naive maximum:

* `NumberField.iSup_finitePlace_intCast_eq_one_of_gcd_eq_one` — at a finite place of `K` the
  supremum over a coprime integer tuple is `1`.  This is
  `Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one` with `ℚ` replaced by `K`; the Bézout proof
  needs nothing about the base field, only that the place is nonarchimedean and bounded by `1`
  on the image of `ℤ`.
* `NumberField.mulHeight_intCast_of_gcd_eq_one` — hence
  `H_K(x) = (max_i |x_i|)^{∑_v mult v} = (max_i |x_i|)^{[K:ℚ]}`, the exponent coming from
  `NumberField.InfinitePlace.sum_mult_eq`.  Its `ℚ`-counterpart is Mathlib's
  `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`.

The general case follows because `Height.mulHeight` is invariant under scaling
(`Height.mulHeight_smul_eq_mulHeight`) and every nonzero rational tuple is a nonzero rational
multiple of a coprime integer one — `Rat.exists_primitive_smul`, proved by clearing denominators
with their product and dividing out `Finset.extract_gcd`.

## Caveats

Only the base field `ℚ` is treated.  The general tower statement `H_L(x) = H_K(x)^{[L:K]}` for
`x ∈ K ⊆ L` needs the sum-of-local-degrees identity `∑_{w ∣ v} [L_w : K_v] = [L : K]` at every
place `v` of `K`; over `ℚ` the archimedean half of that identity is
`NumberField.InfinitePlace.sum_mult_eq` and the nonarchimedean half is invisible, because a
primitive tuple has trivial finite part on both sides.

## References

* Mathlib, `Mathlib/NumberTheory/Height/NumberField.lean`
  (`Rat.mulHeight_eq_max_abs_of_gcd_eq_one`, `NumberField.mulHeight_eq`).
* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, CUP 2006, §1.5.
* [Wal00] M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, §3.
-/

open Finset Height

namespace NumberField

open AdmissibleAbsValues

variable {K : Type*} [Field K] [NumberField K]

/-!
### Coprime integer tuples
-/

section Coprime

variable {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}

/-- At a finite place of a number field, the supremum of the values of a tuple of coprime
integers is `1`.  This is `Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one` over an arbitrary
number field: the Bézout argument uses only that the place is nonarchimedean and `≤ 1` on the
image of `ℤ`. -/
theorem iSup_finitePlace_intCast_eq_one_of_gcd_eq_one (v : FinitePlace K)
    (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v ((x i : K)) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v (n : K) ≤ 1 :=
    IsNonarchimedean.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v) hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul (univ : Finset ι) x
  have hf' : (1 : ℝ) = v (∑ i, (x i : K) * (f i : K)) := by
    have := congrArg (fun n : ℤ => v ((n : K))) hf
    simpa [hx] using this
  have hsum : v (∑ i, (x i : K) * (f i : K)) ≤ ⨆ i, v ((x i : K) * (f i : K)) :=
    IsNonarchimedean.apply_sum_univ_le hv
  replace hf' := hf'.trans_le hsum
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v ((x i : K) * (f i : K)))
  rw [← hi, map_mul] at hf'
  replace hf' : 1 ≤ v ((x i : K)) :=
    hf'.trans <| mul_le_of_le_one_right (apply_nonneg v _) (H _)
  exact le_antisymm (ciSup_le (H <| x ·)) <| Finite.le_ciSup_of_le i hf'

/-- The multiplicative height, over a number field `K` of degree `D`, of a tuple of coprime
integers is the `D`-th power of the maximum of their absolute values.  Over `ℚ` (`D = 1`) this
is `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`. -/
theorem mulHeight_intCast_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    mulHeight (fun i ↦ ((x i : ℤ) : K)) = (⨆ i, |(x i : ℝ)|) ^ Module.finrank ℚ K := by
  have hx₀ : (fun i ↦ ((x i : ℤ) : K)) ≠ 0 := by
    intro h
    have hzero : Finset.univ.gcd x = 0 := Finset.gcd_eq_zero_iff.mpr fun i _ ↦ by
      have hi : ((x i : ℤ) : K) = 0 := by simpa using congrFun h i
      exact_mod_cast hi
    rw [hx] at hzero
    exact one_ne_zero hzero
  rw [NumberField.mulHeight_eq hx₀,
    finprod_eq_one_of_forall_eq_one
      (fun v ↦ iSup_finitePlace_intCast_eq_one_of_gcd_eq_one v hx), mul_one]
  have harch (v : InfinitePlace K) : (⨆ i, v ((x i : K))) = ⨆ i, |(x i : ℝ)| := by
    refine iSup_congr fun i ↦ ?_
    rw [InfinitePlace.map_intCast, Int.norm_eq_abs]
  simp_rw [harch]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end Coprime

end NumberField

/-!
### Primitive representatives of rational tuples
-/

namespace Rat

/-- Every nonzero tuple of rational numbers is a nonzero rational multiple of a tuple of
coprime integers: clear denominators with their product, then divide out the gcd. -/
theorem exists_primitive_smul {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℚ} (hx : x ≠ 0) :
    ∃ (c : ℚ) (y : ι → ℤ), c ≠ 0 ∧ Finset.univ.gcd y = 1 ∧
      x = c • (((↑) : ℤ → ℚ) ∘ y) := by
  classical
  obtain ⟨i₀, hi₀'⟩ := Function.ne_iff.mp hx
  have hi₀ : x i₀ ≠ 0 := by simpa using hi₀'
  set d : ℕ := ∏ i, (x i).den with hd
  have hd0 : (0 : ℚ) < (d : ℚ) := by
    have : 0 < d := Finset.prod_pos fun i _ ↦ (x i).den_pos
    exact_mod_cast this
  have hd0' : (d : ℚ) ≠ 0 := hd0.ne'
  set z : ι → ℤ := fun i ↦ ((d / (x i).den : ℕ) : ℤ) * (x i).num with hz
  have hzq (i : ι) : ((z i : ℤ) : ℚ) = (d : ℚ) * x i := by
    have hden : (x i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hden0 : ((x i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (x i).den_nz
    have hcast : (((d / (x i).den : ℕ) : ℤ) : ℚ) = (d : ℚ) / ((x i).den : ℚ) := by
      rw [Int.cast_natCast, Nat.cast_div hden hden0]
    calc ((z i : ℤ) : ℚ) = (((d / (x i).den : ℕ) : ℤ) : ℚ) * ((x i).num : ℚ) := by
          rw [hz]; push_cast; ring
      _ = (d : ℚ) * (((x i).num : ℚ) / ((x i).den : ℚ)) := by rw [hcast]; ring
      _ = (d : ℚ) * x i := by rw [Rat.num_div_den]
  have hz₀ : z i₀ ≠ 0 := by
    intro h
    have hzi := hzq i₀
    rw [h] at hzi
    simp only [Int.cast_zero] at hzi
    exact hi₀ ((mul_eq_zero.mp hzi.symm).resolve_left hd0')
  obtain ⟨y, hy, hgcd⟩ := Finset.extract_gcd z ⟨i₀, Finset.mem_univ i₀⟩
  set g : ℤ := Finset.univ.gcd z with hgdef
  have hg0 : g ≠ 0 := fun h ↦ hz₀ (Finset.gcd_eq_zero_iff.mp h i₀ (Finset.mem_univ i₀))
  refine ⟨(g : ℚ) / (d : ℚ), y, div_ne_zero (by exact_mod_cast hg0) hd0', hgcd, ?_⟩
  funext i
  have hzi : (d : ℚ) * x i = (g : ℚ) * ((y i : ℤ) : ℚ) := by
    rw [← hzq i, hy i (Finset.mem_univ i)]
    push_cast
    ring
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  field_simp
  linarith [hzi]

end Rat

/-!
### The extension formula
-/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Heights over a number field are `D`-th powers of heights over `ℚ`**: for a tuple of
rational numbers, the multiplicative height computed in a number field `K` is the height
computed in `ℚ` raised to the degree `[K : ℚ]`.  This is the base-change formula for Mathlib's
*relative* height, and the reason a Subspace-type theorem instantiated over `K` and applied to
rational data sees its height exponent multiplied by `[K : ℚ]`. -/
theorem mulHeight_ratCast {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    mulHeight (fun i ↦ ((x i : ℚ) : K)) = mulHeight x ^ Module.finrank ℚ K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [mulHeight_eq_one_of_subsingleton, mulHeight_eq_one_of_subsingleton, one_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨c, y, hc, hgcd, hxy⟩ := Rat.exists_primitive_smul hx
  have hcK : ((c : ℚ) : K) ≠ 0 := by exact_mod_cast hc
  have hlhs : (fun i ↦ ((x i : ℚ) : K)) = ((c : ℚ) : K) • (fun i ↦ ((y i : ℤ) : K)) := by
    funext i
    have hxi : x i = c * ((y i : ℤ) : ℚ) := by
      have := congrFun hxy i
      simpa using this
    simp only [Pi.smul_apply, smul_eq_mul, hxi]
    push_cast
    ring
  rw [hlhs, mulHeight_smul_eq_mulHeight _ hcK, mulHeight_intCast_of_gcd_eq_one hgcd, hxy,
    mulHeight_smul_eq_mulHeight _ hc, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd]
  congr 1
  rw [Finite.map_iSup_of_monotone (fun i ↦ |y i|) (Int.cast_mono (R := ℝ))]
  exact iSup_congr fun _ ↦ Int.cast_abs.symm

/-- `NumberField.mulHeight_ratCast` in `algebraMap` form, for consumers that carry the
`ℚ`-algebra structure map rather than the coercion. -/
theorem mulHeight_algebraMap_rat {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    mulHeight (fun i ↦ algebraMap ℚ K (x i)) = mulHeight x ^ Module.finrank ℚ K := by
  simp only [eq_ratCast]
  exact mulHeight_ratCast x

/-- The logarithmic form of `NumberField.mulHeight_ratCast`: `h_K(x) = [K : ℚ] · h_ℚ(x)`. -/
theorem logHeight_ratCast {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    logHeight (fun i ↦ ((x i : ℚ) : K)) = Module.finrank ℚ K * logHeight x := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_ratCast, Real.log_pow]

/-- The height of a rational number computed in a number field `K` is its height over `ℚ`
raised to the degree `[K : ℚ]`. -/
theorem mulHeight₁_ratCast (q : ℚ) :
    mulHeight₁ ((q : ℚ) : K) = mulHeight₁ q ^ Module.finrank ℚ K := by
  have h : (![((q : ℚ) : K), 1] : Fin 2 → K) = fun i ↦ ((![q, 1] i : ℚ) : K) := by
    funext i; fin_cases i <;> simp
  rw [mulHeight₁_eq_mulHeight, mulHeight₁_eq_mulHeight, h, mulHeight_ratCast]

/-- The logarithmic form: `h_K(q) = [K : ℚ] · h_ℚ(q)` for `q : ℚ`. -/
theorem logHeight₁_ratCast (q : ℚ) :
    logHeight₁ ((q : ℚ) : K) = Module.finrank ℚ K * logHeight₁ q := by
  rw [logHeight₁_eq_log_mulHeight₁, logHeight₁_eq_log_mulHeight₁, mulHeight₁_ratCast,
    Real.log_pow]

/-- The single-element `algebraMap` form of `NumberField.mulHeight₁_ratCast`. -/
theorem mulHeight₁_algebraMap_rat (q : ℚ) :
    mulHeight₁ (algebraMap ℚ K q) = mulHeight₁ q ^ Module.finrank ℚ K := by
  simp only [eq_ratCast]
  exact mulHeight₁_ratCast q

/-- The explicit value: `H_K(q) = max(|num q|, den q)^{[K:ℚ]}`. -/
theorem mulHeight₁_ratCast_eq_max (q : ℚ) :
    mulHeight₁ ((q : ℚ) : K)
      = (max (q.num.natAbs : ℝ) (q.den : ℝ)) ^ Module.finrank ℚ K := by
  rw [mulHeight₁_ratCast, Rat.mulHeight₁_eq_max]
  push_cast
  ring

/-- The height of a nonzero integer in a number field of degree `D` is `|n|^D`. -/
theorem mulHeight₁_intCast {n : ℤ} (hn : n ≠ 0) :
    mulHeight₁ ((n : ℤ) : K) = (n.natAbs : ℝ) ^ Module.finrank ℚ K := by
  have h : ((n : ℤ) : K) = (((n : ℚ) : ℚ) : K) := by norm_cast
  rw [h, mulHeight₁_ratCast, Rat.mulHeight₁_intCast hn]

/-- The logarithmic height of an integer in a number field of degree `D` is `D · log |n|`
(unconditionally, since `Real.log 0 = 0`). -/
theorem logHeight₁_intCast (n : ℤ) :
    logHeight₁ ((n : ℤ) : K) = Module.finrank ℚ K * Real.log |(n : ℝ)| := by
  have h : ((n : ℤ) : K) = (((n : ℚ) : ℚ) : K) := by norm_cast
  rw [h, logHeight₁_ratCast, Rat.logHeight₁_intCast]

/-- The height of a positive natural number in a number field of degree `D` is `n^D`. -/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ ((n : ℕ) : K) = (n : ℝ) ^ Module.finrank ℚ K := by
  have h : ((n : ℕ) : K) = (((n : ℚ) : ℚ) : K) := by norm_cast
  rw [h, mulHeight₁_ratCast, Rat.mulHeight₁_natCast]

end NumberField
