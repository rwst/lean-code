/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.PlaceTwoProduct
import B3.HeightVsRate
import Mathlib.NumberTheory.Height.NumberField
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The height-vs-rate reduction for the `Φ`-side Subspace points (Route (i), Tiers 1, 2.1 & 2.2)

This file discharges the **bookkeeping half** of the `Φ`-side height-vs-rate kernel
([[b3-automatic-cc-corpus-root]], `B3.subspace_contradiction_of_rate_sharp`'s `hrate`), isolating the
*genuine* open content into a single sharply-stated index inequality.

## What is proved here (the reduction)

* `mulHeight_placePoint` — the height of the Subspace point `(D, −1, P)` is `max(|D|, 1, |P|)`. The `−1`
  coordinate forces `gcd(D, −1, P) = 1`, so every finite-place factor is `1` (Mathlib
  `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`); **no coprimality of `D, P` is needed**.
* `mulHeight_placePoint_le`, `mulHeight_placePoint_pos` — the height is `≤ B` when each coordinate is, and
  is positive.
* `sup_vinf_placePoint_eq_mulHeight` — the archimedean coordinate-sup `⨆ⱼ vinf(xⱼ)` *equals* the height
  `H(x)` (finite local heights `= 1`); this turns the `(⨆ⱼ vinf(xⱼ))⁻¹` arch factor of
  `B3.phi_twoPlace_product_le_invSup` into the `H⁻¹` of `B3.subspace_contradiction_of_rate_sharp` (Tier 2.1).
* `phiExp` — the base-`3` complexity exponent `⌈log₃ Hₖ⌉` of the `k`-th point; gives `Hₖ ≤ 3^{phiExp k}`.
* `phiPoints_rate_pointwise`, `phiPoints_rate` — **(was a `research open` axiom; now a proved reduction).**
  `2^{−Nₖ} ≤ H(placePoint Dₖ Pₖ)^{−2−ε}` for **infinitely many** `k` (`∃ᶠ`, Tier 2.2) — threshold `2`, not
  `3`, because the **arch saving** (Tier 2.1) already pays one power of `H⁻¹` — from `phiPoints_index` via
  the pointwise reduction (`phiPoints_rate_pointwise`: height bridge + `B3.rate_le_den_rpow_gen`) mapped
  over the `∃ᶠ`. This discharges `hrate` of `B3.subspace_contradiction_of_rate_sharp_frequently`.

## What stays open

* `phiPoints_index` — the lone `research open` axiom, now a **pure** `B3.IndexConditionExpFreq 2
  (phiExp D P) N ε`: `(2 + ε)·(phiExp D P k)·log 3 ≤ Nₖ·log 2` for **infinitely many** `k`, the
  base-`2`/base-`3` independence (`ℓ`-vs-`dₗ`, Cobham/Mahler territory — proved only in the large-repetition
  regime `B3.index_of_large_w`). **`∃ᶠ`, not `∀` (Tier 2.2):** only a good subsequence is needed.
  **Threshold `2`, not `3` (Tier 2.1):** the arch factor of the gcd-`1` point contributes a free `H⁻¹`, so
  the rate need only beat `H^{−2−ε}`. The coordinate/height bounds are no longer bundled: `phiExp` is the
  *actual* base-`3` height size, so `Dₖ, |Pₖ| ≤ 3^{phiExp k}` is **proved** (`Nat.le_pow_clog`). No
  `M`-constant is needed — the construction gives only `2`-adic convergence (so `qₖ` is *not*
  archimedean-bounded), but `phiExp` bounds the height directly without it.

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (the stammering transcendence criterion).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), 1154–1169 (the base-`3` denominators `3^{cₘ} − 2^{pₘ}`).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311 (the `H(x)^{−m−ε}` Subspace bound this rate must beat).
-/

namespace B3

open Filter

/-- **The height of the Subspace point `(D, −1, P)` (proved).** `Height.mulHeight (placePoint D P) =
⨆ᵢ |·ᵢ| = max(|D|, 1, |P|)` — the `−1` coordinate forces `gcd(D, −1, P) = 1`, so every finite-place factor
is `1` and the height is the archimedean max (Mathlib `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`). No
coprimality of `D, P` is needed. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint (D P : ℤ) :
    Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) = ((⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i| : ℤ) : ℝ) := by
  have hgcd : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) = 1 := by
    have hdvd : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) ∣ (![D, -1, P] : Fin 3 → ℤ) 1 :=
      Finset.gcd_dvd (Finset.mem_univ 1)
    have hd1 : Finset.univ.gcd (![D, -1, P] : Fin 3 → ℤ) ∣ (-1 : ℤ) := by simpa using hdvd
    rw [← Finset.normalize_gcd]
    exact normalize_eq_one.mpr (isUnit_of_dvd_unit hd1 isUnit_one.neg)
  have hpt : placePoint (D : ℚ) (P : ℚ) = ((↑) : ℤ → ℚ) ∘ (![D, -1, P] : Fin 3 → ℤ) := by
    ext i; fin_cases i <;> simp [placePoint]
  rw [hpt]; exact Rat.mulHeight_eq_max_abs_of_gcd_eq_one hgcd

/-- **The Subspace height is at most `B` when each coordinate is (proved).** If `|D|, |P| ≤ B` and
`1 ≤ B`, then `Height.mulHeight (placePoint D P) ≤ B` — the height is `max(|D|, 1, |P|)`
(`mulHeight_placePoint`), bounded coordinate-wise via `ciSup_le`. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint_le (D P : ℤ) {B : ℝ} (h1 : 1 ≤ B)
    (hD : |(D : ℝ)| ≤ B) (hP : |(P : ℝ)| ≤ B) :
    Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) ≤ B := by
  rw [mulHeight_placePoint, Finite.map_iSup_of_monotone _ Int.cast_mono]
  apply ciSup_le
  intro i
  fin_cases i <;> simp_all [Int.cast_abs]

/-- **The Subspace height is positive (proved).** `0 < Height.mulHeight (placePoint D P)`: the height is
`⨆ᵢ |·ᵢ| ≥ |−1| = 1 > 0`. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem mulHeight_placePoint_pos (D P : ℤ) :
    0 < Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) := by
  rw [mulHeight_placePoint]
  have h1 : (1 : ℤ) ≤ ⨆ i, |(![D, -1, P] : Fin 3 → ℤ) i| := by
    have := le_ciSup (f := fun i => |(![D, -1, P] : Fin 3 → ℤ) i|) (Set.finite_range _).bddAbove 1
    simpa using this
  exact_mod_cast lt_of_lt_of_le one_pos h1

/-- **The archimedean coordinate-sup *is* the height of the Subspace point (proved).** For the standard
archimedean absolute value `vinf` of `ℚ` (`hvinf : vinf q = |q|`, e.g. `Rat.infinitePlace`),
`⨆ⱼ vinf(placePoint D P ⱼ) = Height.mulHeight (placePoint D P)`. Both sides are `max(|D|, 1, |P|)`: the
finite local heights of the gcd-`1` point `(D, −1, P)` are all `1`, so the height *is* the archimedean
maximum (`mulHeight_placePoint`). This identifies the `(⨆ⱼ vinf(xⱼ))⁻¹` of
`B3.phi_twoPlace_product_le_invSup` with `H(x)⁻¹` — the arch-saving factor of
`B3.subspace_contradiction_of_rate_sharp`. -/
@[category research solved, AMS 11 37, ref "AB07" "Eve96", group "b3_missing_lemma"]
theorem sup_vinf_placePoint_eq_mulHeight (D P : ℤ) (vinf : AbsoluteValue ℚ ℝ)
    (hvinf : ∀ q : ℚ, vinf q = ((|q| : ℚ) : ℝ)) :
    (⨆ j, vinf (placePoint (D : ℚ) (P : ℚ) j)) = Height.mulHeight (placePoint (D : ℚ) (P : ℚ)) := by
  rw [mulHeight_placePoint, Finite.map_iSup_of_monotone _ Int.cast_mono]
  refine iSup_congr fun j => ?_
  fin_cases j <;> simp only [placePoint, hvinf, Int.cast_abs] <;> push_cast <;> ring_nf

/-- **The base-`3` complexity exponent of the `k`-th Subspace point.** `phiExp D P k =
⌈log₃ max(|Dₖ|, |Pₖ|, 1)⌉` (`Nat.clog 3`): the base-`3` size of the height `H(placePoint Dₖ Pₖ) =
max(|Dₖ|, 1, |Pₖ|)`, so `H ≤ 3^{phiExp D P k}` (`Nat.le_pow_clog`). Morally the odd-step count `ℓ` plus any
base-`3` powers the pre-period contributes to the reduced denominator; using the *actual* base-`3` size
sidesteps the explicit block-structure denominator bound (awkward because `Φ` is **not** additive, so
`Φ(truncApprox) = Φ(A + 2ᵗ·blockVal)` has no closed denominator and the bit-peel can multiply it by extra
powers of `3`), and keeps the open input a **pure** `IndexCondition`. -/
@[category API, AMS 11 37, ref "AB07" "BL96"]
def phiExp (D P : ℕ → ℤ) : ℕ → ℕ :=
  fun k => Nat.clog 3 (max (D k).natAbs (max (P k).natAbs 1))

/-- **The base-`2`/base-`3` index condition — the pure open kernel (`research open`).** The lone genuinely
open input of Route (i): the base-`2` over-approximation modulus `Nₖ` dominates `(2 + ε)·log 3 / log 2`
times the base-`3` complexity `phiExp D P k = ⌈log₃ Hₖ⌉` of the `k`-th Subspace point — exactly
`B3.IndexConditionExpFreq 2 (phiExp D P) N ε`, i.e. `(2 + ε)·(phiExp D P k)·log 3 ≤ Nₖ·log 2` for
**infinitely many** `k`. This is the `ℓ`-vs-`dₗ` base-`2`/base-`3` independence (Cobham/Mahler territory —
proved only in the large-repetition regime `B3.index_of_large_w`).

**`∃ᶠ`, not `∀` (Tier 2.2, the subsequence relaxation).** The Subspace contradiction
(`B3.subspace_contradiction_of_rate_sharp_frequently`) only needs a good *subsequence* of approximants, so
the kernel is the **frequently**-satisfied `IndexConditionExpFreq` — the genuinely necessary (weaker, more
honest) form. (It is not a route to unconditionality; see `B3.IndexConditionExpFreq`.)

**Threshold `2`, not `3` (Tier 2.1, the archimedean saving).** The Subspace bound is `H^{−3−ε}`, but the
arch factor of the gcd-`1` point `(Dₖ, −1, Pₖ)` contributes a free `H⁻¹`
(`B3.phi_twoPlace_product_le_invSup` + `B3.sup_vinf_placePoint_eq_mulHeight`), so the *rate* need only beat
`H^{−2−ε}` (`B3.subspace_contradiction_of_rate_sharp_frequently`). The arch-saving lowers the index
threshold from `(3 + ε)` to `(2 + ε)` — enough that the overlap-free density `c/s ≈ ½` (Thue–Morse) now
*satisfies* the index condition (`2·½·log 3 ≤ log 2·w` at `w = 2`), which it did not at threshold `3`. It is
the **pure index inequality**: the height/coordinate bounds are **proved** (`phiExp` is the actual base-`3`
height size; `mulHeight_placePoint` + `Nat.le_pow_clog`), no longer bundled into the axiom. -/
@[category research open, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
axiom phiPoints_index (n : ℕ) (D P : ℕ → ℤ) (N : ℕ → ℕ) (ε : ℝ) :
    IndexConditionExpFreq 2 (phiExp D P) N ε

/-- **The pointwise rate reduction (proved).** At a single index `k`, the τ=2 index inequality gives the
arch-saved rate `2^{−Nₖ} ≤ H(placePoint Dₖ Pₖ)^{−2−ε}`. *Proof:* take `cₖ = phiExp D P k`; then
`|Dₖ|, |Pₖ| ≤ 3^{cₖ}` (`Nat.le_pow_clog`) so `mulHeight_placePoint_le` gives `H ≤ 3^{cₖ}`, and
`B3.rate_le_den_rpow_gen` (at `τ = 2`) converts the index inequality to the rate. The frequently-quantified
`phiPoints_rate` is this, mapped over the `∃ᶠ` of `phiPoints_index`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem phiPoints_rate_pointwise (D P : ℕ → ℤ) (N : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hidx : (2 + ε) * (phiExp D P k : ℝ) * Real.log 3 ≤ (N k : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(N k : ℝ)) ≤ Height.mulHeight (placePoint (D k : ℚ) (P k : ℚ)) ^ (-(2 : ℝ) - ε) := by
  set c := phiExp D P k with hc
  have hMk : max (D k).natAbs (max (P k).natAbs 1) ≤ 3 ^ c := Nat.le_pow_clog (by norm_num) _
  have hDnat : (D k).natAbs ≤ 3 ^ c := le_trans (le_max_left _ _) hMk
  have hPnat : (P k).natAbs ≤ 3 ^ c := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMk
  have hD : |(D k : ℝ)| ≤ (3 : ℝ) ^ c := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hDnat
  have hP : |(P k : ℝ)| ≤ (3 : ℝ) ^ c := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hPnat
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ c := one_le_pow₀ (by norm_num)
  exact rate_le_den_rpow_gen 2 (by norm_num) c (N k) (mulHeight_placePoint_pos (D k) (P k))
    (mulHeight_placePoint_le (D k) (P k) h1 hD hP) ε hε hidx

/-- **The base-`2` rate beats the *arch-saved* base-`3` Subspace height, frequently (proved reduction,
Tiers 2.1 & 2.2).** For the truncate-and-complete approximant family, `2^{−Nₖ} ≤ H(placePoint Dₖ Pₖ)^{−2−ε}`
for **infinitely many** `k` — threshold `2`, not `3`, because the archimedean factor of the gcd-`1` point
supplies one power of `H⁻¹` (`B3.subspace_contradiction_of_rate_sharp_frequently`); and `∃ᶠ`, not `∀`,
because only a good subsequence is needed (Tier 2.2). It is `phiPoints_index`'s `∃ᶠ` index condition mapped
through the pointwise reduction `phiPoints_rate_pointwise`. This discharges `hrate` of
`B3.subspace_contradiction_of_rate_sharp_frequently`. The *only* open ingredient is `phiPoints_index` (a
pure `IndexConditionExpFreq 2`); the height computation, coordinate bounds, and rate arithmetic are
theorems. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Eve96", group "b3_missing_lemma"]
theorem phiPoints_rate (n : ℕ) (D P : ℕ → ℤ) (N : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ k in atTop, (2 : ℝ) ^ (-(N k : ℝ)) ≤
      Height.mulHeight (placePoint (D k : ℚ) (P k : ℚ)) ^ (-(2 : ℝ) - ε) :=
  (phiPoints_index n D P N ε).mono (fun k hk => phiPoints_rate_pointwise D P N ε hε k hk)

end B3
