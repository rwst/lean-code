/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.StammeringApproximants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# 2-adic approximants of `Φ(v)` and the isometric distance bound (Route (i), Phase 3)

**Phase 3** of `B3/plan-automatic-cc.md`: *construct the `2`-adic rational approximants of `Φ(v)` and
bound their distance to the integer `n = Φ(v)`*. Building on Phase 2's stammering structure and
geometric-series form ([[b3-automatic-cc-corpus-root]], `B3.StammeringApproximants`):

* **Step 3.1 — Truncate and complete.** From the stammering prefix `Uₘ Vₘ^w` of the parity vector `v`,
  form the approximant `αₘ` by letting `Vₘ` repeat *forever* (the periodic completion); `αₘ` agrees with
  `v` on the long prefix `Uₘ Vₘ^w`, i.e. `αₘ ≡ v (mod 2^{rₘ+Lₘ})`. The general construction lives in the
  block files (`B3.BlockApproximants`, `B3.PrefixApproximants`, `B3.BlockConstruction`).
* **Step 3.2 — Evaluate.** `Φ(αₘ)` is a **rational** `2`-adic number: the geometric series collapses to a
  ratio of integer combinations of powers of `2` and `3` (`B3.Φ_blockValue_mem_ratInt`).
* **Step 3.3 — Bound the distance.** `Φ` is a **`2`-adic isometry** (`Φ_isometry`, from Bernstein–Lagarias
  Corollary A.3, `BL.corollary_A3` — `Φ` is a solenoidal bijection). Hence the distance between the
  integer `n = Φ(v)` and the rational approximant `Φ(αₘ)` equals the distance between `v` and `αₘ`:
  `‖n − Φ(αₘ)‖ = ‖v − αₘ‖ ≤ 2^{−(rₘ+Lₘ)}`   (`approximant_distance_eq`, `approximant_distance_bound`).
  Since `rₘ + Lₘ → ∞`, the rational `Φ(αₘ)` approximates the integer `n` **too well** — the input to the
  Schmidt/Schlickewei Subspace Theorem in Phase 4.

The isometry is the load-bearing step: it converts a hard estimate on `Φ(v) = n` (an integer, whose
rational approximations are *a priori* unconstrained) into the *combinatorial* statement that `v` and
its periodic completion agree on a long prefix — which the stammering structure guarantees.

## Contents
* `Φ_isometry` — (proved) `Φ` preserves the `2`-adic distance: `‖Φ x − Φ y‖ = ‖x − y‖` (BL Cor A.3).
* `norm_sub_le_of_toZModPow_eq` — agreement `mod 2^N` gives `‖x − y‖ ≤ 2^{−N}`.
* `approximant_distance_eq` — (proved, Step 3.3) `Φ v = n ⟹ ‖n − Φ α‖ = ‖v − α‖`.
* `approximant_distance_bound` — (proved, Step 3.3) `+` agreement `mod 2^N` ⟹ `‖n − Φ α‖ ≤ 2^{−N}`.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (Corollary A.3: a solenoidal bijection of `ℤ₂` is an isometry).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (§4 the rational approximants of a stammering expansion).
-/

namespace B3

open BL Function Filter

/-! ### Step 3.3 — `Φ` is a 2-adic isometry (Bernstein–Lagarias Corollary A.3) -/

/-- **`Φ` is a `2`-adic isometry** (Bernstein–Lagarias, Corollary A.3): `‖Φ x − Φ y‖ = ‖x − y‖` for all
`x, y ∈ ℤ₂`. **Proved** from `BL.corollary_A3` (the TFAE "solenoidal bijection ⟺ isometry"), since `Φ`
is solenoidal (`Φ_solenoidal`, cited) and bijective (a homeomorphism). This is the engine of Step 3.3:
it transports a distance estimate on the `Φ`-side (`‖n − Φ α‖`) to the combinatorial `v`-side
(`‖v − α‖`). -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem Φ_isometry (x y : ℤ_[2]) : ‖Φ x - Φ y‖ = ‖x - y‖ := by
  have hsb : Solenoidal (⇑Φ) ∧ Function.Bijective (⇑Φ) :=
    ⟨Φ_solenoidal, Φ.injective, Φ.surjective⟩
  have hiso := ((BL.corollary_A3 (⇑Φ)).out 0 2).mp hsb
  exact hiso x y

/-- **Distance from digit agreement.** If `x` and `y` have the same first `N` binary digits
(`toZModPow N x = toZModPow N y`, i.e. `x ≡ y (mod 2^N)`) then `‖x − y‖ ≤ 2^{−N}`. The standard
ultrametric estimate, via `BL.toZModPow_eq_iff_dvd_sub` and `BL.dvd_pow_iff_norm_le`. -/
@[category API, AMS 11, ref "BL96"]
theorem norm_sub_le_of_toZModPow_eq {x y : ℤ_[2]} {N : ℕ}
    (h : PadicInt.toZModPow N x = PadicInt.toZModPow N y) : ‖x - y‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  have hdvd : (2 : ℤ_[2]) ^ N ∣ (x - y) := (toZModPow_eq_iff_dvd_sub x y N).mp h
  simpa using (dvd_pow_iff_norm_le (x - y) N).mp hdvd

/-! ### Steps 3.1 + 3.3 — the isometric distance bound for an approximant -/

/-- **Step 3.3 (proved): the isometric distance identity.** If `Φ v = n` (the parity vector of the
integer `n`), then for *any* approximant `α` the distance from `n` to `Φ α` equals the distance from
`v` to `α`: `‖n − Φ α‖ = ‖v − α‖`. Immediate from the isometry `Φ_isometry`. This is the exact equality
the plan invokes ("because `Φ` is a `2`-adic isometry, `|n − Φ(αₘ)|₂ = |v − αₘ|₂`"). -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem approximant_distance_eq {v α : ℤ_[2]} {n : ℕ} (hv : Φ v = (n : ℤ_[2])) :
    ‖(n : ℤ_[2]) - Φ α‖ = ‖v - α‖ := by
  rw [← hv]; exact Φ_isometry v α

/-- **Step 3.1 + 3.3 (proved): "too well approximated".** If `Φ v = n` and the approximant `α` agrees
with `v` on its first `N` binary digits (`α ≡ v (mod 2^N)`), then the rational `Φ α` approximates the
integer `n` to within `2^{−N}`: `‖n − Φ α‖ ≤ 2^{−N}`. For the periodic completion `αₘ` of a stammering
`v` this holds with `N = rₘ + Lₘ → ∞` (the length of the repeated prefix `Uₘ Vₘ^w`), so the rational
approximants `Φ(αₘ)` converge to `n` faster than any polynomial in their height — the hypothesis the
Subspace Theorem (Phase 4) contradicts. -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem approximant_distance_bound {v α : ℤ_[2]} {n N : ℕ} (hv : Φ v = (n : ℤ_[2]))
    (hagree : PadicInt.toZModPow N v = PadicInt.toZModPow N α) :
    ‖(n : ℤ_[2]) - Φ α‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  rw [approximant_distance_eq hv]
  exact norm_sub_le_of_toZModPow_eq hagree

end B3
