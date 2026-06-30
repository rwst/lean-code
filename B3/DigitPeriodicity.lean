/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.AutomaticParityVectors
import AB.StammeringSequences
import L90.DivergentAperiodic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Two-adic digit periodicity for `3x+1` parity sequences

The two halves of the standard fact that a `2`-adic integer is **rational** iff its binary expansion is
**eventually periodic** — the `2`-adic analogue of "eventually periodic decimal ⟺ rational" — specialised
to the Bernstein–Lagarias binary-digit / parity-vector vocabulary.

* `not_isEventuallyPeriodic_binaryDigit` — **reverse direction (irrational ⟹ aperiodic digits), now
  PROVED.** An irrational `2`-adic integer `v ∉ RatInt` has a non-eventually-periodic binary expansion
  `binaryDigit v`. Phase 2's bridge from the irrationality hypothesis to the "not eventually periodic"
  clause of Condition (∗)_w; feeds `B3.binaryDigit_isStammering` (`B3/StammeringApproximants.lean`).
  Proved via the contrapositive (the harder, "eventually periodic ⟹ rational" half): eventual
  periodicity makes `Sᴺ v` a **shift periodic point** (`shiftPeriodicPoint_mem_ratInt`,
  `digitExpansion_injective`), whose *finite* telescope (`BL.parity_partial_expansion`) collapses to
  `(1 − 2^p)·w = C ∈ ℕ`, a rational — no infinite geometric series.
* `ratInt_imp_eventuallyPeriodicParity` — **forward direction (rational ⟹ eventually-periodic parities),
  now PROVED.** If the parity vector `parityVector n ∈ RatInt = ℚ ∩ ℤ₂`, then `n`'s parity sequence
  `j ↦ parity (Tʲ n)` is eventually periodic. Phrased in the `L90` parity-sequence vocabulary
  (`L90.EventuallyPeriodicParity`, on `↑n : ℚ`) so it feeds Lagarias's Corollary 2.1b inside the report
  §7.1 capstone `B3.divergent_imp_not_automatic` (`B3/NoDivergence.lean`).

## The proof of the forward direction

The forward direction is the *easy* (provable, elementary) half. It rests on the **finiteness of the
shift-orbit** of a rational `2`-adic integer, `BL.ratInt_S_orbit_finite` — **imported from
`BL.ConjugacyMap`** (where it discharges `BL.periodicity_imp_no_divergent_trajectories`), together with
its supporting `BL.S_value` / `BL.boundedRat_finite` / `BL.ratInt_odd_den`. (These were originally
proved here and have since been moved down to BL, their natural home, so this file just reuses them.)

* `ratInt_eventuallyPeriodic_binaryDigit` — a finite orbit forces a repeat `Sⁱ v = Sʲ v`, hence the
  digit sequence `binaryDigit v = parity ∘ (Sᵏ v)` is eventually periodic.
* `digit_eq` — the `L90` parity sequence equals the binary-digit sequence: both `binaryDigit
  (parityVector n) j` and `L90.parity (L90.Tʲ ↑n)` equal the `j`-th Collatz parity bit `(Tʲ n) mod 2`
  (via `Φ⁻¹ = Q`, the inverse semiconjugacy `Sʲ ∘ Φ⁻¹ = Φ⁻¹ ∘ T₂ʲ`, parity preservation, and the
  `natCast` bridges).

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (Condition (∗)_w; rationality ⟺ eventual periodicity of the expansion).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the parity-vector map and binary digits of `2`-adic integers).
* [Lag90] Lagarias, Jeffrey C. *The set of rational cycles for the `3x+1` problem.* Acta Arithmetica 56
  (1990), 33–53 (the parity-sequence vocabulary of Corollary 2.1b that the forward direction feeds).
-/

namespace B3

open BL AB Function

/-- **Binary digits determine the `2`-adic integer.** If `x` and `y` have the same shift-parity at
every position (`parity (Sᵏ x) = parity (Sᵏ y)` for all `k`) then `x = y`: both reconstruct from those
digits via `tsum_parity_S`. The injectivity behind uniqueness of binary expansions. -/
@[category API, AMS 11 37, ref "BL96"]
theorem digitExpansion_injective {x y : ℤ_[2]}
    (h : ∀ k, parity (S^[k] x) = parity (S^[k] y)) : x = y := by
  rw [← tsum_parity_S x, ← tsum_parity_S y]
  exact tsum_congr fun i => by rw [h i]

/-- **A shift periodic point is rational.** If `S^[p] w = w` with `p > 0`, then `w ∈ RatInt`. *Proof:*
the finite binary expansion `parity_partial_expansion w p` reads `w = C + 2^p · S^[p] w` with
`C = ∑_{i<p} parity(Sⁱw)·2ⁱ ∈ ℕ`; substituting `S^[p] w = w` collapses it to `(1 − 2^p)·w = C`. Since
`‖2^p‖ < 1` (as `p > 0`), `1 − 2^p ≠ 0`, so in the field `ℚ₂` we get `w = C/(1 − 2^p)`, a rational
value. (`1 − 2^p` is the odd—hence unit—denominator of the standard closed form.) -/
@[category research solved, AMS 11 37, ref "BL96" "AB07", group "b3_missing_lemma"]
theorem shiftPeriodicPoint_mem_ratInt {w : ℤ_[2]} {p : ℕ} (hp : 0 < p)
    (hfix : S^[p] w = w) : w ∈ RatInt := by
  set C : ℕ := ∑ i ∈ Finset.range p, parity (S^[i] w) * 2 ^ i with hC
  have hCcast : ((C : ℕ) : ℤ_[2]) = ∑ i ∈ Finset.range p, (parity (S^[i] w) : ℤ_[2]) * 2 ^ i := by
    rw [hC]; push_cast; ring
  have hexp := parity_partial_expansion w p
  rw [hfix, ← hCcast] at hexp
  have hkey : (1 - (2 : ℤ_[2]) ^ p) * w = (C : ℤ_[2]) := by linear_combination hexp
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hRnorm : ‖(2 : ℤ_[2]) ^ p‖ < 1 := by
    rw [norm_pow]
    calc ‖(2 : ℤ_[2])‖ ^ p ≤ ‖(2 : ℤ_[2])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) h2lt1.le hp
      _ = ‖(2 : ℤ_[2])‖ := pow_one _
      _ < 1 := h2lt1
  have hne2 : (1 : ℤ_[2]) - 2 ^ p ≠ 0 := by
    intro hh
    have h1 : (2 : ℤ_[2]) ^ p = 1 := by linear_combination -hh
    rw [h1, norm_one] at hRnorm; exact lt_irrefl 1 hRnorm
  have hcQ : ((1 : ℚ_[2]) - 2 ^ p) * (w : ℚ_[2]) = (C : ℚ_[2]) := by
    exact_mod_cast congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hkey
  have hneQ : (1 : ℚ_[2]) - 2 ^ p ≠ 0 := by
    have h0 : ((1 - 2 ^ p : ℤ_[2]) : ℚ_[2]) ≠ ((0 : ℤ_[2]) : ℚ_[2]) :=
      fun hh => hne2 (PadicInt.ext hh)
    push_cast at h0; exact h0
  refine ⟨(C : ℚ) / ((1 : ℚ) - 2 ^ p), ?_⟩
  push_cast
  rw [eq_div_iff hneQ]
  linear_combination hcQ

/-- **(was cited; now PROVED.)** An **irrational** `2`-adic integer has a **non-eventually-periodic**
binary expansion. Equivalently (contrapositive), an eventually periodic binary expansion sums to a
rational (a `2`-adic integer in `RatInt = ℚ ∩ ℤ₂`) — the `2`-adic analogue of "eventually periodic
decimal ⟺ rational". The bridge from Phase 1's irrationality hypothesis `v ∉ RatInt` to the "not
eventually periodic" clause of Condition (∗)_w. *Proof of the contrapositive:* eventual periodicity
(preperiod `N`, period `p`) makes `w := Sᴺ v` a shift periodic point `S^[p] w = w` — both `S^{N+p} v`
and `Sᴺ v` have identical digits (`digitExpansion_injective`) — so `w ∈ RatInt`
(`shiftPeriodicPoint_mem_ratInt`), and `v = A + 2ᴺ·w` (`parity_partial_expansion`) is rational. No
infinite geometric series is needed; the finite telescope plus the periodic point suffice. -/
@[category research solved, AMS 11, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem not_isEventuallyPeriodic_binaryDigit (v : ℤ_[2]) (h : v ∉ RatInt) :
    ¬ AB.IsEventuallyPeriodic (binaryDigit v) := by
  intro hper
  apply h
  obtain ⟨N, p, hp, hper⟩ := hper
  have hfix : S^[p] (S^[N] v) = S^[N] v := by
    apply digitExpansion_injective
    intro k
    simp only [← Function.iterate_add_apply]
    have hk := hper (k + N) (Nat.le_add_left N k)
    simp only [binaryDigit] at hk
    rw [show k + (p + N) = k + N + p from by omega]
    exact hk
  obtain ⟨qw, hqw⟩ := shiftPeriodicPoint_mem_ratInt hp hfix
  set A : ℕ := ∑ i ∈ Finset.range N, parity (S^[i] v) * 2 ^ i with hA
  have hAcast : ((A : ℕ) : ℤ_[2]) = ∑ i ∈ Finset.range N, (parity (S^[i] v) : ℤ_[2]) * 2 ^ i := by
    rw [hA]; push_cast; ring
  have hexp := parity_partial_expansion v N
  rw [← hAcast] at hexp
  refine ⟨(A : ℚ) + 2 ^ N * qw, ?_⟩
  have hvQ : (v : ℚ_[2]) = (A : ℚ_[2]) + 2 ^ N * ((S^[N] v : ℤ_[2]) : ℚ_[2]) := by
    exact_mod_cast congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hexp
  rw [hvQ, hqw]
  push_cast
  ring

/-- **Forward digit periodicity (proved).** A rational `2`-adic integer `v ∈ RatInt` has an **eventually
periodic** binary expansion `binaryDigit v`. *Proof:* the finite shift-orbit (`ratInt_S_orbit_finite`)
forces a repeat `Sⁱ v = Sʲ v` (`i < j`); then for all `k ≥ i`, `S^{k+(j−i)} v = Sᵏ v`, so
`binaryDigit v (k+(j−i)) = binaryDigit v k`. This is the provable companion of the cited
`not_isEventuallyPeriodic_binaryDigit`. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem ratInt_eventuallyPeriodic_binaryDigit {v : ℤ_[2]} (hv : v ∈ RatInt) :
    AB.IsEventuallyPeriodic (binaryDigit v) := by
  have hni : ¬ Injective (fun k => S^[k] v) :=
    fun hinj => (Set.infinite_range_of_injective hinj) (ratInt_S_orbit_finite hv)
  rw [Function.not_injective_iff] at hni
  obtain ⟨a, b, hfab, hne⟩ := hni
  have key : ∀ i j : ℕ, i < j → S^[i] v = S^[j] v → AB.IsEventuallyPeriodic (binaryDigit v) := by
    intro i j hlt heq
    refine ⟨i, j - i, by omega, fun k hk => ?_⟩
    show binaryDigit v (k + (j - i)) = binaryDigit v k
    unfold binaryDigit
    have hper : S^[k + (j - i)] v = S^[k] v := by
      conv_lhs => rw [show k + (j - i) = (k - i) + j from by omega, Function.iterate_add_apply,
        ← heq, ← Function.iterate_add_apply, show (k - i) + i = k from by omega]
    rw [hper]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key a b hlt hfab
  · exact key b a hgt hfab.symm

/-! ### The digit sequence is the `L90` parity sequence -/

/-- The `2`-adic and `ℚ`-side parities of a natural number agree: `parity (↑m : ℤ₂) = L90.parity (↑m : ℚ)`
— both equal `m mod 2`. -/
@[category API, AMS 11 37, ref "BL96" "Lag90"]
theorem parityBridge (m : ℕ) : parity (m : ℤ_[2]) = L90.parity (m : ℚ) := by
  have h1 : parity (m : ℤ_[2]) = m % 2 := by unfold parity; rw [map_natCast, ZMod.val_natCast]
  have h2 : L90.parity (m : ℚ) = m % 2 := by unfold L90.parity; rw [Rat.num_natCast]; omega
  rw [h1, h2]

/-- **The binary digit equals the `L90` parity bit.** `binaryDigit (parityVector n) j =
L90.parity (L90.Tʲ ↑n)` — both are the `j`-th Collatz parity bit `(Tʲ n) mod 2`. *Proof:* on the left,
`parityVector n = Q ↑n = Φ⁻¹ ↑n` (`Φ_symm_eq_Q`), the inverse semiconjugacy `Sʲ ∘ Φ⁻¹ = Φ⁻¹ ∘ T₂ʲ` and
parity preservation `parity ∘ Φ⁻¹ = parity` reduce the `j`-th digit to `parity (T₂ʲ ↑n)`; both sides then
land on the integer parity via the `natCast` bridges (`T₂_iterate_natCast`, `L90.T_iterate_natCast`,
`parityBridge`). -/
@[category API, AMS 11 37, ref "BL96" "Lag90"]
theorem digit_eq (n j : ℕ) :
    binaryDigit (parityVector n) j = L90.parity (L90.T^[j] (n : ℚ)) := by
  have hsc : ∀ w, Φ.symm (T₂ w) = S (Φ.symm w) := by
    intro w; apply Φ.injective
    rw [Φ.apply_symm_apply, Φ_semiconj (Φ.symm w), Φ.apply_symm_apply]
  have hiter : ∀ (i : ℕ) (x : ℤ_[2]), S^[i] (Φ.symm x) = Φ.symm (T₂^[i] x) := by
    intro i x; induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hsc]
  have hpar : ∀ z, parity (Φ.symm z) = parity z := by
    intro z; have h := Φ_parity (Φ.symm z); rw [Φ.apply_symm_apply] at h; exact h.symm
  unfold binaryDigit parityVector
  rw [← Φ_symm_eq_Q, hiter, hpar, T₂_iterate_natCast, parityBridge, L90.T_iterate_natCast,
    T_iter_eq_iterate]

/-- **Digit-periodicity, forward direction (PROVED).** *If the parity vector of `n` is rational
(`parityVector n ∈ RatInt = ℚ ∩ ℤ₂`), then `n`'s parity sequence `j ↦ parity (Tʲ n)` is **eventually
periodic**.* The forward half of the `2`-adic "rational ⟺ eventually periodic expansion" equivalence,
phrased in the `L90` parity-sequence vocabulary so it feeds Lagarias's Corollary 2.1b with no further
glue. **Proved** (was a cited axiom): `ratInt_eventuallyPeriodic_binaryDigit` gives eventual periodicity
of the binary digits, which `digit_eq` identifies with the `L90` parity sequence. -/
@[category research solved, AMS 11 37, ref "AB07" "BL96" "Lag90", group "b3_missing_lemma"]
theorem ratInt_imp_eventuallyPeriodicParity (n : ℕ) (h : parityVector n ∈ RatInt) :
    L90.EventuallyPeriodicParity (n : ℚ) := by
  obtain ⟨N, p, hp, hper⟩ := ratInt_eventuallyPeriodic_binaryDigit h
  refine ⟨N, p, hp, fun j hj => ?_⟩
  rw [← digit_eq n (j + p), ← digit_eq n j]
  exact hper j hj

end B3
