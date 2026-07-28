/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — the three open conjectures of BL96 §1

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

`BL/ConjugacyMap.lean` builds the conjugacy map `Φ` and everything provable about it. This file
holds the three statements of BL96 §1 that are **open**, and nothing else:

* **`periodicity_conjecture`** — `Φ(ℚ ∩ ℤ₂) = ℚ ∩ ℤ₂`;
* **`fixed_point_conjecture`** — `Φ` has exactly two odd fixed points, `-1` and `1/3`;
* **`conjugacy_finiteness_conjecture`** — for each `j`, finitely many odd points of period `2ʲ`.

## Why they are segregated, and why they are `sorry`s and not axioms

Corpus policy forbids axiomatising an open conjecture: an `axiom` asserts a refereed fact, and
these are not facts yet. So each is a `theorem` carrying `@[category research open]` **and** a
`sorry` — the only construct that records "this statement is the conjecture" without letting any
proof consume it. Keeping them in one small file means the three `sorry` warnings are localised
and self-explanatory: `BL/ConjugacyMap.lean` is now `sorry`-free, and any future `sorry` warning
from it is a genuine defect rather than a policy artefact.

Nothing imports this file. That is deliberate — a consumer would be building on an unproved
statement. The results that *do* concern these conjectures live in `BL.ConjugacyMap` and take the
statement as an explicit **hypothesis** rather than referring to the declarations here:

* `BL.periodicity_imp_no_divergent_trajectories` — the Periodicity Conjecture ⟹ the 3x+1 map has
  no divergent trajectory (proved as an implication);
* `BL.periodicity_conjecture_iff_iterate` — `Φ(ℚ∩ℤ₂) = ℚ∩ℤ₂ ↔ Φᵏ(ℚ∩ℤ₂) = ℚ∩ℤ₂` for `k ≥ 1`,
  proved **unconditionally** from the cited one-sided inclusion `BL.Φ_image_ratInt_subset`;
* `BL.conjugacy_finiteness_zero_of_fixed_point` — the Fixed Point Conjecture ⟹ the `j = 0` case of
  the Finiteness Conjecture (a `sorry`-free reduction between two conjectures).

The *known* halves are likewise proved or cited in `BL.ConjugacyMap`, not here:
`Φ_image_ratInt_subset` (the easy inclusion `Φ(ℚ∩ℤ₂) ⊆ ℚ∩ℤ₂`, cited), `Φ_neg_one` (`-1` really is
fixed, proved), `parity_neg_one` / `parity_inv_three` / `neg_one_ne_inv_three` (both candidate
fixed points are odd and distinct). What is left open below is in each case the reverse inclusion
or the finiteness itself.

## References

* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169.  (§1: all three conjectures.)
* [Ber94] Bernstein, Daniel J. *A noniterative 2-adic statement of the 3N+1 conjecture.* Proc.
  Amer. Math. Soc. 121 (1994), no. 2, 405–408.  (The explicit formula `(1.6)` behind the known
  inclusion and behind the paper's computation that `1/3` is fixed.)
-/

namespace BL

/-! ### The Periodicity Conjecture (BL96, §1) -/

/-- **Periodicity Conjecture (Bernstein–Lagarias 1996).** The 3x+1 conjugacy map `Φ` maps the
rational 2-adic integers **onto themselves**: `Φ(ℚ ∩ ℤ₂) = ℚ ∩ ℤ₂`. This is **open** — recorded as a
`sorry`ed `research open` statement (never an `axiom`, per the corpus policy on open conjectures). It
would imply that the 3x+1 map has no divergent trajectories
(`periodicity_imp_no_divergent_trajectories`).

The `⊆` half is *known* and carried as the cited axiom `Φ_image_ratInt_subset`; the open content is
`ℚ∩ℤ₂ ⊆ Φ(ℚ∩ℤ₂)`. By `periodicity_conjecture_iff_iterate` the statement is equivalent to the same
equality for any iterate `Φᵏ`, `k ≥ 1`. -/
@[category research open, AMS 11 37, ref "BL96", group "bl_periodicity_conjecture"]
theorem periodicity_conjecture : (⇑Φ) '' RatInt = RatInt := by
  sorry

/-! ### The Fixed Point Conjecture (BL96, §1) -/

/-- **Fixed Point Conjecture (Bernstein–Lagarias 1996).** The 3x+1 conjugacy map `Φ` has **exactly two
odd fixed points**, `-1` and `1/3`: the set of odd fixed points is `{-1, 1/3}`. **Open** — recorded as a
`sorry`ed `research open` statement (never an `axiom`). The `⊇` inclusion is *known*: `-1` is a fixed
point (`Φ_neg_one`, proved in `BL.ConjugacyMap`) and `1/3 = Ring.inverse 3` is one (the paper's
computation, via the explicit formula `(1.6)`), both odd (`parity_neg_one`, `parity_inv_three`) and
distinct (`neg_one_ne_inv_three`); the open content is `⊆`, that there is no *other* odd fixed
point. -/
@[category research open, AMS 11 37, ref "BL96", group "bl_fixed_point_conjecture"]
theorem fixed_point_conjecture :
    {x : ℤ_[2] | Φ x = x ∧ parity x = 1} = {-1, Ring.inverse 3} := by
  sorry

/-! ### The Conjugacy Finiteness Conjecture (BL96, §1) -/

/-- **3x+1 Conjugacy Finiteness Conjecture (Bernstein–Lagarias 1996).** For each `j ≥ 0`, the conjugacy
map `Φ` has **finitely many odd periodic points of period `2ʲ`** — i.e. the set of odd `x` with
`Φ^[2ʲ] x = x` (`Function.IsPeriodicPt Φ (2ʲ) x`) is finite. **Open** — recorded as a `sorry`ed
`research open` statement (never an `axiom`). It generalises the Fixed Point Conjecture: the `j = 0`
case (period `2⁰ = 1`) is finiteness of the odd *fixed* points, which `fixed_point_conjecture` sharpens
to "exactly two" — that reduction is proved, as `conjugacy_finiteness_zero_of_fixed_point` in
`BL.ConjugacyMap`. -/
@[category research open, AMS 11 37, ref "BL96", group "bl_finiteness_conjecture"]
theorem conjugacy_finiteness_conjecture (j : ℕ) :
    {x : ℤ_[2] | (⇑Φ)^[2 ^ j] x = x ∧ parity x = 1}.Finite := by
  sorry

end BL
