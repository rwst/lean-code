/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.ResidueClass
import TShift.FreeZone
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The window cap beyond one residue class — the three stretch variants of T1′

`TShift/ResidueClass.lean` proves the reduction T1′ is for: repulsion at the dates of one class
mod `q` caps every sojourn at `L ≤ κ(θ)·n + max((1+κ(θ))·q + C₀, q)`, because a class meets every
window of `q` consecutive dates.  Three variants of that argument were left open there, and are
built here (plan-Tshift-S5 WP6).

**(iii) The good-date abstraction, and the composition with an exceptional set.**  The window
argument consumes exactly one property of the class: *it meets every window of `g` consecutive
dates from some date on*.  `TShift.MeetsWindow` names it, `TShift.sojourn_cap_on` proves the cap
from it alone, and `TShift.sojourn_cap_class` is the instance.  The point of naming it is closure
under the defect of the other T-shift lane: removing a set of dates that is *bounded* — plan-S2's
exceptional set, which its Theorem A confines to boundedly many dyadic blocks — leaves the property
intact above the last removed date (`TShift.MeetsWindow.sdiff`, `TShift.MeetsWindow.sdiff_blocks`).
So the two defects compose additively, as report §1.5's D3 predicted.

They also compose to *nothing*, which is the finding this section records
(`TShift.isRepelledMulClass_of_sdiff_bounded`): `IsRepelledMulClass` is existential in its threshold
`n₀`, so a bounded exceptional set is absorbed into `n₀` and the composed hypothesis is literally
the class hypothesis again.  The composition lemma is therefore worth stating and worth *not*
instantiating: at the one instance available — plan-S2's bad blocks, whose finiteness is what
`TShift/DyadicBlocks.lean` proves from the Ridout cover — it reproduces a statement the corpus
already has, at the price of importing a cited axiom.  This file does not import it.

**(ii) The general base.**  The whole argument is base-agnostic: only the slope changes.
`TShift.sojourn_cap_class_base` is the cap at any real base `b > 1` with `TShift.kappaB b θ` in
place of `κ(θ)`, and base `3/2` is recovered verbatim.  What that buys is the first *unconditional*
inhabitant of the entire T1′ pipeline, payoff included: at base `5/2` the free `q`-adic floor of
`TShift/GeneralBase.lean` gives the rate `θ = 1/2` at every date, and
`κ_b(5/2, 1/2) = κ_floor(5,2) = 0.7565 < 1` (`TShift.freeZone_five_two`) — so
`TShift.sojourn_cap_class_five_two` is a class-restricted sojourn cap with a sublinear slope that
depends on no conjecture, no cited axiom and no unproved rate.  At base `3/2` the same instance has
slope `κ(1/2) = 1.70951 > 1` and says nothing; the pipeline is legible only because some base
inhabits it.

**(i) The single-target variant.**  T1′ is stated in multiplier form because a bound at one fixed
target `ρ` is unusable at the sojourn phases whose visits to `ρ` miss the class (finding F2 of gate
G‑A).  This section machine-checks both halves of that finding.  The obstruction is exact —
`TShift.not_biclass_of_not_modEq`: if `r ≢ s (mod gcd(q,p))` then *no* date at all satisfies both
congruences, and `TShift.not_biclass_two_six` is the flagship instance `(p,q) = (2,6)`, where half
the phases are lost.  When the congruence does hold, the window is `lcm(q,p)` and never `q`
(`TShift.exists_mem_biclass_Ico`), and the cap survives with that window
(`TShift.sojourn_cap_single`).

The single-target variant needs one identity the corpus did not have, report N2: inside a periodic
block the orbit shadows a *rotating* cycle member, `x_{n+1} − ρ_{i+1} = (3/2)(x_n − ρ_i)`.  It is
proved here in the form the argument uses (`TShift.sub_cycle_pow`, `TShift.abs_sub_cycle_le`,
`TShift.abs_sub_cycle_le_shift`, `TShift.shadow_at_phase`): two trajectories of the *same* affine
cocycle separate by exactly `r^j`, so the shadowing bound `(1/r)^{L'}` holds against the rotated
member, and periodicity turns "the rotated member is `ρ`" into the phase congruence
`n' ≡ s (mod p)`.  `TShift.abs_sub_fixed_le` of `TShift/Basic.lean` is the `p = 1` case, and is
re-derived here from the general one.

## What is not claimed

Nothing here proves a repulsion bound at base `3/2`, on any class, at any rate: every statement is
a reduction whose Diophantine hypothesis is open, exactly as in `TShift/ResidueClass.lean`.  The
base-`5/2` instance is unconditional but is not about base `3/2` — it inhabits the pipeline, it does
not feed it (the free zone `q² < p` excludes `3/2` by `TShift.not_freeZone_three_two`, and that
exclusion is the whole difficulty of the subject).  The single-target variant is *weaker* than the
multiplier form it complements, not an alternative to it: its window is `lcm(q,p)` instead of `q`,
it carries a phase hypothesis, and for `gcd(q,p) ∤ r − s` it is vacuous.

And the `κ`-discipline of report §9 is in force here as everywhere: below `θ* = 0.78885`
(`TShift.thetaFree`, `TShift.kappa_lt_free_iff`) the base-`3/2` conclusions of this file are already
unconditional at the better slope `κ_free = log₂(3/2)` (`TShift.free_sojourn_cap_logb`), so what
these statements record is which *hypotheses* suffice.  The base-`5/2` instance is exempt from that
caveat: its slope is `κ_floor(5,2) = 0.75647`, and the free carry-word cap at that base runs at
`κ_casc(5,2) = 1.32194 > 1` (`TShift.kappaFloor_mul_kappaCasc`), so there the class-restricted
statement is the better one.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`, no kernel `decide` on `ℚ` or `ℝ`.  Imports are `TShift.ResidueClass` and
`TShift.FreeZone`, both `std3` with zero cited axioms; nothing from `CITED/` or `BB13/` enters, and
the composition of §§1–3 is stated over an abstract bounded exceptional set precisely so that it
need not.

## References

* `plans/plan-Tshift-S5.html` — WP6 (this package: (i) the single-target variant, (ii) the
  general-base window cap, (iii) the class-∩-cofinite composition of D3), §1.4 D1/D3, §2;
  `plans/note-Tshift-S5-GA.html` §2 (finding F2 and its `1/gcd(p,q)` sharpening, with the
  brute-force phase census), §4 (finding F5);
  `plans/note-Tshift-S5-WP6.html` — the WP6 record.  Quoted numerals are the harness's:
  `python3 TShift/tshift_numerics.py s5 20000 6`.
* `report-Tshift.html` §1.4 (the circulated T1′), §1.5 (the sojourn cap), N2 (the cycle-shift
  identity proved here), N3 (the free zone), corrections C20, C21.
* `TShift/ResidueClass.lean` — T1′, the class window lemma, Theorem B, the descent;
  `TShift/FreeZone.lean` and `TShift/GeneralBase.lean` — `kappaB`, `sojourn_cap_base`,
  `kappaFloor`, the `q`-adic floor and the base-`5/2` free zone (plan-Tshift-S1314 WP4/WP5);
  `TShift/DyadicBlocks.lean` — plan-S2's bad blocks, the intended but deliberately unbuilt instance
  of the composition of §§1–3.
-/

namespace TShift

/-! ## 1. Good-date sets: syndetic with gap `g`

The window argument of `TShift/ResidueClass.lean` §8 uses one property of the residue class, and
`MeetsWindow` is that property with the class forgotten.  The cap of §3 is proved from it alone. -/

/-- `MeetsWindow G g n₀`: from the date `n₀` on, every window of `g` consecutive dates contains a
member of `G` — "syndetic with gap `g`, eventually".  A residue class mod `q` is the case
`g = q`, `n₀ = 0` (`meetsWindow_class`); the eventual form is what survives the removal of a
bounded set of dates (`MeetsWindow.sdiff`). -/
def MeetsWindow (G : Set ℕ) (g n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∃ m ∈ G, n ≤ m ∧ m < n + g

/-- A residue class meets every window of `q` consecutive dates, from the start: the window lemma
`TShift.exists_mem_class_Ico` in the abstraction of this file. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem meetsWindow_class {q : ℕ} (hq : 0 < q) (r : ℕ) :
    MeetsWindow {n | n % q = r % q} q 0 := by
  intro n _
  obtain ⟨m, h1, h2, h3⟩ := exists_mem_class_Ico hq n r
  exact ⟨m, h3, h1, h2⟩

/-- The property is monotone in the starting date. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem MeetsWindow.mono_start {G : Set ℕ} {g n₀ n₁ : ℕ} (h : MeetsWindow G g n₀) (hn : n₀ ≤ n₁) :
    MeetsWindow G g n₁ := fun n hn' => h n (le_trans hn hn')

/-- The property is monotone in the gap. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem MeetsWindow.gap_mono {G : Set ℕ} {g g' n₀ : ℕ} (h : MeetsWindow G g n₀) (hg : g ≤ g') :
    MeetsWindow G g' n₀ := by
  intro n hn
  obtain ⟨m, hmG, h1, h2⟩ := h n hn
  exact ⟨m, hmG, h1, by omega⟩

/-- **The composition step (D3).**  Deleting a *bounded* set of dates from a good-date set leaves
it good, above the last deleted date: the gap is unchanged and only the threshold moves.  This is
the whole content of "the class defect and an exceptional-set defect compose additively" — the
exceptional set costs a threshold, never a gap. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem MeetsWindow.sdiff {G S : Set ℕ} {g n₀ N : ℕ} (h : MeetsWindow G g n₀)
    (hS : ∀ x ∈ S, x < N) : MeetsWindow (G \ S) g (max n₀ N) := by
  intro n hn
  obtain ⟨m, hmG, h1, h2⟩ := h n (le_trans (le_max_left _ _) hn)
  have hN : N ≤ n := le_trans (le_max_right n₀ N) hn
  exact ⟨m, ⟨hmG, fun hmS => absurd (hS m hmS) (by omega)⟩, h1, h2⟩

/-- The same for a finite exceptional set: finiteness gives the bound. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem MeetsWindow.sdiff_finite {G S : Set ℕ} {g n₀ : ℕ} (h : MeetsWindow G g n₀)
    (hS : S.Finite) : ∃ n₁, MeetsWindow (G \ S) g n₁ := by
  obtain ⟨N, hN⟩ := hS.bddAbove
  exact ⟨max n₀ (N + 1), h.sdiff (fun x hx => by have := hN hx; omega)⟩

/-- **The composition step, in plan-S2's currency.**  If every excluded date lies in a dyadic block
of index at most `M` — `blockIdx = Nat.log 2` is `TShift.blockIdx` of `TShift/DyadicBlocks.lean`,
and plan-S2's Theorem A bounds the number of such blocks — then the excluded set is bounded by
`2^{M+1}` and the good-date property survives above it.

Stated over the index bound rather than over `TShift.badBlocks` on purpose: this file carries no
cited axiom, and the finiteness of the bad blocks is what the Ridout lane's axiom buys. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem MeetsWindow.sdiff_blocks {G S : Set ℕ} {g n₀ M : ℕ} (h : MeetsWindow G g n₀)
    (hS : ∀ x ∈ S, Nat.log 2 x ≤ M) : MeetsWindow (G \ S) g (max n₀ (2 ^ (M + 1))) := by
  refine h.sdiff (fun x hx => ?_)
  have h1 : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have h2 : (2 : ℕ) ^ (Nat.log 2 x + 1) ≤ 2 ^ (M + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := hS x hx; omega)
  omega

/-! ## 2. Repulsion on a set of dates

`IsRepelledMulOn θ D G` is `IsRepelledMulClass` with the class replaced by an arbitrary set of
dates.  It is not a new problem — `isRepelledMulOn_class_iff` says the class case is the old one —
but it is the form in which the composition of §1 can be applied to the Diophantine hypothesis as
well as to the window. -/

/-- The multiplier repulsion bound `‖D·(3/2)ⁿ‖ ≥ c·θⁿ`, demanded only at the dates of `G`. -/
def IsRepelledMulOn (θ : ℝ) (D : ℕ) (G : Set ℕ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ∈ G, n₀ ≤ n →
    c * θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)

/-- At a residue class the set form is the class form: no generality was added, only a name. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulOn_class_iff {θ : ℝ} {D q r : ℕ} :
    IsRepelledMulOn θ D {n | n % q = r % q} ↔ IsRepelledMulClass θ D q r := by
  constructor
  · rintro ⟨c, hc, n₀, h⟩
    exact ⟨c, hc, n₀, fun n hn hcls => h n hcls hn⟩
  · rintro ⟨c, hc, n₀, h⟩
    exact ⟨c, hc, n₀, fun n hcls hn => h n hn hcls⟩

/-- Restriction to a smaller set of dates: a bound on `G` is a bound on every subset. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem IsRepelledMulOn.mono {θ : ℝ} {D : ℕ} {G G' : Set ℕ} (h : IsRepelledMulOn θ D G)
    (hsub : G' ⊆ G) : IsRepelledMulOn θ D G' := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  exact ⟨c, hc, n₀, fun n hn => hn₀ n (hsub hn)⟩

/-- **The composition is invisible to the predicate.**  A class bound that is allowed to fail on a
*bounded* set of dates is a class bound: the exceptional set is absorbed into the threshold `n₀`,
which `IsRepelledMulClass` quantifies existentially.

This is the honest verdict on D3's composition at base `3/2`.  The defect of the exception-count
lane (plan-S2: the bad dates lie in boundedly many dyadic blocks, positions unlocated) costs the
class-restricted problem nothing at all, exactly as the ineffective threshold of the transported
record rate costs it nothing (plan-S1 WP7, finding F3).  What such a defect does cost is a
statement with exhibited numerals — `TShift.TShiftProblemAt` is the pattern — and there the
absorbing constant is precisely the unlocated quantity. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClass_of_sdiff_bounded {θ : ℝ} {D q r N : ℕ} {S : Set ℕ}
    (hS : ∀ x ∈ S, x < N) (h : IsRepelledMulOn θ D ({n | n % q = r % q} \ S)) :
    IsRepelledMulClass θ D q r := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  refine ⟨c, hc, max n₀ N, fun n hn hcls => ?_⟩
  have hNn : N ≤ n := le_trans (le_max_right n₀ N) hn
  exact hn₀ n ⟨hcls, fun hmS => absurd (hS n hmS) (by omega)⟩ (le_trans (le_max_left n₀ N) hn)

/-- The same with a finite exceptional set. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClass_of_sdiff_finite {θ : ℝ} {D q r : ℕ} {S : Set ℕ} (hS : S.Finite)
    (h : IsRepelledMulOn θ D ({n | n % q = r % q} \ S)) : IsRepelledMulClass θ D q r := by
  obtain ⟨N, hN⟩ := hS.bddAbove
  exact isRepelledMulClass_of_sdiff_bounded (N := N + 1) (fun x hx => by have := hN hx; omega) h

/-! ## 3. The cap over a good-date set

Theorem B of `TShift/ResidueClass.lean` with the class replaced by any good-date set: the proof is
the same two branches, and the class hypothesis is now consumed through `MeetsWindow` rather than
through the window lemma directly. -/

/-- **Theorem B, over a good-date set.**  Repulsion at the dates of `G`, plus "`G` meets every
window of `g` consecutive dates from `n₀` on", caps every sojourn at

  `L ≤ κ(θ)·n + max((1+κ(θ))·g + C₀, g)`,   `C₀ = -log c/log(3/2)`,

for every date past both thresholds.  `sojourn_cap_class` is the instance `G = ` the class,
`g = q`, `n₀ = 0` — checked immediately below.

Same non-claims as there: the rate is a hypothesis and is open above `2/3` on every set of dates of
positive density that anyone can name, and below `θ* = 0.78885` the conclusion holds
unconditionally at the better slope `κ_free = log₂(3/2)` (`free_sojourn_cap_logb`,
`kappa_lt_free_iff`). -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_on {θ : ℝ} {D g n₀ : ℕ} {G : Set ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (_hg : 0 < g)
    (hG : MeetsWindow G g n₀) (h : IsRepelledMulOn θ D G) :
    ∃ c > 0, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n') ≤ (2 / 3 : ℝ) ^ L') →
      (L : ℝ) ≤ kappa θ * n
        + max ((1 + kappa θ) * g + (-Real.log c) / Real.log (3 / 2)) g := by
  obtain ⟨c, hc, n₂, hn₂⟩ := h
  refine ⟨c, hc, max n₀ n₂, fun n hn L hshadow => ?_⟩
  rcases lt_or_ge L g with hshort | hlong
  · have hcap := sojourn_cap_window_short (n := n) hθ hθ1 hshort
    have hle := le_max_right ((1 + kappa θ) * g + (-Real.log c) / Real.log (3 / 2)) ((g : ℝ))
    linarith
  · obtain ⟨n', hn'G, hn'l, hn'r⟩ := hG n (le_trans (le_max_left n₀ n₂) hn)
    have hcap := sojourn_cap_window hc hθ hθ1 hn'l hn'r (by omega : L ≤ (n + L - n') + g)
      (hn₂ n' hn'G (le_trans (le_trans (le_max_right n₀ n₂) hn) hn'l))
      (hshadow n' (n + L - n') hn'l (by omega))
    have hle := le_max_left ((1 + kappa θ) * g + (-Real.log c) / Real.log (3 / 2)) ((g : ℝ))
    linarith

/-- `TShift.sojourn_cap_class` is the residue-class instance of `sojourn_cap_on`: the generalization
is machine-verified rather than asserted. -/
example {θ : ℝ} {D q r : ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hq : 0 < q)
    (h : IsRepelledMulClass θ D q r) :
    ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n') ≤ (2 / 3 : ℝ) ^ L') →
      (L : ℝ) ≤ kappa θ * n
        + max ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) q :=
  sojourn_cap_on hθ hθ1 hq (meetsWindow_class hq r) (isRepelledMulOn_class_iff.mpr h)

/-- **The composed cap (D3), packaged.**  A device that proves its bound on one residue class
*except* on a bounded set of dates still caps every sojourn, with the same gap `q` and a threshold
pushed past the exceptional set.  By `isRepelledMulClass_of_sdiff_bounded` the hypothesis is the
class hypothesis again; the statement is kept because the *route* is what D3 asked for and because
the two lanes' defects are visible in it side by side. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_class_sdiff {θ : ℝ} {D q r N : ℕ} {S : Set ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hq : 0 < q) (hS : ∀ x ∈ S, x < N)
    (h : IsRepelledMulOn θ D ({n | n % q = r % q} \ S)) :
    ∃ c > 0, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n') ≤ (2 / 3 : ℝ) ^ L') →
      (L : ℝ) ≤ kappa θ * n
        + max ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) q :=
  sojourn_cap_on hθ hθ1 hq ((meetsWindow_class hq r).sdiff hS) h

/-! ## 4. The payoff, in slope form

`TShift.dyadic_block_visit_window` is stated with `κ(θ)`; the general-base cap of §5 needs the same
statement with `kappaB b θ`, and the free lane already uses it with `κ_free`.  All three are the
same lemma in an abstract slope, so it is proved once here and the base-`3/2` version is recovered
as an instance. -/

/-- **The dyadic payoff at an abstract slope.**  An escape recursion `e_{k+1} ≤ (1+κ)·e_k + C` with
`κ < 1` puts a visit in every dyadic block above the burn-in `C/(1−κ)`.  `κ` is any real: the
sojourn slope of a repulsion rate (`kappa θ`, `kappaB b θ`) or the free carry-word slope
`κ_free = log₂(3/2)`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem dyadic_block_visit_slope {κ C : ℝ} {e : ℕ → ℝ} {k₀ m : ℕ} (hκ : κ < 1)
    (hmono : StrictMono e) (hunb : ∀ M : ℝ, ∃ k, M ≤ e k)
    (he : ∀ k, e (k + 1) ≤ (1 + κ) * e k + C)
    (hburn : C / (1 - κ) < e k₀) (hm : e k₀ ≤ 2 ^ m) :
    ∃ k, (2 : ℝ) ^ m ≤ e k ∧ e k < 2 ^ (m + 1) := by
  refine dyadic_block_visit hmono (fun k hk => ?_) hunb hm
  refine lt_two_mul_of_lt_two (by linarith) (he k) ?_
  rw [show (2 : ℝ) - (1 + κ) = 1 - κ by ring]
  exact lt_of_lt_of_le hburn (hmono.monotone hk)

/-- `TShift.dyadic_block_visit_window` is the `κ = kappa θ` instance. -/
example {θ C : ℝ} {e : ℕ → ℝ} {k₀ m : ℕ} (hκ : kappa θ < 1)
    (hmono : StrictMono e) (hunb : ∀ M : ℝ, ∃ k, M ≤ e k)
    (he : ∀ k, e (k + 1) ≤ (1 + kappa θ) * e k + C)
    (hburn : C / (1 - kappa θ) < e k₀) (hm : e k₀ ≤ 2 ^ m) :
    ∃ k, (2 : ℝ) ^ m ≤ e k ∧ e k < 2 ^ (m + 1) :=
  dyadic_block_visit_slope hκ hmono hunb he hburn hm

/-! ## 5. The window cap at a general base

Only the slope changes: `TShift.kappaB b θ = log(1/θ)/log b` in place of `κ(θ)`, and the shadowing
contraction `(1/b)^{L'}` in place of `(2/3)^{L'}`.  `TShift.sojourn_cap_base`
(`TShift/FreeZone.lean`, plan-S1314 WP5) is the unrestricted cap; these are its window versions. -/

/-- `κ_b(θ) ≥ 0` for `0 < θ ≤ 1` at any base `b > 1`: the general-base `kappa_nonneg`, and again the
step that makes the window shift a cost rather than a gift. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem kappaB_nonneg {b θ : ℝ} (hb : 1 < b) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : 0 ≤ kappaB b θ := by
  rw [kappaB]
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hθ.le hθ1)) (Real.log_pos hb).le

/-- **The window sojourn cap at base `b`, long branch.**  `sojourn_cap_base` applied at an
admissible date in the window `[n, n+g)`, paying `κ_b(θ)·g` for the shifted date and `g` for the
shortened block. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_window_base {b c θ d' : ℝ} {n n' L L' g : ℕ} (hb : 1 < b) (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (_hn' : n ≤ n') (hwin : n' < n + g) (hL : L ≤ L' + g)
    (hrep : c * θ ^ n' ≤ d') (hshadow : d' ≤ (1 / b) ^ L') :
    (L : ℝ) ≤ kappaB b θ * n + ((1 + kappaB b θ) * g + (-Real.log c) / Real.log b) := by
  have hκ := kappaB_nonneg hb hθ hθ1
  have hcap := sojourn_cap_base hb hc hθ hrep hshadow
  have hLR : (L : ℝ) ≤ (L' : ℝ) + g := by exact_mod_cast hL
  have hn'R : (n' : ℝ) ≤ (n : ℝ) + g := by exact_mod_cast (by omega : n' ≤ n + g)
  have hmul : kappaB b θ * n' ≤ kappaB b θ * ((n : ℝ) + g) := mul_le_mul_of_nonneg_left hn'R hκ
  linarith

/-- **The window sojourn cap at base `b`, short branch** — a sojourn shorter than the window needs
no repulsion input, at any base. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_window_base_short {b θ : ℝ} {n L g : ℕ} (hb : 1 < b) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hLg : L < g) : (L : ℝ) ≤ kappaB b θ * n + g := by
  have hκn : (0 : ℝ) ≤ kappaB b θ * n :=
    mul_nonneg (kappaB_nonneg hb hθ hθ1) (Nat.cast_nonneg n)
  have hLR : (L : ℝ) < g := by exact_mod_cast hLg
  linarith

/-- The class-restricted repulsion predicate at a general base: `‖D·bⁿ‖ ≥ c·θⁿ` at the dates of one
class.  `IsRepelledMulClass` is the case `b = 3/2` (`isRepelledMulClassB_three_halves_iff`). -/
def IsRepelledMulClassB (b θ : ℝ) (D q r : ℕ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, n % q = r % q →
    c * θ ^ n ≤ distToNearestInt ((D : ℝ) * b ^ n)

/-- Base `3/2` is the base-`3/2` predicate: the generalization renames nothing. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClassB_three_halves_iff {θ : ℝ} {D q r : ℕ} :
    IsRepelledMulClassB (3 / 2) θ D q r ↔ IsRepelledMulClass θ D q r := Iff.rfl

/-- **Theorem B at a general base.**  Class-restricted repulsion at rate `θ ∈ (0,1]` against the
contraction `1/b` caps every sojourn at `L ≤ κ_b(θ)·n + max((1+κ_b(θ))·q + C₀, q)`,
`C₀ = -log c/log b`.  The base-`3/2` case is `sojourn_cap_class`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_class_base {b θ : ℝ} {D q r : ℕ} (hb : 1 < b) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hq : 0 < q) (h : IsRepelledMulClassB b θ D q r) :
    ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * b ^ n') ≤ (1 / b) ^ L') →
      (L : ℝ) ≤ kappaB b θ * n
        + max ((1 + kappaB b θ) * q + (-Real.log c) / Real.log b) q := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  refine ⟨c, hc, n₀, fun n hn L hshadow => ?_⟩
  rcases lt_or_ge L q with hshort | hlong
  · have hcap := sojourn_cap_window_base_short (b := b) (n := n) hb hθ hθ1 hshort
    have hle := le_max_right ((1 + kappaB b θ) * q + (-Real.log c) / Real.log b) ((q : ℝ))
    linarith
  · obtain ⟨n', hn'l, hn'r, hn'c⟩ := exists_mem_class_Ico hq n r
    have hcap := sojourn_cap_window_base hb hc hθ hθ1 hn'l hn'r (by omega : L ≤ (n + L - n') + q)
      (hn₀ n' (le_trans hn hn'l) hn'c) (hshadow n' (n + L - n') hn'l (by omega))
    have hle := le_max_left ((1 + kappaB b θ) * q + (-Real.log c) / Real.log b) ((q : ℝ))
    linarith

/-! ## 6. The unconditional inhabitant: base `5/2`

Report N3's free zone (`q² < p`) is where the `q`-adic floor alone gives a sublinear sojourn cap.
Base `5/2` is in it and base `3/2` is not, which is the whole reason the T-shift problem is hard.
The instance below is what the pipeline of §§1–5 looks like when its Diophantine hypothesis is a
theorem: rate `θ = 1/2` at every date from the free floor, hence on every class, hence a window cap
at slope `κ_floor(5,2) = 0.75647 < 1`, unconditionally and with no cited axiom. -/

/-- **The free `q`-adic floor as a class-restricted repulsion bound at base `5/2`.**  For odd `D`,
`‖D·(5/2)ⁿ‖ ≥ (1/2)ⁿ` at every date (`distToNearestInt_mul_ge_base`), hence on every class.  Unlike
every rate at base `3/2` this is a theorem, and unlike the base-`3/2` free rate its slope is below
`1`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClassB_five_two_half {D : ℕ} (hD : Odd D) (q r : ℕ) :
    IsRepelledMulClassB (5 / 2) (1 / 2) D q r := by
  refine ⟨1, one_pos, 1, fun n hn _ => ?_⟩
  have h := distToNearestInt_mul_ge_base (p := 5) (q := 2) (by norm_num) (by norm_num)
    (D := D) (Nat.coprime_two_right.mpr hD) hn
  have hcast : (((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = (5 : ℝ) / 2 := by norm_num
  rw [hcast] at h
  calc (1 : ℝ) * (1 / 2) ^ n = 1 / ((2 : ℕ) : ℝ) ^ n := by push_cast; rw [div_pow]; ring
    _ ≤ distToNearestInt ((D : ℝ) * ((5 : ℝ) / 2) ^ n) := h

/-- `κ_b(5/2, 1/2) = κ_floor(5,2) = log 2/log(5/2) = 0.75647 < 1`: the free zone, in the slope
currency of this file. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem kappaB_five_two_half_lt_one : kappaB ((5 : ℝ) / 2) (1 / 2) < 1 := by
  have h := kappaFloor_eq_kappaB (p := 5) (q := 2)
  have hcast : kappaB (((5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) (1 / ((2 : ℕ) : ℝ))
      = kappaB ((5 : ℝ) / 2) (1 / 2) := by norm_num
  rw [hcast] at h
  rw [← h]
  exact freeZone_five_two

/-- **The template.**  The whole T1′ pipeline, unconditional, at base `5/2`: for every odd
multiplier and every residue class, every sojourn obeys `L ≤ κ·n + C` with
`κ = κ_b(5/2,1/2) < 1` — no cited axiom, no unproved rate, no open hypothesis except the
combinatorial shadowing premise that every statement of this circle carries (S13(iii)).

This is what report §1.5's payoff would look like at base `3/2` if the rate existed there.  It does
not: the free zone is `q² < p` (`freeZone_iff`), which excludes `3/2` (`not_freeZone_three_two`),
and at base `3/2` the same instance has slope `κ(1/2) = 1.70951 > 1` (`one_lt_kappa_half`). -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_class_five_two {D q r : ℕ} (hD : Odd D) (hq : 0 < q) :
    ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * ((5 : ℝ) / 2) ^ n') ≤ (1 / ((5 : ℝ) / 2)) ^ L') →
      (L : ℝ) ≤ kappaB ((5 : ℝ) / 2) (1 / 2) * n
        + max ((1 + kappaB ((5 : ℝ) / 2) (1 / 2)) * q
            + (-Real.log c) / Real.log ((5 : ℝ) / 2)) q :=
  sojourn_cap_class_base (by norm_num) (by norm_num) (by norm_num) hq
    (isRepelledMulClassB_five_two_half hD q r)

/-- **The template, payoff included.**  At base `5/2` the escape recursion runs at the
*unconditional* slope `κ_b(5/2,1/2) < 1`, so every dyadic block of dates past the burn-in carries a
visit — report §1.5's conclusion with no Diophantine hypothesis anywhere, at a base where the
`q`-adic floor is enough.

The contrast with base `3/2` is the point.  There the same free rate gives `κ(1/2) = 1.70951 > 1`
and this corollary is unavailable; the unconditional dyadic payoff at base `3/2`
(`TShift.dyadic_block_visit`) comes from the *carry-word* ceiling instead, at
`κ_free = log₂(3/2)` (C20), and repulsion would improve on it only above `θ* = 0.78885`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem dyadic_block_visit_five_two {C : ℝ} {e : ℕ → ℝ} {k₀ m : ℕ} (hmono : StrictMono e)
    (hunb : ∀ M : ℝ, ∃ k, M ≤ e k)
    (he : ∀ k, e (k + 1) ≤ (1 + kappaB ((5 : ℝ) / 2) (1 / 2)) * e k + C)
    (hburn : C / (1 - kappaB ((5 : ℝ) / 2) (1 / 2)) < e k₀) (hm : e k₀ ≤ 2 ^ m) :
    ∃ k, (2 : ℝ) ^ m ≤ e k ∧ e k < 2 ^ (m + 1) :=
  dyadic_block_visit_slope kappaB_five_two_half_lt_one hmono hunb he hburn hm

/-! ## 7. The single-target variant, and the identity it needs (report N2)

T1′ is stated in multiplier form because the single-target reading of report §6's S5 line is false
(gate G‑A, finding F2).  This section proves both halves of that finding and then the variant that
survives it.

The mechanism is the cycle-shift identity of report N2: inside a `p`-periodic block the orbit does
not shadow a fixed target but a rotating one, `x_{n+1} − ρ_{i+1} = (3/2)(x_n − ρ_i)`.  In the form
the argument uses it, this is a statement about two trajectories of the same affine cocycle — the
orbit and the cycle share the carry sequence — so `sub_cycle_pow` is proved for an arbitrary shift
sequence `c` and specializes to both. -/

/-- **Report N2, the identity.**  Two trajectories of the *same* affine cocycle `t ↦ r·t − c i`
separate by exactly `r^j`.  With `u` the orbit and `v` the cycle this is
`x_{n+j} − ρ_{i+j} = (3/2)^j (x_n − ρ_i)`: the target the orbit shadows advances by one member each
date, which is why a bound at a fixed member is a bound at one class of dates mod `p`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sub_cycle_pow {r : ℝ} {u v c : ℕ → ℝ} (hu : ∀ i, u (i + 1) = r * u i - c i)
    (hv : ∀ i, v (i + 1) = r * v i - c i) (j : ℕ) : u j - v j = r ^ j * (u 0 - v 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : u (j + 1) - v (j + 1) = r * (u j - v j) := by rw [hu j, hv j]; ring
      rw [hstep, ih]
      ring

/-- **The shadowing bound against a rotating target.**  If the two trajectories are still within
`1` of each other after `j` steps, they started within `(1/r)^j` — `TShift.abs_sub_fixed_le` with
the fixed point replaced by a second trajectory. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem abs_sub_cycle_le {r : ℝ} {u v c : ℕ → ℝ} (hr : 1 < r) (hu : ∀ i, u (i + 1) = r * u i - c i)
    (hv : ∀ i, v (i + 1) = r * v i - c i) {j : ℕ} (hb : |u j - v j| ≤ 1) :
    |u 0 - v 0| ≤ (1 / r) ^ j := by
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have hrj : (0 : ℝ) < r ^ j := by positivity
  have habs : |u j - v j| = r ^ j * |u 0 - v 0| := by
    rw [sub_cycle_pow hu hv j, abs_mul, abs_of_pos hrj]
  rw [div_pow, one_pow, le_div_iff₀ hrj, mul_comm]
  linarith [habs ▸ hb]

/-- `TShift.abs_sub_fixed_le` is the constant-second-trajectory case: a fixed point of the affine
map is the trajectory that stays put.  The `p = 1` cycle, in the language of this section. -/
example {r c ρ : ℝ} (hr : 1 < r) (hfix : r * ρ - c = ρ) {z : ℕ → ℝ}
    (hz : ∀ i, z (i + 1) = r * z i - c) {j : ℕ} (hb : |z j - ρ| ≤ 1) :
    |z 0 - ρ| ≤ (1 / r) ^ j :=
  abs_sub_cycle_le (v := fun _ => ρ) (c := fun _ => c) hr hz (fun _ => hfix.symm) hb

/-- The shifted form: the same bound applied inside a block, from the date `i` to the block end
`j`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem abs_sub_cycle_le_shift {r : ℝ} {u v c : ℕ → ℝ} (hr : 1 < r)
    (hu : ∀ i, u (i + 1) = r * u i - c i) (hv : ∀ i, v (i + 1) = r * v i - c i)
    {i j : ℕ} (hij : i ≤ j) (hb : |u j - v j| ≤ 1) : |u i - v i| ≤ (1 / r) ^ (j - i) := by
  have hu' : ∀ k, (fun k => u (i + k)) (k + 1) = r * (fun k => u (i + k)) k
      - (fun k => c (i + k)) k := by
    intro k
    show u (i + (k + 1)) = r * u (i + k) - c (i + k)
    rw [show i + (k + 1) = (i + k) + 1 by ring]
    exact hu (i + k)
  have hv' : ∀ k, (fun k => v (i + k)) (k + 1) = r * (fun k => v (i + k)) k
      - (fun k => c (i + k)) k := by
    intro k
    show v (i + (k + 1)) = r * v (i + k) - c (i + k)
    rw [show i + (k + 1) = (i + k) + 1 by ring]
    exact hv (i + k)
  have hend : |(fun k => u (i + k)) (j - i) - (fun k => v (i + k)) (j - i)| ≤ 1 := by
    show |u (i + (j - i)) - v (i + (j - i))| ≤ 1
    rw [show i + (j - i) = j by omega]
    exact hb
  simpa using abs_sub_cycle_le (u := fun k => u (i + k)) (v := fun k => v (i + k))
    (c := fun k => c (i + k)) hr hu' hv' hend

/-- A `p`-periodic trajectory takes the same value at dates of the same class mod `p`: the
elementary fact that turns "the orbit shadows the member `ρ`" into a congruence on the date. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem periodic_eq_of_mod {v : ℕ → ℝ} {p : ℕ} (hper : ∀ i, v (i + p) = v i) {m s : ℕ}
    (h : m % p = s % p) : v m = v s := by
  have key : ∀ a k : ℕ, v (a + p * k) = v a := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show a + p * (k + 1) = (a + p * k) + p by ring, hper, ih]
  have h1 : v m = v (m % p) := by
    conv_lhs => rw [← Nat.mod_add_div m p]
    exact key _ _
  have h2 : v s = v (s % p) := by
    conv_lhs => rw [← Nat.mod_add_div s p]
    exact key _ _
  rw [h1, h2, h]

/-- **The shadowing hypothesis of the single-target variant, derived.**  Inside a block on which
the orbit `u` and the `p`-periodic cycle `v` share their carries, at a date `i` of the phase class
of `s` the orbit is within `(1/r)^{j-i}` of the *fixed* member `v s`.

This is what makes the phase-restricted hypothesis of `sojourn_cap_single` the right one: the
single-target bound is usable exactly at the dates `i ≡ s (mod p)`, and `s` is a property of the
sojourn, not of the device. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem shadow_at_phase {r : ℝ} {u v c : ℕ → ℝ} {p : ℕ} (hr : 1 < r)
    (hu : ∀ i, u (i + 1) = r * u i - c i) (hv : ∀ i, v (i + 1) = r * v i - c i)
    (hper : ∀ i, v (i + p) = v i) {i j s : ℕ} (hij : i ≤ j) (hb : |u j - v j| ≤ 1)
    (hphase : i % p = s % p) : |u i - v s| ≤ (1 / r) ^ (j - i) := by
  rw [← periodic_eq_of_mod hper hphase]
  exact abs_sub_cycle_le_shift hr hu hv hij hb

/-! ### The two congruences

A single-target bound on the class `r` mod `q` is usable at a sojourn of phase `s` mod `p` only at
dates meeting both congruences.  That set is a class mod `lcm(q,p)` when `r ≡ s (mod gcd(q,p))`,
and is **empty** otherwise — F2, both halves. -/

/-- **The window lemma for two congruences.**  If `r ≡ s (mod gcd(q,p))` then every window of
`lcm(q,p)` consecutive dates contains a date in both classes.  The guaranteed window is `lcm(q,p)`,
never `q`: that is the price the single-target form pays over the multiplier form, and it is a price
even in the coprime case, where `lcm(q,p) = q·p`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem exists_mem_biclass_Ico {q p : ℕ} (hq : 0 < q) (hp : 0 < p) {r s : ℕ}
    (h : r ≡ s [MOD Nat.gcd q p]) (n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + Nat.lcm q p ∧ m % q = r % q ∧ m % p = s % p := by
  have hlcm : 0 < Nat.lcm q p := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  obtain ⟨k, hkr, hks⟩ := Nat.chineseRemainder' h
  obtain ⟨m, h1, h2, h3⟩ := exists_mem_class_Ico hlcm n k
  have hdq : q ∣ Nat.lcm q p := Nat.dvd_lcm_left q p
  have hdp : p ∣ Nat.lcm q p := Nat.dvd_lcm_right q p
  refine ⟨m, h1, h2, ?_, ?_⟩
  · calc m % q = m % Nat.lcm q p % q := (Nat.mod_mod_of_dvd m hdq).symm
      _ = k % Nat.lcm q p % q := by rw [h3]
      _ = k % q := Nat.mod_mod_of_dvd k hdq
      _ = r % q := hkr
  · calc m % p = m % Nat.lcm q p % p := (Nat.mod_mod_of_dvd m hdp).symm
      _ = k % Nat.lcm q p % p := by rw [h3]
      _ = k % p := Nat.mod_mod_of_dvd k hdp
      _ = s % p := hks

/-- The coprime case, which is the proviso WP6(i) was posed with: every phase is usable and the
window is `q·p`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem exists_mem_biclass_Ico_coprime {q p : ℕ} (hq : 0 < q) (hp : 0 < p)
    (hcop : Nat.Coprime q p) (r s n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + q * p ∧ m % q = r % q ∧ m % p = s % p := by
  have hg : Nat.gcd q p = 1 := hcop
  have h : r ≡ s [MOD Nat.gcd q p] := by
    show r % Nat.gcd q p = s % Nat.gcd q p
    rw [hg, Nat.mod_one, Nat.mod_one]
  have := exists_mem_biclass_Ico hq hp h n
  rwa [hcop.lcm_eq_mul] at this

/-- **The obstruction (F2), exactly.**  If `r ≢ s (mod gcd(q,p))` then *no* date satisfies both
congruences — not "a longer window", but none at all, at any window length.  So a single-target
class hypothesis is unusable at those sojourn phases, and for a fixed class the usable fraction of
phases is `1/gcd(q,p)`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem not_biclass_of_not_modEq {q p r s : ℕ} (h : ¬ (r ≡ s [MOD Nat.gcd q p])) (m : ℕ) :
    ¬ (m % q = r % q ∧ m % p = s % p) := by
  rintro ⟨h1, h2⟩
  refine h ?_
  have hdq : Nat.gcd q p ∣ q := Nat.gcd_dvd_left q p
  have hdp : Nat.gcd q p ∣ p := Nat.gcd_dvd_right q p
  show r % Nat.gcd q p = s % Nat.gcd q p
  calc r % Nat.gcd q p = r % q % Nat.gcd q p := (Nat.mod_mod_of_dvd r hdq).symm
    _ = m % q % Nat.gcd q p := by rw [h1]
    _ = m % Nat.gcd q p := Nat.mod_mod_of_dvd m hdq
    _ = m % p % Nat.gcd q p := (Nat.mod_mod_of_dvd m hdp).symm
    _ = s % p % Nat.gcd q p := by rw [h2]
    _ = s % Nat.gcd q p := Nat.mod_mod_of_dvd s hdp

/-- **The flagship instance of F2**: at `(D,p) = (5,2)` with Beukers' class `q = 6`, a bound at the
dates `≡ 1 (mod 6)` is unusable at every sojourn whose visits to the target have even phase — no
date is both odd and even.  Half the sojourn phases are lost, which is `1/gcd(2,6) = 1/2` of
them. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem not_biclass_two_six (m : ℕ) : ¬ (m % 6 = 1 % 6 ∧ m % 2 = 0 % 2) := by
  rintro ⟨h1, h2⟩
  omega

/-- **The single-target window cap** — WP6(i), the variant T1′ does not use.  A single-target class
bound at `ρ`, at a sojourn whose phase `s` satisfies the solvability condition
`r ≡ s (mod gcd(q,p))`, caps the sojourn at

  `L ≤ κ(θ)·n + max((1+κ(θ))·lcm(q,p) + C₀, lcm(q,p))`,

i.e. `sojourn_cap_class` with the window `q` replaced by `lcm(q,p)`.  The shadowing hypothesis is
phase-restricted, as `shadow_at_phase` says it must be: inside the block the orbit shadows the
rotating member, and it is near `ρ` exactly at the dates `n' ≡ s (mod p)`.

Weaker than the multiplier form in three ways, all of them F2's: the window is `lcm(q,p)` and not
`q`; there is a phase hypothesis; and for `r ≢ s (mod gcd(q,p))` the hypothesis is unusable at that
sojourn altogether (`not_biclass_of_not_modEq`), which at the flagship `(p,q) = (2,6)` is half the
phases.  `TShift.IsRepelledMulClass.isRepelledClass` avoids all three by bounding every target at
once, which is why T1′ is stated for the multiplier. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_single {θ ρ : ℝ} {q r p s : ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hq : 0 < q)
    (hp : 0 < p) (hgcd : r ≡ s [MOD Nat.gcd q p]) (h : IsRepelledClass θ ρ q r) :
    ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L → n' % p = s % p →
        distToNearestInt (((3 : ℝ) / 2) ^ n' - ρ) ≤ (2 / 3 : ℝ) ^ L') →
      (L : ℝ) ≤ kappa θ * n
        + max ((1 + kappa θ) * Nat.lcm q p + (-Real.log c) / Real.log (3 / 2))
            (Nat.lcm q p) := by
  have hlcm : 0 < Nat.lcm q p := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  refine ⟨c, hc, n₀, fun n hn L hshadow => ?_⟩
  rcases lt_or_ge L (Nat.lcm q p) with hshort | hlong
  · have hcap := sojourn_cap_window_short (n := n) hθ hθ1 hshort
    have hle := le_max_right ((1 + kappa θ) * Nat.lcm q p + (-Real.log c) / Real.log (3 / 2))
      ((Nat.lcm q p : ℝ))
    linarith
  · obtain ⟨n', hn'l, hn'r, hn'q, hn'p⟩ := exists_mem_biclass_Ico hq hp hgcd n
    have hcap := sojourn_cap_window hc hθ hθ1 hn'l hn'r
      (by omega : L ≤ (n + L - n') + Nat.lcm q p)
      (hn₀ n' (le_trans hn hn'l) hn'q) (hshadow n' (n + L - n') hn'l (by omega) hn'p)
    have hle := le_max_left ((1 + kappa θ) * Nat.lcm q p + (-Real.log c) / Real.log (3 / 2))
      ((Nat.lcm q p : ℝ))
    linarith

end TShift
