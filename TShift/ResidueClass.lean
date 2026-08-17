/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.Basic
import TShift.FreeSojourn
import TShift.MultiplierTransfer
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# T1′ — the residue-class relaxation of the T-shift problem

The T-shift problem (`TShift.TShiftProblem`, and its multiplier form `TShift.IsRepelledMul`) asks
for a repulsion bound `‖D·(3/2)ⁿ‖ ≥ c·θⁿ` with `θ > 2/3` at **every** date `n ≥ n₀`.  No shifted
Padé device in the literature proves its bound at every date *directly*: Beukers' §5 estimate holds
for `δ ≡ -k (mod 6)` [Beu81], Habsieger's (3.2) lives on the date lattice `6ℤ` [Hab03].  Each paper
then recovers an unrestricted theorem by a **descent** `k = qm − δ`, which costs the bound at the
multipliers `2^δ·D` and nothing in the rate — that is §11, and it is the scope statement the
relaxation has to be read with.  The date restriction was one of the two structural mismatches
disqualifying those devices as T-shift candidates.  This file states the weakening that matches their shape,

  **T1′**  `‖D_p·(3/2)ⁿ‖ ≥ c·θⁿ`  for some `θ > 2/3` and all large `n ≡ r (mod q)`,

as `TShift.T1Prime`, with the class-restricted predicates `TShift.IsRepelledMulClass` and
`TShift.IsRepelledClass`, the window lemma that makes a class usable inside a sojourn
(`TShift.exists_mem_class_Ico`), the transport to every cycle target
(`TShift.IsRepelledMulClass.isRepelledClass`), and the elementary weakening/monotonicity plumbing
that certifies T1′ as a genuine relaxation: `q = 1` recovers the unrestricted problem
(`TShift.isRepelledMulClass_one_iff`), and a class bound restricts to every subclass
(`TShift.IsRepelledMulClass.subclass`).

**And it proves the reduction the relaxation is for.**  The sojourn cap of report §1.5 does not need
the repulsion bound at every date: it needs it at *some* date within a bounded window of each
sojourn, and a class mod `q` meets every window of `q` consecutive dates.  So the cap survives the
restriction at the price of an additive constant — `TShift.sojourn_cap_window` and
`TShift.sojourn_cap_class`,

  `L ≤ κ(θ)·n + max((1+κ(θ))·q + C₀, q)`,   `C₀ = -log c/log(3/2)`,

against the unrestricted `L ≤ κ(θ)·n + C₀` of `TShift.sojourn_cap_kappa` — and the escape recursion
then delivers a visit in every dyadic block past the burn-in exactly as before
(`TShift.dyadic_block_visit_window`, feeding `TShift.dyadic_block_visit`).  The window cost is
`(1+κ(θ))·q`: `q` for the block shortened by the shift, `κ(θ)·q` for the shifted date itself.  It is
*not* `q·log₂(3/2)`, which is the same block shortening counted in bits of `(2/3)^L` — one unit of
`L` is `log₂(3/2)` bits, so that term is `q` units of `L` and the date-shift term is missing.  There
are two branches, not one: the window lemma places the admissible date in `[n, n+q)`, which is inside
the block only when `q ≤ L`, and a sojourn shorter than the window needs no cap at all
(`TShift.sojourn_cap_window_short`).

## Why the multiplier form is the official statement

T1′ is stated for the multiplier `D`, never for a single target `A/D`, and that is forced.  Inside a
`p`-periodic sojourn the orbit rotates through the cycle `ρ₀, …, ρ_{p-1}`: at date `n` it shadows
the rotated member, so a bound at one fixed `ρ` is usable only at dates meeting a *second*
congruence `n ≡ s (mod p)`.  The pair `n ≡ r (mod q)`, `n ≡ s (mod p)` is solvable exactly when
`gcd(p,q) ∣ r - s`, so for a fixed class only `1/gcd(p,q)` of the sojourn phases admit a usable date
at all — and at the flagship instance `(D,p) = (5,2)` with Beukers' `q = 6` that is half of them.
The multiplier form has no phase condition: `TShift.distToNearestInt_mul_le` bounds the distance to
*every* `A/D` at once, and all members of a `p`-cycle share the denominator `D_p = 3^p - 2^p`
(`Z32.cycle_point_eq`, `TShift.numerator_periodic`).  The free-numerator devices deliver the
multiplier form anyway, so nothing is lost.  `TShift.IsRepelledMulClass.isRepelledClass` is that
step, made explicit.

## What T1′ buys, and what it does not

What it buys is a **per-`n` floor at the dates of one class**: a lower bound on `‖D·(3/2)ⁿ‖` at a
specified date, which no free argument supplies at any date.

What it does **not** buy is the dynamical payoff of the sojourn cap.  A `p`-periodic block of the
carry word of length `L` at date `n` forces `2^L ∣ mₙ`, hence `L ≤ log₂(3/2)·n + p·log₂3`
unconditionally (`TShift.free_sojourn_cap_logb`), so `κ_free = log₂(3/2) = 0.58496 < 1` and every
dyadic block of dates already carries a visit (`TShift.dyadic_block_visit`) with no Diophantine
input at all.  A repulsion rate improves on that cap only above
`θ* = exp(-log²(3/2)/log 2) = 0.78885` (`TShift.thetaFree`), which is above the Waring threshold
`3/4` and far above every rate in print.  `TShift.kappa_lt_free_iff` machine-checks that crossover,
so the regime in which the cap below says anything new is on the record rather than asserted: the
operative bar for the *cap* is `θ*`, not `2/3`.  So the sojourn conclusion is *preserved* by the
relaxation, not *bought* by it.

And a class-restricted floor does not discharge consumers that quantify over every date: the Waring
criterion `‖(3/2)^k‖ ≥ (3/4)^k` **for all** `k` is the standard example.  T1′ is a legitimate
target for device-builders because devices are proved on classes; it is not a substitute for T1 in
any application that consumes all `k`.

## Status

`T1Prime p` is **effectively open** for every `p ≥ 2`, exactly like the T-shift problem; it is
formally weaker, and that weakening is its entire content.  As with `TShift.TShiftProblem`, the
bare existential is a theorem — `TShift.t1Prime_holds` in `TShift/MahlerCountMul.lean`, by the
class `0 mod 1` — so what is open here too is the version with the numerals exhibited
(`TShift.TShiftProblemAt` is the pattern).  No rate above `2/3` is known on any residue
class: the best class-restricted rate in print is `2^{-0.8972} = 0.53693` [Beu81, §5], the best
unrestricted one `0.5803` [Zud07], and the corpus's own transported `0.57434`
(`TShift.isRepelledMul_habsieger`) carries no class restriction and is still short of `2/3`.  The
only inhabitant proved here is the free rate `θ = 1/2` (`TShift.isRepelledMulClass_half`), where
`κ(1/2) = 1.70951 > 1` (`TShift.one_lt_kappa_half`): a non-vacuity witness that claims nothing.

## Scope

Complete as designed: the predicate layer (plan-Tshift-S5 WP1), the reduction (WP2), and the
re-admission socket (WP3, `TShift.isRepelledMulClass_of_twoForms` and
`TShift.t1Prime_of_twoForms` — a class-restricted two-form family produces a class-restricted
repulsion bound, so the date restriction of report §1.6.2 is no longer disqualifying).

§11 was added afterwards, at plan-Tshift-S7's angle O‑4 (finding F7): it prices the re-admission.
A class bound at the `q` multipliers `2^δ·D` gives the *unrestricted* bound at the same rate
(`isRepelledMul_of_isRepelledMulClass_pow_two`), hence settles `TShiftProblem` itself
(`tShiftProblem_of_isRepelledMulClass_pow_two`) — so T1′ is a relaxation exactly for a device whose
multiplier is rigid, and none is in print in this circle.  Nothing above §11 changes: `T1Prime` is
one instance and the descent consumes `q`, so the two problems remain formally distinct.

Three things are deliberately *not* here.  The escape recursion is not restated (finding F6):
`TShift.dyadic_block_visit` is already generic, so it is imported and specialized.  The
syndetic-`G` abstraction of the window argument is deferred until something consumes it — a class
mod `q`, a class minus finitely many dates, and a class intersected with the complement of a finite
bad set are all "meets every window of `q` consecutive dates", but nothing needs the common
generalization yet.  And the single-target class variant (which needs `gcd(p,q) = 1` and window
`lcm(p,q)`, and with it the cycle-shift identity `|x_{n+1} − ρ_{i+1}| = (3/2)|x_n − ρ_i|`, not
formalized anywhere) is out of scope: the multiplier form makes it unnecessary.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide` (`TShift.exists_mem_class_Ico` needs only `propext` and `Quot.sound`).  The
relaxation is Diophantine-free — nothing from `CITED/` or `BB13/` is imported, and the socket is
parametric: its two-form family and its size bookkeeping are hypotheses, not axioms.  This keeps the
three T-shift lanes `#print axioms`-distinguishable: S1's is `std3 + Habsieger.padeData`
(`TShift/HabsiegerTransfer.lean`), S2's is to be `std3 + BugeaudEvertse.ridout_line_cover` (not built
yet), and this one is `std3`.

## Claim level

Formalization only, and of a *reduction*: no repulsion bound is proved here at any rate, on any
class, so `T1Prime p` is as open — effectively — as `TShift.TShiftProblemAt`.  The window lemma is
`omega`-level
arithmetic; the weakenings are one-liners; the transport is `TShift.distToNearestInt_mul_le` with the
class guard carried through; the cap is `TShift.sojourn_cap_kappa` applied at a shifted date, and the
constant it pays is the only quantitative content of the file.  The `κ`-discipline of report §9 is in
force: every payoff statement names `κ(θ)` explicitly, and every one of them also names
`κ_free = log₂(3/2)`, since post-C20 no sojourn slope is legible without it.

## References

* `plans/plan-Tshift-S5.html` — the plan (§1.4 D1–D3, §2 target statements, §3.1 file map);
  `plans/note-Tshift-S5-GA.html` — gate G‑A, findings F1–F6, conventions K1–K6.  The numerals quoted
  in this file (`0.53693`, `0.5803`, `θ*`, `(1+κ)q` at the tabulated rates, the 99.24% short-branch
  census) are the harness's: `python3 TShift/tshift_numerics.py s5 20000 6`.
* `report-Tshift.html` §1.4 (the circulated T1′ statement), §1.5 (the sojourn cap), §1.6.2 (the two
  structural mismatches), corrections C14, C20, C21.
* [Beu81] F. Beukers, *Fractional parts of powers of rationals*, Math. Proc. Cambridge Philos.
  Soc. **90** (1981), 13–20 — §5, the class-restricted shifted device, `δ ≡ -k (mod 6)`.
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–309 — (3.2), the dyadic shifted device on the lattice `6ℤ`.
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)^k‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323 — the unrestricted record `0.5803`.
-/

namespace TShift

/-! ## 1. The window lemma

The one arithmetic fact the relaxation needs: a residue class mod `q` is *syndetic with gap `q`* —
every window of `q` consecutive dates contains one of its members.  This is what turns "a bound at
the dates of one class" into "a bound at some date within `q` of the start of each sojourn", which
is all the sojourn cap consumes (the cap itself is WP2).

The class guard is written `n % q = r % q` throughout (convention K1), never `n % q = r`: it avoids
the side condition `r < q` everywhere, it is exactly what this lemma produces, and subclass
monotonicity is cleanest with it. -/

/-- **The window lemma.**  For `q > 0` every half-open window `[n, n+q)` of dates meets the residue
class of `r` mod `q`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem exists_mem_class_Ico {q : ℕ} (hq : 0 < q) (n r : ℕ) :
    ∃ m, n ≤ m ∧ m < n + q ∧ m % q = r % q := by
  have hs : n % q < q := Nat.mod_lt _ hq
  have hd : (r + q - n % q) % q < q := Nat.mod_lt _ hq
  refine ⟨n + (r + q - n % q) % q, Nat.le_add_right _ _, by omega, ?_⟩
  calc n + (r + q - n % q) % q
      ≡ n + (r + q - n % q) [MOD q] := (Nat.mod_modEq _ _).add_left _
    _ ≡ n % q + (r + q - n % q) [MOD q] := (Nat.mod_modEq n q).symm.add_right _
    _ = r + q := by omega
    _ ≡ r [MOD q] := Nat.add_mod_right r q

/-! ## 2. The class-restricted repulsion predicates

`IsRepelledMulClass` and `IsRepelledClass` are `IsRepelledMul` and `IsRepelled` with the dates
restricted to one class.  Both keep the effective shape of the originals (an explicit constant `c`
and a threshold `n₀`), so a device that proves either supplies the same data it always did. -/

/-- `IsRepelledMulClass θ D q r`: the multiplier repulsion bound `‖D·(3/2)ⁿ‖ ≥ c·θⁿ`, demanded only
at the dates of the class `r` mod `q`.  For `q = 1` this is `IsRepelledMul` verbatim
(`isRepelledMulClass_one_iff`). -/
def IsRepelledMulClass (θ : ℝ) (D q r : ℕ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, n % q = r % q →
    c * θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n)

/-- `IsRepelledClass θ ρ q r`: the single-target form of the same restriction — repulsion from `ρ`
at the dates of the class `r` mod `q`.

This is *not* the official statement of T1′ (`T1Prime` uses the multiplier form): a single-target
hypothesis is unusable at the sojourn phases whose visits to `ρ` miss the class, which is half of
them at `(D,p) = (5,2)`, `q = 6`.  It appears here as the *conclusion* of
`IsRepelledMulClass.isRepelledClass`, where it holds at every target simultaneously and the phase
obstruction cannot arise. -/
def IsRepelledClass (θ ρ : ℝ) (q r : ℕ) : Prop :=
  ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, n % q = r % q →
    c * θ ^ n ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - ρ)

/-! ## 3. T1′ -/

/-- **T1′ — the official weakened problem** (multiplier form).  For `p ≥ 2` and
`D = D_p = 3^p - 2^p`: is there a rate `θ > 2/3`, a modulus `q > 0`, a residue `r`, an effective
`c > 0` and a threshold `n₀` with

  `‖D·(3/2)ⁿ‖ ≥ c·θⁿ`  for all `n ≥ n₀` with `n ≡ r (mod q)`?

**Effectively open** for every `p ≥ 2`: no rate above `2/3` is known on any class (see the module
docstring's status paragraph).  As an existential it is a theorem, like the T-shift problem itself
(`TShift.t1Prime_holds`).  It is a genuine weakening of the T-shift problem —
`t1Prime_of_isRepelledMul` takes `q = 1` — and it is the form in which the shifted Padé devices are
proved, which is its entire point.

Two non-claims travel with this definition.  (i) The dynamical payoff of the sojourn cap is *not*
what T1′ buys: that payoff is unconditional (`free_sojourn_cap_logb`, `dyadic_block_visit`, slope
`κ_free = log₂(3/2) = 0.58496`), and a repulsion rate improves on it only above
`θ* = 0.78885 = thetaFree`.  What T1′ buys is a per-`n` floor at the dates of the class.  (ii) That
floor does not discharge consumers quantifying over every date — the Waring criterion
`‖(3/2)^k‖ ≥ (3/4)^k` for all `k` is the standard example.  T1′ is not a substitute for T1. -/
def T1Prime (p : ℕ) : Prop :=
  ∃ θ > (2 : ℝ) / 3, ∃ q > 0, ∃ r : ℕ, IsRepelledMulClass θ (Z32.cycleDenom p) q r

/-! ## 4. Proposition A: T1′ is a genuine weakening

Three one-liners certifying that nothing was smuggled in: the unrestricted bound implies the class
bound, `q = 1` recovers the unrestricted bound exactly, and a class bound restricts to every
subclass.  Together they say a solution of T1′ cannot be harder to find than a solution of the
T-shift problem. -/

/-- Dropping the date restriction: an unrestricted multiplier bound is a class bound, on every
class. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem IsRepelledMul.isRepelledMulClass {θ : ℝ} {D : ℕ} (h : IsRepelledMul θ D) (q r : ℕ) :
    IsRepelledMulClass θ D q r := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  exact ⟨c, hc, n₀, fun n hn _ => hn₀ n hn⟩

/-- **`q = 1` recovers T1.**  The class relaxation at modulus `1` is the unrestricted problem
verbatim, so `IsRepelledMulClass` really does interpolate between `IsRepelledMul` and nothing. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClass_one_iff {θ : ℝ} {D r : ℕ} :
    IsRepelledMulClass θ D 1 r ↔ IsRepelledMul θ D := by
  simp [IsRepelledMulClass, IsRepelledMul, Nat.mod_one]

/-- **Subclass monotonicity.**  A bound on the class `r` mod `q` restricts to any class mod `k·q`
contained in it.  (No hypothesis on `k`: at `k = 0` the guard degenerates to `n = r'`, and the
statement still holds.) -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem IsRepelledMulClass.subclass {θ : ℝ} {D q r : ℕ} (h : IsRepelledMulClass θ D q r)
    (k : ℕ) {r' : ℕ} (hr' : r' % q = r % q) : IsRepelledMulClass θ D (k * q) r' := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  refine ⟨c, hc, n₀, fun n hn hcls => hn₀ n hn ?_⟩
  have hdvd : q ∣ k * q := dvd_mul_left q k
  calc n % q = n % (k * q) % q := (Nat.mod_mod_of_dvd n hdvd).symm
    _ = r' % (k * q) % q := by rw [hcls]
    _ = r' % q := Nat.mod_mod_of_dvd r' hdvd
    _ = r % q := hr'

/-- **T1′ is weaker than the T-shift problem's multiplier premise.**  A rate `θ > 2/3` for
`‖D_p·(3/2)ⁿ‖` at every date settles T1′ at `q = 1`.  So T1′ is at most as hard as the problem it
relaxes; the interest is that its converse is not available. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem t1Prime_of_isRepelledMul {p : ℕ}
    (h : ∃ θ > (2 : ℝ) / 3, IsRepelledMul θ (Z32.cycleDenom p)) : T1Prime p := by
  obtain ⟨θ, hθ, hrep⟩ := h
  exact ⟨θ, hθ, 1, one_pos, 0, hrep.isRepelledMulClass 1 0⟩

/-! ## 5. Transport: one class bound at the multiplier, every target at once

The formal content of the multiplier-form convention (K3).  `distToNearestInt_mul_le` is pointwise
in the date, so it commutes with any date restriction: a class bound at `D` gives the class bound at
*every* rational `A/D`, the rotated cycle member included, with no congruence on the sojourn
phase. -/

/-- **The reduction, class version.**  A multiplier bound on the class `r` mod `q` gives the shifted
bound at every target `A/D`, uniformly in `A`, on the same class.  This is what removes the phase
obstruction of the single-target reading: the orbit may shadow whichever cycle member it likes. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem IsRepelledMulClass.isRepelledClass {θ : ℝ} {D q r : ℕ} (hD : 0 < D)
    (h : IsRepelledMulClass θ D q r) (A : ℤ) : IsRepelledClass θ ((A : ℝ) / D) q r := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨c / D, by positivity, n₀, fun n hn hcls => ?_⟩
  have h1 := hn₀ n hn hcls
  have h2 := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  rw [div_mul_eq_mul_div, div_le_iff₀ hDR]
  calc c * θ ^ n ≤ distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n) := h1
    _ ≤ (D : ℝ) * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / D) := h2
    _ = distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / D) * D := by ring

/-- **What a solution of T1′ would deliver**: the class-restricted floor at every cycle target of
period `p` simultaneously — the exact analogue of `tShiftProblem_of_isRepelledMul`, and still only
on the class. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledClass_of_t1Prime {p : ℕ} (hp : 1 ≤ p) (h : T1Prime p) (A : ℤ) :
    ∃ θ > (2 : ℝ) / 3, ∃ q > 0, ∃ r : ℕ,
      IsRepelledClass θ ((A : ℝ) / Z32.cycleDenom p) q r := by
  obtain ⟨θ, hθ, q, hq, r, hrep⟩ := h
  exact ⟨θ, hθ, q, hq, r, hrep.isRepelledClass (Z32.cycleDenom_pos hp) A⟩

/-! ## 6. The sanity instance

The free rate inhabits the class predicate, on every class.  It claims nothing about T1′:
`κ(1/2) = log 2/log(3/2) = 1.70951 > 1` (`one_lt_kappa_half`), so it is below the `2/3` threshold —
far below the `θ* = 0.78885` at which a rate would improve on the free sojourn cap — and
`half_not_gt_two_thirds` records that it cannot be the `θ` of `T1Prime`.  Its purpose is
non-vacuity of the definitions: something satisfies them, and the whole pipeline of §§4–5 runs on
it.  (A non-trivial inhabitant at `θ = 0.57434`, still below `2/3`, is a one-line corollary of
`isRepelledMul_habsieger` via `IsRepelledMul.isRepelledMulClass` — at the cost of that file's cited
axiom, and with no class restriction needed, which is why the class-restricted Habsieger instance
was retired.) -/

/-- The free rate `θ = 1/2` satisfies the class-restricted multiplier bound for every odd `D`, on
every class.  Non-vacuity only: `κ(1/2) > 1`, so no payoff and no instance of T1′. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClass_half {D : ℕ} (hD : Odd D) (q r : ℕ) :
    IsRepelledMulClass (1 / 2) D q r :=
  (isRepelledMul_half hD).isRepelledMulClass q r

/-- The free rate transported to every target, on every class: the composite
`isRepelledMulClass_half` → `IsRepelledMulClass.isRepelledClass` exercised end to end. -/
@[category test, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledClass_half {p : ℕ} (hp : 1 ≤ p) (A : ℤ) (q r : ℕ) :
    IsRepelledClass (1 / 2) ((A : ℝ) / Z32.cycleDenom p) q r :=
  (isRepelledMulClass_half (Z32.cycleDenom_odd hp) q r).isRepelledClass
    (Z32.cycleDenom_pos hp) A

/-! ## 7. κ bookkeeping: where the relaxation is worth anything

Two facts about the sojourn slope `κ(θ) = log(1/θ)/log(3/2)` of `TShift.kappa`.  `kappa_nonneg` is
what the window shift consumes: moving the date from `n` to `n' ≤ n + q` costs `κ(θ)·q`, and that is
a cost rather than a gift only because `κ(θ) ≥ 0`.

`kappa_lt_free_iff` is the honest measure of what the cap of §8 is worth (convention K6).  Post-C20
no statement about sojourn slopes is legible without the free slope `κ_free = log₂(3/2)` beside it:
the free cap `TShift.free_sojourn_cap_logb` is unconditional, so a repulsion-derived cap improves on
what is *already owned* only above `θ* = TShift.thetaFree = 0.78885`, and below `θ*` the conclusion
of §§8–9 holds without their hypothesis.  The operative bar for the cap is therefore `θ*`, not the
`2/3` of `TShift.kappa_lt_one_iff` — which remains the bar for `κ(θ) < 1`, i.e. for the cap being
sublinear at all. -/

/-- `κ(θ) ≥ 0` for `0 < θ ≤ 1`: no repulsion rate at or below `1` yields a negative sojourn slope.
This is the step that prices the window shift at `κ(θ)·q` in `sojourn_cap_window`. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem kappa_nonneg {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) : 0 ≤ kappa θ := by
  rw [kappa]
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hθ.le hθ1)) log_three_halves_pos.le

/-- `κ` is strictly antitone on the positive rates: a better repulsion rate is a smaller sojourn
slope, and nothing else changes. -/
@[category API, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem kappa_lt_kappa_iff {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    kappa θ₁ < kappa θ₂ ↔ θ₂ < θ₁ := by
  have hpos := log_three_halves_pos
  have hinv : 0 < (Real.log (3 / 2 : ℝ))⁻¹ := by positivity
  have hiff : kappa θ₁ < kappa θ₂ ↔ Real.log θ₂ < Real.log θ₁ := by
    simp only [kappa, div_eq_mul_inv]
    constructor <;> intro h <;> nlinarith
  rw [hiff]
  exact Real.log_lt_log_iff h₂ h₁

/-- **The crossover (K6).**  `κ(θ) < κ_free = log₂(3/2) ⟺ θ > θ* = exp(-log²(3/2)/log 2)`, the rate
`TShift.thetaFree = 0.7888478…` at which repulsion would match the free carry-word ceiling.

This is what the reduction of §8 is worth *as a cap*, machine-checked rather than asserted: for
`θ ≤ θ*` the window cap `sojourn_cap_class` proves nothing that `TShift.free_sojourn_cap_logb` does
not already give unconditionally, and `θ*` is above the Waring threshold `3/4`, far above the
unrestricted record `0.5803` [Zud07] and far above the best class-restricted rate in print,
`0.53693` [Beu81, §5].  What T1′ buys at any rate above `2/3` is the per-`n` floor on the class, not
this. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem kappa_lt_free_iff {θ : ℝ} (hθ : 0 < θ) :
    kappa θ < Real.logb 2 (3 / 2) ↔ thetaFree < θ := by
  rw [← kappa_thetaFree]
  exact kappa_lt_kappa_iff hθ thetaFree_pos

/-! ## 8. Theorem B — the window sojourn cap

The reduction.  `TShift.sojourn_cap_kappa` applies the repulsion bound at the date `n` where the
sojourn starts; the class version cannot, since `n` need not lie in the class.  It applies it instead
at the admissible date `n'` handed over by `exists_mem_class_Ico`, and pays twice for the shift:
`κ(θ)·q` because the repulsion at `n'` is weaker than at `n` (`θ^{n'} ≥ θ^{n+q}`), and `q` because
the periodic block remaining at `n'` is shorter (`L ≤ L' + q`).  Total `(1+κ(θ))·q` — `2q` as
`θ ↓ 2/3`, `1.26·q` at `θ = 0.9`, and `+7.56` at `θ = 0.9` with the Beukers class `q = 6`.

Both statements stay at the abstraction of `sojourn_cap`: the shadowing bound is a hypothesis, taken
per date, and nothing here proves that any block of the carry word is periodic.  That combinatorial
premise — S13(iii) of the report — is the binding constraint of the program and is untouched by the
relaxation, which weakens only the Diophantine half. -/

/-- **The window sojourn cap, long branch.**  Repulsion applied at an admissible date `n'` in the
window `[n, n+q)`, against the shadowing bound `(2/3)^{L'}` for the block remaining there, caps a
sojourn of length `L` at

  `L ≤ κ(θ)·n + ((1+κ(θ))·q + C₀)`,   `C₀ = -log c/log(3/2)`,

which is `sojourn_cap_kappa`'s cap with `C₀ ↦ C₀ + (1+κ(θ))·q`.  Hypotheses are exactly
`sojourn_cap_kappa`'s plus the window (`n ≤ n' < n+q`) and the shortened block (`L ≤ L' + q`); of the
two window bounds only `n' < n+q` is consumed by the arithmetic — hence the `_hn'` — the lower one
being what places `n'` inside the block so that the shadowing hypothesis is available at all, and it
is recorded because the consumer must supply it (see `sojourn_cap_window_short` for what happens when
it cannot).

The added `θ ≤ 1` over `sojourn_cap_kappa` is what makes `κ(θ) ≥ 0`, i.e. what makes the date shift a
cost. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_window {c θ d' : ℝ} {n n' L L' q : ℕ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (_hn' : n ≤ n') (hwin : n' < n + q) (hL : L ≤ L' + q)
    (hrep : c * θ ^ n' ≤ d') (hshadow : d' ≤ (2 / 3 : ℝ) ^ L') :
    (L : ℝ) ≤ kappa θ * n + ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) := by
  have hκ := kappa_nonneg hθ hθ1
  have hcap := sojourn_cap_kappa hc hθ hrep hshadow
  have hLR : (L : ℝ) ≤ (L' : ℝ) + q := by exact_mod_cast hL
  have hn'R : (n' : ℝ) ≤ (n : ℝ) + q := by exact_mod_cast (by omega : n' ≤ n + q)
  have hmul : kappa θ * n' ≤ kappa θ * ((n : ℝ) + q) := mul_le_mul_of_nonneg_left hn'R hκ
  linarith

/-- **The window sojourn cap, short branch** (finding F5).  A sojourn shorter than the window needs
no repulsion input at all: `L < q ≤ κ(θ)·n + q` for every date `n`, since `κ(θ) ≥ 0`.

This is not pedantry.  The window lemma places the admissible date in `[n, n+q)`, which lies inside
the block only when `q ≤ L`, so without this branch the reduction has a hole exactly where the real
carry word lives: at `n ≤ 20000`, 99.24% of maximal 2-periodic blocks are shorter than the canonical
Beukers window `q = 6` (and for `p ≥ q` the short branch is empty by definition, since a
`p`-periodic block has `L ≥ p`). -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_window_short {θ : ℝ} {n L q : ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hLq : L < q) :
    (L : ℝ) ≤ kappa θ * n + q := by
  have hκn : (0 : ℝ) ≤ kappa θ * n := mul_nonneg (kappa_nonneg hθ hθ1) (Nat.cast_nonneg n)
  have hLR : (L : ℝ) < q := by exact_mod_cast hLq
  linarith

/-- **Theorem B — the reduction, packaged.**  Class-restricted repulsion at rate `θ ∈ (0,1]` caps
*every* sojourn, at every date past the device's own threshold:

  `L ≤ κ(θ)·n + max((1+κ(θ))·q + C₀, q)`,   `C₀ = -log c/log(3/2)`,

with the two branches of `sojourn_cap_window` / `sojourn_cap_window_short` combined into the single
constant `max((1+κ(θ))·q + C₀, q)`.  The class hypothesis enters exactly once, through
`exists_mem_class_Ico`: whichever date the window offers, the bound is available there.

Parametric in the forced-periodicity premise, exactly as `sojourn_cap` is: `hshadow` is the
hypothesis that at every date `n'` of the block the multiplier distance is at most `(2/3)^{L'}` for
the block length `L'` remaining there, which is what a forced-periodic block delivers (the multiplier
factor absorbed into the constant).  Nothing here proves it — that is S13(iii), and it is where the
program is actually blocked.

Two non-claims, per convention K5.  The *rate* is not proved: `IsRepelledMulClass θ D q r` is a
hypothesis here and is open for every `θ > 2/3` on every class.  And the *conclusion* is only
interesting above `θ* = 0.78885`: for `θ ≤ θ*` the free cap `free_sojourn_cap_logb` already gives a
slope at least as good unconditionally, by `kappa_lt_free_iff`.  Useful content of the theorem: it
records that the class-restricted hypothesis suffices — the weakening costs an additive constant and
nothing else. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem sojourn_cap_class {θ : ℝ} {D q r : ℕ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hq : 0 < q)
    (h : IsRepelledMulClass θ D q r) :
    ∃ c > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (∀ n' L' : ℕ, n ≤ n' → n' + L' = n + L →
        distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ n') ≤ (2 / 3 : ℝ) ^ L') →
      (L : ℝ) ≤ kappa θ * n
        + max ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) q := by
  obtain ⟨c, hc, n₀, hn₀⟩ := h
  refine ⟨c, hc, n₀, fun n hn L hshadow => ?_⟩
  rcases lt_or_ge L q with hshort | hlong
  · have hcap := sojourn_cap_window_short (n := n) hθ hθ1 hshort
    have hle := le_max_right ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) ((q : ℝ))
    linarith
  · obtain ⟨n', hn'l, hn'r, hn'c⟩ := exists_mem_class_Ico hq n r
    have hcap := sojourn_cap_window hc hθ hθ1 hn'l hn'r (by omega : L ≤ (n + L - n') + q)
      (hn₀ n' (le_trans hn hn'l) hn'c) (hshadow n' (n + L - n') hn'l (by omega))
    have hle := le_max_left ((1 + kappa θ) * q + (-Real.log c) / Real.log (3 / 2)) ((q : ℝ))
    linarith

/-! ## 9. The payoff, and why it is not the point

The escape recursion is not restated here (finding F6).  `TShift.dyadic_block_visit` in
`TShift/FreeSojourn.lean` already consumes nothing but `∀ k ≥ k₀, e (k+1) < 2·e k`, so the window cap
is fed into it through the generic `TShift.lt_two_mul_of_lt_two`, and `TShift.escape_ratio`,
`TShift.escape_lt_two_mul` are reused as they stand.

Read the result with C20 in hand: the conclusion below is **unconditional** at
`κ_free = log₂(3/2) = 0.58496 < 1` (`free_sojourn_cap_logb` plus the same recursion), so this
corollary is a statement about which hypotheses suffice, not about what is true.  It earns its place
because the class-restricted hypothesis is the one the literature's devices could conceivably supply,
and because `kappa_lt_free_iff` pins exactly where it would start to say more: `θ > θ* = 0.78885`. -/

/-- **The payoff, class version.**  A cap `L_k ≤ κ(θ)·n_k + C'` on the sojourn following the escape
date `n_k` puts the next escape at `n_{k+1} ≤ (1+κ(θ))·n_k + C'+1`; with `κ(θ) < 1`, i.e. `θ > 2/3`
(`kappa_lt_one_iff`), consecutive escape dates then satisfy `n_{k+1} < 2·n_k` from the burn-in date
`C/(1-κ(θ))` on, and `TShift.dyadic_block_visit` turns that into a visit in every dyadic block
`[2^m, 2^{m+1})` above the starting scale.  In dyadic terms the burn-in is
`m₀ = ⌈log₂(C/(1-κ(θ)))⌉`, which blows up as `θ ↓ 2/3` — the `κ` must be printed with any use of
this.

The hypotheses are the escape recursion (`he`), the threshold (`hburn`, propagated to all later `k`
by monotonicity) and the scale (`hm`); `C` here is the `C'+1` of the recursion, not the cap's
constant.

Unconditional below `θ*`: with `κ_free = log₂(3/2)` in place of `κ(θ)` the same conclusion holds with
no repulsion hypothesis whatsoever (`TShift.escape_lt_two_mul`, `TShift.dyadic_block_visit`), and by
`kappa_lt_free_iff` that is a *better* slope for every `θ ≤ θ* = 0.78885`.  This corollary claims
only that a class-restricted rate suffices to reach the same conclusion. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem dyadic_block_visit_window {θ C : ℝ} {e : ℕ → ℝ} {k₀ m : ℕ} (hκ : kappa θ < 1)
    (hmono : StrictMono e) (hunb : ∀ M : ℝ, ∃ k, M ≤ e k)
    (he : ∀ k, e (k + 1) ≤ (1 + kappa θ) * e k + C)
    (hburn : C / (1 - kappa θ) < e k₀) (hm : e k₀ ≤ 2 ^ m) :
    ∃ k, (2 : ℝ) ^ m ≤ e k ∧ e k < 2 ^ (m + 1) := by
  refine dyadic_block_visit hmono (fun k hk => ?_) hunb hm
  refine lt_two_mul_of_lt_two (by linarith) (he k) ?_
  rw [show (2 : ℝ) - (1 + kappa θ) = 1 - kappa θ by ring]
  exact lt_of_lt_of_le hburn (hmono.monotone hk)

/-! ## 10. Proposition C — the re-admission socket

The point of the whole relaxation, in one theorem.  Report §1.6.2 lists two structural mismatches
that disqualify the Beukers-§5-style devices as T-shift candidates: their **denominators** (targets
`M̄/3^δ`, not `A/D_p`) and their **dates** (bounds proved only for `δ ≡ -k (mod 6)`).  The first is
discharged by the multiplier transfer of `TShift/MultiplierTransfer.lean` — one bound at the
multiplier controls every target sharing its denominator.  The second is discharged here: a two-form
family that exists only at the dates of a residue class still produces a repulsion bound, on that
class, and `T1Prime` is satisfied by exactly that.  So a future device with a free numerator, `2^δ`
or `3^δ` denominators and any date congruence feeds `t1Prime_of_twoForms` directly.

The socket is **parametric, not axiomatic**: `F` and `hrate` are hypotheses.  Nothing here imports a
Padé construction — this file depends on no cited axiom and on nothing from `CITED/` or `BB13/`, and
if a draft ever needed such an import the design would be wrong.  `hrate` is the outcome of the size
bookkeeping (the `Λ`, `B`, `P` accounting of S1's endgame, `TShift.le_distToNearestInt_uniform` being
its one worked instance), left as a hypothesis so that the socket knows nothing about which engine
produced the forms — the same posture as `TShift/MultiplierTransfer.lean` §4.

No instance above `2/3` is supplied, on this class or any other, because none exists in print: the
best class-restricted rate is `0.53693` [Beu81, §5] and the best unrestricted one `0.5803` [Zud07].
The socket is what a device would plug into, not evidence that one will. -/

/-- **Proposition C — re-admission.**  A class-restricted two-form family at the dates `k ≡ r (mod q)`,
`k ≥ k₀`, whose size bookkeeping yields the rate `θ`, gives `IsRepelledMulClass θ D q r`.

The bookkeeping hypothesis `hrate` is stated against exactly the quantity
`TShift.TwoForms.le_distToNearestInt` returns at `X = 2^k`, `Y = 3^k`, `c = D`:

  `(P k · 2^k − D · Λ k) / (B k · 2^k) ≤ ‖D·(3/2)^k‖`,

so a device supplies its forms and its accounting, and this lemma does the rest.  A thin wrapper —
the content is that the date restriction survives the transfer untouched, the transfer being
pointwise in `k`. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMulClass_of_twoForms {θ c : ℝ} {D q r k₀ : ℕ} {P Λ B : ℕ → ℝ}
    (hD : 0 < D) (hc : 0 < c) (hB : ∀ k, 0 < B k)
    (F : ∀ k, k₀ ≤ k → k % q = r % q → TwoForms ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) (P k) (Λ k) (B k))
    (hrate : ∀ k, k₀ ≤ k → k % q = r % q →
      c * θ ^ k ≤ (P k * 2 ^ k - (D : ℝ) * Λ k) / (B k * 2 ^ k)) :
    IsRepelledMulClass θ D q r := by
  refine ⟨c, hc, k₀, fun k hk hcls => ?_⟩
  have hDne : ((D : ℤ)) ≠ 0 := by exact_mod_cast hD.ne'
  have h := (F k hk hcls).le_distToNearestInt (by positivity) hDne (hB k)
  have habs : |((D : ℤ) : ℝ)| = (D : ℝ) := by
    push_cast
    exact abs_of_nonneg (by positivity)
  have harg : ((D : ℤ) : ℝ) * (((3 : ℤ) ^ k : ℤ) : ℝ) / (((2 : ℤ) ^ k : ℤ) : ℝ)
      = (D : ℝ) * ((3 : ℝ) / 2) ^ k := by
    push_cast
    rw [div_pow]
    ring
  rw [habs, harg] at h
  push_cast at h
  exact le_trans (hrate k hk hcls) h

/-- **Proposition C, in problem form.**  The same family, at a rate above the threshold and at the
multiplier `D_p = 3^p − 2^p`, settles `T1Prime p` — the formal content of "the §1.6.2 devices
re-enter the pool of candidates".  For T1′, and not for `TShift.TShiftProblem`: what a class-restricted
device delivers is the per-`n` floor on its class, which does not discharge any consumer quantifying
over every date. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem t1Prime_of_twoForms {θ c : ℝ} {p q r k₀ : ℕ} {P Λ B : ℕ → ℝ}
    (hp : 1 ≤ p) (hθ : (2 : ℝ) / 3 < θ) (hq : 0 < q) (hc : 0 < c) (hB : ∀ k, 0 < B k)
    (F : ∀ k, k₀ ≤ k → k % q = r % q → TwoForms ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) (P k) (Λ k) (B k))
    (hrate : ∀ k, k₀ ≤ k → k % q = r % q →
      c * θ ^ k ≤ (P k * 2 ^ k - (Z32.cycleDenom p : ℝ) * Λ k) / (B k * 2 ^ k)) :
    T1Prime p :=
  ⟨θ, hθ, q, hq, r, isRepelledMulClass_of_twoForms (Z32.cycleDenom_pos hp) hc hB F hrate⟩

/-- **Orientation check for the socket wiring**, at the date `k = 4` and the flagship multiplier
`D = D₂ = 5`, with the forms of `TShift.transfer_prop_one_sanity`: `−5·2⁴ + 1·3⁴ = 1` and
`−81·2⁴ + 16·3⁴ = 0`, independent (determinant `1`), `P = 1`, `Λ = 1`, `B = 16`.  The per-date step
that `isRepelledMulClass_of_twoForms` performs returns `(P·2⁴ − D·Λ)/(B·2⁴) = 11/256` against the
true `‖5·(3/2)⁴‖ = ‖405/16‖ = 5/16 = 80/256` — positive, so neither vacuous nor reversed, and taken
at `D ≠ 1` so that the `c := D` instantiation and the `D·3^k/2^k = D·(3/2)^k` rewriting are both
exercised. -/
@[category test, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem twoForms_socket_sanity :
    (11 : ℝ) / 256 ≤ distToNearestInt (5 * ((3 : ℝ) / 2) ^ 4) := by
  have F : TwoForms ((2 : ℤ) ^ 4) ((3 : ℤ) ^ 4) 1 1 16 :=
    { a₁ := -5, b₁ := 1, Γ₁ := 1, a₂ := -81, b₂ := 16, Γ₂ := 1
      det := by norm_num
      dvd_a₁ := one_dvd _, dvd_b₁ := one_dvd _, dvd_a₂ := one_dvd _, dvd_b₂ := one_dvd _
      le_content₁ := by norm_num
      le_content₂ := by norm_num
      size₁ := by norm_num
      size₂ := by norm_num
      coeff₁ := by norm_num
      coeff₂ := by norm_num }
  -- `h : (P·2⁴ − |c|·Λ)/(B·2⁴) ≤ ‖c·3⁴/2⁴‖`, i.e. `11/256 ≤ ‖405/16‖`, straight from the socket
  have h := F.le_distToNearestInt (c := 5) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  rw [show (5 : ℝ) * ((3 : ℝ) / 2) ^ 4 = 405 / 16 by norm_num]
  exact h

/-! ## 11. The descent — when a date restriction is not one

Proposition C re-admits a class-restricted device.  This section prices the re-admission, and the
price is the honest scope statement for T1′: as a *statement* the relaxation is strictly weaker, but
for the devices it was built to re-admit it is not weaker in effect.

Write a date `k` as `k = n - δ` with `n ≡ r (mod q)` and `δ < q`; the window lemma of §1 supplies
`n`.  Then

  `2^δ · D · (3/2)^n = 3^δ · (D · (3/2)^k)`

*identically*, so a class bound at the multiplier `2^δ·D` is a bound at the unrestricted date `k` —
at the **same rate** `θ`, the whole cost being the one-off constant `(θ/3)^{q-1}`.  The hypothesis is
`q` instances of `IsRepelledMulClass`, one per `δ < q`, differing only in the multiplier, and that is
exactly the resource a two-form device has to spare: in `isRepelledMulClass_of_twoForms` the family
`F` never mentions `D`, which enters only through the term `− D·Λ k` of `hrate`, so passing to
`2^δ·D` costs a factor `≤ 2^{q-1}` of slack in the error column and nothing else.

This is the closing move of every device in this literature — [Beu81] §5 "*by putting `k = 6m − δ`*",
[Hab03] §5 "*Take `k = 6m − δ` with `δ ∈ {0,…,5}`*", [Ben93] (19) "*defining `k = cm − δ`*" — and it
is why all three state **unrestricted** theorems although their estimates live on a lattice.  This
corpus performs it at `q = 6`: `TShift.distToNearestInt_descent` (`TShift/HabsiegerTransfer.lean` §5)
is `distToNearestInt_descent'` below with `n = 6m`, and it is what makes
`TShift.isRepelledMul_habsieger` unrestricted although `Habsieger.padeData` lives at the columns
`(2^{6m}, 3^{6m})`.  Priced at that instance: a factor `2^5 = 32` of admissible multiplier range,
which `bHab^k = (1216/1215)^k` passes at `k = 4213` against that theorem's own burn-in
`kHab = 64 440 001`; and `(θ/3)^5 = 2.57·10⁻⁴`, i.e. `8.27` nats, in the constant.

So T1′ is a genuine relaxation for a device whose multiplier is **rigid**, and no such device is in
print in this circle.  `T1Prime p` itself is untouched by all of this: it is *one* instance, the
descent consumes `q` of them, and `t1Prime_of_isRepelledMul` (the `q = 1` direction) remains the only
implication between the two problems proved here.  Nor does anything below prove a bound: the
descent is a conversion, and its hypothesis is as open as its conclusion.

Provenance: plan-Tshift-S7's outgoing angle O‑4, finding F7 (`plans/note-Tshift-S7-O4.html`), with
the identity and the inequality verified exactly in `ℚ` by harness check `[G]`,
`python3 TShift/tshift_numerics.py s5 20000 6`.  The `κ`-discipline is unchanged and is the point:
the descent moves the constant only, so `κ(θ)` and its side of `2/3` are the same before and after,
and `κ < 1` remains free below `θ* = 0.78885` (`kappa_lt_free_iff`, `free_kappa_lt_one`). -/

/-- **The descent, at a general date.**  For `n = k + δ`,

  `‖2^δ·D·(3/2)^n‖ ≤ 3^δ·‖D·(3/2)^k‖`,

because `2^δ·D·(3/2)^n = 3^δ·(D·(3/2)^k)` identically and `‖N·x‖ ≤ N·‖x‖`
(`TShift.distToNearestInt_mul_le` at `A = 0`).

`TShift.distToNearestInt_descent` of `TShift/HabsiegerTransfer.lean` §5 is this statement with `n`
fixed to `6 * m`; it is restated here rather than imported because that file carries the cited axiom
`Habsieger.padeData`, and importing it would break this file's `std3`-only trust ledger.  The two
proofs are the same three rewrites. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem distToNearestInt_descent' {D δ k n : ℕ} (hn : n = k + δ) :
    distToNearestInt ((2 : ℝ) ^ δ * (D : ℝ) * ((3 : ℝ) / 2) ^ n)
      ≤ 3 ^ δ * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
  have h32 : (2 : ℝ) ^ δ * ((3 : ℝ) / 2) ^ δ = 3 ^ δ := by rw [← mul_pow]; norm_num
  have hrw : (2 : ℝ) ^ δ * (D : ℝ) * ((3 : ℝ) / 2) ^ n
      = ((3 ^ δ : ℕ) : ℝ) * ((D : ℝ) * ((3 : ℝ) / 2) ^ k) := by
    have hc : ((3 ^ δ : ℕ) : ℝ) = (3 : ℝ) ^ δ := by push_cast; ring
    rw [hc, hn, pow_add, ← h32]
    ring
  rw [hrw]
  have h := distToNearestInt_mul_le (D := 3 ^ δ) (by positivity) ((D : ℝ) * ((3 : ℝ) / 2) ^ k) 0
  simpa using h

/-- **A class bound whose multiplier is free is not class-restricted.**  If the class bound holds at
the dates `n ≡ r (mod q)` for each of the `q` multipliers `2^δ·D`, `δ < q`, then the *unrestricted*
bound holds at the same rate `θ`, with constant `c·(θ/3)^{q-1}` where `c` is the least of the `q`
class constants.

The rate is what matters and the rate survives: `κ(θ)` is unchanged, so a class-restricted device at
`θ > 2/3` settles the T-shift problem itself (`tShiftProblem_of_isRepelledMulClass_pow_two`), not
merely `T1Prime`.  What the descent costs is `2^{q-1}` of multiplier range at the device and
`(θ/3)^{q-1}` in the constant — see the section docstring for both, priced at the corpus's own
`q = 6` instance.

This is **not** `T1Prime p → TShiftProblem p A`: the hypothesis is `q` instances of
`IsRepelledMulClass`, T1′ asserts one, and a device with a rigid multiplier supplies only one.  It is
the reason no such device is known: every printed one in this circle carries a free integer. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem isRepelledMul_of_isRepelledMulClass_pow_two {θ : ℝ} {D q r : ℕ}
    (hq : 0 < q) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h : ∀ δ < q, IsRepelledMulClass θ (2 ^ δ * D) q r) :
    IsRepelledMul θ D := by
  simp only [IsRepelledMulClass] at h
  choose! C hCpos N hN using h
  have hne : (Finset.range q).Nonempty := ⟨0, Finset.mem_range.2 hq⟩
  set c : ℝ := (Finset.range q).inf' hne C with hc
  set n₀ : ℕ := (Finset.range q).sup N with hn₀
  have hcpos : 0 < c := by
    rw [hc, Finset.lt_inf'_iff]
    exact fun i hi => hCpos i (Finset.mem_range.1 hi)
  refine ⟨c * (θ / 3) ^ (q - 1), by positivity, n₀, fun k hk => ?_⟩
  obtain ⟨n, hkn, hnlt, hncls⟩ := exists_mem_class_Ico hq k r
  have hnk : n = k + (n - k) := by omega
  have hδq : n - k < q := by omega
  have hmem : n - k ∈ Finset.range q := Finset.mem_range.2 hδq
  have hbound := hN (n - k) hδq n (le_trans (le_trans (Finset.le_sup hmem) hk) hkn) hncls
  have hcast : (((2 ^ (n - k) * D : ℕ)) : ℝ) = (2 : ℝ) ^ (n - k) * (D : ℝ) := by push_cast; ring
  rw [hcast] at hbound
  have hchain : C (n - k) * θ ^ n
      ≤ 3 ^ (n - k) * distToNearestInt ((D : ℝ) * ((3 : ℝ) / 2) ^ k) :=
    le_trans hbound (distToNearestInt_descent' hnk)
  have h3 : (0 : ℝ) < 3 ^ (n - k) := by positivity
  refine le_of_mul_le_mul_left (le_trans ?_ hchain) h3
  have hle : c ≤ C (n - k) := Finset.inf'_le C hmem
  have hpow : (θ / 3) ^ (q - 1) ≤ (θ / 3) ^ (n - k) :=
    pow_le_pow_of_le_one (by positivity) (by linarith) (by omega)
  have hid : (3 : ℝ) ^ (n - k) * (θ / 3) ^ (n - k) = θ ^ (n - k) := by
    rw [div_pow]; field_simp
  calc 3 ^ (n - k) * (c * (θ / 3) ^ (q - 1) * θ ^ k)
      ≤ 3 ^ (n - k) * (C (n - k) * (θ / 3) ^ (n - k) * θ ^ k) := by
        gcongr
        exact (hCpos _ hδq).le
    _ = (3 ^ (n - k) * (θ / 3) ^ (n - k)) * (C (n - k) * θ ^ k) := by ring
    _ = θ ^ (n - k) * (C (n - k) * θ ^ k) := by rw [hid]
    _ = C (n - k) * θ ^ (k + (n - k)) := by rw [pow_add]; ring
    _ = C (n - k) * θ ^ n := by rw [← hnk]

/-- **The punchline, in problem form.**  A device that proves its bound at `θ > 2/3` on one residue
class, at the `q` multipliers `2^δ·D_p`, settles `TShiftProblem p A` — the *unrestricted* T-shift
problem, at every cycle target — and not only `T1Prime p`.

Contrast `t1Prime_of_twoForms`, which is what the same device settles when only one multiplier is
available.  The gap between the two theorems is the whole content of the relaxation. -/
@[category research solved, AMS 11 37, ref "TshiftS5", group "tshift_s5"]
theorem tShiftProblem_of_isRepelledMulClass_pow_two {θ : ℝ} {p q r : ℕ}
    (hp : 1 ≤ p) (hq : 0 < q) (hθ : (2 : ℝ) / 3 < θ) (hθ1 : θ ≤ 1)
    (h : ∀ δ < q, IsRepelledMulClass θ (2 ^ δ * Z32.cycleDenom p) q r) (A : ℤ) :
    TShiftProblem p A :=
  tShiftProblem_of_isRepelledMul hp A
    ⟨θ, hθ, isRepelledMul_of_isRepelledMulClass_pow_two hq (by linarith) hθ1 h⟩

end TShift
