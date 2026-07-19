/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.QuadraticPisot
import RB.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# E.2, stated (plan-B1E2, M5)

E.2 is the **automatic upgrade of [Dub09] Thm 2**:

> [Dub09] **Thm 2** (p. 244, verbatim): *Let `β > 1` be an algebraic number with minimal
> polynomial `b_d X^d + ⋯ + b_1 X + b_0 ∈ ℤ[X]`.  If the sequence
> `w_n = b_d x_{n+d} + ⋯ + b_1 x_{n+1} + b_0 x_n`, `n = 0,1,2,…`, is **ultimately periodic**,
> then `β` must be either a Pisot number or a Salem number.*

Replace "ultimately periodic" by "`k`-automatic" in the hypothesis; the conclusion is
`β ∈ Bertin.U` (`Bertin.U_eq_S_union_T` : `U = S ∪ T` = Pisot ∪ Salem).  **Nothing here is
proved** — E.2 is open, and per the layered-QA policy it is a `def`, never an axiom.  What this
file does is (i) *state* it precisely at `d = 2`, (ii) record the encoding trap that makes the
obvious statement false, and (iii) prove the two facts that fix E.2's position: its converse in
the quadratic case, and that our own `β = 3/2` is not exempt.

## Why `d = 2` and not general `d`

The general statement needs the minimal polynomial's coefficient vector as the word's kernel,
which the corpus does not carry; the quadratic case is exactly where [Dub09] §6's examples live,
where `Bertin.no_salem_lt_four` removes the Salem clause outright, and where `RB.QuadraticPisot`
supplies the converse.  Cases `d ≥ 3`, and E.2's cases 1–3, stay parked behind WP5 ([B1E2] §5).

## The encoding trap — why `E2Quadratic` is not stated with `Int.toNat`

`AS.IsAutomatic` consumes `ℕ → ℕ`, while `w` is `ℤ`-valued, so the obvious move is to state the
hypothesis as `AS.IsAutomatic (fun n => (pisotWord β a b x₀ n).toNat)`.  **That statement is
false**, and not subtly:

> take `β = (5+√5)/2`, the larger root of `X² − 5X + 5` (`a = 5`, `b = 5`).  Its conjugate
> `β' = (5−√5)/2 = 1.381…` exceeds `1`, so `β ∉ S`; it is quadratic, so `β ∉ T`
> (`RB.not_mem_T_of_natDegree_two`); hence **`β ∉ U`**.  But `β − a = −1.381…`, so
> `w_n = τ_{n+1} + (β−a)τ_n ∈ (−1.381…, 1)`, i.e. `w` takes values in `{−1, 0}` — and
> `Int.toNat` maps *both* to `0`.  So `toNat ∘ w` is the constant `0`, which is automatic, while
> `β ∉ U`: the implication fails.  (Checked numerically: `w` really does take both values, at
> `n = 2, 17, 27, …`.)

`Int.toNat` is not injective on `w`'s range, so it destroys exactly the distinction the
hypothesis is about.  The fix used below is to quantify over an **arbitrary faithful encoding**
`f : ℕ → ℕ` (`∀ m n, f m = f n ↔ w m = w n`).  This is the honest reading: automaticity depends
only on the sequence up to injective relabelling of the alphabet, so "some faithful `f` is
automatic" is exactly "`w` is automatic" — with no arbitrary choice of offset.

## Where E.2 has content, and where it does not

* **Off `U`** it is a real statement — and that is where our `β = 3/2` lives:
  `three_halves_not_mem_Bertin_U` (`3/2` is not even an algebraic integer).  This is the formal
  content of [B1E2] §5's *deficient-place framing*: Pisot and Salem numbers are exempt because
  they have no deficient place, and `3/2` manifestly does.
* **On `U`** its conclusion is not improvable: `RB.isAutomatic_pisotWord` shows every quadratic
  Pisot `β` really does produce an automatic (indeed constant) word.  So the Pisot clause is
  **populated, not vacuous** — E.2 cannot be sharpened by dropping it.

Together with `e2Quadratic_converse` below, `E2Quadratic` would upgrade to an **iff**:
`w` automatic `⟺` `β ∈ Bertin.S`, for quadratic `β`.  The `⟸` half is a theorem here; the `⟹`
half is E.2.

## Contents

* **`RB.E2Quadratic`** — E.2 at `d = 2`, stated. **Open; a `def`, not an axiom.**
* **`RB.e2Quadratic_converse`** — the converse, **proved**: quadratic Pisot ⇒ `w` automatic.
* **`RB.three_halves_not_mem_Bertin_U`** — `3/2` is not Pisot or Salem (not an algebraic
  integer): our `β` is not exempt.
* `RB.not_isIntegral_three_halves` — the underlying integrality failure.

## References

* [Dub09] A. Dubickas. Glasgow Math. J. **51** (2009), 243–252.  Thm 2 (p. 244) = E.2's periodic
  case, **already proved**; §6 (pp. 250–251) = the converse, formalized in `RB.QuadraticPisot`.
* [Ber92] M.-J. Bertin et al. *Pisot and Salem numbers.* Birkhäuser 1992.  (Def 5.1 `U`.)
* [Sch80] K. Schmidt. *On periodic expansions of Pisot numbers and Salem numbers.* Bull. LMS
  **12** (1980), 269–278.  ([Dub09] notes Thm 2's conclusion is the same as Schmidt's.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §5 (E.2 re-scoped — cases 1–3 parked), M5.
-/

namespace RB

open Polynomial

/-! ## `3/2` is not exempt -/

/-- `3/2` is **not an algebraic integer**: `ℤ` is integrally closed in `ℚ`, and `3/2 ∉ ℤ`. -/
@[category research solved, AMS 11, ref "Ber92", group "rb_quadratic_pisot"]
theorem not_isIntegral_three_halves : ¬ IsIntegral ℤ ((3 : ℝ) / 2) := by
  intro hint
  rw [show ((3 : ℝ) / 2) = algebraMap ℚ ℝ (3 / 2) by rw [eq_ratCast]; norm_num] at hint
  rw [isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective,
    IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨y, hy⟩ := hint
  have h1 : (y : ℚ) = 3 / 2 := by simpa using hy
  have h2 : (2 : ℤ) * y = 3 := by
    have : (2 : ℚ) * (y : ℚ) = 3 := by rw [h1]; ring
    exact_mod_cast this
  omega

/-- **`3/2` is neither a Pisot nor a Salem number** — it is not even an algebraic integer.

This is [B1E2] §5's *deficient-place framing*, made formal: `U` (Pisot ∪ Salem) is exactly the
class [Dub09] Thm 2 exempts, and `3/2` is not in it.  So E.2's hypothesis is not vacuous for our
`β`, and `RB.wmin` is a legitimate target.

It also gives a **second proof of `RB.not_eventually_periodic`**, via the literature rather than
via the corpus: [Dub09] Thm 2 says an ultimately periodic `w` forces `β ∈ U`, and `3/2 ∉ U`.  The
corpus's own proof is `RB.not_eventually_periodic` (std3, [AFS08] Prop 26), so this is a
cross-check on the identification, not a new dependency — Thm 2 is deliberately **not**
axiomatized here, since its only consumer would be a theorem we already have. -/
@[category research solved, AMS 11, ref "Ber92" "Dub09", group "rb_quadratic_pisot"]
theorem three_halves_not_mem_Bertin_U : ((3 : ℝ) / 2) ∉ Bertin.U := by
  rintro ⟨-, hint, -⟩
  exact not_isIntegral_three_halves hint

/-! ## E.2, stated at `d = 2` -/

/-- **E.2 at `d = 2`, stated** ([B1E2] §5; the automatic upgrade of [Dub09] Thm 2).

> For a quadratic irrational `β > 1` with `β² − aβ + b = 0` and any `x₀ > 0`: if the word
> `wₙ = x_{n+2} − a·x_{n+1} + b·xₙ` of the ceiling orbit `xₙ = ⌈βxₙ₋₁⌉` is **automatic**, then
> `β` is a **Pisot** number.

Two deliberate choices:

* The conclusion is `β ∈ Bertin.S` (Pisot), not `β ∈ Bertin.U` (Pisot **or** Salem) as in
  [Dub09] Thm 2 — because at degree `2` they coincide (`mem_S_iff_mem_U_of_natDegree_two`, via
  `Bertin.no_salem_lt_four`).  Stating `U` here would be strictly weaker for no reason.
* The hypothesis quantifies over an arbitrary **faithful** `ℕ`-encoding `f` of the `ℤ`-valued
  `w`, rather than a fixed one.  See the module doc: the obvious `Int.toNat` encoding makes this
  statement **false** (witness `β = (5+√5)/2`), because `toNat` is not injective on `w`'s range.

**Open.**  A `def`, never an axiom — the layered-QA policy forbids axiomatizing open conjectures,
and unlike [Dub09] Thm 2 (refereed, and merely *not* formalized) E.2 is proved nowhere. -/
@[category API, AMS 11 68, ref "Dub09" "B1E2", group "rb_quadratic_pisot"]
def E2Quadratic : Prop :=
  ∀ (β : ℝ) (a b x₀ : ℤ) (f : ℕ → ℕ),
    1 < β → Irrational β → β ^ 2 - a * β + b = 0 → 0 < x₀ →
    (∀ m n, f m = f n ↔ pisotWord β a b x₀ m = pisotWord β a b x₀ n) →
    AS.IsAutomatic f → β ∈ Bertin.S

/-- **The converse of `E2Quadratic`, proved** ([Dub09] §6): a quadratic Pisot `β` *does* produce
an automatic word — indeed a constant one, so *every* faithful encoding `f` of it is constant and
hence automatic.

So E.2's Pisot clause is populated: were `E2Quadratic` proved, the two would combine into an
**iff** — for quadratic `β`, `w` is automatic **exactly** when `β` is Pisot. -/
@[category research solved, AMS 11 68, ref "Dub09" "Ber92", group "rb_quadratic_pisot"]
theorem e2Quadratic_converse {β : ℝ} {a b : ℤ} (h : IsQuadraticPisot β a b) {x₀ : ℤ}
    (hx₀ : 0 < x₀) (f : ℕ → ℕ)
    (hfaithful : ∀ m n, f m = f n ↔ pisotWord β a b x₀ m = pisotWord β a b x₀ n) :
    AS.IsAutomatic f := by
  obtain ⟨c, hc⟩ := pisotWord_constant h hx₀
  have hconst : f = fun _ => f 0 := by
    funext n
    exact (hfaithful n 0).mpr (by rw [hc, hc])
  rw [hconst]
  exact isAutomatic_const _

end RB
