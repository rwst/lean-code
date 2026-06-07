/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import BertinPisot.PhiFamily
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Compact families of rational functions `ℱ(q, k, δ)` (Bertin §2.2)

Bertin's **Definition 2.2** (*Pisot and Salem Numbers*, [Ber92]): for parameters `q ∈ ℕ*`, `k ∈ ℕ`
and `δ ∈ ℝ⁺*`, the family `ℱ(q, k, δ)` is the set of rational functions `f` that can be written
`f = A / Q` with integer polynomials `A, Q ∈ ℤ[X]` such that

* **i)** `Q(0) = q` and `A(0) ≠ 0`;
* **ii)** `Q` has at most `k` zeros in the open unit disk `D(0,1)`, and `Q` does not vanish on
  `D(0,δ) ∪ {z ∈ ℂ : |z| = 1}`;
* **iii)** `|A(z) / Q(z)| ≤ 1` whenever `|z| = 1`.

These are the families Bertin proves **compact** (for the topology of uniform convergence on the
compact subsets of `D(0,1)`); the bound `k` on the number of poles inside the disk together with the
non-vanishing collar `D(0,δ)` and the boundary modulus bound iii) are exactly what a normal-family /
Montel argument needs. Every member has denominator constant term `Q(0) = q`, so
`ℱ(q, k, δ) ⊆ Φ_q` (`BertinPisot.PhiFamily`): `ℱ` is the analytically constrained subfamily of `Φ_q`
carved out by conditions ii) and iii).

`Family_isCompact` is **Theorem 2.2.1**: `ℱ(q, k, δ)` is compact for the topology of uniform
convergence on the compact subsets of `D(0, δ)`. Each member is holomorphic on `D(0, δ)` (its
denominator does not vanish there, ii), so realises as a continuous map `D(0,δ) → ℂ`; the
realisations form a compact subset of `C(D(0,δ), ℂ)` — whose compact-open topology, `D(0,δ)` being
locally compact, **is** the topology of uniform convergence on the compacts of `D(0,δ)`. Recorded as
a literature axiom: its proof is the classical normal-families argument — `ℱ` is uniformly bounded on
each compact of `D(0,δ)` (from the boundary bound iii) and the at-most-`k` poles ii), via a finite
Blaschke product and the maximum-modulus principle), so by **Montel's theorem** it is normal, i.e.
relatively compact; closedness uses **Hurwitz's theorem** to keep the pole count and non-vanishing
stable under limits, and the §2.1 closure of `Φ_q` (`mem_Phi_of_tendsto`) to keep the integer
denominator with constant term `q`. Montel's and Hurwitz's theorems are not yet in Mathlib.

`le_zeros_ball_of_norm_le_on_circle` is **Lemma 2.2.1**, a Rouché-type tool of §2.2 (about general
analytic functions, independent of `ℱ`): if `f, g` are analytic on `D(0,r)` (`r > 1`) with
`|f| ≤ |g|` on the unit circle `|z| = 1`, and `f - g` vanishes to order exactly `n` at `0`
(`f - g = γₙ zⁿ + ⋯`, `γₙ ≠ 0`), then `g` has at least `n` zeros in `D(0,1)` counted with
multiplicity. Recorded as a literature axiom: Bertin's proof applies **Rouché's theorem** to
`f - λ g` (`λ > 1`) and lets `λ → 1`, after dividing out the boundary zeros of `g`; Rouché's theorem
is not yet in Mathlib.

`limitPoint_num_ne_reverse_denom` is **Proposition 2.2.1**: if `f = A / Q` (reduced integer
representation, `Q(0) = q`) is a limit point of `ℱ(q, k, δ)`, then `A ≠ ± Q*`, where `Q* = Q.reverse`
is the reciprocal polynomial of `Q`. Recorded as a literature axiom; its proof combines **Theorem
2.2.1** (`Family_isCompact`, convergence of the `Aₙ/Qₙ`) and **Lemma 2.2.1**
(`le_zeros_ball_of_norm_le_on_circle`): a putative `A = ε Q*` would, via the order/zero-count bounds,
force a convergent subsequence to be eventually constant equal to `f`, contradicting that a limit
point is approached by *distinct* members.

## Encoding

* `f : RatFunc ℚ`, with the representative integer polynomials sent into `RatFunc ℚ` along
  `ℤ[X] → ℚ[X] → RatFunc ℚ` (`Polynomial.map (Int.castRingHom ℚ)`, then the polynomial-to-fraction
  coercion), matching `Phi`.
* The parameter constraints `q ∈ ℕ*` and `δ ∈ ℝ⁺*` are recorded as the guards `0 < q` and `0 < δ`
  inside the membership predicate (so `ℱ(q, k, δ) = ∅` for `q = 0` or `δ ≤ 0`), parallel to `Phi`;
  `k ∈ ℕ` needs no guard (`k = 0` allows no pole in the disk).
* Complex evaluation `A(z), Q(z)` is `Polynomial.aeval z` along the `ℤ`-algebra map `ℤ[X] → ℂ`. The
  zeros of `Q` are its complex root multiset `Q.aroots ℂ`, so condition ii)'s count is **with
  multiplicity** (`Multiset.card` of the roots filtered into the disk). The open disk `D(0,r)` is
  `‖z‖ < r` and the unit circle is `‖z‖ = 1`. Conditions i)–ii) force every pole of `f` in `D(0,1)`
  into the annulus `δ ≤ |z| < 1`, at most `k` of them counted with multiplicity.
* The function-space topology of Theorem/Proposition 2.2.1 lives on `C(D(0,δ), ℂ)` (continuous maps,
  compact-open topology = uniform-on-compacts since `D(0,δ)` is locally compact); members of `ℱ` enter
  it through `FamilyRealizations` (`f ↦ z ↦ RatFunc.eval (algebraMap ℚ ℂ) z f`), and "limit point" is
  `AccPt _ (𝓟 (FamilyRealizations q k δ))`. The reciprocal polynomial `Q*` is `Polynomial.reverse Q`.

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
-/

open Polynomial

open Classical in
/-- **Bertin's compact family `ℱ(q, k, δ)`** (Definition 2.2; `q ∈ ℕ*`, `k ∈ ℕ`, `δ ∈ ℝ⁺*`): the set
of rational functions `f : RatFunc ℚ` admitting a representation `f = A / Q` with `A, Q ∈ ℤ[X]`
(mapped into `RatFunc ℚ` along `Int.castRingHom ℚ`) such that

* **i)** `Q(0) = q` and `A(0) ≠ 0` (`Q.coeff 0 = q`, `A.coeff 0 ≠ 0`);
* **ii)** `Q` has at most `k` zeros in `D(0,1)` counted with multiplicity
  (`((Q.aroots ℂ).filter (‖·‖ < 1)).card ≤ k`) and is non-zero on `D(0,δ) ∪ {z : |z| = 1}`;
* **iii)** `‖A(z) / Q(z)‖ ≤ 1` for `|z| = 1`.

The guards `0 < q`, `0 < δ` encode `q ∈ ℕ*`, `δ ∈ ℝ⁺*` (so the family is empty otherwise). Every
member lies in `Φ_q` (denominator constant term `q`); `ℱ` is the analytically constrained subfamily
Bertin proves compact. -/
@[category API, AMS 11 12 30, ref "Ber92"]
def Family (q k : ℕ) (δ : ℝ) : Set (RatFunc ℚ) :=
  { f | 0 < q ∧ 0 < δ ∧ ∃ A Q : ℤ[X],
      f = (A.map (Int.castRingHom ℚ) : RatFunc ℚ) / (Q.map (Int.castRingHom ℚ) : RatFunc ℚ) ∧
      Q.coeff 0 = (q : ℤ) ∧ A.coeff 0 ≠ 0 ∧
      ((Q.aroots ℂ).filter (fun z => ‖z‖ < 1)).card ≤ k ∧
      (∀ z : ℂ, (‖z‖ < δ ∨ ‖z‖ = 1) → (aeval z Q : ℂ) ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖(aeval z A : ℂ) / (aeval z Q : ℂ)‖ ≤ 1) }

/-- The members of `ℱ(q, k, δ)` **realised as continuous functions on `D(0, δ)`**: the set of
`g : C(D(0,δ), ℂ)` agreeing with some `f ∈ Family q k δ`, i.e. `g z = f(z)` for all `z ∈ D(0,δ)`,
where `f(z) = RatFunc.eval (algebraMap ℚ ℂ) z f`. Each member of `ℱ` is holomorphic on `D(0, δ)` (its
denominator is non-vanishing there, condition ii), hence has such a realisation. This set carries the
compact-open topology — uniform convergence on the compacts of `D(0, δ)`, as `D(0, δ)` is locally
compact — in which `ℱ` is compact (`Family_isCompact`, Theorem 2.2.1) and limit points are taken
(`limitPoint_num_ne_reverse_denom`, Proposition 2.2.1). -/
@[category API, AMS 11 12 30, ref "Ber92", formal_uses Family]
def FamilyRealizations (q k : ℕ) (δ : ℝ) : Set C(↥(Metric.ball (0 : ℂ) δ), ℂ) :=
  { g | ∃ f ∈ Family q k δ, ∀ z : ↥(Metric.ball (0 : ℂ) δ),
      g z = RatFunc.eval (algebraMap ℚ ℂ) (z : ℂ) f }

/-! ## Informal-result registry

The classical complex-analysis theorems Bertin's proof of Theorem 2.2.1 relies on that are **not** in
Mathlib, recorded at the level of "what notion the proof needs", so the `informal_uses` edges share
canonical nodes. -/

informal_result "montel-normal-families"
  latex "Montel's theorem on normal families of holomorphic functions: a family of holomorphic functions on a domain that is uniformly bounded on every compact subset is normal — relatively compact for the topology of uniform convergence on compact subsets, with every limit again holomorphic. Obtained from local equiboundedness through the Cauchy estimates (giving local equicontinuity) and the Arzelà–Ascoli theorem with a diagonal extraction; the classical compactness engine for families of analytic functions."
  refs "Ber92"

informal_result "hurwitz-zeros"
  latex "Hurwitz's theorem on zeros: if holomorphic functions converge uniformly on compact subsets to a limit that is not identically zero, then for every closed disk on whose boundary the limit does not vanish, the functions eventually have — counted with multiplicity — the same number of zeros inside as the limit. Governs how the count of zeros (hence of poles) in a disk behaves under local uniform limits; here it keeps the bound of at most k poles in D(0,1) and the non-vanishing on D(0,δ) ∪ {|z|=1} closed under limits, so the limit stays inside ℱ(q,k,δ)."
  refs "Ber92"

/-- **Theorem 2.2.1** (Bertin). The family `ℱ(q, k, δ)` (`Family`) is **compact** for the topology of
uniform convergence on the compact subsets of the open disk `D(0, δ)`.

Each `f ∈ ℱ(q, k, δ)` is holomorphic on `D(0, δ)` — its denominator `Q` does not vanish there
(condition ii) — so `f` has a continuous realisation `z ↦ f(z) = RatFunc.eval (algebraMap ℚ ℂ) z f`
on `D(0, δ)`. The statement is the compactness of the set of these realisations inside the continuous
maps `C(D(0,δ), ℂ)`; as `D(0, δ)` is locally compact, the compact-open topology on `C(D(0,δ), ℂ)`
**is** the topology of uniform convergence on the compact subsets of `D(0, δ)`, so this is exactly
Bertin's statement.

Recorded as a literature axiom on the authority of [Ber92]. Proof sketch: the boundary bound iii)
(`|f| ≤ 1` on `|z| = 1`) together with the at-most-`k` poles in `D(0,1)` (ii) bounds `ℱ` uniformly on
each compact of `D(0, δ)` — multiply `f` by the finite Blaschke product over its poles and apply the
maximum-modulus principle — so by **Montel's theorem** (`montel-normal-families`) `ℱ` is a normal
family, i.e. relatively compact. Closedness (a local-uniform limit of members is again a member) uses
**Hurwitz's theorem** (`hurwitz-zeros`) to preserve the pole count ii) and the non-vanishing, while
the integer-denominator constraints i) (`Q(0) = q`, integer coefficients) pass to the limit through
the `q`-power integrality bounds of §2.1 — uniform-on-compacts convergence near `0` forces
coefficientwise convergence, so the closure of `Φ_q` under formal convergence (`mem_Phi_of_tendsto`,
Theorem 2.1) applies. Montel's theorem and Hurwitz's theorem on zeros are not yet in Mathlib;
`#print axioms` surfaces this dependency in every downstream proof. -/
@[category research solved, AMS 11 12 30, ref "Ber92",
  formal_uses Family FamilyRealizations mem_Phi_of_tendsto,
  informal_uses "montel-normal-families" "hurwitz-zeros"]
axiom Family_isCompact (q k : ℕ) (δ : ℝ) : IsCompact (FamilyRealizations q k δ)

/-! ## Lemma 2.2.1 — a Rouché-type lower bound on zeros

A supporting analytic tool of §2.2 (independent of `ℱ`): the classical theorem Bertin's proof needs
that is **not** in Mathlib, recorded as a registry node so the `informal_uses` edge below points at
it. -/

informal_result "rouche-theorem"
  latex "Rouché's theorem: if f and g are holomorphic on a domain containing the closed disk and |f(z) − g(z)| < |g(z)| on the bounding circle, then f and g have the same number of zeros inside the disk, counted with multiplicity (equivalently, by the argument principle, equal winding numbers of f and g about 0). The classical tool for locating and counting zeros of holomorphic functions by boundary comparison."
  refs "Ber92"

/-- **Lemma 2.2.1** (Bertin). Let `f, g` be analytic on `D(0, r)` with `r > 1`. If

* i) `‖f z‖ ≤ ‖g z‖` whenever `‖z‖ = 1`, and
* ii) `f - g` vanishes to order exactly `n` at `0` (`analyticOrderAt (f - g) 0 = n`, i.e.
  `f(z) - g(z) = γₙ zⁿ + ⋯` with `γₙ ≠ 0`),

then `g` has at least `n` zeros in the open unit disk `D(0,1)`, counted with multiplicity:
`n ≤ ∑ᶠ z ∈ D(0,1), analyticOrderNatAt g z`, the total vanishing order of `g` over the disk
(`analyticOrderNatAt g z` is the order of `g`'s zero at `z`, `0` away from zeros; the `finsum` is its
finite total, since `g ≢ 0` forces isolated zeros, finite in the relatively compact `D(0,1) ⊂ D(0,r)`).

Recorded as a literature axiom on the authority of [Ber92]. Proof (Bertin): write `k` for the number
of zeros of `g` in `D(0,1)`. (a) If `g` does not vanish on `|z| = 1`, then for `λ > 1` the function
`hλ = f - λ g` has `‖f‖ < ‖λ g‖` on the circle, so by **Rouché's theorem** `hλ` has the same `k`
zeros in `D(0,1)` as `λ g`; letting `λ → 1` shows `h₁ = f - g` has at most `k` zeros, whence `n ≤ k`.
(b) In general, divide out the boundary zeros: with `P = ∏ (z - αᵢ)` over the zeros `αᵢ` of `g` on
`|z| = 1`, inequality i) makes `f / P` and `g / P` analytic on `D(0,1)`, their difference still of
order `n` at `0` (leading coefficient `γₙ / P(0)`), and case (a) applies. **Rouché's theorem** is not
yet in Mathlib; `#print axioms` surfaces this dependency downstream. -/
@[category research solved, AMS 30, ref "Ber92", informal_uses "rouche-theorem"]
axiom le_zeros_ball_of_norm_le_on_circle {f g : ℂ → ℂ} {r : ℝ} {n : ℕ}
    (hr : 1 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 r))
    (hi : ∀ z : ℂ, ‖z‖ = 1 → ‖f z‖ ≤ ‖g z‖)
    (hii : analyticOrderAt (fun z => f z - g z) 0 = (n : ℕ∞)) :
    n ≤ ∑ᶠ z ∈ Metric.ball (0 : ℂ) 1, analyticOrderNatAt g z

/-! ## Proposition 2.2.1 — limit points are not (anti)palindromic -/

/-- **Proposition 2.2.1** (Bertin). Let `f = A / Q` be a **limit point** of `ℱ(q, k, δ)`, taken in its
reduced integer representation — `A, Q ∈ ℤ[X]` with coprime images over `ℚ[X]` (`hcop`) and
`Q(0) = q` (`hQ0`), and `A / Q ∈ ℱ(q, k, δ)` (`hmem`). Then `A ≠ ± Q*`, where `Q* = Q.reverse` is the
reciprocal polynomial of `Q` (its coefficients reversed); that is, `A ≠ Q.reverse ∧ A ≠ -Q.reverse`.

The limit point is taken in the function-space realisation of `ℱ`: `gf` is the realisation of `f` on
`D(0, δ)` (`hgf`, `gf z = RatFunc.eval (algebraMap ℚ ℂ) z (A/Q)`), and `hacc` says `gf` is an
accumulation point of `FamilyRealizations q k δ` — exactly "`f` is a limit point of `ℱ`" in the
topology of uniform convergence on the compacts of `D(0, δ)` (Theorem 2.2.1).

Recorded as a literature axiom on the authority of [Ber92]. Proof: a limit point is the limit of a
sequence of distinct `fₙ = Aₙ / Qₙ ∈ ℱ`, and by (the proof of) Theorem 2.2.1
(`Family_isCompact`) `Aₙ / Qₙ → A / Q`. Suppose `A = ε Q*` with `ε = ±1`, and set `s = 1 + k + deg Q`.
Convergence gives `ord (Aₙ Q − ε Q* Qₙ) ≥ s` for all large `n`. Since `fₙ ∈ ℱ`, condition iii) gives
`|Aₙ(z) Q(z)| ≤ |ε Q*(z) Qₙ(z)|` on `|z| = 1` (using `|Q*| = |Q|` there, as `Q` has real
coefficients), while `Q* Qₙ` has at most `s − 1` zeros in `D(0,1)` (the `≤ k` poles of `fₙ` plus
`deg Q`). **Lemma 2.2.1** (`le_zeros_ball_of_norm_le_on_circle`), applied to `Aₙ Q` and `ε Q* Qₙ`,
then forces `fₙ = f` for all large `n`, contradicting the distinctness of the `fₙ`. Hence
`A ≠ ± Q*`. -/
@[category research solved, AMS 11 12 30, ref "Ber92",
  formal_uses Family FamilyRealizations Family_isCompact le_zeros_ball_of_norm_le_on_circle,
  informal_uses "rouche-theorem" "montel-normal-families"]
axiom limitPoint_num_ne_reverse_denom {q k : ℕ} {δ : ℝ} {A Q : ℤ[X]}
    (hQ0 : Q.coeff 0 = (q : ℤ))
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)))
    (hmem : ((A.map (Int.castRingHom ℚ) : RatFunc ℚ) /
            (Q.map (Int.castRingHom ℚ) : RatFunc ℚ)) ∈ Family q k δ)
    (gf : C(↥(Metric.ball (0 : ℂ) δ), ℂ))
    (hgf : ∀ z : ↥(Metric.ball (0 : ℂ) δ), gf z =
      RatFunc.eval (algebraMap ℚ ℂ) (z : ℂ)
        ((A.map (Int.castRingHom ℚ) : RatFunc ℚ) / (Q.map (Int.castRingHom ℚ) : RatFunc ℚ)))
    (hacc : AccPt gf (Filter.principal (FamilyRealizations q k δ))) :
    A ≠ Q.reverse ∧ A ≠ -Q.reverse
