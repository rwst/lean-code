/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Polynomial.Reverse
import BertinPisot.SchurClass
import BertinPisot.GeneralizedSchur
import BertinPisot.GeometricMean
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Characterization of certain meromorphic functions on `D(0,1)` (Bertin §3.4)

Bertin's **§3.4** (*Pisot and Salem Numbers*, [Ber92]) studies the class `𝓜_∞` of meromorphic
functions on the open unit disk that are bounded by `1` at the boundary — the meromorphic
generalisation of the Schur class `𝓜 = Complex.schurClass` (§3.2, `BertinPisot.SchurClass`).

**Definition 3.4.** `𝓜_∞` is the set of functions `f` meromorphic on `D(0,1)` with

* **no pole at the origin**, and
* a **finite number of poles** in `D(0,1)`, that verify
* `limsup_{z → e^{iθ}, |z| < 1} |f(z)| ≤ 1` for every `θ ∈ [0, 2π]`.

* `Complex.schurClassInfty` is `𝓜_∞`, a `Set (ℂ → ℂ)`:
  - meromorphic on the disk — `MeromorphicOn f (ball 0 1)`;
  - no pole at `0` — `AnalyticAt ℂ f 0`;
  - finitely many poles — the set of non-analyticity points inside the disk,
    `{z ∈ ball 0 1 | ¬ AnalyticAt ℂ f z}`, is finite (for a meromorphic function the poles are
    exactly the points of non-analyticity);
  - boundary bound — for every boundary point `w` (`|w| = 1`, i.e. `w = e^{iθ}` as `θ` ranges over
    `[0, 2π]`), the `limsup` of `‖f‖` along `z → w` from inside the disk is `≤ 1`. The `limsup` is
    taken in `EReal`, so a pole accumulating at the boundary yields `⊤ ≰ 1` and is correctly excluded.
* `Complex.mem_schurClassInfty` unfolds membership.

## Remark 3.4.1 — the Blaschke-quotient factorisation of `𝓜_∞`

Bertin's **Remark 3.4.1** characterises `𝓜_∞` by a finite-Blaschke factorisation: `f ∈ 𝓜_∞` **iff**
`f = (P*/P)·h` with `h ∈ 𝓜` (the Schur class, `BertinPisot.SchurClass`), `P ∈ ℂ[z]`, `P(0) ≠ 0`, and
all zeros of `P` in `D(0,1)`. Here `P* = reciprocalC P` is the **reciprocal polynomial** of §3.1
(`BertinPisot.SchurAlgorithm`), `P*(z) = z^{deg P}·conj(P(1/conj z))`; `P*/P` is a finite Blaschke
product: unimodular on `|z| = 1`, with poles exactly the zeros of `P` (inside `D`) and zeros `1/conj α`
(outside `D`).

* `Complex.norm_eval_reciprocalC` is the **proved** elementary heart: `‖P*(z)‖ = ‖P(z)‖` on the unit
  circle `‖z‖ = 1` (so the Blaschke quotient has modulus `1` there,
  `Complex.norm_eval_reciprocalC_div_eq_one`).
* `Complex.mem_schurClassInfty_iff_reciprocalC_mul` is the characterisation itself, a `cited` axiom
  (`ref "Ber92"`): its proof needs finite-Blaschke / bounded-type meromorphic factorisation and a
  maximum-modulus boundary argument, none of which is in Mathlib (the `informal_uses` edge
  `meromorphic-blaschke-factorization` names this pillar) — the same situation as Theorem 3.2.1 and
  Corollary 3.2.2 in `BertinPisot.SchurClass`.

## Lemma 3.4.1 — the Schur-step polynomials `Eₗ, Sₗ` and the determinant recursion

Bertin's **Lemma 3.4.1**: for `F = Fⁱ` in the generalised Schur algorithm with successor `G = Fⁱ⁺ˡ`
(`l ≥ 1`), there are `Eₗ, Sₗ ∈ ℂ[z]` with **a)** i) `d°Eₗ, d°Sₗ ≤ l`,
ii) `G = (F Eₗ − Sₗ)/(Ẽₗ − F S̃ₗ)` (`Ã = reciprocalAt l A`, Bertin's `Ã(z) = zˡ Ā(1/z)`),
iii) `Eₗ Ẽₗ − Sₗ S̃ₗ = tₗ zˡ` (`tₗ > 0`), iv) `ord(F S̃ₗ − Ẽₗ) = l` with leading coefficient `vₗ ≠ 0`,
v) `ord(F Eₗ − Sₗ) ≥ l`; and **b)** the determinant recursion
`δₙ(F) = (|vₗ|²/tₗˡ)^{n+1} δₙ₋ₗ(G)` for `n ≥ l`. Bertin proves it per transformation:

* **Proof case 2 — the Schur transform (`l = 1`), proved here in full.** With `E₁ = 1`, `S₁ = C γ₀`
  (`γ₀ = F(0)`, `|γ₀| < 1`), `G = schurTransform F`: `Complex.schurStep_relation` is ii) (off
  `schurTransform_spec`), `Complex.schurStep_pseudonorm` is iii) with `t₁ = 1 − γ₀γ̄₀`
  (`Complex.schurStep_t_pos`), `Complex.schurStep_leadCoeff` is iv) with `v₁ = |γ₀|² − 1`
  (`Complex.schurStep_v_ne_zero`), `Complex.schurStep_order` is v), and `Complex.schurDelta_schurStep`
  is b), `δₙ(F) = (1 − |γ₀|²)^{n+1} δₙ₋₁(F¹)` — exactly `schurDelta_recurrence` (Lemma 3.1.2); the
  general constant `(|v₁|²/t₁¹)^{n+1}` reduces to it.
* **Proof case 1 — a unimodular step (`l = 2k + s`).** `Eₗ = zˢ(Q − zᵏ)`, `Sₗ = zˢ γ₀ Q` with `Q` the
  degree-`≤ 2k` numerator of Lemma 3.3.1; `Complex.unimodularStep_natDegree_E`/`_S` prove i).
  Properties ii)–v) and b) reduce to **Lemma 3.3.1** (`BertinPisot.GeneralizedSchur`), a `cited` axiom.

`Complex.schurDelta_lemma_3_4_1` records the **general b)** as a `cited` axiom over the a)-data
`(Eₗ, Sₗ, tₗ, vₗ, G)`. The Schur-transform case is a fully proved instance.

## Lemma 3.4.2 — convergent representation of `F` via `Fⁱ` and the determinant formula

Bertin's **Lemma 3.4.2** is the convergent companion of Lemma 3.4.1, relating `F` to its `i`-th Schur
iterate `Fⁱ = schurTransform^[i] F`: **a)** there are `Aᵢ, Qᵢ ∈ ℂ[z]` with i) `d°Aᵢ, d°Qᵢ ≤ i`,
ii) `F = (Aᵢ + Q̃ᵢ Fⁱ)/(Qᵢ + Ãᵢ Fⁱ)`, iii) `ord(F Ãᵢ − Q̃ᵢ) = i` with leading coefficient `uᵢ ≠ 0`,
iv) `ord(F Qᵢ − Aᵢ) ≥ i`, v) `Qᵢ Q̃ᵢ − Aᵢ Ãᵢ = ωᵢ zⁱ` (`ωᵢ > 0`); and **b)** the determinant formula
`δₙ(F) = (|uᵢ|²ⁿ/ωᵢⁿ) λᵢ δₙ₋ᵢ(Fⁱ)` (`λᵢ ≠ 0`, `n ≥ i`). Bertin proves it by induction from Lemma 3.4.1.

* `Complex.exists_convergents_lemma_3_4_2` is **a)**, a `cited` axiom (`ref "Ber92"`) — the `Fⁱ`-form
  Schur–Wall convergent representation, the companion of the §3.2 `exists_convergents` (Lemma 3.2.1 b).
* `Complex.schurDelta_lemma_3_4_2` is **b)**, **proved**: it is the already-proved iterated determinant
  formula `schurDelta_add_eq_iterate_prod` (Lemma 3.2.1 c) with offset `k = n − i`, giving
  `δₙ(F) = (∏_{j<i} δ₀(Fʲ)^{(i−j)+(n−i+1)}) δₙ₋ᵢ(Fⁱ)` for `n ≥ i`; the explicit Schur-parameter product
  is Bertin's constant `(|uᵢ|²ⁿ/ωᵢⁿ) λᵢ` written out (its nonvanishing,
  `Complex.schurDelta_lemma_3_4_2_const_ne_zero`, is Bertin's `λᵢ ≠ 0`). The exponent `n−i+1` is the one
  the recurrence forces — Bertin's printed `|uᵢ|²ⁿ/ωᵢⁿ` carries the same off-by-one noted for
  Lemma 3.2.1 c.

## Lemma 3.4.3 — the finite-algorithm dichotomy

Bertin's **Lemma 3.4.3**: if the generalised Schur algorithm for `F` is finite, then **either** `F` has
finite rank (`δₙ(F)` eventually `0`) **or** `F = A/B` is rational (`A, B ∈ ℂ[z]`) with `|A| > |B|` on
the unit circle and `δₙ(F) = λ bⁿ` (`λ ≠ 0`, `b < 0` — so the determinants never vanish and alternate
in sign).

* `Complex.SchurAlgorithmFinite` is the **opaque** hypothesis predicate ("the algorithm terminates",
  Definition 3.3.1 / Remark 3.3.1 — the sequence object is not yet formalised in this corpus).
* `Complex.finiteRank_or_rational_lemma_3_4_3` is the dichotomy, a `cited` axiom (`ref "Ber92"`).

## Lemma 3.4.4 — the Schur step is `𝓜_∞`-preserving and pole-count non-increasing

Bertin's **Lemma 3.4.4**: for `g ∈ 𝓜_∞` with `p` poles in `D(0,1)`, `G = taylorSeries g`, and `Gˡ` the
first Schur transform of `g`: i) `Gˡ` is the Taylor series of some `gˡ ∈ 𝓜_∞` with **at most `p`** poles;
ii) if `Gˡ` comes from transformation 4) or 5a), `gˡ` has **at most `p − 1`** poles.

* `Complex.poleCount g` is the number of poles of `g` in `D(0,1)` (`Set.ncard` of the non-analyticity
  set; the genuine count for `g ∈ 𝓜_∞`, where the set is finite).
* `Complex.IsFirstSchurTransform G Gˡ` / `Complex.IsReciprocalOrUnimodularStep G Gˡ` express that `Gˡ`
  is a first Schur step (transformation 3/4/5a), resp. one of the pole-reducing transformations 4)/5a),
  via the concrete step maps `schurTransform`, `genSchurReciprocalStep`, `genSchurUnimodularStep`
  (`BertinPisot.GeneralizedSchur`).
* `Complex.poleCount_firstSchurTransform_lemma_3_4_4` is the statement, a `cited` axiom (`ref "Ber92"`):
  `poleCount gˡ ≤ poleCount g`, dropping to `poleCount gˡ + 1 ≤ poleCount g` for transformations 4)/5a).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
  (Definition 3.4, Remark 3.4.1, Lemma 3.4.1.)
* [Pat72] Pathiaux, Martine. *Sur les multiples de polynômes irréductibles associés à certains nombres
  algébriques.* Séminaire Delange–Pisot–Poitou. Théorie des nombres **14**.1 (1972), 1–9.
  (Theorem 3.4.1 — the `𝓜_∞` Taylor-series characterisation.)
* [Boy77] Boyd, David W. *Pisot numbers and the width of meromorphic functions.* Privately circulated
  manuscript, 1977. (Theorem 3.4.2 — the meromorphic Szegő limit with the pole correction.)
-/

open Filter Topology Metric
open Polynomial

namespace Complex

/-- **Definition 3.4** (Bertin). The class `𝓜_∞`: the set of functions `f` meromorphic on the open
unit disk `D(0,1)` that (i) have **no pole at the origin** (`AnalyticAt ℂ f 0`), (ii) have only
**finitely many poles** in `D(0,1)` — the set of non-analyticity points inside the disk is finite —
and (iii) satisfy the boundary bound `limsup_{z → e^{iθ}, |z| < 1} |f(z)| ≤ 1` for every
`θ ∈ [0, 2π]`, encoded as: for every boundary point `w` (`|w| = 1`), the `limsup` of `‖f‖` along
`z → w` from inside the disk is `≤ 1` (in `EReal`, so a pole accumulating at the boundary gives
`⊤ ≰ 1`). This is the meromorphic generalisation of the Schur class `𝓜 = schurClass` (§3.2). -/
@[category API, AMS 30, ref "Ber92"]
def schurClassInfty : Set (ℂ → ℂ) :=
  { f | MeromorphicOn f (ball 0 1) ∧ AnalyticAt ℂ f 0 ∧
        {z ∈ ball (0 : ℂ) 1 | ¬ AnalyticAt ℂ f z}.Finite ∧
        ∀ w ∈ sphere (0 : ℂ) 1,
          Filter.limsup (fun z => (‖f z‖ : EReal)) (𝓝[ball 0 1] w) ≤ 1 }

/-- A function lies in `𝓜_∞` iff it is meromorphic on `D(0,1)`, analytic at `0`, has finitely many
poles in the disk, and its boundary `limsup ‖f‖` is `≤ 1` at every point of the unit circle. -/
@[category API, AMS 30, ref "Ber92", formal_uses schurClassInfty]
theorem mem_schurClassInfty {f : ℂ → ℂ} :
    f ∈ schurClassInfty ↔
      MeromorphicOn f (ball 0 1) ∧ AnalyticAt ℂ f 0 ∧
        {z ∈ ball (0 : ℂ) 1 | ¬ AnalyticAt ℂ f z}.Finite ∧
        ∀ w ∈ sphere (0 : ℂ) 1,
          Filter.limsup (fun z => (‖f z‖ : EReal)) (𝓝[ball 0 1] w) ≤ 1 := Iff.rfl

/-! ### Remark 3.4.1 — the Blaschke-quotient factorisation of `𝓜_∞`

Bertin's **Remark 3.4.1**: `f ∈ 𝓜_∞` iff `f = (P*/P)·h` with `h ∈ 𝓜`, `P ∈ ℂ[z]`, `P(0) ≠ 0` and all
zeros of `P` in `D(0,1)`. `P* = reciprocalC P` is the reciprocal polynomial of §3.1; `P*/P` is a finite
Blaschke product (unimodular on `|z| = 1`). The elementary, in-Mathlib heart — that `P*/P` has modulus
`1` on the unit circle — is **proved** here; the full factorisation is a `cited` axiom. -/

informal_result "meromorphic-blaschke-factorization"
  latex "Factorisation of meromorphic functions of bounded type on the unit disk D(0,1): a function f meromorphic on D(0,1), analytic at 0, with finitely many poles and limsup |f| ≤ 1 at every boundary point factors as f = (P*/P) h, where P ∈ C[z] is the polynomial whose zeros are the poles of f (so P(0) ≠ 0 and every zero lies in D(0,1)), P*(z) = z^{deg P} · conj(P(1/conj z)) is its conjugate-reciprocal polynomial — the finite Blaschke product P*/P is unimodular on |z| = 1, with poles the zeros of P inside D and zeros 1/conj(α) outside D — and h ∈ M is a Schur function (analytic and bounded by 1 on D(0,1)); conversely every such product lies in M_∞. The forward direction divides out the poles by the Blaschke quotient P*/P, which has modulus 1 on the boundary so transfers the boundary bound to h = f·P/P*, then applies the maximum modulus principle to the analytic function h."
  refs "Ber92"

/-- **Boundary modulus of `P*`** (the elementary heart of Remark 3.4.1). On the unit circle
`‖z‖ = 1` the reciprocal polynomial `P* = reciprocalC P` (§3.1, `BertinPisot.SchurAlgorithm`) has the
same modulus as `P`: `‖P*(z)‖ = ‖P(z)‖`. Indeed `P*(z) = z^{deg P} · conj(P(z))` there (since
`1/conj z = z` when `|z| = 1`), and `‖z‖ = 1`. -/
@[category API, AMS 30 12, ref "Ber92", formal_uses reciprocalC]
theorem norm_eval_reciprocalC (P : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(reciprocalC P).eval z‖ = ‖P.eval z‖ := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hns : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hcz : (starRingEnd ℂ) z = z⁻¹ := by
    have hmul : (starRingEnd ℂ) z * z = 1 := by rw [mul_comm, Complex.mul_conj, hns]; norm_num
    exact eq_inv_of_mul_eq_one_left hmul
  have hcomp : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext x; simp
  haveI : Invertible z := invertibleOfNonzero hz0
  have hinvz : (⅟z : ℂ) = z⁻¹ := invOf_eq_inv z
  have key := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z P
  rw [hinvz] at key
  have hP : ‖P.eval z‖ = ‖(P.reverse).eval z⁻¹‖ := by
    have hn := congrArg norm key
    rw [norm_mul, norm_pow, hz, one_pow, mul_one] at hn
    exact hn.symm
  rw [reciprocalC,
    show ((P.reverse).map (starRingEnd ℂ)).eval z = eval₂ (starRingEnd ℂ) z (P.reverse) from
      eval_map _ _,
    ← Complex.norm_conj (eval₂ (starRingEnd ℂ) z (P.reverse)), hom_eval₂, hcomp, hcz, hP]
  rfl

/-- The finite Blaschke quotient `P*/P` is **unimodular on the unit circle**: for `‖z‖ = 1` with
`P(z) ≠ 0`, `‖P*(z)/P(z)‖ = 1`. Immediate from `norm_eval_reciprocalC`. -/
@[category API, AMS 30 12, ref "Ber92", formal_uses reciprocalC norm_eval_reciprocalC]
theorem norm_eval_reciprocalC_div_eq_one (P : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ = 1)
    (hPz : P.eval z ≠ 0) : ‖(reciprocalC P).eval z / P.eval z‖ = 1 := by
  rw [norm_div, norm_eval_reciprocalC P hz, div_self (norm_ne_zero_iff.mpr hPz)]

/-- **Remark 3.4.1** (Bertin). A function `f` belongs to `𝓜_∞` **iff** it factors as `f = (P*/P)·h`
with `h ∈ 𝓜` (the Schur class), `P ∈ ℂ[z]`, `P(0) ≠ 0`, and all zeros of `P` in `D(0,1)` — `P*/P` the
finite Blaschke product `reciprocalC P / P` (`P*` the reciprocal polynomial of §3.1). The factorisation
identity is stated on the disk away from the poles (where `P(z) ≠ 0`), the natural domain on which `f`
is analytic; the poles of `f` in `D(0,1)` are exactly the zeros of `P`.

Recorded as a `cited` axiom (`ref "Ber92"`). The forward direction needs the factorisation of
bounded-type meromorphic functions through a finite Blaschke product together with the maximum-modulus
principle (the boundary bound transfers to `h = f·P/P*` because `‖P*/P‖ = 1` on `|z| = 1`,
`norm_eval_reciprocalC_div_eq_one`); the converse is the elementary check that such a product lies
in `𝓜_∞`. Neither the finite-Blaschke / inner-function theory nor this factorisation is in Mathlib
(the `informal_uses` edge `meromorphic-blaschke-factorization` names the pillar), so `#print axioms`
surfaces this axiom downstream — the same situation as Theorem 3.2.1 / Corollary 3.2.2 in
`BertinPisot.SchurClass`. -/
@[category research solved, AMS 30 12, ref "Ber92",
  formal_uses schurClassInfty schurClass reciprocalC,
  informal_uses "meromorphic-blaschke-factorization"]
axiom mem_schurClassInfty_iff_reciprocalC_mul {f : ℂ → ℂ} :
    f ∈ schurClassInfty ↔
      ∃ (P : Polynomial ℂ) (h : ℂ → ℂ),
        h ∈ schurClass ∧ P.eval 0 ≠ 0 ∧
        (∀ z, P.IsRoot z → z ∈ ball (0 : ℂ) 1) ∧
        ∀ z ∈ ball (0 : ℂ) 1, P.eval z ≠ 0 →
          f z = (reciprocalC P).eval z / P.eval z * h z

/-! ### Lemma 3.4.1 — the Schur-step polynomials `Eₗ, Sₗ` and the determinant recursion

For a step `F = Fⁱ ↦ G = Fⁱ⁺ˡ` of the generalised Schur algorithm there are polynomials `Eₗ, Sₗ` with
the properties a) i)–v) and the determinant recursion b). The **Schur-transform case** (`l = 1`) is
proved here in full; the **unimodular case** (`l = 2k + s`) has its degree bounds proved and reduces
otherwise to Lemma 3.3.1; the general b) is a `cited` axiom over the a)-data. Throughout, Bertin's
tilde `Ã(z) = zˡ Ā(1/z)` is `reciprocalAt l A` and `δₙ` is `schurDelta`. -/

informal_result "generalized-schur-step-determinant"
  latex "Determinant recursion for a step of the generalised Schur algorithm (Bertin, Lemma 3.4.1 b). If F = F^i and G = F^{i+l} are consecutive iterates (step length l ≥ 1) realised by polynomials E_l, S_l ∈ C[z] of degree ≤ l with G = (F E_l − S_l)/(Ẽ_l − F S̃_l), E_l Ẽ_l − S_l S̃_l = t_l z^l (t_l > 0 real), and F S̃_l − Ẽ_l = v_l z^l + ⋯ (v_l ≠ 0), where Ã(z) = z^l Ā(1/z), then the Schur determinants satisfy δ_n(F^i) = (|v_l|²/t_l^l)^{n+1} δ_{n−l}(F^{i+l}) for all n ≥ l. The proof iterates the single-step recurrence δ_n(F) = δ_0(F)^{n+1} δ_{n−1}(F^1) of Lemma 3.1.2 and, in the unimodular case, the convergent/determinant identities of Lemma 3.3.1; for l = 1 (the Schur transform) it reduces to δ_n(F^i) = (1 − |γ_0|²)^{n+1} δ_{n−1}(F^{i+1})."
  refs "Ber92"

/-- `reciprocalAt 1 (1) = z` (`Ẽ₁` for `E₁ = 1`): Bertin's tilde of the constant `1` at rank `1`. -/
@[category API, AMS 12, ref "Ber92", formal_uses reciprocalAt]
theorem reciprocalAt_one_one : reciprocalAt 1 (1 : Polynomial ℂ) = X := by
  rw [reciprocalAt]; ext n; rw [coeff_map, coeff_reflect]
  rcases n with _ | _ | n <;> simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]

/-- `reciprocalAt 1 (C γ) = γ̄ z` (`S̃₁` for `S₁ = C γ`): Bertin's tilde of a constant at rank `1`. -/
@[category API, AMS 12, ref "Ber92", formal_uses reciprocalAt]
theorem reciprocalAt_one_C (γ : ℂ) : reciprocalAt 1 (C γ) = C (starRingEnd ℂ γ) * X := by
  rw [reciprocalAt]; ext n; rw [coeff_map, coeff_reflect]
  rcases n with _ | _ | n <;> simp [Polynomial.revAt, Polynomial.coeff_C]

/-- **Lemma 3.4.1 b)** (Bertin), the **determinant recursion**, as a `cited` axiom over the a)-data.
Given a step `F ↦ G` of the generalised Schur algorithm (`l ≥ 1`) realised by polynomials `Eₗ, Sₗ` of
degree `≤ l` with ii) `G·(Ẽₗ − F S̃ₗ) = F Eₗ − Sₗ`, iii) `Eₗ Ẽₗ − Sₗ S̃ₗ = tₗ zˡ` (`tₗ > 0`),
iv) leading coefficient `coeff l (F S̃ₗ − Ẽₗ) = vₗ ≠ 0`, and v) `ord(F Eₗ − Sₗ) ≥ l` (`Ã = reciprocalAt l A`),
the Schur determinants satisfy `δₙ(F) = (|vₗ|²/tₗˡ)^{n+1} δₙ₋ₗ(G)` for all `n ≥ l`. Recorded as a
`cited` axiom (`ref "Ber92"`); its proof iterates `schurDelta_recurrence` (Lemma 3.1.2) and, for a
unimodular step, the convergent identities of Lemma 3.3.1 — not formalised here. The Schur-transform
case (`schurDelta_schurStep` below) is a fully proved instance: there `tₗ = 1 − |γ₀|²`, `vₗ = |γ₀|² − 1`,
so `(|vₗ|²/tₗ¹)^{n+1} = (1 − |γ₀|²)^{n+1}`. -/
@[category research solved, AMS 30 15 13, ref "Ber92",
  formal_uses schurDelta reciprocalAt schurTransform,
  informal_uses "generalized-schur-step-determinant"]
axiom schurDelta_lemma_3_4_1 (F G : PowerSeries ℂ) (l : ℕ) (hl : 1 ≤ l)
    (E S : Polynomial ℂ) (t : ℝ) (ht : 0 < t) (v : ℂ) (hv : v ≠ 0)
    (hdeg : E.natDegree ≤ l ∧ S.natDegree ≤ l)
    (hstep : G * ((reciprocalAt l E : PowerSeries ℂ) - F * (reciprocalAt l S : PowerSeries ℂ))
        = (F * E - S : PowerSeries ℂ))
    (hiii : E * reciprocalAt l E - S * reciprocalAt l S = C (t : ℂ) * X ^ l)
    (hiv : PowerSeries.coeff l
        ((F * (reciprocalAt l S : PowerSeries ℂ)) - (reciprocalAt l E : PowerSeries ℂ)) = v)
    (hord : (↑l : ℕ∞) ≤ (F * E - S : PowerSeries ℂ).order) :
    ∀ n, l ≤ n →
      schurDelta F n = ((Complex.normSq v / t ^ l : ℝ) : ℂ) ^ (n + 1) * schurDelta G (n - l)

/-! #### Proof case 2 — the Schur transform (`l = 1`, `E₁ = 1`, `S₁ = C γ₀`), proved in full -/

/-- **Lemma 3.4.1 a) ii), Schur-transform case.** With `E₁ = 1`, `S₁ = C γ₀` (`γ₀ = F(0)`), the
successor `G = schurTransform F` satisfies the fractional-linear relation
`G·(Ẽ₁ − F S̃₁) = F E₁ − S₁`, i.e. `F¹·(z − γ̄₀ z F) = F − γ₀`. Proved off `schurTransform_spec`
(needs `|γ₀| ≠ 1`). -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses schurTransform reciprocalAt schurTransform_spec reciprocalAt_one_one reciprocalAt_one_C]
theorem schurStep_relation (F : PowerSeries ℂ)
    (hγ : Complex.normSq (PowerSeries.constantCoeff F) ≠ 1) :
    schurTransform F * ((reciprocalAt 1 (1 : Polynomial ℂ) : PowerSeries ℂ)
        - F * (reciprocalAt 1 (C (PowerSeries.constantCoeff F)) : PowerSeries ℂ))
      = (F * (1 : Polynomial ℂ) - (C (PowerSeries.constantCoeff F) : Polynomial ℂ) :
          PowerSeries ℂ) := by
  rw [reciprocalAt_one_one, reciprocalAt_one_C]
  push_cast [Polynomial.coe_C, Polynomial.coe_X]
  linear_combination schurTransform_spec F hγ

/-- **Lemma 3.4.1 a) iii), Schur-transform case.** `E₁ Ẽ₁ − S₁ S̃₁ = t₁ z` with `t₁ = 1 − γ₀γ̄₀`
(`= 1 − |γ₀|²`): `1·z − γ₀·(γ̄₀ z) = (1 − γ₀γ̄₀) z`. -/
@[category API, AMS 12 30, ref "Ber92", formal_uses reciprocalAt reciprocalAt_one_one reciprocalAt_one_C]
theorem schurStep_pseudonorm (γ : ℂ) :
    (1 : Polynomial ℂ) * reciprocalAt 1 1 - C γ * reciprocalAt 1 (C γ)
      = C (1 - γ * starRingEnd ℂ γ) * X := by
  rw [reciprocalAt_one_one, reciprocalAt_one_C, map_sub, map_one, map_mul]; ring

/-- The pseudo-norm `t₁ = 1 − |γ₀|²` of iii) is **positive** when `|γ₀| < 1` (Schur step is genuine). -/
@[category API, AMS 30, ref "Ber92"]
theorem schurStep_t_pos {γ : ℂ} (hγ : Complex.normSq γ < 1) : (0 : ℝ) < 1 - Complex.normSq γ := by
  linarith

/-- **Lemma 3.4.1 a) iv), Schur-transform case.** The leading coefficient of `F S̃₁ − Ẽ₁ = vₗ z + ⋯`
is `v₁ = |γ₀|² − 1`: `coeff 1 (F·γ̄₀ z − z) = γ₀γ̄₀ − 1`. -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses reciprocalAt reciprocalAt_one_one reciprocalAt_one_C]
theorem schurStep_leadCoeff (F : PowerSeries ℂ) :
    PowerSeries.coeff 1 ((F * (reciprocalAt 1 (C (PowerSeries.constantCoeff F)) : PowerSeries ℂ))
        - (reciprocalAt 1 (1 : Polynomial ℂ) : PowerSeries ℂ))
      = (Complex.normSq (PowerSeries.constantCoeff F) : ℂ) - 1 := by
  rw [reciprocalAt_one_one, reciprocalAt_one_C]
  push_cast [Polynomial.coe_C, Polynomial.coe_X]
  rw [map_sub, show F * (PowerSeries.C (starRingEnd ℂ (PowerSeries.constantCoeff F)) * PowerSeries.X)
        = PowerSeries.X * (PowerSeries.C (starRingEnd ℂ (PowerSeries.constantCoeff F)) * F) by ring,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    PowerSeries.constantCoeff_C, PowerSeries.coeff_one_X, mul_comm, Complex.mul_conj]

/-- The leading coefficient `v₁ = |γ₀|² − 1` of iv) is **nonzero** when `|γ₀| < 1`. -/
@[category API, AMS 30, ref "Ber92"]
theorem schurStep_v_ne_zero {γ : ℂ} (hγ : Complex.normSq γ < 1) :
    (Complex.normSq γ : ℂ) - 1 ≠ 0 := by
  rw [sub_ne_zero]; exact fun h => ne_of_lt hγ (by exact_mod_cast h)

/-- **Lemma 3.4.1 a) v), Schur-transform case.** `ord(F E₁ − S₁) = ord(F − γ₀) ≥ 1`, since `F − γ₀`
has zero constant term. -/
@[category research solved, AMS 30 13, ref "Ber92"]
theorem schurStep_order (F : PowerSeries ℂ) :
    (1 : ℕ∞) ≤ (F * (1 : Polynomial ℂ) - (C (PowerSeries.constantCoeff F) : Polynomial ℂ) :
      PowerSeries ℂ).order := by
  push_cast [Polynomial.coe_C, Polynomial.coe_one]
  rw [mul_one]
  apply PowerSeries.le_order
  intro i hi
  have hi' : i < 1 := by exact_mod_cast hi
  obtain rfl : i = 0 := by omega
  rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_C, sub_self]

/-- **Lemma 3.4.1 b), Schur-transform case** (proved). For the Schur transform `F¹ = schurTransform F`
(step `l = 1`, `γ₀ = F(0)`, `|γ₀| < 1`), the determinant recursion is
`δₙ(F) = (1 − |γ₀|²)^{n+1} δₙ₋₁(F¹)` for `n ≥ 1` — exactly `schurDelta_recurrence` (Lemma 3.1.2). This
is the proved instance of the general `schurDelta_lemma_3_4_1`: there `t₁ = 1 − |γ₀|²`,
`v₁ = |γ₀|² − 1`, so `(|v₁|²/t₁¹)^{n+1} = (1 − |γ₀|²)^{n+1}`. -/
@[category research solved, AMS 30 15 13, ref "Ber92",
  formal_uses schurDelta schurTransform schurDelta_recurrence schurDelta_zero]
theorem schurDelta_schurStep (F : PowerSeries ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hγ : Complex.normSq (PowerSeries.coeff 0 F) < 1) :
    schurDelta F n = (1 - (Complex.normSq (PowerSeries.coeff 0 F) : ℂ)) ^ (n + 1)
      * schurDelta (schurTransform F) (n - 1) := by
  have hne : Complex.normSq (PowerSeries.constantCoeff F) ≠ 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact ne_of_lt hγ
  rw [schurDelta_recurrence F n hn hne, schurDelta_zero]

/-! #### Proof case 1 — a unimodular step (`l = 2k + s`): the degree bounds i) -/

/-- **Lemma 3.4.1 a) i), unimodular case** for `Eₗ = zˢ(Q − zᵏ)`: `d°Eₗ ≤ 2k + s` whenever the
numerator `Q` (from Lemma 3.3.1) has `d°Q ≤ 2k`. -/
@[category API, AMS 12, ref "Ber92"]
theorem unimodularStep_natDegree_E (Q : Polynomial ℂ) (k s : ℕ) (hQ : Q.natDegree ≤ 2 * k) :
    (X ^ s * (Q - X ^ k)).natDegree ≤ 2 * k + s := by
  calc (X ^ s * (Q - X ^ k)).natDegree
      ≤ (X ^ s).natDegree + (Q - X ^ k).natDegree := natDegree_mul_le
    _ ≤ s + 2 * k := by
        gcongr
        · simp
        · exact (natDegree_sub_le _ _).trans (by simp; omega)
    _ = 2 * k + s := by ring

/-- **Lemma 3.4.1 a) i), unimodular case** for `Sₗ = zˢ γ₀ Q`: `d°Sₗ ≤ 2k + s` whenever `d°Q ≤ 2k`. -/
@[category API, AMS 12, ref "Ber92"]
theorem unimodularStep_natDegree_S (Q : Polynomial ℂ) (γ : ℂ) (k s : ℕ) (hQ : Q.natDegree ≤ 2 * k) :
    (X ^ s * (C γ * Q)).natDegree ≤ 2 * k + s := by
  calc (X ^ s * (C γ * Q)).natDegree
      ≤ (X ^ s).natDegree + (C γ * Q).natDegree := natDegree_mul_le
    _ ≤ s + 2 * k := by
        gcongr
        · simp
        · exact (natDegree_C_mul_le _ _).trans hQ
    _ = 2 * k + s := by ring

/-! ### Lemma 3.4.2 — convergent representation of `F` via `Fⁱ` and the determinant formula

Bertin's **Lemma 3.4.2** (convergent companion of Lemma 3.4.1): a) the `Fⁱ`-form Schur–Wall convergents
`Aᵢ, Qᵢ`; b) the determinant formula `δₙ(F) = (|uᵢ|²ⁿ/ωᵢⁿ) λᵢ δₙ₋ᵢ(Fⁱ)`. Part a) is a `cited` axiom;
part b) is **proved** as the iterated determinant formula `schurDelta_add_eq_iterate_prod` (Lemma 3.2.1 c)
with offset `n − i`. Bertin's tilde `Ã = reciprocalAt i A`. -/

/-- **Lemma 3.4.2 a)** (Bertin). For `F ∈ ℂ⟦z⟧` with `δ₀(F), …, δᵢ(F)` nonzero (so
`Fⁱ = schurTransform^[i] F` is defined), there are convergent polynomials `Aᵢ, Qᵢ ∈ ℂ[z]`, a leading
coefficient `uᵢ`, and a Wronskian constant `ωᵢ` with i) `d°Aᵢ, d°Qᵢ ≤ i`,
ii) `F·(Qᵢ + Ãᵢ Fⁱ) = Aᵢ + Q̃ᵢ Fⁱ` (the continued-fraction representation
`F = (Aᵢ + Q̃ᵢ Fⁱ)/(Qᵢ + Ãᵢ Fⁱ)`, `Ã = reciprocalAt i`), iii) `coeff i (F Ãᵢ − Q̃ᵢ) = uᵢ ≠ 0`,
iv) `ord(F Qᵢ − Aᵢ) ≥ i`, v) `Qᵢ Q̃ᵢ − Aᵢ Ãᵢ = ωᵢ zⁱ` with `ωᵢ > 0`. The `Fⁱ`-form companion of the
§3.2 `exists_convergents` (Lemma 3.2.1 b); recorded as a `cited` axiom (`ref "Ber92"`), the Schur–Wall
convergent construction not being formalised. -/
@[category research solved, AMS 12 15 30 13, ref "Ber92",
  formal_uses schurDelta schurTransform reciprocalAt]
axiom exists_convergents_lemma_3_4_2 (F : PowerSeries ℂ) (i : ℕ)
    (hδ : ∀ j ≤ i, schurDelta F j ≠ 0) :
    ∃ (A Q : Polynomial ℂ) (u : ℂ) (ω : ℝ),
      (A.natDegree ≤ i ∧ Q.natDegree ≤ i) ∧
      F * ((Q : PowerSeries ℂ) + (reciprocalAt i A : PowerSeries ℂ) * schurTransform^[i] F)
          = (A : PowerSeries ℂ) + (reciprocalAt i Q : PowerSeries ℂ) * schurTransform^[i] F ∧
      u ≠ 0 ∧ PowerSeries.coeff i ((F * (reciprocalAt i A : PowerSeries ℂ))
          - (reciprocalAt i Q : PowerSeries ℂ)) = u ∧
      (↑i : ℕ∞) ≤ (F * (Q : PowerSeries ℂ) - (A : PowerSeries ℂ)).order ∧
      0 < ω ∧ Q * reciprocalAt i Q - A * reciprocalAt i A = C (ω : ℂ) * X ^ i

/-- **Lemma 3.4.2 b)** (Bertin), the **determinant formula** (proved). For `F` with `δ₀(F), …, δᵢ(F)`
nonzero and `n ≥ i`, `δₙ(F) = (∏_{j<i} δ₀(Fʲ)^{(i−j)+(n−i+1)}) · δₙ₋ᵢ(Fⁱ)`
(`Fⁱ = schurTransform^[i] F`). This is the iterated determinant formula `schurDelta_add_eq_iterate_prod`
(Lemma 3.2.1 c) with offset `k = n − i`. The Schur-parameter product is Bertin's constant
`(|uᵢ|²ⁿ/ωᵢⁿ) λᵢ` written out — nonzero by `schurDelta_lemma_3_4_2_const_ne_zero` (Bertin's `λᵢ ≠ 0`);
the exponent `n−i+1` is the one the recurrence forces (the off-by-one noted for Lemma 3.2.1 c). -/
@[category research solved, AMS 15 30 13, ref "Ber92",
  formal_uses schurDelta schurTransform schurDelta_add_eq_iterate_prod]
theorem schurDelta_lemma_3_4_2 (F : PowerSeries ℂ) (i : ℕ)
    (hδ : ∀ j ≤ i, schurDelta F j ≠ 0) (n : ℕ) (hn : i ≤ n) :
    schurDelta F n
      = (∏ j ∈ Finset.range i, schurDelta (schurTransform^[j] F) 0 ^ ((i - j) + (n - i + 1)))
          * schurDelta (schurTransform^[i] F) (n - i) := by
  have h := schurDelta_add_eq_iterate_prod F i hδ (n - i)
  rwa [Nat.add_sub_cancel' hn] at h

/-- The proportionality constant of `schurDelta_lemma_3_4_2` — Bertin's `λᵢ` factor — is **nonzero**
(each `δ₀(Fʲ) ≠ 0` for `j < i`, from `schurDelta_zero_iterate_ne_zero`). -/
@[category API, AMS 15 30, ref "Ber92",
  formal_uses schurDelta schurTransform schurDelta_zero_iterate_ne_zero]
theorem schurDelta_lemma_3_4_2_const_ne_zero (F : PowerSeries ℂ) (i : ℕ)
    (hδ : ∀ j ≤ i, schurDelta F j ≠ 0) (n : ℕ) :
    (∏ j ∈ Finset.range i, schurDelta (schurTransform^[j] F) 0 ^ ((i - j) + (n - i + 1))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (schurDelta_zero_iterate_ne_zero F i hδ j (le_of_lt (Finset.mem_range.mp hj)))

/-! ### Lemma 3.4.3 — the finite-algorithm dichotomy -/

/-- **Abstract "the generalised Schur algorithm for `F` terminates"** (Bertin, Definition 3.3.1 /
Remark 3.3.1): the algorithm sequence `(Fⁿ)` reaches a stopping configuration (a constant of modulus
`≥ 1`, cases 1–2, or a unimodular constant, case 5b) after finitely many steps. The sequence object
itself is recorded only in prose in `BertinPisot.GeneralizedSchur`, so this hypothesis predicate is
left **opaque**, to be connected to the explicit algorithm once that is built; it is the hypothesis of
Lemma 3.4.3. -/
@[category API, AMS 30 13, ref "Ber92"]
opaque SchurAlgorithmFinite : PowerSeries ℂ → Prop

/-- **Lemma 3.4.3** (Bertin). If `F ∈ ℂ⟦z⟧` and the generalised Schur algorithm for `F` is finite
(`SchurAlgorithmFinite F`), then **either** `F` has **finite rank** — its Schur determinants eventually
vanish, `∃ N, ∀ n ≥ N, δₙ(F) = 0` (the non-`HasIndefiniteRank` case) — **or** `F = A/B` is rational
with `A, B ∈ ℂ[z]` (`B ≠ 0`, `F·B = A`), `|A(z)| > |B(z)|` on `|z| = 1`, and `δₙ(F) = λ bⁿ` with
`λ ≠ 0` and `b < 0` (so the determinants never vanish and alternate in sign).

Recorded as a `cited` axiom (`ref "Ber92"`); its proof rests on the generalised Schur algorithm
(Definition 3.3.1) and Lemmas 3.4.1–3.4.2, and the hypothesis `SchurAlgorithmFinite` is the opaque
"algorithm terminates" predicate pending a full formalisation of the algorithm sequence. -/
@[category research solved, AMS 30 13 12, ref "Ber92",
  formal_uses schurDelta SchurAlgorithmFinite]
axiom finiteRank_or_rational_lemma_3_4_3 (F : PowerSeries ℂ) (hfin : SchurAlgorithmFinite F) :
    (∃ N, ∀ n, N ≤ n → schurDelta F n = 0)
    ∨ (∃ (A B : Polynomial ℂ) (lam : ℂ) (b : ℝ),
        B ≠ 0 ∧ F * (B : PowerSeries ℂ) = (A : PowerSeries ℂ) ∧
        (∀ z : ℂ, ‖z‖ = 1 → ‖B.eval z‖ < ‖A.eval z‖) ∧
        lam ≠ 0 ∧ b < 0 ∧ ∀ n, schurDelta F n = lam * (b : ℂ) ^ n)

/-! ### Lemma 3.4.4 — the Schur step is `𝓜_∞`-preserving and pole-count non-increasing -/

/-- The **number of poles** of `g` in `D(0,1)`: the `Set.ncard` of the non-analyticity set
`{z ∈ ball 0 1 | ¬ AnalyticAt ℂ g z}`. For `g ∈ 𝓜_∞` this set is finite, so `poleCount g` is the
genuine pole count (Bertin's `p`). -/
@[category API, AMS 30, ref "Ber92"]
noncomputable def poleCount (g : ℂ → ℂ) : ℕ :=
  {z ∈ ball (0 : ℂ) 1 | ¬ AnalyticAt ℂ g z}.ncard

/-- `Gˡ` is obtained from `G` by one of the **pole-reducing transformations** of the generalised Schur
algorithm — transformation 4) (`genSchurReciprocalStep`) or 5a) (`genSchurUnimodularStep`),
Definition 3.3.1. -/
@[category API, AMS 30 13, ref "Ber92",
  formal_uses genSchurReciprocalStep genSchurUnimodularStep]
def IsReciprocalOrUnimodularStep (G Gl : PowerSeries ℂ) : Prop :=
  (∃ k, Gl = genSchurReciprocalStep k G) ∨ (∃ k s cps, Gl = genSchurUnimodularStep k s cps G)

/-- `Gˡ` is a **first Schur transform** of `G`: the result of one algorithm step — transformation 3)
(`schurTransform`), 4), or 5a). -/
@[category API, AMS 30 13, ref "Ber92",
  formal_uses schurTransform IsReciprocalOrUnimodularStep]
def IsFirstSchurTransform (G Gl : PowerSeries ℂ) : Prop :=
  Gl = schurTransform G ∨ IsReciprocalOrUnimodularStep G Gl

/-- **Lemma 3.4.4** (Bertin). Let `g ∈ 𝓜_∞` have `p = poleCount g` poles in `D(0,1)`,
`G = taylorSeries g`, and `Gˡ` a first Schur transform of `g`. Then **i)** `Gˡ` is the Taylor series at
`0` of some `gˡ ∈ 𝓜_∞` with at most `p` poles (`poleCount gˡ ≤ poleCount g`); and **ii)** if `Gˡ` is
obtained by transformation 4) or 5a) (`IsReciprocalOrUnimodularStep`), then `gˡ` has at most `p − 1`
poles (`poleCount gˡ + 1 ≤ poleCount g`). Recorded as a `cited` axiom (`ref "Ber92"`); the proof tracks
the pole count through the algorithm step (the unimodular transformations 4)/5a) divide out a boundary
factor, removing a pole) and is not formalised here. -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses schurClassInfty taylorSeries poleCount IsFirstSchurTransform IsReciprocalOrUnimodularStep]
axiom poleCount_firstSchurTransform_lemma_3_4_4 (g : ℂ → ℂ) (hg : g ∈ schurClassInfty)
    (Gl : PowerSeries ℂ) (hGl : IsFirstSchurTransform (taylorSeries g) Gl) :
    ∃ gl : ℂ → ℂ, gl ∈ schurClassInfty ∧ taylorSeries gl = Gl ∧
      poleCount gl ≤ poleCount g ∧
      (IsReciprocalOrUnimodularStep (taylorSeries g) Gl → poleCount gl + 1 ≤ poleCount g)

/-! ### Lemma 3.4.5 — a no-finite-rank `𝓜_∞`-function reduces to the Schur class `𝓜` -/

/-- `G` is an **`n`-fold first Schur transform** of `F`: there is a length-`n` chain
`F = seq 0, seq 1, …, seq n = G` whose every step `seq i ↝ seq (i+1)` is a first Schur transform
(transformation 3), 4), or 5a); `IsFirstSchurTransform`). This is the explicit, count-carrying form of
the iterated generalised Schur algorithm — Bertin's passage from `F` to its `n`-th transform `Fⁿ`
(the sequence object of Remark 3.3.1, built here from the *concrete* one-step relation rather than the
opaque `SchurAlgorithmFinite`). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses IsFirstSchurTransform]
def IsIteratedFirstSchurTransform (F G : PowerSeries ℂ) (n : ℕ) : Prop :=
  ∃ seq : ℕ → PowerSeries ℂ, seq 0 = F ∧ seq n = G ∧
    ∀ i, i < n → IsFirstSchurTransform (seq i) (seq (i + 1))

/-- **Lemma 3.4.5** (Bertin). Let `f ∈ 𝓜_∞` have **no finite rank** (`HasIndefiniteRank f`) and let
`F = taylorSeries f`. Then there is an `n₀ ∈ ℕ` such that the Schur transform `Fⁿ⁰` of `F` exists (`F`
reaches it by an `n₀`-fold first Schur transform, `IsIteratedFirstSchurTransform`) and `Fⁿ⁰` is the
Taylor series at `0` of a function `g` belonging to the **Schur class `𝓜`** and again **with no finite
rank** (`HasIndefiniteRank g`).

**Proof** (Bertin). By Lemma 3.4.3 the generalised algorithm for `F` does not stop. By Lemma 3.4.4 the
pole-reducing transformations 4)/5a) are used only finitely often — each strictly drops the pole count
`poleCount f`, a fixed finite integer, and `ℕ` is well-ordered — so past some `n₀` only transformation
3) is used: from `Fⁿ⁰` on the algorithm is the basic Schur step, whence `Fⁿ⁰` is the Taylor series of a
Schur-class function `g`, of indefinite rank since the algorithm never terminates.

Recorded as a `cited` axiom (`ref "Ber92"`): mathematically a one-paragraph well-ordering on
`poleCount`, but it runs over the generalised-algorithm *sequence*, which is recorded only in prose
(Remark 3.3.1; `SchurAlgorithmFinite` is opaque), so it is not formalised here. The iterate is encoded
through the concrete `IsIteratedFirstSchurTransform` chain (built on `IsFirstSchurTransform`), keeping
the statement off the opaque predicate. -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses schurClassInfty schurClass taylorSeries HasIndefiniteRank IsIteratedFirstSchurTransform]
axiom exists_iterate_mem_schurClass_lemma_3_4_5
    (f : ℂ → ℂ) (hf : f ∈ schurClassInfty) (hrank : HasIndefiniteRank f) :
    ∃ (n₀ : ℕ) (g : ℂ → ℂ),
      IsIteratedFirstSchurTransform (taylorSeries f) (taylorSeries g) n₀ ∧
      g ∈ schurClass ∧ HasIndefiniteRank g

/-! ### Lemma 3.4.6 — `δₙ(F) < 0` for all `n` forces a one-pole `𝓜_∞`-function -/

/-- **Lemma 3.4.6** (Bertin). If `F ∈ ℂ⟦z⟧` has **all** Schur determinants negative — `δₙ(F) < 0` for
every `n` (the negative-real condition `(δₙ F).re < 0 ∧ (δₙ F).im = 0`, mirroring the positivity
encoding of Theorem 3.2.1) — then `F` is the Taylor series at `0` of a function `f ∈ 𝓜_∞` having
**exactly one pole** in `D(0,1)` (`poleCount f = 1`).

**Proof** (Bertin). Write `F = Σ aᵢ zⁱ`. From `δ₀(F) = 1 − |a₀|² < 0` we get `|a₀| > 1`; from
`δ₁(F) = (1 − |a₀|²)² − |a₁|² < 0`, `a₁ ≠ 0`, so the Schur transform `F¹ = z(1 − ā₀F)/(F − a₀)` is
defined. By Lemma 3.4.2, `δₙ(F) = hⁿ λ δₙ₋₁(F¹)` with `h > 0`, and `δ₀(F¹) = 1 − |1 − a₀ā₀|²/|a₁|² > 0`
forces `λ < 0`; hence `δₙ(F¹) > 0` for every `n`, so by **Theorem 3.2.1** `F¹` is the Taylor series of
some `f₁ ∈ 𝓜`. Setting `f = (a₀ f₁ + z)/(f₁ + ā₀z)` (equivalently `F = (a₀F¹ + z)/(F¹ + ā₀z)`),
**Rouché's theorem** applied to the denominator `f₁ + ā₀z` shows `f` has at most one pole in `D(0,1)`,
and `|a₀| > 1` gives `limsup_{z → e^{iθ}} |f(z)| ≤ 1`, so `f ∈ 𝓜_∞`. Finally `δₙ(F) < 0` excludes the
no-pole (`𝓜`) branch of **Theorem 3.2.1**, so `f` has *exactly* one pole.

Recorded as a `cited` axiom (`ref "Ber92"`): the algebraic `δ`-reductions (`|a₀| > 1`, `a₁ ≠ 0`) are
easy, but the analytic core — the meromorphic Möbius construction `f = (a₀f₁ + z)/(f₁ + ā₀z)`,
pole counting by **Rouché's theorem** (`rouche-theorem`; Mathlib has only Cauchy-integral / Jensen /
Nevanlinna machinery, no usable Rouché / argument principle), the boundary `limsup` estimate, and the
matching `taylorSeries f = F` — is well beyond a screenshot increment and is not formalised here. -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses schurDelta schurClassInfty taylorSeries poleCount,
  informal_uses "rouche-theorem"]
axiom exists_mem_schurClassInfty_poleCount_one_lemma_3_4_6 (F : PowerSeries ℂ)
    (hF : ∀ n, (schurDelta F n).re < 0 ∧ (schurDelta F n).im = 0) :
    ∃ f : ℂ → ℂ, f ∈ schurClassInfty ∧ taylorSeries f = F ∧ poleCount f = 1

/-! ### Theorem 3.4.1 — the `𝓜_∞` characterisation by Schur-determinant signs (Pathiaux) -/

/-- `F` is the **Taylor series at `0` of a function in `𝓜_∞`**: some `f ∈ 𝓜_∞` (meromorphic on
`D(0,1)`, analytic at `0`, finitely many poles, boundary-bounded by `1`) has `F` as its Taylor series,
`taylorSeries f = F`. The meromorphic analogue of `IsTaylorSeriesOfSchurClass` (Theorem 3.2.1). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses schurClassInfty taylorSeries]
def IsTaylorSeriesOfSchurClassInfty (F : PowerSeries ℂ) : Prop :=
  ∃ f : ℂ → ℂ, f ∈ schurClassInfty ∧ taylorSeries f = F

/-- **Theorem 3.4.1** (Pathiaux [Pat72]; Bertin [Ber92], §3.4). A power series `F ∈ ℂ⟦z⟧` is the Taylor
series at `0` of a function in `𝓜_∞` **iff** there is a threshold `n₀` past which the Schur determinants
are *eventually sign-coherent*: **either** `δₙ(F)·δₙ₊₁(F) > 0` for all `n ≥ n₀` (consecutive
determinants share a sign — the no-finite-rank / genuine-pole case), **or** `δₙ(F) = 0` for all
`n ≥ n₀` (the finite-rank case). `δₙ(F)·δₙ₊₁(F) > 0` is the positive-real condition
`0 < (δₙ(F)·δₙ₊₁(F)).re ∧ (δₙ(F)·δₙ₊₁(F)).im = 0`, mirroring the encoding of Theorem 3.2.1.

**Proof** (Bertin). *(⟹)* If `f ∈ 𝓜_∞` has finite rank then `δₙ(F) = 0` eventually by definition. If `f`
has **no** finite rank, Lemma 3.4.5 (`exists_iterate_mem_schurClass_lemma_3_4_5`) gives `n₀` with
`Fⁿ⁰` the Taylor series of some `g ∈ 𝓜` of indefinite rank, so `δₙ(Fⁿ⁰) > 0` for all `n`
(Theorem 3.2.1 / Corollary 3.2.1); Lemma 3.4.2 then gives `δ_{n+n₀}(F) = ρⁿλ δₙ(Fⁿ⁰)` (`ρ > 0`,
`λ ≠ 0`), whence `δ_{n+n₀}(F)·δ_{n+1+n₀}(F) = ρ^{2n+1}λ² δₙ(Fⁿ⁰)δₙ₊₁(Fⁿ⁰) > 0`. *(⟸)* From the
sign-coherent branch, Lemma 3.4.3 shows the algorithm does not stop; picking `i ≥ n₀`, Lemma 3.4.2 gives
`δₙ(Fⁱ) > 0` for all `n`, so by Lemma 3.4.6 and Theorem 3.2.1 `Fⁱ` is the Taylor series of some `fᵢ ∈ 𝓜_∞`
with at most one pole; reconstructing `f = (Aᵢ + Q̃ᵢ fᵢ)/(Qᵢ + Ãᵢ fᵢ)` (Lemma 3.4.2's convergents) and
arguing as in Lemma 3.4.4 places `f ∈ 𝓜_∞`.

Recorded as a `cited` axiom (`ref "Pat72" "Ber92"`). The result is **attempted**, not assumed: the
finite-rank branch of `(⟹)` is mechanical — `¬ HasIndefiniteRank f` unfolds to exactly the `δₙ(F) = 0`
disjunct (`obtain ⟨N, hN⟩ := not_not.mp hrank; exact ⟨N, Or.inr hN⟩`). The other three quarters are
blocked on infrastructure that is itself only `cited`: `(⟹)` no-finite-rank needs Lemma 3.4.2's
determinant proportionality across the **generalised** iterate `Fⁿ⁰` (our `schurDelta_lemma_3_4_2` is the
*pure-Schur* `schurTransform^[i]` specialisation, whose step-count vs. degree index shift does not
transfer), and `(⟸)` needs the meromorphic Möbius reconstruction `f = (Aᵢ + Q̃ᵢfᵢ)/(Qᵢ + Ãᵢfᵢ)` and its
`𝓜_∞`-membership (the same Rouché / boundary analysis cited in Lemma 3.4.6). -/
@[category research solved, AMS 30 13, ref "Pat72" "Ber92",
  formal_uses schurDelta IsTaylorSeriesOfSchurClassInfty schurClassInfty taylorSeries]
axiom isTaylorSeriesOfSchurClassInfty_iff (F : PowerSeries ℂ) :
    IsTaylorSeriesOfSchurClassInfty F ↔
      ∃ n₀ : ℕ,
        (∀ n, n₀ ≤ n → 0 < (schurDelta F n * schurDelta F (n + 1)).re ∧
            (schurDelta F n * schurDelta F (n + 1)).im = 0) ∨
        (∀ n, n₀ ≤ n → schurDelta F n = 0)

/-! ### Notation — the Schur determinants `δₙ(f)` of an analytic function

Bertin (§3.4): for `f` analytic in a neighbourhood of `0`, set `δₙ(f) := δₙ(F)` for every `n ∈ ℕ`,
where `F = taylorSeries f` is the Taylor series of `f` at `0`.

This is already the corpus convention — there is **no separate symbol**: `δₙ(f)` is written
`schurDelta (taylorSeries f) n`. The `taylorSeries` bridge lives in `BertinPisot.SchurClass` (§3.2,
introduced alongside `HasIndefiniteRank`, whose definition is precisely "the `δₙ(f) = schurDelta
(taylorSeries f) n` do not eventually vanish"), and the same composition underlies
`IsTaylorSeriesOfSchurClassInfty` and Theorem 3.4.1 above. Recorded here for Bertin's §3.4 placement; no
new declaration is needed. -/

/-! ### Corollary 3.4.1 — the ratio `δₙ₊₁(f)/δₙ(f)` is eventually positive and decreasing -/

/-- For `f ∈ 𝓜_∞` with **no finite rank**, the Schur determinants `δₙ(f)` are **eventually nonzero**:
some `n₀` has `δₙ(f) ≠ 0` for all `n ≥ n₀`. This is the *"defined"* part of Corollary 3.4.1, **proved**
here from Theorem 3.4.1: `f ∈ 𝓜_∞` puts `taylorSeries f` in the sign-coherent dichotomy
(`isTaylorSeriesOfSchurClassInfty_iff`), no finite rank rules out the `δₙ = 0` branch, and the surviving
`δₙ(f)·δₙ₊₁(f) > 0` forces `δₙ(f) ≠ 0`. (`#print axioms` lists the cited Theorem 3.4.1.) -/
@[category research solved, AMS 30 15 13, ref "Ber92",
  formal_uses schurDelta taylorSeries schurClassInfty HasIndefiniteRank
    IsTaylorSeriesOfSchurClassInfty isTaylorSeriesOfSchurClassInfty_iff]
theorem schurDelta_eventually_ne_zero_corollary_3_4_1 (f : ℂ → ℂ)
    (hf : f ∈ schurClassInfty) (hrank : HasIndefiniteRank f) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → schurDelta (taylorSeries f) n ≠ 0 := by
  obtain ⟨n₀, hdisj⟩ := (isTaylorSeriesOfSchurClassInfty_iff (taylorSeries f)).mp ⟨f, hf, rfl⟩
  rcases hdisj with hpos | hzero
  · refine ⟨n₀, fun n hn hcontra => ?_⟩
    have := (hpos n hn).1
    rw [hcontra, zero_mul, Complex.zero_re] at this
    exact lt_irrefl 0 this
  · exact absurd ⟨n₀, hzero⟩ hrank

/-- **Corollary 3.4.1** (Bertin). If `f ∈ 𝓜_∞` has **no finite rank**, then there is an `n₀` such that
the ratio sequence `n ↦ δₙ₊₁(f)/δₙ(f)` is, for `n ≥ n₀`, **well-defined** (`δₙ(f) ≠ 0`), **positive**
(`0 < (·).re ∧ (·).im = 0`), and **decreasing** (`(δₙ₊₂/δₙ₊₁).re ≤ (δₙ₊₁/δₙ).re`).

**Proof** (Bertin). By Lemma 3.4.5 there is `n₀` with `Fⁿ⁰ = taylorSeries fₙ₀`, `fₙ₀ ∈ 𝓜` of indefinite
rank, so `δₙ(Fⁿ⁰) > 0` for all `n`. Lemma 3.4.2 gives `ρ > 0`, `μ ≠ 0` with `δₙ₊ₙ₀(F) = ρⁿμ δₙ(Fⁿ⁰)`,
whence `δₙ(f) ≠ 0` for `n ≥ n₀` and `δₙ₊ₙ₀₊₁(F)/δₙ₊ₙ₀(F) = ρ·δₙ₊₁(fₙ₀)/δₙ(fₙ₀)`; by Corollary 3.2.1 the
right side is positive and decreasing.

Recorded as a `cited` axiom (`ref "Ber92"`). The **"defined"** conjunct is genuinely provable — it is
`schurDelta_eventually_ne_zero_corollary_3_4_1` above (off Theorem 3.4.1). The **"positive"** and
**"decreasing"** conjuncts are blocked: "positive" needs the realness of `δₙ(f)` (a
Hermitian-determinant fact not isolated in the corpus), and "decreasing" needs Lemma 3.4.2's determinant
proportionality across the **generalised** iterate `Fⁿ⁰` fed into Corollary 3.2.1 — the same
proportionality gap as Theorem 3.4.1 (our `schurDelta_lemma_3_4_2` is the pure-Schur specialisation; a
version keyed to the unconstrained step relations would be unsound). -/
@[category research solved, AMS 30 15 13, ref "Ber92",
  formal_uses schurDelta taylorSeries schurClassInfty HasIndefiniteRank]
axiom schurDelta_ratio_pos_antitone_corollary_3_4_1 (f : ℂ → ℂ)
    (hf : f ∈ schurClassInfty) (hrank : HasIndefiniteRank f) :
    ∃ n₀ : ℕ,
      (∀ n, n₀ ≤ n → schurDelta (taylorSeries f) n ≠ 0) ∧
      (∀ n, n₀ ≤ n →
        0 < (schurDelta (taylorSeries f) (n + 1) / schurDelta (taylorSeries f) n).re ∧
        (schurDelta (taylorSeries f) (n + 1) / schurDelta (taylorSeries f) n).im = 0) ∧
      (∀ n, n₀ ≤ n →
        (schurDelta (taylorSeries f) (n + 2) / schurDelta (taylorSeries f) (n + 1)).re ≤
        (schurDelta (taylorSeries f) (n + 1) / schurDelta (taylorSeries f) n).re)

/-! ### Theorem 3.4.2 — the meromorphic Szegő limit (pole-corrected) -/

/-- **Theorem 3.4.2** (Bertin; D. W. Boyd [Boy77]). Let `f ∈ 𝓜_∞` have **no finite rank**, with poles
`θ₁, …, θₛ` in `D(0,1)` (the points of `{z ∈ D(0,1) | f not analytic at z}`, of which there are
`s = poleCount f`), and radial boundary function `f̂ = boundaryFun f`. Then the consecutive
Schur-determinant ratios converge to the geometric mean of the boundary spectral density `1 − |f̂|²`
**corrected by the pole product**:
`lim_{n→∞} δₙ₊₁(f)/δₙ(f) = ℒ(1 − |f̂|²) / ∏ᵢ₌₁ˢ |θᵢ|²`.

This is the meromorphic generalisation of **Theorem 3.2.2** (`schurDelta_ratio_tendsto_geometricMean`):
for `f ∈ 𝓜` (no poles) the product is empty (`= 1`) and the two statements coincide. The pole product is
written `∏ᶠ z ∈ {z ∈ ball 0 1 | ¬ AnalyticAt ℂ f z}, ‖z‖²` (a `finprod` over the finite pole set — the
same set whose cardinality is `poleCount f`); poles are taken **as the distinct points** of that set,
matching the `poleCount` convention of Lemmas 3.4.4–3.4.6.

Recorded as a `cited` axiom (`ref "Ber92" "Boy77"`): like Theorem 3.2.2 its proof is the Szegő limit
theorem (`szego-infimum-theorem`) plus Fatou boundary values (`fatou-radial-boundary-values`), now with
the Blaschke pole factor `∏ (z − θᵢ)/(1 − θ̄ᵢ z)` contributing the `∏ |θᵢ|²` denominator — none of which
is in Mathlib. -/
@[category research solved, AMS 30 15 42, ref "Ber92" "Boy77",
  formal_uses geometricMean boundaryFun schurDelta taylorSeries schurClassInfty HasIndefiniteRank,
  informal_uses "szego-infimum-theorem" "fatou-radial-boundary-values"]
axiom schurDelta_ratio_tendsto_geometricMean_div_poles_theorem_3_4_2 {f : ℂ → ℂ}
    (hf : f ∈ schurClassInfty) (hrank : HasIndefiniteRank f) :
    Tendsto (fun n => schurDelta (taylorSeries f) (n + 1) / schurDelta (taylorSeries f) n)
      atTop (𝓝 (((geometricMean (fun z => 1 - ‖boundaryFun f z‖ ^ 2) /
        ∏ᶠ z ∈ {z ∈ ball (0 : ℂ) 1 | ¬ AnalyticAt ℂ f z}, ‖z‖ ^ 2 : ℝ) : ℂ)))

end Complex
