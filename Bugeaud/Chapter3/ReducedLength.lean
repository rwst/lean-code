/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import ForMathlib.NumberTheory.PisotNumber
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.3 — the reduced length and Theorem 3.5

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Definition 3.4** and **Theorem 3.5** (Dubickas [Dub06], [Dub09]).

## Definition 3.4 (length and reduced length)

The **length** of a polynomial is the sum of the moduli of its coefficients. For an algebraic number
`α` with (primitive) integer minimal polynomial `P`, its length `L(α)` is the length of `P`, and its
**reduced length** `ℓ(α)` is the infimum of the lengths of `P·G` where `G` runs over the real
polynomials whose leading *or* constant coefficient equals `1`.

Formalized here as:
* `polyLength (P : Polynomial ℝ)` — `∑ |coeff|`;
* `NormalizedG G` — `G.leadingCoeff = 1 ∨ G.coeff 0 = 1`;
* `reducedPolyLength P` — `⨅_{G : NormalizedG} polyLength (P·G)`;
* `intMinpolyR α` — the primitive integer minimal polynomial of `α`, as a real polynomial
  (`IsLocalization.integerNormalization` clears denominators of `minpoly ℚ α`, `primPart` makes it
  primitive; `polyLength`/`reducedPolyLength` are sign- and content-normalization aware, so this is
  the right representative);
* `L α := polyLength (intMinpolyR α)` and `reducedLength α := reducedPolyLength (intMinpolyR α)`.

Proved structural facts: `polyLength_nonneg`, `reducedPolyLength_nonneg`, `reducedPolyLength_le`
(the infimum is `≤` the `G = 1` value), hence `reducedLength_le_L` (`ℓ(α) ≤ L(α)`).

## Theorem 3.5 (Dubickas — the spread lower bound)

For a real algebraic `α > 1`, any real `η`, and any non-zero real `ξ` that lies **outside `ℚ(α)`**
when `α` is a Pisot or Salem number,
`limsup {ξαⁿ + η} − liminf {ξαⁿ + η} ≥ 1/ℓ(α)`.
This is the exact spread constant behind the corpus' rational-base results: for `α = p/q` coprime with
`p > q ≥ 1` one has `ℓ(p/q) = p` (**Exercise 3.2**, `reducedLength_ratCast`), so Theorem 3.5 at
`η = 0` recovers the `1/p` spread bound — e.g. `ℓ(3/2) = 3` (`reducedLength_three_halves`), matching
the independently **proved** `FLP.three_halves_spread` (`1/3 ≤` spread of `ξ(3/2)ⁿ`).

The proof is the hard capstone of §3.3: writing `sₙ = ∑ qᵢ(ξαⁿ⁺ⁱ+η)`, one shows `(sₙ)` is **not
ultimately periodic** (a linear-recurrence + interpolation argument — Lemma 3.6, a Vandermonde
inversion — combined with the Pisot/Salem/`ℚ(α)` exclusion), then multiplies `Q` by an arbitrary real
`1 + b₁X + ⋯ + bₘXᵐ` and reads a spread bound `≥ 1/L(P)` off a repeated-block estimate (Corollary
A.4), whose infimum over `G` is `1/ℓ(α)`. It has no short Mathlib formalization, so — following the
corpus' layered convention — it is a `cited` axiom (`theorem_3_5`) with the complete proof in the
`informal_result` `"bugeaud-thm-3-5-spread"`.

## References

* [Bug12] Bugeaud, Yann. *Distribution Modulo One and Diophantine Approximation.* Cambridge Tracts in
  Mathematics 193, 2012. §3.3 (Def 3.4, Lemma 3.6, Thm 3.5, Ex 3.2).
* [Dub06] A. Dubickas, *Arithmetical properties of powers of algebraic numbers*, Bull. London Math.
  Soc. 38 (2006). [Dub09] A. Dubickas, *On the limit points of `(aξⁿ)ₙ` mod 1 …*.
-/

open Polynomial Filter Topology

namespace Bugeaud

/-! ### Definition 3.4 — length and reduced length -/

/-- **Length of a real polynomial** (Def 3.4): the sum of the absolute values (moduli) of its
coefficients. For the integer minimal polynomial of `α` this is Bugeaud's `L(α)`; Def 3.4 states it
for complex polynomials, but for a real algebraic `α` the defining polynomial and the multipliers `G`
are all real. -/
noncomputable def polyLength (P : Polynomial ℝ) : ℝ := ∑ i ∈ P.support, |P.coeff i|

/-- A real polynomial is **normalized** (an admissible multiplier `G` in Def 3.4) if its leading
coefficient *or* its constant coefficient equals `1`. -/
def NormalizedG (G : Polynomial ℝ) : Prop := G.leadingCoeff = 1 ∨ G.coeff 0 = 1

instance : Nonempty {G : Polynomial ℝ // NormalizedG G} := ⟨⟨1, Or.inl (by simp)⟩⟩

/-- **Reduced length of a real polynomial** (Def 3.4): the infimum of `polyLength (P·G)` over the
normalized real multipliers `G`. -/
noncomputable def reducedPolyLength (P : Polynomial ℝ) : ℝ :=
  ⨅ G : {G : Polynomial ℝ // NormalizedG G}, polyLength (P * G.1)

/-- The **primitive integer minimal polynomial** of an algebraic real `α`, as a real polynomial:
clear the denominators of the monic `minpoly ℚ α` (`IsLocalization.integerNormalization`) and take the
primitive part. For an algebraic integer this is the monic integer minimal polynomial; for `p/q`
(coprime) it is `qX − p`. (For transcendental `α`, `minpoly ℚ α = 0` and this is `0`.) -/
noncomputable def intMinpolyR (α : ℝ) : Polynomial ℝ :=
  ((IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (minpoly ℚ α)).primPart).map (Int.castRingHom ℝ)

/-- **Length `L(α)`** of an algebraic number (Def 3.4): the length of its integer minimal polynomial. -/
noncomputable def L (α : ℝ) : ℝ := polyLength (intMinpolyR α)

/-- **Reduced length `ℓ(α)`** of an algebraic number (Def 3.4, Dubickas): the reduced length of its
integer minimal polynomial. -/
noncomputable def reducedLength (α : ℝ) : ℝ := reducedPolyLength (intMinpolyR α)

/-- The length of a real polynomial is nonnegative. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_5"]
theorem polyLength_nonneg (P : Polynomial ℝ) : 0 ≤ polyLength P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The reduced length of a real polynomial is nonnegative. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_5"]
theorem reducedPolyLength_nonneg (P : Polynomial ℝ) : 0 ≤ reducedPolyLength P :=
  le_ciInf (fun _ => polyLength_nonneg _)

/-- The reduced length is `≤` the plain length: take the multiplier `G = 1`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_5", formal_uses polyLength]
theorem reducedPolyLength_le (P : Polynomial ℝ) : reducedPolyLength P ≤ polyLength P := by
  have hbdd : BddBelow (Set.range (fun G : {G : Polynomial ℝ // NormalizedG G} =>
      polyLength (P * G.1))) := ⟨0, by rintro x ⟨G, rfl⟩; exact polyLength_nonneg _⟩
  have h := ciInf_le hbdd (⟨1, Or.inl (by simp)⟩ : {G : Polynomial ℝ // NormalizedG G})
  simpa [reducedPolyLength] using h

/-- **`ℓ(α) ≤ L(α)`**: the reduced length never exceeds the length. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_5", formal_uses reducedLength L]
theorem reducedLength_le_L (α : ℝ) : reducedLength α ≤ L α :=
  reducedPolyLength_le _

/-- **`ℓ(α) ≥ 0`.** -/
@[category API, AMS 11, ref "Bug12", group "bug_3_5", formal_uses reducedLength]
theorem reducedLength_nonneg (α : ℝ) : 0 ≤ reducedLength α :=
  reducedPolyLength_nonneg _

/-! ### Exercise 3.2 — the reduced length of a rational -/

/- Bugeaud's Exercise 3.2: `ℓ(p/q) = p` for coprime `p > q ≥ 1`. The upper bound `≤ p` is a
telescoping construction; the exact value (hence the lower bound) is Dubickas' computation, which
makes Theorem 3.5 extend Theorems 3.1 and 3.3. -/
informal_result "bugeaud-reduced-length-rational"
  latex "For coprime integers $p>q\\ge1$ the reduced length of $p/q$ equals $p$. The minimal integer polynomial of $p/q$ is $P(X)=qX-p$, of length $p+q$. \\emph{Upper bound $\\ell(p/q)\\le p$.} Multiply by the normalized (constant coefficient $1$) real polynomial $G_N(X)=\\sum_{k=0}^{N}(q/p)^kX^k$: in $P(X)G_N(X)=(qX-p)\\sum_{k=0}^{N}(q/p)^kX^k$ the coefficient of $X^{k}$ for $1\\le k\\le N$ is $q(q/p)^{k-1}-p(q/p)^{k}=0$, so $P G_N=-p+(q/p)^N qX^{N+1}$, of length $p+(q/p)^Nq\\to p$ as $N\\to\\infty$. \\emph{Lower bound $\\ell(p/q)\\ge p$.} This is Dubickas' theorem (a special case of the mechanism of Theorem 3.5): no normalized multiplier drives the length of $P G$ below $p$. Hence $\\ell(p/q)=p$; in particular $\\ell(3/2)=3$, and Theorem 3.5 at $\\eta=0$ then gives the spread bound $1/p$ for $(\\{\\xi(p/q)^n\\})$."
  refs "Bug12"

/-- **Exercise 3.2** (Bugeaud §3.3; Dubickas). For coprime integers `p > q ≥ 1`, the reduced length of
`p/q` is `p`. This is what makes Theorem 3.5 extend Theorems 3.1 and 3.3 (for `α = p/q` the spread
bound `1/ℓ(α)` becomes `1/p`). The upper bound `≤ p` is an explicit telescoping construction; the exact
value is Dubickas' — recorded as a `cited` axiom, full argument in the `informal_result`
`"bugeaud-reduced-length-rational"`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_5", formal_uses reducedLength,
  informal_uses "bugeaud-reduced-length-rational"]
axiom reducedLength_ratCast (p q : ℕ) (hcop : Nat.Coprime p q) (hq : 1 ≤ q) (hpq : q < p) :
    reducedLength ((p : ℝ) / (q : ℝ)) = (p : ℝ)

/-- **`ℓ(3/2) = 3`** — the reduced length of `3/2`, the exact constant behind the `1/3` spread of the
`(3/2)ⁿ` orbit (`FLP.three_halves_spread`). Immediate from Exercise 3.2 with `p = 3, q = 2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_5", formal_uses reducedLength]
theorem reducedLength_three_halves : reducedLength ((3 : ℝ) / 2) = 3 := by
  have h := reducedLength_ratCast 3 2 (by decide) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-! ### Theorem 3.5 — the reduced-length spread bound -/

/- Bugeaud's full proof of Theorem 3.5 (Dubickas' Theorem 2 in [Dub09]; the `η = 0` case is [Dub06]),
recorded faithfully. The genuine inputs are the linear-recurrence solution (Theorem F.1), the
Vandermonde interpolation Lemma 3.6, the not-ultimately-periodic block dichotomy (Corollary A.4), and
the Pisot/Salem theory used to derive a contradiction from `ξ ∈ ℚ(α)`. -/
informal_result "bugeaud-thm-3-5-spread"
  latex "Let $Q(X)=q_dX^d+\\cdots+q_0$ be the minimal defining polynomial of $\\alpha$ over $\\mathbb{Q}$; for $n\\ge1$ put $x_n=\\xi\\alpha^n+\\eta$, $y_n=\\{\\xi\\alpha^n+\\eta\\}$, and $s_n=\\sum_i q_ix_{n+i}=-\\sum_i q_iy_{n+i}+\\eta Q(1)$. \\emph{(s_n) is not ultimately periodic.} Suppose $s_n=s_{n+\\ell}$ for $n\\ge n_0$. Then $u_n=x_{n+\\ell}-x_n$ satisfies $\\sum_i q_iu_{n+i}=0$, so by the theory of linear recurrences (Theorem F.1) $u_n=\\sum_{j=1}^d\\zeta_j\\alpha_j^n$ over the conjugates $\\alpha_1=\\alpha,\\dots,\\alpha_d$. Applying the interpolation Lemma 3.6 to the Vandermonde system $\\sum_jX_j\\alpha_j^{n-m}=u_n$ ($n=m,\\dots,m+d-1$) gives an integer polynomial $G_m$ of degree $\\le d-1$ with $Q'(\\alpha_j)\\zeta_j\\alpha_j^m=G_m(\\alpha_j)$; hence each $\\zeta_j\\in\\mathbb{Q}(\\alpha_j)$ and, the $\\zeta_j$ being conjugate, $\\zeta_1\\ne0$. As $a\\alpha^m=aG_m(\\alpha)/(Q'(\\alpha)\\zeta_1)$ is an algebraic integer for arbitrarily large $m$ (with $a$ a fixed denominator-clearing integer), $\\alpha$ is an algebraic integer. Next $\\delta_n=y_{n+\\ell}-y_n=\\xi(\\alpha-1)\\alpha^n-u_n=(\\xi(\\alpha-1)-\\zeta_1)\\alpha_1^n-\\zeta_2\\alpha_2^n-\\cdots-\\zeta_d\\alpha_d^n$; since $|\\delta_n|\\le1$, Lemma 3.6 bounds $X_1=(\\xi(\\alpha-1)-\\zeta_1)\\alpha_1^m,\\ X_j=-\\zeta_j\\alpha_j^m$ uniformly in $m$, forcing $\\zeta_1=\\xi(\\alpha-1)$ and $|\\alpha_2|,\\dots,|\\alpha_d|\\le1$. Thus $\\alpha$ is a Pisot or Salem number and $\\xi=\\zeta_1/(\\alpha-1)\\in\\mathbb{Q}(\\alpha)$, contradicting the hypothesis on $\\xi$. So $(s_n)$ is not ultimately periodic. \\emph{The spread bound.} For real $b_1,\\dots,b_m$ set $P(X)=Q(X)(1+b_1X+\\cdots+b_mX^m)=\\sum_jc_jX^j$; then $v_n:=\\sum_jc_jx_{n+j}=-\\sum_jc_jy_{n+j}+\\eta P(1)=b_ms_{n+m}+\\cdots+b_1s_{n+1}+s_n$. Since $s$ is not ultimately periodic, Corollary A.4 yields blocks $z_0z_1\\cdots z_m$ and $z_0'z_1\\cdots z_m$ occurring infinitely often with $z_0>z_0'$. With $\\lambda=\\liminf y_n$, $\\mu=\\limsup y_n$ and $\\varepsilon>0$, evaluating $v_n$ along these blocks gives $z_0+\\sum z_ib_i<\\eta P(1)+(\\mu+\\varepsilon)\\sum_{c_j<0}(-c_j)-(\\lambda-\\varepsilon)\\sum_{c_j>0}c_j$ and $-z_0'-\\sum z_ib_i<-\\eta P(1)+(\\mu+\\varepsilon)\\sum_{c_j>0}c_j-(\\lambda-\\varepsilon)\\sum_{c_j<0}(-c_j)$; adding, $1\\le z_0-z_0'<(\\mu-\\lambda+2\\varepsilon)L(P)$. Letting $\\varepsilon\\to0$, $\\mu-\\lambda\\ge1/L(P)$; the same holds for $P=Q\\cdot G$ with $G$ having leading or constant coefficient $1$, so taking the infimum over $G$ gives $\\mu-\\lambda\\ge1/\\ell(\\alpha)$. $\\qquad\\blacksquare$"
  refs "Bug12"

/-- **Theorem 3.5** (Bugeaud §3.3; Dubickas). Let `α > 1` be a real algebraic number and `η` a real
number. Let `ξ ≠ 0` be a real number that lies **outside the field `ℚ(α)`** when `α` is a Pisot or a
Salem number. Then the fractional parts of `ξαⁿ + η` have **spread at least `1/ℓ(α)`**:
`limsup {ξαⁿ + η} − liminf {ξαⁿ + η} ≥ 1/ℓ(α)`.

`ℓ(α)` is the reduced length (Def 3.4, `reducedLength`). This extends Theorems 3.1 and 3.3 via
`ℓ(p/q) = p` (`reducedLength_ratCast`), and its `α = 3/2, η = 0` instance is the `1/3` spread bound
independently proved as `FLP.three_halves_spread`. The proof (not-ultimately-periodic `(sₙ)` +
Lemma 3.6 + the `G`-multiplication trick) has no short Mathlib formalization, so it is a `cited` axiom;
the full argument is in the `informal_result` `"bugeaud-thm-3-5-spread"`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_5", formal_uses reducedLength,
  informal_uses "bugeaud-thm-3-5-spread"]
axiom theorem_3_5 (α : ℝ) (halg : IsAlgebraic ℚ α) (hα : 1 < α) (η ξ : ℝ) (hξ : ξ ≠ 0)
    (hexcl : (IsPisot α ∨ IsSalem α) →
      ξ ∉ (IntermediateField.adjoin ℚ ({α} : Set ℝ) : Set ℝ)) :
    1 / reducedLength α ≤
      limsup (fun n : ℕ => Int.fract (ξ * α ^ n + η)) atTop
        - liminf (fun n : ℕ => Int.fract (ξ * α ^ n + η)) atTop

end Bugeaud
