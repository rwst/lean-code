/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Tactic
import ForMathlib.NumberTheory.PisotNumber
import ForMathlib.NumberTheory.ConjugatePowerSum
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.4 — Theorem 3.7 (powers of a Salem number)

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Theorem 3.7** (Pisot and Salem [567]):

> For any Salem number `α`, the sequence `(αⁿ)ₙ≥₁` is **dense modulo one**, but is **not uniformly
> distributed** modulo one.

This is the Salem counterpart of the Pisot fact `‖αⁿ‖ → 0` (Theorem 3.1-adjacent): a Pisot number's
powers converge to `0` modulo one, whereas a Salem number's powers spread out densely yet fail to
equidistribute.

## The proof (Bugeaud §3.4)

Let `d = 2s` be the degree of `α`, with conjugates `α, 1/α` (real, `α > 1 > 1/α > 0`) and the
`s − 1` unimodular conjugate pairs `α⁽ʲ⁾ = e^{2πiω⁽ʲ⁾}, α⁽ʲ⁾⁻¹` (`j = 3, …, d−1`, `j` odd). For every
`n` the power sum `αⁿ + α⁻ⁿ + ∑ⱼ(α⁽ʲ⁾ⁿ + α⁽ʲ⁾⁻ⁿ)` is a rational integer — the trace
`Tr_{ℚ(α)/ℚ}(αⁿ)` — so modulo one `(αⁿ)` agrees, up to the vanishing `α⁻ⁿ → 0`, with the oscillatory
conjugate sum `2∑ⱼ cos 2πnω⁽ʲ⁾`. This trace reduction is the **proved** opener
`salem_conj_powerSum_isInt` (via the general `conj_powerSum_isInt`).

* **Dense.** The reals `1, ω⁽³⁾, …, ω⁽ᵈ⁻¹⁾` are ℤ-linearly independent (a Galois argument,
  `Lemma 3.8`), so by **Theorem 1.18** (Kronecker) the conjugate sum can be steered to any prescribed
  `ρ ∈ (0, 1)`; hence there are arbitrarily large `n` with an integer `rₙ` and `rₙ − αⁿ ≈ ρ`, i.e.
  `(αⁿ)` is dense modulo one.
* **Not u.d.** For `φ(x) = 2 cos 2πx` the Weyl transform `∫₀¹ exp(4πih cos 2πt) dt = J₀(4πh)` is the
  Bessel function of order `0`, nonzero for every nonzero integer `h`; by **Theorem 1.19** the image
  sequence `2∑ⱼ cos 2πnω⁽ʲ⁾`, hence `(αⁿ)`, is not uniformly distributed modulo one.

The genuine inputs beyond the proved trace reduction — the unimodular-conjugate arguments `ω⁽ʲ⁾`,
their ℤ-linear independence, the nonvanishing of `J₀(4πh)`, and the cited equidistribution Theorems
1.18/1.19 — have no short Mathlib formalization, so, following the same layered convention as the
structurally identical dense-but-not-u.d. results elsewhere in the corpus, the full statement is
recorded as a `cited` axiom (`theorem_3_7`) with the complete proof in the `informal_result`
`"bugeaud-salem-power-dense-not-ud"`.

## Scope note

This is a Bugeaud-namespace (`ref "Bug12"`) formalization of Theorem 3.7. The identical Pisot–Salem
result is also recorded, independently, in the Bertin (`ref "Ber92"`) estate as
`Bertin.theorem_5_3_2` (`BertinPisot/AlphaPowSalemMod1.lean`), with the same proof and the same cited
inputs. The two are kept as separate cited axioms — this file imports no `BertinPisot` module — so
that `Bugeaud/Chapter3/` stays self-contained; the general Salem predicate (`IsSalem`) and the trace
fact (`conj_powerSum_isInt`) live in `ForMathlib` and are shared.

## References

* [Bug12] Bugeaud, Yann. *Distribution Modulo One and Diophantine Approximation.* Cambridge Tracts in
  Mathematics 193, Cambridge University Press, 2012. §3.4 (Theorem 3.7, Lemma 3.8).
-/

open Polynomial

namespace Bugeaud

/-- **Power sum of the conjugates of a Salem number is a rational integer** (the opening of Bugeaud's
proof of Theorem 3.7). For a Salem number `α` and every `n`, the sum `∑ βⁿ` over the roots `β` of
`minpoly ℚ α` — i.e. `αⁿ + α⁻ⁿ + ∑_{j}(α⁽ʲ⁾ⁿ + α⁽ʲ⁾⁻ⁿ)` — is a rational integer (the trace
`Tr_{ℚ(α)/ℚ}(αⁿ)`). **Proved**: a Salem number is an algebraic integer (`hα.2.1`), so this is the
general trace fact `conj_powerSum_isInt`. It is what lets us pass modulo `1` from `(αⁿ)` to the
oscillatory conjugate sum `2∑ⱼ cos 2πnω⁽ʲ⁾`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_7", formal_uses IsSalem]
theorem salem_conj_powerSum_isInt (α : ℝ) (hα : IsSalem α) (n : ℕ) :
    ∃ m : ℤ, (((minpoly ℚ α).aroots ℂ).map (· ^ n)).sum = (m : ℂ) :=
  conj_powerSum_isInt α hα.2.1 n

/- Bugeaud's full proof of Theorem 3.7 (both the density and the non-equidistribution halves),
recorded faithfully. The genuine inputs beyond the proved trace reduction are the unimodular
conjugate arguments `ω⁽ʲ⁾`, their ℤ-linear independence (Galois, Lemma 3.8), the nonvanishing of the
Bessel transform `J₀(4πh)`, and the cited equidistribution Theorems 1.18 (Kronecker) and 1.19. -/
informal_result "bugeaud-salem-power-dense-not-ud"
  latex "Let $\\alpha$ be a Salem number of degree $d$, with Galois conjugates $\\alpha,\\alpha^{-1}$ (real, $\\alpha>1>\\alpha^{-1}>0$) and the unimodular conjugates $\\alpha_3,\\alpha_3^{-1},\\dots,\\alpha_{d-1},\\alpha_{d-1}^{-1}$ arranged in complex-conjugate pairs; for $j=3,\\dots,d-1$ odd write $\\alpha_j=e^{2\\pi i\\omega_j}$. \\emph{Trace reduction.} For every $n$ the power sum $\\alpha^n+\\alpha^{-n}+\\alpha_3^{n}+\\alpha_3^{-n}+\\cdots+\\alpha_{d-1}^{-n}=\\operatorname{Tr}_{\\mathbb{Q}(\\alpha)/\\mathbb{Q}}(\\alpha^n)$ is a rational integer, and $\\alpha^{-n}\\to0$; so modulo $1$ the sequence $(\\alpha^n)$ is governed by $\\alpha^{-n}+2\\sum_{j}\\cos 2\\pi n\\omega_j$. \\emph{Lemma 3.8.} The reals $1,\\omega_3,\\dots,\\omega_{d-1}$ are $\\mathbb{Z}$-linearly independent: a relation $a_1+a_3\\omega_3+\\cdots+a_{d-1}\\omega_{d-1}=0$ exponentiates to $\\prod_{j}\\alpha_j^{a_j}=1$; applying the complex embedding $\\sigma_h$ with $\\sigma_h(\\alpha_h)=\\alpha$ gives $\\alpha^{a_h}\\prod_{j\\ne h}\\sigma_h(\\alpha_j)^{a_j}=1$, and since every $\\sigma_h(\\alpha_j)$ ($j\\ge3$, $j\\ne h$) is on the unit circle while $\\alpha>1$, taking moduli forces $a_h=0$ for each $h$. Hence, by Theorem 1.18 (Kronecker's simultaneous inhomogeneous approximation), for any prescribed unimodular $\\eta_3,\\dots,\\eta_{d-1}$ (paired) and any $\\varepsilon>0$ there are arbitrarily large $n$ with $|\\alpha_k^{n}-\\eta_k|<\\varepsilon$ for $k=3,\\dots,d$. \\emph{(a) Dense.} Fix $\\rho\\in(0,1)$; let $\\eta_3$ be unimodular with real part $\\rho/2$ and $\\eta_5=\\cdots=\\eta_{d-1}=i$. By Lemma 3.8 there are arbitrarily large $n$ with $\\rho-d\\varepsilon\\le\\alpha^{-n}+\\alpha_3^{n}+\\alpha_3^{-n}+\\cdots+\\alpha_{d-1}^{-n}\\le\\rho+d\\varepsilon$, so there is an integer $r_n$ with $\\rho-d\\varepsilon\\le r_n-\\alpha^{n}\\le\\rho+d\\varepsilon$; thus $(\\alpha^n)$ is dense modulo one. \\emph{(b) Not uniformly distributed.} By the $\\mathbb{Z}$-independence the sequence $((n\\omega_j)_j)$ is uniformly distributed modulo one in the torus; for $\\varphi(x)=2\\cos 2\\pi x$ the exponential integral $\\int_0^1\\exp(4\\pi i h\\cos 2\\pi t)\\,dt=J_0(4\\pi h)$ ($J_0$ the Bessel function of order $0$) is nonzero for every $h\\in\\mathbb{Z}^{*}$, so by Theorem 1.19 the image sequence $\\bigl(2\\sum_{j}\\cos 2\\pi n\\omega_j\\bigr)$, and hence $(\\alpha^n)$, is not uniformly distributed modulo one. $\\qquad\\blacksquare$"
  refs "Bug12"

/- The Galois step of Lemma 3.8: the arguments `ω⁽ʲ⁾` of the unimodular conjugates of a Salem number
are, together with `1`, ℤ-linearly independent. Uses transitivity of the Galois action on the
conjugates (an embedding `σₕ` sending each `αₕ` to `α`) plus a modulus comparison. -/
informal_result "bugeaud-salem-conjugate-arguments-linindep"
  latex "Let $\\alpha$ be a Salem number with unimodular conjugates $\\alpha_j=e^{2\\pi i\\omega_j}$ ($j=3,\\dots,d-1$ odd). Then $1,\\omega_3,\\dots,\\omega_{d-1}$ are $\\mathbb{Z}$-linearly independent. Indeed a relation $a_1+\\sum_{j}a_j\\omega_j=0$ with $a_i\\in\\mathbb{Z}$ exponentiates to $\\prod_{j}\\alpha_j^{a_j}=\\exp\\!\\big(2\\pi i\\sum_j a_j\\omega_j\\big)=1$. For each odd $h$ let $\\sigma_h$ be the complex embedding with $\\sigma_h(\\alpha_h)=\\alpha$; applying it gives $\\alpha^{a_h}\\prod_{j\\ne h}\\sigma_h(\\alpha_j)^{a_j}=1$. Every $\\sigma_h(\\alpha_j)$ ($j\\ge3$, $j\\ne h$) is again a conjugate of modulus $1$, so taking absolute values yields $\\alpha^{a_h}=1$, whence $a_h=0$ since $\\alpha>1$. Thus all $a_j=0$, and then $a_1=0$."
  refs "Bug12"

/- The non-equidistribution input of part (b): the Weyl transform of the cosine map is a Bessel value
`J₀(4πh)`, nonzero for every nonzero integer `h` — exactly the criterion (Theorem 1.19) that fails,
so the cosine-image of the equidistributed `(nω⁽ʲ⁾)` is not u.d. -/
informal_result "bugeaud-bessel-J0-transform-nonvanishing"
  latex "For the cosine map $\\varphi(t)=2\\cos 2\\pi t$ and a nonzero integer $h$, the exponential integral $\\int_0^1\\exp\\!\\big(2\\pi i h\\,\\varphi(t)\\big)\\,dt=\\int_0^1\\exp(4\\pi i h\\cos 2\\pi t)\\,dt$ equals $J_0(4\\pi h)$, the Bessel function of the first kind of order $0$ (via $J_0(z)=\\frac1{2\\pi}\\int_0^{2\\pi}e^{iz\\cos\\theta}\\,d\\theta$). This value is nonzero for every $h\\in\\mathbb{Z}^{*}$: the positive real zeros $j_{0,k}$ of $J_0$ ($j_{0,1}\\approx2.405,\\ j_{0,2}\\approx5.520,\\dots$) are not integer multiples of $4\\pi$, so $4\\pi h$ is never a zero. Because these transforms are all nonzero for $h\\ne0$, the cosine-image of an equidistributed sequence violates Weyl's criterion (Theorem 1.19) and is therefore not uniformly distributed modulo one."
  refs "Bug12"

/-- **Theorem 3.7** (Bugeaud §3.4; Pisot and Salem). For any **Salem number** `α`, the sequence
`(αⁿ)ₙ≥₁` is **dense modulo one** but is **not uniformly distributed** modulo one.

The proof opens with the **proved** trace reduction (`salem_conj_powerSum_isInt`): `αⁿ` agrees modulo
`1`, up to the vanishing `α⁻ⁿ`, with the oscillatory conjugate sum `2∑ⱼ cos 2πnω⁽ʲ⁾`. Density then
follows from the ℤ-linear independence of `1, ω⁽³⁾, …, ω⁽ᵈ⁻¹⁾` (a Galois argument, Lemma 3.8) via
Kronecker's Theorem 1.18; non-equidistribution from Theorem 1.19 together with the nonvanishing of the
Bessel transform `J₀(4πh)`. Those inputs have no short Mathlib formalization, so — as for the
structurally identical dense-but-not-u.d. results in the corpus — the full statement is a `cited`
axiom; see the `informal_result` `"bugeaud-salem-power-dense-not-ud"` for the complete proof.

Independently recorded in the Bertin estate as `Bertin.theorem_5_3_2`; kept separate (this file imports
no `BertinPisot` module). -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_7",
  formal_uses IsSalem salem_conj_powerSum_isInt,
  informal_uses "bugeaud-salem-power-dense-not-ud" "bugeaud-salem-conjugate-arguments-linindep"
    "bugeaud-bessel-J0-transform-nonvanishing"]
axiom theorem_3_7 (α : ℝ) (hα : IsSalem α) :
    IsDenseModuloOne (fun n : ℕ => α ^ n) ∧ ¬ IsEquidistributedModuloOne (fun n : ℕ => α ^ n)

end Bugeaud
