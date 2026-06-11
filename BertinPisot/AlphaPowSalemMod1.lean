/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowMod1
import BertinPisot.UniformDistribution
import BertinPisot.MultidimDistribution
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem 5.3.2 — powers of a Salem number are dense but not u.d. mod 1 (Bertin §5.3)

Bertin's **Theorem 5.3.2** (*Pisot and Salem Numbers* [Ber92], §5.3): if `τ` is a `T`-number (a
Salem number) then the sequence `(τⁿ)` is **dense** modulo `1` but **not uniformly distributed**
modulo `1`. This is the Salem counterpart of Theorem 5.3.1 (`Bertin.theorem_5_3_1`): for a Pisot
number the powers *converge* to `0` mod `1`, whereas for a Salem number they spread out densely yet
fail Weyl's equidistribution.

**The reduction (proved opening).** A Salem number `τ` of degree `2s` has conjugates `τ`, `τ⁻¹` (real,
`τ > 1 > τ⁻¹ > 0`) together with `s − 1` unimodular conjugate pairs
`τ⁽ʲ⁾ = e^{2πiω⁽ʲ⁾}, τ̄⁽ʲ⁾ = e^{−2πiω⁽ʲ⁾}` (`j = 2, …, s`). The trace
`τⁿ + τ⁻ⁿ + ∑_{j=2}^{s}(τ⁽ʲ⁾ⁿ + τ̄⁽ʲ⁾ⁿ) = τⁿ + τ⁻ⁿ + 2∑_{j=2}^{s} cos 2πnω⁽ʲ⁾` is a **rational
integer** — the power sum over all conjugates, `Tr_{ℚ(τ)/ℚ}(τⁿ) ∈ ℤ`, which is **proved**
(`salem_conj_powerSum_isInt`, a direct instance of the trace fact `conj_powerSum_isInt`). Hence mod
`1` the distribution of `(τⁿ)` equals that of `−(τ⁻ⁿ + 2∑_{j=2}^{s} cos 2πnω⁽ʲ⁾)`; as `τ⁻ⁿ → 0`, it is
governed by the bounded oscillatory sum `(2∑_{j=2}^{s} cos 2πnω⁽ʲ⁾)`.

**(a) Dense — cited.** First `1, ω⁽²⁾, …, ω⁽ˢ⁾` are ℚ-linearly independent (a Galois argument: an
automorphism `σ` of the splitting field with `σ(τ⁽²⁾) = τ` turns a relation `∏ τ⁽ʲ⁾^{ℓⱼ} = 1` into a
modulus contradiction unless every `ℓⱼ = 0`). Then **Theorem 4.6.4** (inhomogeneous Kronecker,
`kronecker_theorem_4_6_4`) applied to `(ω⁽ʲ⁾)` with target `μ = (β, 1/4, …, 1/4)` makes
`2∑_{j} cos 2πmω⁽ʲ⁾` approximate any prescribed `ρ = 2cos 2πβ`, so `(τⁿ)` is dense mod `1`.

**(b) Not u.d. — cited.** By ℚ-independence and **Theorem 4.6.3** (`uniformlyDistributedModOne_nα`),
`((nω⁽ʲ⁾)_{j})` is u.d. mod `1` in `ℝˢ⁻¹`. For `φ(x) = 2cos 2πx` the integral
`∫₀¹ exp(4iπh cos 2πt) dt = J₀(4hπ)` (the order-`0` Bessel function) is nonzero for every `h ∈ ℤ*`, so
by **Theorem 4.6.5** (`uniformlyDistributedModOne_sum_comp_continuous_iff`) the image sequence
`2∑_{j} cos 2πnω⁽ʲ⁾`, and hence `(τⁿ)`, is **not** u.d. mod `1`.

Parts (a) and (b) rest on the unimodular-conjugate structure `τ⁽ʲ⁾ = e^{2πiω⁽ʲ⁾}` and its arguments
`ω⁽ʲ⁾`, the Galois linear-independence, the nonvanishing of the Bessel transform, and the cited
equidistribution Theorems 4.6.3/4.6.4/4.6.5 — none of which is available as a short Mathlib
formalization. Following the same convention as the structurally identical "dense but not u.d."
**Theorem 4.4.3** (`denseNotUniformlyDistributedModOne_theorem_4_4_3`, itself a cited axiom), the full
statement is recorded as a `cited` axiom (`theorem_5_3_2`) with the complete proof in the
`informal_result` `"salem-power-dense-not-ud"`; the trace reduction that opens it is proved.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.3, Thm 5.3.2.
-/

open Filter Topology

namespace Bertin

/-- **Power sum of the conjugates of a Salem number is a rational integer** (the opening of Bertin's
proof of Theorem 5.3.2). For `τ ∈ T` and every `n`, the sum `∑ βⁿ` over the roots `β` of `minpoly ℚ τ`
— i.e. `τⁿ + τ⁻ⁿ + ∑_{j=2}^{s}(τ⁽ʲ⁾ⁿ + τ̄⁽ʲ⁾ⁿ)` — is a rational integer (the trace
`Tr_{ℚ(τ)/ℚ}(τⁿ)`). **Proved**: a Salem number is an algebraic integer (`hτ.2.1`), so this is the
trace fact `conj_powerSum_isInt`. It is what lets us pass mod `1` from `(τⁿ)` to the oscillatory
conjugate sum `(2∑_{j=2}^{s} cos 2πnω⁽ʲ⁾)`. -/
@[category research solved, AMS 11, ref "Ber92", formal_uses T,
  informal_uses "conjugate-power-sum-integer"]
theorem salem_conj_powerSum_isInt (τ : ℝ) (hτ : τ ∈ T) (n : ℕ) :
    ∃ m : ℤ, (((minpoly ℚ τ).aroots ℂ).map (· ^ n)).sum = (m : ℂ) :=
  conj_powerSum_isInt τ hτ.2.1 n

/- Bertin's full proof of Theorem 5.3.2 (both the density and the non-equidistribution halves),
recorded faithfully. The genuine inputs beyond the proved trace reduction are: the unimodular
conjugate arguments `ω⁽ʲ⁾`, their ℚ-linear independence (Galois), the nonvanishing of the Bessel
transform `J₀(4hπ)`, and the cited equidistribution Theorems 4.6.3/4.6.4/4.6.5. -/
informal_result "salem-power-dense-not-ud"
  latex "Let $\\tau$ be a Salem ($T$-) number of degree $2s$, with conjugates $\\tau,\\tau^{-1}$ (real, $\\tau>1>\\tau^{-1}>0$) and $s-1$ unimodular conjugate pairs $\\tau^{(j)}=e^{2\\pi i\\omega^{(j)}},\\ \\overline{\\tau^{(j)}}=e^{-2\\pi i\\omega^{(j)}}$ ($j=2,\\dots,s$). \\emph{Reduction.} The trace $\\tau^n+\\tau^{-n}+\\sum_{j=2}^{s}(\\tau^{(j)n}+\\overline{\\tau^{(j)}}^{\\,n})=\\tau^n+\\tau^{-n}+2\\sum_{j=2}^{s}\\cos 2\\pi n\\omega^{(j)}$ is a rational integer, so modulo $1$ the sequence $(\\tau^n)$ has the same distribution as $\\bigl(-(\\tau^{-n}+2\\sum_{j=2}^{s}\\cos 2\\pi n\\omega^{(j)})\\bigr)$; since $\\tau^{-n}\\to 0$ it is governed by $\\bigl(2\\sum_{j=2}^{s}\\cos 2\\pi n\\omega^{(j)}\\bigr)$. \\emph{(a) Dense.} The reals $1,\\omega^{(2)},\\dots,\\omega^{(s)}$ are $\\mathbb{Q}$-linearly independent: if $\\ell_1+\\sum_{j=2}^{s}\\ell_j\\omega^{(j)}=0$ with $\\ell_i\\in\\mathbb{Z}$ then $\\exp(2\\pi i\\sum_{j\\ge 2}\\ell_j\\omega^{(j)})=1$, i.e. $\\prod_{j=2}^{s}\\tau^{(j)\\ell_j}=1$; in the Galois extension $\\mathbb{Q}(\\tau,\\tau^{-1},\\tau^{(2)},\\overline{\\tau^{(2)}},\\dots)$ there is an automorphism $\\sigma$ with $\\sigma(\\tau^{(2)})=\\tau$, whence $\\tau^{\\ell_2}\\prod_{j\\ge 3}\\sigma(\\tau^{(j)})^{\\ell_j}=1$, impossible by moduli ($\\tau>1$, the rest unimodular) unless $\\ell_2=0$; likewise every $\\ell_j=0$. Given $\\rho$ with $-\\tfrac12\\le\\rho\\le\\tfrac12$, write $\\rho=2\\cos 2\\pi\\beta$ ($\\beta\\in[-1,1]$); by Theorem 4.6.4 (inhomogeneous Kronecker) applied to $(\\omega^{(j)})_{2\\le j\\le s}$ with $\\mu=(\\beta,\\tfrac14,\\dots,\\tfrac14)$, for every $\\varepsilon>0$ there is an arbitrarily large $m$ with $|m\\omega^{(2)}-\\beta|<\\varepsilon$ and $|m\\omega^{(j)}-\\tfrac14|<\\varepsilon$ (mod $1$, $j\\ge 3$), so $2\\sum_{j=2}^{s}\\cos 2\\pi m\\omega^{(j)}$ is within $O(\\varepsilon)$ of $2\\cos 2\\pi\\beta+0=\\rho$. Thus $(\\tau^n)$ is dense modulo $1$. \\emph{(b) Not uniformly distributed.} By the $\\mathbb{Q}$-independence and Theorem 4.6.3 the sequence $((n\\omega^{(j)})_{j=2,\\dots,s})$ is uniformly distributed modulo $1$ in $\\mathbb{R}^{s-1}$. For $\\varphi(x)=2\\cos 2\\pi x$ the integral $\\int_0^1\\exp(4\\pi i h\\cos 2\\pi t)\\,dt=J_0(4h\\pi)$ ($J_0$ the Bessel function of order $0$) is nonzero for all $h\\in\\mathbb{Z}^*$, so by Theorem 4.6.5 the image sequence $2\\sum_{j=2}^{s}\\cos 2\\pi n\\omega^{(j)}$, hence $(\\tau^n)$, is not uniformly distributed modulo $1$. $\\qquad\\blacksquare$"
  refs "Ber92"

/- The Galois step of part (a): the arguments `ω⁽ʲ⁾` of the unimodular conjugates of a Salem number
are, together with `1`, ℚ-linearly independent. The proof uses transitivity of the Galois action on
conjugates (an automorphism `σ` with `σ(τ⁽²⁾) = τ`) plus a modulus comparison. -/
informal_result "salem-conjugate-arguments-linindep"
  latex "Let $\\tau$ be a Salem number with unimodular conjugates $\\tau^{(j)}=e^{2\\pi i\\omega^{(j)}}$ ($j=2,\\dots,s$). Then $1,\\omega^{(2)},\\dots,\\omega^{(s)}$ are $\\mathbb{Q}$-linearly independent. Indeed a relation $\\ell_1+\\sum_{j=2}^{s}\\ell_j\\omega^{(j)}=0$ with $\\ell_i\\in\\mathbb{Z}$ exponentiates to $\\prod_{j=2}^{s}\\tau^{(j)\\ell_j}=\\exp\\!\\big(2\\pi i\\sum_{j\\ge 2}\\ell_j\\omega^{(j)}\\big)=1$. The Galois group of the splitting field $\\mathbb{Q}(\\tau,\\tau^{-1},\\tau^{(2)},\\overline{\\tau^{(2)}},\\dots,\\tau^{(s)},\\overline{\\tau^{(s)}})$ acts transitively on the conjugates of the (irreducible) minimal polynomial, so there is an automorphism $\\sigma$ with $\\sigma(\\tau^{(2)})=\\tau$; applying it gives $\\tau^{\\ell_2}\\prod_{j\\ge 3}\\sigma(\\tau^{(j)})^{\\ell_j}=1$. Each $\\sigma(\\tau^{(j)})$ is again a conjugate of modulus $1$, so taking moduli forces $\\tau^{\\ell_2}=1$, hence $\\ell_2=0$ since $\\tau>1$. Repeating with automorphisms sending each $\\tau^{(j)}$ to $\\tau$ gives $\\ell_3=\\dots=\\ell_s=0$, and then $\\ell_1=0$."
  refs "Ber92"

/- The non-equidistribution input of part (b): the Weyl transform of the cosine map is a Bessel value
`J₀(4πh)`, nonzero for every nonzero integer `h` — which is exactly the criterion (Theorem 4.6.5) that
fails, so the cosine-image of the equidistributed `(nω⁽ʲ⁾)` is not u.d. -/
informal_result "bessel-J0-transform-nonvanishing"
  latex "For the cosine map $\\varphi(t)=2\\cos 2\\pi t$ and a nonzero integer $h$, the exponential integral $\\int_0^1\\exp\\!\\big(2\\pi i h\\,\\varphi(t)\\big)\\,dt=\\int_0^1\\exp(4\\pi i h\\cos 2\\pi t)\\,dt$ equals $J_0(4\\pi h)$, where $J_0$ is the Bessel function of the first kind of order $0$ (via $J_0(z)=\\frac1{2\\pi}\\int_0^{2\\pi}e^{iz\\cos\\theta}\\,d\\theta$). This value is nonzero for every $h\\in\\mathbb{Z}^*$: the positive real zeros $j_{0,k}$ of $J_0$ ($j_{0,1}\\approx 2.405,\\ j_{0,2}\\approx 5.520,\\dots$) are not integer multiples of $4\\pi$, so $4\\pi h$ is never a zero. Because these transforms are all nonzero for $h\\ne 0$, the cosine-image of an equidistributed sequence violates Weyl's criterion and is therefore not uniformly distributed modulo one (the mechanism of Theorem 4.6.5)."
  refs "Ber92"

/-- **Theorem 5.3.2** (Bertin §5.3). The powers of a Salem number are **dense but not uniformly
distributed** modulo `1`: for `τ ∈ T`, the residues `ε(τⁿ)` are dense in `[-1/2, 1/2)`, yet `(τⁿ)` is
not uniformly distributed modulo `1`.

This is the Salem counterpart of Theorem 5.3.1 (Pisot powers converge to `0` mod `1`). The proof
opens with the **proved** trace reduction (`salem_conj_powerSum_isInt`): `τⁿ` agrees mod `1`, up to the
vanishing `τ⁻ⁿ`, with the oscillatory conjugate sum `2∑_{j=2}^{s} cos 2πnω⁽ʲ⁾`. Density then follows
from the ℚ-linear independence of `1, ω⁽²⁾, …, ω⁽ˢ⁾` (a Galois argument) via the inhomogeneous
Kronecker Theorem 4.6.4; non-equidistribution from Theorem 4.6.3 together with the nonvanishing of the
Bessel transform `J₀(4hπ)` and Theorem 4.6.5. Those inputs (the unimodular-conjugate arguments `ω⁽ʲ⁾`,
the Galois independence, the Bessel fact, and the cited Theorems 4.6.3/4.6.4/4.6.5) have no short
Mathlib formalization, so — as for the structurally identical Theorem 4.4.3 — the full statement is a
`cited` axiom; see the `informal_result` `"salem-power-dense-not-ud"` for the complete proof. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses T salem_conj_powerSum_isInt Multidim.uniformlyDistributedModOne_nα
    Multidim.kronecker_theorem_4_6_4 Multidim.uniformlyDistributedModOne_sum_comp_continuous_iff,
  informal_uses "salem-power-dense-not-ud" "conjugate-power-sum-integer"
    "salem-conjugate-arguments-linindep" "bessel-J0-transform-nonvanishing"]
axiom theorem_5_3_2 (τ : ℝ) (hτ : τ ∈ T) :
    (Set.Ico (-(1/2) : ℝ) (1/2) ⊆ closure (Set.range (fun n : ℕ => ε (τ ^ n))))
      ∧ ¬ UniformlyDistributedModOne (fun n : ℕ => τ ^ n)

end Bertin
