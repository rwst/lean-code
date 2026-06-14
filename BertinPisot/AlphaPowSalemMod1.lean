/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import BertinPisot.AlphaPowMod1
import BertinPisot.AlphaPowDistribution
import BertinPisot.UniformDistribution
import BertinPisot.MultidimDistribution
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Salem numbers mod 1: powers (Theorem 5.3.2, §5.3) and scaled powers (Theorems 5.5.1–5.5.2, §5.5)

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

## Theorem 5.5.1 (§5.5) — a Salem multiple, small and dense in a tiny interval

Bertin's **Theorem 5.5.1** (§5.5): for a Salem number `τ` and any `0 < η < 1/2` there is a **non-zero
real `λ`** with `‖λτⁿ‖ < η` for all large `n`, and `(λτⁿ)` is **dense mod 1 in an interval centred at
`0` and contained in `[−η, η]`**. The construction takes a Pisot number `θ ∈ S ∩ ℚ(γ)` (`γ = τ + τ⁻¹`,
the totally real field of Theorem 5.2.3) and `λ = θ^{2h}`: the trace
`Tr_{ℚ(τ)/ℚ}(λτⁿ) = λ(τⁿ+τ⁻ⁿ) + 2∑_{j=2}^{s} λ⁽ʲ⁾cos 2πnω⁽ʲ⁾` is a rational integer, the conjugate sum
`0 < 2∑_j λ⁽ʲ⁾ ≤ 2(s−1)δ^{2h}` (`δ = max_j |θ⁽ʲ⁾| < 1`, the Pisot conjugates of `θ`) is forced below
`η/2` by taking `h` large (and then `λτ⁻ⁿ < η/2`), and the density in `[−λ⁽²⁾, λ⁽²⁾]` is the
Theorem 5.3.2 Kronecker argument applied to the scaled residues. Resting on the cited multiplier
structure of Theorem 5.2.3 (`theorem_5_2_3`) and the §5.3.2 density technique (`theorem_5_3_2`), it is
recorded — like them — as a `cited` axiom (`theorem_5_5_1`), the full proof in the `informal_result`
`"salem-scaled-power-small-dense"`.

**Theorem 5.5.2 (§5.5) — a function-theoretic characterization.** `τ > 1` is a Salem number **iff**
there is a non-zero `λ` for which the residue generating function `ε(z) = ∑ₙ ε(λτⁿ) zⁿ` (analytic on
`D(0,1)`, `AlphaPow.εTaylor`) has **real part bounded above** on `D(0,1)` yet **`ε ∉ H²`**. This is the
Salem counterpart of Theorem 5.4.2 (Pisot ⟺ `ε ∈ H²`): for a Salem number `ε` *fails* `H²` but its real
part stays bounded above. As with Theorem 5.4.2, `H²` membership is read off the coefficients by
Parseval (`ε ∈ H² ⟺ ∑ₙ ε(λτⁿ)² < ∞`), so `ε ∉ H²` is `¬ Summable (ε(λτⁿ)²)`; "real part bounded
above" is `∃ M, ∀ z ∈ D(0,1), Re ε(z) ≤ M`. Stated without proof in the source — a `cited` axiom
(`theorem_5_5_2`).

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.3 (Thm 5.3.2),
    §5.5 (Thms 5.5.1–5.5.2).
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

/- Bertin's full proof of Theorem 5.5.1 (§5.5), recorded faithfully. The genuine inputs are the cited
multiplier structure of Theorem 5.2.3 (the totally real field `ℚ(γ)`, `γ = τ + τ⁻¹`, and a Pisot
number `θ ∈ S ∩ ℚ(γ)` with `λ = θ^{2h}`) and the §5.3.2 density technique (ℚ-independence of the
unimodular conjugate arguments `ω⁽ʲ⁾` plus the inhomogeneous Kronecker theorem), applied to the
`λ`-scaled trace `Tr_{ℚ(τ)/ℚ}(λτⁿ)`. -/
informal_result "salem-scaled-power-small-dense"
  latex "Let $\\tau$ be a Salem ($T$-) number of degree $2s$, with conjugates $\\tau,\\tau^{-1}$ (real, $\\tau>1>\\tau^{-1}>0$) and $s-1$ unimodular conjugate pairs $\\tau^{(j)}=e^{2\\pi i\\omega^{(j)}}$ ($j=2,\\dots,s$); put $\\gamma=\\tau+\\tau^{-1}$, $K=\\mathbb{Q}(\\tau)$, and fix $\\eta$ with $0<\\eta<\\tfrac12$. By Theorem 5.2.3 the field $\\mathbb{Q}(\\gamma)$ is totally real; choose a Pisot number $\\theta\\in S\\cap\\mathbb{Q}(\\gamma)$ and set $\\lambda=\\theta^{2h}$ ($h\\in\\mathbb{N}^{*}$). Since $\\theta\\in S\\subset\\mathbb{Q}(\\gamma)$ is totally real its conjugates $\\theta^{(j)}$ are real, so the conjugates $\\lambda^{(j)}=\\theta^{(j)2h}$ ($j=2,\\dots,s$) of $\\lambda$ are real and positive. The trace $\\lambda(\\tau^n+\\tau^{-n})+2\\sum_{j=2}^{s}\\lambda^{(j)}\\cos 2\\pi n\\omega^{(j)}=\\operatorname{Tr}_{K/\\mathbb{Q}}(\\lambda\\tau^n)$ is a rational integer (the algebraic integer $\\lambda\\tau^n$ has integer trace). Set $\\delta=\\max_{j=2,\\dots,s}|\\theta^{(j)}|<1$ (the non-dominant conjugates of the Pisot number $\\theta$ have modulus $<1$). Then $0<2\\sum_{j=2}^{s}\\lambda^{(j)}\\le 2(s-1)\\delta^{2h}$. Choose $h$, and then $n_0\\ge 1$, so that $2(s-1)\\delta^{2h}<\\eta/2$ and $\\lambda\\tau^{-n_0}<\\eta/2$. For $n\\ge n_0$ the residue of $\\lambda\\tau^n$ modulo $1$ is $-\\bigl(\\lambda\\tau^{-n}+2\\sum_{j=2}^{s}\\lambda^{(j)}\\cos 2\\pi n\\omega^{(j)}\\bigr)$ (the integer trace removed), so $\\|\\lambda\\tau^n\\|\\le\\lambda\\tau^{-n}+2\\sum_{j=2}^{s}\\lambda^{(j)}<\\tfrac{\\eta}{2}+\\tfrac{\\eta}{2}=\\eta$. Hence $\\|\\lambda\\tau^n\\|<\\eta$ for all $n\\ge n_0$. \\emph{Density.} Assume w.l.o.g. $\\lambda^{(2)}=\\max_{j}\\lambda^{(j)}$. Exactly as in the proof of Theorem 5.3.2 --- the reals $1,\\omega^{(2)},\\dots,\\omega^{(s)}$ are $\\mathbb{Q}$-linearly independent (a Galois argument) and the inhomogeneous Kronecker theorem applies to $(\\omega^{(j)})_{2\\le j\\le s}$ --- for every $\\rho\\in[-\\lambda^{(2)},\\lambda^{(2)}]$ and every neighbourhood $V$ of $\\rho$ there are arbitrarily large integers $m$ with $\\varepsilon_m:=\\varepsilon(\\lambda\\tau^m)\\in V$. Thus $(\\lambda\\tau^n)$ is dense modulo $1$ in $[-\\lambda^{(2)},\\lambda^{(2)}]$, an interval centred at $0$ and (by the choice of $h,n_0$, since $\\lambda^{(2)}\\le\\sum_j\\lambda^{(j)}<\\eta$) contained in $[-\\eta,\\eta]$. $\\qquad\\blacksquare$"
  refs "Ber92"

/-- **Theorem 5.5.1** (Bertin §5.5 — cited). Let `τ` be a `T`-number (Salem number) and `0 < η < 1/2`.
Then there is a **non-zero real `λ`** such that:

* `‖λτⁿ‖ < η` for all `n ≥ n₀` (some `n₀ ≥ 1`) — the multiple `λτⁿ` is eventually within `η` of an
  integer; and
* `(λτⁿ)` is **dense modulo `1`** in some interval `[−c, c]` (`0 < c ≤ η`) centred at `0` and contained
  in `[−η, η]`.

The Salem (`T`) counterpart of the Pisot scaled-power theory: where a Pisot multiple `λθⁿ` *converges*
to `0` mod `1` (`pisot_smul_pow_tendsto_zero`), a Salem multiple can be made to stay within any
prescribed `η` while *densely filling* a small symmetric interval. Bertin's construction (§5.5) takes a
Pisot `θ ∈ S ∩ ℚ(γ)` (`γ = τ + τ⁻¹`, totally real by Theorem 5.2.3) and `λ = θ^{2h}`: the integer
trace `Tr_{ℚ(τ)/ℚ}(λτⁿ) = λ(τⁿ+τ⁻ⁿ) + 2∑_{j} λ⁽ʲ⁾cos 2πnω⁽ʲ⁾` reduces `‖λτⁿ‖` to the conjugate sum
`2∑_j λ⁽ʲ⁾ ≤ 2(s−1)δ^{2h}` (`δ = max_j|θ⁽ʲ⁾| < 1`), forced below `η` for `h` large, while the density in
`[−λ⁽²⁾, λ⁽²⁾]` is the Theorem 5.3.2 Kronecker argument on the scaled residues. It rests on the cited
multiplier structure of Theorem 5.2.3 (`theorem_5_2_3`) and the §5.3.2 density technique
(`theorem_5_3_2`) — neither short to formalize — so, as for those, it is a `cited` axiom; the complete
proof is in the `informal_result` `"salem-scaled-power-small-dense"`. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses T S theorem_5_2_3 theorem_5_3_2,
  informal_uses "salem-scaled-power-small-dense" "salem-field-structure-5-2-3"
    "salem-conjugate-arguments-linindep"]
axiom theorem_5_5_1 (τ : ℝ) (hτ : τ ∈ T) (η : ℝ) (hη0 : 0 < η) (hη : η < 1/2) :
    ∃ lam : ℝ, lam ≠ 0 ∧
      (∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → distToNearestInt (lam * τ ^ n) < η) ∧
      (∃ c : ℝ, 0 < c ∧ c ≤ η ∧
        Set.Icc (-c) c ⊆ closure (Set.range (fun n : ℕ => ε (lam * τ ^ n))))

/- Theorem 5.5.2 (Bertin §5.5) — the function-theoretic Salem characterization, stated without proof
in the source, recorded as a `cited` axiom. The two conditions on `ε(z) = ∑ₙ ε(λτⁿ) zⁿ`
(`AlphaPow.εTaylor`, analytic on `D(0,1)`): real part bounded above on the disk, and `ε ∉ H²` — read
via Parseval as the non-square-summability `¬ Summable (ε(λτⁿ)²)`, exactly as `H²` is handled in
Theorem 5.4.2. -/
informal_result "salem-eps-reBddAbove-not-H2"
  latex "A real $\\tau>1$ belongs to $T$ (is a Salem number) if and only if there exists a non-zero real $\\lambda$ such that the residue generating function $\\varepsilon(z)=\\sum_{n\\ge 0}\\varepsilon(\\lambda\\tau^n)\\,z^n$ --- analytic on $D(0,1)$ --- has its real part bounded above on $D(0,1)$, i.e. $\\sup_{|z|<1}\\operatorname{Re}\\varepsilon(z)<\\infty$, yet $\\varepsilon\\notin H^2$ (equivalently, by Parseval, $\\sum_{n}\\varepsilon(\\lambda\\tau^n)^2=\\infty$). This is the Salem ($T$) counterpart of Theorem 5.4.2: there $\\tau$ is a Pisot number iff $\\varepsilon\\in H^2$ for some $\\lambda\\ne 0$; here, for a Salem number, $\\varepsilon$ fails $H^2$ while keeping its real part bounded above on the disk. (Bertin §5.5; stated without proof in the source.)"
  refs "Ber92"

/-- **Theorem 5.5.2** (Bertin §5.5 — cited, stated without proof). A real `τ > 1` belongs to `T` (is a
Salem number) **iff** there is a non-zero real `λ` for which the residue generating function
`ε(z) = ∑ₙ ε(λτⁿ) zⁿ` (`AlphaPow.εTaylor lam τ`, analytic on `D(0,1)`):

* has **real part bounded above** on the disk — `∃ M, ∀ z, ‖z‖ < 1 → Re (ε z) ≤ M`; and
* **does not belong to `H²`** — recorded, via Parseval (`ε ∈ H² ↔ ∑ₙ εₙ² < ∞`, the same reading used
  for Theorem 5.4.2), as `¬ Summable (fun n => ε(λτⁿ)²)`.

The function-theoretic Salem counterpart of Theorem 5.4.2 (Pisot ⟺ `ε ∈ H²`): for a Pisot number the
residue series is square-summable (`ε ∈ H²`), whereas for a Salem number it just fails `H²` while its
real part remains bounded above on `D(0,1)`. The screenshot supplies the statement only; the proof
(Bertin §5.5, the Hardy-space/Nevanlinna circle) is not formalized, so this is a `cited` axiom. -/
@[category research solved, AMS 11, ref "Ber92",
  formal_uses T AlphaPow.εTaylor AlphaPow.ε,
  informal_uses "salem-eps-reBddAbove-not-H2"]
axiom theorem_5_5_2 (τ : ℝ) (hτ : 1 < τ) :
    τ ∈ T ↔ ∃ lam : ℝ, lam ≠ 0 ∧
      (∃ M : ℝ, ∀ z : ℂ, ‖z‖ < 1 → ((AlphaPow.εTaylor lam τ).sum z).re ≤ M) ∧
      ¬ Summable (fun n : ℕ => (AlphaPow.ε lam τ n) ^ 2)

end Bertin
