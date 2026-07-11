/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Yu's p-adic logarithmic forms (Forum Math. 2007), ℚ-specialization

Yu Kunrui's theory of `p`-adic logarithmic forms ([Yu07], the third in the series
[Yu98], [Yu99], [Yu07]; the 2007 Main Theorem and its first consequence read in full
2026-07-08) gives an **effective** upper bound for the `p`-adic valuation of
`α₁^{b₁}···αₙ^{bₙ} − 1`.  This is the `p`-adic companion of Baker–Wüstholz
(`CITED/BakerWustholz.lean`) and, unlike the Subspace-based engines in this directory
(`CZ`, `Evertse`, `BCZ`), it is **fully effective** — the constant is written down.

The clean citable form is the **first consequence** of the Main Theorem ([Yu07], p. 190),
which drops every side condition of the Main Theorem (no multiplicative independence, no
`ord_𝔭 α_j = 0`, roots of unity allowed):

> Let `α₁, …, αₙ` be non-zero algebraic numbers in a number field `K` of degree `d`, let
> `𝔭` be a prime of `K` above the rational prime `p`, and set `Ξ = α₁^{b₁}···αₙ^{bₙ}`
> with `b_j ∈ ℤ` not all zero and `Ξ ≠ 1`.  Then
>
>   `ord_𝔭(Ξ − 1) < n · C₀(n, d, 𝔭) · h₁···hₙ · log B`,
>
> where `B ≥ max(|b₁|, …, |bₙ|, 3)`, `h_j = max(h₀(α_j), 1/(16 e² d²))`, and
> `C₀(n, d, 𝔭) = (16 e d)^{2(n+1)} · n^{3/2} · log(2nd) · log(2d) · e_𝔭ⁿ ·
> p^{f_𝔭}/(f_𝔭 log p)²`.

`h₀` is the absolute logarithmic Weil height and `e_𝔭, f_𝔭` are the ramification index
and residue degree of `𝔭`.

## Statement conventions (the ℚ-specialization — all uses in this corpus)

* **`K = ℚ`, `d = 1`, `𝔭 = p` a rational prime** (so `e_𝔭 = f_𝔭 = 1`).  Then
  `ord_𝔭 = ord_p` is the ordinary `p`-adic exponential valuation, transcribed as
  `padicValRat p : ℚ → ℤ`, cast to `ℝ`.
* **Bases `α : Fin n → ℚ`** non-zero, exponents `b : Fin n → ℤ` not all zero; the form is
  `Ξ = ∏ j, (α j)^(b j) ∈ ℚ` (integer `zpow`), with `Ξ ≠ 1` (else `Ξ − 1 = 0` and
  `ord_p` is `+∞`).
* **Height.**  `h₀(α_j)` is `Height.logHeight₁ (α j)` (Mathlib's log Weil height; for a
  rational it is `log max(|num|, den)`, `Rat.logHeight₁_eq_log_max`) — the same height
  primitive as `CITED/BakerWustholz.lean`.  The *modified* height of [Yu07] is
  `Yu.yuHeight (α j) = max(h₀(α_j), 1/(16 e²))` (the `d = 1` value of `1/(16 e² d²)`).
* **The constant is explicit** — `Yu.C₀ n p` is the `d = 1`, `e_𝔭 = f_𝔭 = 1`
  specialization of `C₀(n, d, 𝔭)`:
  `(16 e)^{2(n+1)} · n^{3/2} · log(2n) · log 2 · p / (log p)²`.  **This explicitness is
  the whole point**: Yu's bound is *effective*, so downstream one may in principle compute
  the threshold — in contrast to the ineffective Subspace engines here.
* **`B`** is a free real with `3 ≤ B` and `|b_j| ≤ B` for all `j` (i.e.
  `B ≥ max(|b_j|, 3)`, [Yu07] (1.18)).

Role ([M4A3] §8 row 3, priority 2): effective flat-window (`p = 2`) bounds for the binary
digits of the `(3/2)ⁿ` program — `Yu.padicVal2_prod_sub_one_lt` is the `p = 2` instance.
Note the *single-base* case `v₂(3ⁿ − 1)` is elementary (LTE, `n = 1`), so Yu is only
needed for genuinely multi-term forms ([M4A3] §11: on the current A5 route the two-term
`Γ = ⟨2, 3⟩` forms are LTE-exact, and Yu is a reserve engine).

## The sharp `p = 3` bound (`plan-formalize-logforms.html` F-3)

The first consequence above drops *every* side condition (roots of unity allowed, no
multiplicative independence, no `ord_𝔭 α_j = 0`), which costs a factor of roughly
`10²·⁵`–`10⁴` in the constant.  Yu's **Theorem 1** ([Yu07] (1.24), §1.2) keeps those side
conditions and delivers the sharp bound
`ord_𝔭(Ξ − 1) < C₁*(n,d,𝔭) · Ω · log B`, with `C₁* = (n+1)·C₁` from (1.6).

`ord3_prod_sub_one_lt_sharp` transcribes Theorem 1 specialized to **`K = ℚ`, `d = 1`,
`𝔭 = 3`** (§1.3 **case I.2**: `c⁽¹⁾ = 537`, `a⁽¹⁾ = 16`, `q^u = 2`, `e_𝔭 = f_𝔭 = 1`), for
**multiplicatively independent** rationals.  Two simplifications then apply:

* Multiplicative independence makes `rank Γ = n`, so the height product `Ω` of (1.22)
  collapses to the **true absolute Weil heights** `∏ⱼ h₀(αⱼ)` — no modified height, **no
  `1/(16e²d²)` floor** (unlike the first consequence's `yuHeight`).  The modified height
  `h⁽ⁿ⁾` and the constant `κ₁ = 20` are therefore irrelevant here (they appear only in
  `Ω`'s `a ∖ b` factors, empty in the independent case).
* Condition (1.5) is **automatic** over `ℚ` at `p = 3`: with `q = 2` (since `p > 2`) it
  reads `ord₂(3^{f_𝔭} − 1) = 1`, and `ord₂(3 − 1) = ord₂ 2 = 1`.  So it is stated in the
  docstring, not carried as a hypothesis.  Multiplicative independence and `ord₃ αⱼ = 0`
  ((1.15)) *are* carried, as hypotheses.

The resulting constant `C₁sharp n = (n+1)·C₁(n,1,𝔭₃)` is `≈ 1.2×10⁸` at `n = 2` and
`≈ 5.1×10¹⁰` at `n = 3` — roughly `780×` (`n=2`) to `12000×` (`n=3`) sharper than the
first-consequence constant `n·C₀`.

### Not transcribed (verdicts, per F-3)

* **Second consequence** (the `δ`-form, Sharpening II — [Yu07] p. 190–191): its constant
  carries an additive `log c₁(n,d) ≈ 51`–`92` *inside* the outer log, so it loses to the
  first/sharp consequence for single-shot instances; its habitat is Stewart–Yu-style
  `Bₙ ≪ B` iterations, of which the corpus has no instance.  Skipped.
* **The `(10ed)`-for-`(16ed)` remark** ([Yu07] p. 191): for `p > 2` the factor
  `(16ed)^{2(n+1)}` in the *first-consequence* constant `C₀` may be replaced by
  `(10ed)^{2(n+1)}` (a `≈17×` gain at `n = 2`).  The printed placement is ambiguous
  (stated after the second consequence but arguably global); it is **claimed nowhere** and
  recorded here only.
* **[Yu98] headline consequence** (`≈20`–`30×` over the first consequence, one-line
  constant): heights are floored at `log p` and an `ord`-condition is not explicit in
  print — the documented middle option, not an axiom.
* **`p = 2` companion.** The sharp `p = 2` bound must be stated over `ℚ(ζ₃)` (`d = 2`,
  `f_𝔭 = 2`, case VII, `c⁽¹⁾ = 160`) with the bridge `ord_𝔭 ↾_ℚ = ord₂` — heavier plumbing
  (a concrete `NumberField` instance) for a `≈170×` gain.  **Deferred.**

## Contents

* `Yu.yuHeight` — the modified height `max(h₀(α), 1/(16 e²))` of [Yu07] (`d = 1`).
* `Yu.yuHeight_pos` — it is strictly positive (so the product bound is by a positive real).
* `Yu.C₀` — the explicit constant `C₀(n, 1, p)` of [Yu07].
* `Yu.padicVal_prod_sub_one_lt` — **the first consequence of the Main Theorem** ([Yu07]),
  ℚ-specialized; a cited effective bound recorded as an `axiom`.
* `Yu.padicVal2_prod_sub_one_lt` — the `p = 2` instance, proved from the axiom.
* `Yu.C₁sharp` — the explicit sharp constant `C₁*(n) = (n+1)·C₁(n,1,𝔭₃)` of [Yu07]
  Theorem 1 (§1.3 case I.2).
* `Yu.ord3_prod_sub_one_lt_sharp` — **Theorem 1** ([Yu07] (1.24)), specialized to `p = 3`,
  `d = 1`, multiplicatively independent bases; a cited effective bound recorded as an
  `axiom`.

## References

* [Yu07] Yu, Kunrui. "P-adic logarithmic forms and group varieties III." *Forum
  Mathematicum* **19** (2007), 187–280.  (Main Theorem and first consequence, p. 190; MSC
  11J86, 11J61.)  Preceded by [Yu98] (J. reine angew. Math. **502** (1998), 29–92) and
  [Yu99] (Acta Arith. **89** (1999), 337–378); the theory refines Matveev's estimates.
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §7 (engine audit), §8 row 3
  (transcription brief), §11 (A5 route / LTE remark).
-/

namespace Yu

/-- The **modified height** of [Yu07] (specialized to `d = 1`): `max(h₀(α), 1/(16 e²))`,
where `h₀ = Height.logHeight₁` is the log Weil height. -/
@[category API, AMS 11, ref "Yu07", group "three_halves_m4"]
noncomputable def yuHeight (α : ℚ) : ℝ :=
  max (Height.logHeight₁ α) (1 / (16 * Real.exp 1 ^ 2))

/-- The modified height is strictly positive (it dominates `1/(16 e²) > 0`). -/
@[category API, AMS 11, ref "Yu07", group "three_halves_m4"]
lemma yuHeight_pos (α : ℚ) : 0 < yuHeight α := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  positivity

/-- The **explicit constant** `C₀(n, 1, p)` of [Yu07] (with `d = 1`, `e_𝔭 = f_𝔭 = 1`):
`(16 e)^{2(n+1)} · n^{3/2} · log(2n) · log 2 · p / (log p)²`.  Written out because Yu's
bound is *effective*. -/
@[category API, AMS 11, ref "Yu07", group "three_halves_m4"]
noncomputable def C₀ (n p : ℕ) : ℝ :=
  (16 * Real.exp 1) ^ (2 * (n + 1)) * (n : ℝ) ^ ((3 : ℝ) / 2) *
    Real.log (2 * n) * Real.log 2 * (p : ℝ) / Real.log (p : ℝ) ^ 2

/-- **Yu's p-adic logarithmic forms bound** ([Yu07], first consequence of the Main
Theorem, p. 190), ℚ-specialized to `K = ℚ`, `d = 1`, `𝔭 = p` a rational prime (see the
module doc): for non-zero rationals `α₁, …, αₙ`, integers `b₁, …, bₙ` not all zero, and
`Ξ = ∏ αⱼ^{bⱼ} ≠ 1`,

  `ord_p(Ξ − 1) < n · C₀(n, p) · (∏ⱼ hⱼ) · log B`,

where `hⱼ = yuHeight (αⱼ)` and `B ≥ max(|bⱼ|, 3)`.  Recorded as a cited `axiom` on the
authority of [Yu07] — a `p`-adic linear-forms-in-logarithms estimate (Kummer descent on
group varieties, refining Matveev) we do not re-derive.  Unlike the Subspace engines in
this directory the bound is **effective** (the constant `C₀` is explicit). -/
@[category research solved, AMS 11, ref "Yu07", group "three_halves_m4"]
axiom padicVal_prod_sub_one_lt (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 2 ≤ n)
    (α : Fin n → ℚ) (hα : ∀ j, α j ≠ 0) (b : Fin n → ℤ) (hb : ∃ j, b j ≠ 0)
    (hΞ : (∏ j, α j ^ b j) ≠ 1)
    (B : ℝ) (hB : (3 : ℝ) ≤ B) (hbB : ∀ j, (|b j| : ℝ) ≤ B) :
    ((padicValRat p ((∏ j, α j ^ b j) - 1) : ℤ) : ℝ)
      < (n : ℝ) * C₀ n p * (∏ j, yuHeight (α j)) * Real.log B

/-- **The 2-adic instance** ([Yu07] at `p = 2`): the effective flat-window prime of the
`(3/2)ⁿ` program.  Proved from `padicVal_prod_sub_one_lt`. -/
@[category research solved, AMS 11, ref "Yu07", group "three_halves_m4"]
lemma padicVal2_prod_sub_one_lt (n : ℕ) (hn : 2 ≤ n) (α : Fin n → ℚ) (hα : ∀ j, α j ≠ 0)
    (b : Fin n → ℤ) (hb : ∃ j, b j ≠ 0) (hΞ : (∏ j, α j ^ b j) ≠ 1)
    (B : ℝ) (hB : (3 : ℝ) ≤ B) (hbB : ∀ j, (|b j| : ℝ) ≤ B) :
    ((padicValRat 2 ((∏ j, α j ^ b j) - 1) : ℤ) : ℝ)
      < (n : ℝ) * C₀ n 2 * (∏ j, yuHeight (α j)) * Real.log B :=
  padicVal_prod_sub_one_lt 2 Nat.prime_two n hn α hα b hb hΞ B hB hbB

/-- The **sharp constant** `C₁*(n) = (n+1)·C₁(n,1,𝔭₃)` of [Yu07] Theorem 1, specialized to
`K = ℚ`, `d = 1`, `𝔭 = 3` (§1.3 **case I.2**: `c⁽¹⁾ = 537`, `a⁽¹⁾ = 16`, `q^u = 2`,
`e_𝔭 = f_𝔭 = 1`).  From (1.6),
`C₁(n,1,𝔭₃) = 537·16ⁿ·(nⁿ(n+1)ⁿ⁺¹/n!)·(3/2)·(1/(log 3)ⁿ⁺²)·max(log(e⁴(n+1)), 1, log 3)`,
where the factor `log max(d,e) = log e = 1` (`d = 1`) is omitted, `p^{f_𝔭}/q^u = 3/2`,
`(d/(f_𝔭 log p))ⁿ⁺² = 1/(log 3)ⁿ⁺²`, and the last max is
`max(log(e⁴(n+1)d), e_𝔭, f_𝔭 log p)` at the case values.  Numerically `≈ 1.2×10⁸` at
`n = 2`, `≈ 5.1×10¹⁰` at `n = 3`. -/
@[category API, AMS 11, ref "Yu07", group "yu_padic_sharp"]
noncomputable def C₁sharp (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) *
    (537 * 16 ^ n * ((n : ℝ) ^ n * ((n : ℝ) + 1) ^ (n + 1) / (n.factorial : ℝ))
      * (3 / 2)
      * (1 / Real.log 3 ^ (n + 2))
      * max (Real.log (Real.exp 4 * ((n : ℝ) + 1))) (max 1 (Real.log 3)))

/-- **Yu's sharp `p`-adic bound, Theorem 1** ([Yu07] (1.24), §1.2), specialized to `K = ℚ`,
`d = 1`, `𝔭 = 3` (see the module doc): for `2 ≤ n`, **multiplicatively independent** nonzero
rationals `α₁, …, αₙ` with `ord₃ αⱼ = 0` ((1.15)), integers `b₁, …, bₙ` not all zero, and
`Ξ = ∏ⱼ αⱼ^{bⱼ} ≠ 1`,

  `ord₃(Ξ − 1) < C₁sharp(n) · (∏ⱼ h₀(αⱼ)) · log B`,

where `h₀ = Height.logHeight₁` is the **true absolute Weil height** (`d = 1`, *no*
`yuHeight` floor — multiplicative independence collapses `Ω` of (1.22) to `∏ h₀`) and
`B ≥ max(|bⱼ|, 3)`.  Condition (1.5) is automatic here (`ord₂(3 − 1) = 1`, module doc), so
it is not carried.  Recorded as a cited `axiom` on the authority of [Yu07] — the sharp
sibling of `padicVal_prod_sub_one_lt`, `≈ 780×` (`n=2`) to `12000×` (`n=3`) smaller. -/
@[category research solved, AMS 11, ref "Yu07", group "yu_padic_sharp"]
axiom ord3_prod_sub_one_lt_sharp (n : ℕ) (hn : 2 ≤ n)
    (α : Fin n → ℚ) (hα : ∀ j, α j ≠ 0)
    (hord : ∀ j, padicValRat 3 (α j) = 0)
    (hindep : ∀ c : Fin n → ℤ, (∏ j, α j ^ c j) = 1 → ∀ j, c j = 0)
    (b : Fin n → ℤ) (hb : ∃ j, b j ≠ 0) (hΞ : (∏ j, α j ^ b j) ≠ 1)
    (B : ℝ) (hB : (3 : ℝ) ≤ B) (hbB : ∀ j, (|b j| : ℝ) ≤ B) :
    ((padicValRat 3 ((∏ j, α j ^ b j) - 1) : ℤ) : ℝ)
      < C₁sharp n * (∏ j, Height.logHeight₁ (α j)) * Real.log B

end Yu
