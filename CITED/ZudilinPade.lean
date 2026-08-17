/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Zudilin's Padé construction for `‖(3/2)^k‖` — cited

The construction data of [Zud07] — the current record engine, `θ = 0.5803` — packaged as the
**two independent integer forms** that an elimination step consumes, exactly as
`CITED/HabsiegerPade.lean` packages [Hab03].  `Zudilin.PadeData m` is the bundle;
`Zudilin.padeData` is the single axiom producing it.  Nothing here mentions a multiplier, a
distance to the nearest integer, or a rate.

**The one structural difference from the [Hab03] bundle, and it is the whole point of this file:**
[Zud07]'s estimates are *limits* ((19), (20), (21)), so the bundle holds only above a threshold
that the source does not compute.  The axiom therefore quantifies existentially over that
threshold, and every consequence downstream is existential in its first date.  [Zud07]'s own
Theorem 1 says exactly this: `‖(3/2)^k‖ > 0.5803^k` for `k ≥ K`, "where `K` is a certain effective
constant" — effective, and uncomputed.  See `plans/note-Tshift-S1-WP7.html` §3.

## What the source proves, and where

[Zud07], J. Théor. Nombres Bordeaux **19** (2007), 311–323.  Fix `a = αm`, `b = βm`,
`n = γm` or `γm + 1` with `α = γ = 9`, `β = 19` (p. 318, 321); write `S = α + β + γ = 37`.
Let `Q_n, P_n ∈ ℤ[x]` be the Padé denominator/numerator (8), (10) of the *shifted* binomial
series `F(a, b; z) = ∑_ν C(a+b+ν, b) z^ν` (7), and `R_n` the remainder (11), so that

> `Q_n(z⁻¹)F(z) = P_n(z⁻¹) + R_n(z)`  (9)
>
> **Lemma 2.**  `Q_{n+1}(x)P_n(x) − Q_n(x)P_{n+1}(x) = (−1)ⁿ C(a+2n+1, a+n)·C(a+b+n, b−n)·x`
>
> **Lemma 3.**  `Φ⁻¹Q_n(x) ∈ ℤ[x]` and `Φ⁻¹P_n(x) ∈ ℤ[x]`, `Φ = ∏_{p > √(a+b+n)} p^{e_p}` (13), (15)
>
> **Lemma 4.**  `(n+1)Φ′⁻¹Q_{n+1}(x) ∈ ℤ[x]` and `(n+1)Φ′⁻¹P_{n+1}(x) ∈ ℤ[x]`  (16)
>
> `C₀(z) = lim_m log|R_n(z)|/m`  (19),  `C₁(z) = lim_m log|Q_n(z⁻¹)|/m`  (20),
> `C₂ = lim_m log Φ(αm, βm, γm)/m = C₂′`  (21), (22)
>
> at `z = 1/9`, `(α, β, γ) = (9, 19, 9)`:  `C₀ = 3.28973907…`, `C₁ = 35.48665992…`,
> `C₂ = 4.46695926…`  (p. 321)

## How the displays become this bundle

Zudilin's (6) is `(3/2)^{3(b+1)} = T + 3^{b−2a+1}F(a, b; 1/9)` with
`T = ∑_{k<a} C(b+k, b)·3^{b+1−2k} ∈ ℤ`.  Put `N := 3(b+1) = 57m + 3` and, for each of the two
indices `i ∈ {γm, γm+1}`,

`bⁱ := Q_i(9)`,  `aⁱ := −(Q_i(9)·T + P_i(9)·3^{b−2a+1})`,  `b − 2a + 1 = m + 1`,

so that (9) at `z = 1/9`, cleared by `3^{m+1}·2^N`, is exactly the two-column form

`aⁱ·2^N + bⁱ·3^N = 2^N·3^{m+1}·R_i(1/9)`.

`T` is absorbed into `aⁱ` and **cancels from the determinant** — the same thing that happens to
[Hab03]'s `W`, for the same reason — leaving, by Lemma 2 at `x = 9`,

`|a¹b² − a²b¹| = 3^{m+1}·9·C(a+2n+1, a+n)·C(a+b+n, b−n) = 3^{m+3}·C(27m+1, 18m)·C(37m, 10m)`.

The contents are `Γ₁ = Φ` (Lemma 3) and `Γ₂ = Φ′/gcd(Φ′, γm+1)` (Lemma 4); the polynomial factor
`γm + 1` is absorbed by reading (21) strictly, i.e. `contentBase < e^{C₂}`.  All four clauses were
verified as exact integers at `m = 1, 2, 3, 4` — including the determinant value, both
divisibilities and the two-column identity — by `python3 TShift/tshift_numerics.py s1z`, block [C].

## The rational surrogates, and their direction

Each of the three limits is replaced by a rational base rounded *away* from the claim, read off
the digits printed on p. 321 rather than from any recomputation:

| printed | recorded surrogate | direction | cost |
|---|---|---|---|
| `C₀ = 3.28973907…` | `errorBase = 26.8358608 ≥ e^{3.28973908}` | up | `7.3·10⁻⁹` nats/`m` |
| `C₁ = 35.48665992…` | `denomBase = 2 580 242 883 000 000 ≥ e^{35.48665993}` | up | `5.7·10⁻⁹` nats/`m` |
| `C₂ = 4.46695926…` | `contentBase = 87.0914921 ≤ e^{4.4669592}` | down | `6.6·10⁻⁸` nats/`m` |

Total `7.1·10⁻⁸` nats per `m`, against the `δ = 0.00027320432…` of rounding slack that [Zud07]
itself leaves between `e^{−(C₁−C₂)/57} = 0.580302781…` and the printed `0.5803` — the surrogates
spend **0.026 %** of that budget.  The two inequalities the consumer needs are therefore both
true with room: `3·errorBase < contentBase` is condition (26) (margin `e^{0.0786079} = 1.08178`),
and `denomBase·0.5803^57 ≤ contentBase` is the rate (margin `1.0002732`).

Since the estimates hold only asymptotically, the *value* of the bases below the limit is
irrelevant; what is recorded is that they bound the limits strictly in the stated direction.  The
constants were independently recomputed to 40 digits from (19), (20), (21) — the maximisations
solved to machine precision and `C₂` summed as `∑(ψ(bᵢ) − ψ(aᵢ))` over the eighteen intervals
printed on p. 321 — and agree with every printed digit; see `s1z` block [A].

## What this axiom may not smuggle

* **Nothing about a multiplier.**  No `D` occurs in any statement of this file.
* **Not the nonvanishing.**  The bundle records the *value* of the determinant from Lemma 2, and
  `PadeData.det_ne_zero` derives nonvanishing in Lean from `Nat.choose_pos`.  ([Zud07] states this
  as "Lemma 2 guarantees that, for at least one of `n = γm` or `γm+1`, `M″_k ≠ 0`", p. 320.)
* **Not the choice of `(α, β, γ)`.**  The bundle is `(9, 19, 9)`, the triple [Zud07] Theorem 1 is
  proved at.  The larger rates found at `(35, 74, 35)` and `(44, 93, 44)`
  (`plans/note-Tshift-S8-WPF.html`) are *computations, not theorems*, and are deliberately absent.
* **Not the threshold.**  It is existentially quantified, because the source computes none.
* **Nothing about `‖(3/2)^k‖`.**  The date bookkeeping `k = 3(βm+1) + j`, the descent, the
  elimination and the endgame are all proved in `TShift/ZudilinTransfer.lean`, not cited.

## Trust ledger

One cited axiom, `Zudilin.padeData`, on the authority of [Zud07] (6)–(11), Lemma 2, Lemma 3,
Lemma 4, (19)–(22) and the constants of p. 321.  Everything else in the file is `std3`.

## Claim level

Cited.  Each clause is independently checkable against `papers/Zudilin2007.pdf`, and every
rounding is recorded above with its direction and its cost.

## References

* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)^k‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.  In repo: `papers/Zudilin2007.pdf`.
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308 — the previous rate, `0.57434`, and the sibling bundle `CITED/HabsiegerPade.lean`.
* [Beu81] F. Beukers, *Fractional parts of powers of rationals*, Math. Proc. Cambridge Philos.
  Soc. **90** (1981), 13–20 — the Padé construction [Zud07] modifies (Remark 1).
* `plans/note-Tshift-S1-WP7.html` — the source audit this file freezes: §2 (the two-form check),
  §3 (the threshold), §4 (the surrogate table).
-/

namespace Zudilin

/-! ## 1. The frozen constants

Real numerals throughout, so that a consumer compares bases with `norm_num` and never meets
`Real.exp`. -/

/-- `≤ e^{C₂}`, the base of the content bound (21).  Rounded **down**, from the printed
`C₂ = 4.46695926…`: `87.0914921 ≤ e^{4.4669592} = 87.09149215…`, itself below
`e^{C₂} = 87.09149781…`. -/
noncomputable def contentBase : ℝ := 870914921 / 10000000

/-- `≥ e^{C₀}`, the base of the remainder bound (19).  Rounded **up**, from the printed
`C₀ = 3.28973907…`: `26.8358608 ≥ e^{3.28973908} = 26.83586073…`. -/
noncomputable def errorBase : ℝ := 268358608 / 10000000

/-- `≥ e^{C₁}`, the base of the denominator bound (20).  Rounded **up**, from the printed
`C₁ = 35.48665992…`: `2 580 242 883 000 000 ≥ e^{35.48665993} = 2.58024288271…·10¹⁵`. -/
def denomBase : ℝ := 2580242883000000

@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem contentBase_pos : 0 < contentBase := by rw [contentBase]; norm_num

@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem errorBase_pos : 0 < errorBase := by rw [errorBase]; norm_num

@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem denomBase_pos : 0 < denomBase := by rw [denomBase]; norm_num

@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem contentBase_pow_pos (m : ℕ) : 0 < contentBase ^ m := pow_pos contentBase_pos m

@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem denomBase_pow_pos (m : ℕ) : 0 < denomBase ^ m := pow_pos denomBase_pos m

/-! ## 2. The bundle -/

/-- **The construction data of [Zud07] at parameter `m`**, in two-column form, at the columns
`2^{57m+3}` and `3^{57m+3}` — the date `N = 3(βm + 1)` from which the whole block
`k = N, …, N + 3β − 1` is reached.

The two forms sit at the Padé indices `n = 9m` and `n + 1`; the two contents are genuinely
different integers (`Φ` and `Φ′/gcd(Φ′, 9m+1)`), and what (21)–(22) supplies for both is the
common lower bound `contentBase ^ m`. -/
structure PadeData (m : ℕ) where
  /-- First coefficient of the form at index `9m`. -/
  a₁ : ℤ
  /-- Second coefficient of the form at index `9m`. -/
  b₁ : ℤ
  /-- Content of the form at index `9m` (the paper's `Φ`). -/
  Γ₁ : ℤ
  /-- First coefficient of the form at index `9m + 1`. -/
  a₂ : ℤ
  /-- Second coefficient of the form at index `9m + 1`. -/
  b₂ : ℤ
  /-- Content of the form at index `9m + 1` (the paper's `Φ′/(γm+1)`, cleared to an integer). -/
  Γ₂ : ℤ
  /-- Lemma 2 at `x = 9`, with the `T`-terms cancelled: the determinant, in absolute value, as the
  printed product of binomial coefficients.  No sign is asserted. -/
  det_eq : |a₁ * b₂ - a₂ * b₁|
    = 3 ^ (m + 3)
      * ((Nat.choose (27 * m + 1) (18 * m) * Nat.choose (37 * m) (10 * m) : ℕ) : ℤ)
  /-- Lemma 3 at index `9m`. -/
  dvd_a₁ : Γ₁ ∣ a₁
  /-- Lemma 3 at index `9m`. -/
  dvd_b₁ : Γ₁ ∣ b₁
  /-- Lemma 4 at index `9m + 1`. -/
  dvd_a₂ : Γ₂ ∣ a₂
  /-- Lemma 4 at index `9m + 1`. -/
  dvd_b₂ : Γ₂ ∣ b₂
  /-- (21)–(22) at index `9m`. -/
  content₁ : contentBase ^ m ≤ (Γ₁ : ℝ)
  /-- (21)–(22) at index `9m + 1`. -/
  content₂ : contentBase ^ m ≤ (Γ₂ : ℝ)
  /-- (9) at `z = 1/9` cleared, with (19), at index `9m`. -/
  size₁ : |(a₁ : ℝ) * 2 ^ (57 * m + 3) + (b₁ : ℝ) * 3 ^ (57 * m + 3)|
    ≤ 2 ^ (57 * m + 3) * 3 ^ (m + 1) * errorBase ^ m
  /-- (9) at `z = 1/9` cleared, with (19), at index `9m + 1`. -/
  size₂ : |(a₂ : ℝ) * 2 ^ (57 * m + 3) + (b₂ : ℝ) * 3 ^ (57 * m + 3)|
    ≤ 2 ^ (57 * m + 3) * 3 ^ (m + 1) * errorBase ^ m
  /-- (20) at index `9m`. -/
  coeff₁ : |(b₁ : ℝ)| ≤ denomBase ^ m
  /-- (20) at index `9m + 1`. -/
  coeff₂ : |(b₂ : ℝ)| ≤ denomBase ^ m

/-- **The cited axiom.**  Beyond some threshold, [Zud07]'s construction supplies the bundle above.

The existential is the honest transcription of a proof that runs through the limits (19), (20),
(21): the source's own Theorem 1 reads "for `k ≥ K`, where `K` is a certain effective constant",
and computes no `K`.  Making the threshold explicit is a research task, not a transcription one —
it needs an explicit lower bound for `Φ(9m, 19m, 9m)` at finite `m` and explicit versions of
(19)/(20); see `plans/note-Tshift-S1-WP7.html` §3 and `plans/note-Tshift-S8-WPA.html` §7 (F7).

Recorded on the authority of [Zud07] (6)–(11), Lemma 2, Lemma 3, Lemma 4, (19)–(22) and p. 321;
the source statements are quoted in the module docstring, together with every rounding and its
direction.  One axiom, quantified over `m` — not a family. -/
@[category research solved, AMS 11, ref "Zud07", group "tshift_s1"]
axiom padeData : ∃ M : ℕ, ∀ m : ℕ, M < m → Nonempty (PadeData m)

/-! ## 3. What Lean derives from the bundle

The independence certificate, which the source leaves as an appeal to Lemma 2. -/

namespace PadeData

variable {m : ℕ}

/-- **The two forms are independent.**  Both binomial coefficients of Lemma 2 are positive —
`18m ≤ 27m + 1` and `10m ≤ 37m` — so the determinant recorded by `det_eq` is a nonzero integer.
This is the clause the source discharges by "Lemma 2 guarantees…"; here it is proved. -/
@[category research solved, AMS 11, ref "Zud07", group "tshift_s1"]
theorem det_ne_zero (F : PadeData m) : F.a₁ * F.b₂ ≠ F.a₂ * F.b₁ := by
  have h1 : 0 < Nat.choose (27 * m + 1) (18 * m) := Nat.choose_pos (by omega)
  have h2 : 0 < Nat.choose (37 * m) (10 * m) := Nat.choose_pos (by omega)
  have hpos : (0 : ℤ) < 3 ^ (m + 3)
      * ((Nat.choose (27 * m + 1) (18 * m) * Nat.choose (37 * m) (10 * m) : ℕ) : ℤ) := by
    have : (0 : ℤ) < ((Nat.choose (27 * m + 1) (18 * m)
        * Nat.choose (37 * m) (10 * m) : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos h1 h2
    positivity
  have habs : |F.a₁ * F.b₂ - F.a₂ * F.b₁| ≠ 0 := by
    rw [F.det_eq]
    exact ne_of_gt hpos
  intro hcon
  exact habs (by rw [hcon, sub_self, abs_zero])

/-- The contents are positive, since `contentBase ^ m` is. -/
@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem content₁_pos (F : PadeData m) : (0 : ℝ) < (F.Γ₁ : ℝ) :=
  lt_of_lt_of_le (contentBase_pow_pos m) F.content₁

/-- The contents are positive, since `contentBase ^ m` is. -/
@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem content₂_pos (F : PadeData m) : (0 : ℝ) < (F.Γ₂ : ℝ) :=
  lt_of_lt_of_le (contentBase_pow_pos m) F.content₂

/-- The content bound in the absolute-value form an elimination step asks for. -/
@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem content₁_abs (F : PadeData m) : contentBase ^ m ≤ |(F.Γ₁ : ℝ)| := by
  rw [abs_of_pos F.content₁_pos]
  exact F.content₁

/-- The content bound in the absolute-value form an elimination step asks for. -/
@[category API, AMS 11, ref "Zud07", group "tshift_s1"]
theorem content₂_abs (F : PadeData m) : contentBase ^ m ≤ |(F.Γ₂ : ℝ)| := by
  rw [abs_of_pos F.content₂_pos]
  exact F.content₂

end PadeData

end Zudilin
