/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Mignotte–Voutier's kit for linear forms in three logarithms

Mignotte and Voutier's *kit* ([MV24], appendix by M. Laurent): an instance-tuned lower
bound for a nonzero linear form `Λ = b₁ log α₁ + b₂ log α₂ − b₃ log α₃` in **three**
logarithms, obtained by Laurent's interpolation-determinant method (Waldschmidt's §7.4
construction).  Unlike the closed-form engines of the corpus ([BW93]
`CITED/BakerWustholz`, [Mat00] `CITED/Matveev`, [Lau08] `CITED/LaurentTwoLogs`,
[Rhi87] `CITED/RhinLogForm`), the kit does not give a single universal constant: for a
given `b`-vector the user runs a **parameter search** (the authors' PARI code,
`github.com/PV-314/lf13-kit`) and the theorem then delivers a **trichotomy** — a
per-instance lower bound `Λ' > ρ^{-KL}`, *or* one of two degeneracies (small coefficients,
or a bounded integer relation among the `bᵢ`).  Certified end-products run at
`10⁷`–`10⁸`-grade coefficients (e.g. `log|Λ| ≥ −8.535×10⁷ log y` at `D = 2`,
`−4.185×10⁷ log y` at `D = 1`) — a further `10³`–`10⁴×` sharper than the closed-form
`n = 3` engines, at the cost of the per-instance search.

This file transcribes `plan-formalize-logforms.html` brief **F-4**: [MV24] Theorem 2.1
restricted to the transcription-friendly regime (rational `α₁,α₂,α₃ > 1`,
multiplicatively independent, real case), as a cited `axiom` with the trichotomy
conclusion; plus the proved companion **split lemma** `lambda_split` that converts a
lower bound on the auxiliary `Λ'` into one on `|Λ|` (the consumer-facing surface); plus
the *instance-certification pattern* documented below.

## The restricted regime and its simplifications (`D = 1`, `w = 2`)

Taking `α₁, α₂, α₃ ∈ ℚ` with `αᵢ > 1` collapses several of the paper's general
quantities, and this file bakes those collapses in (each flagged at its use site):

* `D := [ℚ(α₁,α₂,α₃):ℚ] = 1`.  Hence the paper's `(D+1) log N` becomes `2 log N`, the
  factor `2D(K−1) log b/3` becomes `2(K−1) log b/3`, and `2D h(αᵢ) = 2 h(αᵢ)`; since the
  unnormalized height `D·h(αᵢ)` is Mathlib's `Height.logHeight₁ αᵢ` and `D = 1`, we have
  `2D h(αᵢ) = 2 · Height.logHeight₁ αᵢ`.
* `χ_field := [ℝ(α₁,α₂,α₃):ℝ] = 1` (real embedding).  **Do not confuse** this with the
  free real parameter `χ > 0` of condition (2.9)/`V` below — the paper reuses the letter
  `χ` for two unrelated things; only the (2.9) parameter appears here.
* `w`, the maximal order of a root of unity in `ℚ(α₁,α₂,α₃)`, is `2` (roots of unity in
  `ℚ` are `±1`), so the hypothesis `0 < |Λ| < 2π/w` reads `|Λ| < π` (the footnote's
  `Λ ∉ iπℚ` is automatic for a nonzero *real* `Λ`).
* `α₁, α₂, α₃` multiplicatively independent makes the map `(r,s,t) ↦ α₁ʳ α₂ˢ α₃ᵗ`
  injective, so the cardinalities of (2.10)/(2.11) equal the box sizes
  `(R₁+1)(S₁+1)(T₁+1)` / `(R₂+1)(S₂+1)(T₂+1)`; those two conditions are transcribed in
  their collapsed product form (`hCard1`, `hCard2`).

The **WLOG balance** `b₃|log α₃| = b₁|log α₁| + b₂|log α₂| ± |Λ|` of the paper is *not* a
separate hypothesis here: with `αᵢ > 1` (so `|log αᵢ| = log αᵢ`) and the `(+,+,−)` sign
convention of `Λ`, it holds by definition (`b₃ log α₃ = b₁ log α₁ + b₂ log α₂ − Λ`).

## Notation (paper §2.2)

`Nval`, `g`, `factProd`, `bMV`, `Vval`, `Mval`, `LambdaPrime` transcribe, respectively,
`N = K(K+1)L/2`, `g = −1/4 + N/(12RST)`, `∏_{k=1}^{K−1}(k!)^{K−k}`, the quantity `b` of
eq. (2.5), `V = √((R₁+1)(S₁+1)(T₁+1))`, `M = max{R₁+S₁+1, S₁+T₁+1, R₁+T₁+1, χV}`, and the
`Λ'` of the conclusion.  Two cautions from the plan's pitfall list:

* the factorial normalization `(∏_k (k!)^{K−k})^{−12/(K(K−1)(K+1))}` in `bMV` **differs
  from the BMS-I ancestor** ([BMS06] §12) — the constants are *not* interchangeable
  across the two papers, and MV24 supersedes BMS06 §12 (Thm 12.9), whose arXiv-v1 also
  carries typos;
* the conclusion bounds `Λ'`, **not** `|Λ|`; `lambda_split` is the bridge.

## The trichotomy is load-bearing

`three_logs_kit` concludes `Λ' > ρ^{-KL}  ∨  (2.14)  ∨  (2.15)`.  To extract a
transcendence bound a consumer must **positively exclude** the small-coefficients
alternative (2.14) and the integer-relation alternative (2.15), then apply `lambda_split`.
In particular the kit must **never** be cited for a `b`-vector carrying a small integer
relation `u₁b₁+u₂b₂+u₃b₃=0` — e.g. the `‖(3/2)ᵏ‖` shape `b = (k,1,k)` has the relation
`(1,0,−1)`, so (2.15) is trivially satisfied and the kit yields nothing (plan §3(b)).

## Instance-certification pattern (the sanctioned mode of use)

Because the constants are instance-tuned, the intended workflow — how [MV24] themselves
certify e.g. `log|Λ| ≥ −8.535×10⁷ log y` — is: run the authors' PARI kit
(`github.com/PV-314/lf13-kit`) offline for the target `b`-vector to produce a parameter
tuple `(K,L,R,S,T,Rᵢ,Sᵢ,Tᵢ,ρ,χ)` satisfying (2.7)–(2.13) and excluding (2.14)/(2.15),
then record the resulting numeric inequality as its own cited `axiom` (à la
`Rhin.logForm_lower_bound`) **with the parameter tuple written into its docstring**, so
conditions (2.7)–(2.13) are independently re-checkable.  `three_logs_kit` is the general
template that such an instance discharges; no closed `(2,3,·)` instance is provided here
(there is none without the search).

## References

* [MV24] M. Mignotte, P. Voutier, "A kit for linear forms in three logarithms," with an
  appendix by M. Laurent.  *Math. Comp.* (2024; final volume/pages to be verified — this
  transcription follows arXiv:2205.08899v3, the accepted version).  Theorem 2.1 and
  notation §2.2–2.3, pp. 4–6.  PARI code: `github.com/PV-314/lf13-kit`.  Read in full
  2026-07-09.
* [BMS06] Y. Bugeaud, M. Mignotte, S. Siksek, "Classical and modular approaches to
  exponential Diophantine equations I." *Ann. of Math.* **163** (2006), 969–1018, §12
  (Thm 12.9, the three-log ancestor superseded here).
* [Lau08], [Mat00], [BW93], [Rhi87] — the corpus's other log-form engines; see
  `CITED/LaurentTwoLogs.lean`, `CITED/Matveev.lean`, `CITED/BakerWustholz.lean`,
  `CITED/RhinLogForm.lean`.
* `plan-formalize-logforms.html` §4 brief F-4 (this repository).
-/

namespace MV

/-- `N = K(K+1)L/2` (paper §2.2): the size of the index set of the interpolation
determinant, also the lower bound required of `RST`. -/
@[category API, AMS 11, ref "MV24"]
noncomputable def Nval (K L : ℕ) : ℝ := (K : ℝ) * (K + 1) * L / 2

/-- `g = −1/4 + N/(12RST)` (paper eq. (2.2)).  Note `g < 0` (since `RST ≥ N` forces
`N/(12RST) ≤ 1/12`), so the term `gL(a₁R+a₂S+a₃T)` of (2.8) is *negative*. -/
@[category API, AMS 11, ref "MV24"]
noncomputable def g (K L R S T : ℕ) : ℝ := -1 / 4 + Nval K L / (12 * R * S * T)

/-- The factorial product `∏_{k=1}^{K−1} (k!)^{K−k}` appearing in the normalization of the
quantity `b` of eq. (2.5). -/
@[category API, AMS 11, ref "MV24"]
noncomputable def factProd (K : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 (K - 1), (Nat.factorial k : ℝ) ^ (K - k)

/-- The quantity `b` of [MV24] eq. (2.5):
`b = (b'₃ η₀)(b''₃ ζ₀) · (∏_{k=1}^{K−1}(k!)^{K−k})^{−12/(K(K−1)(K+1))}`, with
`b'₃ = b₃/gcd(b₁,b₃)`, `b''₃ = b₃/gcd(b₂,b₃)`, `β₁ = b₁/b₃`, `β₂ = b₂/b₃`,
`η₀ = (R−1)/2 + β₁(T−1)/2`, `ζ₀ = (S−1)/2 + β₂(T−1)/2` (eqs. (2.3), (2.4)).  It enters
only through `log b` on the right of condition (2.8).  **The factorial normalization
differs from the BMS-I ancestor** — see the module doc. -/
@[category API, AMS 11, ref "MV24"]
noncomputable def bMV (b₁ b₂ b₃ : ℤ) (K R S T : ℕ) : ℝ :=
  let d₁ : ℝ := (Int.gcd b₁ b₃ : ℝ)
  let d₂ : ℝ := (Int.gcd b₂ b₃ : ℝ)
  let η₀ : ℝ := ((R : ℝ) - 1) / 2 + ((b₁ : ℝ) / (b₃ : ℝ)) * ((T : ℝ) - 1) / 2
  let ζ₀ : ℝ := ((S : ℝ) - 1) / 2 + ((b₂ : ℝ) / (b₃ : ℝ)) * ((T : ℝ) - 1) / 2
  ((b₃ : ℝ) / d₁ * η₀) * ((b₃ : ℝ) / d₂ * ζ₀) *
    (factProd K) ^ (-(12 : ℝ) / ((K : ℝ) * (K - 1) * (K + 1)))

/-- `V = √((R₁+1)(S₁+1)(T₁+1))` (paper §2.3, before condition (2.9)). -/
@[category API, AMS 11, ref "MV24"]
noncomputable def Vval (R₁ S₁ T₁ : ℕ) : ℝ :=
  Real.sqrt (((R₁ : ℝ) + 1) * ((S₁ : ℝ) + 1) * ((T₁ : ℝ) + 1))

/-- `M = max{R₁+S₁+1, S₁+T₁+1, R₁+T₁+1, χV}` (paper conditions (2.9), (2.15)); `χ > 0` is
the *free parameter* of (2.9), not the field's real-degree indicator. -/
@[category API, AMS 11, ref "MV24"]
noncomputable def Mval (R₁ S₁ T₁ : ℕ) (χ : ℝ) : ℝ :=
  max (max (max ((R₁ : ℝ) + S₁ + 1) ((S₁ : ℝ) + T₁ + 1)) ((R₁ : ℝ) + T₁ + 1)) (χ * Vval R₁ S₁ T₁)

/-- The auxiliary form `Λ' := |Λ| · L T e^{LT|Λ|/(2b₃)} / (2b₃)` of the conclusion of
[MV24] Theorem 2.1.  The theorem lower-bounds `Λ'`; `lambda_split` converts that to a
bound on `|Λ|`. -/
@[category API, AMS 11, ref "MV24"]
noncomputable def LambdaPrime (Λ L T b₃ : ℝ) : ℝ :=
  |Λ| * (L * T * Real.exp (L * T * |Λ| / (2 * b₃))) / (2 * b₃)

/-- **Mignotte–Voutier's kit, Theorem 2.1** ([MV24], p. 5), restricted to the
transcription-friendly regime: `α₁,α₂,α₃ ∈ ℚ` with `αᵢ > 1` (real, positive logs),
multiplicatively independent; `b₁,b₂,b₃` positive with `gcd(b₁,b₂,b₃) = 1`; and the form
`Λ = b₁ log α₁ + b₂ log α₂ − b₃ log α₃ ≠ 0` with `|Λ| < π` (the `2π/w` bound at `w = 2`).

Given integer parameters `K ≥ 3`, `L ≥ 5`, `R,S,T`, and the triples `R₁R₂R₃`, `S₁S₂S₃`,
`T₁T₂T₃`, a real `ρ ≥ 2`, a free real `χ > 0`, and upper bounds `a₁,a₂,a₃` for
`(ρ−1)log αᵢ + 2·logHeight₁ αᵢ` (the `aᵢ ≥ ρ|log αᵢ| − log|αᵢ| + 2D h(αᵢ)` of the paper at
`D = 1`), suppose `RST ≥ N`, the partition conditions (2.7), the analytic condition (2.8),
and the geometric conditions (2.9)–(2.13) — with (2.10)/(2.11) in their multiplicatively
independent collapsed product form — all hold.  Then the **trichotomy**:
`Λ' > ρ^{−KL}`, or the small-coefficient degeneracy (2.14), or a bounded primitive integer
relation (2.15) among the `bᵢ`.

Recorded as a cited `axiom` on the authority of [MV24] (a Laurent interpolation-determinant
estimate we do not re-derive).  The trichotomy is **load-bearing**: a consumer must
exclude (2.14) and (2.15) — see the module doc and `lambda_split`. -/
@[category research solved, AMS 11, ref "MV24", group "mv_three_logs_kit"]
axiom three_logs_kit
    (α : Fin 3 → ℚ) (hα : ∀ i, 1 < α i)
    (hindep : ∀ c : Fin 3 → ℤ, ∏ i, (α i) ^ (c i) = 1 → ∀ i, c i = 0)
    (b : Fin 3 → ℤ) (hb : ∀ i, 0 < b i)
    (hgcd : Int.gcd (Int.gcd (b 0) (b 1)) (b 2) = 1)
    (Λ : ℝ)
    (hΛdef : Λ = (b 0 : ℝ) * Real.log (α 0) + (b 1 : ℝ) * Real.log (α 1)
      - (b 2 : ℝ) * Real.log (α 2))
    (hΛne : Λ ≠ 0) (hΛsmall : |Λ| < Real.pi)
    (K L R S T : ℕ) (R₁ R₂ R₃ S₁ S₂ S₃ T₁ T₂ T₃ : ℕ)
    (ρ χ : ℝ) (a : Fin 3 → ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hρ : 2 ≤ ρ) (hχ : 0 < χ)
    (hN : Nval K L ≤ (R * S * T : ℕ))
    (ha : ∀ i, (ρ - 1) * Real.log (α i) + 2 * Height.logHeight₁ (α i) ≤ a i)
    (h27R : R₁ + R₂ + R₃ < R) (h27S : S₁ + S₂ + S₃ < S) (h27T : T₁ + T₂ + T₃ < T)
    (h28 : ((K * L : ℕ) / 2 + (L : ℝ) / 2 - 0.37 * K - 2) * Real.log ρ
        ≥ 2 * Real.log (Nval K L)
          + g K L R S T * L * (a 0 * R + a 1 * S + a 2 * T)
          + 2 * ((K : ℝ) - 1) * Real.log (bMV (b 0) (b 1) (b 2) K R S T) / 3)
    (h29 : (K : ℝ) * Mval R₁ S₁ T₁ χ < ((R₁ + 1) * (S₁ + 1) * (T₁ + 1) : ℕ))
    (hCard1 : (L : ℝ) < ((R₁ + 1) * (S₁ + 1) * (T₁ + 1) : ℕ))
    (hCard2 : (2 * K * L : ℕ) < (R₂ + 1) * (S₂ + 1) * (T₂ + 1))
    (h212 : (K ^ 2 : ℕ) < (R₂ + 1) * (S₂ + 1) * (T₂ + 1))
    (h213 : (3 * K ^ 2 * L : ℕ) < (R₃ + 1) * (S₃ + 1) * (T₃ + 1)) :
    LambdaPrime Λ (L : ℝ) (T : ℝ) (b 2 : ℝ) > ρ ^ (-((K : ℝ) * L))
    ∨ ((b 0).natAbs ≤ max R₁ R₂ ∧ (b 1).natAbs ≤ max S₁ S₂ ∧ (b 2).natAbs ≤ max T₁ T₂)
    ∨ (∃ u : Fin 3 → ℤ, u 0 * b 0 + u 1 * b 1 + u 2 * b 2 = 0
        ∧ Int.gcd (Int.gcd (u 0) (u 1)) (u 2) = 1
        ∧ (|u 0| : ℝ) ≤ ((S₁ + 1) * (T₁ + 1) : ℕ) / (Mval R₁ S₁ T₁ χ - (max S₁ T₁ : ℕ))
        ∧ (|u 1| : ℝ) ≤ ((R₁ + 1) * (T₁ + 1) : ℕ) / (Mval R₁ S₁ T₁ χ - (max R₁ T₁ : ℕ))
        ∧ (|u 2| : ℝ) ≤ ((R₁ + 1) * (S₁ + 1) : ℕ) / (Mval R₁ S₁ T₁ χ - (max R₁ S₁ : ℕ)))

/-- **The `Λ' → |Λ|` split lemma** (proved companion, the consumer-facing surface of the
kit).  Writing `x = LT|Λ|/(2b₃)`, the auxiliary form `Λ' = |Λ| · L T eˣ / (2b₃)` satisfies:
either `|Λ| ≥ 2b₃/(LT)` (the exponent `x ≥ 1`, a direct bound), or
`|Λ| ≥ Λ' · 2b₃/(e·LT)` (the exponent `x ≤ 1`, so `eˣ ≤ e`).  Combined with the kit's
`Λ' > ρ^{−KL}`, this turns the conclusion into a genuine lower bound for `|Λ|`.  Requires
only `L, T, b₃ > 0`. -/
@[category research solved, AMS 11, ref "MV24", group "mv_three_logs_kit"]
theorem lambda_split (Λ L T b₃ : ℝ) (hL : 0 < L) (hT : 0 < T) (hb₃ : 0 < b₃) :
    2 * b₃ / (L * T) ≤ |Λ|
      ∨ LambdaPrime Λ L T b₃ * (2 * b₃) / (Real.exp 1 * (L * T)) ≤ |Λ| := by
  set x : ℝ := L * T * |Λ| / (2 * b₃) with hx
  have hLT : 0 < L * T := mul_pos hL hT
  have h2b₃ : 0 < 2 * b₃ := by positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · left
    rw [hx] at hx1
    rw [div_le_iff₀ hLT]
    linarith [(le_div_iff₀ h2b₃).mp hx1]
  · right
    have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_lt hx1)
    have hLP : LambdaPrime Λ L T b₃ = |Λ| * (L * T * Real.exp x) / (2 * b₃) := by
      rw [LambdaPrime, hx]
    rw [hLP, div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp 1 * (L * T))]
    have key : |Λ| * (L * T * Real.exp x) / (2 * b₃) * (2 * b₃)
        = |Λ| * (L * T) * Real.exp x := by field_simp
    rw [key]
    calc |Λ| * (L * T) * Real.exp x
        ≤ |Λ| * (L * T) * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = |Λ| * (Real.exp 1 * (L * T)) := by ring

end MV
