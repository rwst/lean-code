/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Mixed-base representations (YAH §3)

To give the Collatz-simulating rewriting system of [YAH] an arithmetical meaning, its strings are
read as numbers in a **mixed-base numeral system** — a positional numeral system whose base may
change from position to position (mixed-radix systems go back to Cantor, [Can69]). The payoff is
that when the least-significant digit is binary the parity of the represented number — hence which
case of the Collatz map applies — can be read off that one digit, instead of scanning the whole
string as one must in unary. Since erasing a trailing binary `0` divides by two and appending a
trailing binary `1` realises `n ↦ 3n + 1`, one Collatz step then becomes a single rewrite step.

* `MixedDigit` — one *symbol* `(n)_b`: a digit `n : ℕ` tagged with the base `b : ℕ` of its position.
  [YAH] "identify the matrix `N` with a string `(n₁)_{b₁} ⋯ (nₖ)_{bₖ}`, where each `(nᵢ)_{bᵢ}` is
  viewed as a single symbol"; here that string is a `List MixedDigit`.
* `IsMixedBaseRep B N` — **Definition 3.11** (mixed-base representation). For a set of bases
  `B ⊆ ℕ`, the string `N : List MixedDigit` is a *mixed `B`-ary representation* when every base lies
  in `B` and every digit **other than the most significant** is bounded by its base (`nᵢ < bᵢ`,
  imposed for `2 ≤ i ≤ k` only). The leading digit `n₁` carries no bound — it may absorb arbitrary
  overflow — so the constraint falls exactly on the tail `N.tail`. The two rows of the paper's
  `2 × k` matrix `N` are recovered as `N.map (·.digit)` (digits) and `N.map (·.base)` (bases).
* `basesProd N` / `Val N` — the value the string represents, **equation (6)** of [YAH]:
  `Val(N) = Σ_{i=1}^{k} nᵢ ∏_{j=i+1}^{k} bⱼ`, each digit weighted by the product (`basesProd`) of the
  bases to its right. Two observations the paper draws from (6): `val_leadingZero` /
  `val_leadingZeros` — prepending zero digits `0_b` leaves the value unchanged, so one may assume
  `n₁ > 0`; and `val_headBase_irrelevant` / `val_replace_headBase_zero` — the leading base `b₁` does
  not affect the value, so it may be set to `0`. The companion `tailBase_pos` records the
  parenthetical "by Definition 3.11 no other base is zero": every base past the first is positive
  (`bᵢ > nᵢ ≥ 0`), which is what makes the canonical choice `b₁ := 0` collision-free.
* `beta b n` / `Gamma N` — the **function view** ([YAH], equation (7)). The symbol `(n)_b` is also
  the affine map `β_b^n(x) = b·x + n` (the paper conflates the two, writing `n_b`), and the whole
  string is the composite `Γ_N = β_{bₖ}^{nₖ} ∘ ⋯ ∘ β_{b₁}^{n₁}` (leftmost symbol innermost).
  `gamma_eq` is the rearrangement of (6) linking the views, `Γ_N(x) = basesProd(N)·x + Val(N)`; in
  canonical form `b₁ = 0` the `x`-term vanishes and `Val(N) = Γ_N(x)` for every `x`
  (`gamma_headBase_zero`). `baseSwap` is the paper's last ingredient: two adjacent symbols' bases may
  be swapped, `β_b^n ∘ β_c^m = β_c^{m'} ∘ β_b^{n'}` with `0 ≤ n' < b` and `0 ≤ m' < c`, without
  changing the composite — hence without changing the represented value.
-/

namespace StringRewriting.MixedBase

/-- A single **symbol** `(n)_b` of a mixed-base numeral: the digit `n` together with the base `b` of
the position it occupies. A mixed-base representation is a string (`List`) of these — [YAH] write the
symbol `(nᵢ)_{bᵢ}` and view it as one letter "denoting the `bᵢ`-ary digit `nᵢ`". -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
structure MixedDigit where
  /-- The digit value `nᵢ`. -/
  digit : ℕ
  /-- The base `bᵢ` of the position this digit occupies. -/
  base : ℕ
  deriving DecidableEq, Repr

/-- **Definition 3.11** (mixed-base representation, [YAH]; mixed-radix numeral systems, [Can69]). Fix
a set of bases `B ⊆ ℕ`. A string `N = (n₁)_{b₁} ⋯ (nₖ)_{bₖ} : List MixedDigit` — equivalently the
paper's `2 × k` matrix with digit row `n₁ ⋯ nₖ` and base row `b₁ ⋯ bₖ` — is a **mixed `B`-ary
representation** when

* every base lies in `B` (`bᵢ ∈ B` for all `i`), and
* every digit except the most significant is bounded by its base (`nᵢ < bᵢ` for `2 ≤ i ≤ k`).

The leading digit `n₁` (`N.head`) is left unconstrained — it may be `≥ b₁`, absorbing arbitrary
overflow — so the bound is imposed exactly on the tail `(n₂)_{b₂} ⋯ (nₖ)_{bₖ}` (`N.tail`). -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
def IsMixedBaseRep (B : Set ℕ) (N : List MixedDigit) : Prop :=
  (∀ s ∈ N, s.base ∈ B) ∧ (∀ s ∈ N.tail, s.digit < s.base)

/-- The empty string is vacuously a mixed `B`-ary representation, for any set of bases `B`. -/
@[category test, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem isMixedBaseRep_nil (B : Set ℕ) : IsMixedBaseRep B [] :=
  ⟨by simp, by simp⟩

/-- A one-symbol string `(n)_b` is a mixed `B`-ary representation as soon as its base `b ∈ B`, with
**no** constraint on the digit `n`. This is the most-significant-digit exception of Definition 3.11
in its purest form: the lone digit is the leading one, so it may be arbitrarily large — even `≥ b`. -/
@[category test, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem isMixedBaseRep_singleton {b : ℕ} {B : Set ℕ} (hb : b ∈ B) (n : ℕ) :
    IsMixedBaseRep B [⟨n, b⟩] :=
  ⟨by simpa using hb, by simp⟩

/-- A concrete mixed binary–ternary representation over `B = {2, 3}`: the string `(1)₂ (2)₃ (1)₂`.
All three bases lie in `B`, and the two tail digits obey their bounds (`2 < 3` and `1 < 2`); the
leading digit needs no check. -/
@[category test, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem isMixedBaseRep_example :
    IsMixedBaseRep {2, 3} [⟨1, 2⟩, ⟨2, 3⟩, ⟨1, 2⟩] := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · fin_cases hs <;> simp
  · simp only [List.tail_cons] at hs
    fin_cases hs <;> simp

/-! ### The value of a representation (YAH equation (6)) -/

/-- `basesProd N` is the product `∏ bⱼ` of the bases of all symbols of `N` (the empty product is
`1`). It is the place value used by `Val`: a digit's weight is `basesProd` of the symbols lying to
its right — everything after it in the string. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
def basesProd : List MixedDigit → ℕ
  | [] => 1
  | s :: rest => s.base * basesProd rest

/-- The empty string has empty base-product `1`. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem basesProd_nil : basesProd [] = 1 := rfl

/-- Defining equation of `basesProd` on a `cons`: factor off the leading symbol's base. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem basesProd_cons (s : MixedDigit) (N : List MixedDigit) :
    basesProd (s :: N) = s.base * basesProd N := rfl

/-- **Equation (6)** ([YAH]). The natural number a mixed-base string `N = (n₁)_{b₁} ⋯ (nₖ)_{bₖ}`
represents:
`Val(N) = Σ_{i=1}^{k} nᵢ · ∏_{j=i+1}^{k} bⱼ`,
each digit `nᵢ` scaled by the product of the bases to its right. Splitting off the `i = 1` term —
whose weight `∏_{j=2}^{k} bⱼ` is `basesProd` of the tail — turns the sum into the head-first
recursion below; note that the leading base `b₁` never enters (cf. `val_headBase_irrelevant`). -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
def Val : List MixedDigit → ℕ
  | [] => 0
  | s :: rest => s.digit * basesProd rest + Val rest

/-- The empty string represents `0`. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_nil : Val [] = 0 := rfl

/-- Head-first recursion for `Val` — the `i = 1` term of equation (6) split off: the leading digit
`n₁` is weighted by `basesProd` of the tail (the product of every base to its right), and the rest
of the string contributes `Val` of the tail. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_cons (s : MixedDigit) (N : List MixedDigit) :
    Val (s :: N) = s.digit * basesProd N + Val N := rfl

/-- The value of the running example `(1)₂ (2)₃ (1)₂` is `1·(3·2) + 2·2 + 1 = 11`. -/
@[category test, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_example : Val [⟨1, 2⟩, ⟨2, 3⟩, ⟨1, 2⟩] = 11 := by decide

/-- **Leading zeros do not change the value** ([YAH], from equation (6)): prepending a single
most-significant zero digit `(0)_b` — of any base `b` — leaves `Val` unchanged, because its
contribution `0 · basesProd N` vanishes. Iterating (`val_leadingZeros`), one may assume without loss
of generality that the leading digit satisfies `n₁ > 0`. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_leadingZero (b : ℕ) (N : List MixedDigit) : Val (⟨0, b⟩ :: N) = Val N := by
  rw [val_cons]; simp

/-- The block form of `val_leadingZero`: prepending any string `zs` of zero digits (every symbol has
`digit = 0`, with arbitrary bases) leaves the value unchanged. This is the paper's "addition of
leading zeros (symbols `0_b` for any `b`) to a string does not change its value". -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_leadingZeros (zs N : List MixedDigit) (h : ∀ s ∈ zs, s.digit = 0) :
    Val (zs ++ N) = Val N := by
  induction zs with
  | nil => simp
  | cons s zs ih =>
    have hs : s.digit = 0 := h s (by simp)
    rw [List.cons_append, val_cons, hs, Nat.zero_mul, Nat.zero_add]
    exact ih (fun t ht => h t (List.mem_cons_of_mem s ht))

/-- **The leading base `b₁` does not affect the value** ([YAH], from equation (6)): changing the
most-significant symbol's base from `b` to `b'` (its digit and the whole tail fixed) leaves `Val`
unchanged. Indeed `b₁` occurs in no term of (6) — every product `∏_{j=i+1}^{k} bⱼ` starts at
`j ≥ 2` — so it is *definitionally* invisible to `Val` (the equality holds by `rfl`). -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_headBase_irrelevant (n b b' : ℕ) (N : List MixedDigit) :
    Val (⟨n, b⟩ :: N) = Val (⟨n, b'⟩ :: N) := rfl

/-- Consequently the leading base may be canonicalised to `0` ([YAH] "so we replace it by zero").
This is legitimate as a normal form because, by `tailBase_pos`, no *other* base of a mixed-base
representation is `0`. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem val_replace_headBase_zero (n b : ℕ) (N : List MixedDigit) :
    Val (⟨n, b⟩ :: N) = Val (⟨n, 0⟩ :: N) :=
  val_headBase_irrelevant n b 0 N

/-- **By Definition 3.11 no base other than the leading one is zero.** In a mixed `B`-ary
representation `N`, every symbol past the first has `bᵢ > nᵢ ≥ 0`, hence `bᵢ > 0` (the digit bound of
Definition 3.11 applies exactly to the tail). This is what makes setting `b₁ := 0` in
`val_replace_headBase_zero` a faithful canonical form: it cannot collide with a genuine base. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem tailBase_pos {B : Set ℕ} {N : List MixedDigit} (h : IsMixedBaseRep B N)
    {s : MixedDigit} (hs : s ∈ N.tail) : 0 < s.base := by
  have hlt := h.2 s hs
  omega

/-! ### Function view: the maps `β_b^n` and `Γ_N` (YAH equation (7)), and base swapping -/

/-- The affine **function `β_b^n(x) := b·x + n`** that [YAH] attach to a symbol `(n)_b`: applying the
`b`-ary digit `n` shifts the running value by `n` after scaling by the base `b`. The paper conflates
the symbol, the digit, and this function — writing `β_b^n` also as `n_b` — and `beta` is that
function (its argument order matches `β`'s decoration: base `b` first, then digit `n`). -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
def beta (b n : ℕ) : ℕ → ℕ := fun x => b * x + n

/-- **Equation (7)** ([YAH]). The composite-function view of a string
`N = (n₁)_{b₁} ⋯ (nₖ)_{bₖ}`:
`Γ_N(x) := (β_{bₖ}^{nₖ} ∘ β_{bₖ₋₁}^{nₖ₋₁} ∘ ⋯ ∘ β_{b₁}^{n₁})(x)`,
the **leftmost** symbol being applied **innermost**. As a left fold the leftmost symbol is consumed
first, so it is the innermost application — matching the composition above. The value `Val(N)` is
recovered by evaluating `Γ_N` at any point once the leading base is `0` (`gamma_headBase_zero`). -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
def Gamma (N : List MixedDigit) (x : ℕ) : ℕ :=
  N.foldl (fun acc s => beta s.base s.digit acc) x

/-- `Γ_[] = id` (the empty composite). -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_nil (x : ℕ) : Gamma [] x = x := rfl

/-- Peeling off the innermost (leftmost) symbol: `Γ_{(n)_b ∷ N}(x) = Γ_N(β_b^n x)`, i.e. apply the
head's map `x ↦ b·x + n` first, then the rest of the string. -/
@[category API, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_cons (s : MixedDigit) (N : List MixedDigit) (x : ℕ) :
    Gamma (s :: N) x = Gamma N (s.base * x + s.digit) := rfl

/-- **"After rearranging (6)"** ([YAH]): the function view is the affine map
`Γ_N(x) = basesProd(N)·x + Val(N)` — its constant term is exactly the value `Val(N)`, and its linear
coefficient is the product of *all* bases (including the leading `b₁`). This is the bridge between
the string view (`Val`) and the function view (`Γ`); the leading base shows up only in the `x`-term,
which is why setting `b₁ = 0` collapses `Γ_N` to the constant `Val(N)`. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_eq (N : List MixedDigit) (x : ℕ) : Gamma N x = basesProd N * x + Val N := by
  induction N generalizing x with
  | nil => simp [Gamma, basesProd, Val]
  | cons s N ih => rw [gamma_cons, ih, basesProd_cons, val_cons]; ring

/-- If the base-product vanishes (some base is `0`), `Γ_N` is the constant function `Val(N)`: the
linear term `basesProd(N)·x` of `gamma_eq` drops out. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_eq_val_of_basesProd_zero (N : List MixedDigit) (x : ℕ) (h : basesProd N = 0) :
    Gamma N x = Val N := by
  rw [gamma_eq, h]; simp

/-- **Equation (7) in canonical form** ([YAH]): once the leading base is `0` — the innermost map
`β_0^{n₁}(x) = n₁` is constant — the value is `Γ_N(x)` at *any* `x`. (This is what equation (7)
asserts: the leading base does not affect the value, so it is set to `0`, and then `Γ_N` no longer
depends on `x`.) -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_headBase_zero (n : ℕ) (N : List MixedDigit) (x : ℕ) :
    Gamma (⟨n, 0⟩ :: N) x = Val (⟨n, 0⟩ :: N) :=
  gamma_eq_val_of_basesProd_zero _ x (by rw [basesProd_cons]; simp)

/-- The canonical form of the running example `(1)₂ (2)₃ (1)₂` (leading base set to `0`):
`Γ_{(1)₀ (2)₃ (1)₂}(x) = 11` for every `x` — here at `x = 99` — equal to its value (cf.
`val_example`). -/
@[category test, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem gamma_example : Gamma [⟨1, 0⟩, ⟨2, 3⟩, ⟨1, 2⟩] 99 = 11 := by decide

/-- **Base swapping** ([YAH], the last ingredient before the rewriting system). The composite of two
adjacent symbol-maps `β_b^n ∘ β_c^m` (value `b·c·x + b·m + n`) can be rewritten with the two **bases
swapped**, `β_c^{m'} ∘ β_b^{n'}` (value `c·b·x + c·n' + m'`), for suitable digits `0 ≤ n' < b` and
`0 ≤ m' < c` — namely `n' = (b·m + n) / c` and `m' = (b·m + n) % c`. Since the two functions agree at
*every* `x`, swapping the bases of two adjacent positions preserves the value of the whole string.
The hypotheses `n < b`, `m < c` (the symbols are genuine non-leading digits, Definition 3.11) are
what force the new digits back below their bases. -/
@[category research solved, AMS 68 11, ref "YAH", group "mixed_base_representation"]
theorem baseSwap (b c n m : ℕ) (hn : n < b) (hm : m < c) :
    ∃ n' m', n' < b ∧ m' < c ∧ ∀ x, beta b n (beta c m x) = beta c m' (beta b n' x) := by
  have hc : 0 < c := by omega
  refine ⟨(b * m + n) / c, (b * m + n) % c, ?_, Nat.mod_lt _ hc, fun x => ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hc]
    have h1 : b * (m + 1) ≤ b * c := Nat.mul_le_mul_left b hm
    have h2 : b * (m + 1) = b * m + b := by ring
    omega
  · have h : c * ((b * m + n) / c) + (b * m + n) % c = b * m + n := Nat.div_add_mod _ _
    simp only [beta]
    calc b * (c * x + m) + n
        = b * c * x + (b * m + n) := by ring
      _ = b * c * x + (c * ((b * m + n) / c) + (b * m + n) % c) := by rw [h]
      _ = c * (b * x + (b * m + n) / c) + (b * m + n) % c := by ring

end StringRewriting.MixedBase
