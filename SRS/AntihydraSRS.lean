/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.AntihydraSRSaxiom
import SRS.MixedBaseRepresentation
import SRS.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Relation

/-!
# The Antihydra-simulating SRS (mixed-base model)

A string-rewriting model of the **Antihydra** machine — the BB(6) non-halting candidate whose
Turing-machine macro analysis lives in `SRS.AntihydraMachine` (`BusyLean`-based). Its `BusyLean`-free
macro model — the maps `A` / `nextMathState`, the halting predicate `mathHalts`, and the halting
characterization `mathHalts_iff_Aiter_8_2` — is re-exposed in `SRS.AntihydraSRSaxiom` and imported
here. Here we instead use the mixed-base **function view** of `SRS.MixedBaseRepresentation` (the YAH
technique used for the Collatz system in `SRS.CollatzSRS`) to read each string as a number.

The Antihydra iteration is `a ↦ ⌊3a/2⌋` together with a counter `b` that gains `2` on every even step
and loses `1` on every odd step, **halting** when an odd value arrives with `b = 0`. A configuration
is `<w>cᵇ`: a mixed-base string `<w>` of value `Val(<w>) = a`, followed by a unary block of `b`
counter symbols `c`. (The digit symbols are the `beta` maps of `SRS.MixedBaseRepresentation`:
`f = 2x`, `t = 2x+1`, `0/1/2 = 3x+d`, `< = β₀¹` the leading `1`, `> = β₁⁰` the end; `c = β₁⁰` is the
identity, so the counter does not affect the value.)

* `ASym` / `symFun` / `compFun` — the 8-symbol alphabet, equation (8), and the composite value map.
* `countC` — the counter `b` (number of `c`'s).
* `dynRules` (`f▷ → 0▷cc`, `t▷c → 1▷`), `auxA` (transport), `auxB` (boundary), `auxRules`,
  `antihydraSRS` — the rewriting system.
* `macroStep` — the Antihydra macro map `(a, b) ↦ (⌊3a/2⌋, b+2)` (even) / `(⌊3a/2⌋, b−1)` (odd) /
  `none` (odd with `b = 0` — HALT), with `macroStep_even`/`_odd`/`_halt`.
* `antihydraSRS_represents_macro` — **the SRS represents the macro behaviour**: the transport and
  boundary rules preserve both the value `a` and the counter `b`; the even dynamic rule sends value
  `2x ↦ 3x` and `b ↦ b+2`; the odd dynamic rule sends `2x+1 ↦ 3x+1` and `b ↦ b−1` (consuming one
  `c`). `config_even_step`/`config_odd_step` exhibit these as actual rewrites on configurations
  `<w>cᵇ`, and `dynRules_odd_needs_counter` is the halting obstruction (`t▷` with no `c` is not a
  redex). The initial configuration `<fff>` has `(a, b) = (8, 0)` (`initial_config`).
* `nextMathState_halt_condition` — the bridge to the macro model of `SRS.AntihydraSRSaxiom`: that
  model halts (`nextMathState ⟨a, 0⟩ = none`) at an empty counter exactly when `a` is odd — matching
  the SRS halt above (an odd value `t▷` with no `c`).

This model tracks `a = Val(<w>)` directly; the `SRS.AntihydraMachine` model uses a different (padded)
`a`-coordinate, so the two macro maps differ by a coordinate change while describing the same machine.
-/

namespace StringRewriting.AntihydraSRS

open StringRewriting StringRewriting.MixedBase

/-- The 8-symbol alphabet of the Antihydra SRS: binary digits `f = 0₂`, `t = 1₂`; ternary digits
`d0, d1, d2 = 0₃, 1₃, 2₃`; the begin marker `lhd = ◁`; the end marker `rhd = ▷`; and the counter
symbol `c` (a unary tally of the counter `b`). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
inductive ASym | f | t | d0 | d1 | d2 | lhd | rhd | c
  deriving DecidableEq, Repr

open ASym

/-- **Equation (8)** for the Antihydra alphabet: each symbol's affine map `β_b^n(x) = b·x + n`
(`beta` of `SRS.MixedBaseRepresentation`). `f(x)=2x`, `t(x)=2x+1` (binary); `d0/d1/d2(x)=3x+0/1/2`
(ternary); `◁(x)=1`, `▷(x)=x`; and `c(x)=x` (the counter symbol is the identity, so it is invisible
to the value). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def symFun : ASym → (ℕ → ℕ)
  | f => beta 2 0
  | t => beta 2 1
  | d0 => beta 3 0
  | d1 => beta 3 1
  | d2 => beta 3 2
  | lhd => beta 0 1
  | rhd => beta 1 0
  | c => beta 1 0

/-- The composite value map `Γ_w` of a string (equation (7) for this alphabet): the leftmost symbol
is applied innermost, as a left fold of `symFun`. For a configuration `<w>cᵇ` this evaluates to the
represented value `a = Val(<w>)` (at any point, since `◁` makes it constant). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def compFun (w : List ASym) (x : ℕ) : ℕ := w.foldl (fun acc s => symFun s acc) x

/-- Peeling off the innermost (leftmost) symbol. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem compFun_cons (s : ASym) (w : List ASym) (x : ℕ) :
    compFun (s :: w) x = compFun w (symFun s x) := rfl

/-- Splitting a string for `compFun`: `Γ_{u ++ v}(x) = Γ_v(Γ_u(x))`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem compFun_append (u v : List ASym) (x : ℕ) :
    compFun (u ++ v) x = compFun v (compFun u x) := by
  simp [compFun, List.foldl_append]

/-- The counter symbol `c` is the identity map. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem symFun_c (x : ℕ) : symFun c x = x := by simp [symFun, beta]

/-- A block of counter symbols is value-transparent: `Γ_{cʲ}(x) = x`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem compFun_replicate_c (j x : ℕ) : compFun (List.replicate j c) x = x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, compFun_cons, symFun_c]; exact ih x

/-- Appending a counter block does not change a string's value (`c` is the identity). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem compFun_append_replicate_c (w : List ASym) (j x : ℕ) :
    compFun (w ++ List.replicate j c) x = compFun w x := by
  rw [compFun_append, compFun_replicate_c]

/-- The counter `b` of a string: the number of counter symbols `c` it contains. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def countC : List ASym → ℕ
  | [] => 0
  | s :: rest => (if s = c then 1 else 0) + countC rest

/-- Defining equation of `countC` on a `cons`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem countC_cons (s : ASym) (w : List ASym) :
    countC (s :: w) = (if s = c then 1 else 0) + countC w := rfl

/-- The counter is additive over concatenation. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem countC_append (u v : List ASym) : countC (u ++ v) = countC u + countC v := by
  induction u with
  | nil => simp [countC]
  | cons s u ih => simp only [List.cons_append, countC, ih]; ring

/-- The **dynamic rules** of the Antihydra SRS: `f▷ → 0▷cc` (even step — turn the trailing binary
`0` into ternary `0`, the value `2x ↦ 3x`, and grow the counter by `2`) and `t▷c → 1▷` (odd step —
the value `2x+1 ↦ 3x+1`, consuming one counter `c`, so `b ↦ b−1`). The odd rule needs a `c`: when
`b = 0` it cannot fire — that is the halt (`dynRules_odd_needs_counter`). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def dynRules : System ASym := fun ℓ r =>
  (ℓ = [f, rhd] ∧ r = [d0, rhd, c, c]) ∨ (ℓ = [t, rhd, c] ∧ r = [d1, rhd])

/-- The **transport rules** `𝒜` (value-preserving base swaps): `f0→0f`, `f1→0t`, `f2→1f`, `t0→1t`,
`t1→2f`, `t2→2t`. They push binary symbols toward the boundary `▷` without changing the value. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def auxA : System ASym := fun ℓ r =>
  (ℓ = [f, d0] ∧ r = [d0, f]) ∨ (ℓ = [f, d1] ∧ r = [d0, t]) ∨ (ℓ = [f, d2] ∧ r = [d1, f]) ∨
  (ℓ = [t, d0] ∧ r = [d1, t]) ∨ (ℓ = [t, d1] ∧ r = [d2, f]) ∨ (ℓ = [t, d2] ∧ r = [d2, t])

/-- The **boundary rules** `ℬ` (value-preserving): `◁0→◁t`, `◁1→◁ff`, `◁2→◁ft`, rewriting the leading
ternary digit into binary just after `◁`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def auxB : System ASym := fun ℓ r =>
  (ℓ = [lhd, d0] ∧ r = [lhd, t]) ∨ (ℓ = [lhd, d1] ∧ r = [lhd, f, f]) ∨
  (ℓ = [lhd, d2] ∧ r = [lhd, f, t])

/-- The value-preserving subsystem `𝒳 = 𝒜 ∪ ℬ` (transport ∪ boundary). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def auxRules : System ASym := System.union auxA auxB

/-- The full **Antihydra SRS** `𝒟 ∪ 𝒳` (dynamic ∪ value-preserving rules). -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def antihydraSRS : System ASym := System.union dynRules auxRules

/-- The **Antihydra macro step** on a state `(a, b)`: the value advances by `a ↦ ⌊3a/2⌋ = 3·a/2`,
the counter gains `2` on an even value and loses `1` on an odd value, and the machine **halts**
(`none`) exactly when an odd value meets an empty counter `b = 0`. -/
@[category API, AMS 11 68, ref "YAH", group "antihydra_srs"]
def macroStep : ℕ × ℕ → Option (ℕ × ℕ)
  | (a, b) => if a % 2 = 0 then some (3 * a / 2, b + 2)
              else if b = 0 then none else some (3 * a / 2, b - 1)

/-- The even branch of the Antihydra map: `(2x, b) ↦ (3x, b+2)` (here `3·(2x)/2 = 3x`). -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem macroStep_even (x b : ℕ) : macroStep (2 * x, b) = some (3 * x, b + 2) := by
  simp [macroStep]; omega

/-- The odd, non-halting branch: `(2x+1, b+1) ↦ (3x+1, b)` (here `3·(2x+1)/2 = 3x+1`, `b ↦ b−1`). -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem macroStep_odd (x b : ℕ) : macroStep (2 * x + 1, b + 1) = some (3 * x + 1, b) := by
  rw [macroStep]; simp [show (2 * x + 1) % 2 = 1 from by omega]; omega

/-- The halting branch: an odd value with an empty counter halts. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem macroStep_halt (x : ℕ) : macroStep (2 * x + 1, 0) = none := by
  rw [macroStep]; simp [show (2 * x + 1) % 2 = 1 from by omega]

/-- A **configuration** `<w>cᵇ`: the mixed-base string `◁ w ▷` (value `a = Val(<w>)`) followed by a
unary block of `b` counter symbols. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
def config (w : List ASym) (b : ℕ) : List ASym := lhd :: (w ++ rhd :: List.replicate b c)

/-- The value of a configuration is independent of the counter: `Val(<w>cᵇ) = Val(<w>) = a`. -/
@[category API, AMS 68, ref "YAH", group "antihydra_srs"]
theorem cfgVal (w : List ASym) (b x : ℕ) :
    compFun (config w b) x = compFun (lhd :: (w ++ [rhd])) x := by
  rw [config, compFun_cons,
      show w ++ rhd :: List.replicate b c = (w ++ [rhd]) ++ List.replicate b c from by simp,
      compFun_append_replicate_c, ← compFun_cons]

/-- Every **transport/boundary rule preserves the value**: for `ℓ → r ∈ 𝒳` the two sides have equal
composite maps. (The 9 cases are the function-view identities of equation (8).) -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs"]
theorem auxRules_preserve_value (ℓ r : List ASym) (h : auxRules ℓ r) (x : ℕ) :
    compFun ℓ x = compFun r x := by
  rcases h with hA | hB
  · rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil] <;> ring
  · rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil] <;> ring

/-- Every transport/boundary rule preserves the counter (none of them mentions `c`). -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs"]
theorem auxRules_preserve_count (ℓ r : List ASym) (h : auxRules ℓ r) :
    countC ℓ = countC r := by
  rcases h with hA | hB
  · rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- **Transport/boundary rewriting preserves the value** in any context. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses auxRules_preserve_value compFun_append]
theorem auxRules_rewriteStep_preserve_value (u v : List ASym)
    (h : RewriteStep auxRules u v) (x : ℕ) : compFun u x = compFun v x := by
  obtain ⟨pre, post, ℓ, r, hrule, rfl, rfl⟩ := h
  simp only [compFun_append]
  rw [auxRules_preserve_value ℓ r hrule (compFun pre x)]

/-- **Transport/boundary rewriting preserves the counter** in any context. -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs",
  formal_uses auxRules_preserve_count countC_append]
theorem auxRules_rewriteStep_preserve_count (u v : List ASym)
    (h : RewriteStep auxRules u v) : countC u = countC v := by
  obtain ⟨pre, post, ℓ, r, hrule, rfl, rfl⟩ := h
  simp only [countC_append]
  rw [auxRules_preserve_count ℓ r hrule]

/-- **The even dynamic rule `f▷ → 0▷cc` realizes `(a, b) ↦ (3·(a/2), b+2)` on an even value.**
Reading `p = Val` of the prefix, the value before is `2p` and after is `3p` (i.e. `2x ↦ 3x`), and the
counter grows by `2`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses compFun_append countC_append]
theorem dynEven (pre : List ASym) (x : ℕ) :
    compFun (pre ++ [f, rhd]) x = 2 * compFun pre x ∧
    compFun (pre ++ [d0, rhd, c, c]) x = 3 * compFun pre x ∧
    countC (pre ++ [d0, rhd, c, c]) = countC (pre ++ [f, rhd]) + 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [compFun_append]; simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil]; ring
  · rw [compFun_append]; simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil]; ring
  · rw [countC_append, countC_append]; simp [countC]

/-- **The odd dynamic rule `t▷c → 1▷` realizes `(a, b) ↦ (3·(a/2)+1, b−1)` on an odd value.**
The value before is `2p+1` and after `3p+1` (i.e. `2x+1 ↦ 3x+1`), and one counter `c` is consumed
(`b ↦ b−1`). -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses compFun_append countC_append]
theorem dynOdd (pre : List ASym) (x : ℕ) :
    compFun (pre ++ [t, rhd, c]) x = 2 * compFun pre x + 1 ∧
    compFun (pre ++ [d1, rhd]) x = 3 * compFun pre x + 1 ∧
    countC (pre ++ [t, rhd, c]) = countC (pre ++ [d1, rhd]) + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [compFun_append]; simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil]; ring
  · rw [compFun_append]; simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil]; ring
  · rw [countC_append, countC_append]; simp [countC]

/-- **The Antihydra SRS represents the macro behaviour.** Three facts pin down the dynamics on a
configuration's state `(a, b) = (value, counter)`:

* every **transport/boundary** rewrite (a rule of `𝒳`, in any context) preserves both the value `a`
  and the counter `b`;
* the **even dynamic rule** `f▷ → 0▷cc` sends value `2x ↦ 3x` (`= ⌊3a/2⌋` for the even `a = 2x`) and
  counter `b ↦ b+2`;
* the **odd dynamic rule** `t▷c → 1▷` sends value `2x+1 ↦ 3x+1` (`= ⌊3a/2⌋` for the odd `a = 2x+1`)
  and counter `b ↦ b−1`, consuming one `c`.

These are exactly the branches of `macroStep`; so a derivation of the Antihydra SRS runs the
Antihydra iteration `a ↦ ⌊3a/2⌋` while tracking the counter `b`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses auxRules_rewriteStep_preserve_value auxRules_rewriteStep_preserve_count dynEven dynOdd]
theorem antihydraSRS_represents_macro :
    (∀ u v, RewriteStep auxRules u v → (∀ x, compFun u x = compFun v x) ∧ countC u = countC v) ∧
    (∀ pre x, compFun (pre ++ [f, rhd]) x = 2 * compFun pre x ∧
              compFun (pre ++ [d0, rhd, c, c]) x = 3 * compFun pre x ∧
              countC (pre ++ [d0, rhd, c, c]) = countC (pre ++ [f, rhd]) + 2) ∧
    (∀ pre x, compFun (pre ++ [t, rhd, c]) x = 2 * compFun pre x + 1 ∧
              compFun (pre ++ [d1, rhd]) x = 3 * compFun pre x + 1 ∧
              countC (pre ++ [t, rhd, c]) = countC (pre ++ [d1, rhd]) + 1) :=
  ⟨fun u v h => ⟨auxRules_rewriteStep_preserve_value u v h, auxRules_rewriteStep_preserve_count u v h⟩,
   dynEven, dynOdd⟩

/-- The even macro step as an actual rewrite on configurations: `<w f>cᵇ →  <w 0>c^{b+2}`. The
counter visibly grows by `2`; the value goes `2x ↦ 3x` (`dynEven`, `cfgVal`). -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs"]
theorem config_even_step (w : List ASym) (b : ℕ) :
    RewriteStep antihydraSRS (config (w ++ [f]) b) (config (w ++ [d0]) (b + 2)) := by
  refine ⟨lhd :: w, List.replicate b c, [f, rhd], [d0, rhd, c, c],
    Or.inl (Or.inl ⟨rfl, rfl⟩), ?_, ?_⟩
  · simp [config, List.append_assoc]
  · simp [config, List.replicate_succ, List.append_assoc]

/-- The odd macro step as an actual rewrite on configurations: `<w t>c^{b+1} →  <w 1>cᵇ`. One
counter `c` is consumed (`b+1 ↦ b`); the value goes `2x+1 ↦ 3x+1` (`dynOdd`, `cfgVal`). -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs"]
theorem config_odd_step (w : List ASym) (b : ℕ) :
    RewriteStep antihydraSRS (config (w ++ [t]) (b + 1)) (config (w ++ [d1]) b) := by
  refine ⟨lhd :: w, List.replicate b c, [t, rhd, c], [d1, rhd],
    Or.inl (Or.inr ⟨rfl, rfl⟩), ?_, ?_⟩
  · simp [config, List.replicate_succ, List.append_assoc]
  · simp [config, List.append_assoc]

/-- **Halting**: an odd value at the boundary with no counter left, `…t▷` (no `c`), is not a dynamic
redex — the odd rule `t▷c → 1▷` needs a `c` after `t▷`, so when `b = 0` it cannot fire. -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs"]
theorem dynRules_odd_needs_counter (r : List ASym) : ¬ dynRules [t, rhd] r := by
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

/-- **Bridge to the macro model** (`SRS.AntihydraSRSaxiom`): with an empty counter, the Antihydra
macro model halts (`nextMathState ⟨a, 0⟩ = none`) exactly when the value `a` is odd. This matches the
SRS halt of `dynRules_odd_needs_counter`: an odd value `t▷` with no `c` left is the halting
configuration `…t▷`. -/
@[category research solved, AMS 11 68, ref "bbchallenge", group "antihydra_srs"]
theorem nextMathState_halt_condition (a : ℕ) (ha : 2 ≤ a) :
    nextMathState { a := a, b := 0 } = none ↔ a % 2 = 1 := by
  unfold nextMathState
  simp only [show a / 2 ≥ 1 from by omega, if_true, beq_iff_eq]
  by_cases h : a % 2 = 0
  · simp [h]
  · simp [h]; omega

/-- The **initial configuration** `<fff>` represents `(a, b) = (8, 0)`: `8 = 1000₂` and the counter
is empty. -/
@[category test, AMS 68 11, ref "YAH", group "antihydra_srs"]
theorem initial_config : compFun (config [f, f, f] 0) 0 = 8 ∧ countC (config [f, f, f] 0) = 0 := by
  decide

/-! ### Strategy-independence of the counter

The Antihydra value orbit `a ↦ ⌊3a/2⌋` is **deterministic** (it is a function, `valStep` /
`valOrbit`), so the sequence of step parities — hence the number of even steps `eⱼ` preceding the
`j`-th odd step — is fixed by the initial value `a₀` alone, independent of any rewriting choices. A
*rewriting strategy* is the freedom in how the value-preserving rules `𝒳` are interleaved between
dynamic steps; `auxDeriv_preserve_count` shows that **any** such interleaving (a `→*`-derivation of
any length, in any context) leaves the counter unchanged, and each dynamic step shifts it by a fixed
parity-determined amount (`dynEven` / `dynOdd`: `+2` even, `−1` odd). Consequently the counter after
the `j`-th odd step is the determined value `b₀ + 2eⱼ − j` (`counterZ_after_jth_odd`, in additive
integer form `b₀ + 2n − 3j` at the `n`-th step) — the same for every strategy.

(The one ingredient still missing for a *fully* faithful statement — that an SRS derivation's
dynamic-step parities really do follow the value orbit, i.e. the auxiliary system normalizes the
representation so the trailing binary digit equals the parity of `a` — is the simulation layer,
deferred. The pieces here are the per-step invariants that, granting that simulation, pin the
counter down.)
-/

/-- **Aux derivations preserve the value.** Any `→*`-derivation using only the value-preserving rules
`𝒳` (a transport/boundary "rewriting strategy", in any context, of any length) leaves the represented
value unchanged. Lifts `auxRules_rewriteStep_preserve_value` along `Relation.ReflTransGen`. -/
@[category research solved, AMS 68 11, ref "YAH", group "antihydra_srs",
  formal_uses auxRules_rewriteStep_preserve_value]
theorem auxDeriv_preserve_value (u v : List ASym)
    (h : Relation.ReflTransGen (RewriteStep auxRules) u v) (x : ℕ) :
    compFun u x = compFun v x := by
  induction h with
  | refl => rfl
  | tail _ step ih => rw [ih]; exact auxRules_rewriteStep_preserve_value _ _ step x

/-- **The counter is strategy-independent between dynamic steps.** Any `→*`-derivation using only the
value-preserving rules `𝒳` — i.e. *any* rewriting strategy, of any length — leaves the counter `b`
unchanged. This is the heart of strategy-independence: a strategy is precisely a choice of how to
apply the `𝒳`-rules, and none of them touch the counter. Lifts
`auxRules_rewriteStep_preserve_count` along `Relation.ReflTransGen`. -/
@[category research solved, AMS 68, ref "YAH", group "antihydra_srs",
  formal_uses auxRules_rewriteStep_preserve_count]
theorem auxDeriv_preserve_count (u v : List ASym)
    (h : Relation.ReflTransGen (RewriteStep auxRules) u v) :
    countC u = countC v := by
  induction h with
  | refl => rfl
  | tail _ step ih => rw [ih]; exact auxRules_rewriteStep_preserve_count _ _ step

/-- The **total Antihydra value map** `a ↦ ⌊3a/2⌋ = 3·a/2` (the first component of `macroStep` on
either parity branch, `macroStep_value`). -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
def valStep (a : ℕ) : ℕ := 3 * a / 2

/-- On either non-halting branch, the value advances by `valStep`: the first component of a successor
state of `macroStep` is `⌊3a/2⌋`, regardless of parity. -/
@[category research solved, AMS 11, ref "YAH", group "antihydra_srs"]
theorem macroStep_value {a b a' b' : ℕ} (h : macroStep (a, b) = some (a', b')) :
    a' = valStep a := by
  simp only [macroStep] at h
  unfold valStep
  split_ifs at h <;> simp_all [Prod.ext_iff]

/-- The **deterministic value orbit**: `valOrbit a₀ n` is the value after `n` macro steps from `a₀`
(`valStep` iterated `n` times). It depends only on `a₀` and `n` — never on the rewriting strategy. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
def valOrbit (a₀ : ℕ) : ℕ → ℕ
  | 0 => a₀
  | n + 1 => valStep (valOrbit a₀ n)

/-- One step of the value orbit. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem valOrbit_succ (a₀ n : ℕ) : valOrbit a₀ (n + 1) = valStep (valOrbit a₀ n) := rfl

/-- The number of **even** steps among the first `n` of the orbit from `a₀`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
def evenSteps (a₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evenSteps a₀ n + (if valOrbit a₀ n % 2 = 0 then 1 else 0)

/-- The number of **odd** steps among the first `n` of the orbit from `a₀`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
def oddSteps (a₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSteps a₀ n + (if valOrbit a₀ n % 2 = 0 then 0 else 1)

/-- The **counter after `n` macro steps** from initial counter `b₀`, along the orbit from `a₀`. Kept
in `ℤ` so the `−1` on an odd step never truncates; each step adds `+2` (even value) or `−1` (odd
value) — exactly the counter change of `dynEven` / `dynOdd`. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
def counterZ (b₀ : ℤ) (a₀ : ℕ) : ℕ → ℤ
  | 0 => b₀
  | n + 1 => counterZ b₀ a₀ n + (if valOrbit a₀ n % 2 = 0 then 2 else -1)

/-- One step of the counter orbit: the increment is `+2` / `−1` by the parity of the current value —
the same increment the dynamic rules `dynEven` / `dynOdd` produce on a configuration. -/
@[category API, AMS 11, ref "YAH", group "antihydra_srs"]
theorem counterZ_succ (b₀ : ℤ) (a₀ n : ℕ) :
    counterZ b₀ a₀ (n + 1) =
      counterZ b₀ a₀ n + (if valOrbit a₀ n % 2 = 0 then 2 else -1) := rfl

/-- Every macro step is even or odd: `eₙ + oₙ = n`. -/
@[category research solved, AMS 11, ref "YAH", group "antihydra_srs"]
theorem evenSteps_add_oddSteps (a₀ n : ℕ) : evenSteps a₀ n + oddSteps a₀ n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evenSteps, oddSteps]
    by_cases h : valOrbit a₀ n % 2 = 0 <;> simp [h] <;> omega

/-- **Closed form of the counter.** After `n` macro steps the counter is `b₀ + 2eₙ − oₙ`, where `eₙ`,
`oₙ` are the even / odd step counts of the deterministic orbit. -/
@[category research solved, AMS 11, ref "YAH", group "antihydra_srs"]
theorem counterZ_closed (b₀ : ℤ) (a₀ n : ℕ) :
    counterZ b₀ a₀ n = b₀ + 2 * (evenSteps a₀ n : ℤ) - (oddSteps a₀ n : ℤ) := by
  induction n with
  | zero => simp [counterZ, evenSteps, oddSteps]
  | succ n ih =>
    simp only [counterZ, evenSteps, oddSteps, ih]
    by_cases h : valOrbit a₀ n % 2 = 0 <;> simp [h] <;> ring

/-- **The counter after the `j`-th odd step is strategy-independent.** If the `n`-th macro step is the
`j`-th odd one (`oddSteps a₀ n = j`), the counter is `b₀ + 2n − 3j` — a value fixed by the initial
counter `b₀`, the step index `n`, and `j` alone (equivalently `b₀ + 2eⱼ − j` with `eⱼ = n − j` the
determined number of preceding even steps). Because the value orbit is deterministic, `n` and `j` do
not depend on how the value-preserving rules were interleaved (`auxDeriv_preserve_count`), so neither
does the counter. -/
@[category research solved, AMS 11 68, ref "YAH", group "antihydra_srs",
  formal_uses counterZ_closed evenSteps_add_oddSteps]
theorem counterZ_after_jth_odd (b₀ : ℤ) (a₀ n j : ℕ) (hj : oddSteps a₀ n = j) :
    counterZ b₀ a₀ n = b₀ + 2 * (n : ℤ) - 3 * (j : ℤ) := by
  have he : evenSteps a₀ n + oddSteps a₀ n = n := evenSteps_add_oddSteps a₀ n
  rw [counterZ_closed, hj]
  have hev : (evenSteps a₀ n : ℤ) = (n : ℤ) - j := by
    have hsum : evenSteps a₀ n + j = n := by rw [← hj]; exact he
    omega
  rw [hev]; ring

end StringRewriting.AntihydraSRS
