/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Basic
import SRS.MixedBaseRepresentation
import Mathlib.Tactic.Ring

/-!
# The Collatz-simulating SRS `𝒯` (YAH §3, equations (8)–(7); the 11-rule system)

[YAH] build a string-rewriting system `𝒯` over the 7 symbols `{f, t, 0, 1, 2, ◁, ▷}` that simulates
the iterated **accelerated Collatz function** `T(n) = n/2` (n even), `(3n+1)/2` (n odd). A positive
integer is encoded as a mixed-base string (`SRS.MixedBaseRepresentation`): the binary symbols `f, t`
are the digits `0₂, 1₂` and the ternary symbols `0, 1, 2` are `0₃, 1₃, 2₃`; the marker `◁` begins the
string and stands for the (WLOG) most significant digit `1₀`, while `▷` ends it and stands for the
redundant trailing digit `0₁`. Each symbol is the affine map `β_b^n(x) = b·x + n` of the previous
section (equation (8)), so a string is the composite `Γ_N` of these maps.

* `TSym` / `symFun` — the alphabet and the **functional view, equation (8)**: `f(x)=2x`, `t(x)=2x+1`,
  `0(x)=3x`, `1(x)=3x+1`, `2(x)=3x+2`, `◁(x)=1`, `▷(x)=x`, each given as a `beta` map.
* `compFun w` — the composite `Γ_N` of equation (7) for a `𝒯`-string `w` (leftmost symbol innermost),
  the natural number `w` represents (read off at any point: `◁` makes it constant).
* `T` — the accelerated (Terras) Collatz map, with `T_even`/`T_odd` its two cases. (Distinct from the
  standard `3n+1` map `collatzMap` of `SRS.Zantema`; here `T(19) = 29`, cf. Example 3.13.)
* `dynRules` (`𝒟_T`, 2 rules `f▷→▷`, `t▷→2▷`), `auxA` (`𝒜`, 6 rules), `auxB` (`ℬ`, 3 rules),
  `auxRules` (`𝒳 = 𝒜 ∪ ℬ`), `collatzSRS` (`𝒯 = 𝒟_T ∪ 𝒳`) — the **11-rule SRS**.
* `collatzSRS_represents_T` — **`𝒯` represents `T` exactly**: every auxiliary rewrite preserves the
  represented value (the `𝒳`-rules only swap the bases of adjacent positions), while every dynamic
  rewrite at the end of a string replaces its value `v` by `T(v)` (the `𝒟_T`-rules apply one Collatz
  step). So a `𝒯`-derivation runs the Collatz iteration of `T`.
-/

namespace StringRewriting.CollatzSRS

open StringRewriting StringRewriting.MixedBase

/-- The 7-symbol alphabet of `𝒯` ([YAH]): binary digits `f = 0₂`, `t = 1₂`; ternary digits
`d0 = 0₃`, `d1 = 1₃`, `d2 = 2₃`; the begin marker `lhd = ◁` (also the leading digit `1₀`) and the end
marker `rhd = ▷` (also the trailing digit `0₁`). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
inductive TSym | f | t | d0 | d1 | d2 | lhd | rhd
  deriving DecidableEq, Repr

open TSym

/-- **Equation (8)** ([YAH]). The affine map `β_b^n(x) = b·x + n` each symbol stands for (the paper's
"functional view", conflating a symbol with its map): `f(x) = 2x`, `t(x) = 2x+1` (binary digits);
`0(x) = 3x`, `1(x) = 3x+1`, `2(x) = 3x+2` (ternary digits); `◁(x) = 1` (constant — the base-`0`
leading digit `1`) and `▷(x) = x` (identity — the base-`1` trailing digit `0`). Each is a `beta`. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def symFun : TSym → (ℕ → ℕ)
  | f => beta 2 0
  | t => beta 2 1
  | d0 => beta 3 0
  | d1 => beta 3 1
  | d2 => beta 3 2
  | lhd => beta 0 1
  | rhd => beta 1 0

/-- **Equation (7)** for a `𝒯`-string `w = s₁ ⋯ sₖ`: the composite map
`Γ_w = β_{sₖ} ∘ ⋯ ∘ β_{s₁}` (the leftmost symbol applied innermost), as a left fold of `symFun`. For
a well-formed string `◁ ⋯ ▷` this is constant in `x` (the innermost `◁` ignores `x`), and its value
is the natural number the string represents. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def compFun (w : List TSym) (x : ℕ) : ℕ := w.foldl (fun acc s => symFun s acc) x

/-- Splitting a string for `compFun`: the maps of `u` are applied first (innermost), then those of
`v`, so `Γ_{u ++ v}(x) = Γ_v(Γ_u(x))`. This is what lets a local rewrite be analysed in isolation. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
theorem compFun_append (u v : List TSym) (x : ℕ) :
    compFun (u ++ v) x = compFun v (compFun u x) := by
  simp [compFun, List.foldl_append]

/-- The **accelerated (Terras) Collatz function** `T(n) = n/2` if `n` is even, `(3n+1)/2` if `n` is
odd — the map [YAH]'s system `𝒯` iterates. (Not the standard `3n+1` map `collatzMap` of
`SRS.Zantema`: `T` folds the forced division by two into the odd step, e.g. `T(19) = 29`.) -/
@[category API, AMS 11 68, ref "YAH", group "collatz_srs"]
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- On an even input `T` halves: `T(2x) = x`. -/
@[category API, AMS 11, ref "YAH", group "collatz_srs"]
theorem T_even (x : ℕ) : T (2 * x) = x := by simp only [T]; split <;> omega

/-- On an odd input `T` is the accelerated odd step: `T(2x+1) = 3x+2`. -/
@[category API, AMS 11, ref "YAH", group "collatz_srs"]
theorem T_odd (x : ℕ) : T (2 * x + 1) = 3 * x + 2 := by simp only [T]; split <;> omega

/-- The **dynamic rules** `𝒟_T` ([YAH]): `f▷ → ▷` (drop a trailing binary `0`, halving an even
number) and `t▷ → 2▷` (rewrite a trailing binary `1`, applying the odd step). These two rules encode
one application of the Collatz function `T` (cf. `dynRules_applyT`). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def dynRules : System TSym := fun ℓ r =>
  (ℓ = [f, rhd] ∧ r = [rhd]) ∨ (ℓ = [t, rhd] ∧ r = [d2, rhd])

/-- The **auxiliary rules** `𝒜` ([YAH]): `f0→0f`, `f1→0t`, `f2→1f`, `t0→1t`, `t1→2f`, `t2→2t`. Each
swaps a binary symbol past a ternary one (a base swap of two adjacent positions), pushing binary
symbols rightward without changing the value (cf. `auxRules_preserve`). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def auxA : System TSym := fun ℓ r =>
  (ℓ = [f, d0] ∧ r = [d0, f]) ∨ (ℓ = [f, d1] ∧ r = [d0, t]) ∨ (ℓ = [f, d2] ∧ r = [d1, f]) ∨
  (ℓ = [t, d0] ∧ r = [d1, t]) ∨ (ℓ = [t, d1] ∧ r = [d2, f]) ∨ (ℓ = [t, d2] ∧ r = [d2, t])

/-- The **auxiliary rules** `ℬ` ([YAH]): `◁0→◁t`, `◁1→◁ff`, `◁2→◁ft`. These rewrite the leading
ternary digit into binary just after the begin marker `◁`, again preserving the value (the
function-view identities `0(◁)=t(◁)=3`, `1(◁)=f(f(◁))=4`, `2(◁)=t(f(◁))=5`). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def auxB : System TSym := fun ℓ r =>
  (ℓ = [lhd, d0] ∧ r = [lhd, t]) ∨ (ℓ = [lhd, d1] ∧ r = [lhd, f, f]) ∨
  (ℓ = [lhd, d2] ∧ r = [lhd, f, t])

/-- The auxiliary subsystem `𝒳 = 𝒜 ∪ ℬ` ([YAH]): the 9 value-preserving rules. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def auxRules : System TSym := System.union auxA auxB

/-- The full **11-rule SRS `𝒯 = 𝒟_T ∪ 𝒳`** ([YAH]) simulating the Collatz function `T`. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def collatzSRS : System TSym := System.union dynRules auxRules

/-- Every **auxiliary rule preserves the represented value**: for `ℓ → r ∈ 𝒳` the two sides have the
same composite map, `Γ_ℓ = Γ_r`. Each is a base swap (`SRS.MixedBaseRepresentation`'s `baseSwap`)
between adjacent positions; the 9 cases are the function-view identities of equation (8). -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs", formal_uses compFun]
theorem auxRules_preserve (ℓ r : List TSym) (h : auxRules ℓ r) (x : ℕ) :
    compFun ℓ x = compFun r x := by
  rcases h with hA | hB
  · rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil] <;> ring
  · rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil] <;> ring

/-- Every **dynamic rule applies one Collatz step**: for `ℓ → r ∈ 𝒟_T`, `T(Γ_ℓ x) = Γ_r x`. The
`f▷` side is always even (`Γ = 2x`) so `T` halves it to `Γ_▷ = x`; the `t▷` side is always odd
(`Γ = 2x+1`) so `T` sends it to `3x+2 = Γ_{2▷}`. -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs", formal_uses T_even T_odd]
theorem dynRules_applyT (ℓ r : List TSym) (h : dynRules ℓ r) (x : ℕ) :
    T (compFun ℓ x) = compFun r x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [compFun, symFun, beta, List.foldl_cons, List.foldl_nil]
  · rw [show 1 * (2 * x + 0) + 0 = 2 * x by ring, T_even]; ring
  · rw [show 1 * (2 * x + 1) + 0 = 2 * x + 1 by ring, T_odd]; ring

/-- **Auxiliary rewriting preserves the value**, in any context: if `u →_𝒳 v` then `Γ_u = Γ_v`.
Replacing a factor `ℓ` by an equal-composite `r` (`auxRules_preserve`) leaves the whole composite
unchanged, by `compFun_append`. -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses auxRules_preserve compFun_append]
theorem auxRules_rewriteStep_preserve (u v : List TSym)
    (h : RewriteStep auxRules u v) (x : ℕ) : compFun u x = compFun v x := by
  obtain ⟨pre, post, ℓ, r, hrule, rfl, rfl⟩ := h
  simp only [compFun_append]
  rw [auxRules_preserve ℓ r hrule (compFun pre x)]

/-- **Dynamic rewriting at the end of a string applies `T`**: for `ℓ → r ∈ 𝒟_T` and any prefix `pre`,
`T(Γ_{pre ++ ℓ} x) = Γ_{pre ++ r} x`. (The dynamic rules carry the end marker `▷`, so in a
well-formed string they fire only at the right end — empty right context.) -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses dynRules_applyT compFun_append]
theorem dynRules_rewriteStep_applyT (pre ℓ r : List TSym) (hrule : dynRules ℓ r) (x : ℕ) :
    T (compFun (pre ++ ℓ) x) = compFun (pre ++ r) x := by
  simp only [compFun_append]
  exact dynRules_applyT ℓ r hrule (compFun pre x)

/-- **The SRS `𝒯` represents the Collatz function `T` exactly.** Two facts pin down the dynamics:

* every **auxiliary** rewrite (a rule of `𝒳 = 𝒜 ∪ ℬ`, in any context) preserves the represented
  value `Γ` — these rules only reshuffle the digits; and
* every **dynamic** rewrite (a rule of `𝒟_T`, at the end of the string) replaces the value `v` by
  `T(v)` — these rules perform one Collatz step.

Hence a `𝒯`-derivation of `◁ ⋯ ▷` strings computes the orbit of `T`: the auxiliary rules normalise
the representation and the dynamic rules advance the iteration. -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses auxRules_rewriteStep_preserve dynRules_rewriteStep_applyT]
theorem collatzSRS_represents_T :
    (∀ u v, RewriteStep auxRules u v → ∀ x, compFun u x = compFun v x) ∧
    (∀ pre ℓ r, dynRules ℓ r → ∀ x, T (compFun (pre ++ ℓ) x) = compFun (pre ++ r) x) :=
  ⟨fun u v h x => auxRules_rewriteStep_preserve u v h x,
   fun pre ℓ r h x => dynRules_rewriteStep_applyT pre ℓ r h x⟩

/-! ### Example 3.13 ([YAH]): `19 →_𝒯 29` -/

/-- `19 = Val(◁0f1▷)`: the string `◁0f1▷` represents `19` (any evaluation point; `◁` makes it
constant). -/
@[category test, AMS 68 11, ref "YAH", group "collatz_srs"]
theorem compFun_19 : compFun [lhd, d0, f, d1, rhd] 0 = 19 := by decide

/-- After the auxiliary rewrite `f1 → 0t`, the string `◁00t▷` still represents `19` — `𝒳` preserves
the value. -/
@[category test, AMS 68 11, ref "YAH", group "collatz_srs"]
theorem compFun_19' : compFun [lhd, d0, d0, t, rhd] 0 = 19 := by decide

/-- `T(19) = 29 = Val(◁002▷)`: the dynamic rewrite `t▷ → 2▷` advances `◁00t▷` to `◁002▷`, whose value
is `T(19) = 29`. -/
@[category test, AMS 11, ref "YAH", group "collatz_srs"]
theorem compFun_29 : compFun [lhd, d0, d0, d2, rhd] 0 = 29 ∧ T 19 = 29 := by decide

/-- The concrete rewrite `◁0f1▷ →_𝒯 ◁00t▷` (Example 3.13, the auxiliary rule `f1 → 0t` applied in the
context `◁0 _ ▷`) — a single step of `𝒯` that, by `auxRules_rewriteStep_preserve`, keeps the value
`19`. -/
@[category test, AMS 68, ref "YAH", group "collatz_srs"]
theorem rewriteStep_example :
    RewriteStep collatzSRS [lhd, d0, f, d1, rhd] [lhd, d0, d0, t, rhd] := by
  refine ⟨[lhd, d0], [rhd], [f, d1], [d0, t], ?_, rfl, rfl⟩
  exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))

end StringRewriting.CollatzSRS
