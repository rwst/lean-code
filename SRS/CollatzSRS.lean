/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Basic
import SRS.Interpretation
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

/-! ### Lemma 3.15 ([YAH]): `SN(𝒯 ∖ ℬ)` and `SN(𝒯 ∖ 𝒟_T)` by monotone interpretations

Removing *either* of two rule groups makes `𝒯` terminating, each witnessed by a natural-number
interpretation. The interpretations are read in the leftmost-outermost convention of `strInterp`
(`[σ₁ ⋯ σₙ] = [σ₁] ∘ ⋯ ∘ [σₙ]`, `SRS.Interpretation`), under which the *reversed* system is oriented;
ordinary termination of `𝒯 ∖ ·` then follows by reversal invariance (`terminating_reverse_iff`, the
`S = ∅` case of Lemma 2.8). This mirrors [YAH]'s proof, which exhibits interpretations orienting
`(𝒯 ∖ ℬ)ʳᵉᵛ` and `(𝒯 ∖ 𝒟_T)ʳᵉᵛ` and concludes by Lemma 2.8. Both lemmas are building blocks of the
rule-removal termination argument for `𝒯` (Theorem 2.6). -/

/-- The interpretation `𝔄₁` of **Lemma 3.15** proving `SN(𝒯 ∖ ℬ)` ([YAH]): over `ℕ`,
`[f] = [t] = 2x+1`, `[0] = [1] = [2] = 2x`, `[▷] = x`. The begin marker `[◁]` is irrelevant — no
rule of `𝒯 ∖ ℬ` mentions it — and is set to the identity (any strictly monotone map would do). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def den_noB : TSym → ℕ → ℕ
  | f => fun x => 2 * x + 1
  | t => fun x => 2 * x + 1
  | d0 => fun x => 2 * x
  | d1 => fun x => 2 * x
  | d2 => fun x => 2 * x
  | lhd => id
  | rhd => id

/-- The interpretation `𝔄₂` of **Lemma 3.15** proving `SN(𝒯 ∖ 𝒟_T)` ([YAH]): over `ℕ`,
`[f] = [t] = [◁] = x+1`, `[0] = [1] = [2] = 4x`. The end marker `[▷]` is irrelevant — no rule of
`𝒯 ∖ 𝒟_T` mentions it — and is set to the identity. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def den_noD : TSym → ℕ → ℕ
  | f => fun x => x + 1
  | t => fun x => x + 1
  | lhd => fun x => x + 1
  | d0 => fun x => 4 * x
  | d1 => fun x => 4 * x
  | d2 => fun x => 4 * x
  | rhd => id

/-- The common engine of **Lemma 3.15**: a per-symbol `ℕ`-interpretation `den`, strictly monotone in
each symbol (`hmono`), whose value strictly **drops across every reversed rule** of `Rsub`
(`[r̄](x) < [ℓ̄](x)` for `ℓ → r ∈ Rsub`, `hrule`), proves `SN(Rsub)`. The interpretation makes the
induced order `>_𝔄` a reduction order (Theorem 2.12, `interpOrder_isReductionOrder`) that orients
`Rsubʳᵉᵛ` (Theorem 2.11, `terminating_iff_exists_reductionOrder`); reversal invariance
(`terminating_reverse_iff`) transfers termination back to `Rsub`. -/
private theorem sn_of_interp (Rsub : System TSym) (den : TSym → ℕ → ℕ)
    (hmono : ∀ σ a b, a > b → den σ a > den σ b)
    (hrule : ∀ ℓ r, Rsub ℓ r → ∀ x, strInterp den r.reverse x < strInterp den ℓ.reverse x) :
    Terminating (RewriteStep Rsub) := by
  rw [← terminating_reverse_iff, terminating_iff_exists_reductionOrder]
  refine ⟨interpOrder den (· > ·),
    interpOrder_isReductionOrder den (terminating_of_measure (fun n => n) fun _ _ h => h)
      (fun _ _ _ => gt_trans) hmono, ?_⟩
  intro ℓ r hrev
  rw [system_reverse_iff] at hrev
  obtain ⟨ℓ₀, r₀, hR, rfl, rfl⟩ := hrev
  exact fun x => hrule ℓ₀ r₀ hR x

/-- **Lemma 3.15** ([YAH]), first half: **`SN(𝒯 ∖ ℬ)`**. Dropping the three `ℬ`-rules
(`◁0→◁t`, `◁1→◁ff`, `◁2→◁ft`) leaves a terminating system. The interpretation `den_noB`
(`[f]=[t]=2x+1`, `[0]=[1]=[2]=2x`, `[▷]=x`) strictly decreases across every reversed rule of
`𝒯 ∖ ℬ` (the `𝒟_T`- and `𝒜`-rules), so `sn_of_interp` applies. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses sn_of_interp den_noB]
theorem terminating_collatzSRS_diff_auxB :
    Terminating (RewriteStep (System.diff collatzSRS auxB)) := by
  refine sn_of_interp _ den_noB ?_ ?_
  · intro σ a b h
    cases σ <;> simp only [den_noB, id_eq] <;> omega
  · rintro ℓ r ⟨hin, hnB⟩ x
    simp only [collatzSRS, auxRules, System.union] at hin
    rcases hin with hdyn | hA | hB
    · simp only [dynRules] at hdyn
      rcases hdyn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          strInterp, Function.comp_apply, den_noB, id_eq] <;> omega
    · simp only [auxA] at hA
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          strInterp, Function.comp_apply, den_noB, id_eq] <;> omega
    · exact absurd hB hnB

/-- **Lemma 3.15** ([YAH]), second half: **`SN(𝒯 ∖ 𝒟_T)`**. Dropping the two dynamic rules
(`f▷→▷`, `t▷→2▷`) leaves a terminating system. The interpretation `den_noD`
(`[f]=[t]=[◁]=x+1`, `[0]=[1]=[2]=4x`) strictly decreases across every reversed rule of `𝒯 ∖ 𝒟_T`
(the `𝒜`- and `ℬ`-rules), so `sn_of_interp` applies. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses sn_of_interp den_noD]
theorem terminating_collatzSRS_diff_dynRules :
    Terminating (RewriteStep (System.diff collatzSRS dynRules)) := by
  refine sn_of_interp _ den_noD ?_ ?_
  · intro σ a b h
    cases σ <;> simp only [den_noD, id_eq] <;> omega
  · rintro ℓ r ⟨hin, hnD⟩ x
    simp only [collatzSRS, auxRules, System.union] at hin
    rcases hin with hdyn | hA | hB
    · exact absurd hdyn hnD
    · simp only [auxA] at hA
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          strInterp, Function.comp_apply, den_noD, id_eq] <;> omega
    · simp only [auxB] at hB
      rcases hB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          strInterp, Function.comp_apply, den_noD, id_eq] <;> omega

/-- **Lemma 3.15** ([YAH]). Both `SN(𝒯 ∖ ℬ)` and `SN(𝒯 ∖ 𝒟_T)` hold: removing either the leading
ternary-rewrite rules `ℬ` or the dynamic rules `𝒟_T` from `𝒯` yields a terminating system. These are
the two component-termination facts feeding the rule-removal proof that `𝒯` simulates `T` without
spurious nontermination. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses terminating_collatzSRS_diff_auxB terminating_collatzSRS_diff_dynRules]
theorem lemma_3_15 :
    Terminating (RewriteStep (System.diff collatzSRS auxB)) ∧
      Terminating (RewriteStep (System.diff collatzSRS dynRules)) :=
  ⟨terminating_collatzSRS_diff_auxB, terminating_collatzSRS_diff_dynRules⟩

/-! ### Lemma 3.16 ([YAH]): reduction to the canonical form `◁(f|t|0|1|2)*▷`

It suffices to prove termination of `𝒯` on **canonical-form initial strings** `◁(f|t|0|1|2)*▷` (the
well-formed encodings); termination on *all* strings then follows. [YAH] prove this by **type
introduction** ([SZ17], Sabel–Zantema): give the types `𝕋 = {ρ, σ, τ}` with
`◁ : σ → τ`, `f,t,0,1,2 : σ → σ`, `▷ : ρ → σ`, under which `𝒯` is well-typed (all rules have
non-empty left-hand sides), so by **[SZ17, Corollary 3.4]** — *a well-typed SRS is string terminating
iff it is string terminating in the typed setting* — untyped termination equals typed termination.
In the typed setting **Lemma 3.15** (`terminating_collatzSRS_diff_auxB` / `_diff_dynRules`) shows a
string whose source or target type is `σ` cannot start an infinite reduction, so only strings of type
`ρ → τ` can — and those are exactly the canonical-form strings.

[YAH] also give an **elementary proof in Appendix A**, which is the one formalised here. It is by
contrapositive: an infinite `𝒯`-derivation is localized — using that markers `◁, ▷` are *walls* never
created or moved by any rule — to an infinite derivation on a single **marker block** `c N d`
(`N ∈ {f,t,0,1,2}*`, `c, d ∈ {◁, ▷}`); the four shapes are then dispatched by **Lemma 3.15**:
* `▷N▷` contains no `◁`, so only `𝒯 ∖ ℬ`-rules fire — `SN(𝒯 ∖ ℬ)` (`terminatingFrom_no_lhd`);
* `◁N◁` contains no `▷`, so only `𝒯 ∖ 𝒟_T`-rules fire — `SN(𝒯 ∖ 𝒟_T)` (`terminatingFrom_no_rhd`);
* `▷N◁` has its markers at the wrong ends, so only `𝒜`-rules fire — `SN(𝒜)` (`terminating_auxA`);
* `◁N▷` is the canonical form — the only block that can loop.

The block-localization bookkeeping is the **cited axiom** `blockLocalization`; the case analysis it
feeds — the genuine Lemma-3.15 content — is proved (`terminatingFrom_no_lhd`, `terminatingFrom_no_rhd`,
`terminating_auxA`, and `lemma_3_16` itself). -/

/-- The **canonical form** `◁(f|t|0|1|2)*▷` ([YAH]): a begin marker `◁`, then a (possibly empty) block
of binary/ternary digits `f,t,0,1,2`, then an end marker `▷`. These are the well-formed encodings of
natural numbers; Lemma 3.16 reduces termination of `𝒯` to its termination on these. -/
@[category API, AMS 68, ref "YAH", group "collatz_srs"]
def canonicalForm (w : List TSym) : Prop :=
  ∃ mid : List TSym, (∀ s ∈ mid, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) ∧
    w = lhd :: (mid ++ [rhd])

/-- Engine for the elementary cases of Lemma 3.16. If a symbol `c` occurs in the left-hand side of
every rule of a subsystem `Bad ⊆ 𝒯` (`hBadHas`) and is never *created* by a `c`-free rewrite
(`hCreate`), then a `𝒯`-rewrite of a `c`-free string is in fact a `𝒯 ∖ Bad`-rewrite and stays
`c`-free. Iterating, a `c`-free string can only start a `𝒯 ∖ Bad`-derivation. -/
private theorem step_avoid (c : TSym) (Bad : System TSym)
    (hBadHas : ∀ ℓ r, Bad ℓ r → c ∈ ℓ)
    (hCreate : ∀ ℓ r, collatzSRS ℓ r → c ∉ ℓ → c ∉ r)
    {u v : List TSym} (h : RewriteStep collatzSRS u v) (hu : c ∉ u) :
    RewriteStep (System.diff collatzSRS Bad) u v ∧ c ∉ v := by
  obtain ⟨p, q, ℓ, r, hrule, rfl, rfl⟩ := h
  simp only [List.mem_append, not_or] at hu
  obtain ⟨⟨hp, hℓ⟩, hq⟩ := hu
  have hr : c ∉ r := hCreate ℓ r hrule hℓ
  refine ⟨⟨p, q, ℓ, r, ⟨hrule, fun hB => hℓ (hBadHas ℓ r hB)⟩, rfl, rfl⟩, ?_⟩
  simp only [List.mem_append, not_or]
  exact ⟨⟨hp, hr⟩, hq⟩

/-- **Elementary core of Lemma 3.16, no-`◁` case.** A string **not containing the begin marker `◁`**
cannot start an infinite `𝒯`-derivation: no rule creates `◁` and the `ℬ`-rules all need `◁`, so such
a derivation uses only `𝒯 ∖ ℬ`-rules — terminating by **Lemma 3.15**
(`terminating_collatzSRS_diff_auxB`). (Type-theoretically: a string with target type `σ`.) -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses step_avoid terminating_collatzSRS_diff_auxB]
theorem terminatingFrom_no_lhd :
    TerminatingFrom (RewriteStep collatzSRS) (fun w => lhd ∉ w) := by
  have hBadHas : ∀ ℓ r, auxB ℓ r → lhd ∈ ℓ := by
    intro ℓ r hB; simp only [auxB] at hB
    rcases hB with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hCreate : ∀ ℓ r, collatzSRS ℓ r → lhd ∉ ℓ → lhd ∉ r := by
    intro ℓ r hrule hℓ
    simp only [collatzSRS, auxRules, System.union] at hrule
    rcases hrule with hd | hA | hB
    · simp only [dynRules] at hd
      rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    · simp only [auxA] at hA
      rcases hA with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    · simp only [auxB] at hB
      rcases hB with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp at hℓ
  rintro ⟨s, h0, hstep⟩
  have key : ∀ i, lhd ∉ s i := by
    intro i
    induction i with
    | zero => exact h0
    | succ k ih => exact (step_avoid lhd auxB hBadHas hCreate (hstep k) ih).2
  exact terminating_collatzSRS_diff_auxB
    ⟨s, fun i => (step_avoid lhd auxB hBadHas hCreate (hstep i) (key i)).1⟩

/-- **Elementary core of Lemma 3.16, no-`▷` case.** A string **not containing the end marker `▷`**
cannot start an infinite `𝒯`-derivation: no rule creates `▷` and the dynamic rules `𝒟_T` all need
`▷`, so such a derivation uses only `𝒯 ∖ 𝒟_T`-rules — terminating by **Lemma 3.15**
(`terminating_collatzSRS_diff_dynRules`). (Type-theoretically: a string with source type `σ`.) -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses step_avoid terminating_collatzSRS_diff_dynRules]
theorem terminatingFrom_no_rhd :
    TerminatingFrom (RewriteStep collatzSRS) (fun w => rhd ∉ w) := by
  have hBadHas : ∀ ℓ r, dynRules ℓ r → rhd ∈ ℓ := by
    intro ℓ r hd; simp only [dynRules] at hd
    rcases hd with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hCreate : ∀ ℓ r, collatzSRS ℓ r → rhd ∉ ℓ → rhd ∉ r := by
    intro ℓ r hrule hℓ
    simp only [collatzSRS, auxRules, System.union] at hrule
    rcases hrule with hd | hA | hB
    · simp only [dynRules] at hd
      rcases hd with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp at hℓ
    · simp only [auxA] at hA
      rcases hA with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    · simp only [auxB] at hB
      rcases hB with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  rintro ⟨s, h0, hstep⟩
  have key : ∀ i, rhd ∉ s i := by
    intro i
    induction i with
    | zero => exact h0
    | succ k ih => exact (step_avoid rhd dynRules hBadHas hCreate (hstep k) ih).2
  exact terminating_collatzSRS_diff_dynRules
    ⟨s, fun i => (step_avoid rhd dynRules hBadHas hCreate (hstep i) (key i)).1⟩

/-- `SN(𝒜)` — the auxiliary digit-swap subsystem `𝒜` (= `𝒯 ∖ (ℬ ∪ 𝒟_T)`) is terminating. Since
`𝒜 ⊆ 𝒯 ∖ ℬ` (every `𝒜`-rule is a rule of `𝒯` and is never a `ℬ`-rule), this is immediate from
`SN(𝒯 ∖ ℬ)` (**Lemma 3.15**, `terminating_collatzSRS_diff_auxB`) and `terminating_of_subrelation`.
This is the subsystem of Appendix A's case (iii) (`▷N◁`), where the markers sit at the wrong ends so
neither `ℬ` nor `𝒟_T` can fire and only `𝒜` rewrites the block. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses terminating_of_subrelation terminating_collatzSRS_diff_auxB]
theorem terminating_auxA : Terminating (RewriteStep auxA) := by
  refine terminating_of_subrelation (fun u v h => ?_) terminating_collatzSRS_diff_auxB
  obtain ⟨p, q, ℓ, r, hrule, rfl, rfl⟩ := h
  refine ⟨p, q, ℓ, r, ⟨Or.inr (Or.inl hrule), fun hB => ?_⟩, rfl, rfl⟩
  simp only [auxA] at hrule
  rcases hrule with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [auxB] at hB

/-- `SN(𝒳)` — the full auxiliary subsystem `𝒳 = 𝒜 ∪ ℬ` (= `𝒯 ∖ 𝒟_T`) is terminating. Since `𝒳` is
exactly `𝒯` with the dynamic rules removed (the value-preserving rules are disjoint from `𝒟_T`), this
is `terminating_collatzSRS_diff_dynRules` (**Lemma 3.15**) read through `terminating_of_subrelation`.
It is the termination fact [YAH] invoke for the backward direction of **Theorem 3.17**: along any
infinite `𝒯`-derivation the dynamic rules must fire infinitely often. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses terminating_of_subrelation terminating_collatzSRS_diff_dynRules]
theorem terminating_auxRules : Terminating (RewriteStep auxRules) := by
  refine terminating_of_subrelation (fun u v h => ?_) terminating_collatzSRS_diff_dynRules
  obtain ⟨p, q, ℓ, r, hrule, rfl, rfl⟩ := h
  refine ⟨p, q, ℓ, r, ⟨Or.inr hrule, fun hdyn => ?_⟩, rfl, rfl⟩
  rcases hrule with hA | hB
  · simp only [auxA] at hA
    rcases hA with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩ <;>
      simp [dynRules] at hdyn
  · simp only [auxB] at hB
    rcases hB with ⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩ <;> simp [dynRules] at hdyn

/-- **Block localization** ([YAH], Appendix A) — the combinatorial core of the elementary proof, a
**cited axiom**. If some string admits an infinite `𝒯`-derivation, then so does a single *marker
block* `c N d`: a digit block `N ∈ {f,t,0,1,2}*` flanked by two markers `c, d ∈ {◁, ▷}`, and that
block is **not** of the shape `▷N◁`.

Justification (Appendix A): pad the looping string to `Z = d₀ N₁ d₁ ⋯ N_k d_k`; since no rule of `𝒯`
creates, deletes or moves a marker (`ℬ` keeps its `◁`, `𝒟_T` keeps its `▷`, `𝒜` has none), the markers
are *walls* and every rewrite acts inside a single block — so by pigeonhole (finitely many blocks) some
block `cNd` loops. A `▷N◁` block can only be rewritten by `𝒜`-rules (`𝒯` has no rule `s◁ → t◁` or
`▷s → ▷t`), and `SN(𝒜)` (`terminating_auxA`), so it cannot loop; the three surviving shapes `◁N▷`
(canonical), `▷N▷`, `◁N◁` are returned. Recorded as `cited`: the block-decomposition / pigeonhole
bookkeeping is not formalised here — but the *case analysis* on the three surviving shapes (below) is,
via Lemma 3.15. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses terminating_auxA]
axiom blockLocalization (s : ℕ → List TSym)
    (h : ∀ i, RewriteStep collatzSRS (s i) (s (i + 1))) :
    ∃ (s' : ℕ → List TSym) (N : List TSym),
      (∀ x ∈ N, x = f ∨ x = t ∨ x = d0 ∨ x = d1 ∨ x = d2) ∧
        (∀ i, RewriteStep collatzSRS (s' i) (s' (i + 1))) ∧
        (s' 0 = lhd :: (N ++ [rhd]) ∨ s' 0 = rhd :: (N ++ [rhd]) ∨ s' 0 = lhd :: (N ++ [lhd]))

/-- **Lemma 3.16** ([YAH], elementary proof of Appendix A). If `𝒯` is terminating on all initial
strings of the canonical form `◁(f|t|0|1|2)*▷`, then `𝒯` is terminating on all strings.
*Contrapositive*: an infinite `𝒯`-derivation localizes to an infinite derivation on a marker block
`cNd` (`blockLocalization`); its three possible shapes are each dispatched by **Lemma 3.15** —
`▷N▷` contains no `◁` (`terminatingFrom_no_lhd`, case (i)), `◁N◁` contains no `▷`
(`terminatingFrom_no_rhd`, case (ii)), and `◁N▷` is *canonical*, contradicting the hypothesis. (Case
(iii) `▷N◁` was already excluded by `blockLocalization` via `terminating_auxA`. The paper's main text
instead proves the lemma by type introduction, [SZ17, Corollary 3.4]; see the section note.) -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses blockLocalization terminatingFrom_no_lhd terminatingFrom_no_rhd canonicalForm]
theorem lemma_3_16 (h : TerminatingFrom (RewriteStep collatzSRS) canonicalForm) :
    Terminating (RewriteStep collatzSRS) := by
  rintro ⟨s, hs⟩
  obtain ⟨s', N, hN, hs', hcase⟩ := blockLocalization s hs
  have hNl : lhd ∉ N := fun hm => by have := hN lhd hm; simp at this
  have hNr : rhd ∉ N := fun hm => by have := hN rhd hm; simp at this
  rcases hcase with h0 | h0 | h0
  · exact h ⟨s', by rw [h0]; exact ⟨N, hN, rfl⟩, hs'⟩
  · exact terminatingFrom_no_lhd ⟨s', by rw [h0]; simp [List.mem_append, hNl], hs'⟩
  · exact terminatingFrom_no_rhd ⟨s', by rw [h0]; simp [List.mem_append, hNr], hs'⟩

/-- **Converse of Lemma 3.16** ([YAH], "the converse is obvious"). If `𝒯` is terminating, then it is
terminating on all initial strings of any form — in particular on the canonical form
`◁(f|t|0|1|2)*▷`. This is the trivial restriction `SN(→) → SN(→ from `P`)`
(`terminatingFrom_of_terminating`). Together with `lemma_3_16`, termination of `𝒯` is *equivalent* to
termination on canonical-form strings. -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses terminatingFrom_of_terminating canonicalForm]
theorem lemma_3_16_converse (h : Terminating (RewriteStep collatzSRS)) :
    TerminatingFrom (RewriteStep collatzSRS) canonicalForm :=
  terminatingFrom_of_terminating canonicalForm h

/-- **`𝒯` simulates the iterated application of `T` (except at 1)** ([YAH], closing remark of §3).
Putting the pieces together: along any `𝒯`-derivation the represented value (`compFun`) is an
invariant of the auxiliary rewriting — here in its **iterated** form, preserved along the whole
reflexive–transitive closure of `→_𝒳` — while each dynamic rewrite advances it by exactly one step of
the accelerated Collatz map `T` (`dynRules_rewriteStep_applyT`). So a `𝒯`-derivation of canonical
strings computes the `T`-orbit of the encoded number, the simulation breaking only at the fixed point
`1` (where the encoding's trailing/leading conventions stop matching a further `T`-step). -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses auxRules_rewriteStep_preserve dynRules_rewriteStep_applyT]
theorem collatzSRS_simulates_T :
    (∀ u v, Relation.ReflTransGen (RewriteStep auxRules) u v → ∀ x, compFun u x = compFun v x) ∧
      (∀ pre ℓ r, dynRules ℓ r → ∀ x, T (compFun (pre ++ ℓ) x) = compFun (pre ++ r) x) := by
  refine ⟨fun u v h x => ?_, fun pre ℓ r hr x => dynRules_rewriteStep_applyT pre ℓ r hr x⟩
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih]; exact auxRules_rewriteStep_preserve _ _ hstep x

end StringRewriting.CollatzSRS
