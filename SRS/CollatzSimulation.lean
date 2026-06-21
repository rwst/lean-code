/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.CollatzSRS
import Mathlib.Logic.Function.Iterate

/-!
# Theorem 3.17 ([YAH]): `𝒯` terminates iff the Collatz conjecture holds

The capstone of [YAH]'s Collatz-simulating system `𝒯` (`SRS.CollatzSRS`): the string rewriting
system `𝒯` is **terminating if and only if `T` is convergent** — i.e. iff the **Collatz conjecture**
holds for the accelerated map `T(n) = n/2` (`n` even), `(3n+1)/2` (`n` odd).

[YAH]'s proof reduces — by **Lemma 3.16** (`lemma_3_16`) — to the canonical-form strings
`◁(f|t|0|1|2)*▷`, and runs on three claims about the value `Val(N)` an encoding represents:

* **Claim 1** (`claim_1`) — an auxiliary rewrite `N →_𝒳 N'` preserves `Val`, while a dynamic rewrite
  `N →_{𝒟_T} N'` advances it by one Collatz step. This is exactly `collatzSRS_represents_T` read
  through `Val = compFun · 0`, so `claim_1` is **genuinely proved** here (delegation).
* **Claim 2** (`claim_2`) — a canonical string with `Val = 1` is a `𝒯`-normal form: the simulation
  halts at the fixed point `1`. **Genuinely proved** here (the elementary Appendix-A argument: only
  `◁▷` has value `1`, and `◁▷` is irreducible).
* **Claim 3** (`claim_3`) — from a canonical string with `Val = ν > 1` one can `𝒯`-derive a string
  with `Val = T(ν)`: the simulation advances one `T`-step. **Genuinely proved** here (slide a binary
  symbol to `▷` via `𝒜`-swaps, then one `𝒟_T` step).

`Val` and `TConvergent` are defined here. **Claims 1–3 and Theorem 3.17 are all genuinely proved**
(no `sorry`). Theorem 3.17 rests, beyond the standard axioms, only on two elementary `cited`
*marker-invariant* axioms — `blockLocalization` (via Lemma 3.16) and `canonicalStep`, both the same
"markers are walls" list combinatorics — and on Claims 1–3 and `terminating_auxRules` (`SN(𝒳)`). The
open conjecture is **not** axiomatized: `TConvergent` is only a `Prop` and is never asserted; Theorem
3.17 is the *equivalence* (asserting neither side). Cf. the analogous `Zantema.zantema_theorem_3_2` (`SN(𝒵) ↔ Collatz`),
which the corpus instead discharges structurally via two `research open` lemmas.
-/

namespace StringRewriting.CollatzSRS

open StringRewriting.MixedBase TSym Relation

/-- The **value `Val(N)`** a `𝒯`-string `N` represents: its composite map `Γ_N` (`compFun`) read off
at `0`. For a canonical string `◁ ⋯ ▷` the map is constant in its argument (the innermost `◁` ignores
it), so the evaluation point is irrelevant; `0` is the canonical choice (cf.
`compFun_19 : compFun [◁,0,f,1,▷] 0 = 19`). -/
@[category API, AMS 68, ref "YAH", group "collatz_srs", formal_uses compFun]
def Val (w : List TSym) : ℕ := compFun w 0

/-- **`T` is convergent** ([YAH]): every positive integer reaches `1` under iteration of the
accelerated Collatz map `T`. This is the **Collatz conjecture** — equivalent to
`Zantema.CollatzConjecture` (stated there for the standard `3n+1` map; the accelerated `T` folds the
forced halving into the odd step but has the same convergence behaviour). An **open** problem, stated
here only as a `Prop` and never asserted. -/
@[category API, AMS 11, ref "YAH", group "collatz_srs", formal_uses T]
def TConvergent : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, T^[k] n = 1

/-- **Claim 1** ([YAH], proof of Theorem 3.17). Along any `𝒯`-rewrite the represented value `Val` is
governed by the two rule groups: an **auxiliary** rewrite `N →_𝒳 N'` preserves it (`Val N' = Val N`),
while a **dynamic** rewrite `N →_{𝒟_T} N'` at the end of the string advances it by one Collatz step
(`Val N' = T(Val N)`). This is exactly `collatzSRS_represents_T` read through `Val = compFun · 0`, so
it is **genuinely proved** here (a delegation, not a cited axiom). -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses Val T auxRules_rewriteStep_preserve dynRules_rewriteStep_applyT]
theorem claim_1 :
    (∀ N N', RewriteStep auxRules N N' → Val N' = Val N) ∧
      (∀ pre ℓ r, dynRules ℓ r → Val (pre ++ r) = T (Val (pre ++ ℓ))) := by
  refine ⟨fun N N' h => ?_, fun pre ℓ r h => ?_⟩
  · simpa only [Val] using (auxRules_rewriteStep_preserve N N' h 0).symm
  · simpa only [Val] using (dynRules_rewriteStep_applyT pre ℓ r h 0).symm

/-- Helper for **Claim 2**: a block of digit symbols `{f,t,0,1,2}` never decreases the value it acts
on — `x ≤ Γ_mid(x)` for all `x`. Each digit map (`f,t : x ↦ 2x(+1)`, `0,1,2 : x ↦ 3x(+·)`) is `≥ id`
on `ℕ`; the begin marker `◁` (the constant `1`) is the only symbol that can *decrease* a value, and a
digit block excludes it. Structural recursion on `mid` (using `compFun (s :: rest) = Γ_rest ∘ [s]`). -/
private theorem compFun_digits_ge : ∀ (mid : List TSym),
    (∀ s ∈ mid, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) → ∀ (x : ℕ),
    x ≤ compFun mid x
  | [], _, x => by simp [compFun]
  | s :: rest, hd, x => by
      have hs := hd s (List.mem_cons.mpr (Or.inl rfl))
      have key : compFun (s :: rest) x = compFun rest (symFun s x) := by simp [compFun]
      rw [key]
      have hstep : x ≤ symFun s x := by
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [symFun, beta] <;> omega
      exact le_trans hstep
        (compFun_digits_ge rest (fun s' hs' => hd s' (List.mem_cons.mpr (Or.inr hs'))) (symFun s x))

/-- The value of a canonical string `◁ mid ▷` is `Γ_mid(1)`: the begin marker contributes the constant
`1`, the digit block transforms it, and the end marker `▷` (identity) leaves it unchanged. -/
private theorem val_canonical (mid : List TSym) :
    Val (lhd :: (mid ++ [rhd])) = compFun mid 1 := by
  have e1 : compFun [lhd] 0 = 1 := by decide
  have e2 : ∀ y, compFun [rhd] y = y := fun y => by simp [compFun, symFun, beta]
  simp only [Val]
  rw [show lhd :: (mid ++ [rhd]) = [lhd] ++ mid ++ [rhd] from by simp,
    compFun_append, compFun_append, e1, e2]

/-- **Claim 2** ([YAH], proof of Theorem 3.17). A canonical-form string `N` with `Val(N) = 1` is a
**`𝒯`-normal form**: no rewrite `N →_𝒯 N'` applies, so the simulation halts at the fixed point `1`.

*Proof* (the Appendix-A argument of [YAH]). Writing `N = ◁ mid ▷` one computes `Val(N) = Γ_mid(1)`;
since every digit symbol satisfies `x ≤ [s](x)` and the first one sends `1 ↦ ≥ 2`
(`compFun_digits_ge`), a *non-empty* `mid` forces `Val(N) ≥ 2`. Hence `Val(N) = 1` gives `mid = []`,
i.e. `N = ◁▷`; and `◁▷` (length `2`, second symbol `▷`) matches the left-hand side of no rule of `𝒯`
— every rule has a length-`2` lhs, none equal to `◁▷`. The `canonicalForm` hypothesis is essential:
the non-canonical `t▷` also has value `1` yet rewrites via `t▷ → 2▷`. -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses Val canonicalForm compFun_append]
theorem claim_2 (N : List TSym) (hc : canonicalForm N) (hv : Val N = 1) :
    ¬ ∃ N', RewriteStep collatzSRS N N' := by
  obtain ⟨mid, hmid, rfl⟩ := hc
  rw [val_canonical] at hv
  rcases mid with _ | ⟨s, rest⟩
  · -- `mid = []` : `N = ◁▷` is a normal form
    simp only [List.nil_append]
    rintro ⟨N', p, q, ℓ, r, hrule, heq, -⟩
    have hℓ2 : ℓ.length = 2 := by
      simp only [collatzSRS, auxRules, System.union] at hrule
      rcases hrule with hd | hA | hB
      · simp only [dynRules] at hd; rcases hd with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
      · simp only [auxA] at hA
        rcases hA with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> rfl
      · simp only [auxB] at hB; rcases hB with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> rfl
    have hlen := congrArg List.length heq
    simp only [List.length_cons, List.length_append, List.length_nil, hℓ2] at hlen
    rcases p with _ | ⟨a, pp⟩
    · rcases q with _ | ⟨b, qq⟩
      · simp only [List.nil_append, List.append_nil] at heq
        subst heq
        simp [collatzSRS, auxRules, System.union, dynRules, auxA, auxB] at hrule
      · exfalso; simp only [List.length_cons, List.length_nil] at hlen; omega
    · exfalso; simp only [List.length_cons] at hlen; omega
  · -- `mid = s :: rest` : the value is `≥ 2`, contradicting `Val = 1`
    exfalso
    have hs := hmid s (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ s' ∈ rest, s' = f ∨ s' = t ∨ s' = d0 ∨ s' = d1 ∨ s' = d2 :=
      fun s' hs' => hmid s' (List.mem_cons.mpr (Or.inr hs'))
    have h2 : 2 ≤ symFun s 1 := by rcases hs with rfl|rfl|rfl|rfl|rfl <;> decide
    have hstep : compFun (s :: rest) 1 = compFun rest (symFun s 1) := by simp [compFun]
    have hge : symFun s 1 ≤ compFun rest (symFun s 1) :=
      compFun_digits_ge rest hrest (symFun s 1)
    rw [hstep] at hv
    omega

/-- A single `𝒜`-swap `b·t → t'·b'` exists for every binary `b ∈ {f,t}` and ternary
`t ∈ {0,1,2}`, and the produced symbol `b'` is again binary: the six rules `f0→0f`, `f1→0t`, `f2→1f`,
`t0→1t`, `t1→2f`, `t2→2t` move a binary symbol one step to the right past a ternary one. -/
private theorem swap_exists {b c : TSym} (hb : b = f ∨ b = t) (hc : c = d0 ∨ c = d1 ∨ c = d2) :
    ∃ c' b', (b' = f ∨ b' = t) ∧ auxA [b, c] [c', b'] := by
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl | rfl
  · exact ⟨d0, f, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨d0, t, Or.inr rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨d1, f, Or.inl rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨d1, t, Or.inr rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  · exact ⟨d2, f, Or.inl rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  · exact ⟨d2, t, Or.inr rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩

/-- **Pushing a binary symbol to the end marker** ([YAH], the inner loop of Claim 3's proof). A binary
symbol `b` followed by a block `ts` of ternary symbols and then `▷` can be `𝒜`-rewritten so the binary
symbol ends up immediately before `▷`: `pre · b · ts · ▷ →*_𝒜 pre · ts' · b' · ▷` for some binary
`b'`. By recursion on `ts`, each step applying one swap (`swap_exists`) and recursing under the
extended prefix. -/
private theorem push : ∀ (ts : List TSym), (∀ s ∈ ts, s = d0 ∨ s = d1 ∨ s = d2) →
    ∀ (b : TSym), (b = f ∨ b = t) → ∀ (pre : List TSym),
    ∃ mid' b', (b' = f ∨ b' = t) ∧
      ReflTransGen (RewriteStep auxA) (pre ++ b :: (ts ++ [rhd])) (pre ++ mid' ++ [b', rhd])
  | [], _, b, hb, pre => ⟨[], b, hb, by simpa using ReflTransGen.refl⟩
  | c :: rest, hts, b, hb, pre => by
      have hc : c = d0 ∨ c = d1 ∨ c = d2 := hts c (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ s ∈ rest, s = d0 ∨ s = d1 ∨ s = d2 :=
        fun s hs => hts s (List.mem_cons.mpr (Or.inr hs))
      obtain ⟨c', b', hb', hrule⟩ := swap_exists hb hc
      have step : RewriteStep auxA (pre ++ b :: (c :: rest ++ [rhd]))
          (pre ++ c' :: b' :: (rest ++ [rhd])) := by
        have := (RewriteStep.of_rule hrule).append_context pre (rest ++ [rhd])
        simpa using this
      obtain ⟨mid'', b'', hb'', hreach⟩ := push rest hrest b' hb' (pre ++ [c'])
      refine ⟨c' :: mid'', b'', hb'', ReflTransGen.head step ?_⟩
      have e1 : pre ++ c' :: b' :: (rest ++ [rhd]) = (pre ++ [c']) ++ b' :: (rest ++ [rhd]) := by simp
      have e2 : pre ++ (c' :: mid'') ++ [b'', rhd] = (pre ++ [c']) ++ mid'' ++ [b'', rhd] := by simp
      rw [e1, e2]; exact hreach

/-- **Last-binary decomposition** ([YAH], Claim 3's "the string contains some substring `b·t…t·▷`").
A digit list `m` containing at least one binary symbol splits as `m = pre0 · b · ts` where `b` is a
binary symbol and `ts` (everything after the *last* binary) is all ternary. Structural recursion on
`m`, branching on whether the tail still contains a binary. -/
private theorem last_binary : ∀ (m : List TSym),
    (∀ s ∈ m, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) → (∃ s ∈ m, s = f ∨ s = t) →
    ∃ pre0 b ts, (b = f ∨ b = t) ∧ (∀ s ∈ ts, s = d0 ∨ s = d1 ∨ s = d2) ∧ m = pre0 ++ b :: ts
  | [], _, hbin => by simp at hbin
  | x :: rest, hm, hbin => by
      by_cases hr : ∃ s ∈ rest, s = f ∨ s = t
      · obtain ⟨pre0, b, ts, hb, hts, heq⟩ :=
          last_binary rest (fun s hs => hm s (List.mem_cons.mpr (Or.inr hs))) hr
        exact ⟨x :: pre0, b, ts, hb, hts, by rw [heq, List.cons_append]⟩
      · have hx : x = f ∨ x = t := by
          obtain ⟨s, hs, hsb⟩ := hbin
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact hsb
          · exact absurd ⟨s, hs', hsb⟩ hr
        have hts : ∀ s ∈ rest, s = d0 ∨ s = d1 ∨ s = d2 := by
          intro s hs
          rcases hm s (List.mem_cons.mpr (Or.inr hs)) with h | h | h | h | h
          · exact absurd ⟨s, hs, Or.inl h⟩ hr
          · exact absurd ⟨s, hs, Or.inr h⟩ hr
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        exact ⟨[], x, rest, hx, hts, rfl⟩

/-- **Reaching a binary-before-`▷` configuration** ([YAH], Claim 3). If the digit block `m` of a
canonical string `◁ m ▷` contains a binary symbol, then `◁ m ▷` `𝒳`-rewrites (only swap rules `𝒜`) to
a string `pre · b · ▷` with `b` binary — ready for a dynamic step. Combines `last_binary` (locate the
last binary, with an all-ternary suffix) and `push` (slide it to the end), lifting the `𝒜`-derivation
to `𝒳 = auxRules`. -/
private theorem reach_contains_binary (m : List TSym)
    (hm : ∀ s ∈ m, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) (hbin : ∃ s ∈ m, s = f ∨ s = t) :
    ∃ pre b, (b = f ∨ b = t) ∧
      ReflTransGen (RewriteStep auxRules) (lhd :: (m ++ [rhd])) (pre ++ [b, rhd]) := by
  obtain ⟨pre0, b, ts, hb, hts, rfl⟩ := last_binary m hm hbin
  obtain ⟨mid', b', hb', hpush⟩ := push ts hts b hb (lhd :: pre0)
  have lift : ∀ u v, RewriteStep auxA u v → RewriteStep auxRules u v := by
    rintro u v ⟨p, q, ℓ, r, hr, rfl, rfl⟩
    exact ⟨p, q, ℓ, r, Or.inl hr, rfl, rfl⟩
  refine ⟨(lhd :: pre0) ++ mid', b', hb', ?_⟩
  have hsrc : lhd :: ((pre0 ++ b :: ts) ++ [rhd]) = (lhd :: pre0) ++ b :: (ts ++ [rhd]) := by simp
  rw [hsrc]
  exact hpush.mono lift

/-- **Reaching a binary-before-`▷` configuration, in general** ([YAH], Claim 3). For a *non-empty*
digit block `mid`, the canonical string `◁ mid ▷` `𝒳`-rewrites to some `pre · b · ▷` with `b` binary.
If `mid` already has a binary symbol this is `reach_contains_binary`; otherwise `mid` is all ternary,
and a `ℬ`-rule `◁c → ◁(binary…)` fires on the leading ternary symbol to create a binary, reducing to
the previous case. -/
private theorem reach_binary_end (mid : List TSym)
    (hmid : ∀ s ∈ mid, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) (hne : mid ≠ []) :
    ∃ pre b, (b = f ∨ b = t) ∧
      ReflTransGen (RewriteStep auxRules) (lhd :: (mid ++ [rhd])) (pre ++ [b, rhd]) := by
  by_cases hbin : ∃ s ∈ mid, s = f ∨ s = t
  · exact reach_contains_binary mid hmid hbin
  · obtain ⟨c, rest', rfl⟩ : ∃ c rest', mid = c :: rest' := by
      cases mid with
      | nil => exact absurd rfl hne
      | cons c rest' => exact ⟨c, rest', rfl⟩
    have hc : c = d0 ∨ c = d1 ∨ c = d2 := by
      rcases hmid c (List.mem_cons.mpr (Or.inl rfl)) with h | h | h | h | h
      · exact absurd ⟨c, List.mem_cons.mpr (Or.inl rfl), Or.inl h⟩ hbin
      · exact absurd ⟨c, List.mem_cons.mpr (Or.inl rfl), Or.inr h⟩ hbin
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hrest' : ∀ s ∈ rest', s = d0 ∨ s = d1 ∨ s = d2 := by
      intro s hs
      rcases hmid s (List.mem_cons.mpr (Or.inr hs)) with h | h | h | h | h
      · exact absurd ⟨s, List.mem_cons.mpr (Or.inr hs), Or.inl h⟩ hbin
      · exact absurd ⟨s, List.mem_cons.mpr (Or.inr hs), Or.inr h⟩ hbin
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨bs', hrule, hallbin, hsomebin⟩ :
        ∃ bs', auxB [lhd, c] (lhd :: bs') ∧ (∀ s ∈ bs', s = f ∨ s = t) ∧ ∃ s ∈ bs', s = f ∨ s = t := by
      rcases hc with rfl | rfl | rfl
      · exact ⟨[t], Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩
      · exact ⟨[f, f], Or.inr (Or.inl ⟨rfl, rfl⟩), by decide, by decide⟩
      · exact ⟨[f, t], Or.inr (Or.inr ⟨rfl, rfl⟩), by decide, by decide⟩
    have hstepB : RewriteStep auxRules (lhd :: (c :: rest' ++ [rhd]))
        (lhd :: (bs' ++ rest' ++ [rhd])) := by
      have hr : auxRules [lhd, c] (lhd :: bs') := Or.inr hrule
      have := (RewriteStep.of_rule hr).append_context [] (rest' ++ [rhd])
      simpa using this
    have hnew : ∀ s ∈ bs' ++ rest', s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2 := by
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · rcases hallbin s h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (hrest' s h))
    have hbinnew : ∃ s ∈ bs' ++ rest', s = f ∨ s = t := by
      obtain ⟨s, hs, hsb⟩ := hsomebin
      exact ⟨s, List.mem_append.mpr (Or.inl hs), hsb⟩
    obtain ⟨pre, b, hbbin, hreach⟩ := reach_contains_binary (bs' ++ rest') hnew hbinnew
    exact ⟨pre, b, hbbin, ReflTransGen.head hstepB hreach⟩

/-- **Claim 3** ([YAH], proof of Theorem 3.17). From a canonical-form string `N` representing `ν > 1`
one can run the simulation one `T`-step: there is a string `N'` with `N →*_𝒯 N'` and `Val(N') = T(ν)`.

*Proof* (the constructive argument of [YAH]). Since `ν > 1`, the digit block of `N` is non-empty, so
by `reach_binary_end` the auxiliary `𝒳`-rules rewrite `N` to a string `pre · b · ▷` with `b` binary
(the `𝒜`-swaps slide a binary symbol rightward to the end marker, or a `ℬ`-rule first creates one) —
value-preserving (`collatzSRS_simulates_T`), so still `Val = ν`. Then the dynamic rule `f▷ → ▷`
(if `b = f`) or `t▷ → 2▷` (if `b = t`) fires at the end, sending the value to `T(ν)` by Claim 1
(`dynRules_rewriteStep_applyT`). Genuinely proved — the `canonicalForm` and `ν > 1` hypotheses are
both used (`ν > 1` to force the block non-empty, `canonicalForm` for the marker layout `◁ … ▷`). -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses Val T canonicalForm reach_binary_end collatzSRS_simulates_T dynRules_rewriteStep_applyT]
theorem claim_3 (ν : ℕ) (hν : 1 < ν) (N : List TSym) (hc : canonicalForm N) (hv : Val N = ν) :
    ∃ N', Relation.ReflTransGen (RewriteStep collatzSRS) N N' ∧ Val N' = T ν := by
  obtain ⟨mid, hmid, rfl⟩ := hc
  have hne : mid ≠ [] := by
    rintro rfl
    have h1 : Val (lhd :: ([] ++ [rhd])) = 1 := by decide
    omega
  obtain ⟨pre, b, hbbin, hreach⟩ := reach_binary_end mid hmid hne
  have hvalpre : Val (pre ++ [b, rhd]) = ν := by
    have h := collatzSRS_simulates_T.1 _ _ hreach 0
    simp only [Val] at hv ⊢
    rw [← h]; exact hv
  have lift2 : ∀ u v, RewriteStep auxRules u v → RewriteStep collatzSRS u v := by
    rintro u v ⟨p, q, ℓ, r, hr, rfl, rfl⟩
    exact ⟨p, q, ℓ, r, Or.inr hr, rfl, rfl⟩
  have hreach' : ReflTransGen (RewriteStep collatzSRS) (lhd :: (mid ++ [rhd])) (pre ++ [b, rhd]) :=
    hreach.mono lift2
  rcases hbbin with rfl | rfl
  · refine ⟨pre ++ [rhd], hreach'.tail ?_, ?_⟩
    · have hr : collatzSRS [f, rhd] [rhd] := Or.inl (Or.inl ⟨rfl, rfl⟩)
      have := (RewriteStep.of_rule hr).append_context pre []
      simpa using this
    · have h := dynRules_rewriteStep_applyT pre [f, rhd] [rhd] (Or.inl ⟨rfl, rfl⟩) 0
      simp only [Val] at hvalpre ⊢
      rw [← h, hvalpre]
  · refine ⟨pre ++ [d2, rhd], hreach'.tail ?_, ?_⟩
    · have hr : collatzSRS [t, rhd] [d2, rhd] := Or.inl (Or.inr ⟨rfl, rfl⟩)
      have := (RewriteStep.of_rule hr).append_context pre []
      simpa using this
    · have h := dynRules_rewriteStep_applyT pre [t, rhd] [d2, rhd] (Or.inr ⟨rfl, rfl⟩) 0
      simp only [Val] at hvalpre ⊢
      rw [← h, hvalpre]

/-- A canonical string represents a **positive** value: `Val(◁ mid ▷) = Γ_mid(1) ≥ 1`
(`val_canonical` + `compFun_digits_ge`). -/
private theorem canonical_val_pos (N : List TSym) (hc : canonicalForm N) : 0 < Val N := by
  obtain ⟨mid, hmid, rfl⟩ := hc
  rw [val_canonical]
  have := compFun_digits_ge mid hmid 1
  omega

/-- **Marker invariant** ([YAH], the backward direction of Theorem 3.17) — *cited axiom*. A single
`𝒯`-step from a **canonical** string stays canonical, and is *either* an auxiliary `𝒳`-step (which
preserves the value, `auxRules_rewriteStep_preserve`) *or* advances the value by exactly one Collatz
step (`Val N' = T(Val N)`).

This is the "markers are walls" fact: in `◁ mid ▷` the begin marker `◁` occurs only at the front and
the end marker `▷` only at the back, so a `ℬ`-rule (needs `◁`) fires only at the front and a `𝒟_T`-rule
(needs `▷`) only at the back — the latter at the *end*, where Claim 1's `dynRules_rewriteStep_applyT`
applies and gives `T`. The elementary list-position bookkeeping is the same combinatorics underlying
`blockLocalization`; recorded as a `cited` axiom (status `cited`, [YAH]). -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses canonicalForm Val auxRules_rewriteStep_preserve dynRules_rewriteStep_applyT]
axiom canonicalStep (N N' : List TSym) (hc : canonicalForm N)
    (h : RewriteStep collatzSRS N N') :
    canonicalForm N' ∧ (RewriteStep auxRules N N' ∨ Val N' = T (Val N))

/-- **Backward direction of Theorem 3.17** (contrapositive). If `𝒯` is **not** terminating then `T`
is **not** convergent. From an infinite `𝒯`-derivation (which, by `lemma_3_16`, may be taken to start
canonical) the value sequence `νᵢ = Val(sᵢ)` advances along the Collatz map at every dynamic step and
is constant otherwise (`canonicalStep`); `SN(𝒳) = terminating_auxRules` forces infinitely many dynamic
steps, so the orbit `T^[k](ν₀)` is realised cofinally in the sequence — and no `νᵢ` is `1` (else by
Claim 2 the string would be a normal form, ending the derivation). Hence `ν₀ > 0` has a non-convergent
`T`-orbit. -/
private theorem backward_aux (h : ¬ Terminating (RewriteStep collatzSRS)) : ¬ TConvergent := by
  have hnt : ¬ TerminatingFrom (RewriteStep collatzSRS) canonicalForm :=
    fun ht => h (lemma_3_16 ht)
  simp only [TerminatingFrom, not_not] at hnt
  obtain ⟨s, hc0, hstep⟩ := hnt
  have hcanon : ∀ i, canonicalForm (s i) := by
    intro i
    induction i with
    | zero => exact hc0
    | succ k ih => exact (canonicalStep (s k) (s (k + 1)) ih (hstep k)).1
  have hne1 : ∀ i, Val (s i) ≠ 1 := fun i h1 =>
    claim_2 (s i) (hcanon i) h1 ⟨s (i + 1), hstep i⟩
  have hadv : ∀ i, ¬ RewriteStep auxRules (s i) (s (i + 1)) → Val (s (i + 1)) = T (Val (s i)) := by
    intro i hni
    rcases (canonicalStep (s i) (s (i + 1)) (hcanon i) (hstep i)).2 with ha | hT
    · exact absurd ha hni
    · exact hT
  have hpres : ∀ i, RewriteStep auxRules (s i) (s (i + 1)) → Val (s (i + 1)) = Val (s i) :=
    fun i ha => (auxRules_rewriteStep_preserve _ _ ha 0).symm
  have hunb : ∀ N, ∃ i, N ≤ i ∧ ¬ RewriteStep auxRules (s i) (s (i + 1)) := by
    intro N
    by_contra hcon
    refine terminating_auxRules ⟨fun i => s (N + i), fun i => ?_⟩
    by_contra hc
    exact hcon ⟨N + i, Nat.le_add_right N i, hc⟩
  have horbit : ∀ k, ∃ i, Val (s i) = T^[k] (Val (s 0)) := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      obtain ⟨i, hi⟩ := ih
      classical
      have hex : ∃ j, ¬ RewriteStep auxRules (s (i + j)) (s (i + j + 1)) := by
        obtain ⟨m, him, hmd⟩ := hunb i
        exact ⟨m - i, by rwa [Nat.add_sub_cancel' him]⟩
      have hconst : ∀ j ≤ Nat.find hex, Val (s (i + j)) = Val (s i) := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ l ihl =>
          intro hle
          have hlt : l < Nat.find hex := by omega
          have haux : RewriteStep auxRules (s (i + l)) (s (i + l + 1)) :=
            not_not.mp (Nat.find_min hex hlt)
          have hstep_eq : Val (s (i + (l + 1))) = Val (s (i + l)) := by
            have e : i + (l + 1) = i + l + 1 := rfl
            rw [e]; exact hpres (i + l) haux
          rw [hstep_eq]; exact ihl (by omega)
      refine ⟨i + Nat.find hex + 1, ?_⟩
      have hdyn : ¬ RewriteStep auxRules (s (i + Nat.find hex)) (s (i + Nat.find hex + 1)) :=
        Nat.find_spec hex
      rw [hadv _ hdyn, hconst _ le_rfl, hi, Function.iterate_succ_apply']
  intro hconv
  obtain ⟨k, hk⟩ := hconv (Val (s 0)) (canonical_val_pos (s 0) (hcanon 0))
  obtain ⟨i, hi⟩ := horbit k
  exact hne1 i (hi.trans hk)

/-- **Canonical encodings exist** ([YAH], the forward direction of Theorem 3.17). Every positive
integer `n` is the value of some canonical digit block: `∃ mid (digits), Γ_mid(1) = n`. By strong
induction — `n = 1` is the empty block `◁▷`, and for `n ≥ 2`, append a binary symbol (`f` for `n = 2m`,
`t` for `n = 2m+1`) to a block for `m = ⌊n/2⌋ ≥ 1` (appending at the end doubles, resp. doubles-and-
adds-one). This is the binary expansion of `n`, with `◁` supplying the leading `1`. -/
private theorem encode_exists : ∀ n, 0 < n →
    ∃ mid, (∀ s ∈ mid, s = f ∨ s = t ∨ s = d0 ∨ s = d1 ∨ s = d2) ∧ compFun mid 1 = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · refine ⟨[], by simp, ?_⟩
      have hn1 : n = 1 := by omega
      rw [hn1]; rfl
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      have hmpos : 0 < m := by omega
      have hmlt : m < n := by omega
      obtain ⟨mid, hmid, hval⟩ := ih m hmlt hmpos
      rcases hm with he | ho
      · refine ⟨mid ++ [f], ?_, ?_⟩
        · intro s hs
          rcases List.mem_append.mp hs with hsm | hsf
          · exact hmid s hsm
          · rw [List.mem_singleton] at hsf; exact Or.inl hsf
        · rw [compFun_append, hval, he]; simp [compFun, symFun, beta]
      · refine ⟨mid ++ [t], ?_, ?_⟩
        · intro s hs
          rcases List.mem_append.mp hs with hsm | hst
          · exact hmid s hsm
          · rw [List.mem_singleton] at hst; exact Or.inr (Or.inl hst)
        · rw [compFun_append, hval, ho]; simp [compFun, symFun, beta]

/-- Every positive integer is the value of a **canonical string** (`encode_exists` + `val_canonical`). -/
private theorem encode_canonical (n : ℕ) (hn : 0 < n) : ∃ N, canonicalForm N ∧ Val N = n := by
  obtain ⟨mid, hmid, hval⟩ := encode_exists n hn
  exact ⟨lhd :: (mid ++ [rhd]), ⟨mid, hmid, rfl⟩, by rw [val_canonical, hval]⟩

/-- Canonical form is preserved along a whole `𝒯`-derivation (`canonicalStep` iterated). -/
private theorem reflTransGen_canonical {N N' : List TSym} (hc : canonicalForm N)
    (h : ReflTransGen (RewriteStep collatzSRS) N N') : canonicalForm N' := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact (canonicalStep _ _ ih hstep).1

/-- **Claim 3 with canonical output**: the one-`T`-step simulation `claim_3` lands on a *canonical*
string (so it can be iterated), since `𝒯`-steps preserve canonical form (`reflTransGen_canonical`). -/
private theorem claim_3_canonical (ν : ℕ) (hν : 1 < ν) (N : List TSym) (hc : canonicalForm N)
    (hv : Val N = ν) :
    ∃ N', ReflTransGen (RewriteStep collatzSRS) N N' ∧ canonicalForm N' ∧ Val N' = T ν := by
  obtain ⟨N', hreach, hval'⟩ := claim_3 ν hν N hc hv
  exact ⟨N', hreach, reflTransGen_canonical hc hreach, hval'⟩

/-- `T` preserves positivity: `0 < m → 0 < T m` (an even `m ≥ 2` halves to `≥ 1`, an odd `m` maps to
`(3m+1)/2 ≥ 2`). -/
private theorem T_pos {m : ℕ} (hm : 0 < m) : 0 < T m := by simp only [T]; split <;> omega

/-- The transitive closure of a terminating relation is terminating: an infinite `→⁺`-chain would
flatten to an infinite `→`-chain. Via `terminating_iff_wellFounded` and `WellFounded.transGen`
(`→⁺` of the converse is the converse of `→⁺`). -/
private theorem terminating_transGen {α : Type*} {r : α → α → Prop} (h : Terminating r) :
    Terminating (Relation.TransGen r) := by
  rw [terminating_iff_wellFounded] at h ⊢
  have hwf : WellFounded (Relation.TransGen fun a b => r b a) := WellFounded.transGen h
  refine Subrelation.wf ?_ hwf
  intro x y hxy
  induction hxy with
  | single hh => exact Relation.TransGen.single hh
  | tail _ hzx ih => exact Relation.TransGen.head hzx ih

/-- An infinite chain of **non-trivial** multi-step derivations `a 0 →⁺ a 1 →⁺ ⋯` witnesses
non-termination (`terminating_transGen`). -/
private theorem not_terminating_of_transGen {α : Type*} {r : α → α → Prop} (a : ℕ → α)
    (h : ∀ i, Relation.TransGen r (a i) (a (i + 1))) : ¬ Terminating r :=
  fun hterm => terminating_transGen hterm ⟨a, h⟩

/-- **Forward direction of Theorem 3.17** (contrapositive). If `T` is **not** convergent then `𝒯` is
**not** terminating. Pick `n > 0` whose `T`-orbit avoids `1`; then every orbit value `T^[k] n` is `> 1`
(positive and `≠ 1`). Encoding `n` as a canonical string (`encode_canonical`) and iterating
`claim_3_canonical` builds canonical strings `Nₖ` with `Val Nₖ = T^[k] n` and `Nₖ →*_𝒯 Nₖ₊₁`; each
step is non-trivial (consecutive values differ, `T x ≠ x`), so the chain flattens to an infinite
`𝒯`-derivation (`not_terminating_of_transGen`). -/
private theorem forward_aux (h : ¬ TConvergent) : ¬ Terminating (RewriteStep collatzSRS) := by
  simp only [TConvergent, not_forall] at h
  obtain ⟨n, hpos, hnoconv⟩ := h
  have htpos : ∀ k, 0 < T^[k] n := by
    intro k
    induction k with
    | zero => exact hpos
    | succ k ih => rw [Function.iterate_succ_apply']; exact T_pos ih
  have htraj : ∀ k, 1 < T^[k] n := fun k => by
    have h1 : T^[k] n ≠ 1 := fun he => hnoconv ⟨k, he⟩
    have := htpos k; omega
  have hTne : ∀ k, T^[k] n ≠ T^[k + 1] n := by
    intro k he
    rw [Function.iterate_succ_apply'] at he
    have hx := htpos k
    simp only [T] at he
    split at he <;> omega
  obtain ⟨N0, hN0c, hN0v⟩ := encode_canonical n hpos
  let F : (k : ℕ) → { M : List TSym // canonicalForm M ∧ Val M = T^[k] n } := fun k =>
    Nat.rec (motive := fun k => { M : List TSym // canonicalForm M ∧ Val M = T^[k] n })
      ⟨N0, hN0c, by simpa using hN0v⟩
      (fun k Fk => ⟨(claim_3_canonical (T^[k] n) (htraj k) Fk.1 Fk.2.1 Fk.2.2).choose,
        (claim_3_canonical (T^[k] n) (htraj k) Fk.1 Fk.2.1 Fk.2.2).choose_spec.2.1,
        by rw [(claim_3_canonical (T^[k] n) (htraj k) Fk.1 Fk.2.1 Fk.2.2).choose_spec.2.2,
          Function.iterate_succ_apply']⟩) k
  refine not_terminating_of_transGen (fun k => (F k).1) (fun k => ?_)
  have hreach : ReflTransGen (RewriteStep collatzSRS) (F k).1 (F (k + 1)).1 :=
    (claim_3_canonical (T^[k] n) (htraj k) (F k).1 (F k).2.1 (F k).2.2).choose_spec.1
  have hne : (F k).1 ≠ (F (k + 1)).1 := by
    intro heq
    have hv : Val (F k).1 = Val (F (k + 1)).1 := by rw [heq]
    rw [(F k).2.2, (F (k + 1)).2.2] at hv
    exact hTne k hv
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hreach with heq | htrans
  · exact absurd heq.symm hne
  · exact htrans

/-- **Theorem 3.17** ([YAH]). The Collatz-simulating system **`𝒯` is terminating if and only if `T`
is convergent** (`TConvergent`), i.e. iff the **Collatz conjecture** holds.

*Proof*, both directions by contraposition. **Forward** (`SN(𝒯) ⇒` conv, `forward_aux`): a
non-convergent orbit `T^[k] n` (all values `> 1`) is simulated by canonically encoding `n`
(`encode_canonical`) and iterating Claim 3 with canonical output (`claim_3_canonical`), producing an
infinite non-trivial `𝒯`-derivation (flattened via `not_terminating_of_transGen`) — so `𝒯` does not
terminate. **Backward** (conv `⇒ SN(𝒯)`, `backward_aux`): an infinite `𝒯`-derivation may be taken
canonical (`lemma_3_16`); the value tracks the Collatz map (`canonicalStep`), `SN(𝒳)`
(`terminating_auxRules`) forces infinitely many dynamic steps, and no value is `1` (Claim 2) — so `n`
has a non-convergent orbit.

**Genuinely proved** from Claims 1–3, Lemma 3.15 (`SN(𝒳)`) and Lemma 3.16; the only literature-`cited`
input is the marker invariant `canonicalStep` (the "markers are walls" combinatorics, as for
`blockLocalization`). Mirrors `Zantema.zantema_theorem_3_2` (`SN(𝒵) ↔ Collatz`), but here the
equivalence is reduced to that single elementary axiom rather than asserted. -/
@[category research solved, AMS 68 11, ref "YAH", group "collatz_srs",
  formal_uses TConvergent forward_aux backward_aux lemma_3_16 canonicalStep]
theorem theorem_3_17 : Terminating (RewriteStep collatzSRS) ↔ TConvergent := by
  constructor
  · intro hterm
    by_contra hnc
    exact forward_aux hnc hterm
  · intro hconv
    by_contra hnt
    exact backward_aux hnt hconv

/- Registry node for the informal proof method that Lemma 3.18 rests on. -/
informal_result "dependency-pair-framework"
  latex "The dependency pair method for termination (Arts–Giesl; Giesl, Thiele, Schneider-Kamp, Falke [GTSF06], *Mechanizing and Improving Dependency Pairs*, J. Automated Reasoning 37 (2006)). The dependency pair transformation reduces (relative and top) termination of a string/term rewriting system to the absence of infinite chains of dependency pairs; the dependency pair framework then discharges the resulting DP problem automatically through a sequence of DP processors. Here it certifies, for the boundary rules ℬ and the reversed dynamic rules 𝒟_T^rev of the Collatz SRS 𝒯 — which on canonical strings apply only at the leftmost end — that relative top-termination implies full relative termination."
  refs "GTSF06"

/-- **Lemma 3.18** ([YAH]) — *cited axiom*. Two relative-termination reductions for the Collatz SRS
`𝒯`, each trading full relative termination for the easier relative **top**-termination:

1. for every subsystem `ℛ ⊆ ℬ`, if `SN(ℛ_top / 𝒯)` then `SN(ℛ / 𝒯)`; and
2. for every subsystem `𝒬 ⊆ 𝒟_T`, if `SN(𝒬ʳᵉᵛ_top / 𝒯ʳᵉᵛ)` then `SN(𝒬ʳᵉᵛ / 𝒯ʳᵉᵛ)`,

where `SN(· / ·)` is relative termination (`TerminatingRelativeTo`), `·_top` the top (leftmost-only)
rewrite relation (`TopRewriteStep`), and `·ʳᵉᵛ` reversal (`System.reverse`).

By **Lemma 3.16** one may restrict to canonical strings `◁(f|t|0|1|2)*▷`; there every `ℬ`-rule has the
form `◁s → ◁t` and every reversed `𝒟_T`-rule the form `▷s' → ▷t'`, so they can only fire at the
**leftmost end** (`◁`/`▷` are never to their left). Hence an infinite sequence applying `ℛ`
(resp. `𝒬ʳᵉᵛ`) infinitely often applies it at the top infinitely often — relative *top*-nontermination
— which is the contrapositive. [YAH] prove this automatically via the dependency-pair transformation
and framework [GTSF06]; recorded here as a `cited` axiom carrying that method as its `informal_uses`
(see `[[dependency-pair-framework]]`). The reductions feed the rule-removal termination argument for
`𝒯` (cf. Lemma 3.15). -/
@[category research solved, AMS 68, ref "YAH", group "collatz_srs",
  formal_uses TerminatingRelativeTo TopRewriteStep System.reverse,
  informal_uses "dependency-pair-framework"]
axiom lemma_3_18 :
    (∀ R : System TSym, (∀ ℓ r, R ℓ r → auxB ℓ r) →
        TerminatingRelativeTo (TopRewriteStep R) (RewriteStep collatzSRS) →
        TerminatingRelativeTo (RewriteStep R) (RewriteStep collatzSRS)) ∧
    (∀ Q : System TSym, (∀ ℓ r, Q ℓ r → dynRules ℓ r) →
        TerminatingRelativeTo (TopRewriteStep (System.reverse Q))
          (RewriteStep (System.reverse collatzSRS)) →
        TerminatingRelativeTo (RewriteStep (System.reverse Q))
          (RewriteStep (System.reverse collatzSRS)))

end StringRewriting.CollatzSRS
