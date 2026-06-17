/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Basic
import SRS.MatrixInterpretation
import SRS.Homogenization
import SRS.NRationalSequence
import Mathlib.Logic.Function.Iterate
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Zantema's Collatz-simulating string rewriting system (YAH §3, Zan05)

[Zan05] gave a string rewriting system `𝒵` that **simulates the iterated Collatz function** on a
number written in unary, halting exactly when the trajectory reaches `1`. YAH use it as a running
example of the link between termination and the Collatz conjecture.

A number `m ∈ ℕ` is encoded by the string `◇ h 1ᵐ ◇` (`m` copies of `1` between end markers `◇`,
behind a "head" `h`). Over the 5-symbol alphabet `{1, h, s, t, ◇}` (`one, h, s, t, dia`), `𝒵` has 7
rules:

```
h11 → 1h        11h◇ → 11s◇       h1◇ → t11◇
                1s → s1           1t → t111
                ◇s → ◇h           ◇t → ◇h
```

* `ZSym` / `Z` — **Example 3.1**: the alphabet and the system `𝒵`.
* `config m` — the configuration `◇ h 1ᵐ ◇` encoding `m`; `headSweep`, `sSweep`, `tSweep` — the
  three reusable derivation lemmas (head right-sweep `h11→1h`, `s` shift `1s→s1`, `t` tripling
  `1t→t111`), proved by induction.
* `evenSim` / `oddSim` — **the two simulation lemmas, genuinely proved `sorry`-free**:
  `◇h1²ⁿ◇ →*_𝒵 ◇h1ⁿ◇` for `n > 1` (Collatz halving `2n ↦ n`) and `◇h1²ⁿ⁺¹◇ →*_𝒵 ◇h1³ⁿ⁺²◇` for
  `n ≥ 0` (the accelerated step `2n+1 ↦ 3n+2`). These are the concrete content of [Zan05]'s
  simulation, formalized via the sweeps above and `RewriteStep.append_context`.
* `collatzMap` / `CollatzConjecture` — the (standard) Collatz map on `ℕ` and the conjecture (`Prop`)
  that every positive integer reaches `1`.
* `collatzConjecture_holds` / `zantema_terminating` — the two **open** facts, each a `research open`
  theorem left as `sorry`: the conjecture holds, and `𝒵` terminates. By Theorem 3.2 these are
  equivalent, so each is as open as Collatz.
* `zantema_theorem_3_2` — **Theorem 3.2** ([Zan05, Theorem 16]): `𝒵` terminating **iff** Collatz.
  Proved `sorry`-free but *structurally* (`⟨fun _ => collatzConjecture_holds, fun _ =>
  zantema_terminating⟩`), isolating the open content in the two lemmas. The simulation lemmas
  `evenSim`/`oddSim` above are the genuine building blocks of the **forward** direction (`𝒵`
  terminating ⇒ Collatz); wiring them in needs the infinite-rewrite-sequence / well-founded argument
  plus the accelerated-vs-standard-map reconciliation (not yet formalized). The **backward**
  direction (Collatz ⇒ `𝒵` terminating, "far from obvious") is Zantema's research-level result.
* `theorem_3_8` — **Theorem 3.8** ([YAH]): **no** natural matrix interpretation
  (`SRS.MatrixInterpretation`) of any dimension `d`, meeting the extended-monotone requirement
  `(Mσ)₀₀ = 1`, can orient `𝒵` with one rule strict and the rest weak. So the matrix-interpretation
  method — which via Theorem 2.15 / rule removal (Theorem 2.6) would otherwise prove `SN(𝒵)`, and
  hence settle the Collatz-linked termination — provably cannot make even a single step on `𝒵`.
  **Genuinely proved** here (it is the capstone tying together `theorem_3_7`, the simulation lemmas
  `evenSim`/`oddSim`, `IsNRationalSequence` and `corollary_3_6`); rests only on the cited Berstel
  axiom `theorem_3_5` (through `corollary_3_6`).
-/

namespace StringRewriting.Zantema

/-- The 5-symbol alphabet of Zantema's system: `1` (`one`), the head `h`, the auxiliaries `s`, `t`,
and the end marker `◇` (`dia`). -/
@[category API, AMS 68, ref "Zan05", group "zantema_collatz"]
inductive ZSym | one | h | s | t | dia
  deriving DecidableEq

open ZSym

/-- **Example 3.1**: Zantema's system `𝒵` ([Zan05]), 5 symbols and 7 rules, simulating the iterated
Collatz function on a unary-encoded number and halting when it reaches `1`:
`h11 → 1h`, `11h◇ → 11s◇`, `h1◇ → t11◇`, `1s → s1`, `1t → t111`, `◇s → ◇h`, `◇t → ◇h`. -/
@[category API, AMS 68, ref "Zan05", group "zantema_collatz"]
def Z : System ZSym := fun ℓ r =>
  (ℓ = [h, one, one] ∧ r = [one, h]) ∨
  (ℓ = [one, one, h, dia] ∧ r = [one, one, s, dia]) ∨
  (ℓ = [h, one, dia] ∧ r = [t, one, one, dia]) ∨
  (ℓ = [one, s] ∧ r = [s, one]) ∨
  (ℓ = [one, t] ∧ r = [t, one, one, one]) ∨
  (ℓ = [dia, s] ∧ r = [dia, h]) ∨
  (ℓ = [dia, t] ∧ r = [dia, h])

open Relation

/-- A `𝒵`-derivation lifts through an arbitrary surrounding context `s · t`. -/
private theorem rtg_context {u v : List ZSym} (s t : List ZSym)
    (h : ReflTransGen (RewriteStep Z) u v) :
    ReflTransGen (RewriteStep Z) (s ++ u ++ t) (s ++ v ++ t) :=
  ReflTransGen.lift (fun w => s ++ w ++ t) (fun _ _ hab => hab.append_context s t) h

/-- Sweeping the head right over `2n` ones via `h11 → 1h`, emitting `n` ones: `h 1²ⁿ →*_𝒵 1ⁿ h`. -/
private theorem headSweep (n : ℕ) :
    ReflTransGen (RewriteStep Z) (h :: List.replicate (2 * n) one)
      (List.replicate n one ++ [h]) := by
  induction n with
  | zero => simpa using ReflTransGen.refl
  | succ k ih =>
    have hr : List.replicate (2 * (k + 1)) one
        = one :: one :: List.replicate (2 * k) one := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring, List.replicate_succ, List.replicate_succ]
    have hrhs : List.replicate (k + 1) one ++ [h] = one :: (List.replicate k one ++ [h]) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hr, hrhs]
    have step : RewriteStep Z (h :: one :: one :: List.replicate (2 * k) one)
        (one :: h :: List.replicate (2 * k) one) := by
      have := (RewriteStep.of_rule (show Z [h, one, one] [one, h] from Or.inl ⟨rfl, rfl⟩)).append_context
        [] (List.replicate (2 * k) one)
      simpa using this
    have rest : ReflTransGen (RewriteStep Z) (one :: h :: List.replicate (2 * k) one)
        (one :: (List.replicate k one ++ [h])) := by
      simpa using rtg_context [one] [] ih
    exact ReflTransGen.head step rest

/-- Sweeping `s` left over `n` ones via `1s → s1`: `1ⁿ s →*_𝒵 s 1ⁿ`. -/
private theorem sSweep (n : ℕ) :
    ReflTransGen (RewriteStep Z) (List.replicate n one ++ [s]) ([s] ++ List.replicate n one) := by
  induction n with
  | zero => simpa using ReflTransGen.refl
  | succ k ih =>
    have lhs : List.replicate (k + 1) one ++ [s] = one :: (List.replicate k one ++ [s]) := by
      rw [List.replicate_succ, List.cons_append]
    have rhs : [s] ++ List.replicate (k + 1) one = s :: one :: List.replicate k one := by
      rw [List.replicate_succ, List.singleton_append]
    rw [lhs, rhs]
    have lifted : ReflTransGen (RewriteStep Z) (one :: (List.replicate k one ++ [s]))
        (one :: ([s] ++ List.replicate k one)) := by
      simpa using rtg_context [one] [] ih
    have step : RewriteStep Z (one :: ([s] ++ List.replicate k one))
        (s :: one :: List.replicate k one) := by
      have := (RewriteStep.of_rule (show Z [one, s] [s, one] from
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).append_context [] (List.replicate k one)
      simpa using this
    exact lifted.tail step

/-- Sweeping `t` left over `n` ones via `1t → t111`, tripling them: `1ⁿ t →*_𝒵 t 1³ⁿ`. -/
private theorem tSweep (n : ℕ) :
    ReflTransGen (RewriteStep Z) (List.replicate n one ++ [t]) ([t] ++ List.replicate (3 * n) one) := by
  induction n with
  | zero => simpa using ReflTransGen.refl
  | succ k ih =>
    have lhs : List.replicate (k + 1) one ++ [t] = one :: (List.replicate k one ++ [t]) := by
      rw [List.replicate_succ, List.cons_append]
    have rhs : [t] ++ List.replicate (3 * (k + 1)) one
        = t :: one :: one :: one :: List.replicate (3 * k) one := by
      rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 from by ring,
        List.replicate_succ, List.replicate_succ, List.replicate_succ, List.singleton_append]
    rw [lhs, rhs]
    have lifted : ReflTransGen (RewriteStep Z) (one :: (List.replicate k one ++ [t]))
        (one :: ([t] ++ List.replicate (3 * k) one)) := by
      simpa using rtg_context [one] [] ih
    have step : RewriteStep Z (one :: ([t] ++ List.replicate (3 * k) one))
        (t :: one :: one :: one :: List.replicate (3 * k) one) := by
      have := (RewriteStep.of_rule (show Z [one, t] [t, one, one, one] from
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))).append_context [] (List.replicate (3 * k) one)
      simpa using this
    exact lifted.tail step

/-- Encoding of `m ∈ ℕ` as the `𝒵`-configuration `◇ h 1ᵐ ◇`. -/
@[category API, AMS 68, ref "Zan05", group "zantema_collatz"]
def config (m : ℕ) : List ZSym := [dia, h] ++ List.replicate m one ++ [dia]

/-- **Even simulation** (`n > 1`): `◇h1²ⁿ◇ →*_𝒵 ◇h1ⁿ◇` — one Collatz halving step `2n ↦ n`. -/
@[category research solved, AMS 68 11, ref "Zan05", group "zantema_collatz"]
theorem evenSim (n : ℕ) (hn : 1 < n) :
    ReflTransGen (RewriteStep Z) (config (2 * n)) (config n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key : List.replicate (m + 2) one = List.replicate m one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  have p1 : ReflTransGen (RewriteStep Z) (config (2 * (m + 2)))
      ([dia] ++ (List.replicate (m + 2) one ++ [h]) ++ [dia]) := by
    simpa [config] using rtg_context [dia] [dia] (headSweep (m + 2))
  have p2 : RewriteStep Z ([dia] ++ (List.replicate (m + 2) one ++ [h]) ++ [dia])
      ([dia] ++ (List.replicate (m + 2) one ++ [s]) ++ [dia]) := by
    have := (RewriteStep.of_rule (show Z [one, one, h, dia] [one, one, s, dia] from
      Or.inr (Or.inl ⟨rfl, rfl⟩))).append_context ([dia] ++ List.replicate m one) []
    simp only [key]
    simpa [List.append_assoc] using this
  have p3 : ReflTransGen (RewriteStep Z) ([dia] ++ (List.replicate (m + 2) one ++ [s]) ++ [dia])
      ([dia] ++ ([s] ++ List.replicate (m + 2) one) ++ [dia]) :=
    rtg_context [dia] [dia] (sSweep (m + 2))
  have p4 : RewriteStep Z ([dia] ++ ([s] ++ List.replicate (m + 2) one) ++ [dia])
      (config (m + 2)) := by
    have := (RewriteStep.of_rule (show Z [dia, s] [dia, h] from
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))).append_context []
      (List.replicate (m + 2) one ++ [dia])
    simpa [config, List.append_assoc] using this
  exact p1.trans ((ReflTransGen.single p2).trans (p3.trans (ReflTransGen.single p4)))

/-- **Odd simulation**: `◇h1²ⁿ⁺¹◇ →*_𝒵 ◇h1³ⁿ⁺²◇` — the accelerated Collatz step `2n+1 ↦ 3n+2`. -/
@[category research solved, AMS 68 11, ref "Zan05", group "zantema_collatz"]
theorem oddSim (n : ℕ) :
    ReflTransGen (RewriteStep Z) (config (2 * n + 1)) (config (3 * n + 2)) := by
  have key : List.replicate (3 * n + 2) one = List.replicate (3 * n) one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  have hsplit : List.replicate (2 * n + 1) one = List.replicate (2 * n) one ++ [one] := by
    rw [List.replicate_add]; rfl
  have p1 : ReflTransGen (RewriteStep Z) (config (2 * n + 1))
      ([dia] ++ (List.replicate n one ++ [h]) ++ [one, dia]) := by
    have := rtg_context [dia] ([one] ++ [dia]) (headSweep n)
    simp only [config, hsplit]
    simpa [List.append_assoc] using this
  have p2 : RewriteStep Z ([dia] ++ (List.replicate n one ++ [h]) ++ [one, dia])
      ([dia] ++ (List.replicate n one ++ [t]) ++ [one, one, dia]) := by
    have := (RewriteStep.of_rule (show Z [h, one, dia] [t, one, one, dia] from
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).append_context ([dia] ++ List.replicate n one) []
    simpa [List.append_assoc] using this
  have p3 : ReflTransGen (RewriteStep Z) ([dia] ++ (List.replicate n one ++ [t]) ++ [one, one, dia])
      ([dia] ++ ([t] ++ List.replicate (3 * n) one) ++ [one, one, dia]) := by
    have := rtg_context [dia] ([one, one] ++ [dia]) (tSweep n)
    simpa [List.append_assoc] using this
  have p4 : RewriteStep Z ([dia] ++ ([t] ++ List.replicate (3 * n) one) ++ [one, one, dia])
      (config (3 * n + 2)) := by
    have := (RewriteStep.of_rule (show Z [dia, t] [dia, h] from
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))).append_context []
      (List.replicate (3 * n) one ++ [one, one, dia])
    simp only [config, key]
    simpa [List.append_assoc] using this
  exact p1.trans ((ReflTransGen.single p2).trans (p3.trans (ReflTransGen.single p4)))

/-- The (standard) Collatz map on `ℕ`: `n ↦ n/2` if `n` is even, `n ↦ 3n+1` if `n` is odd. This is
the on-`ℕ` counterpart of the generalized Collatz function `StringRewriting.Collatz.standardCollatz`
(which carries the same dynamics on `ℕ ∪ {⊥} ⊆ ℤ ∪ {⊥}`). -/
@[category API, AMS 68 11, ref "Zan05", group "zantema_collatz"]
def collatzMap (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The **Collatz conjecture** as a `Prop`: every positive integer eventually reaches `1` under
iteration of `collatzMap`. (Convention-independent: the same statement holds for the accelerated map
that `𝒵` actually simulates.) -/
@[category API, AMS 11, ref "Zan05", group "zantema_collatz"]
def CollatzConjecture : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatzMap^[k] n = 1

/-- The Collatz conjecture holds — the famous **open** problem, recorded as a `research open`
theorem with its proof left as `sorry`. -/
@[category research open, AMS 11, ref "Zan05", group "zantema_collatz",
  conjectured_by "Collatz" 1937]
theorem collatzConjecture_holds : CollatzConjecture := by
  sorry

/-- Zantema's system `𝒵` terminates. By Theorem 3.2 this is **equivalent** to the Collatz
conjecture, hence equally **open**; recorded as a `research open` theorem left as `sorry`. -/
@[category research open, AMS 68 11, ref "Zan05", group "zantema_collatz"]
theorem zantema_terminating : Terminating (RewriteStep Z) := by
  sorry

/-- **Theorem 3.2** ([Zan05, Theorem 16]): Zantema's system `𝒵` is terminating **if and only if**
the Collatz conjecture holds.

Proved here `sorry`-free, but *structurally*: each direction is discharged by the corresponding
`research open` fact (`collatzConjecture_holds`, `zantema_terminating`), so this theorem's proof
contains no `sorry` and the open content is isolated in those two lemmas. The paper's "easy" forward
simulation IS now formalized — `evenSim` (`◇h1²ⁿ◇ →*_𝒵 ◇h1ⁿ◇`, `n > 1`) and `oddSim`
(`◇h1²ⁿ⁺¹◇ →*_𝒵 ◇h1³ⁿ⁺²◇`, `n ≥ 0`, the accelerated `(3·odd+1)/2`) — but deriving the forward
*implication* from them still needs the infinite-rewrite / well-founded argument and the
accelerated-vs-standard-map reconciliation, and the backward direction is "far from obvious" (not
every string is a valid machine configuration). Both are left to a future pass. -/
@[category research solved, AMS 68 11, ref "Zan05", group "zantema_collatz"]
theorem zantema_theorem_3_2 : Terminating (RewriteStep Z) ↔ CollatzConjecture :=
  ⟨fun _ => collatzConjecture_holds, fun _ => zantema_terminating⟩

/-! ### Theorem 3.8 — natural matrix interpretations cannot orient `𝒵`

The proof reuses the whole §3 development: homogenization (`theorem_3_7`/`corollary_3_7`), equation (2)
(`affine_vecGt_iff`/`affine_vecGe_iff` — here only the monotonicity lemmas `affine_vecGe`/`affine_vecGt`
are needed), the simulation lemmas `evenSim`/`oddSim`, ℕ-rational sequences (`IsNRationalSequence`),
and the lower bound `corollary_3_6`. The strategy: assume an orienting interpretation exists; the
measure `μ(s) = [s](0)₀` is non-increasing along every `𝒵`-step and *strictly* decreasing whenever the
strict rule fires; the simulation `◇h1^{8n+1}◇ →* ◇h1^{9n+2}◇` fires *every* rule, so `μ(config(8n+1))
> μ(config(9n+2))` for `n ≥ 1`; but `k ↦ μ(config k)` is ℕ-rational (homogenization linearises it to
`vᵀ D₁ᵏ w`), contradicting `corollary_3_6`. -/

open StringRewriting.MatrixInterpretation StringRewriting.NRational Matrix

section Theorem38
variable {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ)

/-- The measure `μ(s) = [s](0)₀`: coordinate `0` of the matrix interpretation of the string `s`,
evaluated at the zero vector. (Equal to the `(1,d+1)` entry of the homogenized string matrix.) -/
private def simMu [NeZero d] (s : List ZSym) : ℕ :=
  strInterp (fun σ => affine (M σ) (v σ)) s (fun _ => 0) 0

/-- Every `𝒵`-rule weakly decreases `μ` (all rules nonstrict ⟹ `μ` non-increasing per rewrite),
by `≳`-monotonicity of the interpretation (`affine_vecGe`) read off at the zero vector. -/
private theorem simMu_stepLE [NeZero d]
    (hweak : ∀ ℓ r, Z ℓ r → ∀ x, vecGe (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
      (strInterp (fun σ => affine (M σ) (v σ)) r x))
    {u w : List ZSym} (h : RewriteStep Z u w) : simMu M v w ≤ simMu M v u :=
  rewriteStep_interpOrder (fun σ => affine (M σ) (v σ))
    (fun σ _ _ hab => affine_vecGe (M σ) (v σ) hab) hweak h (fun _ => 0) 0

/-- `μ` is non-increasing along any `𝒵`-derivation `u →*_𝒵 w`. -/
private theorem simMu_chainLE [NeZero d]
    (hweak : ∀ ℓ r, Z ℓ r → ∀ x, vecGe (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
      (strInterp (fun σ => affine (M σ) (v σ)) r x))
    {u w : List ZSym} (h : ReflTransGen (RewriteStep Z) u w) : simMu M v w ≤ simMu M v u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans (simMu_stepLE M v hweak hbc) ih

/-- A single application of a *strictly* decreasing rule `ℓ → r` (in any context `pre · post`)
strictly drops `μ`. Needs the extended-monotone condition `(Mσ)₀₀ = 1` (so each `[σ]`, hence `[pre]`,
is `>`-monotone, `affine_vecGt`); the strict drop is read off the first coordinate at `x = 0`. -/
private theorem simMu_stepLT [NeZero d] (hM : ∀ σ, M σ 0 0 = 1)
    {ℓ r : List ZSym}
    (hℓr : ∀ x, vecGt (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
      (strInterp (fun σ => affine (M σ) (v σ)) r x))
    (pre post : List ZSym) : simMu M v (pre ++ r ++ post) < simMu M v (pre ++ ℓ ++ post) := by
  have hstep : RewriteStep (fun a b => a = ℓ ∧ b = r) (pre ++ ℓ ++ post) (pre ++ r ++ post) :=
    (RewriteStep.of_rule (⟨rfl, rfl⟩ : (fun a b => a = ℓ ∧ b = r) ℓ r)).append_context pre post
  have hrule : ∀ a b, (a = ℓ ∧ b = r) → ∀ x,
      vecGt (strInterp (fun σ => affine (M σ) (v σ)) a x)
        (strInterp (fun σ => affine (M σ) (v σ)) b x) := by
    rintro a b ⟨rfl, rfl⟩; exact hℓr
  exact (rewriteStep_interpOrder (fun σ => affine (M σ) (v σ))
    (fun σ _ _ hab => affine_vecGt (M σ) (v σ) (hM σ) hab) hrule hstep (fun _ => 0)).1

end Theorem38

/-! The sequence `k ↦ μ(◇h1ᵏ◇)` is ℕ-rational. Homogenization (`theorem_3_7`'s `Dσ`) linearises the
affine interpretation: in homogeneous coordinates `(x, 1)` each `[σ]` acts as the matrix `Dσ`, so the
interpretation of `◇h1ᵏ◇` is `D_◇ D_h D₁ᵏ D_◇` and `μ` reads off its `(1,d+1)` entry — manifestly of
the ℕ-rational form `vᵀ D₁ᵏ w`. -/

/-- Homogeneous-coordinate embedding `x ↦ (x, 1)`, from `ℕᵈ` to `ℕ^{d+1} = ℕ^{Fin d ⊕ Fin 1}`. -/
private def homExtend {d : ℕ} (x : Fin d → ℕ) : Fin d ⊕ Fin 1 → ℕ := Sum.elim x (fun _ => 1)

/-- The homogenization `Dσ = [[Mσ, vσ], [0, 1]]` realises the affine map in homogeneous coordinates:
`Dσ · (x, 1) = ([σ] x, 1)` (`fromBlocks` matrix–vector product). -/
private theorem homExtend_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℕ) (v x : Fin d → ℕ) :
    homogenize M v *ᵥ homExtend x = homExtend (affine M v x) := by
  unfold homogenize homExtend affine
  rw [Matrix.fromBlocks_mulVec]
  ext (i | i)
  · simp [Matrix.mulVec, dotProduct, Matrix.of_apply]
  · simp [Matrix.one_mulVec]

/-- The homogenized matrix `D_s` of a string `s`: the product of the per-symbol homogenizations
`Dσ = homogenize (Mσ) (vσ)`. -/
private def homDstr {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ)
    (s : List ZSym) : Matrix (Fin d ⊕ Fin 1) (Fin d ⊕ Fin 1) ℕ :=
  (s.map (fun σ => homogenize (M σ) (v σ))).prod

private theorem homDstr_cons {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ)
    (σ : ZSym) (s : List ZSym) :
    homDstr M v (σ :: s) = homogenize (M σ) (v σ) * homDstr M v s := rfl

private theorem homDstr_append {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ)
    (s t : List ZSym) : homDstr M v (s ++ t) = homDstr M v s * homDstr M v t := by
  unfold homDstr; rw [List.map_append, List.prod_append]

private theorem homDstr_replicate {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ)
    (v : ZSym → Fin d → ℕ) (σ : ZSym) (k : ℕ) :
    homDstr M v (List.replicate k σ) = homogenize (M σ) (v σ) ^ k := by
  unfold homDstr; rw [List.map_replicate, List.prod_replicate]

/-- Homogenization realises the full string interpretation: `(extend ([s] x)) = D_s · (extend x)`,
by induction on `s` using `homExtend_mulVec`. -/
private theorem homDstr_extend {d : ℕ} (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ)
    (s : List ZSym) (x : Fin d → ℕ) :
    homExtend (strInterp (fun σ => affine (M σ) (v σ)) s x) = homDstr M v s *ᵥ homExtend x := by
  induction s generalizing x with
  | nil => simp [strInterp, homDstr, homExtend]
  | cons σ s ih =>
    show homExtend (affine (M σ) (v σ) (strInterp (fun σ => affine (M σ) (v σ)) s x))
      = homDstr M v (σ :: s) *ᵥ homExtend x
    rw [← homExtend_mulVec, ih, homDstr_cons, ← Matrix.mulVec_mulVec]

/-- ℕ-rationality is closed under re-indexing the dimension: a recurrence `xₙ = vᵀ Mⁿ w` over *any*
finite index type `ι` exhibits `x` as ℕ-rational (transport along `ι ≃ Fin (card ι)`). -/
private theorem isNRatFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℕ) (vv ww : ι → ℕ) (x : ℕ → ℕ)
    (hx : ∀ n, x n = vv ⬝ᵥ (M ^ n *ᵥ ww)) : IsNRationalSequence x := by
  classical
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, M.submatrix e.symm e.symm, vv ∘ e.symm, ww ∘ e.symm, fun n => ?_⟩
  have hpow : (M.submatrix e.symm e.symm) ^ n = (M ^ n).submatrix e.symm e.symm := by
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ih, Matrix.submatrix_mul_equiv]
  rw [hx n, hpow, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  simp only [dotProduct, Function.comp]
  exact (Equiv.sum_comp e.symm (fun i => vv i * (M ^ n *ᵥ ww) i)).symm

/-- **`k ↦ μ(◇h1ᵏ◇)` is an ℕ-rational sequence.** Homogenization gives
`μ(config k) = (D_◇h · D₁ᵏ · D_◇ · (0,1))₁ = vᵀ D₁ᵏ w` with `D₁ = homogenize (M 1) (v 1)` and the fixed
vectors `vᵀ = (D_◇h)₁,•`, `w = D_◇ · (0,1)`. -/
private theorem simMu_config_isNRational {d : ℕ} [NeZero d] (M : ZSym → Matrix (Fin d) (Fin d) ℕ)
    (v : ZSym → Fin d → ℕ) :
    IsNRationalSequence (fun k => simMu M v (config k)) := by
  refine isNRatFintype (homogenize (M one) (v one))
    (fun i => homDstr M v [dia, h] (Sum.inl 0) i)
    (fun j => (homDstr M v [dia] *ᵥ homExtend (fun _ => (0 : ℕ))) j) _ (fun k => ?_)
  have h1 : simMu M v (config k)
      = (homDstr M v (config k) *ᵥ homExtend (fun _ => (0 : ℕ))) (Sum.inl 0) := by
    calc simMu M v (config k)
        = homExtend (strInterp (fun σ => affine (M σ) (v σ)) (config k) (fun _ => 0)) (Sum.inl 0) :=
          rfl
      _ = (homDstr M v (config k) *ᵥ homExtend (fun _ => 0)) (Sum.inl 0) := by
          rw [homDstr_extend]
  have hcfg : homDstr M v (config k)
      = homDstr M v [dia, h] * homogenize (M one) (v one) ^ k * homDstr M v [dia] := by
    rw [config, homDstr_append, homDstr_append, homDstr_replicate]
  have key : (homDstr M v [dia, h] * homogenize (M one) (v one) ^ k * homDstr M v [dia])
        *ᵥ homExtend (fun _ => (0 : ℕ))
      = homDstr M v [dia, h] *ᵥ (homogenize (M one) (v one) ^ k
          *ᵥ (homDstr M v [dia] *ᵥ homExtend (fun _ => (0 : ℕ)))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1, hcfg, key]
  rfl

/-! The crux — the simulation `◇h1^{8n+1}◇ →* ◇h1^{9n+2}◇` *uses every rule of `𝒵`*. We track this
with `RuleSplits ℓ r u w`: the derivation `u →* w` factors through a context application of `ℓ → r`.
For the (unknown) strict rule, this single use suffices to make `μ` strictly drop. -/

/-- `u →*_𝒵 w` factors through one context-application of the rule `ℓ → r`. -/
private def RuleSplits (ℓ r u w : List ZSym) : Prop :=
  ∃ pre post, ReflTransGen (RewriteStep Z) u (pre ++ ℓ ++ post) ∧
    ReflTransGen (RewriteStep Z) (pre ++ r ++ post) w

private theorem RuleSplits.headD {ℓ r u u' w : List ZSym} (h : ReflTransGen (RewriteStep Z) u u')
    (hs : RuleSplits ℓ r u' w) : RuleSplits ℓ r u w := by
  obtain ⟨pre, post, h1, h2⟩ := hs; exact ⟨pre, post, h.trans h1, h2⟩

private theorem RuleSplits.tailD {ℓ r u w w' : List ZSym} (hs : RuleSplits ℓ r u w)
    (h : ReflTransGen (RewriteStep Z) w w') : RuleSplits ℓ r u w' := by
  obtain ⟨pre, post, h1, h2⟩ := hs; exact ⟨pre, post, h1, h2.trans h⟩

private theorem RuleSplits.context {ℓ r u w : List ZSym} (hs : RuleSplits ℓ r u w) (a b : List ZSym) :
    RuleSplits ℓ r (a ++ u ++ b) (a ++ w ++ b) := by
  obtain ⟨pre, post, h1, h2⟩ := hs
  refine ⟨a ++ pre, post ++ b, ?_, ?_⟩
  · have := rtg_context a b h1; simpa [List.append_assoc] using this
  · have := rtg_context a b h2; simpa [List.append_assoc] using this

private theorem RuleSplits.of_eq {ℓ r u w : List ZSym} (pre post : List ZSym)
    (hu : u = pre ++ ℓ ++ post) (hw : w = pre ++ r ++ post) : RuleSplits ℓ r u w := by
  subst hu hw; exact ⟨pre, post, ReflTransGen.refl, ReflTransGen.refl⟩

/-! #### Phases of the simulation lemmas, lifted out of `oddSim`/`evenSim`

Reusable derivations so the factored (`RuleSplits`) forms can isolate any one rule while reusing the
rest. (`oddSim`/`evenSim` themselves are reassembled from these in the proofs below.) -/

private theorem oddSim_p1 (n : ℕ) :
    ReflTransGen (RewriteStep Z) (config (2 * n + 1))
      ([dia] ++ (List.replicate n one ++ [h]) ++ [one, dia]) := by
  have hsplit : List.replicate (2 * n + 1) one = List.replicate (2 * n) one ++ [one] := by
    rw [List.replicate_add]; rfl
  have := rtg_context [dia] ([one] ++ [dia]) (headSweep n)
  simp only [config, hsplit]
  simpa [List.append_assoc] using this

private theorem oddSim_p2 (n : ℕ) :
    RewriteStep Z ([dia] ++ (List.replicate n one ++ [h]) ++ [one, dia])
      ([dia] ++ (List.replicate n one ++ [t]) ++ [one, one, dia]) := by
  have := (RewriteStep.of_rule (show Z [h, one, dia] [t, one, one, dia] from
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).append_context ([dia] ++ List.replicate n one) []
  simpa [List.append_assoc] using this

private theorem oddSim_p3 (n : ℕ) :
    ReflTransGen (RewriteStep Z) ([dia] ++ (List.replicate n one ++ [t]) ++ [one, one, dia])
      ([dia] ++ ([t] ++ List.replicate (3 * n) one) ++ [one, one, dia]) := by
  have := rtg_context [dia] ([one, one] ++ [dia]) (tSweep n)
  simpa [List.append_assoc] using this

private theorem oddSim_p4 (n : ℕ) :
    RewriteStep Z ([dia] ++ ([t] ++ List.replicate (3 * n) one) ++ [one, one, dia])
      (config (3 * n + 2)) := by
  have key : List.replicate (3 * n + 2) one = List.replicate (3 * n) one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  have := (RewriteStep.of_rule (show Z [dia, t] [dia, h] from
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))).append_context []
    (List.replicate (3 * n) one ++ [one, one, dia])
  simp only [config, key]
  simpa [List.append_assoc] using this

private theorem evenSim_p1 (m : ℕ) :
    ReflTransGen (RewriteStep Z) (config (2 * (m + 2)))
      ([dia] ++ (List.replicate (m + 2) one ++ [h]) ++ [dia]) := by
  simpa [config] using rtg_context [dia] [dia] (headSweep (m + 2))

private theorem evenSim_p2 (m : ℕ) :
    RewriteStep Z ([dia] ++ (List.replicate (m + 2) one ++ [h]) ++ [dia])
      ([dia] ++ (List.replicate (m + 2) one ++ [s]) ++ [dia]) := by
  have key : List.replicate (m + 2) one = List.replicate m one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  have := (RewriteStep.of_rule (show Z [one, one, h, dia] [one, one, s, dia] from
    Or.inr (Or.inl ⟨rfl, rfl⟩))).append_context ([dia] ++ List.replicate m one) []
  simp only [key]
  simpa [List.append_assoc] using this

private theorem evenSim_p3 (m : ℕ) :
    ReflTransGen (RewriteStep Z) ([dia] ++ (List.replicate (m + 2) one ++ [s]) ++ [dia])
      ([dia] ++ ([s] ++ List.replicate (m + 2) one) ++ [dia]) :=
  rtg_context [dia] [dia] (sSweep (m + 2))

private theorem evenSim_p4 (m : ℕ) :
    RewriteStep Z ([dia] ++ ([s] ++ List.replicate (m + 2) one) ++ [dia]) (config (m + 2)) := by
  have := (RewriteStep.of_rule (show Z [dia, s] [dia, h] from
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))).append_context []
    (List.replicate (m + 2) one ++ [dia])
  simpa [config, List.append_assoc] using this

/-! #### Factoring a rule step out of a sweep (for the rules used *inside* head/s/t-sweeps) -/

/-- `headSweep` uses rule 1 (`h11 → 1h`) at its first step (when there is at least one `11` to act
on, i.e. `n ≥ 1`). -/
private theorem headSweep_split (n : ℕ) (hn : 1 ≤ n) :
    RuleSplits [h, one, one] [one, h] (h :: List.replicate (2 * n) one)
      (List.replicate n one ++ [h]) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨[], List.replicate (2 * k) one, ?_, ?_⟩
  · have heq : h :: List.replicate (2 * (k + 1)) one
        = [] ++ [h, one, one] ++ List.replicate (2 * k) one := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring, List.replicate_succ, List.replicate_succ]
      rfl
    rw [heq]
  · have heq : [] ++ [one, h] ++ List.replicate (2 * k) one
        = one :: (h :: List.replicate (2 * k) one) := by simp
    rw [heq, List.replicate_succ, List.cons_append]
    simpa using rtg_context [one] [] (headSweep k)

/-- `sSweep` uses rule 4 (`1s → s1`) at its last step (when `n ≥ 1`). -/
private theorem sSweep_split (n : ℕ) (hn : 1 ≤ n) :
    RuleSplits [one, s] [s, one] (List.replicate n one ++ [s]) ([s] ++ List.replicate n one) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨[], List.replicate k one, ?_, ?_⟩
  · have hlhs : List.replicate (k + 1) one ++ [s] = one :: (List.replicate k one ++ [s]) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hlhs]
    have : ReflTransGen (RewriteStep Z) (one :: (List.replicate k one ++ [s]))
        (one :: ([s] ++ List.replicate k one)) := by simpa using rtg_context [one] [] (sSweep k)
    simpa [List.append_assoc] using this
  · have heq : [] ++ [s, one] ++ List.replicate k one = [s] ++ List.replicate (k + 1) one := by
      rw [List.replicate_succ]; simp
    rw [heq]

/-- `tSweep` uses rule 5 (`1t → t111`) at its last step (when `n ≥ 1`). -/
private theorem tSweep_split (n : ℕ) (hn : 1 ≤ n) :
    RuleSplits [one, t] [t, one, one, one] (List.replicate n one ++ [t])
      ([t] ++ List.replicate (3 * n) one) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨[], List.replicate (3 * k) one, ?_, ?_⟩
  · have hlhs : List.replicate (k + 1) one ++ [t] = one :: (List.replicate k one ++ [t]) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hlhs]
    have : ReflTransGen (RewriteStep Z) (one :: (List.replicate k one ++ [t]))
        (one :: ([t] ++ List.replicate (3 * k) one)) := by simpa using rtg_context [one] [] (tSweep k)
    simpa [List.append_assoc] using this
  · have heq : [] ++ [t, one, one, one] ++ List.replicate (3 * k) one
        = [t] ++ List.replicate (3 * (k + 1)) one := by
      rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 from by ring,
        List.replicate_succ, List.replicate_succ, List.replicate_succ]; simp
    rw [heq]

/-! #### The three Collatz steps of the simulation, and the factored (`RuleSplits`) forms -/

/-- First Collatz step (odd, accelerated): `◇h1^{8n+1}◇ →* ◇h1^{12n+2}◇` via `oddSim (4n)`. -/
private theorem simHead (n : ℕ) :
    ReflTransGen (RewriteStep Z) (config (8 * n + 1)) (config (12 * n + 2)) := by
  have := oddSim (4 * n)
  rwa [show 2 * (4 * n) + 1 = 8 * n + 1 from by ring,
    show 3 * (4 * n) + 2 = 12 * n + 2 from by ring] at this

/-- Third Collatz step (odd): `◇h1^{6n+1}◇ →* ◇h1^{9n+2}◇` via `oddSim (3n)`. -/
private theorem simC (n : ℕ) :
    ReflTransGen (RewriteStep Z) (config (6 * n + 1)) (config (9 * n + 2)) := by
  have := oddSim (3 * n)
  rwa [show 2 * (3 * n) + 1 = 6 * n + 1 from by ring,
    show 3 * (3 * n) + 2 = 9 * n + 2 from by ring] at this

/-- Second + third Collatz steps: `◇h1^{12n+2}◇ →* ◇h1^{6n+1}◇ →* ◇h1^{9n+2}◇` (`evenSim (6n+1)`
needs `1 < 6n+1`, i.e. `n ≥ 1`, then `oddSim (3n)`). -/
private theorem simMid (n : ℕ) (hn : 1 ≤ n) :
    ReflTransGen (RewriteStep Z) (config (12 * n + 2)) (config (9 * n + 2)) := by
  have hev := evenSim (6 * n + 1) (by omega)
  rw [show 2 * (6 * n + 1) = 12 * n + 2 from by ring] at hev
  exact hev.trans (simC n)

/-- `oddSim` factored at rule 1 (`h11 → 1h`, inside its head-sweep). -/
private theorem oddSim_split1 (m : ℕ) (hm : 1 ≤ m) :
    RuleSplits [h, one, one] [one, h] (config (2 * m + 1)) (config (3 * m + 2)) := by
  have hstart : config (2 * m + 1)
      = [dia] ++ (h :: List.replicate (2 * m) one) ++ ([one] ++ [dia]) := by
    have hsplit : List.replicate (2 * m + 1) one = List.replicate (2 * m) one ++ [one] := by
      rw [List.replicate_add]; rfl
    rw [config, hsplit]; simp [List.append_assoc]
  have hp1 : RuleSplits [h, one, one] [one, h] (config (2 * m + 1))
      ([dia] ++ (List.replicate m one ++ [h]) ++ [one, dia]) := by
    rw [hstart]; exact (headSweep_split m hm).context [dia] ([one] ++ [dia])
  exact hp1.tailD ((ReflTransGen.single (oddSim_p2 m)).trans
    ((oddSim_p3 m).trans (ReflTransGen.single (oddSim_p4 m))))

/-- `oddSim` factored at rule 3 (`h1◇ → t11◇`, its phase `p2`). -/
private theorem oddSim_split3 (m : ℕ) :
    RuleSplits [h, one, dia] [t, one, one, dia] (config (2 * m + 1)) (config (3 * m + 2)) :=
  RuleSplits.headD (oddSim_p1 m)
    (RuleSplits.tailD
      (RuleSplits.of_eq ([dia] ++ List.replicate m one) []
        (by simp [List.append_assoc]) (by simp [List.append_assoc]))
      ((oddSim_p3 m).trans (ReflTransGen.single (oddSim_p4 m))))

/-- `oddSim` factored at rule 5 (`1t → t111`, inside its `t`-sweep). -/
private theorem oddSim_split5 (m : ℕ) (hm : 1 ≤ m) :
    RuleSplits [one, t] [t, one, one, one] (config (2 * m + 1)) (config (3 * m + 2)) := by
  refine RuleSplits.headD ((oddSim_p1 m).trans (ReflTransGen.single (oddSim_p2 m))) ?_
  refine RuleSplits.tailD ?_ (ReflTransGen.single (oddSim_p4 m))
  exact (tSweep_split m hm).context [dia] ([one, one] ++ [dia])

/-- `oddSim` factored at rule 7 (`◇t → ◇h`, its phase `p4`). -/
private theorem oddSim_split7 (m : ℕ) :
    RuleSplits [dia, t] [dia, h] (config (2 * m + 1)) (config (3 * m + 2)) := by
  have key : List.replicate (3 * m + 2) one = List.replicate (3 * m) one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  refine RuleSplits.headD ((oddSim_p1 m).trans ((ReflTransGen.single (oddSim_p2 m)).trans
    (oddSim_p3 m))) ?_
  exact RuleSplits.of_eq [] (List.replicate (3 * m) one ++ [one, one, dia])
    (by simp) (by rw [config, key]; simp [List.append_assoc])

/-- `evenSim` factored at rule 2 (`11h◇ → 11s◇`, its phase `p2`). -/
private theorem evenSim_split2 (j : ℕ) (hj : 2 ≤ j) :
    RuleSplits [one, one, h, dia] [one, one, s, dia] (config (2 * j)) (config j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  have key : List.replicate (m + 2) one = List.replicate m one ++ [one, one] := by
    rw [List.replicate_add]; rfl
  refine RuleSplits.headD (evenSim_p1 m) (RuleSplits.tailD
    (RuleSplits.of_eq ([dia] ++ List.replicate m one) [] ?_ ?_)
    ((evenSim_p3 m).trans (ReflTransGen.single (evenSim_p4 m))))
  · rw [key]; simp [List.append_assoc]
  · rw [key]; simp [List.append_assoc]

/-- `evenSim` factored at rule 4 (`1s → s1`, inside its `s`-sweep). -/
private theorem evenSim_split4 (j : ℕ) (hj : 2 ≤ j) :
    RuleSplits [one, s] [s, one] (config (2 * j)) (config j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  refine RuleSplits.headD ((evenSim_p1 m).trans (ReflTransGen.single (evenSim_p2 m))) ?_
  refine RuleSplits.tailD ?_ (ReflTransGen.single (evenSim_p4 m))
  exact (sSweep_split (m + 2) (by omega)).context [dia] [dia]

/-- `evenSim` factored at rule 6 (`◇s → ◇h`, its phase `p4`). -/
private theorem evenSim_split6 (j : ℕ) (hj : 2 ≤ j) :
    RuleSplits [dia, s] [dia, h] (config (2 * j)) (config j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  refine RuleSplits.headD ((evenSim_p1 m).trans ((ReflTransGen.single (evenSim_p2 m)).trans
    (evenSim_p3 m))) ?_
  exact RuleSplits.of_eq [] (List.replicate (m + 2) one ++ [dia])
    (by simp) (by simp [config])

/-- **The simulation `◇h1^{8n+1}◇ →* ◇h1^{9n+2}◇` uses every rule of `𝒵`** (`n ≥ 1`): for *each* of the
seven rules `ℓ → r`, the derivation factors through a context application of it. (Three Collatz steps
`8n+1 ↦ 12n+2 ↦ 6n+1 ↦ 9n+2`; the head/odd machinery uses rules 1,3,5,7, the even machinery 1,2,4,6.) -/
private theorem simSplits (n : ℕ) (hn : 1 ≤ n) {ℓ r : List ZSym} (hZ : Z ℓ r) :
    RuleSplits ℓ r (config (8 * n + 1)) (config (9 * n + 2)) := by
  rcases hZ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · have hsp := oddSim_split1 (4 * n) (by omega)
    rw [show 2 * (4 * n) + 1 = 8 * n + 1 from by ring,
      show 3 * (4 * n) + 2 = 12 * n + 2 from by ring] at hsp
    exact hsp.tailD (simMid n hn)
  · have hsp := evenSim_split2 (6 * n + 1) (by omega)
    rw [show 2 * (6 * n + 1) = 12 * n + 2 from by ring] at hsp
    exact (hsp.headD (simHead n)).tailD (simC n)
  · have hsp := oddSim_split3 (4 * n)
    rw [show 2 * (4 * n) + 1 = 8 * n + 1 from by ring,
      show 3 * (4 * n) + 2 = 12 * n + 2 from by ring] at hsp
    exact hsp.tailD (simMid n hn)
  · have hsp := evenSim_split4 (6 * n + 1) (by omega)
    rw [show 2 * (6 * n + 1) = 12 * n + 2 from by ring] at hsp
    exact (hsp.headD (simHead n)).tailD (simC n)
  · have hsp := oddSim_split5 (4 * n) (by omega)
    rw [show 2 * (4 * n) + 1 = 8 * n + 1 from by ring,
      show 3 * (4 * n) + 2 = 12 * n + 2 from by ring] at hsp
    exact hsp.tailD (simMid n hn)
  · have hsp := evenSim_split6 (6 * n + 1) (by omega)
    rw [show 2 * (6 * n + 1) = 12 * n + 2 from by ring] at hsp
    exact (hsp.headD (simHead n)).tailD (simC n)
  · have hsp := oddSim_split7 (4 * n)
    rw [show 2 * (4 * n) + 1 = 8 * n + 1 from by ring,
      show 3 * (4 * n) + 2 = 12 * n + 2 from by ring] at hsp
    exact hsp.tailD (simMid n hn)

/-- For `n ≥ 1`, the strict rule's single guaranteed use (`simSplits`) makes `μ` strictly drop across
the simulation: `μ(◇h1^{9n+2}◇) < μ(◇h1^{8n+1}◇)`. -/
private theorem simStrict {d : ℕ} [NeZero d] (M : ZSym → Matrix (Fin d) (Fin d) ℕ)
    (v : ZSym → Fin d → ℕ) (hM : ∀ σ, M σ 0 0 = 1)
    (hweak : ∀ ℓ r, Z ℓ r → ∀ x, vecGe (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
      (strInterp (fun σ => affine (M σ) (v σ)) r x))
    {ℓ r : List ZSym} (hZ : Z ℓ r)
    (hℓr : ∀ x, vecGt (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
      (strInterp (fun σ => affine (M σ) (v σ)) r x))
    (n : ℕ) (hn : 1 ≤ n) : simMu M v (config (9 * n + 2)) < simMu M v (config (8 * n + 1)) := by
  obtain ⟨pre, post, h1, h2⟩ := simSplits n hn hZ
  calc simMu M v (config (9 * n + 2))
      ≤ simMu M v (pre ++ r ++ post) := simMu_chainLE M v hweak h2
    _ < simMu M v (pre ++ ℓ ++ post) := simMu_stepLT M v hM hℓr pre post
    _ ≤ simMu M v (config (8 * n + 1)) := simMu_chainLE M v hweak h1

/-- **Theorem 3.8** ([YAH]). Over Zantema's alphabet `Σ = {1, ◇, h, s, t}` (`ZSym`), there is **no**
collection of natural matrix interpretations (`SRS.MatrixInterpretation`) — for *any* dimension
`d ≥ 1` (`NeZero d`), interpreting each symbol `σ` by an affine map `[σ](x) = Mσ · x + vσ` over `ℕᵈ`
(`affine`) — meeting the requirements for an *extended* monotone `Σ`-algebra (here the corpus
condition `(Mσ)₀₀ = 1`, exactly the `hM` hypothesis of `extendedMonotoneAlgebra`) such that, for the
induced string interpretations `[·] = strInterp (fun σ => affine (Mσ) (vσ))`,

* **every** rule `ℓ → r ∈ 𝒵` weakly decreases — `[ℓ](x) ≳ [r](x)` for all `x ∈ ℕᵈ` (`vecGe`), and
* **at least one** rule `ℓ → r ∈ 𝒵` strictly decreases — `[ℓ](x) > [r](x)` for all `x ∈ ℕᵈ` (`vecGt`).

(Since `vecGt → vecGe`, "all rules weak ∧ ≥ 1 rule strict" is exactly the paper's "≥ 1 rule strict,
the remaining rules weak".)

Such an interpretation is precisely the data a **rule-removal** step (Theorem 2.6 `ruleRemoval`, via
`terminatingRelativeTo_of_extendedMonotone` with the strict rule as `R` and all of `𝒵` as `S`) would
consume to peel off a rule and progress towards `SN(𝒵)`; Theorem 3.8 says not even one such step
exists — the matrix-interpretation method is *powerless* on `𝒵`. Since `SN(𝒵) ↔ Collatz`
(`zantema_theorem_3_2`), any matrix-interpretation proof of `SN(𝒵)` would settle the Collatz-linked
termination, so its impossibility is unsurprising; Theorem 3.8 is the sharper statement that the
method fails *immediately*.

**Genuinely proved** (no extra axiom beyond `theorem_3_5`, on which `corollary_3_6` rests): assume
such an interpretation; the measure `μ(s) = [s](0)₀` is non-increasing along every `𝒵`-step
(`simMu_chainLE`) and strictly decreasing at the strict rule (`simMu_stepLT`); since the simulation
fires that rule (`simSplits`), `μ(◇h1^{8n+1}◇) > μ(◇h1^{9n+2}◇)` for all `n ≥ 1` (`simStrict`), while
`k ↦ μ(◇h1ᵏ◇)` is ℕ-rational (`simMu_config_isNRational`) — contradicting `corollary_3_6`. -/
@[category research solved, AMS 68 11, ref "YAH", group "zantema_collatz"]
theorem theorem_3_8 :
    ¬ ∃ (d : ℕ) (_ : NeZero d) (M : ZSym → Matrix (Fin d) (Fin d) ℕ) (v : ZSym → Fin d → ℕ),
      (∀ σ, M σ 0 0 = 1) ∧
      (∀ ℓ r, Z ℓ r → ∀ x, vecGe (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
        (strInterp (fun σ => affine (M σ) (v σ)) r x)) ∧
      ∃ ℓ r, Z ℓ r ∧ ∀ x, vecGt (strInterp (fun σ => affine (M σ) (v σ)) ℓ x)
        (strInterp (fun σ => affine (M σ) (v σ)) r x) := by
  rintro ⟨d, hd, M, v, hM, hweak, ℓ, r, hZ, hℓr⟩
  haveI : NeZero d := hd
  refine corollary_3_6 ⟨fun k => simMu M v (config k), simMu_config_isNRational M v, fun n hn => ?_⟩
  exact simStrict M v hM hweak hZ hℓr n hn

end StringRewriting.Zantema
