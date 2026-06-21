/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Ring
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# String rewriting systems (Book–Otto §2)

The opening definitions of Book and Otto's monograph on string-rewriting (*String-Rewriting
Systems*, [BO93]). An alphabet `Σ` is a set of symbols; here it is an arbitrary type `α`, and
the *strings* over it — Book and Otto's `Σ*` — are the elements of `List α`.

**Convention.** A relation on strings is, equivalently, a subset `R ⊆ Σ* × Σ*` (its graph) or a
binary predicate `List α → List α → Prop`; we use the latter, so that `R ℓ r` means `(ℓ, r) ∈ R`
("`ℓ → r` is a rule of `R`") and the induced relation composes directly with Mathlib's relation
combinators (e.g. `Relation.ReflTransGen (RewriteStep R)` is the reflexive–transitive closure
`→*_R`).

* `StringRewriting.System α` — a **string rewriting system** (SRS) over `α`: a relation on the
  strings `List α`. Each pair `ℓ → r` it relates is a *rewrite rule*.
* `StringRewriting.RewriteStep R` — the **rewrite relation** `→_R` the system induces:
  `u →_R v` iff `u = sℓt` and `v = srt` for some strings `s, t` and some rule `ℓ → r` of `R`.
  Every rule is itself a one-step rewrite (`RewriteStep.of_rule`), and `→_R` is closed under
  surrounding context (`RewriteStep.append_context`) — the two basic facts that make `→_R` the
  rewrite relation of `R`.
* `StringRewriting.Terminating r` — the **termination** (`SN`) of an abstract relation `r` (`→`)
  on a type `α`: no infinite chain `s₀ → s₁ → ⋯`. This is exactly Mathlib's `WellFounded` of the
  converse relation (`terminating_iff_wellFounded`); a strictly decreasing `ℕ`-measure forces it
  (`terminating_of_measure`).
* **Examples** over the two-letter alphabet `Sym = {a, b}`: `R₁ = {aa → a}` and `R₃ = {ab → ba}`
  are terminating (`terminating_R₁` via the length measure; `terminating_R₃` via the inversion
  count `invCount`), whereas `R₂ = {a → aa}` is not (`not_terminating_R₂`, the chain
  `a → aa → aaa → ⋯`).
* `StringRewriting.TerminatingRelativeTo r₁ r₂` — **Definition 2.4**, relative termination
  `SN(→₁ / →₂)`: no infinite chain takes `→₁`-steps infinitely often and `→₂`-steps otherwise. It
  generalises `Terminating` (`terminatingRelativeTo_empty`: `SN(→ / ∅) = SN(→)`), and a measure
  decreasing on `r₁` and non-increasing on `r₂` proves it (`terminatingRelativeTo_of_measure`).
* **Example 2.5**: for `R = {aa → aba}`, `S = {b → bb}`, the union `R ∪ S` is *not* terminating
  (`not_terminating_union`, via `S`), yet `R` *is* terminating relative to `S`
  (`terminating_R_relative_S`) — proved with the `aa`-factor count `adjAA`, which `R` strictly
  decreases and `S` preserves.
* `StringRewriting.ruleRemoval` — **Theorem 2.6** (rule removal, [Zan05, Theorem 1]): for `T ⊆ R`,
  if `SN(T / R)` and `SN(R \ T)` then `SN(R)`. It reduces (`terminating_of_terminatingRelativeTo`)
  to the relation-level fact that `→_R = →_T ∪ →_{R∖T}` (`rewriteStep_union_diff`).
* `StringRewriting.System.reverse` — **Definition 2.7**, the reversal `Rʳᵉᵛ` (reverse every rule
  `ℓ → r` to `ℓʳᵉᵛ → rʳᵉᵛ`). `StringRewriting.ruleReversal` — **Lemma 2.8** ([Zan05, Lemma 2]):
  `SN(R / S) ↔ SN(Rʳᵉᵛ / Sʳᵉᵛ)`, because reversal conjugates `→_R` (`rewriteStep_reverse`) and
  relative termination is invariant under conjugation (`terminatingRelativeTo_comp`).
* `StringRewriting.TopRewriteStep` / `TopTerminating` — **Definition 2.9**: the *top* rewrite
  relation `→_{R_top}` (rewriting only at the front, `ℓ s → r s`) and top termination. Since
  `→_{R_top} ⊆ →_R` (`TopRewriteStep.toRewriteStep`), termination implies top termination
  (`topTerminating_of_terminating`).

## References
* [BO93] Book, Ronald V. and Otto, Friedrich. *String-Rewriting Systems.* Texts and Monographs
  in Computer Science. Springer-Verlag, New York, 1993.
* [Zan05] Zantema, Hans. "Termination of string rewriting proved automatically." *Journal of
  Automated Reasoning* 34.2 (2005), 105–139.
-/

namespace StringRewriting

variable {α : Type*}

/-- **Definition 2.1** (Book–Otto). Let `α` be an alphabet, i.e. a type of symbols, and let the
*strings* over `α` be the elements of `List α` (Book and Otto's `Σ*`). A **string rewriting
system** (SRS) over `α` is a relation `R ⊆ Σ* × Σ*`, here a binary predicate on `List α`. The
pairs it relates are the *rewrite rules*: `R ℓ r` means `(ℓ, r) ∈ R`, usually written `ℓ → r`. -/
@[category API, AMS 68, ref "BO93"]
abbrev System (α : Type*) : Type _ := List α → List α → Prop

/-- **Definition 2.1** (Book–Otto). The **rewrite relation** `→_R` induced by a string rewriting
system `R` on the strings `List α`:
`→_R := {(sℓt, srt) | s, t ∈ Σ*, ℓ → r ∈ R}`.
That is, `RewriteStep R u v` (`u →_R v`) holds iff `u = s ++ ℓ ++ t` and `v = s ++ r ++ t` for some
strings `s, t` and some rule `ℓ → r` of `R` — a single rewrite applied inside a fixed context. -/
@[category API, AMS 68, ref "BO93"]
def RewriteStep (R : System α) (u v : List α) : Prop :=
  ∃ s t ℓ r, R ℓ r ∧ u = s ++ ℓ ++ t ∧ v = s ++ r ++ t

/-- A rewrite rule `ℓ → r` of `R` is in particular a one-step rewrite `ℓ →_R r` (apply it in the
empty context, `s = t = []`). So `R ⊆ →_R`. -/
@[category API, AMS 68, ref "BO93"]
theorem RewriteStep.of_rule {R : System α} {ℓ r : List α} (h : R ℓ r) :
    RewriteStep R ℓ r := by
  refine ⟨[], [], ℓ, r, h, ?_, ?_⟩ <;> simp

/-- The rewrite relation `→_R` is closed under surrounding context: if `u →_R v` then
`s ++ u ++ t →_R s ++ v ++ t` for all strings `s, t`. (This is why `→_R` is defined with arbitrary
context strings — it makes `→_R` a congruence for concatenation.) -/
@[category API, AMS 68, ref "BO93"]
theorem RewriteStep.append_context {R : System α} {u v : List α}
    (h : RewriteStep R u v) (s t : List α) :
    RewriteStep R (s ++ u ++ t) (s ++ v ++ t) := by
  obtain ⟨s', t', ℓ, r, hrule, hu, hv⟩ := h
  refine ⟨s ++ s', t' ++ t, ℓ, r, hrule, ?_, ?_⟩
  · rw [hu]; simp [List.append_assoc]
  · rw [hv]; simp [List.append_assoc]

/-- Sanity check: the empty system (no rules) induces the empty rewrite relation — it rewrites
nothing. -/
@[category test, AMS 68, ref "BO93"]
theorem rewriteStep_empty (u v : List α) :
    ¬ RewriteStep (fun _ _ => False) u v := by
  rintro ⟨s, t, ℓ, r, h, -, -⟩
  exact h

/-! ### Termination -/

/-- **Definition 2.2** (Book–Otto). A relation `r` — written `→` — on a type `α` (Book and Otto's
set `A`) is **terminating** if there is no infinite sequence `s₀, s₁, … : α` with `sᵢ → sᵢ₊₁` for
all `i ≥ 0`. A terminating relation is also called *Noetherian*, *well-founded*, or *strongly
normalizing*, and Book and Otto write `SN(→)`. (`terminating_iff_wellFounded` identifies it with
Mathlib's `WellFounded`.) -/
@[category API, AMS 68, ref "BO93"]
def Terminating (r : α → α → Prop) : Prop :=
  ¬ ∃ s : ℕ → α, ∀ i, r (s i) (s (i + 1))

/-- Sanity check: the empty relation (no steps) is terminating — no sequence can take even one
step. -/
@[category test, AMS 68, ref "BO93"]
theorem terminating_empty : Terminating (fun _ _ : α => False) := by
  rintro ⟨s, hs⟩
  exact hs 0

/-- Book and Otto's termination (`SN(→)`) is exactly Mathlib's well-foundedness of the **converse**
relation `← := fun a b => r b a`: an infinite forward chain `s₀ → s₁ → ⋯` for `r` is the same data
as an infinite descending chain for `←`. This is the bridge that justifies calling a terminating
relation *well-founded*, and lets the corpus reuse Mathlib's well-founded recursion / induction. -/
@[category API, AMS 68, ref "BO93"]
theorem terminating_iff_wellFounded {r : α → α → Prop} :
    Terminating r ↔ WellFounded (fun a b => r b a) := by
  unfold Terminating
  rw [wellFounded_iff_isEmpty_descending_chain, not_exists]
  exact (isEmpty_subtype fun f : ℕ → α => ∀ n, r (f n) (f (n + 1))).symm

/-- The standard way to prove termination: if `r` admits an `ℕ`-valued **measure** `μ` that
strictly decreases along every step (`r u v → μ v < μ u`), then `r` is terminating — an infinite
chain would give an infinite strictly decreasing sequence in `ℕ`, which is impossible. -/
@[category API, AMS 68, ref "BO93"]
theorem terminating_of_measure {r : α → α → Prop} (μ : α → ℕ)
    (h : ∀ u v, r u v → μ v < μ u) : Terminating r := by
  rintro ⟨s, hs⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp wellFounded_lt).elim
    ⟨fun i => μ (s i), fun i => h _ _ (hs i)⟩

/-- **Termination from a restricted set of start states.** `TerminatingFrom r P` holds when no
infinite `r`-chain `s₀ → s₁ → ⋯` has its *initial* state `s₀` satisfying `P`. It weakens
`Terminating` by only forbidding infinite chains that begin in `P`; taking `P` always-true recovers
`Terminating`. This is the shape of a *reduction-to-canonical-forms* hypothesis: "the system
terminates on every start string of the canonical form `P`". -/
@[category API, AMS 68, ref "BO93"]
def TerminatingFrom (r : α → α → Prop) (P : α → Prop) : Prop :=
  ¬ ∃ s : ℕ → α, P (s 0) ∧ ∀ i, r (s i) (s (i + 1))

/-- A terminating relation is terminating from *any* set of start states — an infinite chain
beginning in `P` is in particular an infinite chain. (The "obvious" converse whenever one restricts
the allowed initial strings: `SN(→) → SN(→` from `P`).) -/
@[category API, AMS 68, ref "BO93"]
theorem terminatingFrom_of_terminating {r : α → α → Prop} (P : α → Prop)
    (h : Terminating r) : TerminatingFrom r P := by
  rintro ⟨s, -, hs⟩
  exact h ⟨s, hs⟩

/-! ### Examples (Book–Otto §2)

Three rewriting systems over the two-letter alphabet `Sym = {a, b}`, illustrating termination. -/

/-- The two-letter alphabet `{a, b}` used in Book and Otto's examples. -/
@[category API, AMS 68, ref "BO93"]
inductive Sym | a | b
  deriving DecidableEq

/-- `R₁ = {aa → a}`. -/
@[category API, AMS 68, ref "BO93"]
def R₁ : System Sym := fun ℓ r => ℓ = [Sym.a, Sym.a] ∧ r = [Sym.a]

/-- `R₂ = {a → aa}`. -/
@[category API, AMS 68, ref "BO93"]
def R₂ : System Sym := fun ℓ r => ℓ = [Sym.a] ∧ r = [Sym.a, Sym.a]

/-- `R₃ = {ab → ba}`. -/
@[category API, AMS 68, ref "BO93"]
def R₃ : System Sym := fun ℓ r => ℓ = [Sym.a, Sym.b] ∧ r = [Sym.b, Sym.a]

/-- Each `R₁`-rewrite `aa → a` decreases the length of the string by exactly one. -/
@[category API, AMS 68, ref "BO93"]
theorem rewriteStep_R₁_length {u v : List Sym} (h : RewriteStep R₁ u v) :
    v.length + 1 = u.length := by
  obtain ⟨s, t, ℓ, r, ⟨hℓ, hr⟩, hu, hv⟩ := h
  subst hℓ hr hu hv
  simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **`R₁ = {aa → a}` is terminating**, proved easily by observing that each rewrite decreases the
length of a string by 1 (`rewriteStep_R₁_length`), so the length is a strictly decreasing
measure. -/
@[category textbook, AMS 68, ref "BO93",
  formal_uses terminating_of_measure rewriteStep_R₁_length]
theorem terminating_R₁ : Terminating (RewriteStep R₁) :=
  terminating_of_measure List.length fun u v h => by have := rewriteStep_R₁_length h; omega

/-- **`R₂ = {a → aa}` is not terminating**: even a single occurrence of `a` allows indefinitely
producing more of the symbol `a`. The witnessing infinite chain is `a → aa → aaa → ⋯`, i.e.
`sₙ = aⁿ⁺¹` (`List.replicate (n+1) a`), with each step `aⁿ⁺¹ →_{R₂} aⁿ⁺²` rewriting the leading
`a`. -/
@[category textbook, AMS 68, ref "BO93"]
theorem not_terminating_R₂ : ¬ Terminating (RewriteStep R₂) := by
  intro hT
  apply hT
  refine ⟨fun n => List.replicate (n + 1) Sym.a, fun n => ?_⟩
  refine ⟨[], List.replicate n Sym.a, [Sym.a], [Sym.a, Sym.a], ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp [List.replicate_succ]
  · simp [List.replicate_succ]

/-- `numA u` / `numB u`: the number of `a`s / of `b`s in the string `u`. -/
@[category API, AMS 68, ref "BO93"]
def numA : List Sym → ℕ
  | [] => 0
  | Sym.a :: t => numA t + 1
  | Sym.b :: t => numA t

@[category API, AMS 68, ref "BO93"]
def numB : List Sym → ℕ
  | [] => 0
  | Sym.a :: t => numB t
  | Sym.b :: t => numB t + 1

/-- `invCount u`: the number of **inversions** of `u`, i.e. of pairs of positions `i < j` with
`uᵢ = a` and `uⱼ = b` (an `a` standing before a `b`). This is the measure that proves `R₃`
terminates: a string is `R₃`-irreducible iff it has no inversions, i.e. has the form `b*a*`. -/
@[category API, AMS 68, ref "BO93"]
def invCount : List Sym → ℕ
  | [] => 0
  | Sym.a :: t => numB t + invCount t
  | Sym.b :: t => invCount t

@[category API, AMS 68, ref "BO93"]
theorem numA_append (s t : List Sym) : numA (s ++ t) = numA s + numA t := by
  induction s with
  | nil => simp [numA]
  | cons x s ih => cases x <;> simp +arith [numA, ih]

@[category API, AMS 68, ref "BO93"]
theorem numB_append (s t : List Sym) : numB (s ++ t) = numB s + numB t := by
  induction s with
  | nil => simp [numB]
  | cons x s ih => cases x <;> simp +arith [numB, ih]

/-- Inversions split over a concatenation: the inversions of `s ++ t` are those within `s`, those
within `t`, and the `numA s · numB t` cross pairs (an `a` in `s` before a `b` in `t`). -/
@[category API, AMS 68, ref "BO93", formal_uses numB_append]
theorem invCount_append (s t : List Sym) :
    invCount (s ++ t) = invCount s + invCount t + numA s * numB t := by
  induction s with
  | nil => simp [invCount, numA]
  | cons x s ih =>
    cases x
    · simp only [List.cons_append, invCount, numA, numB_append, ih]; ring
    · simp only [List.cons_append, invCount, numA, ih]

/-- Each `R₃`-rewrite `ab → ba` decreases the inversion count by exactly one: the rewritten `a, b`
pair (one cross inversion) becomes `b, a` (none), while the `numA s · numB t` cross terms with the
surrounding context are unchanged. -/
@[category API, AMS 68, ref "BO93", formal_uses invCount_append numA_append]
theorem rewriteStep_R₃_invCount {u v : List Sym} (h : RewriteStep R₃ u v) :
    invCount v + 1 = invCount u := by
  obtain ⟨s, t, ℓ, r, ⟨hℓ, hr⟩, hu, hv⟩ := h
  subst hℓ hr hu hv
  simp only [invCount_append, numA_append, invCount, numA, numB]; ring

/-- **`R₃ = {ab → ba}` is terminating**, since all rewrite sequences eventually convert a given
string into the form `b*a*` and stop. Formally, every `ab → ba` step strictly drops the inversion
count `invCount` (`rewriteStep_R₃_invCount`), which is therefore a terminating measure. -/
@[category textbook, AMS 68, ref "BO93",
  formal_uses terminating_of_measure rewriteStep_R₃_invCount]
theorem terminating_R₃ : Terminating (RewriteStep R₃) :=
  terminating_of_measure invCount fun u v h => by have := rewriteStep_R₃_invCount h; omega

/-- The first step of Book and Otto's worked example, `abbab →_{R₃} babab` (rewriting the leading
`ab`). The full sequence in the book continues `babab → bbaab → bbaba → bbbaa`. -/
@[category test, AMS 68, ref "BO93"]
theorem rewriteStep_R₃_example :
    RewriteStep R₃ [Sym.a, Sym.b, Sym.b, Sym.a, Sym.b] [Sym.b, Sym.a, Sym.b, Sym.a, Sym.b] := by
  refine ⟨[], [Sym.b, Sym.a, Sym.b], [Sym.a, Sym.b], [Sym.b, Sym.a], ⟨rfl, rfl⟩, ?_, ?_⟩ <;> simp

/-! ### Relative termination (Book–Otto §2) -/

open Filter

/-- **Definition 2.4** (Book–Otto, relative termination). Given relations `r₁`, `r₂` (written `→₁`,
`→₂`) on a type `α`, `r₁` is **terminating relative to** `r₂` — written `SN(→₁ / →₂)` — if there is
no infinite sequence `s₀, s₁, … : α` that takes a `→₁`-step infinitely often (`∃ᶠ i`, the "infinitely
many `i`") and a `→₂`-step at every other index (every non-`→₁` step is a `→₂` step). Equivalently
(`terminatingRelativeTo_empty`), for systems `R`, `S` this says every `R ∪ S`-rewrite sequence
applies the `R`-rules at most finitely often; and since `SN(→ / ∅) = SN(→)`, relative termination
generalises ordinary termination. -/
@[category API, AMS 68, ref "BO93"]
def TerminatingRelativeTo (r₁ r₂ : α → α → Prop) : Prop :=
  ¬ ∃ s : ℕ → α,
    (∃ᶠ i in atTop, r₁ (s i) (s (i + 1))) ∧
    ∀ i, ¬ r₁ (s i) (s (i + 1)) → r₂ (s i) (s (i + 1))

/-- Book and Otto's note that **`SN(→ / ∅) = SN(→)`**: termination relative to the empty relation
is ordinary termination. A sequence witnessing non-relative-termination must, off its infinitely
many `→`-steps, take `∅`-steps — impossible — so in fact every step is a `→`-step, recovering
`Terminating`. -/
@[category textbook, AMS 68, ref "BO93"]
theorem terminatingRelativeTo_empty (r : α → α → Prop) :
    TerminatingRelativeTo r (fun _ _ => False) ↔ Terminating r := by
  unfold TerminatingRelativeTo Terminating
  refine not_congr (exists_congr fun s => ?_)
  constructor
  · rintro ⟨-, h2⟩ i
    exact not_not.mp (h2 i)
  · intro h
    exact ⟨Frequently.of_forall fun i => h i, fun i hi => absurd (h i) hi⟩

/-- The standard tool for relative termination: a **measure** `μ : α → ℕ` that strictly decreases
along every `r₁`-step and never increases along an `r₂`-step proves `SN(r₁ / r₂)`. Along any
`r₁ ∪ r₂`-chain `μ` is then non-increasing and drops at each `r₁`-step, so `r₁` can be applied only
finitely often — otherwise `μ` would form an infinite strictly decreasing sequence in `ℕ`. -/
@[category API, AMS 68, ref "BO93"]
theorem terminatingRelativeTo_of_measure {r₁ r₂ : α → α → Prop} (μ : α → ℕ)
    (h₁ : ∀ u v, r₁ u v → μ v < μ u) (h₂ : ∀ u v, r₂ u v → μ v ≤ μ u) :
    TerminatingRelativeTo r₁ r₂ := by
  rintro ⟨s, hfreq, hrest⟩
  have hanti : Antitone (fun i => μ (s i)) := by
    apply antitone_nat_of_succ_le
    intro i
    by_cases hr : r₁ (s i) (s (i + 1))
    · exact (h₁ _ _ hr).le
    · exact h₂ _ _ (hrest i hr)
  have hfreq' : ∃ᶠ i in atTop, μ (s (i + 1)) < μ (s i) := hfreq.mono fun i hi => h₁ _ _ hi
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq'
  refine (wellFounded_iff_isEmpty_descending_chain.mp wellFounded_lt).elim
    ⟨fun k => μ (s (φ k)), fun k => ?_⟩
  calc μ (s (φ (k + 1))) ≤ μ (s (φ k + 1)) := hanti (Nat.succ_le_of_lt (hφ (Nat.lt_succ_self k)))
    _ < μ (s (φ k)) := hφP k

/-- The **union** `R ∪ S` of two rewriting systems: a pair is a rule of the union iff it is a rule
of `R` or a rule of `S`. -/
@[category API, AMS 68, ref "BO93"]
def System.union (R S : System α) : System α := fun ℓ r => R ℓ r ∨ S ℓ r

/-! ### Example 2.5 -/

/-- `R = {aa → aba}`. -/
@[category API, AMS 68, ref "BO93"]
def R : System Sym := fun ℓ r => ℓ = [Sym.a, Sym.a] ∧ r = [Sym.a, Sym.b, Sym.a]

/-- `S = {b → bb}`. -/
@[category API, AMS 68, ref "BO93"]
def S : System Sym := fun ℓ r => ℓ = [Sym.b] ∧ r = [Sym.b, Sym.b]

/-- `adjAA u`: the number of `aa` factors of `u`, i.e. of positions `i` with `uᵢ = uᵢ₊₁ = a`. This
is the measure that proves `SN(R / S)`: `aa → aba` destroys one `aa` factor, while `b → bb` creates
none. -/
@[category API, AMS 68, ref "BO93"]
def adjAA : List Sym → ℕ
  | [] => 0
  | x :: rest => adjAA rest + (if x = Sym.a ∧ rest.head? = some Sym.a then 1 else 0)

/-- Peeling one symbol off the front: prepending `x` adds an `aa` factor exactly when both `x` and
the previous head are `a`. -/
@[category API, AMS 68, ref "BO93"]
theorem adjAA_cons (x : Sym) (L : List Sym) :
    adjAA (x :: L) = adjAA L + (if x = Sym.a ∧ L.head? = some Sym.a then 1 else 0) := rfl

/-- Applying `aa → aba` inside any context `s … t` removes exactly one `aa` factor: the matched
`aa` becomes `aba`, and since both `aa` and `aba` start and end with `a`, the factors crossing the
boundaries with `s` and `t` are unchanged. -/
@[category API, AMS 68, ref "BO93", formal_uses adjAA_cons]
theorem adjAA_R (s t : List Sym) :
    adjAA (s ++ Sym.a :: Sym.a :: t) = adjAA (s ++ Sym.a :: Sym.b :: Sym.a :: t) + 1 := by
  induction s with
  | nil => simp [adjAA_cons]
  | cons x s' ih =>
    have hhead : (s' ++ Sym.a :: Sym.a :: t).head? = (s' ++ Sym.a :: Sym.b :: Sym.a :: t).head? := by
      cases s' <;> simp
    simp only [List.cons_append, adjAA_cons, ih, hhead]; ring

/-- Applying `b → bb` inside any context preserves the number of `aa` factors (it only touches
`b`s). -/
@[category API, AMS 68, ref "BO93", formal_uses adjAA_cons]
theorem adjAA_S (s t : List Sym) :
    adjAA (s ++ Sym.b :: t) = adjAA (s ++ Sym.b :: Sym.b :: t) := by
  induction s with
  | nil => simp [adjAA_cons]
  | cons x s' ih =>
    have hhead : (s' ++ Sym.b :: t).head? = (s' ++ Sym.b :: Sym.b :: t).head? := by
      cases s' <;> simp
    simp only [List.cons_append, adjAA_cons, ih, hhead]

/-- Every `R`-rewrite strictly decreases `adjAA` (by exactly one). -/
@[category API, AMS 68, ref "BO93", formal_uses adjAA_R]
theorem rewriteStep_R_adjAA {u v : List Sym} (h : RewriteStep R u v) : adjAA v + 1 = adjAA u := by
  obtain ⟨s, t, ℓ, r, ⟨hℓ, hr⟩, hu, hv⟩ := h
  subst hℓ hr hu hv
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have := adjAA_R s t; omega

/-- Every `S`-rewrite preserves `adjAA`. -/
@[category API, AMS 68, ref "BO93", formal_uses adjAA_S]
theorem rewriteStep_S_adjAA {u v : List Sym} (h : RewriteStep S u v) : adjAA v = adjAA u := by
  obtain ⟨s, t, ℓ, r, ⟨hℓ, hr⟩, hu, hv⟩ := h
  subst hℓ hr hu hv
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact (adjAA_S s t).symm

/-- **The system `R ∪ S` is not terminating**, since `S = {b → bb}` already gives rise to the
infinite rewrite sequence `b → bb → bbb → ⋯` (here `bⁿ⁺¹ = List.replicate (n+1) b`). -/
@[category textbook, AMS 68, ref "BO93"]
theorem not_terminating_union : ¬ Terminating (RewriteStep (System.union R S)) := by
  intro hT
  apply hT
  refine ⟨fun n => List.replicate (n + 1) Sym.b, fun n => ?_⟩
  refine ⟨[], List.replicate n Sym.b, [Sym.b], [Sym.b, Sym.b], Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp [List.replicate_succ]
  · simp [List.replicate_succ]

/-- **`R` is terminating relative to `S`** (`SN(R / S)`): although `R ∪ S` is not terminating
(`not_terminating_union`), `R` by itself is terminating and applying `b → bb` does not facilitate
further applications of `aa → aba`. Formally, the `aa`-factor count `adjAA` strictly decreases on
every `R`-step (`rewriteStep_R_adjAA`) and is preserved by every `S`-step (`rewriteStep_S_adjAA`),
so `terminatingRelativeTo_of_measure` applies. -/
@[category textbook, AMS 68, ref "BO93",
  formal_uses terminatingRelativeTo_of_measure rewriteStep_R_adjAA rewriteStep_S_adjAA]
theorem terminating_R_relative_S : TerminatingRelativeTo (RewriteStep R) (RewriteStep S) :=
  terminatingRelativeTo_of_measure adjAA
    (fun _ _ h => by have := rewriteStep_R_adjAA h; omega)
    (fun _ _ h => by have := rewriteStep_S_adjAA h; omega)

/-! ### Rule removal (Book–Otto Theorem 2.6 / [Zan05]) -/

/-- The relation-level content of the **rule-removal theorem** [Zan05, Theorem 1]. If a relation
`r` splits as `t ∪ u`, with `t` terminating relative to `r` (`SN(t / r)`) and `u` terminating
(`SN(u)`), then `r` is terminating. Proof: in an infinite `r`-chain, either `t`-steps occur
infinitely often — impossible by `SN(t / r)`, since every step is also an `r`-step — or only
finitely often, in which case a tail of the chain consists entirely of `u`-steps, an infinite
`u`-chain forbidden by `SN(u)`. -/
@[category research solved, AMS 68, ref "Zan05", group "rule_removal"]
theorem terminating_of_terminatingRelativeTo {r t u : α → α → Prop}
    (hr : ∀ x y, r x y ↔ t x y ∨ u x y)
    (h₁ : TerminatingRelativeTo t r) (h₂ : Terminating u) : Terminating r := by
  rintro ⟨s, hs⟩
  by_cases hfreq : ∃ᶠ i in atTop, t (s i) (s (i + 1))
  · -- `t`-steps infinitely often: the chain witnesses ¬ SN(t / r).
    exact h₁ ⟨s, hfreq, fun i _ => hs i⟩
  · -- only finitely many `t`-steps: a tail is an infinite `u`-chain, witnessing ¬ SN(u).
    rw [not_frequently] at hfreq
    obtain ⟨N, hN⟩ := eventually_atTop.mp hfreq
    apply h₂
    refine ⟨fun i => s (N + i), fun i => ?_⟩
    rcases (hr _ _).mp (hs (N + i)) with ht | hu
    · exact absurd ht (hN (N + i) (Nat.le_add_right N i))
    · exact hu

/-- The **difference** `R \ T`: the rules of `R` that are not rules of `T`. -/
@[category API, AMS 68, ref "BO93"]
def System.diff (R T : System α) : System α := fun ℓ r => R ℓ r ∧ ¬ T ℓ r

/-- For `T ⊆ R`, the one-step rewrite relation of `R` splits as `→_R = →_T ∪ →_{R∖T}`: any
`R`-rewrite uses a rule of `R`, which lies either in `T` or in `R \ T`. -/
@[category API, AMS 68, ref "BO93"]
theorem rewriteStep_union_diff (R T : System α) (hsub : ∀ ℓ w, T ℓ w → R ℓ w) (x y : List α) :
    RewriteStep R x y ↔ RewriteStep T x y ∨ RewriteStep (System.diff R T) x y := by
  constructor
  · rintro ⟨s, t, ℓ, w, hRw, hx, hy⟩
    by_cases hT : T ℓ w
    · exact Or.inl ⟨s, t, ℓ, w, hT, hx, hy⟩
    · exact Or.inr ⟨s, t, ℓ, w, ⟨hRw, hT⟩, hx, hy⟩
  · rintro (⟨s, t, ℓ, w, hTw, hx, hy⟩ | ⟨s, t, ℓ, w, ⟨hRw, _⟩, hx, hy⟩)
    · exact ⟨s, t, ℓ, w, hsub ℓ w hTw, hx, hy⟩
    · exact ⟨s, t, ℓ, w, hRw, hx, hy⟩

/-- **Theorem 2.6** (Rule removal, [Zan05, Theorem 1]). Let `R` be an SRS and `T ⊆ R` a subset of
its rules. If `T` is terminating relative to `R` (`SN(T / R)`) and `R \ T` is terminating
(`SN(R \ T)`), then `R` is terminating (`SN(R)`). Since `→_R = →_T ∪ →_{R∖T}`
(`rewriteStep_union_diff`), this is the abstract rule-removal lemma
`terminating_of_terminatingRelativeTo`. -/
@[category research solved, AMS 68, ref "Zan05", group "rule_removal",
  formal_uses terminating_of_terminatingRelativeTo rewriteStep_union_diff]
theorem ruleRemoval (R T : System α) (hsub : ∀ ℓ w, T ℓ w → R ℓ w)
    (h₁ : TerminatingRelativeTo (RewriteStep T) (RewriteStep R))
    (h₂ : Terminating (RewriteStep (System.diff R T))) :
    Terminating (RewriteStep R) :=
  terminating_of_terminatingRelativeTo (rewriteStep_union_diff R T hsub) h₁ h₂

/-! ### Reversal (Book–Otto Definition 2.7) and rule reversal ([Zan05] Lemma 2.8) -/

/-- Relative termination transfers along a map `e` that **conjugates** the relations: if
`r₁' a b ↔ r₁ (e a) (e b)` and `r₂' a b ↔ r₂ (e a) (e b)`, then `SN(r₁ / r₂)` gives `SN(r₁' / r₂')`
— map a bad `r₁'/r₂'` chain through `e` to a bad `r₁/r₂` chain. The engine behind rule reversal. -/
@[category API, AMS 68, ref "BO93"]
theorem terminatingRelativeTo_comp {r₁ r₂ r₁' r₂' : α → α → Prop} (e : α → α)
    (h₁ : ∀ a b, r₁' a b ↔ r₁ (e a) (e b)) (h₂ : ∀ a b, r₂' a b ↔ r₂ (e a) (e b))
    (H : TerminatingRelativeTo r₁ r₂) : TerminatingRelativeTo r₁' r₂' := by
  rintro ⟨s, hfreq, hrest⟩
  refine H ⟨fun i => e (s i), hfreq.mono fun i hi => (h₁ _ _).mp hi, fun i hi => ?_⟩
  exact (h₂ _ _).mp (hrest i fun h => hi ((h₁ _ _).mp h))

/-- **Definition 2.7** (reversal). The **reversal** `Rʳᵉᵛ` of an SRS `R`: the system whose rules are
the reversed rules `ℓʳᵉᵛ → rʳᵉᵛ` of `R`, where `sʳᵉᵛ = s.reverse`. Since `List.reverse` is an
involution this point-wise form `R ℓʳᵉᵛ rʳᵉᵛ` equals the set-builder `{ℓʳᵉᵛ → rʳᵉᵛ | ℓ → r ∈ R}`
(`system_reverse_iff`). -/
@[category API, AMS 68, ref "BO93"]
def System.reverse (R : System α) : System α := fun ℓ r => R ℓ.reverse r.reverse

/-- Reversal in set-builder form: `Rʳᵉᵛ a b` iff `a`, `b` are the reversals of the two sides of
some rule of `R` — i.e. `Rʳᵉᵛ = {ℓʳᵉᵛ → rʳᵉᵛ | ℓ → r ∈ R}`, exactly Definition 2.7. -/
@[category API, AMS 68, ref "BO93"]
theorem system_reverse_iff (R : System α) (a b : List α) :
    System.reverse R a b ↔ ∃ ℓ r, R ℓ r ∧ a = ℓ.reverse ∧ b = r.reverse := by
  constructor
  · intro h
    exact ⟨a.reverse, b.reverse, h, by simp, by simp⟩
  · rintro ⟨ℓ, r, hR, ha, hb⟩
    subst ha hb
    simpa [System.reverse] using hR

/-- Reversal is an involution on systems: `(Rʳᵉᵛ)ʳᵉᵛ = R`. -/
@[category API, AMS 68, ref "BO93"]
theorem System.reverse_reverse (R : System α) : System.reverse (System.reverse R) = R := by
  funext ℓ r; simp [System.reverse]

/-- Reversal **conjugates** the one-step rewrite relation: `u →_{Rʳᵉᵛ} v` iff `uʳᵉᵛ →_R vʳᵉᵛ`. A
rewrite `s ℓ t → s r t` mirrors to `tʳᵉᵛ ℓʳᵉᵛ sʳᵉᵛ → tʳᵉᵛ rʳᵉᵛ sʳᵉᵛ`. -/
@[category API, AMS 68, ref "BO93"]
theorem rewriteStep_reverse (R : System α) (a b : List α) :
    RewriteStep (System.reverse R) a b ↔ RewriteStep R a.reverse b.reverse := by
  constructor
  · rintro ⟨s, t, ℓ, r, hR, ha, hb⟩
    subst ha hb
    exact ⟨t.reverse, s.reverse, ℓ.reverse, r.reverse, hR,
      by simp [List.reverse_append], by simp [List.reverse_append]⟩
  · rintro ⟨s, t, ℓ, r, hR, ha, hb⟩
    have ha' : a = (s ++ ℓ ++ t).reverse := by rw [← ha, List.reverse_reverse]
    have hb' : b = (s ++ r ++ t).reverse := by rw [← hb, List.reverse_reverse]
    refine ⟨t.reverse, s.reverse, ℓ.reverse, r.reverse, ?_, ?_, ?_⟩
    · simp only [System.reverse, List.reverse_reverse]; exact hR
    · rw [ha']; simp [List.reverse_append]
    · rw [hb']; simp [List.reverse_append]

/-- **Lemma 2.8** (Rule reversal, [Zan05, Lemma 2]). For SRSs `R`, `S`, relative termination is
invariant under reversal: `SN(R / S)` **iff** `SN(Rʳᵉᵛ / Sʳᵉᵛ)`. Reversal conjugates the rewrite
relations (`rewriteStep_reverse`) and relative termination is conjugation-invariant
(`terminatingRelativeTo_comp`); the backward direction uses that reversal is an involution
(`System.reverse_reverse`). -/
@[category research solved, AMS 68, ref "Zan05",
  formal_uses terminatingRelativeTo_comp rewriteStep_reverse System.reverse_reverse]
theorem ruleReversal (R S : System α) :
    TerminatingRelativeTo (RewriteStep R) (RewriteStep S) ↔
      TerminatingRelativeTo (RewriteStep (System.reverse R)) (RewriteStep (System.reverse S)) := by
  constructor
  · exact terminatingRelativeTo_comp List.reverse (rewriteStep_reverse R) (rewriteStep_reverse S)
  · refine terminatingRelativeTo_comp List.reverse ?_ ?_
    · intro a b; have := rewriteStep_reverse (System.reverse R) a b
      rwa [System.reverse_reverse] at this
    · intro a b; have := rewriteStep_reverse (System.reverse S) a b
      rwa [System.reverse_reverse] at this

/-- **Termination is reversal-invariant**: an SRS `R` is terminating iff its reversal `Rʳᵉᵛ` is —
`SN(R) ↔ SN(Rʳᵉᵛ)`. This is the ordinary-termination specialisation of **Lemma 2.8**
(`ruleReversal`, the case `S = ∅`): reversal conjugates the rewrite relation
(`rewriteStep_reverse`), so reversing every string in an infinite `→_R`-chain produces an infinite
`→_{Rʳᵉᵛ}`-chain and vice versa (the backward direction using that reversal is an involution,
`System.reverse_reverse`). -/
@[category research solved, AMS 68, ref "Zan05",
  formal_uses rewriteStep_reverse System.reverse_reverse]
theorem terminating_reverse_iff (R : System α) :
    Terminating (RewriteStep (System.reverse R)) ↔ Terminating (RewriteStep R) := by
  have key : ∀ S : System α, Terminating (RewriteStep S) →
      Terminating (RewriteStep (System.reverse S)) := by
    intro S hS
    rintro ⟨f, hf⟩
    exact hS ⟨fun i => (f i).reverse, fun i => (rewriteStep_reverse S _ _).mp (hf i)⟩
  refine ⟨fun h => ?_, key R⟩
  have h2 := key (System.reverse R) h
  rwa [System.reverse_reverse] at h2

/-! ### Top termination (Book–Otto Definition 2.9) -/

/-- A subrelation of a terminating relation is terminating: any infinite `r'`-chain is in
particular an infinite `r`-chain. -/
@[category API, AMS 68, ref "BO93"]
theorem terminating_of_subrelation {r r' : α → α → Prop} (h : ∀ u v, r' u v → r u v)
    (hr : Terminating r) : Terminating r' := by
  rintro ⟨s, hs⟩
  exact hr ⟨s, fun i => h _ _ (hs i)⟩

/-- **Definition 2.9** (top rewrite relation). The **top rewrite relation** `→_{R_top}` induced by
`R` rewrites only at the front — there is no left context: `u →_{R_top} v` iff `u = ℓ ++ s` and
`v = r ++ s` for some suffix `s` and some rule `ℓ → r` of `R`. -/
@[category API, AMS 68, ref "BO93"]
def TopRewriteStep (R : System α) (u v : List α) : Prop :=
  ∃ s ℓ r, R ℓ r ∧ u = ℓ ++ s ∧ v = r ++ s

/-- **Definition 2.9** (top termination). `R` is **top terminating** when its top rewrite relation
`→_{R_top}` is terminating. -/
@[category API, AMS 68, ref "BO93"]
def TopTerminating (R : System α) : Prop := Terminating (TopRewriteStep R)

/-- Every rule `ℓ → r` is a top rewrite `ℓ →_{R_top} r` (empty suffix). -/
@[category API, AMS 68, ref "BO93"]
theorem TopRewriteStep.of_rule {R : System α} {ℓ r : List α} (h : R ℓ r) :
    TopRewriteStep R ℓ r := by
  refine ⟨[], ℓ, r, h, ?_, ?_⟩ <;> simp

/-- The top rewrite relation is closed under appending a **suffix**: if `u →_{R_top} v` then
`u ++ t →_{R_top} v ++ t`. (Unlike `→_R` it is *not* closed under a left context — that is exactly
what "top" forbids.) -/
@[category API, AMS 68, ref "BO93"]
theorem TopRewriteStep.append_right {R : System α} {u v : List α}
    (h : TopRewriteStep R u v) (t : List α) :
    TopRewriteStep R (u ++ t) (v ++ t) := by
  obtain ⟨s, ℓ, r, hrule, hu, hv⟩ := h
  refine ⟨s ++ t, ℓ, r, hrule, ?_, ?_⟩
  · rw [hu]; simp [List.append_assoc]
  · rw [hv]; simp [List.append_assoc]

/-- A top rewrite is in particular a rewrite: `→_{R_top} ⊆ →_R` (take the empty left context). -/
@[category API, AMS 68, ref "BO93"]
theorem TopRewriteStep.toRewriteStep {R : System α} {u v : List α}
    (h : TopRewriteStep R u v) : RewriteStep R u v := by
  obtain ⟨s, ℓ, r, hrule, hu, hv⟩ := h
  exact ⟨[], s, ℓ, r, hrule, by rw [hu]; simp, by rw [hv]; simp⟩

/-- **Termination implies top termination**: since `→_{R_top} ⊆ →_R`
(`TopRewriteStep.toRewriteStep`), a terminating `R` is in particular top terminating. (The converse
fails in general — top termination is strictly weaker, as it forbids rewriting under a left
context.) -/
@[category textbook, AMS 68, ref "BO93",
  formal_uses terminating_of_subrelation TopRewriteStep.toRewriteStep]
theorem topTerminating_of_terminating {R : System α} (h : Terminating (RewriteStep R)) :
    TopTerminating R :=
  terminating_of_subrelation (fun _ _ hstep => hstep.toRewriteStep) h

end StringRewriting
