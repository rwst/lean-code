/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Basic
import Mathlib.Order.WellFounded
import Mathlib.Logic.Relation
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Reduction orders and the interpretation method (Book–Otto §2)

The standard idea for proving a string rewriting system `R` terminating: exhibit a **well-founded
order** `>` on the strings `List α` (Book and Otto's `Σ*`) that *strictly decreases* along every
rewrite, i.e. `s →_R t → s > t`. Then an infinite rewrite sequence `s₀ →_R s₁ →_R ⋯` would give an
infinite descending chain `s₀ > s₁ > ⋯`, contradicting well-foundedness; so `R` is terminating.

* `StringRewriting.terminating_of_wellFounded` — the abstract principle, for any relation: if `w`
  is well-founded and every `r`-step descends in `w` (`r s t → w t s`), then `r` is terminating.
* `StringRewriting.terminating_of_wellFoundedOrder` — the SRS form (the "main idea"): a
  well-founded `lt` on `List α` with `s →_R t → lt t s` (read `lt t s` as `s > t`) makes `R`
  terminating.

A **reduction order** (Definition 2.10) packages exactly the order that makes this work for a whole
system at once: a well-founded, transitive order `>` on `Σ*` that is **compatible with contexts**,
`s > t → psq > ptq`. Compatibility is what lets the finite check `ℓ > r` on the *rules* propagate to
every rewrite `sℓt →_R srt` (then `sℓt > srt`), yielding the *characterization* of termination:

* `StringRewriting.IsReductionOrder` — **Definition 2.10**: `gt` (read `gt s t` as `s > t`) is
  well-founded (`Terminating gt`), transitive, and context-compatible. Well-foundedness already
  forbids `s > s`, so it is a genuine strict order (`IsReductionOrder.irrefl`).
* `StringRewriting.terminating_iff_exists_reductionOrder` — **Theorem 2.11**
  ([BN98, Theorem 5.2.3]; [BO93, Theorem 2.2.4]): `R` is terminating **iff** there is a reduction
  order `>` with `ℓ > r` for every rule `ℓ → r ∈ R`. The (⇐) direction is the method above; the (⇒)
  direction exhibits the transitive closure `→⁺_R` of the rewrite relation as the witness.

The **interpretation method** is the systematic source of reduction orders. Interpret each symbol
as a function `[σ] : A → A` on a carrier `A` carrying a well-founded order `>`, extend to strings by
composition `[σ₁ ⋯ σₙ] = [σ₁] ∘ ⋯ ∘ [σₙ]`, and compare strings via their interpretations:

* `StringRewriting.strInterp` / `StringRewriting.interpOrder` — the string interpretation `[s]` and
  the induced order `s >_𝔄 t :↔ ∀ x, [s](x) > [t](x)` (equation (1)).
* `StringRewriting.interpOrder_isReductionOrder` — **Theorem 2.12** ([BN98, Theorem 5.3.3]): if `>`
  is well-founded on a nonempty carrier `A` and every `[σ]` is monotone for `>`, then `>_𝔄` is a
  reduction order. (The additive interpretation `[σ] x = x + 1` over `A = ℕ` recovers the
  string-length measure used for `R₁`.)
* `StringRewriting.terminating_R₃_interpretation` — **Example 2.13**: `R₃ = {ab → ba}` is
  terminating, reproved by the interpretation `[a] x = x²`, `[b] x = x + 1` over `ℕ⁺` (for which the
  rule decreases, `(x+1)² > x² + 1`).

The **extended/weakly monotone algebra** framework (Definition 2.14) generalises the single-order
interpretation to a *pair* of relations — a well-founded strict order `>` and a compatible
quasi-order `≳` with `> · ≳ ⊆ >` — the basis for proving relative and top termination by
interpretations:

* `StringRewriting.WeaklyMonotoneAlgebra` / `StringRewriting.ExtendedMonotoneAlgebra` —
  **Definition 2.14**: a per-symbol interpretation `[σ] : A → A` with `>` well-founded and
  `> · ≳ ⊆ >`, where every `[σ]` is `≳`-monotone (*weakly* monotone) and, in the extended case,
  also `>`-monotone.
* `StringRewriting.theorem_2_15_relative` / `StringRewriting.theorem_2_15_top` — **Theorem 2.15**
  ([EWZ08, Theorem 2]): `SN(R / S)` (resp. `SN(R_top / S)`) holds iff such an extended (resp.
  weakly) monotone algebra over a *nonempty* carrier exists in which every `R`-rule strictly
  decreases (`[ℓ] > [r]`) and every `S`-rule weakly decreases (`[ℓ] ≳ [r]`). The soundness (`←`)
  direction is **proven** (`terminatingRelativeTo_of_extendedMonotone` /
  `topTerminatingRelativeTo_of_weaklyMonotone`, on the relative-well-foundedness engine
  `terminatingRelativeTo_of_wf_compat`); only the completeness (`→`) direction — constructing the
  algebra — is a cited axiom.

Only well-foundedness and compatibility are used in the soundness direction — there the order need
not be transitive or irreflexive. The `ℕ`-valued measure principle
`StringRewriting.terminating_of_measure` (in `SRS.Basic`) is itself the special case where the order
is the pullback of `<` on `ℕ` along a measure.

## References
* [BN98] Baader, Franz and Nipkow, Tobias. *Term Rewriting and All That.* Cambridge University
  Press, 1998.
* [BO93] Book, Ronald V. and Otto, Friedrich. *String-Rewriting Systems.* Texts and Monographs
  in Computer Science. Springer-Verlag, New York, 1993.
* [EWZ08] Endrullis, Jörg, Waldmann, Johannes, and Zantema, Hans. "Matrix interpretations for
  proving termination of term rewriting." *Journal of Automated Reasoning* 40.2–3 (2008), 195–220.
-/

namespace StringRewriting

variable {α : Type*}

/-- The abstract **reduction-order principle**. If `w` is a well-founded relation and every
`r`-step *descends* in `w` (`r s t → w t s`), then `r` is terminating: an infinite `r`-chain
`s₀ → s₁ → ⋯` would give an infinite `w`-descending chain `w s₁ s₀`, `w s₂ s₁`, …, which a
well-founded relation forbids. -/
@[category API, AMS 68, ref "BO93", group "wellfounded_order"]
theorem terminating_of_wellFounded {r w : α → α → Prop} (hwf : WellFounded w)
    (h : ∀ s t, r s t → w t s) : Terminating r := by
  rintro ⟨f, hf⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp hwf).elim ⟨f, fun i => h _ _ (hf i)⟩

/-- **The interpretation method** — the main idea for proving an SRS terminating (Book–Otto). If
`lt` is a well-founded order on the strings `List α` along which every rewrite strictly decreases,
`s →_R t → lt t s` (i.e. `s > t`), then `R` is terminating. Read `lt t s` as `s > t`; only
well-foundedness of `lt` and this compatibility are used (the order need not even be transitive). -/
@[category textbook, AMS 68, ref "BO93", group "wellfounded_order",
  formal_uses terminating_of_wellFounded]
theorem terminating_of_wellFoundedOrder {R : System α} (lt : List α → List α → Prop)
    (hwf : WellFounded lt) (hcompat : ∀ s t, RewriteStep R s t → lt t s) :
    Terminating (RewriteStep R) :=
  terminating_of_wellFounded hwf hcompat

/-! ### Reduction orders (Definition 2.10, Theorem 2.11) -/

/-- **Definition 2.10** (reduction order). A relation `gt` on the strings `List α` — read `gt s t`
as `s > t` — is a **reduction order** if it is

* *well-founded*: no infinite descending chain `s₀ > s₁ > ⋯` (stated as `Terminating gt`);
* *transitive*: `s > t → t > u → s > u`; and
* *compatible with contexts*: `s > t → psq > ptq` for all strings `p, q`.

Well-foundedness already forbids `s > s`, so a reduction order is a genuine strict order
(`IsReductionOrder.irrefl`). Context-compatibility is the decisive extra property: it propagates a
check on the rules to every rewrite, and underlies **Theorem 2.11**
(`terminating_iff_exists_reductionOrder`). -/
@[category API, AMS 68, ref "BN98", ref "BO93", group "reduction_order"]
structure IsReductionOrder (gt : List α → List α → Prop) : Prop where
  /-- Well-foundedness of `>`: there is no infinite descending chain `s₀ > s₁ > ⋯`. -/
  wf : Terminating gt
  /-- `>` is transitive: `s > t` and `t > u` give `s > u`. -/
  trans : ∀ {s t u : List α}, gt s t → gt t u → gt s u
  /-- `>` is compatible with contexts: `s > t → psq > ptq` for all strings `p, q`. -/
  compat : ∀ (p q : List α) {s t : List α}, gt s t → gt (p ++ s ++ q) (p ++ t ++ q)

/-- A reduction order is **irreflexive** — `¬ s > s` — and hence a genuine strict order: `s > s`
would give the constant infinite descending chain `s > s > ⋯`, contradicting well-foundedness. -/
@[category API, AMS 68, ref "BO93", group "reduction_order"]
theorem IsReductionOrder.irrefl {gt : List α → List α → Prop}
    (h : IsReductionOrder gt) (s : List α) : ¬ gt s s := fun hs =>
  h.wf ⟨fun _ => s, fun _ => hs⟩

/-- **Theorem 2.11** ([BN98, Theorem 5.2.3]; [BO93, Theorem 2.2.4]). A string rewriting system `R`
is terminating **if and only if** there exists a reduction order `>` on `Σ*` (`List α`) such that
`ℓ > r` for every rule `ℓ → r ∈ R`.

* (⇐) If such a `>` exists then every rewrite `sℓt →_R srt` satisfies `sℓt > srt`, by
  context-compatibility applied to `ℓ > r`; so `>` strictly decreases along `→_R`, and
  well-foundedness gives termination (this is `terminating_of_wellFoundedOrder`).
* (⇒) Conversely, if `R` is terminating then the transitive closure `→⁺_R` of the rewrite relation
  is itself a reduction order: transitive by construction, context-compatible because `→_R` is
  (`RewriteStep.append_context`), well-founded because `R` is terminating, and with `ℓ →⁺_R r` for
  every rule (`RewriteStep.of_rule`). -/
@[category textbook, AMS 68, ref "BN98", ref "BO93", group "reduction_order",
  formal_uses IsReductionOrder terminating_of_wellFoundedOrder terminating_iff_wellFounded
    RewriteStep.append_context RewriteStep.of_rule]
theorem terminating_iff_exists_reductionOrder {R : System α} :
    Terminating (RewriteStep R) ↔
      ∃ gt : List α → List α → Prop, IsReductionOrder gt ∧ ∀ ℓ r, R ℓ r → gt ℓ r := by
  constructor
  · intro h
    refine ⟨Relation.TransGen (RewriteStep R), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [terminating_iff_wellFounded]
      have key : (fun a b => Relation.TransGen (RewriteStep R) b a)
          = Relation.TransGen (Function.swap (RewriteStep R)) := by
        funext a b; exact propext Relation.transGen_swap.symm
      rw [key]
      exact (terminating_iff_wellFounded.mp h).transGen
    · intro s t u; exact Relation.TransGen.trans
    · intro p q s t hst
      exact Relation.TransGen.lift (fun w => p ++ w ++ q)
        (fun _ _ hab => RewriteStep.append_context hab p q) hst
    · intro ℓ r hr
      exact Relation.TransGen.single (RewriteStep.of_rule hr)
  · rintro ⟨gt, hgt, hrules⟩
    refine terminating_of_wellFoundedOrder (fun t s => gt s t)
      (terminating_iff_wellFounded.mp hgt.wf) ?_
    rintro u v ⟨p, q, ℓ, r, hrule, rfl, rfl⟩
    exact hgt.compat p q (hrules ℓ r hrule)

/-! ### The interpretation method (monotone algebras, Theorem 2.12) -/

variable {A : Type*}

/-- The **interpretation of a string** in a monotone algebra (the *interpretation method*). Given an
interpretation `den σ = [σ] : A → A` of each symbol as a function on a carrier `A`, a string
`s = σ₁ ⋯ σₙ` is interpreted as the composite `[s] = [σ₁] ∘ ⋯ ∘ [σₙ]` — so the **last** symbol acts
first — with the empty string interpreted as `id`. -/
@[category API, AMS 68, ref "BN98", group "interpretation_method"]
def strInterp (den : α → A → A) : List α → A → A
  | [] => id
  | σ :: s => den σ ∘ strInterp den s

/-- The interpretation turns concatenation into composition: `[s ++ t] = [s] ∘ [t]`. This
homomorphism property is what makes the induced order compatible with contexts. -/
@[category API, AMS 68, ref "BN98", group "interpretation_method"]
theorem strInterp_append (den : α → A → A) (s t : List α) :
    strInterp den (s ++ t) = strInterp den s ∘ strInterp den t := by
  induction s with
  | nil => rfl
  | cons σ s ih => simp only [List.cons_append, strInterp, ih, Function.comp_assoc]

/-- If every symbol interpretation `[σ]` is strictly monotone for `>` (`a > b → [σ] a > [σ] b`),
then so is the interpretation `[s]` of any string: a strict inequality is preserved through the
whole composite. -/
@[category API, AMS 68, ref "BN98", group "interpretation_method"]
theorem strInterp_strictMono (den : α → A → A) {gtA : A → A → Prop}
    (hmono : ∀ σ a b, gtA a b → gtA (den σ a) (den σ b)) (s : List α) {a b : A}
    (hab : gtA a b) : gtA (strInterp den s a) (strInterp den s b) := by
  induction s with
  | nil => exact hab
  | cons σ s ih => exact hmono σ _ _ ih

/-- The order `>_𝔄` on strings induced by an interpretation `𝔄 = (A, [·], >)` (equation (1)):
`interpOrder den gtA s t` (read `s >_𝔄 t`) holds iff `[s](x) > [t](x)` for **every** `x ∈ A`, where
`gtA a b` is the well-founded order `a > b` on the carrier `A`. -/
@[category API, AMS 68, ref "BN98", group "interpretation_method"]
def interpOrder (den : α → A → A) (gtA : A → A → Prop) (s t : List α) : Prop :=
  ∀ x : A, gtA (strInterp den s x) (strInterp den t x)

/-- **Theorem 2.12** ([BN98, Theorem 5.3.3]) — the **interpretation method**. Let `>` (`gtA`) be a
well-founded, transitive order on a *nonempty* carrier `A`, and interpret each symbol as a function
`[σ] : A → A` that is monotone for `>` (`a > b → [σ] a > [σ] b`). Then the induced order `>_𝔄` of
equation (1) (`interpOrder`) is a **reduction order** on `Σ*`.

* *Well-foundedness*: an infinite `>_𝔄`-descending chain `s₀ >_𝔄 s₁ >_𝔄 ⋯`, evaluated at any fixed
  `x ∈ A` (the carrier is nonempty), yields an infinite `>`-descending chain `[s₀](x) > [s₁](x) > ⋯`
  in `A`, impossible. (Nonemptiness is essential: over an empty `A`, `>_𝔄` is the total relation and
  is not well-founded.)
* *Transitivity* is pointwise, from transitivity of `>`.
* *Context-compatibility* `s >_𝔄 t → psq >_𝔄 ptq`: since `[psq] = [p] ∘ [s] ∘ [q]`
  (`strInterp_append`) and `[p]` is monotone (`strInterp_strictMono`), applying `[p]` after `[q]`
  preserves the strict inequality `[s](y) > [t](y)` at `y = [q](x)`. -/
@[category textbook, AMS 68, ref "BN98", group "interpretation_method",
  formal_uses IsReductionOrder interpOrder strInterp_append strInterp_strictMono]
theorem interpOrder_isReductionOrder [Nonempty A] (den : α → A → A) {gtA : A → A → Prop}
    (hwf : Terminating gtA) (htrans : ∀ a b c, gtA a b → gtA b c → gtA a c)
    (hmono : ∀ σ a b, gtA a b → gtA (den σ a) (den σ b)) :
    IsReductionOrder (interpOrder den gtA) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨f, hf⟩
    obtain ⟨x₀⟩ := ‹Nonempty A›
    exact hwf ⟨fun n => strInterp den (f n) x₀, fun n => hf n x₀⟩
  · intro s t u hst htu x
    exact htrans _ _ _ (hst x) (htu x)
  · intro p q s t hst x
    have hp := strInterp_strictMono den hmono p (hst (strInterp den q x))
    simpa [interpOrder, strInterp_append] using hp

/-! ### Example 2.13 — `R₃ = {ab → ba}` terminates by a monotone interpretation -/

/-- The interpretation `𝔑 = (ℕ⁺, {[a], [b]}, >)` of **Example 2.13**: over the positive integers
`ℕ⁺`, with their usual (well-founded) order, interpret `[a] x = x²` and `[b] x = x + 1`. Both are
monotone for `>`. -/
@[category API, AMS 68, ref "BN98", group "example_2_13"]
def den₃ : Sym → ℕ+ → ℕ+
  | Sym.a => fun x => x ^ 2
  | Sym.b => fun x => x + 1

/-- **Example 2.13**. A second proof that `R₃ = {ab → ba}` is terminating (cf. `terminating_R₃`,
which uses the inversion count) — now by the **interpretation method**. Over `ℕ⁺` with `[a] x = x²`,
`[b] x = x + 1` (`den₃`), both monotone for the well-founded order `>`, Theorem 2.12
(`interpOrder_isReductionOrder`) makes `>_𝔑` a reduction order. The single rule strictly decreases:
`[ab] x = (x + 1)² > x² + 1 = [ba] x` for every `x ∈ ℕ⁺` (positivity is essential — equality holds
at `x = 0`), so `ab >_𝔑 ba`. Theorem 2.11 (`terminating_iff_exists_reductionOrder`) then yields
termination. -/
@[category textbook, AMS 68, ref "BN98", group "example_2_13",
  formal_uses terminating_iff_exists_reductionOrder interpOrder_isReductionOrder interpOrder den₃]
theorem terminating_R₃_interpretation : Terminating (RewriteStep R₃) := by
  rw [terminating_iff_exists_reductionOrder]
  refine ⟨interpOrder den₃ (· > ·), interpOrder_isReductionOrder den₃ ?_ ?_ ?_, ?_⟩
  · exact terminating_of_measure (fun n => (n : ℕ)) (fun u v h => by exact_mod_cast h)
  · exact fun _ _ _ => gt_trans
  · intro σ a b h
    have hba : (b : ℕ) < (a : ℕ) := by exact_mod_cast h
    cases σ with
    | a =>
      show b ^ 2 < a ^ 2
      rw [← PNat.coe_lt_coe]; push_cast; gcongr
    | b =>
      show b + 1 < a + 1
      rw [← PNat.coe_lt_coe]; push_cast; omega
  · rintro ℓ r ⟨rfl, rfl⟩ x
    show strInterp den₃ [Sym.a, Sym.b] x > strInterp den₃ [Sym.b, Sym.a] x
    simp only [strInterp, den₃, Function.comp_apply, id_eq]
    show x ^ 2 + 1 < (x + 1) ^ 2
    rw [← PNat.coe_lt_coe]; push_cast
    nlinarith [x.pos]

/-! ### Extended and weakly monotone algebras (Definition 2.14) -/

/-- **Definition 2.14** (weakly monotone Σ-algebra). A monotone-algebra interpretation over a
carrier `A`: an interpretation `den σ = [σ] : A → A` for each symbol, together with two order
relations on `A` — a strict order `gt` (`>`) and a quasi-order `ge` (`≳`) — such that

* `gt_wf`: `>` is **well-founded** (`Terminating gt` — no infinite `>`-descending chain);
* `compat`: `>` absorbs `≳` on the right, `> · ≳ ⊆ >`, i.e. `a > b → b ≳ c → a > c`;
* `mono_ge`: every `[σ]` is **monotone for `≳`** (`a ≳ b → [σ] a ≳ [σ] b`).

This makes the structure `(A, [·]_Σ, >, ≳)` a *weakly monotone Σ-algebra*; requiring in addition
that every `[σ]` be monotone for `>` yields an `ExtendedMonotoneAlgebra`. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra"]
structure WeaklyMonotoneAlgebra (α A : Type*) where
  /-- The interpretation `[σ] : A → A` of each symbol `σ`. -/
  den : α → A → A
  /-- The well-founded strict order `>` on the carrier. -/
  gt : A → A → Prop
  /-- The compatible quasi-order `≳` on the carrier. -/
  ge : A → A → Prop
  /-- `>` is well-founded: no infinite descending chain `a₀ > a₁ > ⋯`. -/
  gt_wf : Terminating gt
  /-- Compatibility `> · ≳ ⊆ >`: a strict step followed by a weak step is strict. -/
  compat : ∀ a b c, gt a b → ge b c → gt a c
  /-- Every interpretation is monotone for `≳`: `a ≳ b → [σ] a ≳ [σ] b`. -/
  mono_ge : ∀ σ a b, ge a b → ge (den σ a) (den σ b)

/-- **Definition 2.14** (extended monotone Σ-algebra). A `WeaklyMonotoneAlgebra` in which, in
addition, every interpretation `[σ]` is **monotone for the strict order `>`**
(`a > b → [σ] a > [σ] b`). Strict monotonicity is what lets `>` propagate through a rewrite applied
*anywhere* inside a string (the requirement for ordinary termination), whereas weak monotonicity
alone underlies the relative and top variants. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra"]
structure ExtendedMonotoneAlgebra (α A : Type*) extends WeaklyMonotoneAlgebra α A where
  /-- Every interpretation is monotone for `>`: `a > b → [σ] a > [σ] b`. -/
  mono_gt : ∀ σ a b, gt a b → gt (den σ a) (den σ b)

/-! ### Theorem 2.15 — monotone algebras characterise relative and top termination

The soundness (`←`) direction is proven; the completeness (`→`) direction — constructing an algebra
from termination — is the substantive content of [EWZ08] and is recorded as a cited axiom. The
proven half rests on an abstract *relative well-foundedness* engine and the lifting of rewrite steps
to the induced string orders. -/

open Filter

/-- **Relative well-foundedness engine.** If `gt` is well-founded (`Terminating gt`) and absorbs
`ge` on the right — `gt · ge ⊆ gt`, i.e. `a > b → b ≳ c → a > c` (`hcompat`) — then `gt` terminates
*relative to* `ge`. Along a hypothetical bad chain the `gt`-steps occur infinitely often;
enumerating the *consecutive* `gt`-indices and absorbing each intervening `ge`-run via `hcompat`
yields an infinite `gt`-descending chain, contradicting well-foundedness. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra"]
theorem terminatingRelativeTo_of_wf_compat {β : Type*} {gt ge : β → β → Prop}
    (hwf : Terminating gt) (hcompat : ∀ a b c, gt a b → ge b c → gt a c) :
    TerminatingRelativeTo gt ge := by
  rintro ⟨s, hfreq, hrest⟩
  classical
  have hf : ∀ N, ∃ n, N ≤ n ∧ gt (s n) (s (n + 1)) := fun N => by
    obtain ⟨n, hn, hgt⟩ := (frequently_atTop.mp hfreq) N; exact ⟨n, hn, hgt⟩
  let i : ℕ → ℕ := fun k => Nat.rec (Nat.find (hf 0)) (fun _ ik => Nat.find (hf (ik + 1))) k
  have hisucc : ∀ k, i (k + 1) = Nat.find (hf (i k + 1)) := fun _ => rfl
  have hi_spec : ∀ k, gt (s (i k)) (s (i k + 1)) := by
    intro k; cases k with
    | zero => exact (Nat.find_spec (hf 0)).2
    | succ k => rw [hisucc]; exact (Nat.find_spec (hf (i k + 1))).2
  have hi_lb : ∀ k, i k + 1 ≤ i (k + 1) := by
    intro k; rw [hisucc]; exact (Nat.find_spec (hf (i k + 1))).1
  have hi_min : ∀ k m, i k < m → m < i (k + 1) → ¬ gt (s m) (s (m + 1)) := by
    intro k m hlt hub hgt; rw [hisucc] at hub; exact Nat.find_min (hf (i k + 1)) hub ⟨hlt, hgt⟩
  have habsorb : ∀ k, gt (s (i k)) (s (i (k + 1))) := by
    intro k
    have key : ∀ e, i k + 1 + e ≤ i (k + 1) → gt (s (i k)) (s (i k + 1 + e)) := by
      intro e; induction e with
      | zero => intro _; exact hi_spec k
      | succ e ih =>
        intro hbound
        have hgt' := hcompat _ _ _ (ih (by omega))
          (hrest _ (hi_min k (i k + 1 + e) (by omega) (by omega)))
        have heq : i k + 1 + (e + 1) = i k + 1 + e + 1 := by omega
        rw [heq]; exact hgt'
    have hk := key (i (k + 1) - (i k + 1)) (by have := hi_lb k; omega)
    have heq : i k + 1 + (i (k + 1) - (i k + 1)) = i (k + 1) := by have := hi_lb k; omega
    rwa [heq] at hk
  exact hwf ⟨fun k => s (i k), habsorb⟩

/-- If the carrier `A` is nonempty and the base relation `rel` is well-founded, then the induced
string order `interpOrder den rel` is well-founded — a bad string chain, evaluated at any fixed
`x ∈ A`, would descend in `rel`. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra"]
theorem terminating_interpOrder [Nonempty A] (den : α → A → A) {rel : A → A → Prop}
    (hwf : Terminating rel) : Terminating (interpOrder den rel) := by
  rintro ⟨f, hf⟩
  obtain ⟨x₀⟩ := ‹Nonempty A›
  exact hwf ⟨fun n => strInterp den (f n) x₀, fun n => hf n x₀⟩

/-- Relative termination is **antitone in both relations**: from `r₁ ⊆ r₁'` and `r₂ ⊆ r₂'`,
`SN(r₁' / r₂')` gives `SN(r₁ / r₂)` (map a bad `r₁/r₂` chain forward to a bad `r₁'/r₂'` chain). -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra"]
theorem terminatingRelativeTo_mono {β : Type*} {r₁ r₂ r₁' r₂' : β → β → Prop}
    (h₁ : ∀ a b, r₁ a b → r₁' a b) (h₂ : ∀ a b, r₂ a b → r₂' a b)
    (H : TerminatingRelativeTo r₁' r₂') : TerminatingRelativeTo r₁ r₂ := by
  rintro ⟨s, hfreq, hrest⟩
  exact H ⟨s, hfreq.mono fun i hi => h₁ _ _ hi,
    fun i hi => h₂ _ _ (hrest i fun h => hi (h₁ _ _ h))⟩

/-- A rewrite step lifts to the induced string order: if every interpretation is `rel`-monotone and
every rule satisfies `[ℓ](x) rel [r](x)`, then `s →_R t` gives `interpOrder den rel s t` — the rule
decrease propagates through the surrounding context by `strInterp_strictMono`. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses strInterp_strictMono strInterp_append interpOrder]
theorem rewriteStep_interpOrder {R : System α} (den : α → A → A) {rel : A → A → Prop}
    (hmono : ∀ σ a b, rel a b → rel (den σ a) (den σ b))
    (hrule : ∀ ℓ r, R ℓ r → ∀ x, rel (strInterp den ℓ x) (strInterp den r x))
    {s t : List α} (h : RewriteStep R s t) : interpOrder den rel s t := by
  obtain ⟨p, q, ℓ, r, hr, rfl, rfl⟩ := h
  intro x
  simpa [strInterp_append] using
    strInterp_strictMono den hmono p (hrule ℓ r hr (strInterp den q x))

/-- A *top* rewrite step lifts to the induced string order with **no monotonicity hypothesis**:
since `ℓ s →_{R_top} r s` has no left context, the rule decrease `[ℓ](x) rel [r](x)` transfers
directly to `[ℓs] rel [rs]`. This is why weak monotonicity suffices for top termination. -/
@[category API, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses strInterp_append interpOrder]
theorem topRewriteStep_interpOrder {R : System α} (den : α → A → A) {rel : A → A → Prop}
    (hrule : ∀ ℓ r, R ℓ r → ∀ x, rel (strInterp den ℓ x) (strInterp den r x))
    {s t : List α} (h : TopRewriteStep R s t) : interpOrder den rel s t := by
  obtain ⟨w, ℓ, r, hr, rfl, rfl⟩ := h
  intro x
  simpa [strInterp_append] using hrule ℓ r hr (strInterp den w x)

/-- **Theorem 2.15, soundness (`←`), relative form** ([EWZ08, Theorem 2]). An *extended* monotone
algebra `𝔄` over a nonempty carrier in which every `R`-rule strictly decreases (`[ℓ] > [r]`) and
every `S`-rule weakly decreases (`[ℓ] ≳ [r]`) proves relative termination `SN(R / S)`. The `R`- and
`S`-steps lift to `𝔄`'s string orders (`rewriteStep_interpOrder`, via extended / weak
monotonicity), which are relatively terminating by `terminatingRelativeTo_of_wf_compat`. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses terminatingRelativeTo_mono rewriteStep_interpOrder terminatingRelativeTo_of_wf_compat
    terminating_interpOrder]
theorem terminatingRelativeTo_of_extendedMonotone [Nonempty A] {R S : System α}
    (𝔄 : ExtendedMonotoneAlgebra α A)
    (hR : ∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x))
    (hS : ∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) :
    TerminatingRelativeTo (RewriteStep R) (RewriteStep S) :=
  terminatingRelativeTo_mono
    (fun _ _ h => rewriteStep_interpOrder 𝔄.den 𝔄.mono_gt hR h)
    (fun _ _ h => rewriteStep_interpOrder 𝔄.den 𝔄.mono_ge hS h)
    (terminatingRelativeTo_of_wf_compat (terminating_interpOrder 𝔄.den 𝔄.gt_wf)
      (fun _ _ _ hab hbc x => 𝔄.compat _ _ _ (hab x) (hbc x)))

/-- **Theorem 2.15, soundness (`←`), top form** ([EWZ08, Theorem 2]). A *weakly* monotone algebra
with the same rule conditions proves `SN(R_top / S)`. Only weak monotonicity is needed: the strict
`R`-steps act at the top (no left context, `topRewriteStep_interpOrder`), while the weak `S`-steps
use `≳`-monotonicity. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses terminatingRelativeTo_mono topRewriteStep_interpOrder rewriteStep_interpOrder
    terminatingRelativeTo_of_wf_compat terminating_interpOrder]
theorem topTerminatingRelativeTo_of_weaklyMonotone [Nonempty A] {R S : System α}
    (𝔄 : WeaklyMonotoneAlgebra α A)
    (hR : ∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x))
    (hS : ∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) :
    TerminatingRelativeTo (TopRewriteStep R) (RewriteStep S) :=
  terminatingRelativeTo_mono
    (fun _ _ h => topRewriteStep_interpOrder 𝔄.den hR h)
    (fun _ _ h => rewriteStep_interpOrder 𝔄.den 𝔄.mono_ge hS h)
    (terminatingRelativeTo_of_wf_compat (terminating_interpOrder 𝔄.den 𝔄.gt_wf)
      (fun _ _ _ hab hbc x => 𝔄.compat _ _ _ (hab x) (hbc x)))

/-- **Theorem 2.15, completeness (`→`), relative form** ([EWZ08, Theorem 2]). Conversely, relative
termination `SN(R / S)` is *witnessed* by an extended monotone algebra over a nonempty carrier.
Recorded as a **cited axiom** (status *cited*): constructing the algebra is the substantive content
of [EWZ08] and is not formalized here. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra"]
axiom exists_extendedMonotone_of_terminatingRelativeTo.{u} {α : Type u} (R S : System α) :
    TerminatingRelativeTo (RewriteStep R) (RewriteStep S) →
      ∃ (A : Type u) (𝔄 : ExtendedMonotoneAlgebra α A), Nonempty A ∧
        (∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) ∧
        (∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x))

/-- **Theorem 2.15, completeness (`→`), top form** ([EWZ08, Theorem 2]). `SN(R_top / S)` is
witnessed by a weakly monotone algebra over a nonempty carrier. Recorded as a **cited axiom**
(status *cited*); cf. `exists_extendedMonotone_of_terminatingRelativeTo`. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra"]
axiom exists_weaklyMonotone_of_topTerminatingRelativeTo.{u} {α : Type u} (R S : System α) :
    TerminatingRelativeTo (TopRewriteStep R) (RewriteStep S) →
      ∃ (A : Type u) (𝔄 : WeaklyMonotoneAlgebra α A), Nonempty A ∧
        (∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) ∧
        (∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x))

/-- **Theorem 2.15** ([EWZ08, Theorem 2]), relative-termination form. `SN(R / S)` holds **iff**
there is an *extended* monotone Σ-algebra over a nonempty carrier in which every `R`-rule strictly
decreases (`[ℓ] > [r]`) and every `S`-rule weakly decreases (`[ℓ] ≳ [r]`). The `←` (soundness)
direction is fully proven (`terminatingRelativeTo_of_extendedMonotone`); the `→` (completeness)
direction is the cited axiom `exists_extendedMonotone_of_terminatingRelativeTo`. Nonemptiness of the
carrier is part of the statement — over an empty carrier the rule conditions hold vacuously while
termination may fail, so the equivalence would otherwise be false. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses terminatingRelativeTo_of_extendedMonotone
    exists_extendedMonotone_of_terminatingRelativeTo]
theorem theorem_2_15_relative.{u} {α : Type u} (R S : System α) :
    TerminatingRelativeTo (RewriteStep R) (RewriteStep S) ↔
      ∃ (A : Type u) (𝔄 : ExtendedMonotoneAlgebra α A), Nonempty A ∧
        (∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) ∧
        (∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) := by
  refine ⟨exists_extendedMonotone_of_terminatingRelativeTo R S, ?_⟩
  rintro ⟨A, 𝔄, hne, hR, hS⟩
  haveI := hne
  exact terminatingRelativeTo_of_extendedMonotone 𝔄 hR hS

/-- **Theorem 2.15** ([EWZ08, Theorem 2]), top-termination form. `SN(R_top / S)` — relative
termination of the *top* rewrite relation of `R` over the full rewrite relation of `S` — holds
**iff** there is a *weakly* monotone Σ-algebra over a nonempty carrier with the same rule conditions
(`R`-rules strict, `S`-rules weak). The `←` direction is proven
(`topTerminatingRelativeTo_of_weaklyMonotone`); the `→` direction is the cited axiom
`exists_weaklyMonotone_of_topTerminatingRelativeTo`. -/
@[category research solved, AMS 68, ref "EWZ08", group "monotone_algebra",
  formal_uses topTerminatingRelativeTo_of_weaklyMonotone
    exists_weaklyMonotone_of_topTerminatingRelativeTo]
theorem theorem_2_15_top.{u} {α : Type u} (R S : System α) :
    TerminatingRelativeTo (TopRewriteStep R) (RewriteStep S) ↔
      ∃ (A : Type u) (𝔄 : WeaklyMonotoneAlgebra α A), Nonempty A ∧
        (∀ ℓ r, R ℓ r → ∀ x, 𝔄.gt (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) ∧
        (∀ ℓ r, S ℓ r → ∀ x, 𝔄.ge (strInterp 𝔄.den ℓ x) (strInterp 𝔄.den r x)) := by
  refine ⟨exists_weaklyMonotone_of_topTerminatingRelativeTo R S, ?_⟩
  rintro ⟨A, 𝔄, hne, hR, hS⟩
  haveI := hne
  exact topTerminatingRelativeTo_of_weaklyMonotone 𝔄 hR hS

end StringRewriting
