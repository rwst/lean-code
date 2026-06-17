/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.Interpretation
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.GCongr
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Arctic matrix interpretations (KW09, ST14)

Natural matrix interpretations (`SRS.MatrixInterpretation`) adapt to the **max–plus algebra** of
*arctic* numbers — arctic naturals `A_ℕ = ℕ ∪ {−∞}` or arctic integers `A_ℤ = ℤ ∪ {−∞}`
([KW09, ST14]). This enables termination proofs in cases where no other automated method succeeds,
or where only relatively complicated proofs are otherwise known.

The **arctic semiring** `(A, ⊕, ⊗)` has

* `x ⊕ y = max x y` — with `−∞` the identity (`max (−∞) x = x`);
* `x ⊗ y = x + y` — with `−∞` absorbing (`−∞ ⊗ x = −∞`).

This is exactly Mathlib's (min-)tropical semiring of the order dual, `Tropical (WithTop Rᵒᵈ)`. But
on that representation the arctic order comes out *dualized* (arctic `⪰` is the carrier's `≤`), so
here we work with the **order-faithful** synonym `Arctic R := WithBot R` (`−∞ = ⊥`, `⊕ = (· ⊔ ·)`,
`⊗ = (· + ·)` — all Mathlib operations on `WithBot R`), under which the two arctic orders read
directly off Mathlib's order rather than through a dual.

Writing `>` and `≥` for the usual orders on the coefficients, and adopting the conventions `x > −∞`
for every finite `x` and `−∞ ≥ −∞` (both encoded by `−∞ = ⊥` being the bottom), the two arctic
orders are

* `arcticGe` (`⪰`): `x ⪰ y ↔ y ≤ x` — the carrier's order.
* `arcticGt` (`≫`): `x ≫ y ↔ y < x ∨ (x = −∞ ∧ y = −∞)`.

Both extend **elementwise** to arctic vectors (`arcticVecGe` / `arcticVecGt`) and arctic matrices
(`arcticMatGe` / `arcticMatGt`). Because the definition makes `−∞ ≫ −∞` hold (`arcticGt_bot_bot`),
`≫` is **not** well-founded; well-foundedness is recovered by restricting the domain to `ℕ × A^{d−1}`
(the first coordinate a genuine natural number), turning that coordinate into a well-founded
`ℕ`-measure — a step deferred to the termination layer.

Each symbol `σ ∈ Σ` is interpreted by an **arctic affine** map `[σ] : A^d → A^d`, written
`[σ](x) = M_σ ⊗ x ⊕ v_σ` (`arcticAffine`), where `M_σ ⊗ x` is the arctic matrix–vector product
`(M ⊗ x)ᵢ = ⊕ⱼ Mᵢⱼ ⊗ xⱼ = maxⱼ (Mᵢⱼ + xⱼ)` (`arcticMulVec`) — note this is the max–plus product,
*not* Mathlib's ring `Matrix.mulVec`.

**Sufficient conditions for the rule inequalities** ([KW09, Lemma 6.5]). Comparing two arctic affine
interpretations *pointwise over all of `A^d`* is implied by a finite **elementwise** comparison of
their matrices and constant vectors: `Mℓ ≫ Mᵣ ∧ vℓ ≫ vᵣ ⟹ ∀ x, [ℓ](x) ≫ [r](x)`
(`arcticAffine_arcticVecGt`) and likewise for `⪰` (`arcticAffine_arcticVecGe`). These are
*sufficient* (one-directional `⟹`) — unlike the natural-matrix equation (2), an `⟺`. Since the
elementwise comparisons range over finitely many entries, this makes the rule conditions of
Theorem 2.15 checkable and the search for arctic interpretations SAT-encodable.

**Monotone algebras** (Definition 2.14). Restricting to the domain `ℕ × A^{d−1}` (first coordinate
`≥ 0`; `arcticAffine` keeps it there under the closure condition `(Mσ)₀₀ ≥ 0 ∨ (vσ)₀ ≥ 0`,
`arcticAffine_dom`) makes `≫` **well-founded** — the first coordinate is a strictly decreasing
`ℕ`-measure (`arcticInt_terminating`, `arcticNat_terminating`). So the structure is a *weakly*
monotone Σ-algebra (`arcticWeaklyMonotoneAlgebra`), and with `A = A_ℕ`, every `vσ = −∞` (which forces
`(Mσ)₀₀ ≥ 0`) an *extended* monotone algebra (`arcticExtendedMonotoneAlgebra`). Concrete instances:
`arcticIntWeaklyMonotoneAlgebra`, `arcticNatWeaklyMonotoneAlgebra`,
`arcticNatExtendedMonotoneAlgebra`. (So arctic *integers* and finite-entry vectors are used only for
*top* termination — the weakly monotone case.) Plugging these into Theorem 2.15
(`theorem_2_15_relative` / `theorem_2_15_top`) is the arctic-interpretation termination method.

**Composition** of arctic interpretations is the **max–plus matrix product** `arcticMatMul`
(`B ⊗ A`), which acts associatively on vectors (`arcticMulVec_arcticMatMul`) — so the interpretation
of a rule side is again arctic-linear, with matrix the product of the symbol matrices. Combined with
the constant-`−∞` simplification `arcticAffine_bot`, this lets elementwise comparisons of the
composite matrices (Lemma 6.5) discharge the rule conditions of a concrete proof.

## References
* [KW09] Koprowski, Adam, and Waldmann, Johannes. "Max/plus tree automata for termination of term
  rewriting." *Acta Cybernetica* 19.2 (2009), 357–392.
* [ST14] Sternagel, Christian, and Thiemann, René. "Formalizing monotone algebras for certification
  of termination and complexity proofs." *RTA–TLCA 2014*, LNCS 8560, 441–455.
-/

namespace StringRewriting.ArcticInterpretation

variable {R : Type*} {d : ℕ}

/-- The **arctic carrier** `A = R ∪ {−∞}`, the coefficients of an arctic matrix interpretation. We
use `WithBot R` so that `−∞ = ⊥`, the arctic sum `⊕` is `max`/`⊔`, the arctic product `⊗` is the
`WithBot` addition `+` (with `−∞` absorbing), and the arctic order matches Mathlib's order. The two
instances of interest are `ArcticNat` (`R = ℕ`) and `ArcticInt` (`R = ℤ`). -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
abbrev Arctic (R : Type*) := WithBot R

/-- The arctic quasi-order `⪰`: `x ⪰ y ↔ y ≤ x`, the carrier's order (`−∞ = ⊥` is the least
element, so `x ⪰ −∞` for all `x` and `−∞ ⪰ −∞`). -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticGe [LE R] (x y : Arctic R) : Prop := y ≤ x

/-- The arctic strict order `≫`: `x ≫ y ↔ y < x ∨ (x = −∞ ∧ y = −∞)`. The disjunct `x = y = −∞`
makes `≫` reflexive at the bottom — `−∞ ≫ −∞` (`arcticGt_bot_bot`) — which is exactly why `≫`
fails to be well-founded without a domain restriction. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticGt [LT R] (x y : Arctic R) : Prop := y < x ∨ (x = ⊥ ∧ y = ⊥)

/-- `−∞ ≫ −∞`: the arctic strict order is **reflexive at the bottom**. This is the obstruction to
well-foundedness of `≫` noted in [KW09]; it forces the domain restriction to `ℕ × A^{d−1}`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticGt_bot_bot [LT R] : arcticGt (⊥ : Arctic R) ⊥ := Or.inr ⟨rfl, rfl⟩

/-- The arctic quasi-order `⪰` extended **elementwise** to arctic vectors: `x ⪰ y ↔ xᵢ ⪰ yᵢ` for
every coordinate `i`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticVecGe [LE R] (x y : Fin d → Arctic R) : Prop := ∀ i, arcticGe (x i) (y i)

/-- The arctic strict order `≫` extended **elementwise** to arctic vectors: `x ≫ y ↔ xᵢ ≫ yᵢ` for
every coordinate `i`. (Fully elementwise — unlike the natural-matrix `vecGt`, which is strict only
in the first coordinate; here well-foundedness comes instead from the domain restriction.) -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticVecGt [LT R] (x y : Fin d → Arctic R) : Prop := ∀ i, arcticGt (x i) (y i)

/-- The arctic quasi-order `⪰` extended **elementwise** to arctic matrices: `M ⪰ N ↔ Mᵢⱼ ⪰ Nᵢⱼ`
for all entries. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticMatGe [LE R] (M N : Matrix (Fin d) (Fin d) (Arctic R)) : Prop :=
  ∀ i j, arcticGe (M i j) (N i j)

/-- The arctic strict order `≫` extended **elementwise** to arctic matrices: `M ≫ N ↔ Mᵢⱼ ≫ Nᵢⱼ`
for all entries. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticMatGt [LT R] (M N : Matrix (Fin d) (Fin d) (Arctic R)) : Prop :=
  ∀ i j, arcticGt (M i j) (N i j)

/-- The **arctic matrix–vector product** `M ⊗ x`, with the semiring operations `⊕ = max`, `⊗ = +`:
`(M ⊗ x)ᵢ = ⊕ⱼ (Mᵢⱼ ⊗ xⱼ) = maxⱼ (Mᵢⱼ + xⱼ)`. The `⊕`-sum over coordinates is `Finset.sup`, whose
empty value is the `⊕`-identity `−∞ = ⊥`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticMulVec [LinearOrder R] [Add R] (M : Matrix (Fin d) (Fin d) (Arctic R))
    (x : Fin d → Arctic R) : Fin d → Arctic R :=
  fun i => Finset.univ.sup fun j => M i j + x j

/-- The **arctic affine interpretation** `[σ](x) = M ⊗ x ⊕ v` of a symbol: the arctic matrix–vector
product (`arcticMulVec`) followed by a coordinatewise arctic sum (`max`) with the constant vector
`v`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticMulVec]
def arcticAffine [LinearOrder R] [Add R] (M : Matrix (Fin d) (Fin d) (Arctic R))
    (v x : Fin d → Arctic R) : Fin d → Arctic R :=
  fun i => arcticMulVec M x i ⊔ v i

/-- The **arctic integers** `A_ℤ = ℤ ∪ {−∞}`, the coefficient domain of the *below-zero* arctic
interpretations. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
abbrev ArcticInt := Arctic ℤ

/-- The **arctic naturals** `A_ℕ = ℕ ∪ {−∞}`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
abbrev ArcticNat := Arctic ℕ

/-! ### Sufficient conditions for the rule inequalities ([KW09, Lemma 6.5])

Elementwise comparisons of the arctic matrices and constant vectors of two interpretations are
**sufficient** for the pointwise inequalities of Theorem 2.15. The helper lemmas record that the
arctic operations — multiplication `⊗ = (· + ·)` (`arcticGt_add_right`) and sum `⊕ = (· ⊔ ·)`
(`arcticGt_sup`, `arcticGt_finset_sup`) — are monotone for the strict order `≫`. -/

/-- `≫` is preserved by arctic multiplication on the right, `a ≫ b → a ⊗ c ≫ b ⊗ c`: if `c = −∞`
both products are `−∞` (so `≫` by the bottom clause); otherwise strict monotonicity of `+` on
`WithBot R` (`WithBot.add_lt_add_right`) applies. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticGt_add_right [LinearOrder R] [Add R] [AddRightStrictMono R]
    (c : Arctic R) {a b : Arctic R} (h : arcticGt a b) : arcticGt (a + c) (b + c) := by
  rcases h with hlt | ⟨ha, hb⟩
  · rcases eq_or_ne c ⊥ with rfl | hc
    · exact Or.inr ⟨by simp, by simp⟩
    · exact Or.inl (WithBot.add_lt_add_right hc hlt)
  · subst ha hb; exact Or.inr ⟨by simp, by simp⟩

/-- `≫` is preserved by the binary arctic sum `⊕ = (· ⊔ ·)`: `a ≫ b → c ≫ d → a ⊔ c ≫ b ⊔ d`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticGt_bot_bot]
theorem arcticGt_sup [LinearOrder R] {a b c e : Arctic R}
    (h1 : arcticGt a b) (h2 : arcticGt c e) : arcticGt (a ⊔ c) (b ⊔ e) := by
  rcases h1 with hab | ⟨ha, hb⟩ <;> rcases h2 with hce | ⟨hc, he⟩
  · exact Or.inl (sup_lt_iff.mpr ⟨lt_of_lt_of_le hab le_sup_left, lt_of_lt_of_le hce le_sup_right⟩)
  · subst hc he; simp only [sup_bot_eq]; exact Or.inl hab
  · subst ha hb; simp only [bot_sup_eq]; exact Or.inl hce
  · subst ha hb hc he; simp only [sup_bot_eq]; exact arcticGt_bot_bot

/-- `≫` is preserved by the arctic sum over a finite index set `⊕ⱼ`: if `f j ≫ g j` for every
`j ∈ s` then `s.sup f ≫ s.sup g` (the empty sum gives `−∞ ≫ −∞`). -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticGt_sup arcticGt_bot_bot]
theorem arcticGt_finset_sup [LinearOrder R] {f g : Fin d → Arctic R} (s : Finset (Fin d))
    (h : ∀ j ∈ s, arcticGt (f j) (g j)) : arcticGt (s.sup f) (s.sup g) := by
  induction s using Finset.cons_induction with
  | empty => simpa using arcticGt_bot_bot
  | cons a s ha ih =>
    rw [Finset.sup_cons, Finset.sup_cons]
    exact arcticGt_sup (h a (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- **[KW09, Lemma 6.5], strict form.** Elementwise `≫` on the matrices and vectors is a
**sufficient** condition for the pointwise strict inequality everywhere:
`Mℓ ≫ Mᵣ ∧ vℓ ≫ vᵣ ⟹ [ℓ](x) ≫ [r](x)` for all `x ∈ A^d`. (Each coordinate of the matrix–vector
product `⊕`-sums `≫`-dominating terms, and the final `⊕ v` preserves `≫`.) -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticGt_sup arcticGt_finset_sup arcticGt_add_right]
theorem arcticAffine_arcticVecGt [LinearOrder R] [Add R] [AddRightStrictMono R]
    (Mℓ Mᵣ : Matrix (Fin d) (Fin d) (Arctic R)) (vℓ vᵣ : Fin d → Arctic R)
    (hM : arcticMatGt Mℓ Mᵣ) (hv : arcticVecGt vℓ vᵣ) :
    ∀ x, arcticVecGt (arcticAffine Mℓ vℓ x) (arcticAffine Mᵣ vᵣ x) := by
  intro x i
  simp only [arcticAffine, arcticMulVec]
  exact arcticGt_sup (arcticGt_finset_sup _ fun j _ => arcticGt_add_right (x j) (hM i j)) (hv i)

/-- **[KW09, Lemma 6.5], weak form.** Elementwise `⪰` on the matrices and vectors is a
**sufficient** condition for the pointwise weak inequality everywhere:
`Mℓ ⪰ Mᵣ ∧ vℓ ⪰ vᵣ ⟹ [ℓ](x) ⪰ [r](x)` for all `x ∈ A^d`. (Monotonicity of `+` and `⊔`/`Finset.sup`
on `WithBot R`.) -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticAffine_arcticVecGe [LinearOrder R] [Add R] [AddRightMono R]
    (Mℓ Mᵣ : Matrix (Fin d) (Fin d) (Arctic R)) (vℓ vᵣ : Fin d → Arctic R)
    (hM : arcticMatGe Mℓ Mᵣ) (hv : arcticVecGe vℓ vᵣ) :
    ∀ x, arcticVecGe (arcticAffine Mℓ vℓ x) (arcticAffine Mᵣ vᵣ x) := by
  intro x i
  show arcticAffine Mᵣ vᵣ x i ≤ arcticAffine Mℓ vℓ x i
  simp only [arcticAffine, arcticMulVec]
  refine sup_le_sup (Finset.sup_mono_fun fun j _ => ?_) (hv i)
  gcongr
  exact hM i j

/-! ### Monotone algebras over the restricted domain `ℕ × A^{d−1}` (Definition 2.14)

Over the full carrier `≫` is not well-founded (`arcticGt_bot_bot`). Restricting to `ℕ × A^{d−1}` —
vectors whose first coordinate is `≥ 0` (so a genuine natural, never `−∞`) — fixes this: the first
coordinate is then a strictly decreasing `ℕ`-measure along `≫`. With the closure condition
`(Mσ)₀₀ ≥ 0 ∨ (vσ)₀ ≥ 0` the affine maps preserve this domain, giving a *weakly* monotone algebra;
restricting to `A_ℕ` with `vσ = −∞` gives an *extended* one. -/

/-- `≫` is preserved by arctic multiplication on the **left**, `a ≫ b → c ⊗ a ≫ c ⊗ b` (the
commuted form of `arcticGt_add_right`); used for strict monotonicity of the interpretation. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticGt_add_right]
theorem arcticGt_add_left [LinearOrder R] [AddCommMonoid R] [AddRightStrictMono R]
    (c : Arctic R) {a b : Arctic R} (h : arcticGt a b) : arcticGt (c + a) (c + b) := by
  rw [add_comm c a, add_comm c b]; exact arcticGt_add_right c h

/-- **Domain closure.** Under `(Mσ)₀₀ ≥ 0 ∨ (vσ)₀ ≥ 0` the affine map keeps the first coordinate
`≥ 0`: `0 ≤ x₀ → 0 ≤ [σ](x)₀`. (`0` here is `↑(0:R)`, the *finite* zero — `x₀ ≥ 0` says `x₀ ∈ ℕ`,
not that `x₀ = −∞`.) Either the constant `vσ₀ ≥ 0` survives the final `⊕`, or the `j = 0` term
`Mσ₀₀ + x₀ ≥ 0` does. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticAffine_dom [LinearOrder R] [AddCommMonoid R] [AddLeftMono R] [NeZero d]
    {M : Matrix (Fin d) (Fin d) (Arctic R)} {v x : Fin d → Arctic R}
    (hcond : 0 ≤ M 0 0 ∨ 0 ≤ v 0) (hx : 0 ≤ x 0) : 0 ≤ arcticAffine M v x 0 := by
  simp only [arcticAffine, arcticMulVec]
  rcases hcond with hM | hv
  · have h2 : M 0 0 + x 0 ≤ Finset.univ.sup (fun j => M 0 j + x j) :=
      Finset.le_sup (f := fun j => M 0 j + x j) (Finset.mem_univ (0 : Fin d))
    exact ((add_nonneg hM hx).trans h2).trans le_sup_left
  · exact le_trans hv le_sup_right

/-- Scalar compatibility `≫ · ⪰ ⊆ ≫`: `a ≫ b → b ⪰ c → a ≫ c`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticGt_arcticGe [LinearOrder R] {a b c : Arctic R}
    (h1 : arcticGt a b) (h2 : arcticGe b c) : arcticGt a c := by
  rcases h1 with hba | ⟨ha, hb⟩
  · exact Or.inl (lt_of_le_of_lt h2 hba)
  · subst ha hb; exact Or.inr ⟨rfl, le_bot_iff.mp h2⟩

/-- Vector compatibility `≫ · ⪰ ⊆ ≫`, elementwise from `arcticGt_arcticGe`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticGt_arcticGe]
theorem arcticVecGt_arcticVecGe [LinearOrder R] {a b c : Fin d → Arctic R}
    (h1 : arcticVecGt a b) (h2 : arcticVecGe b c) : arcticVecGt a c :=
  fun i => arcticGt_arcticGe (h1 i) (h2 i)

/-- The interpretation is **`⪰`-monotone in its argument**: `x ⪰ y → [σ](x) ⪰ [σ](y)` (the
weakly-monotone-algebra requirement `mono_ge`). -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticAffine_mono [LinearOrder R] [Add R] [AddLeftMono R]
    (M : Matrix (Fin d) (Fin d) (Arctic R)) (v : Fin d → Arctic R) {x y : Fin d → Arctic R}
    (h : arcticVecGe x y) : arcticVecGe (arcticAffine M v x) (arcticAffine M v y) := by
  intro i
  show arcticAffine M v y i ≤ arcticAffine M v x i
  simp only [arcticAffine, arcticMulVec]
  exact sup_le_sup (Finset.sup_mono_fun fun j _ => by gcongr; exact h j) le_rfl

/-- **Natural arctic interpretations give a weakly monotone Σ-algebra** ([KW09], Definition 2.14).
Over the domain `ℕ × A^{d−1}` (`{x // 0 ≤ x 0}`), with `gt = ≫`, `ge = ⪰` and the affine
interpretations `[σ] = arcticAffine (M σ) (v σ)`, provided each symbol satisfies the closure
condition `(Mσ)₀₀ ≥ 0 ∨ (vσ)₀ ≥ 0` and `≫` is well-founded on the domain (`hwf`, supplied by
`arcticInt_terminating` / `arcticNat_terminating`). -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses WeaklyMonotoneAlgebra arcticAffine arcticAffine_dom arcticVecGt_arcticVecGe
    arcticAffine_mono]
def arcticWeaklyMonotoneAlgebra {α : Type*} [LinearOrder R] [AddCommMonoid R] [AddLeftMono R]
    [NeZero d] (M : α → Matrix (Fin d) (Fin d) (Arctic R)) (v : α → Fin d → Arctic R)
    (hcond : ∀ σ, 0 ≤ M σ 0 0 ∨ 0 ≤ v σ 0)
    (hwf : Terminating (fun a b : {x : Fin d → Arctic R // 0 ≤ x 0} => arcticVecGt a.val b.val)) :
    WeaklyMonotoneAlgebra α {x : Fin d → Arctic R // 0 ≤ x 0} where
  den := fun σ x => ⟨arcticAffine (M σ) (v σ) x.val, arcticAffine_dom (hcond σ) x.property⟩
  gt := fun a b => arcticVecGt a.val b.val
  ge := fun a b => arcticVecGe a.val b.val
  gt_wf := hwf
  compat := fun _ _ _ h1 h2 => arcticVecGt_arcticVecGe h1 h2
  mono_ge := fun σ _ _ h => arcticAffine_mono (M σ) (v σ) h

/-- **`A_ℕ` with `vσ = −∞` gives an extended monotone Σ-algebra** ([KW09], Definition 2.14).
Setting every constant vector to `−∞` (so `[σ](x) = Mσ ⊗ x`) and requiring `(Mσ)₀₀ ≥ 0` upgrades the
weakly monotone algebra to an extended one: the interpretation is then also `≫`-monotone in its
argument (`mono_gt`, via `arcticGt_finset_sup` and `arcticGt_add_left`). The `−∞` constant is what
lets `mono_gt` go through — a finite `vσ` would need the false `vσ ≫ vσ`. -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses ExtendedMonotoneAlgebra arcticWeaklyMonotoneAlgebra arcticGt_finset_sup
    arcticGt_add_left]
def arcticExtendedMonotoneAlgebra {α : Type*} [LinearOrder R] [AddCommMonoid R] [AddLeftMono R]
    [AddRightStrictMono R] [NeZero d] (M : α → Matrix (Fin d) (Fin d) (Arctic R))
    (hM : ∀ σ, 0 ≤ M σ 0 0)
    (hwf : Terminating (fun a b : {x : Fin d → Arctic R // 0 ≤ x 0} => arcticVecGt a.val b.val)) :
    ExtendedMonotoneAlgebra α {x : Fin d → Arctic R // 0 ≤ x 0} where
  toWeaklyMonotoneAlgebra :=
    arcticWeaklyMonotoneAlgebra M (fun _ _ => ⊥) (fun σ => Or.inl (hM σ)) hwf
  mono_gt := fun σ a b h => by
    intro i
    show arcticGt (arcticAffine (M σ) (fun _ => ⊥) a.val i) (arcticAffine (M σ) (fun _ => ⊥) b.val i)
    simp only [arcticAffine, arcticMulVec, sup_bot_eq]
    exact arcticGt_finset_sup _ fun j _ => arcticGt_add_left (M σ i j) (h j)

private theorem unbotD_toNat_lt {p q : Arctic ℤ} (hp : (0 : Arctic ℤ) ≤ p) (hpq : p < q) :
    (WithBot.unbotD 0 p).toNat < (WithBot.unbotD 0 q).toNat := by
  have hpne : p ≠ ⊥ := by rintro rfl; simp at hp
  obtain ⟨p', rfl⟩ := WithBot.ne_bot_iff_exists.mp hpne
  obtain ⟨q', rfl⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hpq)
  have hp' : (0 : ℤ) ≤ p' := by exact_mod_cast hp
  have hpq' : p' < q' := by exact_mod_cast hpq
  simp only [WithBot.unbotD_coe]; omega

/-- **`≫` is well-founded on `ℕ × A_ℤ^{d−1}`** (arctic integers). The map `x ↦ (x₀ : ℤ).toNat`
strictly decreases along `≫`: every `≫`-step is strict in the first coordinate, which stays `≥ 0`,
so it gives a strictly decreasing `ℕ`-measure (`terminating_of_measure`). -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses terminating_of_measure arcticVecGt]
theorem arcticInt_terminating [NeZero d] :
    Terminating (fun a b : {x : Fin d → Arctic ℤ // 0 ≤ x 0} => arcticVecGt a.val b.val) := by
  apply terminating_of_measure (fun x => (WithBot.unbotD 0 (x.val 0)).toNat)
  rintro u v huv
  rcases huv 0 with hlt | ⟨hb, _⟩
  · exact unbotD_toNat_lt v.property hlt
  · exact absurd (hb ▸ u.property) (by simp)

private theorem unbotD_lt {p q : Arctic ℕ} (hp : (0 : Arctic ℕ) ≤ p) (hpq : p < q) :
    WithBot.unbotD 0 p < WithBot.unbotD 0 q := by
  have hpne : p ≠ ⊥ := by rintro rfl; simp at hp
  obtain ⟨p', rfl⟩ := WithBot.ne_bot_iff_exists.mp hpne
  obtain ⟨q', rfl⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hpq)
  simp only [WithBot.unbotD_coe]; exact_mod_cast hpq

/-- **`≫` is well-founded on `ℕ × A_ℕ^{d−1}`** (arctic naturals). As for `arcticInt_terminating`,
with the first coordinate `x₀ : ℕ` itself the strictly decreasing measure. -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses terminating_of_measure arcticVecGt]
theorem arcticNat_terminating [NeZero d] :
    Terminating (fun a b : {x : Fin d → Arctic ℕ // 0 ≤ x 0} => arcticVecGt a.val b.val) := by
  apply terminating_of_measure (fun x => WithBot.unbotD 0 (x.val 0))
  rintro u v huv
  rcases huv 0 with hlt | ⟨hb, _⟩
  · exact unbotD_lt v.property hlt
  · exact absurd (hb ▸ u.property) (by simp)

/-- The weakly monotone Σ-algebra of **arctic integers** `A_ℤ` (used for *top* termination). -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticWeaklyMonotoneAlgebra arcticInt_terminating]
def arcticIntWeaklyMonotoneAlgebra {α : Type*} [NeZero d]
    (M : α → Matrix (Fin d) (Fin d) (Arctic ℤ)) (v : α → Fin d → Arctic ℤ)
    (hcond : ∀ σ, 0 ≤ M σ 0 0 ∨ 0 ≤ v σ 0) :
    WeaklyMonotoneAlgebra α {x : Fin d → Arctic ℤ // 0 ≤ x 0} :=
  arcticWeaklyMonotoneAlgebra M v hcond arcticInt_terminating

/-- The weakly monotone Σ-algebra of **arctic naturals** `A_ℕ`. -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticWeaklyMonotoneAlgebra arcticNat_terminating]
def arcticNatWeaklyMonotoneAlgebra {α : Type*} [NeZero d]
    (M : α → Matrix (Fin d) (Fin d) (Arctic ℕ)) (v : α → Fin d → Arctic ℕ)
    (hcond : ∀ σ, 0 ≤ M σ 0 0 ∨ 0 ≤ v σ 0) :
    WeaklyMonotoneAlgebra α {x : Fin d → Arctic ℕ // 0 ≤ x 0} :=
  arcticWeaklyMonotoneAlgebra M v hcond arcticNat_terminating

/-- The **extended** monotone Σ-algebra of arctic naturals `A_ℕ` with `vσ = −∞` and `(Mσ)₀₀ ≥ 0`
(used for ordinary termination). -/
@[category research solved, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticExtendedMonotoneAlgebra arcticNat_terminating]
def arcticNatExtendedMonotoneAlgebra {α : Type*} [NeZero d]
    (M : α → Matrix (Fin d) (Fin d) (Arctic ℕ)) (hM : ∀ σ, 0 ≤ M σ 0 0) :
    ExtendedMonotoneAlgebra α {x : Fin d → Arctic ℕ // 0 ≤ x 0} :=
  arcticExtendedMonotoneAlgebra M hM arcticNat_terminating

/-! ### Composition of arctic interpretations (the max–plus matrix product)

The interpretation of a string composes the per-symbol maps; over the arctic semiring this is the
**max–plus matrix product** `(B ⊗ A)ᵢₖ = maxⱼ (Bᵢⱼ + Aⱼₖ)` (`arcticMatMul`), which acts on vectors
associatively (`arcticMulVec_arcticMatMul`). So the interpretation `[σ₁⋯σₙ]` of a rule side is again
a single arctic-linear map, with matrix the product `M_{σ₁} ⊗ ⋯ ⊗ M_{σₙ}` — letting elementwise
comparisons (Lemma 6.5) decide the rule conditions. (Here the constant vectors are `−∞`, the
extended-algebra case; `arcticAffine M (−∞) = arcticMulVec M`, `arcticAffine_bot`.) -/

/-- Arctic multiplication distributes over the finite arctic sum on the right:
`(⊕ᵢ fᵢ) ⊗ c = ⊕ᵢ (fᵢ ⊗ c)`, i.e. `(s.sup f) + c = s.sup (f · + c)`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arctic_sup_add [LinearOrder R] [AddCommMonoid R] [AddLeftMono R] {ι : Type*}
    (s : Finset ι) (f : ι → Arctic R) (c : Arctic R) :
    s.sup f + c = s.sup (fun i => f i + c) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => rw [Finset.sup_cons, Finset.sup_cons, max_add, ih]

/-- Arctic multiplication distributes over the finite arctic sum on the left:
`c ⊗ (⊕ᵢ fᵢ) = ⊕ᵢ (c ⊗ fᵢ)`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arctic_add_sup [LinearOrder R] [AddCommMonoid R] [AddLeftMono R] {ι : Type*}
    (s : Finset ι) (f : ι → Arctic R) (c : Arctic R) :
    c + s.sup f = s.sup (fun i => c + f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih => rw [Finset.sup_cons, Finset.sup_cons, add_max, ih]

/-- The **max–plus matrix product** `(B ⊗ A)ᵢₖ = ⊕ⱼ Bᵢⱼ ⊗ Aⱼₖ = maxⱼ (Bᵢⱼ + Aⱼₖ)`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
def arcticMatMul [LinearOrder R] [Add R] (B A : Matrix (Fin d) (Fin d) (Arctic R)) :
    Matrix (Fin d) (Fin d) (Arctic R) := fun i k => Finset.univ.sup (fun j => B i j + A j k)

/-- **Associativity of the arctic matrix action**: `(B ⊗ A) ⊗ x = B ⊗ (A ⊗ x)`. This is what makes
the composite of two arctic-linear maps again arctic-linear, with matrix `B ⊗ A` — the arctic analog
of `MatrixInterpretation.affine_comp`. (Proof: distribute `+` over the `sup`s with `arctic_sup_add` /
`arctic_add_sup`, swap the two sums by `Finset.sup_comm`, and reassociate.) -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arctic_sup_add arctic_add_sup]
theorem arcticMulVec_arcticMatMul [LinearOrder R] [AddCommMonoid R] [AddLeftMono R]
    (B A : Matrix (Fin d) (Fin d) (Arctic R)) (x : Fin d → Arctic R) :
    arcticMulVec (arcticMatMul B A) x = arcticMulVec B (arcticMulVec A x) := by
  funext i
  simp only [arcticMulVec, arcticMatMul, arctic_sup_add, arctic_add_sup]
  rw [Finset.sup_comm]
  simp only [add_assoc]

/-- With constant vector `−∞`, the arctic affine map is just the matrix action:
`arcticAffine M (−∞) = arcticMulVec M` (the `⊕ −∞` is the identity). The form taken by the
interpretations in the *extended* monotone-algebra case. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation"]
theorem arcticAffine_bot [LinearOrder R] [Add R] (M : Matrix (Fin d) (Fin d) (Arctic R))
    (x : Fin d → Arctic R) : arcticAffine M (fun _ => ⊥) x = arcticMulVec M x := by
  funext i; simp [arcticAffine]

/-- Lemma 6.5 for the pure matrix action (`v = −∞`): `M ≫ N ⟹ M ⊗ x ≫ N ⊗ x` for all `x`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticAffine_arcticVecGt arcticAffine_bot arcticGt_bot_bot]
theorem arcticMulVec_arcticVecGt [LinearOrder R] [AddCommMonoid R] [AddRightStrictMono R]
    (B C : Matrix (Fin d) (Fin d) (Arctic R)) (hBC : arcticMatGt B C) (x : Fin d → Arctic R) :
    arcticVecGt (arcticMulVec B x) (arcticMulVec C x) := by
  have := arcticAffine_arcticVecGt B C (fun _ => ⊥) (fun _ => ⊥) hBC (fun _ => arcticGt_bot_bot) x
  rwa [arcticAffine_bot, arcticAffine_bot] at this

/-- Lemma 6.5 for the pure matrix action (`v = −∞`): `M ⪰ N ⟹ M ⊗ x ⪰ N ⊗ x` for all `x`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "arctic_interpretation",
  formal_uses arcticAffine_arcticVecGe arcticAffine_bot]
theorem arcticMulVec_arcticVecGe [LinearOrder R] [AddCommMonoid R] [AddRightMono R]
    (B C : Matrix (Fin d) (Fin d) (Arctic R)) (hBC : arcticMatGe B C) (x : Fin d → Arctic R) :
    arcticVecGe (arcticMulVec B x) (arcticMulVec C x) := by
  have := arcticAffine_arcticVecGe B C (fun _ => ⊥) (fun _ => ⊥) hBC (fun _ => le_refl _) x
  rwa [arcticAffine_bot, arcticAffine_bot] at this

/-- `≫` is decidable on arctic scalars (a finite check). -/
instance instDecidableArcticGt [LinearOrder R] (u v : Arctic R) : Decidable (arcticGt u v) := by
  unfold arcticGt; infer_instance

/-- `≫` is decidable on arctic matrices (entrywise). -/
instance instDecidableArcticMatGt [LinearOrder R] (M N : Matrix (Fin d) (Fin d) (Arctic R)) :
    Decidable (arcticMatGt M N) := by unfold arcticMatGt; infer_instance

/-- `⪰` is decidable on arctic matrices (entrywise). -/
instance instDecidableArcticMatGe [LinearOrder R] (M N : Matrix (Fin d) (Fin d) (Arctic R)) :
    Decidable (arcticMatGe M N) := by unfold arcticMatGe arcticGe; infer_instance

/-! ### Example 2.17 — `SN({◁b → ◁ax} / P)` by a 4-dimensional arctic interpretation

A worked instance ([KW09], simulating the Abelian sandpile model over a path): the relative
termination `SN({◁b → ◁ax} / P)` for the SRS
`P = {◁b → ◁ax, aax → bxa, ab → ba, xb → ax, a▷ → ax▷}` over `Σ = {◁, a, b, x, ▷}` (here `◁ = lhd`,
`▷ = rhd`). This has no known *natural* matrix-interpretation proof, but a 4-dimensional **arctic
natural** one: the extended monotone algebra `arcticNatExtendedMonotoneAlgebra Pmat` (constant
vectors `−∞`, top-left entries `0`). Composing the symbol matrices (`arcticMatMul`) and comparing the
rule sides elementwise (`arcticMulVec_arcticVecGt` / `arcticMulVec_arcticVecGe`, all by `decide`)
discharges the conditions of Theorem 2.15 soundness (`terminatingRelativeTo_of_extendedMonotone`):
the `R`-rule `◁b → ◁ax` strictly decreases (`≫`) and every `P`-rule weakly decreases (`⪰`). -/

/-- The alphabet `Σ = {◁, a, b, x, ▷}` of Example 2.17 (`lhd = ◁`, `rhd = ▷`). -/
@[category API, AMS 68, ref "KW09" "ST14", group "example_2_17"]
inductive PLetter | a | b | x | lhd | rhd
  deriving DecidableEq

open PLetter

/-- The five 4×4 arctic-natural interpretation matrices of Example 2.17 (`⊥ = −∞`); the constant
vectors are all `−∞`, and every top-left entry is `0` (so this is an extended monotone algebra). -/
@[category API, AMS 68, ref "KW09" "ST14", group "example_2_17"]
def Pmat : PLetter → Matrix (Fin 4) (Fin 4) (Arctic ℕ)
  | a   => !![0, ⊥, ⊥, ⊥; 1, 1, ⊥, 0; ⊥, 0, ⊥, ⊥; ⊥, ⊥, 0, ⊥]
  | b   => !![0, ⊥, ⊥, ⊥; 1, 1, ⊥, 0; 1, 0, 1, ⊥; ⊥, ⊥, 0, ⊥]
  | x   => !![0, ⊥, ⊥, ⊥; ⊥, ⊥, 0, ⊥; ⊥, ⊥, ⊥, 0; ⊥, 0, ⊥, ⊥]
  | lhd => !![0, ⊥, 0, ⊥; ⊥, ⊥, ⊥, ⊥; ⊥, ⊥, ⊥, ⊥; ⊥, ⊥, ⊥, ⊥]
  | rhd => !![0, ⊥, ⊥, ⊥; ⊥, ⊥, ⊥, ⊥; ⊥, ⊥, ⊥, ⊥; ⊥, ⊥, ⊥, ⊥]

/-- The SRS `P = {◁b → ◁ax, aax → bxa, ab → ba, xb → ax, a▷ → ax▷}` of Example 2.17. -/
@[category API, AMS 68, ref "KW09" "ST14", group "example_2_17"]
def Psys : System PLetter := fun ℓ r =>
  (ℓ = [lhd, b] ∧ r = [lhd, a, x]) ∨ (ℓ = [a, a, x] ∧ r = [b, x, a]) ∨
  (ℓ = [a, b] ∧ r = [b, a]) ∨ (ℓ = [x, b] ∧ r = [a, x]) ∨ (ℓ = [a, rhd] ∧ r = [a, x, rhd])

/-- The single rule `R = {◁b → ◁ax}` whose relative termination over `P` is at stake. -/
@[category API, AMS 68, ref "KW09" "ST14", group "example_2_17"]
def Rrule : System PLetter := fun ℓ r => ℓ = [lhd, b] ∧ r = [lhd, a, x]

private theorem bridge_pair (hM : ∀ σ, (0 : Arctic ℕ) ≤ Pmat σ 0 0) (s t : PLetter)
    (z : {v : Fin 4 → Arctic ℕ // (0 : Arctic ℕ) ≤ v 0}) :
    (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [s, t] z).val
      = arcticMulVec (arcticMatMul (Pmat s) (Pmat t)) z.val := by
  simp only [strInterp, Function.comp_apply, id_eq, arcticNatExtendedMonotoneAlgebra,
    arcticExtendedMonotoneAlgebra, arcticWeaklyMonotoneAlgebra]
  rw [arcticAffine_bot, arcticAffine_bot, arcticMulVec_arcticMatMul]

private theorem bridge_triple (hM : ∀ σ, (0 : Arctic ℕ) ≤ Pmat σ 0 0) (s t u : PLetter)
    (z : {v : Fin 4 → Arctic ℕ // (0 : Arctic ℕ) ≤ v 0}) :
    (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [s, t, u] z).val
      = arcticMulVec (arcticMatMul (Pmat s) (arcticMatMul (Pmat t) (Pmat u))) z.val := by
  simp only [strInterp, Function.comp_apply, id_eq, arcticNatExtendedMonotoneAlgebra,
    arcticExtendedMonotoneAlgebra, arcticWeaklyMonotoneAlgebra]
  rw [arcticAffine_bot, arcticAffine_bot, arcticAffine_bot, arcticMulVec_arcticMatMul,
    arcticMulVec_arcticMatMul]

/-- **Example 2.17** ([KW09]). The single rule `R = {◁b → ◁ax}` is terminating **relative to**
`P = {◁b → ◁ax, aax → bxa, ab → ba, xb → ax, a▷ → ax▷}`, proved by a 4-dimensional arctic-natural
matrix interpretation. The extended monotone algebra `arcticNatExtendedMonotoneAlgebra Pmat` (all
constant vectors `−∞`) interprets each rule side by the max–plus product of its symbol matrices
(`bridge_pair` / `bridge_triple`, via `arcticMatMul`); the `R`-rule then strictly decreases and every
`P`-rule weakly decreases — finite elementwise comparisons of the composite matrices closed by
`decide` (Lemma 6.5, `arcticMulVec_arcticVecGt` / `arcticMulVec_arcticVecGe`) — so Theorem 2.15
soundness (`terminatingRelativeTo_of_extendedMonotone`) gives `SN(R / P)`. This is a relative
termination that has *no* known natural matrix-interpretation proof. -/
@[category textbook, AMS 68, ref "KW09" "ST14", group "example_2_17",
  formal_uses terminatingRelativeTo_of_extendedMonotone arcticNatExtendedMonotoneAlgebra
    arcticMulVec_arcticVecGt arcticMulVec_arcticVecGe arcticMatMul Pmat Psys Rrule]
theorem terminating_Rrule_relative_Psys :
    TerminatingRelativeTo (RewriteStep Rrule) (RewriteStep Psys) := by
  haveI : Nonempty {v : Fin 4 → Arctic ℕ // (0 : Arctic ℕ) ≤ v 0} := ⟨⟨fun _ => 0, le_refl _⟩⟩
  have hM : ∀ σ, (0 : Arctic ℕ) ≤ Pmat σ 0 0 := fun σ => by cases σ <;> decide
  apply terminatingRelativeTo_of_extendedMonotone (arcticNatExtendedMonotoneAlgebra Pmat hM)
  · rintro ℓ r ⟨rfl, rfl⟩ z
    show arcticVecGt (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [lhd, b] z).val
      (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [lhd, a, x] z).val
    rw [bridge_pair, bridge_triple]
    exact arcticMulVec_arcticVecGt _ _ (by decide) z.val
  · rintro ℓ r hr z
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show arcticVecGe (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [lhd, b] z).val
        (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [lhd, a, x] z).val
      rw [bridge_pair, bridge_triple]; exact arcticMulVec_arcticVecGe _ _ (by decide) z.val
    · show arcticVecGe (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [a, a, x] z).val
        (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [b, x, a] z).val
      rw [bridge_triple, bridge_triple]; exact arcticMulVec_arcticVecGe _ _ (by decide) z.val
    · show arcticVecGe (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [a, b] z).val
        (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [b, a] z).val
      rw [bridge_pair, bridge_pair]; exact arcticMulVec_arcticVecGe _ _ (by decide) z.val
    · show arcticVecGe (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [x, b] z).val
        (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [a, x] z).val
      rw [bridge_pair, bridge_pair]; exact arcticMulVec_arcticVecGe _ _ (by decide) z.val
    · show arcticVecGe (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [a, rhd] z).val
        (strInterp (arcticNatExtendedMonotoneAlgebra Pmat hM).den [a, x, rhd] z).val
      rw [bridge_pair, bridge_triple]; exact arcticMulVec_arcticVecGe _ _ (by decide) z.val

end StringRewriting.ArcticInterpretation
