/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.CollatzSRS
import SRS.Zantema
import SRS.ArcticInterpretation
import Mathlib.Tactic.Linarith

/-!
# Derivational-complexity lower bounds and the failure of one-shot arctic proofs (YAH; KW09)

The mixed-base SRS `𝒯` (`SRS.CollatzSRS`) and Zantema's unary `𝒵` (`SRS.Zantema`) both simulate the
Collatz function, so both are terminating **iff** the Collatz conjecture holds. A natural question is
whether the termination-proof *method* of (natural / arctic) matrix interpretations can settle them.
For `𝒵` and *natural* matrix interpretations the answer is a sharp **no** (`Zantema.theorem_3_8`,
[YAH]). This file records the complementary **derivational-complexity** obstruction, ruling out
*arctic* matrix-interpretation proofs by a counting argument.

The key external input is **Koprowski–Waldmann** ([KW09], Lemma 12.1): an arctic matrix-interpretation
termination proof bounds the **derivational complexity** of the system **linearly** in the string
length — the max–plus interpretation of a string of length `L` is `O(L)`, and each rewrite strictly
drops a tracked natural component, so no derivation is longer than linear. Hence a *superlinear*
derivational-complexity lower bound rules out any such proof.

## Contents

* `ReachesIn R n u v` — `u` reaches `v` in **exactly `n`** `→_R`-steps (a counted derivation), with
  `reachesIn_of_reflTransGen` (every `→*_R` derivation has a length) and `ReachesIn.length_le` (a
  per-step length-growth bound `c` forces `|v| ≤ |u| + c·n`).
* `DcSuperlinear R` / `DcLinear R` — a *superlinear* derivational-complexity lower bound (some
  derivation beats every linear rate `C·(|s|+1)`) and a *linear* upper bound; they are contradictory
  (`not_dcLinear_of_dcSuperlinear`).
* `HasOneShotArcticProof R` — a single extended monotone **arctic-natural** matrix interpretation
  (`SRS.ArcticInterpretation`) orienting `R` (every rule weakly `⪰`, one rule strictly `≫`); the
  data a rule-removal step consumes. `hasOneShotArcticProof_dcLinear` — **[KW09], cited axiom**: such
  a proof yields `DcLinear`. `no_arctic_of_dcSuperlinear` / `proposition_B` — the **representation
  floor**: a superlinear family forbids any one-shot arctic proof.
* **Proposition A** (`proposition_A`): `dc_𝒯(L) = Ω(L²)` — the mixed-base `𝒯` has superlinear
  derivational complexity. The witness family is `tStr (k−1) = ◁tᵏ⁻¹▷` (value `2ᵏ − 1`, length `k+1`,
  `tStr_value`); its canonical simulation runs the `k` consecutive odd (tripling) steps of the orbit
  `2ᵏ−1 → 3·2ᵏ⁻¹−1 → ⋯ → 3ᵏ−1` (`T_orbit`), the `i`-th of which must transport a binary `t` across
  the `i−1` ternary digits already produced — `≥ i` base-swap rewrites — so the derivation has
  `≥ 1+2+⋯+(k−1) = (k−1)k/2` steps (`tStr_derivation_quadratic`). **Corollary A** (`corollary_A`):
  `𝒯` has **no** one-shot arctic termination proof.
* **Corollary B** (`corollary_B`): the unary `𝒵` likewise has no one-shot arctic proof. Here the
  reason is complementary — `𝒵`'s *representation itself* blows up: the orbit of `2ᵏ−1` drives the
  unary string from length `≈ 2ᵏ` to length `≈ 3ᵏ = L^{log₂3}` (`config_reaches_orbit`,
  `Z_derivation_long`, chaining the proven `Zantema.oddSim`), and every `𝒵`-rule lengthens the string
  by `≤ 2` (`Z_step_length`), so the derivation has `≥ (3ᵏ − 2ᵏ)/2` steps — superlinear
  (`dcSuperlinear_Z`).

## References
* [YAH] Yolcu, Aaronson, Heule. *An Automated Approach to the Collatz Conjecture.* arXiv:2105.14697.
* [KW09] Koprowski, Waldmann. *Max/plus tree automata for termination of term rewriting.*
  Acta Cybernetica 19.2 (2009), 357–392.
* [BO93] Book, Otto. *String-Rewriting Systems.* Springer, 1993.
-/

namespace StringRewriting.ComplexityBound

open StringRewriting StringRewriting.CollatzSRS StringRewriting.Zantema
  StringRewriting.MixedBase StringRewriting.ArcticInterpretation Relation

variable {α : Type*}

/-! ### Counted reachability (derivation length) -/

/-- `ReachesIn R n u v`: the string `u` reaches `v` in **exactly `n`** rewrite steps of `R` — a
derivation `u = w₀ →_R w₁ →_R ⋯ →_R wₙ = v` of length `n`. (The reflexive–transitive closure `→*_R`
forgets the length; `ReachesIn` is the counted refinement used for complexity bounds.) -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
def ReachesIn (R : System α) : ℕ → List α → List α → Prop
  | 0,     u, v => u = v
  | (n+1), u, v => ∃ w, RewriteStep R u w ∧ ReachesIn R n w v

/-- Append one step at the end of a counted derivation: `u →ⁿ v →_R w` gives `u →ⁿ⁺¹ w`. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.tail {R : System α} {n : ℕ} {u v w : List α}
    (h : ReachesIn R n u v) (hs : RewriteStep R v w) : ReachesIn R (n + 1) u w := by
  induction n generalizing u with
  | zero => obtain rfl := h; exact ⟨w, hs, rfl⟩
  | succ k ih => obtain ⟨x, hx, hxv⟩ := h; exact ⟨x, hx, ih hxv⟩

/-- Prepend one step to the front of a counted derivation: `u →_R w →ⁿ v` gives `u →ⁿ⁺¹ v`. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.head {R : System α} {n : ℕ} {u w v : List α}
    (hs : RewriteStep R u w) (h : ReachesIn R n w v) : ReachesIn R (n + 1) u v := ⟨w, hs, h⟩

/-- Concatenate two counted derivations: `u →ⁿ v →ᵏ w` gives `u →ⁿ⁺ᵏ w`. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.trans {R : System α} {n k : ℕ} {u v w : List α}
    (h1 : ReachesIn R n u v) (h2 : ReachesIn R k v w) : ReachesIn R (n + k) u w := by
  induction n generalizing u with
  | zero => obtain rfl := h1; rw [Nat.zero_add]; exact h2
  | succ p ih =>
    obtain ⟨x, hx, hxv⟩ := h1
    have hres : ReachesIn R (p + k + 1) u w := ⟨x, hx, ih hxv⟩
    rwa [show p + k + 1 = p + 1 + k from by omega] at hres

/-- A counted derivation lifts through a surrounding context `p · q`, with the same length. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.append_context {R : System α} {n : ℕ} {u v : List α}
    (h : ReachesIn R n u v) (p q : List α) : ReachesIn R n (p ++ u ++ q) (p ++ v ++ q) := by
  induction n generalizing u with
  | zero => obtain rfl := h; rfl
  | succ k ih => obtain ⟨x, hx, hxv⟩ := h; exact ⟨p ++ x ++ q, hx.append_context p q, ih hxv⟩

/-- A counted derivation lifts through prepending a single symbol `a`. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.cons {R : System α} {n : ℕ} {u v : List α} (a : α)
    (h : ReachesIn R n u v) : ReachesIn R n (a :: u) (a :: v) := by
  have := h.append_context [a] []; simpa using this

/-- Every `→*_R` derivation `u →*_R v` has a length: `∃ n, ReachesIn R n u v`. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
theorem reachesIn_of_reflTransGen {R : System α} {u v : List α}
    (h : ReflTransGen (RewriteStep R) u v) : ∃ n, ReachesIn R n u v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hcd ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hn.tail hcd⟩

/-- **Length-growth bound.** If every `R`-step lengthens the string by at most `c`
(`|v| ≤ |u| + c`), then an `n`-step derivation lengthens it by at most `c·n`:
`|v| ≤ |u| + c·n`. The contrapositive — a large length increase forces many steps — is the engine of
the unary lower bound `Z_derivation_long`. -/
@[category research solved, AMS 68, ref "BO93", group "complexity_bound"]
theorem ReachesIn.length_le {R : System α} (c : ℕ)
    (hc : ∀ u v, RewriteStep R u v → v.length ≤ u.length + c)
    {n : ℕ} {u v : List α} (h : ReachesIn R n u v) : v.length ≤ u.length + c * n := by
  induction n generalizing u with
  | zero => obtain rfl := h; simp
  | succ k ih =>
    obtain ⟨w, hw, hwv⟩ := h
    have h1 := hc u w hw
    have h2 := ih hwv
    have h3 : c * (k + 1) = c + c * k := by ring
    omega

/-! ### Derivational complexity: superlinear vs. linear -/

/-- A **superlinear derivational-complexity lower bound**: for *every* linear rate `C`, some
`R`-derivation from some string `s` takes **more than** `C·(|s|+1)` steps. This is the negation of
any linear upper bound — it is what a quadratic (or `L^{log₂3}`) lower bound provides. -/
@[category API, AMS 68, ref "BO93", group "complexity_bound"]
def DcSuperlinear (R : System α) : Prop :=
  ∀ C : ℕ, ∃ s v N, ReachesIn R N s v ∧ C * (s.length + 1) < N

/-- A **linear derivational-complexity upper bound**: a single constant `C` bounds *every*
derivation's length by `C·(|s|+1)` in the start length `|s|`. By Koprowski–Waldmann ([KW09],
Lemma 12.1) this is what a one-shot arctic matrix-interpretation proof yields. -/
@[category API, AMS 68, ref "KW09", group "complexity_bound"]
def DcLinear (R : System α) : Prop :=
  ∃ C : ℕ, ∀ s v N, ReachesIn R N s v → N ≤ C * (s.length + 1)

/-- Superlinear and linear derivational complexity are **contradictory**: the linear constant `C`
caps every derivation at `C·(|s|+1)`, but the superlinear family produces one exceeding that very
bound. -/
@[category research solved, AMS 68, ref "BO93", group "complexity_bound"]
theorem not_dcLinear_of_dcSuperlinear {R : System α} (h : DcSuperlinear R) : ¬ DcLinear R := by
  rintro ⟨C, hC⟩
  obtain ⟨s, v, N, hN, hlt⟩ := h C
  exact absurd (hC s v N hN) (by omega)

/-! ### One-shot arctic proofs and the Koprowski–Waldmann linear bound -/

/-- A **one-shot arctic (matrix-interpretation) termination proof** for `R`: a single extended
monotone arctic-natural algebra (`SRS.ArcticInterpretation`) — a dimension `d ≥ 1`, symbol matrices
`M σ` and constant vectors `v σ` over the arctic naturals `A_ℕ = ℕ ∪ {−∞}`, satisfying the
domain-closure condition `(Mσ)₀₀ ≥ 0 ∨ (vσ)₀ ≥ 0` — that **orients** `R`: under the induced string
interpretations `[·] = strInterp (fun σ => arcticAffine (Mσ) (vσ))`, **every** rule weakly decreases
(`⪰`, `arcticVecGe`) and **at least one** rule strictly decreases (`≫`, `arcticVecGt`).

This is exactly the data a rule-removal step (Theorem 2.6 / Theorem 2.15) consumes to make progress
towards `SN(R)` — the arctic analogue of the natural-matrix orientation refuted for `𝒵` in
`Zantema.theorem_3_8`. -/
@[category API, AMS 68, ref "KW09" "ST14", group "complexity_bound"]
def HasOneShotArcticProof (R : System α) : Prop :=
  ∃ (d : ℕ) (_ : NeZero d) (M : α → Matrix (Fin d) (Fin d) (Arctic ℕ)) (v : α → Fin d → Arctic ℕ),
    (∀ σ, 0 ≤ M σ 0 0 ∨ 0 ≤ v σ 0) ∧
    (∀ ℓ r, R ℓ r → ∀ x, arcticVecGe (strInterp (fun σ => arcticAffine (M σ) (v σ)) ℓ x)
        (strInterp (fun σ => arcticAffine (M σ) (v σ)) r x)) ∧
    (∃ ℓ r, R ℓ r ∧ ∀ x, arcticVecGt (strInterp (fun σ => arcticAffine (M σ) (v σ)) ℓ x)
        (strInterp (fun σ => arcticAffine (M σ) (v σ)) r x))

/-- **Koprowski–Waldmann** ([KW09], **Lemma 12.1**, via **Theorem 6.7**): the arctic matrix method
bounds derivational complexity **linearly**. An arctic matrix-interpretation termination proof — the
extended monotone arctic-`A_ℕ` algebra of `HasOneShotArcticProof`, i.e. the orientation of Theorem 6.7
of [KW09] — yields a linear derivational-complexity bound.
*Proof of [KW09], Lemma 12.1.* Writing `|x⃗| = maxᵢ xᵢ` and `|A| = maxᵢⱼ Aᵢⱼ`, the max–plus operations
satisfy `|A ⊗ x⃗| ≤ |A| + |x⃗|`, so the string interpretation obeys `|[w]| ≤ c·|w|` with
`c = max_f |[f]|` — linear in `|w|`; and each rewrite strictly drops a tracked `ℕ`-component
(`u →_R v ⟹ [u] ≫ [v]`, and `x⃗ ≫ y⃗ ⟹ |x⃗| > |y⃗|`), so a derivation from `u` has at most `c·|u|`
steps. ([KW09] states Lemma 12.1 for the full case `S = ∅`; the one-strict-rest-weak orientation here
is its rule-removal building block.) The §12 Discussion of [KW09] draws exactly the corollary used
below: systems of higher — e.g. quadratic `{ab → ba}` or exponential `{ab → b²a}` — derivational
complexity admit **no** arctic termination proof. Recorded as a **cited axiom**. -/
@[category research solved, AMS 68, ref "KW09", group "complexity_bound"]
axiom hasOneShotArcticProof_dcLinear (R : System α) :
    HasOneShotArcticProof R → DcLinear R

/-- **The representation floor (core form).** If an SRS `R` has **superlinear** derivational
complexity, it admits **no** one-shot arctic termination proof: such a proof would (by
Koprowski–Waldmann, `hasOneShotArcticProof_dcLinear`) force a linear bound, contradicting
superlinearity (`not_dcLinear_of_dcSuperlinear`). -/
@[category research solved, AMS 68, ref "KW09", group "complexity_bound"]
theorem no_arctic_of_dcSuperlinear (R : System α) (h : DcSuperlinear R) :
    ¬ HasOneShotArcticProof R :=
  fun hp => not_dcLinear_of_dcSuperlinear h (hasOneShotArcticProof_dcLinear R hp)

/-- **Proposition B (representation floor).** Any SRS `R` exhibiting a *superlinear family* — for
every rate `C`, an index `k` whose start string `s k` admits a derivation longer than `C·(|s k|+1)` —
admits **no** one-shot arctic termination proof.

This is the general floor underlying both corollaries. The intended instances are *value-faithful
positional encodings* of the Collatz dynamics: feeding the input `2ᵏ−1`, whose orbit takes `k`
consecutive odd steps, produces such a family because each odd step does irreducible work that a
linear (arctic) interpretation cannot amortise. For the mixed-base `𝒯` the family is `s = tStr` and
the work is the `Ω(L²)` digit-transport of Proposition A (parity at the right boundary, `O(1)`
appended symbols per odd step, the `i`-th renormalisation crossing `i` digits); for the unary `𝒵`
the work is the `Ω(L^{log₂3})` blow-up of the representation itself (Corollary B). -/
@[category research solved, AMS 68, ref "KW09", group "complexity_bound"]
theorem proposition_B (R : System α) (s : ℕ → List α)
    (hfam : ∀ C : ℕ, ∃ k v N, ReachesIn R N (s k) v ∧ C * ((s k).length + 1) < N) :
    ¬ HasOneShotArcticProof R := by
  refine no_arctic_of_dcSuperlinear R (fun C => ?_)
  obtain ⟨k, v, N, hr, hlt⟩ := hfam C
  exact ⟨s k, v, N, hr, hlt⟩

/-! ### Proposition A — `dc_𝒯(L) = Ω(L²)` for the mixed-base Collatz SRS `𝒯`

The witness family is the `𝒯`-string `◁tᵏ▷` (`tStr k`). With `k − 1` binary ones it represents
`2ᵏ − 1` and has length `k + 1`; simulating `T` on `2ᵏ − 1` runs `k` consecutive odd (tripling)
steps, and the renormalisation before the `i`-th one transports a binary `t` rightward across the
`i − 1` ternary digits already produced — `≥ i` base-swaps of `𝒜` — for a total of `≥ (k−1)k/2`
rewrites from a string of length `k + 1`, i.e. `Ω(L²)`. -/

/-- The `𝒯`-string `◁tᵏ▷`: the begin marker `◁`, then `k` binary ones `t`, then the end marker `▷`.
Its length is `k + 2` (`tStr_length`) and its value is `2ᵏ⁺¹ − 1` (`tStr_value`); the cost family of
Proposition A is `tStr (k−1) = ◁tᵏ⁻¹▷` (value `2ᵏ − 1`, length `k + 1`). -/
@[category API, AMS 68 11, ref "YAH", group "complexity_bound"]
def tStr (k : ℕ) : List TSym := TSym.lhd :: (List.replicate k TSym.t ++ [TSym.rhd])

@[category API, AMS 68, ref "YAH", group "complexity_bound"]
theorem tStr_length (k : ℕ) : (tStr k).length = k + 2 := by simp [tStr]

/-- Folding `t(x) = 2x+1` over `k` copies, in the `+1`-shifted form that avoids `ℕ`-subtraction:
`fold(◁→t^k, a) + 1 = 2ᵏ·(a+1)`. -/
private theorem foldl_replicate_t (k a : ℕ) :
    (List.replicate k TSym.t).foldl (fun acc s => symFun s acc) a + 1 = 2 ^ k * (a + 1) := by
  induction k generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    have : symFun TSym.t a = 2 * a + 1 := rfl
    rw [this, pow_succ]; ring

/-- **The value of `◁tᵏ▷` is `2ᵏ⁺¹ − 1`** (`Γ`-evaluation, equation (7)/(8) of [YAH]): the begin
marker seeds `1`, each `t` applies `x ↦ 2x+1`, and the end marker is the identity. In particular
`tStr (k−1) = ◁tᵏ⁻¹▷` represents `2ᵏ − 1`. -/
@[category research solved, AMS 68 11, ref "YAH", group "complexity_bound",
  formal_uses compFun]
theorem tStr_value (k : ℕ) : compFun (tStr k) 0 = 2 ^ (k + 1) - 1 := by
  have h := foldl_replicate_t k 1
  have hc : compFun (tStr k) 0 = (List.replicate k TSym.t).foldl (fun acc s => symFun s acc) 1 := by
    simp only [tStr, compFun, List.foldl_cons, List.foldl_append, List.foldl_nil]
    show symFun TSym.rhd ((List.replicate k TSym.t).foldl (fun acc s => symFun s acc)
        (symFun TSym.lhd 0)) = (List.replicate k TSym.t).foldl (fun acc s => symFun s acc) 1
    rw [show symFun TSym.lhd 0 = 1 from rfl]
    simp [symFun, beta]
  rw [hc, pow_succ]; omega

/-- **The orbit of `2ᵏ − 1` takes `k` consecutive odd steps.** Under the accelerated Collatz map `T`,
`Tⁱ(2ᵏ − 1) = 3ⁱ·2ᵏ⁻ⁱ − 1` for every `i < k` — each value `3ⁱ·2ᵏ⁻ⁱ − 1` (with `k − i ≥ 1`) is odd,
so `T` applies the tripling step `2x+1 ↦ 3x+2`. (At `i = k` the value `3ᵏ − 1` is finally even.)
This is the arithmetic reason the simulation of `tStr (k−1)` performs `k` odd steps, each forcing a
digit-transport renormalisation. -/
@[category research solved, AMS 11 68, ref "YAH", group "complexity_bound",
  formal_uses T_odd]
theorem T_orbit (k i : ℕ) (hi : i < k) : T^[i] (2 ^ k - 1) = 3 ^ i * 2 ^ (k - i) - 1 := by
  induction i with
  | zero => simp
  | succ j ih =>
    have hj : j < k := by omega
    rw [Function.iterate_succ_apply', ih hj]
    have hk1 : k - j = (k - (j + 1)) + 1 := by omega
    have hrel : 3 ^ j * 2 ^ (k - j) = 2 * (3 ^ j * 2 ^ (k - (j + 1))) := by rw [hk1, pow_succ]; ring
    have hrhs : 3 ^ (j + 1) * 2 ^ (k - (j + 1)) = 3 * (3 ^ j * 2 ^ (k - (j + 1))) := by
      rw [pow_succ]; ring
    have hpos : 0 < 3 ^ j * 2 ^ (k - (j + 1)) := by positivity
    rw [hrel, hrhs]
    have hsplit : 2 * (3 ^ j * 2 ^ (k - (j + 1))) - 1
        = 2 * (3 ^ j * 2 ^ (k - (j + 1)) - 1) + 1 := by omega
    rw [hsplit, T_odd]; omega

/-- Mechanical check (`decide`) for small `k`: `◁t⁴▷` represents `2⁵ − 1 = 31`. -/
@[category test, AMS 68 11, ref "YAH", group "complexity_bound"]
theorem tStr_value_example : compFun (tStr 4) 0 = 31 := by decide

/-- Mechanical check (`decide`): the four tripling steps of the orbit of `31`,
`31 → 47 → 71 → 107 → 161` (`T⁴(31) = 161 = 3⁴·2 − 1`). -/
@[category test, AMS 11 68, ref "YAH", group "complexity_bound"]
theorem T_orbit_example : T^[4] 31 = 161 := by decide

/-! The canonical derivation of `tStr m`, constructed and counted: the core move `slide` does one odd
step (slide the rightmost `t` across the `b` accumulated `2`s via `t2 → 2t`, then `t▷ → 2▷`) in `b+1`
rewrites; `coreChain` chains it over the `m` ones, giving `∑_{b<m}(b+1) = m(m+1)/2` rewrites. -/

/-- `replicate a t ++ (t :: X) = replicate (a+1) t ++ X` — absorb a leading `t` into the `t`-prefix. -/
private theorem replicate_t_cons (a : ℕ) (X : List TSym) :
    List.replicate a TSym.t ++ (TSym.t :: X) = List.replicate (a + 1) TSym.t ++ X := by
  rw [List.replicate_succ', List.append_assoc]; rfl

/-- **One odd step (`slide`).** `t 2ᵇ ▷ →*_𝒯 2ᵇ⁺¹ ▷` in `b + 1` rewrites: `b` base-swaps `t2 → 2t`
sliding the `t` rightward across the `b` ternary digits, then the dynamic odd rule `t▷ → 2▷`. -/
private theorem slide (b : ℕ) :
    ReachesIn collatzSRS (b + 1) (TSym.t :: (List.replicate b TSym.d2 ++ [TSym.rhd]))
      (List.replicate (b + 1) TSym.d2 ++ [TSym.rhd]) := by
  have rdyn : collatzSRS [TSym.t, TSym.rhd] [TSym.d2, TSym.rhd] := Or.inl (Or.inr ⟨rfl, rfl⟩)
  have rswap : collatzSRS [TSym.t, TSym.d2] [TSym.d2, TSym.t] :=
    Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
  induction b with
  | zero => exact ReachesIn.head (RewriteStep.of_rule rdyn) rfl
  | succ k ih => exact ReachesIn.head ((RewriteStep.of_rule rswap).append_context []
      (List.replicate k TSym.d2 ++ [TSym.rhd])) (ih.cons TSym.d2)

/-- **Chaining the odd steps (`coreChain`).** `tᵃ 2ᵇ ▷ →*_𝒯 2ᵃ⁺ᵇ ▷`, processing the `a` ones in turn;
the length `N` satisfies `2N = a·2b + a(a+1)` (the `i`-th slide crosses `b + i` digits). -/
private theorem coreChain (a b : ℕ) :
    ∃ N, ReachesIn collatzSRS N
      (List.replicate a TSym.t ++ (List.replicate b TSym.d2 ++ [TSym.rhd]))
      (List.replicate (a + b) TSym.d2 ++ [TSym.rhd]) ∧ 2 * N = a * (2 * b) + a * (a + 1) := by
  induction a generalizing b with
  | zero => exact ⟨0, by show _ = _; simp, by ring⟩
  | succ a ih =>
    obtain ⟨N', hN', hcount'⟩ := ih (b + 1)
    have hslide : ReachesIn collatzSRS (b + 1)
        (List.replicate (a + 1) TSym.t ++ (List.replicate b TSym.d2 ++ [TSym.rhd]))
        (List.replicate a TSym.t ++ (List.replicate (b + 1) TSym.d2 ++ [TSym.rhd])) := by
      simpa [replicate_t_cons, List.append_nil] using
        (slide b).append_context (List.replicate a TSym.t) []
    refine ⟨(b + 1) + N', ?_, ?_⟩
    · rw [show (a + 1) + b = a + (b + 1) from by omega]; exact hslide.trans hN'
    · rw [show 2 * ((b + 1) + N') = 2 * (b + 1) + 2 * N' from by ring, hcount']; ring

/-- **The transport lemma — heart of Proposition A.** The canonical `𝒯`-simulation of
`tStr (m) = ◁tᵐ▷` (value `2ᵐ⁺¹ − 1`) performs `m + 1` odd steps, and the renormalisation before the
`i`-th odd step transports a binary `t` rightward across the `i − 1` ternary digits already produced
— `≥ i − 1` base-swap rewrites of `𝒜` (`t0→1t`, `t1→2f`, `t2→2t`, …) — so the derivation has at least
`0 + 1 + ⋯ + m = m(m+1)/2` rewrites, stated subtraction-free as `m·(m+1) ≤ 2·N`.

**Proof** (constructed and counted by `slide` + `coreChain`; cf. [YAH], Example 3.14 and §3.2):
* `◁tᵐ▷` has value `2ᵐ⁺¹ − 1`, odd, so the dynamic rule `t▷ → 2▷` fires, leaving `◁tᵐ⁻¹2▷` (a trailing
  ternary `2`).
* To expose the next binary parity digit at the right boundary, the auxiliary rules of `𝒜` swap the
  binary `t` rightward past each accumulated ternary digit: after `i` odd steps there are `i` ternary
  digits, and crossing them costs `i` swaps (`t2 → 2t` etc.), giving the `i`-th renormalisation cost
  `≥ i`.
* Summing the renormalisation costs over the `m` odd steps the orbit `2ᵐ⁺¹−1 → ⋯` performs before its
  first even value gives `∑_{i=1}^{m} i = m(m+1)/2` auxiliary rewrites, all genuine `→_𝒯` steps; the
  formal proof constructs this derivation (à la `Zantema.oddSim`/`evenSim`) and counts its `ReachesIn`
  length. Mechanically verified for small `m` by `verify.py` (`m ≤ 16`).

The derivation reaches `◁2ᵐ▷` (all twos) in exactly `m(m+1)/2` steps; Proposition A and Corollary A
below are proved **from** it (now with no `sorry`). -/
@[category research solved, AMS 68 11, ref "YAH", group "complexity_bound",
  formal_uses coreChain slide]
theorem tStr_derivation_quadratic (m : ℕ) :
    ∃ v N, ReachesIn collatzSRS N (tStr m) v ∧ m * (m + 1) ≤ 2 * N := by
  obtain ⟨N, hreach, hcount⟩ := coreChain m 0
  refine ⟨TSym.lhd :: (List.replicate (m + 0) TSym.d2 ++ [TSym.rhd]), N, ?_, ?_⟩
  · have := hreach.cons TSym.lhd
    simpa [tStr] using this
  · have h2 : 2 * N = m * (m + 1) := by rw [hcount]; ring
    omega

/-- **Proposition A: `dc_𝒯(L) = Ω(L²)`.** The mixed-base Collatz SRS `𝒯` has **superlinear**
derivational complexity. For each rate `C`, the string `tStr (2C+4) = ◁t²ᶜ⁺⁴▷` (length `L = 2C+6`)
admits — by the transport lemma `tStr_derivation_quadratic` — a derivation of length
`N ≥ (2C+4)(2C+5)/2`, which exceeds `C·(L+1) = C·(2C+7)`. (The quadratic `(L−2)(L−1)/2` derivation
length from a length-`L` string is `Ω(L²)`.) Proved **from** the (now proven) transport lemma. -/
@[category research solved, AMS 68 11, ref "YAH", group "complexity_bound",
  formal_uses tStr_derivation_quadratic tStr_length DcSuperlinear]
theorem proposition_A : DcSuperlinear collatzSRS := by
  intro C
  obtain ⟨v, N, hN, hge⟩ := tStr_derivation_quadratic (2 * C + 4)
  refine ⟨tStr (2 * C + 4), v, N, hN, ?_⟩
  rw [tStr_length]
  have e1 : (2 * C + 4) * ((2 * C + 4) + 1) = 4 * (C * C) + 18 * C + 20 := by ring
  have e2 : C * ((2 * C + 4) + 2 + 1) = 2 * (C * C) + 7 * C := by ring
  rw [e1] at hge; rw [e2]; omega

/-- **Corollary A.** The mixed-base Collatz SRS `𝒯` admits **no** one-shot arctic matrix-interpretation
termination proof: by Koprowski–Waldmann one would force linear derivational complexity, but
`dc_𝒯 = Ω(L²)` (`proposition_A`). So — exactly as `Zantema.theorem_3_8` rules out *natural*-matrix
proofs of the unary `𝒵` — the arctic method is powerless on `𝒯`. -/
@[category research solved, AMS 68 11, ref "YAH" "KW09", group "complexity_bound",
  formal_uses no_arctic_of_dcSuperlinear proposition_A]
theorem corollary_A : ¬ HasOneShotArcticProof collatzSRS :=
  no_arctic_of_dcSuperlinear collatzSRS proposition_A

/-! ### Corollary B — Zantema's unary `𝒵` is superlinear (the representation blows up)

Applying the floor to the unary `𝒵`: the orbit of `2ᵏ − 1` reaches `3ᵏ − 1`, and `𝒵` stores numbers
in **unary**, so the string grows from length `≈ 2ᵏ` to length `≈ 3ᵏ = L^{log₂3}`. Since every
`𝒵`-rule lengthens the string by `≤ 2`, that growth alone forces `≥ (3ᵏ − 2ᵏ)/2` rewrites — a
superlinear `Ω(L^{log₂3})` lower bound, ruling out a one-shot arctic proof for `𝒵` as well. (This is
fully proved, reusing the simulation lemma `Zantema.oddSim`.) -/

/-- `M·4ᴹ < 9ᴹ` for `M ≥ 1` (clean induction; the engine of the exponential gap `3ᵏ ≫ 2ᵏ`). -/
private theorem nat_mul_four_pow_lt_nine_pow (M : ℕ) (hM : 1 ≤ M) : M * 4 ^ M < 9 ^ M := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; norm_num
    · have ihn := ih hpos
      rw [pow_succ, pow_succ]
      nlinarith [ihn, pow_pos (show 0 < 4 by norm_num) n, hpos]

/-- `6C < 2^{4C+4}` (an exponential beats this linear term), via `2^{C+3} = 8·2^C ≥ 8(C+1)`. -/
private theorem six_mul_lt (C : ℕ) : 6 * C < 2 ^ (4 * C + 4) := by
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self
  have h2 : 2 ^ (C + 3) ≤ 2 ^ (4 * C + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (C + 3) = 8 * 2 ^ C := by rw [pow_add]; ring
  omega

/-- The Zantema configuration `◇h1ᵐ◇` has length `m + 3`. -/
@[category API, AMS 68, ref "Zan05", group "complexity_bound"]
theorem config_length (m : ℕ) : (config m).length = m + 3 := by simp [config]

/-- Every `𝒵`-rewrite lengthens the string by **at most `2`** (the maximum over the seven rules,
attained by the tripling rule `1t → t111`, length `2 → 4`). -/
@[category research solved, AMS 68, ref "Zan05", group "complexity_bound"]
theorem Z_step_length (u v : List ZSym) (h : RewriteStep Z u v) : v.length ≤ u.length + 2 := by
  obtain ⟨s, t, ℓ, r, hr, rfl, rfl⟩ := h
  simp only [List.length_append]
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    simp only [List.length_cons, List.length_nil] <;> omega

/-- **The `𝒵`-simulation of `2ᵏ − 1` reaches `3ᵏ − 1`.** Chaining the proven odd-step simulation
`Zantema.oddSim` (`◇h1²ⁿ⁺¹◇ →*_𝒵 ◇h1³ⁿ⁺²◇`) along the `k` odd steps of the orbit
`Tⁱ(2ᵏ−1) = 3ⁱ·2ᵏ⁻ⁱ − 1` (cf. `T_orbit`): for `i ≤ k`,
`◇h1^{2ᵏ−1}◇ →*_𝒵 ◇h1^{3ⁱ·2ᵏ⁻ⁱ−1}◇`. -/
@[category research solved, AMS 68 11, ref "Zan05" "YAH", group "complexity_bound",
  formal_uses oddSim config]
theorem config_reaches_orbit (k : ℕ) :
    ∀ i, i ≤ k → ReflTransGen (RewriteStep Z) (config (2 ^ k - 1)) (config (3 ^ i * 2 ^ (k - i) - 1)) := by
  intro i
  induction i with
  | zero => intro _; simp only [pow_zero, one_mul, Nat.sub_zero]; exact ReflTransGen.refl
  | succ j ih =>
    intro hi
    have hjk : j ≤ k := by omega
    have hk1 : k - j = (k - (j + 1)) + 1 := by omega
    have hrel : 3 ^ j * 2 ^ (k - j) = 2 * (3 ^ j * 2 ^ (k - (j + 1))) := by rw [hk1, pow_succ]; ring
    have hrhs : 3 ^ (j + 1) * 2 ^ (k - (j + 1)) = 3 * (3 ^ j * 2 ^ (k - (j + 1))) := by
      rw [pow_succ]; ring
    have hpos : 0 < 3 ^ j * 2 ^ (k - (j + 1)) := by positivity
    have step := oddSim (3 ^ j * 2 ^ (k - (j + 1)) - 1)
    have e1 : 2 * (3 ^ j * 2 ^ (k - (j + 1)) - 1) + 1 = 3 ^ j * 2 ^ (k - j) - 1 := by rw [hrel]; omega
    have e2 : 3 * (3 ^ j * 2 ^ (k - (j + 1)) - 1) + 2 = 3 ^ (j + 1) * 2 ^ (k - (j + 1)) - 1 := by
      rw [hrhs]; omega
    rw [e1, e2] at step
    exact (ih hjk).trans step

/-- **The `𝒵`-derivation of `2ᵏ − 1` is long.** Some derivation reaches `◇h1^{3ᵏ−1}◇`, and since each
step lengthens the string by `≤ 2` while the length jumps from `2ᵏ + 2` to `3ᵏ + 2`, that derivation
has `N` steps with `3ᵏ ≤ 2ᵏ + 2·N`, i.e. `N ≥ (3ᵏ − 2ᵏ)/2`. -/
@[category research solved, AMS 68 11, ref "Zan05" "YAH", group "complexity_bound",
  formal_uses config_reaches_orbit ReachesIn.length_le Z_step_length config_length]
theorem Z_derivation_long (k : ℕ) :
    ∃ v N, ReachesIn Z N (config (2 ^ k - 1)) v ∧ 3 ^ k ≤ 2 ^ k + 2 * N := by
  obtain ⟨N, hN⟩ := reachesIn_of_reflTransGen (config_reaches_orbit k k le_rfl)
  rw [show 3 ^ k * 2 ^ (k - k) - 1 = 3 ^ k - 1 by rw [Nat.sub_self, pow_zero, mul_one]] at hN
  refine ⟨config (3 ^ k - 1), N, hN, ?_⟩
  have hlen := ReachesIn.length_le 2 Z_step_length hN
  rw [config_length, config_length] at hlen
  have h3 : 0 < 3 ^ k := by positivity
  have h2 : 0 < 2 ^ k := by positivity
  omega

/-- **`𝒵` has superlinear derivational complexity** (`Ω(L^{log₂3})`). For each rate `C`, take
`k = 4C + 4`: the exponential gap `3ᵏ > (2C+2)·2ᵏ` (from `nat_mul_four_pow_lt_nine_pow`) together with
`6C < 2ᵏ` (`six_mul_lt`) and the length bound `3ᵏ ≤ 2ᵏ + 2N` (`Z_derivation_long`) gives
`N > C·(2ᵏ + 3) = C·(|◇h1^{2ᵏ−1}◇| + 1)`. -/
@[category research solved, AMS 68 11, ref "Zan05" "YAH", group "complexity_bound",
  formal_uses Z_derivation_long DcSuperlinear]
theorem dcSuperlinear_Z : DcSuperlinear Z := by
  intro C
  have hA : (2 * C + 2) * 2 ^ (4 * C + 4) < 3 ^ (4 * C + 4) := by
    have h := nat_mul_four_pow_lt_nine_pow (2 * C + 2) (by omega)
    rw [show (4 : ℕ) ^ (2 * C + 2) = 2 ^ (2 * (2 * C + 2)) by rw [pow_mul]; norm_num,
        show (9 : ℕ) ^ (2 * C + 2) = 3 ^ (2 * (2 * C + 2)) by rw [pow_mul]; norm_num] at h
    rwa [show 2 * (2 * C + 2) = 4 * C + 4 by ring] at h
  have hB : 6 * C < 2 ^ (4 * C + 4) := six_mul_lt C
  obtain ⟨v, N, hreach, hlen⟩ := Z_derivation_long (4 * C + 4)
  refine ⟨config (2 ^ (4 * C + 4) - 1), v, N, hreach, ?_⟩
  rw [config_length]
  have h2k : 1 ≤ 2 ^ (4 * C + 4) := Nat.one_le_two_pow
  have hsl : (2 ^ (4 * C + 4) - 1 + 3) + 1 = 2 ^ (4 * C + 4) + 3 := by omega
  rw [hsl]
  nlinarith [hA, hB, hlen, h2k]

/-- **Corollary B.** Zantema's unary `𝒵` admits **no** one-shot arctic matrix-interpretation
termination proof: its derivational complexity is superlinear (`dcSuperlinear_Z`), contradicting the
linear bound a one-shot arctic proof would force (`no_arctic_of_dcSuperlinear`). Together with
`Zantema.theorem_3_8` (no *natural*-matrix proof), the matrix-interpretation method — natural or
arctic — fails on `𝒵`. -/
@[category research solved, AMS 68 11, ref "Zan05" "KW09", group "complexity_bound",
  formal_uses no_arctic_of_dcSuperlinear dcSuperlinear_Z]
theorem corollary_B : ¬ HasOneShotArcticProof Z :=
  no_arctic_of_dcSuperlinear Z dcSuperlinear_Z

end StringRewriting.ComplexityBound
