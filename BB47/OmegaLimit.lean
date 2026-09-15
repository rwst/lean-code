/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Degrees
import BB47.PeriodicOrbits
import ForMathlib.Dynamics.SymbolicDynamics.Rauzy

/-!
# `Ω(u)` as a subshift: `p_∞` is a factor complexity, and [M3, Lem. 3.3] in full

This is the corpus-facing face of `ForMathlib/Dynamics/SymbolicDynamics/`.  It states, in the
vocabulary of Problem 10.47, the two results that `BB47/lean-inventory.md` used to list as
missing because Mathlib's subshift file is a skeleton:

* **[M1M2, Prop. 2.4]** — `p_∞(n, u)` is the factor complexity of a *subshift*, namely of the
  `ω`-limit set `Ω(u)`, whose language at level `n` is `BB47.recFactorSet u n` on the nose.
* **[M3, Lem. 3.3]** — under the standing hypothesis `p_∞(n, u) = n + 1` for all `n`, the set
  `Ω(u)` contains **at most one periodic orbit**.

Neither is proved here.  `Ω(u)` is `SymbolicDynamics.FullShift.omegaLimitSubshift u`, built in
`ForMathlib` from the language `recurrentLanguage u`, and `BB47.recFactorSet u = recurrentLanguage
u` is `rfl`; so the statements below are the `ForMathlib` theorems read through a definitional
identity, and are one line each.  That is the whole point of WP8 of `plans/plan-subshift.html`:
the mathematics lives at the level of generality where it is true, and this root records what it
says about 10.47.

## The two halves of [M3, Lem. 3.3]

The note's proof of Lemma 3.3 has a word-combinatorial half and a graph-theoretic half.

* The word half is Fine and Wilf's theorem, `BB47/PeriodicOrbits.lean` for one-sided words and
  `SymbolicDynamics.FullShift.orbit_eq_or_disjoint_language` for two-sided ones: two periodic
  points either share an orbit or their orbits have **no** common block of length `p + q`.
* The graph half is the counting lemma.  Under `p_∞(n+1) = p_∞(n) + 1` there is at most one
  right-special block of length `p + q` (`BB47.exists_unique_rightSpecial`), so it misses one of
  the two disjoint orbit languages; that orbit language is then closed under out-edges,
  non-empty and proper, which `BB47.not_properOutClosed` forbids.

**The shape lemma [M3, Lem. 3.2] is not needed.**  The note argues from the full shape of
`G_n(Ω)` — `n + 1` vertices, `n + 2` edges, exactly two simple cycles, which meet.  Only the
degree half of that is used above, and `BB47.rightSpecial_of_minimal` is the form in which the
hypothesis of 10.47 supplies it.

## Main results

* `BB47.language_omegaLimitSubshift_eq_recFactorSet` — `𝓛ₙ(Ω(u)) = recFactorSet u n`.
* `BB47.pInf_eq_complexity` — **[M1M2, Prop. 2.4]**: `p_∞(n, u) = p(n, Ω(u))`.
* `BB47.coe_omegaLimitSubshift_eq_omegaLimit` — and `Ω(u)` really is an `ω`-limit set: the carrier
  is Mathlib's `omegaLimit atTop (σ ·) {x}` for any two-sided extension `x` of `u`, independently
  of the extension chosen.
* `BB47.isStronglyConnected_omegaLimitSubshift` — [M1M2, Prop. 3.2] at subshift level.
* `BB47.mem_omegaLimitSubshift_iff_forall_block_mem` — `Ω(u)` is the inverse limit of its Rauzy
  graphs, which is the description `plans/plan-1047.html` §2.2 takes as a definition.
* `BB47.orbit_eq_of_pInf_eq`, `BB47.orbitClosure_eq_of_pInf_eq` — **[M3, Lem. 3.3]**.
* `BB47.orbit_eq_of_pInf_succ_le` — the same with the hypothesis used only at the single level
  `p + q`, which is weaker than the note's.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, CUP 2012 — Problem 10.47, p. 221.
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — §2.2–2.3.
* [FW65] N. J. Fine, H. S. Wilf, Proc. Amer. Math. Soc. **16** (1965), 109–114.
* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — Prop. 2.4, Props. 3.2–3.3.
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Lem. 3.2 (shape, not needed), Lem. 3.3.
-/

namespace BB47

open ForMathlib.SubwordComplexity SymbolicDynamics.FullShift

/-! ## Re-exports

`Ω(u)`, its points and its periodic orbits are not redefined here; these are the `ForMathlib`
constants under their `BB47` names. -/

export SymbolicDynamics.FullShift (omegaLimitSubshift IsTwoSidedExtension IsPeriodicPoint orbit
  orbitClosure block mem_omegaLimitSubshift coe_omegaLimitSubshift_eq_omegaLimit
  omegaLimit_eq_of_isTwoSidedExtension exists_isTwoSidedExtension omegaLimitSubshift_tail
  isStronglyConnected_omegaLimitSubshift)

variable {α : Type*} [TopologicalSpace α] [DiscreteTopology α] [Finite α]

/-! ## [M1M2, Prop. 2.4]: `p_∞` is the complexity of a subshift -/

/-- The vertex set of `G'_n(u)` is the language of `Ω(u)` at level `n`, on the nose. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem language_omegaLimitSubshift_eq_recFactorSet (u : ℕ → α) (n : ℕ) :
    (omegaLimitSubshift u).language n = recFactorSet u n :=
  language_omegaLimitSubshift u n

/-- **[M1M2, Prop. 2.4]: `p_∞(n, u)` is a factor complexity.**  The function of Problem 10.47 is
the factor complexity of the subshift `Ω(u)`, so every general theorem about subshift complexity —
the Morse–Hedlund floor, submultiplicativity, the plateau theorem — applies to it. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem pInf_eq_complexity (u : ℕ → α) (n : ℕ) :
    pInf u n = (omegaLimitSubshift u).complexity n :=
  (complexity_omegaLimitSubshift u n).symm

/-- `Ω(u)` is non-empty. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem omegaLimitSubshift_nonempty (u : ℕ → α) :
    ((omegaLimitSubshift u : Set (ℤ → α))).Nonempty :=
  SymbolicDynamics.FullShift.omegaLimitSubshift_nonempty u

/-- **`Ω(u)` is the inverse limit of its reduced Rauzy graphs**: a bisequence belongs to `Ω(u)`
exactly when every one of its blocks is recurrent in `u`.  This is the description that
`plans/plan-1047.html` §2.2 takes as the definition of `Ω(u)`. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem mem_omegaLimitSubshift_iff_forall_block_mem (u : ℕ → α) (x : ℤ → α) :
    x ∈ omegaLimitSubshift u ↔ ∀ n (i : ℤ), Recurrent u n (block x n i) :=
  Subshift.mem_iff_forall_block_mem _ x |>.trans
    (by simp only [language_omegaLimitSubshift_eq_recFactorSet]; rfl)

/-! ## [M3, Lem. 3.3]: at most one periodic orbit -/

/-- **[M3, Lem. 3.3].**  If the eventual complexity of `u` grows by at most one at the single
level `p + q`, then two periodic points of `Ω(u)` of periods `p` and `q` lie on the same orbit.

This is weaker in its hypothesis than the note, which assumes `p_∞(n) = n + 1` at every level and
takes `p` and `q` to be the *least* periods; neither is needed. -/
@[category research solved, AMS 11 37 68, ref "FW65" "BKK26", group "bugeaud_10_47"]
theorem orbit_eq_of_pInf_succ_le {u : ℕ → α} {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hx : x ∈ omegaLimitSubshift u) (hy : y ∈ omegaLimitSubshift u)
    (hxp : IsPeriodicPoint x p) (hyq : IsPeriodicPoint y q)
    (hcount : pInf u (p + q + 1) ≤ pInf u (p + q) + 1) : orbit x = orbit y :=
  orbit_eq_of_pRecurrent hp hq hx hy hxp hyq hcount

/-- **[M3, Lem. 3.3] under the standing hypothesis (H).**  If `p_∞(n, u) = n + 1` for every `n`,
the `ω`-limit set of `u` contains **at most one periodic orbit**.

Together with `BB47.not_properOutClosed` — which removes the Coven–Hedlund non-Sturmian branch —
this is the combinatorial input to Theorem B of `BB47/M3.tex`. -/
@[category research solved, AMS 11 37 68, ref "FW65" "BKK26", group "bugeaud_10_47"]
theorem orbit_eq_of_pInf_eq {u : ℕ → α} (hu : ∀ n, pInf u n = n + 1) {x y : ℤ → α} {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hx : x ∈ omegaLimitSubshift u) (hy : y ∈ omegaLimitSubshift u)
    (hxp : IsPeriodicPoint x p) (hyq : IsPeriodicPoint y q) : orbit x = orbit y :=
  orbit_eq_of_pRecurrent_eq hu hp hq hx hy hxp hyq

/-- The same conclusion read as an equality of subshifts: the two periodic points generate the
same minimal subsystem of `Ω(u)`. -/
@[category research solved, AMS 11 37 68, ref "FW65" "BKK26", group "bugeaud_10_47"]
theorem orbitClosure_eq_of_pInf_eq {u : ℕ → α} (hu : ∀ n, pInf u n = n + 1) {x y : ℤ → α}
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hx : x ∈ omegaLimitSubshift u)
    (hy : y ∈ omegaLimitSubshift u) (hxp : IsPeriodicPoint x p) (hyq : IsPeriodicPoint y q) :
    orbitClosure x = orbitClosure y := by
  apply SetLike.coe_injective
  rw [coe_orbitClosure_eq_closure_orbit, coe_orbitClosure_eq_closure_orbit,
    orbit_eq_of_pInf_eq hu hp hq hx hy hxp hyq]

end BB47
