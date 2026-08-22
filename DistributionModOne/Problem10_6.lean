/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.MetricSpace.HausdorffDimension
import ForMathlib.NumberTheory.Lacunary
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One

*References:*
  - [Bos83] Boshernitzan, Michael D. "Homogeneously distributed sequences and Poincaré sequences
    of integers of sublacunary growth." Monatshefte für Mathematik 96 (1983): 173-181.
    [Theorem 1.5 answers Problem 10.6 under every subexponential growth reading, in 1983 and in
    the stronger form of uniform distribution; see `problem_10_6_variant_2` below.]
  - [Bos94] Boshernitzan, Michael D. "Density modulo 1 of dilations of sublacunary sequences."
    Advances in Mathematics 108.1 (1994): 104-117.
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Fur67] Furstenberg, H. "Disjointness in ergodic theory, minimal sets, and a problem
    in diophantine approximation". Math. Systems Theory 1, 1–49 (1967).
  - [Kat16] Katz, Asaf. "Generalizations of Furstenberg's Diophantine result."
    arXiv:1607.00670 (2016).
  - [Mat80] de Mathan, Bernard. "Numbers contravening a condition in density modulo 1."
    Acta Mathematica Hungarica 36.3-4 (1980): 237-241.
  - [Khi26] Khintchine, A. "Einige Sätze über Kettenbrüche, mit Anwendungen auf die Theorie der
    Diophantischen Approximationen." Math. Ann. 92 (1926): 115-125. [Hilfssatz III: priority for
    the *existence* half of `pollington_de_mathan`, with an explicit constant; it proves no
    dimension statement.]
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.

Several of the results below are studied further in the `BB6/` corpus root, which backs a short
note on Problem 10.6 (`plans/plan-BB6-paper.html`).  Cross-references to it are given in the
docstrings; `BB6` imports this file, so the pointers cannot be made into Lean dependencies here.
-/

namespace Bugeaud06

open Filter

/-! ## Informal-result registry

General results the (published) proofs below rely on that are **not** in Mathlib,
recorded at the level of "what notion the proof needs". Registry-keyed so the
`informal_uses` edges share canonical nodes. -/

informal_result "hausdorff-dimension-cantor-construction"
  latex "Building sets of prescribed (here full) Hausdorff dimension by nested-interval / Cantor schemes plus the mass distribution principle (Frostman): a lacunary sequence leaves room at each scale to construct a Cantor set of dimension approaching 1 on which density modulo one fails."
  refs "Pol79" "Mat80"

informal_result "furstenberg-x2x3-rigidity"
  latex "Furstenberg's theorem on the rigidity of the action of two multiplicatively independent integers on the circle: the only closed infinite invariant subset is the whole circle, so every irrational orbit under the semigroup (2^m 3^n) is dense modulo one."
  refs "Fur67"

informal_result "sublacunary-density-mod-one"
  latex "Boshernitzan's metric/dimension argument: a sublacunary growth condition (consecutive ratios tending to 1) forces density modulo one for every real number outside an exceptional set of Hausdorff dimension zero."
  refs "Bos94"

informal_result "katz-p-adic-positive-entropy-construction"
  latex "Katz's affirmative answer to Bugeaud's question (building on Meiri's and Lindenstrauss' theory of $q$-Host sequences and the Bourgain--Lindenstrauss--Michel--Venkatesh effective $\\times a, \\times b$ result): a sequence admitting a smooth $p$-adic interpolation with only finitely many critical points inside the unit disc supports a $T_p$-invariant, $T_p$-ergodic Borel measure of positive entropy; combined with Host's and Lindenstrauss' equidistribution and Boshernitzan's non-lacunary density this yields a single, arbitrarily sparse integer sequence $\\{a_n\\}$ with $|\\{a_n\\} \\cap [1,N]| \\le r(N)\\log N$ that is dense modulo one for every irrational $\\xi$. Applied to $\\{2^n 3^{3^{3^{p_1(m)}}} 3^{3^{3^{p_2(k)}}}\\}$ this answers Problem 10.6."
  refs "Kat16"

/-- The **Pollington–de Mathan theorem** [Pol79][Mat80]. For every lacunary sequence
$(m_n)_{n \ge 1}$ of positive integers, the set of real numbers $\xi$ for which
$(\{\xi m_n\})_{n \ge 1}$ is *not* dense modulo one has full Hausdorff dimension.

Two points of fidelity.

*Priority.* The **existence** half — that some irrational $\xi$ has $(\{\xi m_n\})$ non-dense —
is already [Khi26, Hilfssatz III], with an explicit constant polynomial in $\varepsilon$.  What
[Pol79] and [Mat80] add is the *dimension* statement, which is what is recorded here, so the
`ref`/`solved_by` keys below are correct as they stand.

*Hypothesis shape.* [Pol79], [Mat80] and [Khi26] all assume the ratio bound $m_{n+1}/m_n \ge c$
for **every** $n$, whereas `ForMathlib.IsLacunary` — used here — is the eventual form.  The
passage is free, and it is proved rather than assumed: `BB6.dimH_exceptional_eq_one_of_always`
derives the eventual-hypothesis statement from the always-hypothesis one, by applying the latter
to a tail and pushing the exceptional set forward along `BB6.exceptional_tail_subset` (dropping an
initial segment removes finitely many points from the orbit, and the circle has no isolated
points).  So this axiom records exactly what the literature proves. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Pol79" "Mat80", solved_by "Pollington" 1979, solved_by "de Mathan" 1980,
  informal_uses "hausdorff-dimension-cantor-construction"]
axiom pollington_de_mathan (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1

/-- The Pollington–de Mathan theorem implies that a lacunary sequence cannot answer
Problem 10.6. -/
@[category test, AMS 11, group "bugeaud_10_6",
  formal_uses pollington_de_mathan]
theorem problem_lacunary_not_dense_of_pollington_de_mathan
    (h : type_of% pollington_de_mathan) :
    ∃ m : ℕ → ℕ, (∀ n, 0 < m n) ∧ IsLacunary m ∧
      ¬ ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  set m₀ : ℕ → ℕ := fun n => 2 ^ n with hm₀
  have hpos : ∀ n, 0 < m₀ n := by intro n; rw [hm₀]; positivity
  have hlac : IsLacunary m₀ := by
    refine ⟨3 / 2, by norm_num, .of_forall fun k => ?_⟩
    simp only [hm₀]
    push_cast
    rw [pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
  refine ⟨m₀, hpos, hlac, fun hd => ?_⟩
  have hdim := h m₀ hpos hlac
  have hcount :
      {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * m₀ n) : AddCircle (1 : ℝ)))}.Countable :=
    Set.Countable.mono (fun ξ hξ => by by_contra hξr; exact hξ (hd ξ hξr))
      (Set.countable_range _)
  rw [hcount.dimH_zero] at hdim
  exact zero_ne_one hdim

/-- **Furstenberg's theorem** [Fur67] (the $\times 2, \times 3$ case). For every irrational
number $\xi$, the two-parameter family $(\{\xi \, 2^m 3^n\})_{m, n \ge 1}$ is dense modulo
one. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Fur67", solved_by "Furstenberg" 1967,
  informal_uses "furstenberg-x2x3-rigidity"]
axiom furstenberg_two_three (ξ : ℝ) (hξ : Irrational ξ) :
    Dense {x : AddCircle (1 : ℝ) |
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ x = ↑(ξ * (2 ^ m * 3 ^ n : ℕ))}

/-- **Boshernitzan's theorem** [Bos94]. Given a real sublacunary sequence $r$, the set of
real numbers $\xi$ for which $(\{\xi r_n\})_{n \ge 1}$ is *not* dense modulo one has
Hausdorff dimension zero. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Bos94", solved_by "Boshernitzan" 1994,
  informal_uses "sublacunary-density-mod-one"]
axiom boshernitzan (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hunb : ¬ BddAbove (Set.range r))
    (hsub : Tendsto (fun n => r (n + 1) / r n) atTop (nhds 1)) :
    dimH {ξ : ℝ | ¬ Dense (Set.range fun n => (↑(ξ * r n) : AddCircle (1 : ℝ)))} = 0

/-- The sequence defined by $m_0 = 2$ and $m_{n+1} = \lceil m_n (1 + 1/\log n) \rceil$. -/
@[category API, AMS 11, group "bugeaud_10_6"]
noncomputable def mSeq : ℕ → ℕ
  | 0 => 2
  | (n + 1) => ⌈(mSeq n : ℝ) * (1 + 1 / Real.log n)⌉₊

@[category API, AMS 11, group "bugeaud_10_6"]
def IsGenuinelySublacunary (m : ℕ → ℕ) : Prop :=
  ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, (1 + c / Real.log n) ≤ (m (n+1) : ℝ) / m n

/-- The sequence `mSeq`, given by $m_{n+1} = \lceil m_n (1 + 1/\log n) \rceil$, is
genuinely sublacunary: taking $c = 1$, we have $m_{n+1}/m_n \ge 1 + 1/\log n$ because
$\lceil m_n (1 + 1/\log n) \rceil \ge m_n (1 + 1/\log n)$. -/
@[category test, AMS 11, group "bugeaud_10_6"]
lemma example_isGenuineSublacunary : IsGenuinelySublacunary mSeq := by
  -- Every term of `mSeq` is positive.
  have mSeq_pos : ∀ n, 0 < mSeq n := by
    intro n
    induction n with
    | zero => simp [mSeq]
    | succ k ih =>
      simp only [mSeq, Nat.ceil_pos]
      exact mul_pos (by exact_mod_cast ih) (by positivity)
  refine ⟨1, one_pos, .of_forall fun n => ?_⟩
  have hpos : (0 : ℝ) < (mSeq n : ℝ) := by exact_mod_cast mSeq_pos n
  rw [le_div_iff₀ hpos]
  simp only [mSeq]
  rw [mul_comm]
  exact Nat.le_ceil _

@[category API, AMS 11, group "bugeaud_10_6"]
def HasIntermediateGrowth (α : ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, Real.exp ((n : ℝ) ^ α) ≤ m n

/-- `mSeq` has intermediate (subexponential but super-polynomial) growth: for every
`0 < α < 1` its terms eventually dominate $\exp(n^\alpha)$.

**The `sorry` is not a gap in the mathematics.** This is the special case at `m = mSeq` of
`BB6.hasIntermediateGrowth_of_r3` — genuine sublacunarity implies intermediate growth at every
`α < 1`, via the estimate `log mₙ ≥ (c/4)·n/log n` (`BB6.log_lower_of_r3`) — applied to
`example_isGenuineSublacunary` just above.  Both are proved, sorry-free and `std3`, in
`BB6/Readings.lean`, so the statement here is a theorem; it cannot be *discharged in this file*
only because `BB6` imports this file and Lean forbids the resulting import cycle.  Closing it in
place would mean either duplicating `BB6/Readings.lean` here or moving `IsGenuinelySublacunary`
and `HasIntermediateGrowth` out of this file, and neither is worth doing for a `test`-category
example. -/
@[category test, AMS 11, group "bugeaud_10_6"]
lemma example_hasIntermediateGrowth (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    HasIntermediateGrowth α mSeq := by
  sorry

/-! ## Katz's construction

Katz [Kat16] answers Problem 10.6 in the affirmative. The heart of his construction is a
positive-entropy $T_p$-invariant measure obtained from a smooth $p$-adic interpolation
(Meiri, Lindenstrauss) together with Boshernitzan's non-lacunary density; the resulting
*single* sequence can be made as sparse as one likes. We fix Katz's explicit instance
(Corollary 4.9 with the identity polynomials $p_1 = p_2 = \mathrm{id}$) and take its
increasing enumeration.

**What [Kat16] actually adds, and what it does not.** The *growth* reading of Problem 10.6 — the
one recorded below as `problem_10_6_variant_2` — was already answered by [Bos83, Thm 1.5] in 1983,
and in the stronger form of uniform distribution rather than mere density; see that theorem's
docstring. Katz's own contributions are elsewhere:

* **sparsity.** [Kat16, Cor. 4.10] gives a universally densifying sequence with counting function
  $\le r(N)\log N$ for any prescribed $r \ge 1$. This is below the $\log N$ floor that any
  sublacunary sequence must respect, so it is unreachable by [Bos83] or by any sublacunary
  construction.
* **multiplicative structure.** The sequences are $\{2^n 3^e : e \in E\}$, so their gaps are
  governed by the Diophantine behaviour of $\log_2 3$ rather than by a growth condition.
* **the ratio-floor reading, conditionally.** Under a Diophantine hypothesis on $E - E$ the
  increasing enumeration of Katz's set is genuinely sublacunary, which resolves
  `problem_10_6_variant_1`; see `BB6.problem_10_6_variant_1_of_gap`.

The general family, with the tower height and both polynomials as parameters, is
`BB6.katzExponents`/`BB6.twoThreeSet`; `BB6.twoThreeSet_katzExponents` identifies `katzSet`
below as the instance with identity polynomials. Note that the exponent tower there has height
**two**, not three: the outermost `3` in `3 ^ (3 ^ (3 ^ m))` is the `3^e` of the multiplicative
set, not a level of the tower. -/

/-- Katz's explicit sparse generating set (Corollary 4.9, identity polynomials): the
three-parameter multiplicative family
$\{2^n\, 3^{3^{3^m}}\, 3^{3^{3^k}} : n, m, k \in \mathbb{N}\}$. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def katzSet : Set ℕ := {N | ∃ n m k : ℕ, N = 2 ^ n * 3 ^ (3 ^ (3 ^ m)) * 3 ^ (3 ^ (3 ^ k))}

/-- `katzSet` is infinite: it already contains the geometric progression
$2^n \cdot 3^{27} \cdot 3^{27}$ (taking $m = k = 0$). -/
@[category API, AMS 11, group "bugeaud_10_6"]
lemma katzSet_infinite : katzSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 2 ^ n * 3 ^ (3 ^ (3 ^ 0)) * 3 ^ (3 ^ (3 ^ 0))) ?_ ?_
  · intro a b hab
    simp only [mul_assoc] at hab
    exact Nat.pow_right_injective (by norm_num)
      (Nat.eq_of_mul_eq_mul_right (by norm_num) hab)
  · intro a
    exact ⟨a, 0, 0, by ring⟩

/-- **The Katz sequence**: the increasing enumeration of `katzSet`. This is the single,
very rapidly increasing sequence of positive integers that resolves Problem 10.6. -/
@[category API, AMS 11, group "bugeaud_10_6"]
noncomputable def katzSeq : ℕ → ℕ := Nat.nth (· ∈ katzSet)

/-- `katzSeq` is strictly increasing, being the enumeration of an infinite set of naturals. -/
@[category API, AMS 11, group "bugeaud_10_6"]
lemma katzSeq_strictMono : StrictMono katzSeq :=
  Nat.nth_strictMono katzSet_infinite

/-- **Katz's theorem** [Kat16] (Corollary 4.9/4.10, identity polynomials). The single
sequence `katzSeq` is *universally densifying*: for every irrational $\xi$ the orbit
$(\{\xi \, \mathrm{katzSeq}(n)\})_{n \ge 1}$ is dense modulo one. This is Katz's
affirmative answer to Bugeaud's Problem 10.6. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Kat16", solved_by "Katz" 2016,
  informal_uses "katz-p-adic-positive-entropy-construction"]
axiom katz_universal_density (ξ : ℝ) (hξ : Irrational ξ) :
    Dense (Set.range fun n => (↑(ξ * katzSeq n) : AddCircle (1 : ℝ)))

/-- Sparsity of the Katz sequence [Kat16, Corollary 4.10]: its counting function obeys
$|\{\mathrm{katzSeq}\} \cap [1,N]| \le \log N \, (\log\log\log N)^2$, so $\mathrm{katzSeq}(n)$
eventually dominates $\exp(n^{\alpha})$ for some $0 < \alpha < 1$. Hence the sequence has
intermediate (super-polynomial but sub-exponential) growth — it is genuinely "very rapidly
increasing". -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Kat16", solved_by "Katz" 2016,
  informal_uses "katz-p-adic-positive-entropy-construction"]
axiom katzSeq_intermediateGrowth :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ HasIntermediateGrowth α katzSeq

/--
Problem 10.6. Find a very rapidly increasing sequence $(m_n)_{n \ge 1}$ of positive
integers such that $(\{\xi m_n\})_{n \ge 1}$ is dense modulo one for every irrational
number $\xi$. Note: Furstenberg's $2^m3^n$ is sublacunary but requires two parameters.

This variant additionally demands *genuine sublacunarity*
($m_{n+1}/m_n \ge 1 + c/\log n$). Katz's construction (see `problem_10_6_variant_2`)
settles the density requirement, but its multiplicative enumeration `katzSeq` is not
known to meet this pointwise ratio lower bound, so this stronger variant is left open.

**Reduced to one Diophantine statement.** `BB6.problem_10_6_variant_1_of_gap` proves exactly this
statement from the single hypothesis that the exponent set $E$ of Katz's construction satisfies
$\lVert (e-e')\log_2 3 \rVert \ge c/\log\max(e,e')$ for distinct $e, e' \in E$
(`BB6.KatzGapHypothesis`), drawing no axiom beyond `katz_universal_density`. Two further facts
frame how much room is left. The hypothesis cannot be weakened to a *constant* floor — that fails
for every infinite $E$ by pigeonhole (`BB6.not_const_gap_katzExponents`). And it is far out of
reach of current transcendence methods: the best unconditional bound at $(2,3)$ is
$\lVert d\log_2 3\rVert \ge 1.43 \cdot 10^{-4} d^{-13.3}$ [Rhi87], where a decay in
$1/\log d$ is what would be needed. Separately, `BB6.not_isGenuinelySublacunary_furstenbergSeq`
shows the *other* known universally densifying construction, Furstenberg's $\{2^a 3^b\}$, fails
this variant outright. -/
@[category research open, AMS 11, group "bugeaud_10_6",
  ref "Bug12", conjectured_by "Bugeaud" 2012]
theorem problem_10_6_variant_1 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    IsGenuinelySublacunary m ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

/-- Problem 10.6, intermediate-growth variant — **first resolved by Boshernitzan [Bos83,
Thm 1.5]**, and again by Katz [Kat16]. The statement asks only for a strictly increasing sequence
of intermediate (super-polynomial, sub-exponential) growth that is dense modulo one for every
irrational $\xi$; it imposes no sparsity and no ratio condition.

**Priority.** [Bos83, Thm 1.5] answers it, 33 years before [Kat16] and in the stronger form of
*uniform distribution* rather than density: the single sequence $\{\exp(7k/\ln\ln\ln k)\}$
already does it, and the theorem covers every subexponential growth rate. [Kat16]'s contribution
to Problem 10.6 lies in the sparsity and multiplicative-structure directions instead — see the
section docstring above. The `solved_by` keys record both, Boshernitzan first.

**The recorded proof is not the cheapest one.** The witness below is `katzSeq`, so this
declaration depends on the cited axioms `katzSeq_intermediateGrowth` and
`katz_universal_density`. It need not: `BB6.variant_2_of_runs` proves this statement *verbatim*
(it is checked against `type_of% problem_10_6_variant_2`) and is `std3`, with no cited axiom at
all, from an elementary construction — a sequence containing arbitrarily long runs of consecutive
integers is universally densifying (`BB6.universallyDensifying_of_hasLongRuns`), and the runs can
be placed as sparsely as one likes. The proof cannot be substituted here because `BB6` imports
this file. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Bos83" "Kat16", conjectured_by "Bugeaud" 2012,
  solved_by "Boshernitzan" 1983, solved_by "Katz" 2016,
  formal_uses katzSeq_strictMono katzSeq_intermediateGrowth katz_universal_density]
theorem problem_10_6_variant_2 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ HasIntermediateGrowth α m) ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨katzSeq, katzSeq_strictMono, katzSeq_intermediateGrowth, katz_universal_density⟩

end Bugeaud06
