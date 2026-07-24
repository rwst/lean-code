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
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.
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
$(\{\xi m_n\})_{n \ge 1}$ is *not* dense modulo one has full Hausdorff dimension. -/
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
`0 < α < 1` its terms eventually dominate $\exp(n^\alpha)$. -/
@[category test, AMS 11, group "bugeaud_10_6"]
lemma example_hasIntermediateGrowth (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    HasIntermediateGrowth α mSeq := by
  sorry

/-! ## Katz's resolution of Problem 10.6

Katz [Kat16] answers Problem 10.6 in the affirmative. The heart of his construction is a
positive-entropy $T_p$-invariant measure obtained from a smooth $p$-adic interpolation
(Meiri, Lindenstrauss) together with Boshernitzan's non-lacunary density; the resulting
*single* sequence can be made as sparse as one likes. We fix Katz's explicit instance
(Corollary 4.9 with the identity polynomials $p_1 = p_2 = \mathrm{id}$) and take its
increasing enumeration. -/

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
known to meet this pointwise ratio lower bound, so this stronger variant is left open. -/
@[category research open, AMS 11, group "bugeaud_10_6",
  ref "Bug12", conjectured_by "Bugeaud" 2012]
theorem problem_10_6_variant_1 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    IsGenuinelySublacunary m ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  sorry

/-- Problem 10.6, intermediate-growth variant — **resolved by Katz [Kat16]**. The single
sequence `katzSeq` is strictly increasing, has intermediate (super-polynomial,
sub-exponential) growth, and is dense modulo one for every irrational $\xi$. -/
@[category research solved, AMS 11, group "bugeaud_10_6",
  ref "Bug12" "Kat16", conjectured_by "Bugeaud" 2012, solved_by "Katz" 2016,
  formal_uses katzSeq_strictMono katzSeq_intermediateGrowth katz_universal_density]
theorem problem_10_6_variant_2 :
    ∃ m : ℕ → ℕ,
    StrictMono m ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ HasIntermediateGrowth α m) ∧
    ∀ ξ : ℝ, Irrational ξ →
      Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨katzSeq, katzSeq_strictMono, katzSeq_intermediateGrowth, katz_universal_density⟩

end Bugeaud06
