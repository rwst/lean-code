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

import Mathlib.Analysis.RCLike.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Topology.MetricSpace.HausdorffDimension
import ForMathlib.Data.Real.NearestInt
import ForMathlib.NumberTheory.ContinuedFractions.Lagrange
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bugeaud Collection of Conjectures and Open Questions: $p$-adic Littlewood Conjecture

This is the $p$-adic analogue of the Littlewood conjecture, posed by de Mathan and
Teulié. A liminf-based formulation also appears in the file
`FormalConjectures/Wikipedia/LittlewoodConjecture.lean` as `padic_littlewood_conjecture`.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [dMT04] de Mathan, Bernard, and Olivier Teulié. "Problèmes diophantiens simultanés."
    Monatshefte für Mathematik 143.3 (2004): 229-245.
  - [EK07] Einsiedler, Manfred, and Dmitry Kleinbock. "Measure rigidity and $p$-adic
    Littlewood-type problems." Compositio Mathematica 143.3 (2007): 689-702.
-/

namespace Bugeaud

/-! ## Informal-result registry

General results these (published) proofs rely on that are **not** in Mathlib,
recorded at the level of "what notion the proof needs" rather than precise
lemmas. Registry-keyed so the `informal_uses` edges below share canonical
nodes. -/

informal_result "cf-quadratic-periodicity"
  latex "Lagrange's theorem: a real number is a quadratic irrational iff its continued fraction expansion is eventually periodic; hence quadratic irrationals have bounded partial quotients."
  refs "Bug12"
  formalized_as lagrange

informal_result "measure-rigidity-diagonal"
  latex "Einsiedler-Katok-Lindenstrauss measure rigidity: classification of invariant measures for higher-rank diagonalizable (Cartan) actions on homogeneous spaces, forcing positive-entropy ergodic components to be homogeneous (Haar)."
  refs "EK07"

informal_result "dani-correspondence"
  latex "Dani correspondence with an entropy/variational principle: Diophantine approximation of a real corresponds to bounded orbits of a diagonal flow on the space of unimodular lattices, with the Hausdorff dimension of the bounded-orbit (exceptional) set controlled by entropy."
  refs "EK07"

/--
Problem 10.8 ($p$-adic Littlewood conjecture). For every real number $\xi$ and
every prime number $p$,
$$\inf_{q \ge 1} q \cdot \lVert q \xi \rVert \cdot |q|_p = 0,$$
where $\lVert \cdot \rVert$ denotes the distance to the nearest integer and
$|\cdot|_p$ denotes the $p$-adic absolute value. Posed by de Mathan and
Teulié [dMT04].
-/
@[category research open, AMS 11, group "bugeaud_10_8",
  ref "Bug12" "dMT04", conjectured_by "de Mathan" "Teulié" 2004]
theorem problem_10_8 (ξ : ℝ) (p : ℕ) (hp : p.Prime) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  sorry

/--
The quadratic case of Problem 10.8. de Mathan and Teulié [dMT04] solved the
$p$-adic Littlewood conjecture for quadratic real numbers: when $\xi$ is a real
algebraic number of degree $2$ over $\mathbb{Q}$ (equivalently, a quadratic
irrational), one has
$$\inf_{q \ge 1} q \cdot \lVert q \xi \rVert \cdot |q|_p = 0$$
for every prime $p$. In fact they prove the sharper estimate
$\liminf_{q \to \infty} q \log q \cdot \lVert q \xi \rVert \cdot |q|_p < +\infty$.
The condition `(minpoly ℚ ξ).natDegree = 2` characterizes quadratic
irrationals: a transcendental $\xi$ has `minpoly ℚ ξ = 0` (degree $0$), and a
rational $\xi$ has minimal polynomial of degree $1$.
-/
@[category research solved, AMS 11, group "bugeaud_10_8",
  ref "Bug12" "dMT04", conjectured_by "de Mathan" "Teulié" 2004,
  solved_by "de Mathan" "Teulié" 2004, informal_uses "cf-quadratic-periodicity"]
theorem problem_10_8.variants.quadratic (ξ : ℝ) (p : ℕ) (hp : p.Prime)
    (hξ : (minpoly ℚ ξ).natDegree = 2) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  sorry

/--
The exceptional set for Problem 10.8 has Hausdorff dimension zero.
Einsiedler and Kleinbock [EK07], following the measure-rigidity approach of
Einsiedler, Katok and Lindenstrauss, proved that for every prime $p$ the set of
real $\xi$ for which the $p$-adic Littlewood conjecture *fails*, i.e.
$$\liminf_{q \to \infty} q \cdot |q|_p \cdot \lVert q \xi \rVert > 0,$$
has Hausdorff dimension $0$ (in fact it is a countable union of sets of box
dimension $0$). Here the failure is phrased as the liminf-based formulation
(Theorem 1.1 of [EK07], equation (1.1)) being nonzero.
-/
@[category research solved, AMS 11, group "bugeaud_10_8",
  ref "Bug12" "EK07", conjectured_by "de Mathan" "Teulié" 2004,
  solved_by "Einsiedler" "Kleinbock" 2007,
  informal_uses "measure-rigidity-diagonal" "dani-correspondence"]
theorem problem_10_8.variants.exceptional_set_dimH_zero (p : ℕ) (hp : p.Prime) :
    dimH {ξ : ℝ | Filter.atTop.liminf
      (fun q : ℕ ↦ q * padicNorm p q * distToNearestInt (q * ξ)) ≠ 0} = 0 := by
  sorry

end Bugeaud
