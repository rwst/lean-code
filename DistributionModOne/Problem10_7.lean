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

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import ForMathlib.NumberTheory.PisotNumber
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Bugeaud Collection of Conjectures and Open Questions: Confined Powers of Non-Pisot Numbers

*References:*
  - [Bug12a] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Bug12b] Bugeaud, Yann, and Nikolay Moshchevitin. "On fractional parts of powers
    of real numbers close to 1." Mathematische Zeitschrift 271.3 (2012): 627-637.
-/

namespace Bugeaud

/--
Problem 10.7. Let $\varepsilon$ be a positive real number. Are there arbitrarily
large real numbers $\alpha$ such that $\alpha$ is not a Pisot number and all the
fractional parts $\{\alpha^n\}$, $n \ge 1$, are lying in an interval of length
$\varepsilon / \alpha$? [Bug12b]
-/
@[category research open, AMS 11, group "bugeaud_10_7",
  ref "Bug12a" "Bug12b", conjectured_by "Bugeaud" "Moshchevitin" 2012]
theorem problem_10_7 :
    ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, ∃ α : ℝ, M < α ∧ ¬ IsPisot α ∧
      ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → Int.fract (α ^ n) ∈ Set.Icc c (c + ε / α) := by
  sorry

end Bugeaud
