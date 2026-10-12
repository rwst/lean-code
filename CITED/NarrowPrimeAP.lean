/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Chebyshev
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The prime number theorem and narrow progressions in the primes (cited)

Two external inputs of [Oda26] Theorem 68, recorded as cited axioms:

* `PNT.theta_div_tendsto` — the **prime number theorem** in Chebyshev form, `θ(x)/x → 1`
  ([Had96], [dlVP96]).  The Mathlib pinned here has `Chebyshev.theta` and Chebyshev's bounds but not
  the asymptotic; it is formalized in the PrimeNumberTheorem+ project ([PNT+]) and should replace
  this axiom once available in Mathlib.
* `Shao.narrow_ap` — **narrow arithmetic progressions in dense subsets of the primes** ([Sha15]
  Theorem 1.3, qualitative form [TZ14] Theorem 5): for `k ≥ 3` and `δ > 0`, for all large `Y`, every
  set `A` of primes `≤ Y` with `|A| ≥ δY/log Y` contains a nontrivial `k`-term progression with
  common difference `D ≤ C_{k,δ}(log Y)^{(k−1)2^{k−2}}`.  (Stated as quoted in [Oda26] App. E.1;
  a decreasing progression is reversed, so `D > 0`.)

## References

* [Had96] J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s) et ses conséquences
  arithmétiques*, Bull. SMF 24 (1896), 199–220.
* [dlVP96] C.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers*,
  Ann. Soc. Sci. Bruxelles 20 (1896), 183–256.
* [PNT+] A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd*, github.com/AlexKontorovich.
* [Sha15] X. Shao, *Narrow arithmetic progressions in the primes*, IMRN (2017); arXiv:1509.04050.
* [TZ14] T. Tao, T. Ziegler, *Narrow progressions in the primes*, arXiv:1409.1327.
* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace PNT

open Filter Topology

/-- **The prime number theorem** ([Had96], [dlVP96]): `θ(x)/x → 1`. -/
@[category research solved, AMS 11, ref "Had96", group "prime_number_theorem"]
axiom theta_div_tendsto : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)

end PNT

namespace Shao

/-- **Narrow progressions in the primes** ([Sha15] Thm 1.3, [TZ14] Thm 5). -/
@[category research solved, AMS 11, ref "Sha15", group "narrow_prime_ap"]
axiom narrow_ap (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime ∧ (p : ℝ) ≤ Y) →
      δ * Y / Real.log Y ≤ A.card →
      ∃ P D : ℕ, 0 < D ∧ (D : ℝ) ≤ C * Real.log Y ^ ((k - 1) * 2 ^ (k - 2)) ∧
        ∀ j < k, P + j * D ∈ A

end Shao
