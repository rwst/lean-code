/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.BinomialTail
import CC.Decomposition
import CC.Periodicity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Terras "bad residue" set at level `k`

Step 1 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
identifying the residue-class filter that controls the density argument.

The natural quantity carried by the integer `n` is `CC.num_odd_steps k n`, the
count of odd (tripling) steps in the first `k` Terras iterates. The
combinatorial infrastructure of `CC.ParityTail` — in particular the exact
binomial count `card_residues_with_oddCount = choose k j` and the Hoeffding
tail bounds — is stated in terms of `CC.ParityTail.oddCount`, which is a
function on residues `r : ZMod (2 ^ k)`.

The two quantities agree on the natural bridge:

  `CC.ParityTail.oddCount k (n : ZMod (2 ^ k)) = CC.num_odd_steps k n`.

That is the content of `oddCount_natCast`. Combining with the upper-tail
Hoeffding bound `card_residues_with_oddCount_ge_sub_le_hoeffding` gives an
explicit exponential-in-`k` bound on the number of residue classes whose
odd-step count is unusually high — the "bad residue set" of the title.

`ShellCount.lean` lifts these residue counts to counts on a dyadic shell.

## Parametrization

`badResidues k J₀` is indexed by the odd-step **budget** `J₀` — the largest
odd-step count a residue may have and still be "good" — rather than by a
deficit `k - K`. That is deliberate: `J₀` is exactly what the descent criterion
`CC.descent_of_num_odd_steps_le` consumes, so no truncated `Nat` subtraction
appears anywhere between here and the descent bridge.
-/

namespace CC

namespace Density

open CC.ParityTail

/-! ### Bit-level cast

`E_vec` takes values in `{0, 1} ⊂ ℕ`; on this range the coercion `ℕ → ZMod 2`
is injective and preserves the "is `1`" predicate. -/

/-- On the range `{0, 1}`, the cast `ℕ → ZMod 2` sends `1` to `1` and nothing
else. -/
private lemma zmod2_cast_eq_one_iff {x : ℕ} (hx : x ≤ 1) :
    ((x : ZMod 2) = 1) ↔ x = 1 := by
  interval_cases x <;> decide

/-! ### The residue ↔ integer bridge -/

/-- **Residue-integer bridge.** The `ParityTail` odd-step count of a residue
class `(n : ZMod (2 ^ k))` equals the integer-level `CC.num_odd_steps k n`.

`num_odd_steps k n` is a sum of `E_vec k n` over `Fin k`; `oddCount k r` is
the `wordWeight` of `parityVec k r`, itself defined via `E_vec k r.val`.
The proof therefore has three moves: (i) periodicity `terras_backward`
identifies `E_vec k n` and `E_vec k (n % 2 ^ k) = E_vec k ((n : ZMod (2 ^ k)).val)`;
(ii) the sum-form of `num_odd_steps` matches the filter-form of `wordWeight`
because `E_vec` values lie in `{0, 1}`; (iii) the cast `ℕ → ZMod 2` on `{0,1}`
preserves equality with `1`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem oddCount_natCast (k n : ℕ) :
    oddCount k ((n : ZMod (2 ^ k))) = CC.num_odd_steps k n := by
  classical
  set r : ZMod (2 ^ k) := (n : ZMod (2 ^ k)) with hr_def
  -- (i) `r.val = n % 2 ^ k`, and `terras_backward` transports `E_vec` across it.
  have hval : r.val = n % 2 ^ k := by
    rw [hr_def]
    exact ZMod.val_natCast (n := 2 ^ k) n
  have hEvec : E_vec k r.val = E_vec k n := by
    apply terras_backward k r.val n
    rw [hval, Nat.mod_mod]
  -- (ii)-(iii) unfold and match filter- vs sum-forms of the odd-step count.
  unfold oddCount wordWeight CC.parityVec
  rw [num_odd_steps_eq_E_vec_sum]
  -- Rewrite the filter's predicate using the cast lemma, then use sum-of-0/1 = count-of-1.
  have hfilter :
      (Finset.univ.filter fun i : Fin k =>
          ((E_vec k r.val i : ℕ) : ZMod 2) = 1)
        = Finset.univ.filter fun i : Fin k => E_vec k r.val i = 1 := by
    apply Finset.filter_congr
    intro i _
    exact zmod2_cast_eq_one_iff (E_vec_le_one k r.val i)
  rw [hfilter, hEvec]
  -- `card {i | f i = 1} = ∑ i, f i` when `f i ∈ {0, 1}`.
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hle : E_vec k n i ≤ 1 := E_vec_le_one k n i
  change (if E_vec k n i = 1 then 1 else 0) = E_vec k n i
  split_ifs with h <;> omega

/-! ### The bad-residue set and its Hoeffding cardinality bound -/

/-- The **bad residue set** at level `k` with odd-step budget `J₀`: residues
`r : ZMod (2 ^ k)` whose first `k` Terras parity bits contain strictly more
than `J₀` odd steps.

The complement is the useful side: `r ∉ badResidues k J₀` says
`oddCount k r ≤ J₀`, which is verbatim the hypothesis of
`CC.descent_of_num_odd_steps_le`. In the Terras density argument `J₀` is
chosen just below `(log 2 / log 3) · k` — see
`CC.SRSBridge.criticalRatio` — so that a good residue has too few triplings
to escape a `k`-step descent.

The Hoeffding tail from `CC.ParityTail` bounds this set exponentially in `k`
whenever the budget sits a positive slack `t` above the mean `k / 2`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
def badResidues (k J₀ : ℕ) : Finset (ZMod (2 ^ k)) :=
  Finset.univ.filter fun r => J₀ < oddCount k r

@[category API, AMS 11 37, group "terras_density"]
theorem mem_badResidues {k J₀ : ℕ} {r : ZMod (2 ^ k)} :
    r ∈ badResidues k J₀ ↔ J₀ < oddCount k r := by
  classical
  simp [badResidues]

/-- **Hoeffding bound for the bad residue set.** Whenever the budget `J₀` sits
a positive slack `t` above the mean — `(1/2 + t) · k ≤ J₀ + 1` — the bad
residue set has fractional size at most `exp (-2 t² k)`. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "terras_density"]
theorem card_badResidues_le_hoeffding
    {k J₀ : ℕ} {t : ℝ} (ht : 0 ≤ t) (hcut : (1 / 2 + t) * k ≤ (J₀ : ℝ) + 1) :
    ((badResidues k J₀).card : ℝ)
      ≤ (2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k) := by
  simpa [badResidues] using
    (card_residues_with_oddCount_gt_le_hoeffding (k := k) (J₀ := J₀) (t := t) ht hcut)

/-! ### Bad-residue membership in `num_odd_steps` language

Restated in terms of the integer-side count, ready for the shell-count step. -/

/-- **Integer-side membership.** A natural number `n`'s residue class mod
`2 ^ k` lies in `badResidues k J₀` iff its first `k` Terras iterates contain
strictly more than `J₀` odd steps. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem natCast_mem_badResidues {k J₀ n : ℕ} :
    (n : ZMod (2 ^ k)) ∈ badResidues k J₀ ↔ J₀ < CC.num_odd_steps k n := by
  rw [mem_badResidues, oddCount_natCast]

end Density

end CC
