/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.BadResidues
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Shell-level count of Terras bad residues

Step 2 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
lifting the residue-level cardinality bound of `CC.Density.badResidues` to a
count on a dyadic shell `[2 ^ M, 2 ^ (M+1))`.

For `k ≤ M`, every `n ∈ [2 ^ M, 2 ^ (M+1))` decomposes uniquely as
`n = q · 2 ^ k + r` with `q ∈ [2 ^ (M-k), 2 ^ (M-k+1))` and `r ∈ [0, 2 ^ k)`.
The map `n ↦ ((n : ZMod (2^k)), n / 2 ^ k)` is therefore an injection from the
shell into `ZMod (2 ^ k) × [2 ^ (M-k), 2 ^ (M-k+1))`, and restricting to
"bad" residues gives

  `#{n ∈ shell : (n : ZMod (2 ^ k)) ∈ badResidues k J₀}
      ≤ #(badResidues k J₀) · 2 ^ (M-k)`.

Combined with the Hoeffding tail bound for `#(badResidues k J₀)`, the shell-level
count is at most `2 ^ M · exp (-2 t² k)` — the exponential-in-`k` decay in the
shell fraction that the density transport in the next file consumes.
-/

namespace CC

namespace Density

/-! ### The shell-restricted bad set -/

/-- The set of integers in the dyadic shell `[2 ^ M, 2 ^ (M+1))` whose residue
class mod `2 ^ k` is a "bad" residue at level `k` with odd-step budget `J₀`. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
def shellBadResidues (k M J₀ : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    fun n => (n : ZMod (2 ^ k)) ∈ badResidues k J₀

@[category API, AMS 11 37, group "terras_density"]
theorem mem_shellBadResidues {k M J₀ n : ℕ} :
    n ∈ shellBadResidues k M J₀ ↔
      (2 ^ M ≤ n ∧ n < 2 ^ (M + 1)) ∧ (n : ZMod (2 ^ k)) ∈ badResidues k J₀ := by
  classical
  simp [shellBadResidues, Finset.mem_Ico]

/-! ### Fiber-decomposition count bound -/

/-- **Shell count via fiber decomposition.** For `k ≤ M`, every shell element
`n ∈ [2 ^ M, 2 ^ (M+1))` is uniquely determined by its residue class mod
`2 ^ k` and the quotient `n / 2 ^ k ∈ [2 ^ (M-k), 2 ^ (M-k+1))`. Hence the
shell-bad set injects into `badResidues k J₀ × [2 ^ (M-k), 2 ^ (M-k+1))`, which
has cardinality `#(badResidues k J₀) · 2 ^ (M-k)`.

Pure fiber counting: nothing here is specific to Terras beyond the shell being
dyadic. -/
@[category API, AMS 11 37, group "terras_density"]
theorem card_shellBadResidues_le {k M J₀ : ℕ} (hkM : k ≤ M) :
    (shellBadResidues k M J₀).card
      ≤ (badResidues k J₀).card * 2 ^ (M - k) := by
  classical
  have h2kpos : 0 < 2 ^ k := Nat.two_pow_pos k
  set f : ℕ → ZMod (2 ^ k) × ℕ :=
    fun n => ((n : ZMod (2 ^ k)), n / 2 ^ k) with hf_def
  set target : Finset (ZMod (2 ^ k) × ℕ) :=
    badResidues k J₀ ×ˢ Finset.Ico (2 ^ (M - k)) (2 ^ (M - k + 1)) with htarget_def
  have himg : ∀ n ∈ shellBadResidues k M J₀, f n ∈ target := by
    intro n hn
    rw [mem_shellBadResidues] at hn
    obtain ⟨⟨h1, h2⟩, hr⟩ := hn
    rw [htarget_def, Finset.mem_product]
    refine ⟨hr, ?_⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, ?_⟩
    · -- `2 ^ (M-k) ≤ n / 2 ^ k`
      rw [Nat.le_div_iff_mul_le h2kpos]
      calc 2 ^ (M - k) * 2 ^ k = 2 ^ M := by rw [← pow_add]; congr 1; omega
        _ ≤ n := h1
    · -- `n / 2 ^ k < 2 ^ (M-k+1)`
      rw [Nat.div_lt_iff_lt_mul h2kpos]
      calc n < 2 ^ (M + 1) := h2
        _ = 2 ^ (M - k + 1) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  have hinj : Set.InjOn f (shellBadResidues k M J₀) := by
    intro n₁ _ n₂ _ hfeq
    rw [hf_def, Prod.mk.injEq] at hfeq
    obtain ⟨hval, hdiv⟩ := hfeq
    have hmod : n₁ % 2 ^ k = n₂ % 2 ^ k := by
      have h := congr_arg ZMod.val hval
      rwa [ZMod.val_natCast (n := 2 ^ k) n₁, ZMod.val_natCast (n := 2 ^ k) n₂] at h
    have h1 := Nat.div_add_mod n₁ (2 ^ k)
    rw [hdiv, hmod] at h1
    have h2 := Nat.div_add_mod n₂ (2 ^ k)
    omega
  calc (shellBadResidues k M J₀).card
      ≤ target.card := Finset.card_le_card_of_injOn f himg hinj
    _ = (badResidues k J₀).card *
          (Finset.Ico (2 ^ (M - k)) (2 ^ (M - k + 1))).card := by
        rw [htarget_def]; exact Finset.card_product _ _
    _ = (badResidues k J₀).card * 2 ^ (M - k) := by
        rw [Nat.card_Ico]
        congr 1
        rw [pow_succ]; omega

/-! ### Explicit Hoeffding-type shell bound -/

/-- **Shell-level Hoeffding bound.** Combining the residue-level Hoeffding
tail (`card_badResidues_le_hoeffding`) with the fiber-count bound
(`card_shellBadResidues_le`), the shell-bad set on dyadic shell `M` has size at
most `2 ^ M · exp (-2 t² k)`. This is the ingredient consumed by the
shell-to-global density transport in `CET.QuantitativeDensity`. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "terras_density"]
theorem card_shellBadResidues_le_hoeffding
    {k M J₀ : ℕ} {t : ℝ} (hkM : k ≤ M) (ht : 0 ≤ t)
    (hcut : (1 / 2 + t) * k ≤ (J₀ : ℝ) + 1) :
    ((shellBadResidues k M J₀).card : ℝ)
      ≤ (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * k) := by
  have hnat : (shellBadResidues k M J₀).card
      ≤ (badResidues k J₀).card * 2 ^ (M - k) := card_shellBadResidues_le hkM
  have hres := card_badResidues_le_hoeffding (k := k) (J₀ := J₀) (t := t) ht hcut
  have hshellReal :
      ((shellBadResidues k M J₀).card : ℝ)
        ≤ ((badResidues k J₀).card : ℝ) * (2 : ℝ) ^ (M - k) := by
    exact_mod_cast hnat
  have hpowMk : (0 : ℝ) ≤ (2 : ℝ) ^ (M - k) := by positivity
  have hres' :
      ((badResidues k J₀).card : ℝ) * (2 : ℝ) ^ (M - k)
        ≤ ((2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k)) * (2 : ℝ) ^ (M - k) :=
    mul_le_mul_of_nonneg_right hres hpowMk
  have hsplit : (2 : ℝ) ^ k * (2 : ℝ) ^ (M - k) = (2 : ℝ) ^ M := by
    rw [← pow_add]; congr 1; omega
  calc ((shellBadResidues k M J₀).card : ℝ)
      ≤ ((badResidues k J₀).card : ℝ) * (2 : ℝ) ^ (M - k) := hshellReal
    _ ≤ ((2 : ℝ) ^ k * Real.exp (-2 * t ^ 2 * k)) * (2 : ℝ) ^ (M - k) := hres'
    _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ (M - k)) * Real.exp (-2 * t ^ 2 * k) := by ring
    _ = (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * k) := by rw [hsplit]

end Density

end CC
