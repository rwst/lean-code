/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.OrderOfElement
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — §3: stabilization of cycles mod `mⁿ` (BL96, §3)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

The conjugacy map `Φ` and the `3x+1` map `T` act compatibly through every reduction
`ℤ/mⁿ⁺¹ℤ → ℤ/mⁿℤ` (here `m = 2`), so one may study their *cycles* level by level. §3 isolates the
purely combinatorial input behind this: how the length of a cycle changes when one refines the
modulus by one power.

**The general fact (BL96, eq. 3.1).** Call a function `f : ℤ/mⁿ⁺¹ℤ → ℤ/mⁿⁱℤ` **consistent mod `mⁿ`**
if it descends to a function `fₙ` on `ℤ/mⁿℤ`, i.e.

  `x₁ ≡ x₂ (mod mⁿ) ⟹ f(x₁) ≡ f(x₂) (mod mⁿ)`     (`ConsistentMod`).

Such an `f` induces `fₙ = inducedMap` on `ℤ/mⁿℤ`, and the reduction `proj : ℤ/mⁿ⁺¹ℤ → ℤ/mⁿℤ`
semiconjugates `f` to `fₙ` (`induced_semiconj`).

**Lemma 3.1.** If `x` is a purely periodic point of `f` then its reduction `proj x` is a purely
periodic point of `fₙ`, and the period lengths satisfy

  `|σₙ₊₁(x)| = k · |σₙ(proj x)|`     with `1 ≤ k ≤ m`,

where `σ` denotes the periodic orbit. (Here `|σ|` is `Function.minimalPeriod`.) The cycle of `x`
projects onto the cycle of `proj x` as `k` interleaved copies; `k ≤ m` because each residue mod `mⁿ`
has only `m` preimages mod `mⁿ⁺¹` (`proj_fiber_card_le`).

## Contents
* `proj` — the reduction ring hom `ℤ/mⁿ⁺¹ℤ →+* ℤ/mⁿℤ`, with `proj_surjective`, `proj_natCast_val`,
  `proj_eq_iff_val_mod`, and the fiber bound `proj_fiber_card_le` (`≤ m` preimages).
* `ConsistentMod` — eq. (3.1): `f` descends mod `mⁿ`.
* `inducedMap`, `induced_semiconj` — the induced map `fₙ` and the semiconjugacy `proj ∘ f = fₙ ∘ proj`.
* `lemma_3_1` — **Lemma 3.1**: descent of purely periodic points and the period relation
  `|σₙ₊₁(x)| = k·|σₙ(proj x)|`, `1 ≤ k ≤ m`.
* `cycle_length_eq_or_double` — the application to `Φ` (BL96, §3): since `Φ` is **solenoidal**, its
  level maps are consistent mod `2ⁿ`, so Lemma 3.1 applies with `m = 2` and `|σₙ₊₁(x)| = k·|σₙ(x)|`
  with `k = 1` or `2` — the cycle length is **equal to or double** that of the cycle one level down.
* `IsSplit`, `IsInert` — the two cases: a cycle is *split* (`k = 1`, lifts to two cycles `σₙ₊₁(x)`
  and `σₙ₊₁(x) + 2ⁿ`) or *inert* (`k = 2`, lifts to one). `cycle_length_eq_or_double` says every cycle
  is one or the other.
* `proj_eq_zero_two`, `inert_shift` — **eq. (3.2)**: for an inert cycle, `f^[p] x ≡ x + 2ⁿ (mod 2ⁿ⁺¹)`
  where `p = |σₙ(proj x)|` (the two preimages of `proj x` are `x` and `x + 2ⁿ`, and `f^[p]` swaps them).
* `CompatibleFamily`, `cycle_length_pow_two` — **by induction on `n`, every cycle length `|σₙ(x)|` is
  a power of `2`**, for any compatible tower of level maps `Fₙ` (e.g. the level maps `Φₙ` of `Φ`).
* `IsStable`, `stable_length` — a cycle is **stable** if `σₘ(x)` is inert for all `m ≥ n`; then the
  length grows geometrically, `|σ_{b+d}(x)| = 2ᵈ·|σ_b(x)|` (`|σₘ(x)| = 2^{m−n+1}|σₙ₋₁(x)|`).
* `not_isPeriodicPt_of_levels_unbounded`, `stable_not_isPeriodicPt` — **a point with a stable thread
  has no period**: a map `Φ : ℤ₂ → ℤ₂` realizing the family `Fₘ` (`toZModPow m ∘ Φ = Fₘ ∘ toZModPow m`)
  has *no periodic points* on the stable tube, since the level periods `2^{m−n+1}|σₙ₋₁|` are unbounded.
* `theorem_3_1` — **Theorem 3.1** (cited [BL96] axiom): a length-`≥ 4` cycle that is inert together
  with the next cycle up has its second-next cycle inert too, hence is **stable**.
* `levelOrder`, `StableCycle`, `numCyclesOfPeriod`, `Stabilized` — the order of `Φₙ`, a stable cycle,
  the count `|Xₙ,ⱼ|` of period-`2ʲ` cycles, and a *stabilized* set `Xₙ,ⱼ` (all its cycles stable).
* `corollary_3_1A`, `corollary_3_1B` — **Corollaries 3.1A/3.1B** (cited [BL96] axioms): `order(Φₙ) =
  2ⁿ⁻⁴` for `n ≥ 6` (from `σ₆(5)` stable), and persistence of stabilization with constant cycle count.
-/

namespace BL

open Function Set PadicInt

/-- The reduction ring hom `ℤ/mⁿ⁺¹ℤ →+* ℤ/mⁿℤ` ("projection mod `mⁿ`"). -/
@[category API, AMS 11 37, ref "BL96"]
def proj (m n : ℕ) : ZMod (m ^ (n + 1)) →+* ZMod (m ^ n) :=
  ZMod.castHom (pow_dvd_pow m (Nat.le_succ n)) (ZMod (m ^ n))

/-- The reduction `proj` is surjective. -/
@[category API, AMS 11 37, ref "BL96"]
theorem proj_surjective (m n : ℕ) (hm : 0 < m) : Function.Surjective (proj m n) := by
  haveI : NeZero (m ^ n) := ⟨pow_ne_zero _ hm.ne'⟩
  intro y
  refine ⟨((y.val : ℕ) : ZMod (m ^ (n + 1))), ?_⟩
  rw [map_natCast]
  exact ZMod.natCast_rightInverse y

/-- `proj` sends `a` to the residue of its underlying value `a.val` mod `mⁿ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem proj_natCast_val {m n : ℕ} [NeZero (m ^ (n + 1))] (a : ZMod (m ^ (n + 1))) :
    proj m n a = ((a.val : ℕ) : ZMod (m ^ n)) := by
  conv_lhs => rw [← ZMod.natCast_rightInverse a]
  rw [map_natCast]

/-- Two elements have the same reduction mod `mⁿ` iff their values agree mod `mⁿ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem proj_eq_iff_val_mod {m n : ℕ} [NeZero (m ^ (n + 1))] {a b : ZMod (m ^ (n + 1))} :
    proj m n a = proj m n b ↔ a.val % m ^ n = b.val % m ^ n := by
  rw [proj_natCast_val, proj_natCast_val, ZMod.natCast_eq_natCast_iff]; rfl

/-- **BL96, eq. (3.1).** `f : ℤ/mⁿ⁺¹ℤ → ℤ/mⁿ⁺¹ℤ` is *consistent mod `mⁿ`* if it induces a
function on `ℤ/mⁿℤ`, i.e. `x₁ ≡ x₂ (mod mⁿ)` implies `f x₁ ≡ f x₂ (mod mⁿ)`. -/
@[category API, AMS 11 37, ref "BL96"]
def ConsistentMod (m n : ℕ) (f : ZMod (m ^ (n + 1)) → ZMod (m ^ (n + 1))) : Prop :=
  ∀ x₁ x₂ : ZMod (m ^ (n + 1)), proj m n x₁ = proj m n x₂ → proj m n (f x₁) = proj m n (f x₂)

/-- The function `fₙ` on `ℤ/mⁿℤ` induced by a consistent `f` (chosen via any section of `proj`;
well defined on the range of `proj`, which is everything). -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def inducedMap (m n : ℕ) (f : ZMod (m ^ (n + 1)) → ZMod (m ^ (n + 1))) :
    ZMod (m ^ n) → ZMod (m ^ n) :=
  fun y => proj m n (f (Function.invFun (proj m n) y))

/-- For a consistent `f`, the reduction `proj` semiconjugates `f` to the induced map `fₙ`:
`proj (f x) = fₙ (proj x)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem induced_semiconj {m n : ℕ} {f : ZMod (m ^ (n + 1)) → ZMod (m ^ (n + 1))}
    (hf : ConsistentMod m n f) (x : ZMod (m ^ (n + 1))) :
    proj m n (f x) = inducedMap m n f (proj m n x) := by
  show proj m n (f x) = proj m n (f (Function.invFun (proj m n) (proj m n x)))
  exact hf _ _ (Function.invFun_eq ⟨x, rfl⟩).symm

/-- Each residue mod `mⁿ` has at most `m` preimages mod `mⁿ⁺¹` (the fiber bound behind `k ≤ m`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem proj_fiber_card_le (m n : ℕ) (hm : 0 < m) [NeZero (m ^ (n + 1))] (y : ZMod (m ^ n)) :
    Fintype.card {z : ZMod (m ^ (n + 1)) // proj m n z = y} ≤ m := by
  haveI : NeZero (m ^ n) := ⟨pow_ne_zero _ hm.ne'⟩
  -- map a preimage to its top `mⁿ`-digit; injective since the low digits are pinned by `proj`
  let F : {z : ZMod (m ^ (n + 1)) // proj m n z = y} → Fin m := fun z =>
    ⟨z.1.val / m ^ n, by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hm n)]
      calc z.1.val < m ^ (n + 1) := ZMod.val_lt z.1
        _ = m * m ^ n := pow_succ' m n⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hdiv : a.1.val / m ^ n = b.1.val / m ^ n := by simpa [F] using congrArg Fin.val hab
    have hmod : a.1.val % m ^ n = b.1.val % m ^ n := by
      have := a.2.trans b.2.symm; rwa [proj_eq_iff_val_mod] at this
    have hval : a.1.val = b.1.val := by
      rw [← Nat.div_add_mod a.1.val (m ^ n), ← Nat.div_add_mod b.1.val (m ^ n), hdiv, hmod]
    exact Subtype.ext (ZMod.val_injective _ hval)
  calc Fintype.card {z : ZMod (m ^ (n + 1)) // proj m n z = y}
        ≤ Fintype.card (Fin m) := Fintype.card_le_of_injective F hF
    _ = m := Fintype.card_fin m

/-- **BL96, Lemma 3.1.** Let `f : ℤ/mⁿ⁺¹ℤ → ℤ/mⁿ⁺¹ℤ` be consistent mod `mⁿ`. If `x` is a purely
periodic point of `f` (`0 < minimalPeriod f x`), then its reduction `proj x` is a purely periodic
point of the induced map `fₙ`, and the period lengths satisfy `|σₙ₊₁(x)| = k · |σₙ(proj x)|` for some
integer `k` with `1 ≤ k ≤ m`.

*Proof.* The reduction `proj` semiconjugates `f` to `fₙ` (`induced_semiconj`), so a period `P` of `x`
is a period of `proj x`; hence `q := minimalPeriod fₙ (proj x)` divides `P` and `k := P / q ≥ 1`. The
`k` orbit points `f^[j·q] x` (`0 ≤ j < k`) are distinct and all reduce to `proj x`, so they inject
into the fiber of `proj` over `proj x`, which has at most `m` elements (`proj_fiber_card_le`); thus
`k ≤ m`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem lemma_3_1 (m n : ℕ) (hm : 0 < m) (f : ZMod (m ^ (n + 1)) → ZMod (m ^ (n + 1)))
    (hf : ConsistentMod m n f) (x : ZMod (m ^ (n + 1)))
    (hx : 0 < Function.minimalPeriod f x) :
    0 < Function.minimalPeriod (inducedMap m n f) (proj m n x) ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
        Function.minimalPeriod f x = k * Function.minimalPeriod (inducedMap m n f) (proj m n x) := by
  haveI : NeZero (m ^ (n + 1)) := ⟨pow_ne_zero _ hm.ne'⟩
  set g := inducedMap m n f with hgdef
  have hsj : Function.Semiconj (proj m n) f g := fun z => induced_semiconj hf z
  set P := Function.minimalPeriod f x with hPdef
  set q := Function.minimalPeriod g (proj m n x) with hqdef
  have hPpos : 0 < P := hx
  have hper : Function.IsPeriodicPt f P x := isPeriodicPt_minimalPeriod f x
  -- `proj x` is purely periodic under `g` with the same period `P`
  have hgper : Function.IsPeriodicPt g P (proj m n x) := by
    show g^[P] (proj m n x) = proj m n x
    rw [← hsj.iterate_right P x, (hper : f^[P] x = x)]
  have hqdvd : q ∣ P := hgper.minimalPeriod_dvd
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqdvd hPpos
  have hPqP : P / q * q = P := Nat.div_mul_cancel hqdvd
  refine ⟨hqpos, P / q, (Nat.one_le_div_iff hqpos).mpr (Nat.le_of_dvd hPpos hqdvd), ?_,
    (Nat.div_mul_cancel hqdvd).symm⟩
  -- `P / q ≤ m`: the `P/q` orbit points `f^[j·q] x` inject into the fiber of `proj` over `proj x`
  have hmem : ∀ j : Fin (P / q), proj m n (f^[(j : ℕ) * q] x) = proj m n x := by
    intro j
    rw [hsj.iterate_right ((j : ℕ) * q) x, Nat.mul_comm]
    exact (isPeriodicPt_minimalPeriod g (proj m n x)).mul_const j
  let F : Fin (P / q) → {z : ZMod (m ^ (n + 1)) // proj m n z = proj m n x} :=
    fun j => ⟨f^[(j : ℕ) * q] x, hmem j⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    have heq : f^[(a : ℕ) * q] x = f^[(b : ℕ) * q] x := congrArg Subtype.val hab
    have haP : (a : ℕ) * q < P := by
      have := (Nat.mul_lt_mul_right hqpos).mpr a.isLt; rwa [hPqP] at this
    have hbP : (b : ℕ) * q < P := by
      have := (Nat.mul_lt_mul_right hqpos).mpr b.isLt; rwa [hPqP] at this
    have hjj : (a : ℕ) * q = (b : ℕ) * q :=
      iterate_injOn_Iio_minimalPeriod (mem_Iio.mpr haP) (mem_Iio.mpr hbP) heq
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hqpos hjj)
  calc P / q = Fintype.card (Fin (P / q)) := (Fintype.card_fin _).symm
    _ ≤ Fintype.card {z : ZMod (m ^ (n + 1)) // proj m n z = proj m n x} :=
        Fintype.card_le_of_injective F hFinj
    _ ≤ m := proj_fiber_card_le m n hm (proj m n x)

/-- **BL96, §3 (application of Lemma 3.1 to `Φ`).** Since the conjugacy map `Φ` is solenoidal, each
level map `Φₙ₊₁` is consistent mod `2ⁿ`, so Lemma 3.1 applies with the base `m = 2`. Hence for any
purely periodic point `x`, the cycle `σₙ₊₁(x)` it belongs to has length **either equal to or double**
the length of the cycle `σₙ(proj x)` it belongs to one level down: `|σₙ₊₁(x)| = k·|σₙ(proj x)|` with
`k = 1` or `k = 2`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem cycle_length_eq_or_double (n : ℕ) (f : ZMod (2 ^ (n + 1)) → ZMod (2 ^ (n + 1)))
    (hf : ConsistentMod 2 n f) (x : ZMod (2 ^ (n + 1)))
    (hx : 0 < Function.minimalPeriod f x) :
    0 < Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x) ∧
      (Function.minimalPeriod f x = Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x) ∨
        Function.minimalPeriod f x = 2 * Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x)) := by
  obtain ⟨hpos, k, hk1, hk2, hkeq⟩ := lemma_3_1 2 n two_pos f hf x hx
  refine ⟨hpos, ?_⟩
  have hk : k = 1 ∨ k = 2 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exact Or.inl (Nat.le_antisymm (Nat.lt_succ_iff.mp h) hk1)
    · exact Or.inr (Nat.le_antisymm hk2 h)
  rcases hk with rfl | rfl
  · exact Or.inl (by rw [one_mul] at hkeq; exact hkeq)
  · exact Or.inr hkeq

/-- **BL96, §3.** A cycle `σₙ₊₁(x)` is **split** if `|σₙ₊₁(x)| = |σₙ(x)|` (`k = 1`): the cycle
`σₙ(x)` one level down lifts to *two* cycles mod `2ⁿ⁺¹`, namely `σₙ₊₁(x)` and `σₙ₊₁(x) + 2ⁿ`. -/
@[category API, AMS 11 37, ref "BL96"]
def IsSplit (n : ℕ) (f : ZMod (2 ^ (n + 1)) → ZMod (2 ^ (n + 1))) (x : ZMod (2 ^ (n + 1))) : Prop :=
  Function.minimalPeriod f x = Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x)

/-- **BL96, §3.** A cycle `σₙ₊₁(x)` is **inert** if `|σₙ₊₁(x)| = 2|σₙ(x)|` (`k = 2`): the cycle
`σₙ(x)` one level down lifts to a *single* cycle mod `2ⁿ⁺¹`. -/
@[category API, AMS 11 37, ref "BL96"]
def IsInert (n : ℕ) (f : ZMod (2 ^ (n + 1)) → ZMod (2 ^ (n + 1))) (x : ZMod (2 ^ (n + 1))) : Prop :=
  Function.minimalPeriod f x = 2 * Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x)

/-- The kernel of the reduction `proj 2 n` is `{0, 2ⁿ}`: a nonzero element killed by `proj 2 n`
equals `2ⁿ` (the unique nonzero shift between the two preimages of a residue mod `2ⁿ`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem proj_eq_zero_two (n : ℕ) {w : ZMod (2 ^ (n + 1))} (hw : proj 2 n w = 0) (hne : w ≠ 0) :
    w = 2 ^ n := by
  haveI : NeZero (2 ^ (n + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hzero : ((w.val : ℕ) : ZMod (2 ^ n)) = 0 := (proj_natCast_val w).symm.trans hw
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff w.val (2 ^ n)).mp hzero
  have hlt : w.val < 2 ^ n * 2 := by rw [← pow_succ]; exact ZMod.val_lt w
  have ht2 : t < 2 := lt_of_mul_lt_mul_left (by rw [← ht]; exact hlt) (Nat.zero_le _)
  have htne : t ≠ 0 := by
    rintro rfl
    apply hne
    have hv : w.val = 0 := by rw [ht, Nat.mul_zero]
    conv_lhs => rw [← ZMod.natCast_rightInverse w]
    rw [hv, Nat.cast_zero]
  have ht1 : t = 1 := by omega
  have hwval : w.val = 2 ^ n := by rw [ht, ht1, Nat.mul_one]
  conv_lhs => rw [← ZMod.natCast_rightInverse w]
  rw [hwval, Nat.cast_pow, Nat.cast_two]

/-- **BL96, §3, eq. (3.2).** If the cycle `σₙ₊₁(x)` is **inert** (so its length is `2p` where
`p = |σₙ(proj x)|`), then after `p` steps `x` returns to its partner in the fiber over `proj x`:

  `f^[p] x ≡ x + 2ⁿ  (mod 2ⁿ⁺¹)`.

*Proof.* `proj` semiconjugates `f` to `fₙ`, and `p` is a period of `proj x`, so `proj (f^[p] x) =
proj x`, i.e. `f^[p] x − x` lies in the kernel `{0, 2ⁿ}` of `proj` (`proj_eq_zero_two`). It is
nonzero because the minimal period of `x` is `2p > p`, so `f^[p] x ≠ x`; hence `f^[p] x − x = 2ⁿ`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem inert_shift (n : ℕ) (f : ZMod (2 ^ (n + 1)) → ZMod (2 ^ (n + 1)))
    (hf : ConsistentMod 2 n f) (x : ZMod (2 ^ (n + 1)))
    (hx : 0 < Function.minimalPeriod f x) (hinert : IsInert n f x) :
    f^[Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x)] x = x + 2 ^ n := by
  have hinert : Function.minimalPeriod f x =
      2 * Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x) := hinert
  obtain ⟨hpos, -⟩ := lemma_3_1 2 n two_pos f hf x hx
  set p := Function.minimalPeriod (inducedMap 2 n f) (proj 2 n x) with hpdef
  have hsj : Function.Semiconj (proj 2 n) f (inducedMap 2 n f) := fun z => induced_semiconj hf z
  have hprojp : proj 2 n (f^[p] x) = proj 2 n x := by
    rw [hsj.iterate_right p x]
    exact isPeriodicPt_minimalPeriod (inducedMap 2 n f) (proj 2 n x)
  have hne : f^[p] x ≠ x := by
    intro h
    have hper : Function.IsPeriodicPt f p x := h
    have hdvd : Function.minimalPeriod f x ∣ p := hper.minimalPeriod_dvd
    rw [hinert] at hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hw0 : proj 2 n (f^[p] x - x) = 0 := by rw [map_sub, hprojp, sub_self]
  have hw := proj_eq_zero_two n hw0 (sub_ne_zero.mpr hne)
  rw [sub_eq_iff_eq_add] at hw
  rw [hw]; exact add_comm _ _

/-- A **compatible family** of level maps `Fₙ : ℤ/2ⁿℤ → ℤ/2ⁿℤ`: each `Fₙ₊₁` is consistent mod `2ⁿ`
and induces `Fₙ`, i.e. `proj` semiconjugates `Fₙ₊₁` to `Fₙ`. The level maps of a solenoidal map of
`ℤ₂` (such as the conjugacy map `Φ`) form such a family. -/
@[category API, AMS 11 37, ref "BL96"]
def CompatibleFamily (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) : Prop :=
  ∀ n (z : ZMod (2 ^ (n + 1))), proj 2 n (F (n + 1) z) = F n (proj 2 n z)

/-- In a compatible family, every `Fₙ₊₁` is consistent mod `2ⁿ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem CompatibleFamily.consistent {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)}
    (hF : CompatibleFamily F) (n : ℕ) : ConsistentMod 2 n (F (n + 1)) := by
  intro x₁ x₂ h; rw [hF n x₁, hF n x₂, h]

/-- In a compatible family, the map induced by `Fₙ₊₁` is exactly `Fₙ`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem CompatibleFamily.inducedMap_eq {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)}
    (hF : CompatibleFamily F) (n : ℕ) : inducedMap 2 n (F (n + 1)) = F n := by
  funext y
  show proj 2 n (F (n + 1) (Function.invFun (proj 2 n) y)) = F n y
  rw [hF n]
  exact congrArg (F n) (Function.invFun_eq (proj_surjective 2 n two_pos y))

/-- **BL96, §3.** For a compatible family of level maps (e.g. the level maps `Φₙ` of the solenoidal
conjugacy map), the length of any cycle is a **power of `2`**: every purely periodic point of `Fₙ`
has `|σₙ| = 2ʲ` for some `j`. (By induction on `n`: split keeps the length, inert doubles it, both
powers of `2`; the base `ℤ/2⁰ℤ` is a point with cycle length `1 = 2⁰`.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem cycle_length_pow_two {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)}
    (hF : CompatibleFamily F) :
    ∀ (n : ℕ) (x : ZMod (2 ^ n)), 0 < Function.minimalPeriod (F n) x →
      ∃ j : ℕ, Function.minimalPeriod (F n) x = 2 ^ j := by
  intro n
  induction n with
  | zero =>
    intro x _
    haveI : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨0, by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (Subsingleton.elim (F 0 x) x), pow_zero]⟩
  | succ n ih =>
    intro x hx
    obtain ⟨hpos, hdisj⟩ := cycle_length_eq_or_double n (F (n + 1)) (hF.consistent n) x hx
    rw [hF.inducedMap_eq n] at hpos hdisj
    obtain ⟨j, hj⟩ := ih (proj 2 n x) hpos
    rcases hdisj with he | he
    · exact ⟨j, by rw [he, hj]⟩
    · exact ⟨j + 1, by rw [he, hj, pow_succ']⟩

/-- **BL96, §3.** A cycle is **stable** (from base level `b`, along the coherent thread `xs`) if every
higher cycle `σⱼ₊₁(x)` is inert, `j ≥ b`. (The paper's "`σₙ(x)` stable" is `b = n − 1`.) -/
@[category API, AMS 11 37, ref "BL96"]
def IsStable (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n))
    (xs : (m : ℕ) → ZMod (2 ^ m)) (b : ℕ) : Prop :=
  ∀ j, b ≤ j → IsInert j (F (j + 1)) (xs (j + 1))

/-- **BL96, §3.** For a stable cycle the length grows geometrically: `|σ_{b+d}(x)| = 2ᵈ·|σ_b(x)|`
(equivalently `|σₘ(x)| = 2^{m−n+1}|σₙ₋₁(x)|` for `m ≥ n`, with `b = n − 1`). Each higher level is
inert, hence doubles the period (`induced map = Fⱼ`, `proj` thread coherence), and the doublings
compound. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem stable_length {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)} (hF : CompatibleFamily F)
    (xs : (m : ℕ) → ZMod (2 ^ m)) (hxs : ∀ m, proj 2 m (xs (m + 1)) = xs m)
    (b : ℕ) (hstab : IsStable F xs b) :
    ∀ d : ℕ, Function.minimalPeriod (F (b + d)) (xs (b + d))
      = 2 ^ d * Function.minimalPeriod (F b) (xs b) := by
  intro d
  induction d with
  | zero => rw [Nat.add_zero, pow_zero, one_mul]
  | succ d ih =>
    have hin : Function.minimalPeriod (F (b + d + 1)) (xs (b + d + 1))
        = 2 * Function.minimalPeriod (inducedMap 2 (b + d) (F (b + d + 1)))
            (proj 2 (b + d) (xs (b + d + 1))) := hstab (b + d) (Nat.le_add_right b d)
    rw [hF.inducedMap_eq (b + d), hxs (b + d)] at hin
    calc Function.minimalPeriod (F (b + (d + 1))) (xs (b + (d + 1)))
        = 2 * Function.minimalPeriod (F (b + d)) (xs (b + d)) := hin
      _ = 2 * (2 ^ d * Function.minimalPeriod (F b) (xs b)) := by rw [ih]
      _ = 2 ^ (d + 1) * Function.minimalPeriod (F b) (xs b) := by rw [pow_succ', mul_assoc]

/-- If the level periods of `y` are unbounded, then `y` is not a periodic point of any map `G : ℤ₂ →
ℤ₂` realizing the family `Fₘ` (`toZModPow m ∘ G = Fₘ ∘ toZModPow m`): a period `q` of `y` would bound
every level period (`minimalPeriod (Fₘ) (y mod 2ᵐ) ∣ q`). -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem not_isPeriodicPt_of_levels_unbounded {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)}
    (G : ℤ_[2] → ℤ_[2])
    (hG : ∀ m (z : ℤ_[2]), toZModPow m (G z) = F m (toZModPow m z)) (y : ℤ_[2])
    (hub : ∀ q, 0 < q → ∃ m, q < Function.minimalPeriod (F m) (toZModPow m y)) :
    ∀ q, 0 < q → G^[q] y ≠ y := by
  intro q hq hper
  obtain ⟨m, hm⟩ := hub q hq
  have hsc : Function.Semiconj (toZModPow m) G (F m) := fun z => hG m z
  have hpp : Function.IsPeriodicPt (F m) q (toZModPow m y) := by
    show (F m)^[q] (toZModPow m y) = toZModPow m y
    rw [← hsc.iterate_right q y, hper]
  exact absurd (Nat.le_of_dvd hq hpp.minimalPeriod_dvd) (Nat.not_le.mpr hm)

/-- **BL96, §3.** *For a stable cycle, `Φ` restricted to the tube `{y : y ≡ xᵢ (mod 2ⁿ), xᵢ ∈ σₙ(x)}`
has no periodic points.* If the reduction thread of `y` is stable from level `b` (and the base cycle
`σ_b` is genuine, `0 < |σ_b|`), then no iterate of a realizing map `G : ℤ₂ → ℤ₂` fixes `y` — because
`stable_length` makes the level periods `2ᵈ·|σ_b| ≥ 2ᵈ` unbounded. (Tube membership of a stable cycle
yields such a stable thread.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
theorem stable_not_isPeriodicPt {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)}
    (hF : CompatibleFamily F) (G : ℤ_[2] → ℤ_[2])
    (hG : ∀ m (z : ℤ_[2]), toZModPow m (G z) = F m (toZModPow m z)) (y : ℤ_[2]) (b : ℕ)
    (hstab : IsStable F (fun m => toZModPow m y) b)
    (hbpos : 0 < Function.minimalPeriod (F b) (toZModPow b y)) :
    ∀ q, 0 < q → G^[q] y ≠ y := by
  have hxs : ∀ m, proj 2 m (toZModPow (m + 1) y) = toZModPow m y := by
    intro m
    have h := DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow m (m + 1) (Nat.le_succ m)) y
    rwa [RingHom.comp_apply] at h
  apply not_isPeriodicPt_of_levels_unbounded G hG y
  intro q hq
  refine ⟨b + q, ?_⟩
  rw [stable_length hF (fun m => toZModPow m y) hxs b hstab q]
  calc q < 2 ^ q := Nat.lt_two_pow_self
    _ ≤ 2 ^ q * Function.minimalPeriod (F b) (toZModPow b y) := Nat.le_mul_of_pos_right _ hbpos

/-- **BL96, Theorem 3.1** (cited). For the `3x+1` conjugacy map `Φ`, if a cycle has length `≥ 4` and
it together with the next cycle up are both inert, then the cycle two levels up is also inert; hence
the cycle is **stable** (inert at every higher level).

Stated for a compatible family `F` (the level maps `Φₙ` of `Φ`) along a coherent thread `xs`. With `n`
the base level, the length-`≥ 4` cycle is `σₙ₊₁` and the three consecutive cycles `σₙ₊₁, σₙ₊₂, σₙ₊₃`
are the paper's `σₙ, σₙ₊₁, σₙ₊₂`; the conclusion `IsStable F xs n` is the paper's "`σₙ` is stable".

This is a genuine theorem of [BL96] (proved there from the `ax+b` structure of `Φ` and eq. (3.2)); it
is recorded here as a cited axiom rather than reproved. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
axiom theorem_3_1 {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)} (hF : CompatibleFamily F)
    (xs : (m : ℕ) → ZMod (2 ^ m)) (hxs : ∀ m, proj 2 m (xs (m + 1)) = xs m) (n : ℕ)
    (hlen : 4 ≤ Function.minimalPeriod (F (n + 1)) (xs (n + 1)))
    (h1 : IsInert n (F (n + 1)) (xs (n + 1)))
    (h2 : IsInert (n + 1) (F (n + 2)) (xs (n + 2))) :
    IsInert (n + 2) (F (n + 3)) (xs (n + 3)) ∧ IsStable F xs n

/-- The **order** of the level map `Fₙ` (the order of the permutation `Φ̂ₙ`/`Φₙ` of `ℤ/2ⁿℤ`), as an
element of the monoid of self-maps under composition. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def levelOrder (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) (n : ℕ) : ℕ :=
  orderOf (F n : Function.End (ZMod (2 ^ n)))

/-- A level-`n` cycle (the orbit of `x` under `Fₙ`) is a **stable cycle** if some coherent lift `xs`
of `x` to a 2-adic thread is stable from level `n` (inert at every higher level). -/
@[category API, AMS 11 37, ref "BL96"]
def StableCycle (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) (n : ℕ) (x : ZMod (2 ^ n)) : Prop :=
  ∃ xs : (m : ℕ) → ZMod (2 ^ m),
    (∀ m, proj 2 m (xs (m + 1)) = xs m) ∧ xs n = x ∧ IsStable F xs n

/-- The number of cycles of `Fₙ` of period `2ʲ` — the size `|Xₙ,ⱼ|` of the set `Xₙ,ⱼ` of period-`2ʲ`
cycles (points of minimal period `2ʲ`, divided by the common cycle length `2ʲ`). -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def numCyclesOfPeriod (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) (n j : ℕ) : ℕ :=
  Nat.card {x : ZMod (2 ^ n) // Function.minimalPeriod (F n) x = 2 ^ j} / 2 ^ j

/-- `Xₙ,ⱼ` is **stabilized** if it consists entirely of stable cycles: every period-`2ʲ` point of
`Fₙ` lies on a stable cycle. -/
@[category API, AMS 11 37, ref "BL96"]
def Stabilized (F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) (n j : ℕ) : Prop :=
  ∀ x : ZMod (2 ^ n), Function.minimalPeriod (F n) x = 2 ^ j → StableCycle F n x

/-- **BL96, Corollary 3.1A** (cited). `order(Φ̂ₙ) = order(Φₙ) = 2ⁿ⁻⁴` for `n ≥ 6`. The proof's input
is that `σ₆(5) = {5, 17, 37, 49}` is a stable cycle (here `StableCycle F 6 5`), whence Theorem 3.1
makes the higher orders double off the level-`6` data. Cited from [BL96]. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
axiom corollary_3_1A {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)} (hF : CompatibleFamily F)
    (hbij : ∀ n, Function.Bijective (F n)) (hstab : StableCycle F 6 5) (n : ℕ) (hn : 6 ≤ n) :
    levelOrder F n = 2 ^ (n - 4)

/-- **BL96, Corollary 3.1B** (cited). If `Xₙ,ₙ₋ⱼ` is stabilized for all `0 ≤ j ≤ k − 1` and the three
counts `|Xₙ,ₙ₋ₖ| = |Xₙ₊₁,ₙ₊₁₋ₖ| = |Xₙ₊₂,ₙ₊₂₋ₖ|` agree, then `Xₘ,ₘ₋ₖ` is stabilized for all `m ≥ n`
with `|Xₘ,ₘ₋ₖ| = |Xₙ,ₙ₋ₖ|`. (Stabilization, once it sets in, persists up the tower with a constant
count — Theorem 3.1 applied to `Table 2.2`.) Cited from [BL96]. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_cycle_stabilization"]
axiom corollary_3_1B {F : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)} (hF : CompatibleFamily F)
    (n k : ℕ)
    (hstabilized : ∀ j, j ≤ k - 1 → Stabilized F n (n - j))
    (hcard : numCyclesOfPeriod F n (n - k) = numCyclesOfPeriod F (n + 1) (n + 1 - k)
      ∧ numCyclesOfPeriod F (n + 1) (n + 1 - k) = numCyclesOfPeriod F (n + 2) (n + 2 - k)) :
    ∀ m, n ≤ m → Stabilized F m (m - k)
      ∧ numCyclesOfPeriod F m (m - k) = numCyclesOfPeriod F n (n - k)

end BL
