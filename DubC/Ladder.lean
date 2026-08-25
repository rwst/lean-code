/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.CoreCertificate

/-!
# The ladder: certifying `CoreClosed` one prime at a time

`DubC.CoreClosed a M K` — "every residue lying on a cycle of the base-`a` coprimality subshift
modulo `M` is in `K`" — is the one *global* hypothesis of the compressed-core certificate of
`DubC/CoreCertificate.lean`.  Taken literally it quantifies over all of `ZMod M`, which for the
`a = 7` target is `∏_{p≤31} p ≈ 2·10¹¹` residues.  This file cuts it down to a chain of checks
whose largest rung is about `2.2·10⁷` residues, which is the size at which the C engines in this
directory actually work.

## Two ingredients

**A rank certificate replaces the cycle structure.**  `DubC.coreClosed_of_rankOn`: given a
candidate set `C` known to contain every cycle, and a `ρ : ZMod M → ℕ` that never increases
along an admissible step inside `C` and *strictly* decreases out of every state of `C` not in
`K`, no cycle can avoid `K` — a cycle through `r ∉ K` would give `ρ r < ρ r`.  This is the
condensation height, and it is a single pass: no strongly connected components, no iteration.

**The projection carries cycles downwards.**  `DubC.onCycle_proj`: for `M' ∣ M` the ring
homomorphism `ZMod M →+* ZMod M'` maps admissible steps to admissible steps
(`DubC.step_proj` — units map to units, and `t = a·r + d` is preserved), hence cycles to cycles.
So if `K'` already catches every cycle modulo `M'`, every cycle modulo `M` lives inside the
preimage `π⁻¹(K')`, and *that* is the candidate set `C` for the rank certificate one level up.

Putting them together is `DubC.coreClosed_of_ladder`, the **rung**: `CoreClosed a M' K'` plus a
rank function checked only on `π⁻¹(K')` gives `CoreClosed a M K`.

## Why the rung is finite

`DubC.forall_of_forall_lift` turns a quantifier over `{r : ZMod M | K' (π r)}` into a quantifier
over pairs `(r', k)` with `K' r'` and `k < M / M'`, via `r = r'.val + k·M'`.  So the rung costs
`|K'| · (M / M') · a` successor computations and never touches `ZMod M` as a whole.

For the `a = 7` ladder that is, at each new prime `p`, `|K'| · p · 7`:

| rung | `M'` | `|K'|` (from the C runs) | rung size `|K'| · p` |
|------|------|--------------------------|----------------------|
| `p ≤ 17` | — | — | 15 360 (the whole reduced space) |
| `p = 19` | `∏_{p≤17}` | 15 360 | 276 480 |
| `p = 23` | `∏_{p≤19}` | 48 548 | 1 068 056 |
| `p = 29` | `∏_{p≤23}` | 358 529 | 10 038 812 |
| `p = 31` | `∏_{p≤29}` | 738 303 | **22 149 090** |

versus `2·10¹¹` for the naive quantifier — a factor of about `10⁴`.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
-/

namespace DubC

/-! ### A rank function certifies that there are no cycles outside `K` -/

/-- **No cycle can leave `K` if a rank strictly drops out of `K`.**  `C` is any set known to
contain every state lying on a cycle; `ρ` never increases along a step inside `C`, and strictly
decreases out of a state of `C` that is not in `K`.  A cycle through `r ∉ K` would then walk
from `r` back to `r` with a strict drop at the first step and no increase afterwards, giving
`ρ r < ρ r`.

Every state visited by a cycle is itself on a cycle, which is what lets the walk stay inside
`C` — that is the only place the shape of `Relation.TransGen` is used. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem transGen_self_of_rank {S : Type*} {adm : S → S → Prop} (C K : S → Prop) (ρ : S → ℕ)
    (hcyc : ∀ v, Relation.TransGen adm v v → C v)
    (hle : ∀ v t, C v → C t → adm v t → ρ t ≤ ρ v)
    (hlt : ∀ v t, C v → C t → adm v t → ¬ K v → ρ t < ρ v)
    {r : S} (hr : Relation.TransGen adm r r) : K r := by
  by_contra hK
  -- split the cycle into its first step `r → t` and the return path `t →* r`
  obtain ⟨t, hstep, hrest⟩ := Relation.TransGen.head'_iff.mp hr
  have hCr : C r := hcyc r hr
  -- everything on the return path is itself on a cycle, hence in `C`
  have hmid : ∀ s, Relation.ReflTransGen adm t s → Relation.ReflTransGen adm s r → C s := by
    intro s h1 h2
    exact hcyc s (Relation.TransGen.trans_left (Relation.TransGen.tail' h2 hstep) h1)
  -- so `ρ` never increases along the return path
  have walk : ∀ s, Relation.ReflTransGen adm t s → Relation.ReflTransGen adm s r →
      ρ s ≤ ρ t := by
    intro s h1
    induction h1 with
    | refl => intro _; exact le_refl _
    | @tail b c h1' hstep' ih =>
      intro h2
      have hb2 : Relation.ReflTransGen adm b r := Relation.ReflTransGen.head hstep' h2
      exact le_trans (hle b c (hmid b h1' hb2) (hmid c (h1'.tail hstep') h2) hstep') (ih hb2)
  have h1 : ρ r ≤ ρ t := walk r hrest Relation.ReflTransGen.refl
  have h2 : ρ t < ρ r := hlt r t hCr (hmid t Relation.ReflTransGen.refl hrest) hstep hK
  omega

/-- The rank certificate as a statement about the subshift. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem coreClosed_of_rankOn {a M : ℕ} (C K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hcyc : ∀ r, Relation.TransGen (Step a M) r r → C r)
    (hle : ∀ r t, C r → C t → Step a M r t → ρ t ≤ ρ r)
    (hlt : ∀ r t, C r → C t → Step a M r t → ¬ K r → ρ t < ρ r) :
    CoreClosed a M K :=
  fun _ hr => transGen_self_of_rank C K ρ hcyc hle hlt hr

/-- Reversing a chain of steps.  Used only to turn a cycle into a cycle for the reversed
relation, which is what lets the same rank argument run backwards. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem transGen_swap {α : Type*} {r : α → α → Prop} {x y : α}
    (h : Relation.TransGen r x y) : Relation.TransGen (Function.swap r) y x := by
  induction h with
  | single hxy => exact Relation.TransGen.single hxy
  | tail _ hbc ih => exact Relation.TransGen.head hbc ih

/-- **The rank certificate with the arrow reversed.**  A cycle stays a cycle when every step is
reversed, so a rank that never *decreases* along a step inside `C` and strictly increases into
every state of `C` outside `K` also forbids cycles outside `K`.

The point is that forward and backward peeling certify different things and the ladder needs
both: the forward-survivor set of a rung is much larger than its core (at `p = 29`, `2 704 992`
against `748 621`), and it is the backward pass applied *to the forward survivors* that closes
the gap exactly. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem coreClosed_of_rankRevOn {a M : ℕ} (C K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hcyc : ∀ r, Relation.TransGen (Step a M) r r → C r)
    (hle : ∀ r t, C r → C t → Step a M r t → ρ r ≤ ρ t)
    (hlt : ∀ r t, C r → C t → Step a M r t → ¬ K t → ρ r < ρ t) :
    CoreClosed a M K := by
  intro r hr
  exact transGen_self_of_rank (adm := Function.swap (Step a M)) C K ρ
    (fun v h => hcyc v (transGen_swap h)) (fun v t hv ht hst => hle t v ht hv hst)
    (fun v t hv ht hst hK => hlt t v ht hv hst hK) (transGen_swap hr)

/-- The rank certificate with no candidate set — usable at a modulus small enough to enumerate,
which is how the bottom rung of the ladder is discharged. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem coreClosed_of_rank {a M : ℕ} (K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hle : ∀ r t, Step a M r t → ρ t ≤ ρ r)
    (hlt : ∀ r t, Step a M r t → ¬ K r → ρ t < ρ r) :
    CoreClosed a M K :=
  coreClosed_of_rankOn (fun _ => True) K ρ (fun _ _ => trivial) (fun r t _ _ => hle r t)
    (fun r t _ _ => hlt r t)

/-- The bottom-rung check in the shape `decide` can run: quantified over digits, not over target
states. -/
def RankOK (a M : ℕ) (K : ZMod M → Prop) (ρ : ZMod M → ℕ) : Prop :=
  ∀ r : ZMod M, Cop M r → ∀ d < a, Cop M ((a : ZMod M) * r + (d : ZMod M)) →
    ρ ((a : ZMod M) * r + (d : ZMod M)) ≤ ρ r ∧
      (¬ K r → ρ ((a : ZMod M) * r + (d : ZMod M)) < ρ r)

-- The unfolded `RankOK` is a nest of bounded quantifiers; instance search needs room.
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 1000000

/-- `RankOK` is a finite check. -/
instance (a M : ℕ) [NeZero M] (K : ZMod M → Prop) [DecidablePred K] (ρ : ZMod M → ℕ) :
    Decidable (RankOK a M K ρ) := by
  unfold RankOK
  infer_instance

@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem coreClosed_of_rankOK {a M : ℕ} (K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (h : RankOK a M K ρ) : CoreClosed a M K := by
  refine coreClosed_of_rank K ρ ?_ ?_
  · rintro r t ⟨hr, ht, d, hd, rfl⟩
    exact (h r hr d hd ht).1
  · rintro r t ⟨hr, ht, d, hd, rfl⟩ hK
    exact (h r hr d hd ht).2 hK

/-! ### The projection carries cycles downwards -/

/-- **Admissible steps project.**  For `M' ∣ M` the ring homomorphism `ZMod M →+* ZMod M'`
sends an edge of the base-`a` coprimality subshift modulo `M` to an edge modulo `M'`: units map
to units under a ring homomorphism, and `t = a·r + d` is preserved because `a` and `d` are
natural-number casts. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem step_proj {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) {r t : ZMod M}
    (h : Step a M r t) :
    Step a M' (ZMod.castHom hdvd (ZMod M') r) (ZMod.castHom hdvd (ZMod M') t) := by
  obtain ⟨hr, ht, d, hd, rfl⟩ := h
  refine ⟨(cop_iff_isUnit _).mpr (RingHom.isUnit_map _ ((cop_iff_isUnit r).mp hr)),
    (cop_iff_isUnit _).mpr (RingHom.isUnit_map _ ((cop_iff_isUnit _).mp ht)), d, hd, ?_⟩
  simp only [map_add, map_mul, map_natCast]

/-- Chains of admissible steps project. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem transGen_proj {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) {r t : ZMod M}
    (h : Relation.TransGen (Step a M) r t) :
    Relation.TransGen (Step a M') (ZMod.castHom hdvd (ZMod M') r)
      (ZMod.castHom hdvd (ZMod M') t) := by
  induction h with
  | single hst => exact Relation.TransGen.single (step_proj hdvd hst)
  | tail _ hst ih => exact ih.tail (step_proj hdvd hst)

/-- **Cycles project.**  A residue lying on a cycle modulo `M` projects to a residue lying on a
cycle modulo `M'` — the fact the whole ladder rests on. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem onCycle_proj {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) {r : ZMod M}
    (h : Relation.TransGen (Step a M) r r) :
    Relation.TransGen (Step a M') (ZMod.castHom hdvd (ZMod M') r)
      (ZMod.castHom hdvd (ZMod M') r) :=
  transGen_proj hdvd h

/-- **Pull a core-closedness certificate back along the projection.**  If `K'` catches every
cycle modulo `M'`, then its preimage catches every cycle modulo `M`.  This is already a valid
`CoreClosed` certificate — just a very coarse one; the point of the rung below is to shrink it. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem coreClosed_comap {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M)
    {K' : ZMod M' → Prop} (hK' : CoreClosed a M' K') :
    CoreClosed a M (fun r => K' (ZMod.castHom hdvd (ZMod M') r)) :=
  fun _ hr => hK' _ (onCycle_proj hdvd hr)

/-! ### The rung -/

/-- **One rung of the ladder.**  Given a core-closedness certificate `K'` at the smaller modulus
`M'`, a rank function on the preimage `π⁻¹(K')` upgrades it to a core-closedness certificate `K`
at `M`.

The two rank conditions are only ever asked about residues whose projection lies in `K'`, so the
work is `|K'| · (M / M') · a` and not `M · a`; see `DubC.forall_of_forall_lift` for the
enumeration that makes that concrete. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_ladder"]
theorem coreClosed_of_ladder {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M)
    (K' : ZMod M' → Prop) (hK' : CoreClosed a M' K')
    (K : ZMod M → Prop) (ρ : ZMod M → ℕ)
    (hle : ∀ r t, K' (ZMod.castHom hdvd (ZMod M') r) → K' (ZMod.castHom hdvd (ZMod M') t) →
      Step a M r t → ρ t ≤ ρ r)
    (hlt : ∀ r t, K' (ZMod.castHom hdvd (ZMod M') r) → K' (ZMod.castHom hdvd (ZMod M') t) →
      Step a M r t → ¬ K r → ρ t < ρ r) :
    CoreClosed a M K :=
  coreClosed_of_rankOn (fun r => K' (ZMod.castHom hdvd (ZMod M') r)) K ρ
    (fun _ hr => hK' _ (onCycle_proj hdvd hr)) hle hlt

/-! ### Enumerating a fibre: why the rung is finite -/

/-- **The fibre of the projection is `M / M'` explicit residues.**  Every `r : ZMod M` is
`r'.val + k·M'` for its own projection `r'` and a unique `k < M / M'`. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem exists_lift {M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) (r : ZMod M) :
    ∃ k < M / M', r = (((ZMod.castHom hdvd (ZMod M') r).val + k * M' : ℕ) : ZMod M) := by
  have hM' : 0 < M' := Nat.pos_of_ne_zero (NeZero.ne M')
  have hval : ((r.val : ℕ) : ZMod M) = r := by simp
  -- the projection of `r` is the reduction of `r.val` modulo `M'`
  have hproj : ZMod.castHom hdvd (ZMod M') r = ((r.val : ℕ) : ZMod M') := by
    conv_lhs => rw [← hval]
    exact map_natCast _ _
  refine ⟨r.val / M', ?_, ?_⟩
  · exact Nat.div_lt_div_of_lt_of_dvd hdvd (ZMod.val_lt r)
  · rw [hproj, ZMod.val_natCast, Nat.mod_add_div', hval]

/-- **The rung quantifier is finite.**  A property of every residue whose projection lies in `K'`
follows from the property of the explicit lifts `r'.val + k·M'`, `K' r'`, `k < M / M'`.  This is
what turns the `2·10¹¹`-element quantifier of `DubC.coreClosed_of_ladder` into a loop of length
`|K'| · (M / M')`. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_ladder"]
theorem forall_of_forall_lift {M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M)
    {K' : ZMod M' → Prop} {P : ZMod M → Prop}
    (h : ∀ r' : ZMod M', K' r' → ∀ k < M / M', P (((r'.val + k * M' : ℕ) : ZMod M))) :
    ∀ r : ZMod M, K' (ZMod.castHom hdvd (ZMod M') r) → P r := by
  intro r hr
  obtain ⟨k, hk, hlift⟩ := exists_lift hdvd r
  rw [hlift]
  exact h _ hr k hk

end DubC
