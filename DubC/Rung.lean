/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Ladder

/-!
# The rung engine: `CoreClosed` from a *computed* rank

`DubC/Ladder.lean` reduces `DubC.CoreClosed a M K` at the `a = 7` modulus
`∏_{p≤31} p ≈ 2·10¹¹` to a chain of rungs, the largest of which has about `2.3·10⁷`
residues.  A rung is still far too large for anything to be *shipped*: the rank function it
needs takes values up to about `700` and is defined on all `2.3·10⁷` of them.  So the rank has
to be **computed by the checker**, and this file supplies the shapes that make that possible
while keeping the trusted reasoning small.

## Three ingredients

**The rank certificate in `ℕ` arithmetic** (`DubC.coreClosed_of_rankNat`).  The candidate set
`C`, the target set `K` and the rank `ρ` all arrive as functions of the *natural number*
`r.val`, so a checker can be written entirely in `ℕ` and `Array`, with a single bridge lemma
(`DubC.val_stepN`) between `ZMod M` arithmetic and `%`.  Nothing about how `C`, `K` and `ρ` are
computed is assumed: they are arbitrary functions, and a wrong one can only make the check fail.

**The same thing backwards** (`DubC.coreClosed_of_rankRevNat`).  Peeling forwards keeps every
state with an infinite *forward* path; that is a much weaker condition than lying on a cycle
(at the `p = 29` rung it leaves `2 704 992` states where the core has `748 621`).  Reversing the
arrow costs nothing mathematically — `Relation.TransGen` cycles are invariant under
`Function.swap` — and the two together are exactly right:

> if `F` is the forward-survivor set of `C` and `B` the backward-survivor set of `F`, then `B`
> is precisely the set of states of `C` with an infinite path in *both* directions.

That is why the ladder needs **two** rank certificates per rung and not an unbounded
alternation: a third stage is provably empty, and the C prototype `DubC/grid2.c` confirms it
kills nothing at any of the four rungs.

**The nested enumeration** (`DubC.forall_lift_nat`).  A hypothesis of the form
`∀ x < M, Cn x = true → P x` must not be *checked* by running `x` over `M ≈ 2·10¹¹` values.
Because `M = M' · p` and the level-`M` predicate is built as `Cn y = Cn' (y % M') && …`, the
quantifier splits into `x < M'` with `Cn' x` and `k < p` — and recursively down the ladder, so
the check is a nest of small loops whose total length is the *grid size*, not the modulus.

## What is trusted

Exactly what is trusted in `DubC/Y31.lean`: the arithmetic bridges, and nothing about the
witness.  `C`, `K` and `ρ` are whatever the engine computed; every rung obligation is a
decidable statement about those values, checked as written.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
-/

namespace DubC

/-! ### Bridges between `ZMod M` and `ℕ` arithmetic -/

/-- One subshift step, in `ℕ` arithmetic. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem val_stepN {a M : ℕ} [NeZero M] (r : ZMod M) (d : ℕ) :
    ((a : ZMod M) * r + (d : ZMod M)).val = (a * r.val + d) % M := by
  have h : (a : ZMod M) * r + (d : ZMod M) = ((a * r.val + d : ℕ) : ZMod M) := by
    push_cast; simp
  rw [h, ZMod.val_natCast]

/-- The projection to a divisor modulus, in `ℕ` arithmetic. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem val_proj {M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) (r : ZMod M) :
    (ZMod.castHom hdvd (ZMod M') r).val = r.val % M' := by
  have hval : ((r.val : ℕ) : ZMod M) = r := by simp
  have hproj : ZMod.castHom hdvd (ZMod M') r = ((r.val : ℕ) : ZMod M') := by
    conv_lhs => rw [← hval]
    exact map_natCast _ _
  rw [hproj, ZMod.val_natCast]

/-- Pulling a certificate back along the projection, in `ℕ` arithmetic: this is what starts
every rung, with `C = π⁻¹(K')`. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem coreClosed_comapN {a M M' : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) (Kn' : ℕ → Bool)
    (hK' : CoreClosed a M' (fun r => Kn' r.val = true)) :
    CoreClosed a M (fun r => Kn' (r.val % M') = true) := by
  intro r hr
  have h : Kn' (ZMod.castHom hdvd (ZMod M') r).val = true := coreClosed_comap hdvd hK' r hr
  rwa [val_proj hdvd] at h

/-- A residue coprime to `M` is not divisible by any `q > 1` dividing `M`.  This is what lets a
checker discard four of the seven digits with a `%` test: `t = 7r + d` is a unit, hence odd and
not a multiple of `7`, which forces `d ∈ {2,4,6}`. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem mod_ne_zero_of_cop {y M q : ℕ} (hq : 1 < q) (hdvd : q ∣ M) (h : Nat.Coprime y M) :
    y % q ≠ 0 := by
  intro hmod
  have hqy : q ∣ y := Nat.dvd_of_mod_eq_zero hmod
  have hq1 : q ∣ Nat.gcd y M := Nat.dvd_gcd hqy hdvd
  rw [h, Nat.dvd_one] at hq1
  omega

/-! ### The rank certificate in `ℕ` arithmetic -/

/-- The two digit guards, extracted from the admissibility of a step.  An admissible successor
`t = 7r + d` is coprime to `M`, hence odd and not a multiple of `7`; since `2 ∣ M` and `7 ∣ M`
that pins the digit down to `d ∈ {2,4,6}` and does so by arithmetic on `d` and `x` alone — the
checker never has to compute `t` for the other four digits. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem digit_guards {M x d : ℕ} (h2 : 2 ∣ M) (h7 : 7 ∣ M)
    (hc : Nat.Coprime ((7 * x + d) % M) M) : d ≠ 0 ∧ (x + d) % 2 = 1 := by
  have e2 : (7 * x + d) % M % 2 = (7 * x + d) % 2 := Nat.mod_mod_of_dvd _ h2
  have e7 : (7 * x + d) % M % 7 = (7 * x + d) % 7 := Nat.mod_mod_of_dvd _ h7
  have n2 := mod_ne_zero_of_cop one_lt_two h2 hc
  have n7 := mod_ne_zero_of_cop (by norm_num) h7 hc
  rw [e2] at n2
  rw [e7] at n7
  omega

/-- **A computed rank certifies `CoreClosed`.**  `Cn` is a candidate set already known to catch
every cycle, `Kn` the smaller set to be certified, `rho` a rank: along an admissible step inside
`Cn` the rank does not increase, and it strictly drops out of a state of `Cn` outside `Kn`.

Everything is phrased in `ℕ`, so the three data can be `Array` lookups, and *nothing* is assumed
about how they were obtained — a wrong witness can only make the check fail. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem coreClosed_of_rankNat {M : ℕ} [NeZero M] (h2 : 2 ∣ M) (h7 : 7 ∣ M)
    (Cn Kn : ℕ → Bool) (rho : ℕ → ℕ)
    (hcyc : CoreClosed 7 M (fun r => Cn r.val = true))
    (hchk : ∀ x < M, Cn x = true → ∀ d < 7, d ≠ 0 → (x + d) % 2 = 1 →
      Cn ((7 * x + d) % M) = true →
        rho ((7 * x + d) % M) ≤ rho x ∧
          (Kn x = false → rho ((7 * x + d) % M) < rho x)) :
    CoreClosed 7 M (fun r => Kn r.val = true) := by
  refine coreClosed_of_rankOn (fun r => Cn r.val = true) _ (fun r => rho r.val) hcyc ?_ ?_
  · rintro r t hr ht ⟨-, hct, d, hd, rfl⟩
    have hc : Nat.Coprime ((7 * r.val + d) % M) M := by rw [← val_stepN]; exact hct
    obtain ⟨g1, g2⟩ := digit_guards h2 h7 hc
    rw [val_stepN] at ht ⊢
    exact (hchk r.val (ZMod.val_lt r) hr d hd g1 g2 ht).1
  · rintro r t hr ht ⟨-, hct, d, hd, rfl⟩ hK
    have hc : Nat.Coprime ((7 * r.val + d) % M) M := by rw [← val_stepN]; exact hct
    obtain ⟨g1, g2⟩ := digit_guards h2 h7 hc
    rw [val_stepN] at ht ⊢
    refine (hchk r.val (ZMod.val_lt r) hr d hd g1 g2 ht).2 ?_
    simpa using hK

/-- **The same certificate with the arrow reversed.**  A cycle is a cycle for the reversed
relation, so a rank that strictly *increases* into every state of `Cn` outside `Kn` also forbids
cycles outside `Kn`.  This is the backward peeling stage. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem coreClosed_of_rankRevNat {M : ℕ} [NeZero M] (h2 : 2 ∣ M) (h7 : 7 ∣ M)
    (Cn Kn : ℕ → Bool) (rho : ℕ → ℕ)
    (hcyc : CoreClosed 7 M (fun r => Cn r.val = true))
    (hchk : ∀ x < M, Cn x = true → ∀ d < 7, d ≠ 0 → (x + d) % 2 = 1 →
      Cn ((7 * x + d) % M) = true →
        rho x ≤ rho ((7 * x + d) % M) ∧
          (Kn ((7 * x + d) % M) = false → rho x < rho ((7 * x + d) % M))) :
    CoreClosed 7 M (fun r => Kn r.val = true) := by
  refine coreClosed_of_rankRevOn (fun r => Cn r.val = true) _ (fun r => rho r.val) hcyc ?_ ?_
  · rintro r t hr ht ⟨-, hct, d, hd, rfl⟩
    have hc : Nat.Coprime ((7 * r.val + d) % M) M := by rw [← val_stepN]; exact hct
    obtain ⟨g1, g2⟩ := digit_guards h2 h7 hc
    rw [val_stepN] at ht ⊢
    exact (hchk r.val (ZMod.val_lt r) hr d hd g1 g2 ht).1
  · rintro r t hr ht ⟨-, hct, d, hd, rfl⟩ hK
    have hc : Nat.Coprime ((7 * r.val + d) % M) M := by rw [← val_stepN]; exact hct
    obtain ⟨g1, g2⟩ := digit_guards h2 h7 hc
    rw [val_stepN] at ht hK ⊢
    refine (hchk r.val (ZMod.val_lt r) hr d hd g1 g2 ht).2 ?_
    simpa using hK

/-- Condition (a) is automatic for the units, in the `ℕ` form the rung engine uses: this is what
starts the ladder at the bottom modulus. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem coreClosed_copN (a M : ℕ) :
    CoreClosed a M (fun r => decide (Nat.Coprime r.val M) = true) := by
  intro r h
  simp only [decide_eq_true_eq]
  exact coreClosed_cop a M r h

/-! ### The nested enumeration -/

/-- **Splitting the rung quantifier.**  If the level-`M` predicate refines the level-`M'` one
(`hsub`), a statement about every `y < M` with `Cn y` follows from the statement about the
explicit lifts `x + k·M'` with `x < M'`, `Cn' x` and `k < p`.  Iterating this down the ladder
turns one quantifier over `2·10¹¹` residues into a nest of loops of total length the grid
size. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem forall_lift_nat {M M' p : ℕ} (hM : M = M' * p) (hM' : 0 < M') (Cn' Cn : ℕ → Bool)
    (hsub : ∀ y, Cn y = true → Cn' (y % M') = true) {P : ℕ → Prop}
    (h : ∀ x < M', Cn' x = true → ∀ k < p, Cn (x + k * M') = true → P (x + k * M')) :
    ∀ y < M, Cn y = true → P y := by
  intro y hy hCy
  have hlt : y % M' < M' := Nat.mod_lt _ hM'
  have hk : y / M' < p := by
    subst hM; exact Nat.div_lt_of_lt_mul hy
  have hsplit : y % M' + y / M' * M' = y := Nat.mod_add_div' y M'
  have := h (y % M') hlt (hsub y hCy) (y / M') hk (by rw [hsplit]; exact hCy)
  rwa [hsplit] at this

/-- **The candidate set of a rung.**  The core one level down, pulled back along the projection,
*intersected with the units at the new prime*.  Both halves are needed: a residue divisible by
`p` is not a state of the subshift at all, but it does have subshift states among its formal
successors, so leaving it in the candidate set would ask the rank to drop below `0` there and no
rank could pass. -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem coreClosed_comapUnitN {a M M' p : ℕ} [NeZero M] [NeZero M'] (hdvd : M' ∣ M) (hp : p ∣ M)
    (hp1 : 1 < p) (Kn' : ℕ → Bool) (hK' : CoreClosed a M' (fun r => Kn' r.val = true)) :
    CoreClosed a M (fun r => (Kn' (r.val % M') && decide (r.val % p ≠ 0)) = true) := by
  intro r hr
  have h1 : Kn' (r.val % M') = true := coreClosed_comapN hdvd Kn' hK' r hr
  have hcop : Nat.Coprime r.val M := coreClosed_cop a M r hr
  have h2 : r.val % p ≠ 0 := mod_ne_zero_of_cop hp1 hp hcop
  simp [h1, h2]

/-- The refinement hypothesis of `DubC.forall_lift_nat` for the shape the engine produces:
the level-`M` predicate is the level-`M'` one conjoined with a local test. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem sub_of_and {M' : ℕ} (Cn' : ℕ → Bool) (loc : ℕ → Bool) :
    ∀ y, (Cn' (y % M') && loc y) = true → Cn' (y % M') = true :=
  fun _ h => (Bool.and_eq_true _ _ |>.mp h).1

/-! ### A tail-recursive bounded `∀`

`decide`'s own bounded quantifier instances build the proof term for every index, which is not
an option at `10⁷` indices.  This one is a plain loop and its only use is through
`DubC.allLt_spec`. -/

/-- `allLtAux f k i` tests `f` on `i, i+1, …, i+k-1`.  Tail-recursive, so it compiles to a
loop. -/
def allLtAux (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, i => if f i then allLtAux f k (i + 1) else false

@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem allLtAux_spec {f : ℕ → Bool} : ∀ {k i j : ℕ}, allLtAux f k i = true → i ≤ j →
    j < i + k → f j = true := by
  intro k
  induction k with
  | zero => intro i j _ _ hji; omega
  | succ k ih =>
    intro i j h hij hji
    by_cases hfi : f i = true
    · rw [allLtAux, ite_eq_left hfi] at h
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact hfi
      · exact ih h hlt (by omega)
    · rw [allLtAux, ite_eq_right hfi] at h
      exact absurd h (by simp)

/-- Bounded `∀` as a loop. -/
def allLt (n : ℕ) (f : ℕ → Bool) : Bool := allLtAux f n 0

@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem allLt_spec {n : ℕ} {f : ℕ → Bool} (h : allLt n f = true) : ∀ j < n, f j = true :=
  fun _ hj => allLtAux_spec h (Nat.zero_le _) (by omega)

/-! ### The per-state check

`inf x = (g, c)` is the *whole* downward pass at once: `g` is the grid index of `x` at this
level and `c` says whether `x` lies in the candidate set.  Computing them together is what keeps
the cost of a state linear in the depth of the ladder rather than quadratic — the level-`j`
predicate mentions the level-`j-1` predicate, which mentions the level-`j-2` one, and evaluating
those separately would re-walk the whole chain for each. -/

/-- The forward check at one state: along every admissible digit the rank does not increase, and
it strictly drops unless `x` itself survives (rank `= cap`). -/
def rungChkF (M cap : ℕ) (inf : ℕ → ℕ × Bool) (A : Array ℕ) (x : ℕ) : Bool :=
  let ix := inf x
  if !ix.2 then true else
  let rx := A.getD ix.1 0
  let kx := rx == cap
  allLt 7 fun d =>
    if d == 0 then true
    else if (x + d) % 2 != 1 then true
    else
      let iy := inf ((7 * x + d) % M)
      if iy.2 then
        let ry := A.getD iy.1 0
        decide (ry ≤ rx) && (kx || decide (ry < rx))
      else true

@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem rungChkF_spec {M cap : ℕ} {inf : ℕ → ℕ × Bool} {A : Array ℕ} {x : ℕ}
    (h : rungChkF M cap inf A x = true) (hx : (inf x).2 = true) :
    ∀ d < 7, d ≠ 0 → (x + d) % 2 = 1 → (inf ((7 * x + d) % M)).2 = true →
      A.getD (inf ((7 * x + d) % M)).1 0 ≤ A.getD (inf x).1 0 ∧
        (((inf x).2 && (A.getD (inf x).1 0 == cap)) = false →
          A.getD (inf ((7 * x + d) % M)).1 0 < A.getD (inf x).1 0) := by
  intro d hd hd0 hpar hy
  rw [rungChkF, hx] at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  have hb := allLt_spec h d hd
  simp only [beq_iff_eq, hd0, ↓reduceIte, hpar, bne_self_eq_false, Bool.false_eq_true,
    hy, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
  refine ⟨hb.1, fun hK => ?_⟩
  rcases hb.2 with hk | hlt
  · rw [hx, hk] at hK; simp at hK
  · exact hlt

/-- The backward check at one state, against the candidate set "survived the forward stage". -/
def rungChkB (M cap : ℕ) (inf : ℕ → ℕ × Bool) (F B : Array ℕ) (x : ℕ) : Bool :=
  let ix := inf x
  if !(ix.2 && (F.getD ix.1 0 == cap)) then true else
  let rx := B.getD ix.1 0
  allLt 7 fun d =>
    if d == 0 then true
    else if (x + d) % 2 != 1 then true
    else
      let iy := inf ((7 * x + d) % M)
      if iy.2 && (F.getD iy.1 0 == cap) then
        let ry := B.getD iy.1 0
        decide (rx ≤ ry) && ((ry == cap) || decide (rx < ry))
      else true

@[category API, AMS 11 37, ref "Dub09", group "dubc_rung"]
theorem rungChkB_spec {M cap : ℕ} {inf : ℕ → ℕ × Bool} {F B : Array ℕ} {x : ℕ}
    (h : rungChkB M cap inf F B x = true)
    (hx : ((inf x).2 && (F.getD (inf x).1 0 == cap)) = true) :
    ∀ d < 7, d ≠ 0 → (x + d) % 2 = 1 →
      ((inf ((7 * x + d) % M)).2 && (F.getD (inf ((7 * x + d) % M)).1 0 == cap)) = true →
      B.getD (inf x).1 0 ≤ B.getD (inf ((7 * x + d) % M)).1 0 ∧
        ((((inf ((7 * x + d) % M)).2 && (F.getD (inf ((7 * x + d) % M)).1 0 == cap)) &&
            (B.getD (inf ((7 * x + d) % M)).1 0 == cap)) = false →
          B.getD (inf x).1 0 < B.getD (inf ((7 * x + d) % M)).1 0) := by
  intro d hd hd0 hpar hy
  rw [rungChkB, hx] at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  have hb := allLt_spec h d hd
  simp only [beq_iff_eq, hd0, ↓reduceIte, hpar, bne_self_eq_false, Bool.false_eq_true,
    hy, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
  refine ⟨hb.1, fun hK => ?_⟩
  rcases hb.2 with hk | hlt
  · rw [hy, hk] at hK; simp at hK
  · exact hlt

end DubC
