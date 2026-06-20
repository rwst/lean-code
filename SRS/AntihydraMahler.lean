/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SRS.AntihydraSRSObstruction
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Antihydra ↔ Mahler's 3/2 problem / Z-numbers: connections and non-implications

This file is the **Mahler bridge** for the Antihydra development. The regular-invariant ⟹ bounded-dip
machinery it refers to is **already proved** in `SRS.AntihydraSRSObstruction`
(`RegularInvariant`, `futureDip_bound`, `futureDip_lt_card`, `no_regular_invariant_of_unbounded_dips`,
`no_dfa_invariant_of_unbounded_dips`); the value orbit `valOrbit a₀ = ⌊3·/2⌋`-iterated, the signed
counter `counterZ`, the unary-block counter `orbitCounter`, and the future-dip sequence `futureDip`
all live there. We **reuse** them and add only what connects Antihydra to Mahler's `3/2` problem.

The goal (bbchallenge research note §7): the existence of a finite regular invariant for Antihydra
would force a *uniform bound on future dips* — which is "precisely Mahler-3/2-problem territory".

## Rigorous relationships (proved here)

Write `aₙ = valOrbit a₀ n` (the Antihydra value orbit, `SRS.AntihydraSRS.valOrbit`) and
`pₙ = aₙ mod 2 = valParity a₀ n`.

* **`two_mul_valOrbit_succ_add_parity`**: `2·aₙ₊₁ + pₙ = 3·aₙ`. The Antihydra value map is exactly
  geometric growth by `3/2`, minus a half-unit on odd values.
* **`valOrbit_geometric_identity`**: `3ⁿ·a₀ = 2ⁿ·aₙ + Tₙ`, with `Tₙ = parityWeightedSum a₀ n`
  the `(3/2)`-weighted parity sum `Σ_{k<n} 3^{n-1-k}·2^k·pₖ`. So `(3/2)ⁿ·a₀ − aₙ ≥ 0` is precisely the
  accumulated parity defect: the gap between ideal `3/2`-geometric growth and the floored orbit.
* **`mahler_residue_eq`**: `(3ⁿ·a₀) mod 2ⁿ = Tₙ mod 2ⁿ`. Since `{(3/2)ⁿ·a₀} = ((3ⁿa₀) mod 2ⁿ)/2ⁿ`,
  **the Mahler fractional parts of the pure `3/2`-orbit are the `(3/2)`-weighted Antihydra parities
  mod 1** — the formal point of contact with the "powers of `3/2`" distribution problem (the `a₀ = 1`
  case: is `{(3/2)ⁿ}` dense / equidistributed? — open).

## Rigorous non-relationship (proved here)

Antihydra iterates a floor (`aₙ₊₁ = ⌊3aₙ/2⌋`); Mahler's sequence takes a single floor
(`gₙ = ⌊(3/2)ⁿ·a₀⌋ = mahlerFloor a₀ n`). They genuinely differ: `valOrbit 8 6 = 90` but
`mahlerFloor 8 6 = 91` (`valOrbit_ne_mahlerFloor`), and even their **parities** disagree there
(`valParity_ne_mahlerParity`). Hence the Antihydra parity sequence is **not** the parity sequence of
`⌊(3/2)ⁿ·8⌋`: partial results on the Mahler sequence do not transfer termwise, and Antihydra's
halting test is not literally a Z-number condition for any real `ξ`. No implication is known in
**either** direction between `no_Z_numbers` and Antihydra non-halting.

## The connection, made precise

The existing obstruction shows: a finite (DFA) regular invariant of Antihydra forces the future dips
of the counter to be **bounded** (`futureDip_lt_card`), so **unbounded dips ⟹ no finite-automaton
non-halting proof** (`no_dfa_invariant_of_unbounded_dips`). Here `antihydra_future_dips_unbounded`
records the conjecturally-true statement that the dips *are* unbounded — and that is the
Mahler-3/2-flavoured content (it asserts the `(3/2)`-orbit parities never conspire to keep the
counter's excursions bounded). `antihydra_no_dfa_invariant` is then the proved payoff, instantiating
the existing obstruction with that conjecture (no new `sorry` of its own).

## References
* Mahler, *An unsolved problem on the powers of 3/2*, J. Austral. Math. Soc. **8** (1968) 313–321.
* Flatto, Lagarias, Pollington, *On the range of fractional parts {ξ(p/q)ⁿ}*, Acta Arith. **70**
  (1995) 125–147.
* The Busy Beaver Challenge — *Antihydra*; *Finite Automata Reduction (FAR)* deciders (bbchallenge.org).

See `SRS/AntihydraMahler.md` for the full technical note.
-/

namespace StringRewriting.AntihydraSRS

open StringRewriting StringRewriting.MixedBase ASym Relation

/-! ## The `(3/2)`-geometric bridge (rigorous relationships) -/

/-- The **parity** `aₙ mod 2` of the Antihydra value orbit `valOrbit`. `0` = even step
(counter `+2`), `1` = odd step (counter `−1`). -/
@[category API, AMS 11 37, ref "bbchallenge", group "antihydra_mahler"]
def valParity (a₀ n : ℕ) : ℕ := valOrbit a₀ n % 2

/-- **Defect recurrence** (rigorous relationship): `2·aₙ₊₁ + pₙ = 3·aₙ`. One Antihydra value step
is geometric growth by `3/2`, corrected by a half-unit exactly on odd values. -/
@[category API, AMS 11 37, ref "bbchallenge", group "antihydra_mahler"]
theorem two_mul_valOrbit_succ_add_parity (a₀ n : ℕ) :
    2 * valOrbit a₀ (n + 1) + valParity a₀ n = 3 * valOrbit a₀ n := by
  rw [valOrbit_succ]
  simp only [valStep, valParity]
  omega

/-- The `(3/2)`-**weighted parity sum** `Tₙ = Σ_{k<n} 3^{n-1-k}·2^k·pₖ`, via the recurrence
`T₀ = 0`, `Tₙ₊₁ = 3·Tₙ + 2ⁿ·pₙ`: the gap between ideal geometric growth and the floored orbit. -/
@[category API, AMS 11 37, ref "bbchallenge", group "antihydra_mahler"]
def parityWeightedSum (a₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * parityWeightedSum a₀ n + 2 ^ n * valParity a₀ n

/-- **Geometric identity** (rigorous relationship): `3ⁿ·a₀ = 2ⁿ·aₙ + Tₙ`. Dividing by `2ⁿ`,
`(3/2)ⁿ·a₀ − aₙ = (1/2)·Σ_{k<n}(3/2)^{n-1-k}·pₖ ≥ 0` — the deviation of the Antihydra orbit from
pure `3/2`-geometric growth is exactly the accumulated parity defect `Tₙ`. -/
@[category research solved, AMS 11 37, ref "bbchallenge", group "antihydra_mahler",
  formal_uses two_mul_valOrbit_succ_add_parity]
theorem valOrbit_geometric_identity (a₀ n : ℕ) :
    3 ^ n * a₀ = 2 ^ n * valOrbit a₀ n + parityWeightedSum a₀ n := by
  induction n with
  | zero => simp [valOrbit, parityWeightedSum]
  | succ n ih =>
    have hR1 := two_mul_valOrbit_succ_add_parity a₀ n
    have e2 : 2 ^ (n + 1) * valOrbit a₀ (n + 1) + 2 ^ n * valParity a₀ n
            = 3 * (2 ^ n * valOrbit a₀ n) := by
      have h : 2 ^ (n + 1) * valOrbit a₀ (n + 1)
             = 2 ^ n * (2 * valOrbit a₀ (n + 1)) := by ring
      rw [h, ← mul_add, hR1]; ring
    have e1 : 3 ^ (n + 1) * a₀ = 3 * (2 ^ n * valOrbit a₀ n) + 3 * parityWeightedSum a₀ n := by
      have h : 3 ^ (n + 1) * a₀ = 3 * (3 ^ n * a₀) := by ring
      rw [h, ih]; ring
    simp only [parityWeightedSum]
    linarith [e1, e2]

/-- **Mahler residue bridge** (rigorous relationship): `(3ⁿ·a₀) mod 2ⁿ = Tₙ mod 2ⁿ`. Because
`{(3/2)ⁿ·a₀} = ((3ⁿa₀) mod 2ⁿ)/2ⁿ`, the *Mahler fractional parts* of the pure `3/2`-orbit equal the
`(3/2)`-weighted Antihydra parities mod `1`. This is the formal contact with the "powers of `3/2`"
distribution problem. -/
@[category research solved, AMS 11 37, ref "bbchallenge" "Mahler68", group "antihydra_mahler",
  formal_uses valOrbit_geometric_identity]
theorem mahler_residue_eq (a₀ n : ℕ) :
    (3 ^ n * a₀) % 2 ^ n = parityWeightedSum a₀ n % 2 ^ n := by
  rw [valOrbit_geometric_identity a₀ n, Nat.mul_add_mod]

/-! ## The all-even orbit is impossible — odd values recur (report §4)

The `2`-adic Z-number analogue of Mahler's problem for `f(x) = ⌊3x/2⌋` asks for a nonzero `x` whose
whole orbit stays *even* (parity sequence `≡ 0`); such an `x` would make the counter increase by `2`
forever and the dips eventually vanish. Mahler-style this is "trivially" impossible, and here is the
rigorous integer form: **no positive value has an all-even `⌊3·/2⌋`-orbit**, and in fact **odd values
recur** along every orbit from a seed `≥ 2`. This is a genuine *known* fact about the parity sequence
— the opposite extreme to the conjectural large-deviation `antihydra_future_dips_unbounded`, and (as
the report stresses) it does **not** imply that conjecture: ruling out permanent confinement to the
even cylinder is far weaker than forcing unbounded positive excess of odd steps. -/

/-- If every parity in `[0, n)` is even, the weighted parity sum `Tₙ` vanishes. -/
@[category API, AMS 11 37, ref "bbchallenge", group "antihydra_mahler"]
theorem parityWeightedSum_eq_zero_of_allEven (a₀ n : ℕ)
    (h : ∀ k < n, valParity a₀ k = 0) : parityWeightedSum a₀ n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parityWeightedSum, ih (fun k hk => h k (by omega)), h n (by omega)]
    ring

/-- **No all-even orbit** (rigorous; the `2`-adic-Z-number shadow, report §4): every positive seed
`a₀` produces an **odd** value at some step. If all parities were `0` then `Tₙ = 0`, so the geometric
identity gives `3ⁿa₀ = 2ⁿaₙ`, forcing `2ⁿ ∣ a₀` for all `n` — impossible for `a₀ > 0` once `2ⁿ > a₀`. -/
@[category research solved, AMS 11 37, ref "bbchallenge", group "antihydra_mahler",
  formal_uses valOrbit_geometric_identity parityWeightedSum_eq_zero_of_allEven]
theorem exists_valParity_one (a₀ : ℕ) (h : 0 < a₀) : ∃ n, valParity a₀ n = 1 := by
  by_contra hcon
  push Not at hcon
  have heven : ∀ k, valParity a₀ k = 0 := by
    intro k
    rcases (Nat.mod_two_eq_zero_or_one (valOrbit a₀ k)) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon k)
  have hzero : parityWeightedSum a₀ a₀ = 0 :=
    parityWeightedSum_eq_zero_of_allEven a₀ a₀ (fun k _ => heven k)
  have hid := valOrbit_geometric_identity a₀ a₀
  rw [hzero, add_zero] at hid
  have hdvd : (2:ℕ) ^ a₀ ∣ a₀ :=
    (Nat.Coprime.pow a₀ a₀ (by decide)).dvd_of_dvd_mul_left ⟨valOrbit a₀ a₀, hid⟩
  have hle : (2:ℕ) ^ a₀ ≤ a₀ := Nat.le_of_dvd h hdvd
  have : a₀ < 2 ^ a₀ := Nat.lt_two_pow_self
  omega

/-- **Odd values recur** (rigorous): along every orbit from a seed `≥ 2`, odd values occur at
arbitrarily late steps. (Restart the orbit at `N` — its value `≥ 2` by `valOrbit_ge_two` — and apply
`exists_valParity_one`; `valOrbit_add` reindexes.) So the parity sequence is **not eventually `0`**:
the degenerate "counter grows forever, dips vanish" scenario is impossible. -/
@[category research solved, AMS 11 37, ref "bbchallenge", group "antihydra_mahler",
  formal_uses exists_valParity_one valOrbit_add valOrbit_ge_two]
theorem valParity_one_frequently (a₀ : ℕ) (h : 2 ≤ a₀) :
    ∀ N, ∃ n, N ≤ n ∧ valParity a₀ n = 1 := by
  intro N
  obtain ⟨j, hj⟩ := exists_valParity_one (valOrbit a₀ N) (by have := valOrbit_ge_two h N; omega)
  refine ⟨N + j, Nat.le_add_right N j, ?_⟩
  unfold valParity at hj ⊢
  rw [valOrbit_add]; exact hj

/-! ## Mahler's single-floor sequence `⌊(3/2)ⁿ·a₀⌋`, and the non-relationship -/

/-- **Mahler's `3/2`-sequence** `gₙ = ⌊(3/2)ⁿ·a₀⌋ = 3ⁿ·a₀ / 2ⁿ`. Uses a **single** floor at step
`n` — contrast the *iterated* floor of `valOrbit`. -/
@[category API, AMS 11 37, ref "Mahler68", group "antihydra_mahler"]
def mahlerFloor (a₀ n : ℕ) : ℕ := 3 ^ n * a₀ / 2 ^ n

/-- The parity of Mahler's single-floor sequence `⌊(3/2)ⁿ·a₀⌋`. -/
@[category API, AMS 11 37, ref "Mahler68", group "antihydra_mahler"]
def mahlerParity (a₀ n : ℕ) : ℕ := mahlerFloor a₀ n % 2

/-- Antihydra value orbit at `n = 6` from seed `8`: `8,12,18,27,40,60,90`. -/
@[category API, AMS 11 37, ref "bbchallenge", group "antihydra_mahler"]
theorem valOrbit_eight_six : valOrbit 8 6 = 90 := by decide

/-- Mahler single-floor value `⌊(3/2)⁶·8⌋ = ⌊5832/64⌋ = 91 ≠ 90`. -/
@[category API, AMS 11 37, ref "Mahler68", group "antihydra_mahler"]
theorem mahlerFloor_eight_six : mahlerFloor 8 6 = 91 := by decide

/-- **Non-relationship** (rigorous): iterated floor ≠ single floor — `valOrbit 8 6 = 90` but
`mahlerFloor 8 6 = 91`. The Antihydra orbit is not the Mahler `3/2`-sequence. -/
@[category research solved, AMS 11 37, ref "bbchallenge" "Mahler68", group "antihydra_mahler"]
theorem valOrbit_ne_mahlerFloor : valOrbit 8 6 ≠ mahlerFloor 8 6 := by decide

/-- **Non-relationship** (rigorous), parity form: already the *parities* of the two sequences
disagree at `n = 6` (`90` even vs `91` odd). Hence the Antihydra parity sequence is **not** the
parity sequence of `⌊(3/2)ⁿ·8⌋`, so partial results on the Mahler `3/2`-sequence do not transfer
termwise, and Antihydra's halting test is not literally a Z-number condition for any `ξ`. -/
@[category research solved, AMS 11 37, ref "bbchallenge" "Mahler68", group "antihydra_mahler"]
theorem valParity_ne_mahlerParity : valParity 8 6 ≠ mahlerParity 8 6 := by decide

/-! ## Mahler's Z-number conjecture -/

/-- A **Z-number** (Mahler, 1968): a positive real `ξ` all of whose multiples by a power of `3/2`
have fractional part below `1/2`, i.e. `{ξ·(3/2)ⁿ} ∈ [0, 1/2)` for every `n : ℕ`. -/
@[category API, AMS 11 37, ref "Mahler68", group "mahler_z_numbers"]
def IsZNumber (ξ : ℝ) : Prop :=
  0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2

/-- **Mahler's Z-number conjecture** (Mahler, 1968): **there are no Z-numbers**. A famous **open**
problem, recorded as a `research open` theorem with its proof left as `sorry`. It is the real-`ξ`
analogue of the integer `3/2`-orbit questions above; no implication is known in either direction
between this and Antihydra non-halting (`valParity_ne_mahlerParity` is the obstruction to a naive
reduction). -/
@[category research open, AMS 11 37, ref "Mahler68", group "mahler_z_numbers",
  conjectured_by "Mahler" 1968]
theorem no_Z_numbers : ¬ ∃ ξ : ℝ, IsZNumber ξ := by
  sorry

/-! ## Dips as parity large deviations (report §1)

The drop in the counter over an interval `[n, n+L)` is an exact affine function of the number of
**odd** steps in that interval: `bₙ − b_{n+L} = 3·(odd steps in [n,n+L)) − 2L`. So a future dip
`D(n) = max_L (bₙ − b_{n+L}) ≥ q` happens iff some interval has odd-count `≥ (2L+q)/3`, i.e. an
**excess of odd steps over the equilibrium frequency `2/3`** that grows without bound (each odd step
costs the counter `1`, each even step pays `+2`, so balance is two even per odd). This recasts
"unbounded dips" as a *large-deviation* statement about the `⌊3·/2⌋` parity sequence — the precise
Mahler/`3x+1` input (the report's **Hypothesis M**). -/

/-- **Dip = parity excess** (rigorous, report §1): the counter drop over `[n, n+L)` is
`bₙ − b_{n+L} = 3·Δoddₙ,ₗ − 2L`, where `Δoddₙ,ₗ = oₙ₊ₗ − oₙ` is the number of odd steps in the
interval. Hence `bₙ − b_{n+L} ≥ q ⟺ Δoddₙ,ₗ ≥ (2L + q)/3`. -/
@[category research solved, AMS 11 68, ref "bbchallenge", group "antihydra_mahler",
  formal_uses counterZ_closed evenSteps_add_oddSteps]
theorem counter_drop_eq_parity_excess (b₀ : ℤ) (a₀ n L : ℕ) :
    counterZ b₀ a₀ n - counterZ b₀ a₀ (n + L)
      = 3 * ((oddSteps a₀ (n + L) : ℤ) - oddSteps a₀ n) - 2 * L := by
  rw [counterZ_closed, counterZ_closed]
  have h1 := evenSteps_add_oddSteps a₀ n
  have h2 := evenSteps_add_oddSteps a₀ (n + L)
  have h1' : (evenSteps a₀ n : ℤ) + oddSteps a₀ n = n := by exact_mod_cast h1
  have h2' : (evenSteps a₀ (n + L) : ℤ) + oddSteps a₀ (n + L) = (n : ℤ) + L := by
    exact_mod_cast h2
  omega

/-! ## The connection: unbounded dips is "Mahler-3/2 territory"

`SRS.AntihydraSRSObstruction` proves a finite regular (DFA) invariant forces a **uniform bound** on
the counter's future dips, hence **unbounded dips ⟹ no finite-automaton non-halting proof**. The
remaining content — that Antihydra's dips really are unbounded — is the Mahler-flavoured open part. -/

/-- **The Antihydra counter has unbounded future dips** (expected; the Mahler-3/2-territory content).
Conjectural, recorded with `sorry`.

This is exactly the hypothesis that powers `no_dfa_invariant_of_unbounded_dips`: for the **non-halting**
value-`8` orbit (`hnh`), for every depth `q` some step `n` has counter `≥ q` yet a future downswing
`D(n) ≥ q`. (The non-halting premise is needed: on a halting orbit `orbitCounter` is eventually `0`
and the dips are trivially bounded. It is automatic under any candidate invariant — see
`macroIter_isSome` — so it costs the corollary nothing.)

PROOF SKETCH (heuristic, Mahler territory). By `counterZ_closed` the counter is `b₀ + 2eₙ − oₙ`, a
`{+2,−1}`-walk driven by the parities `pₖ = valParity 8 k` of the `3/2`-orbit. These parities are
conjecturally equidistributed, so the increments `2 − 3pₖ` behave like i.i.d. with mean
`2 − 3·(1/2) = 1/2 > 0`. A positive-drift walk still has, from each fixed `n`, an a.s. finite future
minimum — but the **supremum over all `n`** of the future downswing is a.s. infinite (arbitrarily
deep excursions recur). Hence no single `q` bounds every dip. Making this rigorous needs control of
the distribution of `{(3/2)ⁿ·8}` / the orbit parities (via `mahler_residue_eq`) — the same circle of
problems as Mahler's `3/2` conjecture and the equidistribution of `{(3/2)ⁿ}`. ∎ -/
@[category research open, AMS 68 11 37, ref "bbchallenge" "FLP95" "Mahler68",
  group "antihydra_mahler"]
theorem antihydra_future_dips_unbounded (w₀ : List ASym) (b₀ : ℕ) (h8 : cval w₀ = 8)
    (hnh : ∀ n, ∃ an bn, macroIter n (cval w₀, b₀) = some (an, bn)) :
    ∀ q : ℕ, ∃ n, q ≤ orbitCounter w₀ b₀ n ∧ q ≤ futureDip (orbitCounter w₀ b₀) n := by
  sorry

/-- **Payoff** (proved *structurally* from the existing obstruction): if Antihydra's future dips are
unbounded (the Mahler-territory conjecture `antihydra_future_dips_unbounded`), then **no finite
automaton** recognizes a closed, reachable-containing, halt-free invariant of the value-`8` orbit — a
FAR-style finite-automaton non-halting proof of Antihydra is impossible at any state count. The open
content lives entirely in `antihydra_future_dips_unbounded`; this corollary adds no `sorry` of its
own, it just instantiates `no_dfa_invariant_of_unbounded_dips`. -/
@[category research solved, AMS 68 11, ref "bbchallenge", group "antihydra_mahler",
  formal_uses no_dfa_invariant_of_unbounded_dips antihydra_future_dips_unbounded]
theorem antihydra_no_dfa_invariant
    (w₀ : List ASym) (hw₀ : IsBinary w₀) (b₀ : ℕ) (h8 : cval w₀ = 8)
    {σ : Type} [Fintype σ] (M : DFA ASym σ)
    (reach : ∀ c, ReflTransGen (RewriteStep antihydraSRS) (config w₀ b₀) c → c ∈ M.accepts)
    (closed : ∀ u v, u ∈ M.accepts → RewriteStep antihydraSRS u v → v ∈ M.accepts)
    (noHalt : ∀ c ∈ M.accepts, ¬ IsHalting c) : False := by
  have hreg : RegularInvariant w₀ b₀ M.accepts (Fintype.card σ) :=
    regularInvariant_of_dfa M w₀ b₀ reach closed noHalt
  have hnh := macroIter_isSome w₀ hw₀ b₀ (by omega) hreg
  exact no_dfa_invariant_of_unbounded_dips w₀ hw₀ b₀ (by omega)
    (antihydra_future_dips_unbounded w₀ b₀ h8 hnh) M reach closed noHalt

end StringRewriting.AntihydraSRS
