/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Lake
open Lake DSL

package "lean-code" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5e0c4e5239cb0a2d86d68a884bf52cfd963fce22"

-- Heights, Roth, the Subspace Theorem and its applications, sorry-free and std3 (Tau Ceti rules,
-- module system). Shares this package's Mathlib pin; its `ForMathlib/` must not collide with ours.
require SubspaceTheorems from git
  "https://github.com/rwst/Subspace-Theorems" @ "eefd0e02271a92b02637c33c6f8e29b6439c6b0c"


lean_lib Corpus where
  globs := #[.submodules `Corpus]

lean_lib DistributionModOne where
  globs := #[.submodules `DistributionModOne]

-- Mathlib-bound material: sorry-free, no cited axioms, no in-file corpus attributes.
-- `ForMathlib/Topology/MetricSpace/BoxDimension.lean` is the box-counting (Minkowski) dimension,
-- which Mathlib does not have: `upperBoxDim`/`lowerBoxDim` as the exponential growth rate of
-- `Metric.externalCoveringNumber` (Mathlib 2025) along geometric scales, via
-- `ExpGrowth.expGrowthSup`.  Independence of the ratio is the structural theorem
-- (`upperBoxDimWith_eq`); on top of it sit the upper bound from an explicit cover (with a
-- constant allowed in the radius, the form a tail estimate produces), the matching lower bounds
-- for BOTH the upper and the lower box dimension from separated subsets (through
-- `packingNumber_two_mul_le_externalCoveringNumber`) -- so a strongly separated self-similar set
-- gets a box dimension that *exists* -- submultiplicativity of covering numbers on sumsets -- new,
-- and the reason `dim_B (A+B) <= dim_B A + dim_B B`, hence also `dim_B (A-B) <= dim_B A + dim_B B`
-- since x -> -x is an isometry -- and, in R, that upper box dimension < 1 forces Lebesgue
-- measure zero (no Hausdorff measure involved).  `dimH_le_upperBoxDim` compares with Mathlib's
-- Hausdorff dimension, dim_H A <= dim_B A for A NONEMPTY (dim_B empty = bot while dim_H empty = 0):
-- a cover by N balls of radius eps is admissible for muH[d] and contributes N (2 eps)^d.
-- Three side results are about Mathlib objects
-- only: an optimal *external* cover exists when the covering number is finite (the external
-- analogue of `exists_set_encard_eq_coveringNumber`), and an index shift does not change an
-- exponential growth rate.  Motivation: M1 Lemma 1(iii), Lemma 3 and Corollary 5 of
-- note-1061-M1.html, all three of which `BB61/BoxDim.lean` now states.
-- `ForMathlib/MeasureTheory/MassDistribution.lean` is the companion in the other direction:
-- Mathlib's `Measure.le_hausdorffMeasure` asks for a Frostman condition with constant ONE,
-- and every estimate in practice carries a constant; applying the sharp form to C^-1 . mu
-- reinstates it (`smul_le_hausdorffMeasure_of_frostman`, `le_dimH_of_frostman`).  That is the
-- only general input the Hausdorff LOWER bound of a self-similar set needs; the measure itself
-- is bespoke, and for C(alpha) is built in `BB61/Hausdorff.lean`.
-- `ForMathlib/NumberTheory/TraceLadder.lean`: for an algebraic integer alpha generating a number
-- field, the integer sequences obeying alpha's minimal-polynomial recurrence are EXACTLY the
-- trace ladders h_k = Tr(lambda alpha^k) with lambda in the codifferent
-- d^-1 = {gamma : Tr(gamma Z[alpha]) subset Z} (`isRecSeq_iff_exists_codiff`), and
-- lambda |-> (h_k) is a Z-module isomorphism d^-1 = R = Z^d (`codiffEquivRec`, `recEquivInit`).
-- Three separate inputs, deliberately proved apart: the recurrence holds for EVERY lambda and
-- needs no conjugates (sum f_i alpha^i = f(alpha) = 0 in the field itself, trace is linear);
-- integrality is a tautology once Z[alpha] is spanned by the powers of alpha, propagated forward
-- by monicity; surjectivity is nondegeneracy of the trace form plus dimension count.  Euler's
-- identity d^-1 = f'(alpha)^-1 Z[alpha] is Mathlib's `traceForm_dualSubmodule_adjoin` and is
-- recorded, not reproved.  Motivation: M1 Proposition 15 of note-1061-M1.html, stated in
-- `BB61/TraceLadder.lean`.
-- `ForMathlib/Analysis/Equidistribution/ModOne.lean` gained the perturbation lemma
-- `weylCriterion_of_tendsto_sub_int`: Weyl's criterion does not see a perturbation that vanishes
-- MODULO ONE.  If x_n - y_n - N_n -> 0 for integers N_n then y satisfies Weyl's criterion iff x
-- does -- e(h x_n) = e(h y_n) e(h delta_n), |e(h delta_n) - 1| -> 0 by continuity, and a Cesaro
-- average of a null sequence is null.  Chained with the equivalence to
-- `IsEquidistributedModuloOne` this is what makes "the orbit is u.d." a tail property of any
-- construction whose finite-input changes decay to the integers.  Motivation: M5 Theorem 8 of
-- note-1061-M5.html, stated in `BB61/TailEvent.lean`.
-- `ForMathlib/NumberTheory/RationalAlgebraicInteger.lean`: a rational algebraic integer is a
-- rational integer (Z is integrally closed in Q, and Q -> R is injective), and the negative form
-- that is what gets used: NO algebraic integer is a half-odd-integer, hence cos(pi x) != 0 for
-- every real algebraic integer x.  That single fact is the whole arithmetic of the non-vanishing
-- of an Erdos product (1-p) + p e(x_j) whose ladder lies in Z[alpha].
-- `ForMathlib/NumberTheory/ConjugatePowerSum.lean` gained the companions of its power sums: the
-- ladder sum sum_beta (beta-1)beta^m = Tr((theta-1)theta^m) in Z (a difference of two power sums),
-- the fact that theta occurs exactly once among its conjugates (separability) so that the dominant
-- term SPLITS OFF, and the quantitative consequence -- if the full conjugate sum is an integer and
-- ||f z|| <= B at every non-dominant conjugate, then f(theta) is within (d-1)B of an integer.
-- `ForMathlib/NumberTheory/PisotFractionalParts.lean` is the payoff: the DEFINING PROPERTY of a
-- Pisot number, ||theta^n|| <= C rho^n with rho < 1, which Mathlib does not have, and the same for
-- (theta-1)theta^m -- the ladder that generates the Cantor set C(theta).  Motivation: M5 Theorem 3
-- and Theorem 8 of note-1061-M5.html at ANY degree, stated in `BB61/NonVanishing.lean`.
-- `ForMathlib/Analysis/BoundedVariation/Monotone.lean` fills a second Mathlib gap: Mathlib knows
-- a monotone function has bounded variation (`MonotoneOn.locallyBoundedVariationOn`) but not what
-- that variation IS.  On a closed interval it is the total rise, V = f b - f a, because every
-- admissible sum telescopes; with the antitone mirror and the |f b - f a| form these are the atoms
-- a piecewise-monotone computation needs.  `.../BoundedVariation/Trigonometric.lean` is the one
-- this repository wanted: V(cos 2 pi h x) = V(sin 2 pi h x) = 4h on [0,1], the constant in
-- Koksma's inequality applied to a Weyl sum.  Motivation: M5 Corollary 4's discrepancy floor,
-- assembled in `BB61/DiscrepancyFloor.lean` on `CITED/KoksmaInequality.lean`.
-- `ForMathlib/Combinatorics/NatDensity.lean` is the natural (asymptotic) density of a set of
-- naturals, |A cap [0,n)| / n -> d.  Mathlib has only Schnirelmann density, whose own file lists
-- the asymptotic densities as a TODO, and `MeasureTheory/Function/Intersectivity.lean` carries a
-- second "once we have a natural density API" TODO; this is that piece, in the minimal form the
-- phrase "the proportion of ... tends to d" needs: the counting function, the Prop-valued
-- `HasNatDensity` (existence AND value) with uniqueness, empty/univ, the 0 <= d <= 1 bounds and
-- complementation, the junk-valued `natDensity` behind it, and `hasNatDensity_iff_ratCast`, which
-- lets a rational density value be tested in Q -- what a statement whose partial ratios are
-- rational actually needs.  Motivation: EVG25/, where all three statements of the note (Prop. 6,
-- Question 17, Conjecture 18) are exactly density-1/2 assertions.
-- `ForMathlib/Combinatorics/FineWilf.lean` is the theorem of Fine and Wilf (1965), the periodicity
-- lemma of combinatorics on words, which Mathlib does not have: a word with periods p and q read
-- on a window of length L >= p + q - gcd(p,q) has period gcd(p,q).  Window form
-- (`HasPeriodOn u L p`) because that is what the applications read; `List.fine_wilf` is the
-- one-line list version, phrased with l[i]? so no Inhabited is needed.  Proof = the Euclidean
-- algorithm run on the two periods, with the case q = p + gcd(p,q) -- where subtracting the
-- smaller period leaves nothing to induct on -- done by hand.  The length bound is proved SHARP
-- (`exists_not_hasPeriodOn_gcd`: a^(p-1) b a^(p-1) has periods p and p+1 at length 2p-1), and the
-- corollary the applications want is `eq_shift_of_periodic_of_factor_eq`: two periodic words that
-- agree on ONE window of length p + q agree forever.  Motivation: [M3, Lem. 3.3] of the Bugeaud
-- 10.47 program, whose word half is `BB47/PeriodicOrbits.lean`.
-- `ForMathlib/Dynamics/SymbolicDynamics/Instances.lean` puts the order and action instances on
-- Mathlib's own subshift structure.  Mathlib DOES have a subshift API since 2025
-- (`Mathlib/Dynamics/SymbolicDynamics/Basic.lean`: shift action, cylinders, patterns, forbidden
-- sets, `Subshift`, `LanguageOn`) but that file declares no instances at all, so one cannot write
-- `x in Y`, `Y <= Z` or an intersection of subshifts, and -- the point -- the shift does not act
-- on a subshift, so none of `Dynamics/Minimal.lean` or `Dynamics/Transitive.lean` can see one.
-- This file supplies `SetLike`, `PartialOrder` (by `.ofSetLike`) and `CompleteLattice`, and the
-- scoped `AddAction G (G -> A)` / `AddAction G Y` with their `ContinuousConstVAdd`; the action
-- instances are scoped because `G -> A` is a Pi type, so a pointwise action of G on A would give
-- a competing `Pi.instAddAction`.  Two facts special to subshifts get simp lemmas: bottom is the
-- EMPTY subshift and the join is the plain UNION -- no closure operation, because a union of two
-- closed invariant sets is already one.  No new mathematics; the payoff is that
-- `AddAction.IsMinimal G Y` and `AddAction.IsTopologicallyTransitive G Y` now typecheck and carry
-- Mathlib's lemmas (witnessed by `dense_orbit_of_isMinimal`, `eq_bot_or_eq_of_isMinimal`).
-- This is WP1 of `plans/plan-subshift.html`.
-- `ForMathlib/Dynamics/SymbolicDynamics/{Blocks,Duality}.lean` are WP2 of the same plan: the
-- language-subshift duality, on G = Z with blocks in the `Fin n -> alpha` form the rest of the
-- corpus speaks (Mathlib's `LanguageOn` is a set of `Pattern`s over a `Finset G` support, which is
-- the right generality for a monoid and the wrong currency for words).  `Blocks.lean` has `block`,
-- `language` and `IsLanguage` (factorial + extendable), and proves that the language of any
-- non-empty set of configurations satisfies both -- no topology, no invariance, no finiteness.
-- `Duality.lean` proves the two halves of the correspondence.  (i) A subshift is RECOVERED from
-- its language (`mem_of_forall_block_mem_language`), whence `Subshift.ext_language`: two
-- subshifts with the same language are equal.  This needs only closed + shift-invariant; the
-- witness for each finite window is moved into place by the shift.  (ii) Conversely every
-- factorial extendable language IS a language (`language_ofLanguage`): the word is extended one
-- letter at a time in both directions by `Function.update`, each stage realised as a non-empty
-- closed set of configurations, and a limit taken by compactness of Z -> alpha -- the ONLY place
-- the alphabet must be finite.  `IsLanguage.sub` (sub-blocks of legal blocks are legal) is the
-- workhorse that makes the nested sets decrease.  `ofLanguage_language` closes the round trip,
-- for every subshift including the empty one.
-- `ForMathlib/Dynamics/SymbolicDynamics/OmegaLimit.lean` is WP3: the omega-limit subshift
-- `Omega(u)` of a ONE-SIDED word `u : N -> alpha`, which has no orbit closure of its own because
-- it is not a point of the two-sided full shift.  `IsRecurrentFactor u n v` (`v` occurs at
-- arbitrarily late positions) and `recurrentLanguage u n` live in `ForMathlib.SubwordComplexity`,
-- where one-sided words live, and are DEFINITIONALLY `BB47.Recurrent` / `BB47.recFactorSet`.
-- Over a finite alphabet that language is factorial and two-sided extendable
-- (`isLanguage_recurrentLanguage`), so `Omega u := ofLanguage (recurrentLanguage u)` is a subshift
-- whose language is the recurrent language again (`language_omegaLimitSubshift`) -- i.e.
-- `p_inf(n, u)` is literally the complexity of a subshift.  All four language axioms plus
-- non-emptiness reduce to ONE pigeonhole, `exists_frequently_eq`: if P holds at arbitrarily late
-- positions and f has finite range then some value of f is attained at arbitrarily late positions
-- where P holds.  Out-degree of a Rauzy vertex is that with P i := `factor u n i = v`, in-degree
-- the same with f read one position earlier; BB47's `horizon` is not needed.  The topological
-- identity `Omega u = omegaLimit atTop (shift .) {x}` holds for ANY two-sided extension x of u
-- (nothing asked of x on the negative half-line), with independence of the extension as a
-- corollary; it needs discreteness but no finiteness.  `orbitClosure` of a configuration and its
-- language are here too.  Paid for on the way: `Duality.lean` now states "blocks decide closure"
-- once (`mem_closure_iff_forall_exists_block_eq`), and `factor_comp_succ` moved from
-- `InfiniteComplexity.lean` down to `SubwordComplexity.lean` so this file's imports stay
-- fine-grained.
-- `ForMathlib/Dynamics/SymbolicDynamics/Periodic.lean` is WP5: periodic points, their orbits, and
-- the separation of two periodic orbits.  `IsPeriodicPoint x p` is DEFINITIONALLY
-- `Function.Periodic x (p : Z)`, so Mathlib's periodicity API applies unchanged (in particular
-- `Periodic.int_mul` replaces an integer-multiple induction), while
-- `isPeriodicPoint_iff_shift_eq` gives the dynamical reading: a fixed point of `shift p`.  The
-- orbit of a periodic point is finite, hence closed (T1), hence EQUAL to its own `orbitClosure` --
-- so the periodic orbit needs no second bundled definition, and `orbitClosure_le_of_mem`
-- (`OmegaLimit.lean`) makes it the smallest subshift containing the point.  The content is one
-- transport lemma, `eq_of_forall_natCast_eq`: a periodic point is determined by its positive ray.
-- With it, Fine-Wilf on N (`ForMathlib/Combinatorics/FineWilf.lean`) becomes Fine-Wilf on Z --
-- `eq_shift_of_isPeriodicPoint_of_block_eq`, read both points from their shared block, common
-- period p*q -- and hence `orbit_eq_or_disjoint_language`: two periodic points have the same orbit
-- or their orbits share NO block of length p+q.  That is the word half of [M3, Lem. 3.3]; the
-- counting half against the Rauzy graph is WP6.  Also here, moved down from `Complexity.lean`
-- because they use no complexity at all: `Subshift.exists_common_period` and
-- `finite_iff_exists_common_period` (a point of period Q is determined by its block on [0,Q)).
-- `ForMathlib/Dynamics/SymbolicDynamics/Complexity.lean` is WP4, and it closes gap 1 of the 10.47
-- program: `Subshift.complexity Y n = #L_n(Y)`, and `complexity_omegaLimitSubshift` says
-- `p(n, Omega u) = p_inf(n, u)` -- M1M2 Prop. 2.4.  `BB47.pInf u n = pRecurrent u n` is `rfl`, so
-- the corpus-side statement is a rename (WP8).  Elementary API: p(0)=1, monotone, submultiplicative
-- `p(m+n) <= p(m)p(n)` (a block of length m+n is its two halves).  The engine is the PLATEAU
-- THEOREM: if `p(n+1) = p(n)` then BOTH truncation maps `L_{n+1} -> L_n` are bijective -- they are
-- surjective by extendability, hence injective once the cardinalities agree -- so a legal word of
-- length n has a unique legal extension on EACH side.  Left determinism is the step the one-sided
-- theory of `InfiniteComplexity.lean` has no analogue of (right determinism on Z periodises the
-- forward ray only), and it is free.  `block_eq_of_block_eq` then propagates one block agreement
-- over all of Z by a single `Int.induction_on`, for two points at once; taking the two points equal
-- gives that every point is periodic, taking the two positions equal gives that a point is
-- determined by ONE block of length n+1, whence `Y` is finite with `#Y <= p(n+1)`.  Converse
-- direction: a finite subshift has a period COMMON to all its points (the maps sigma^m restricted
-- to Y live in the finite set Y -> Y, so two agree pointwise -- that half is `Periodic.lean`), and
-- then every block occurs at a position in [0,Q), so `p(n) <= #Y * Q` for all n.  Hence
-- Morse-Hedlund for subshifts: non-empty Y
-- over a finite alphabet is finite iff p(n) <= n for some n iff its points share a period iff p is
-- bounded; contrapositive `add_one_le_complexity_of_infinite` is the floor p(n) >= n+1.  No
-- compactness anywhere.  The "common period" phrasing is deliberate and documented: dropping
-- "common" is equivalent but needs a compactness argument nothing here uses.
-- `ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean` is WP6, and it closes gap 3 of the 10.47
-- program at the ForMathlib level.  The Rauzy graph G_n(X) has the legal n-words as vertices and
-- the legal (n+1)-words as edges, `edgeSrc e = e . Fin.castSucc`, `edgeTgt e = e . Fin.succ`.  It
-- is NOT packaged as a SimpleGraph or Quiver: reachability is `Relation.ReflTransGen` of one-step
-- `Step`, which already carries the induction principle every proof needs -- `mem_of_reach`, the
-- exclusion engine ("a set of vertices closed under out-edges absorbs everything reachable from a
-- member"), is two lines and AXIOM-FREE.  Degrees are free: `IsLanguage.exists_outEdge` /
-- `exists_inEdge` ARE the extendability clauses of `IsLanguage` ([M1M2] Prop. 3.3).  The counting
-- lemma `add_two_le_ncard_of_isRightSpecial` is the first-difference formula
-- `p(n+1)-p(n) = sum (outdeg - 1)` in the only form used: two distinct right-special words force
-- `p(n+1) >= p(n)+2`.  It is proved by DELETING two superfluous edges (`edgeSrc` stays onto), not
-- by summing degrees over the vertex set, which is what lets it run on `Set.ncard` for an
-- arbitrary subshift.  CAPSTONE = [M3, Lem. 3.3]: `orbit_eq_of_pRecurrent_eq` -- if
-- `p_inf(n,u) = n+1` for all n then any two periodic points of `Omega u` lie on the same orbit.
-- THE SHAPE LEMMA IS NOT NEEDED: only its degree half.  At most one word of length p+q is
-- right-special, so it misses one of the two (WP5-disjoint) orbit languages; that orbit is then
-- out-closed, non-empty and proper, which strong connectivity forbids.  TWO CORRECTIONS TO THE
-- PLAN: (1) strong connectivity does NOT follow from Mathlib's `IsTopologicallyTransitive` (it
-- asks only for SOME m in Z; the orbit closure of ...000.0101... has a dense orbit yet no walk
-- from 01 back to 00 -- [M3, Ex. 5.3]); it comes from ONE-SIDEDNESS via
-- `exists_forall_isRecurrentFactor`, the ForMathlib form of `BB47.horizon`.  (2) "cycles iff
-- periodic points" holds in one direction only; the true converse is
-- `mem_of_isPeriodicPoint_of_forall_block_mem` (blocks legal at EVERY length).  Also here:
-- `Subshift.mem_iff_forall_block_mem`, i.e. Y = inverse limit of its Rauzy graphs.  WP8 added the
-- LEFT mirrors `IsLeftSpecial` / `exists_isLeftSpecial` / `add_two_le_ncard_of_isLeftSpecial` /
-- `eq_of_isLeftSpecial` -- same proofs with `edgeTgt` for `edgeSrc`, because both degree sums
-- count L_{n+1} -- so that BB47's left-special statement has a home here too.  DUPLICATION WITH
-- BB47 RESOLVED (WP8): this file is now the single source; `BB47/Rauzy.lean` and
-- `BB47/Degrees.lean` re-export from it and their word-level proofs are retired
-- (`BB47.exists_walk` deleted in favour of `reach_recurrentLanguage`, `BB47.mem_of_outClosed`
-- now one line on `mem_of_reach`, and BB47's degree-sum proof of the unique special block
-- replaced by `exists_isRightSpecial`+`eq_of_isRightSpecial`).
-- `ForMathlib/Dynamics/SymbolicDynamics/Minimal.lean` is WP7, the last of that plan, and it opens
-- gap 4a: minimal subshifts and uniformly recurrent languages, NEITHER of which exists anywhere in
-- Mathlib (`Dynamics/Minimal.lean` defines a minimal ACTION but has no minimal-subsystem theorem,
-- and `UniformlyRecurrent` appears nowhere).  `Subshift.exists_isMinimal_le`: every non-empty
-- subshift over a finite alphabet contains a minimal one.  Zorn runs on `Subshift alpha Z` ITSELF
-- in the order dual, never on carriers -- WP1's `CompleteLattice` hands over the lower bound of a
-- chain as `sInf`, already a subshift, so the only obligation is that it is NON-EMPTY, which is
-- Cantor's intersection theorem for a directed family of non-empty compact closed sets.  That is
-- also the only place the alphabet must be finite.  Then FOUR equivalent descriptions: every orbit
-- dense (`isMinimal_iff_forall_orbitClosure_eq`), every legal word occurs in EVERY point
-- (`isMinimal_iff_occursEverywhere`), bounded gaps, and the word form `IsUniformlyRecurrent` --
-- every v in L occurs in every w in L of some length N(v).  The first two are the duality theorem
-- read in each direction and cost nothing; the last two are interchangeable by index arithmetic
-- (`subword`).  EXACTLY ONE STEP IS A THEOREM: "occurs somewhere in every point" to "occurs within
-- a bounded window", paid for with compactness -- the points seeing v within distance N of the
-- origin form a directed open cover of Y.  The definition of uniform recurrence was not left to
-- judgement: BOTH candidate forms are stated and proved equal, and the bound N depends on v, not
-- only on its length (that would be LINEAR recurrence, strictly stronger).  Also here:
-- `isMinimal_iff_addAction` -- this notion IS Mathlib's `AddAction.IsMinimal Z Y`, the payoff WP1's
-- scoped instances were built for, and non-emptiness cannot be dropped from it because Mathlib's
-- condition is vacuous on the empty subshift; `isUniformlyRecurrent_iff_isMinimal_ofLanguage`, the
-- same equivalence on the language side of the duality; and the dichotomy a FINITE minimal subshift
-- is one periodic orbit, hence an APERIODIC minimal subshift obeys the Morse-Hedlund floor
-- p(n) >= n+1 -- the shape in which [M3, Lem. 3.4] hands its generic point to the complexity count.
-- For 10.47 the entry point is `exists_isMinimal_le_omegaLimitSubshift`: Omega(u) contains a
-- minimal subsystem with uniformly recurrent language, for EVERY u, with no complexity hypothesis.
-- Gap 4b, the Coven-Hedlund classification, stays out of scope by design.
lean_lib ForMathlib where
  globs := #[.submodules `ForMathlib]

lean_lib BertinPisot where
  globs := #[.submodules `BertinPisot]

lean_lib Bugeaud where
  globs := #[.submodules `Bugeaud]

lean_lib WeylCriteria where
  globs := #[.submodules `WeylCriteria]

-- `SRS.AntihydraMachine` is deliberately NOT part of this library: it `import BusyLean`,
-- an external package this workspace does not depend on, so it can never be built here.
-- `SRS/AntihydraSRSaxiom.lean` is the in-repo stand-in.  Every other `SRS/` module is listed.
lean_lib SRS where
  globs := #[
    .one `SRS.AntihydraMahler,
    .one `SRS.AntihydraSRSaxiom,
    .one `SRS.AntihydraSRSForward,
    .one `SRS.AntihydraSRS,
    .one `SRS.AntihydraSRSObstruction,
    .one `SRS.AntihydraSRSSimulation,
    .one `SRS.ArcticInterpretation,
    .one `SRS.Basic,
    .one `SRS.CollatzSimulation,
    .one `SRS.CollatzSRS,
    .one `SRS.ComplexityBound,
    .one `SRS.GeneralizedCollatz,
    .one `SRS.Homogenization,
    .one `SRS.Interpretation,
    .one `SRS.MatrixInterpretation,
    .one `SRS.MixedBaseRepresentation,
    .one `SRS.NRationalSequence,
    .one `SRS.Zantema]

lean_lib CC where
  globs := #[.submodules `CC]

lean_lib CITED where
  globs := #[.submodules `CITED]

lean_lib BL where
  globs := #[.submodules `BL]

lean_lib B3 where
  globs := #[.submodules `B3]

lean_lib L90 where
  globs := #[.submodules `L90]

lean_lib RT where
  globs := #[.submodules `RT]

-- Author-original results for research-program.html Part I (paradoxical Collatz
-- sequences).  Files live in ./paradoxical/ (a research dir with PDFs/HTML/Python);
-- globbed like the other libs (module namespace = the lowercase dir name).
lean_lib Paradoxical where
  globs := #[.submodules `paradoxical]

-- "Three halves": M4/A3 program (plan-M4A3.html) — subword complexity of the
-- (3/2)^n steering word.  Extract.lean corpusRoots registration: user's call.
lean_lib TH where
  globs := #[.submodules `TH]

-- Flatto–Lagarias–Pollington ⅓-spread theorem (plan-FLT.html, ref "FLP95") —
-- milestone M3 of the (3/2)ⁿ equidistribution ladder.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib FLP where
  globs := #[.submodules `FLP]

-- Rational base number system 3/2 (plans plan-B1E2.html + plan-B2A2.html, refs
-- "AFS08"/"Dub09") — the orbit ⌈3x/2⌉, its minimal word g_{3/2}, and K = ω_{3/2}.
-- Shared root of both plans.  Build-only registration; Extract.lean corpusRoots
-- registration + db regen: user's call.
lean_lib RB where
  globs := #[.submodules `RB]

-- Forman–Shapiro 1967 / [DubOst06] Conjecture 2 for ⌊ξ·aⁿ⌋ (plan-dubC1.html, refs
-- "Dub09"/"DubOst06"/"DN05") — milestone M1′: the [Dub09] Thm 4 return engine, the digit
-- dynamics, and the C(𝒫) zero-entropy certificate.  Experimental C/Python engines live in
-- the same directory.  Build-only registration; Extract.lean corpusRoots registration + db
-- regen: user's call.
lean_lib DubC where
  globs := #[.submodules `DubC]

-- An unavoidable divisor set for the *nearest* integer ⌊ξ(3/2)ⁿ + 1/2⌋ (plans/plan-dubC2.html,
-- refs "DN05"/"Dub09AA"/"Dub08MN") — the case [DN05] Thm 4 conspicuously omits, its neighbours
-- 7, 5/3, 7/5 being done there.  The driven-carry product subshift (2-adic × odd residues ×
-- interval cells); survivors die to [DN05] Lemma 2, already proved ν-generally as
-- Z32.not_isEventuallyPeriodic_carry, so no Euler-return step is needed.  Imports Z32 (carry
-- formalism, BlockCert cell certificates, SmallInterval arc killer) and DubC's abstract
-- certificate layer only — never DubC.ReturnEngine.  Build-only registration; Extract.lean
-- corpusRoots registration + db regen: user's call.
lean_lib DubC2 where
  globs := #[.submodules `DubC2]

-- Odagiri, "Finite graph certificates for composite terms in rational floor sequences"
-- (plans/plan-oda26.html, ref "Oda26", papers/odagiri2026-floor-certificates.pdf): every provable
-- result of the paper other than its three certificate computations — recurrent carries force
-- composites (Thm 46/50), the (6t+3)/(6t+1) halting equivalence (Thm 58), long prime prefixes
-- (Thm 68), the pseudo-orbit obstructions and prime budget (Thms 39, 42, 44), the waiting time
-- (Thm 3), the word-graph layer and the normal form (Thm 37).  Reuses Z32's carry formalism.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib Oda26 where
  globs := #[.submodules `Oda26]

-- Carry graphs (plans/plan-carry.html, refs "LM95"/"BJG09"): ONE object behind the certificate
-- digraphs of Z32/, DubC/, DubC2/, Oda26/ — finitely branching labelled digraphs, their
-- reachability/rank/core/entropy/sofic theory, and covers of dynamical systems.  Imports only
-- Mathlib + ForMathlib; never mentions certificates.  CarryBridge/ holds the per-root bridges.
-- Supersedes the preliminary CG/ (deleted at M7, archive old-plans/CG-preliminary-2026-10-11.tar.gz).
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib CarryGraph where
  globs := #[.submodules `CarryGraph]

lean_lib CarryBridge where
  globs := #[.submodules `CarryBridge]

-- The (3/2)ⁿ confinement atlas (plans/plan-cert32.html, refs "FLP95"/"Dub09AA") — milestone M1:
-- the floor-residue ⟺ cell dictionary, the five FLP95 Cor 1.4a escape certificates, and T1
-- (residue non-capture mod m ≥ 3); milestone M1-bis: Dubickas 2009 (Acta Arith. 137), no
-- Z_{p/q}(s,s+1/p) is nonempty when 1 < q < p < q², for every real s.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib Z32 where
  globs := #[.submodules `Z32]

-- Bugeaud Problem 10.13 (plan-1013.html, refs "Bug12"/"DD90") — bound #{n : ‖(3/2)ⁿ‖<(3/4)ⁿ}.
-- M2/D1 elementary gap-principle layer: §3 gap identity, linkage lemma, O(log N) tower count.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB13 where
  globs := #[.submodules `BB13]

-- Bugeaud Problem 10.6 (plans/plan-BB6-paper.html, refs "Bug12"/"Bos83"/"Kat16") — the
-- calibration: every reading of "very rapidly increasing" that constrains only the size or the
-- sparsity of the sequence is vacuous, because runs of consecutive integers answer all of them.
-- WP2 layer: Lemma R (runs ⟹ universally densifying), Theorem A(i)–(iii) on one dyadic-block
-- construction, and Corollary A′ — which proves `Bugeaud06.problem_10_6_variant_2` verbatim and
-- std3, de-axiomatizing the two Katz axioms in its recorded proof.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB6 where
  globs := #[.submodules `BB6]

-- Third-party port: reusable infrastructure lifted from `shaikidris/CET` v2.0.1
-- (Apache-2.0, © Idris Ali Shaik), adapted from Lean 4.15.0 to this toolchain.
-- Two independent groups: (a) the (C,D)-density / dyadic-shell API of Inselmann
-- arXiv:2402.03276 Def. 2.6, which this corpus lacked entirely; (b) the Syracuse
-- numerator on compositions with its fixed-length injectivity and the residue-fiber
-- spacing bound.  Deliberately NOT ported: their Terras parity bijection (we already
-- have `CC.terras_bijection`) and the whole endpoint-transport bootstrap, whose
-- headline claim is unverified here.  Build-only registration; Extract.lean
-- corpusRoots registration + db regen: user's call.
lean_lib CET where
  globs := #[.submodules `CET]


-- The T-shift problem (plan-A6+ C7, σ-ledger): exponential repulsion of (3/2)ⁿ from the cycle
-- targets A/(3^p−2^p).  Statement + the elementary layer around it (free bound, multiplier
-- reduction, shadowing, sojourn cap and its 2/3 threshold, diagonal-bit identity); plus
-- MultiplierTransfer.lean (plan-Tshift-S1 WP1), the content-refined rank-2 elimination step that
-- carries a multiplier D at the cost of one product |c|·Λ — engine-agnostic, so no Padé
-- construction enters; and HabsiegerTransfer.lean (WP3 + WP4), which feeds it the cited bundle of
-- CITED/HabsiegerPade.lean to get ‖D(3/2)^k‖ ≥ 0.57434^k for k ≥ 64440001, uniformly in the
-- multiplier (every D ≤ (1216/1215)^k at once), hence repulsion from every cycle target of every
-- period, and at a single date from all periods p ≤ k/1341 simultaneously.  0.57434 < 2/3, so the
-- effective problem is still open (see MahlerCountMul.lean below).  Plus FreeSojourn.lean
-- (plan-Tshift-S11 WP-C), which proves what *is* free: the floor-convention port of Lemma R
-- (from TH/RepetitionIdentity.lean, round convention) gives the unconditional sojourn cap
-- 2^(L+n) <= 3^(n+p) on p-periodic blocks of the carry word, i.e. L <= 0.585 n + 1.585 p, hence
-- the dyadic-block-visit payoff; it also carries the 1/5 parity cascade at a general multiplier.
-- No repulsion hypothesis and no per-n floor: it does not touch the open problem.  Plus
-- MahlerCountMul.lean (plan-Tshift-S2 WP1), which closes the multiplier gap BB13/MahlerCount.lean
-- flags — the residue D*p^n - m*q^n never vanishes for odd D at q = 2 (parity), so the delta = 1
-- per-line confinement runs at every multiplier — and gets Mahler's theorem for ‖D(p/q)^n‖ along
-- the quantitative Ridout route (std3 + BugeaudEvertse.ridout_line_cover).  That last statement is
-- a reproof, not a new result: Mahler 1957 has only D = 1, while Schlickewei 1975 Thm 1 (at n = 1)
-- and Philippon-Rath 2019 Thm 5/12 both print the multiplier form — qualitatively, discarding the
-- cover, which is exactly what DyadicBlocks.lean below needs kept.  At (3,2) that settles
-- the *existential* form of the problem, TShift.TShiftProblem, at every period and numerator, and
-- likewise T1Prime; so the file also carries the repair this forces, TShift.TShiftProblemAt, the
-- problem with its numerals exhibited, which is what is actually open.  Plus DyadicBlocks.lean
-- (plan-Tshift-S2 WP3), the effective shadow of that ineffective finiteness: a line of the Ridout
-- cover is confined to [a, a/f_inf), which meets at most t+1 dyadic blocks [2^m, 2^(m+1)) whenever
-- 2^t f_inf >= 1, so the failures meet at most K(eps)(t+1) + log_2 N_0 + 1 blocks -- Theorem A,
-- BB13.badBlocks_card_le, every quantity explicit -- and all the other blocks are ENTIRELY good.
-- At (D,theta) = (5,3/4) every constant is already certified (eps(3,3/4) = eps*), giving at most
-- 3 720 000 000 004 bad blocks with no new numerics, at kappa(3/4) = 0.70951 < 1: a per-date rate
-- above 2/3 at every date of all but boundedly many blocks.  Positions still ineffective, date
-- count still conditional, and the escape payoff still weaker than FreeSojourn's free one.
-- Plus TowerCurrency.lean (WP5), the second exception currency and its price: the gap principle,
-- the linkage lemma and its four consequences transport to every multiplier (D cancels out of the
-- gap identity, so neither admissibility nor a parity clause is needed), linkage is upgraded to
-- collinearity, and the free O(log N) tower count runs at every multiplier with no decimal log
-- bound (3^66 <= 2^105).  The swap the plan proposed -- replace b_l K(eps) by that count -- is
-- REFUTED, not performed: the block shadow 2(12 + log_{6/5} N) exceeds the floor(log2 N) + 1
-- blocks that exist below N, at every N and at every ratio up to the sharp 1+eps*, so only a line
-- count bounded independently of N (the cited axiom) can show that most blocks are good.  The
-- file also carries WP5(b), the uniform-in-period package: the blocks bad for SOME period p <= P
-- number at most P (2 K(eps*) + log2 max(10,P+1) + 1).  20 of its 25 decls are std3; only that
-- last package inherits the axiom.
-- Plus BlockScope.lean (WP7), which moves Theorem A along its two free parameters and prices each
-- move.  The rate: the line count is monotone in it, so the bound is CHEAPEST at theta -> 2/3 and
-- the plan's question was pointed the wrong way; the price of theta -> 1 is at least cubic,
-- K(eps(3,theta)) >= 1.27e9/(1-theta)^3, so no rate-uniform bound exists -- and it is the WHOLE
-- price, because one block span t = 2 serves every rate below 1 at base 3/2.  The base: the parity
-- clause never used q = 2, only 2 | q, so for D and p odd and q EVEN the residue is odd and
-- Theorem A runs at every coprime p/q of that shape, at every odd multiplier and every rate; the
-- span certificate reduces to the rational inequality (p/(cq))^(2^t) >= p, and the bases (5,2) and
-- (5,4) -- q even but not 2 -- are carried out in full.  Only the decimals are base-specific: they
-- would need log 5 enclosures.  15 of its 24 decls are std3.
-- Plus NoGo.lean (plan-Tshift-NoGo D1/N2), which states as a theorem the one fact S7 and S10 both
-- died of and nobody had written down: scaling a pair of eliminating forms multiplies its size and
-- coefficient slots together, so the floor it certifies is DIVIDED by |t| and eventually turns
-- negative -- hence no scale-invariant real functional F of a pair certifies a positive floor,
-- for ANY phi, TShift.no_floor_from_scaleInvariant.  The quantifier is over a Lean-defined class
-- (TShift.ScaleInvariant) and the class carries a non-constant witness, the projective ratio
-- Lambda/B (1/16 at the corpus's own orientation instance, 81 at the standard basis), so the
-- theorem is not about constants.  std3, 0 cited axioms.  It rules out no engine: what scaling
-- cannot reach is the content slot, which is where every advance since 1975 has come from, and
-- the four T-shift walls S7/S8/S10/S11 remain measurements, not proofs.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib TShift where
  globs := #[.submodules `TShift]

-- The Dubickas S/Z landscape (plans/plan-dubD1.html, ref "Dub06EO" = Dubickas, *Even and odd
-- integral parts of powers of a real number*, Glasgow Math. J. 48 (2006) 331-336; NOT the
-- [Dub06] of Bugeaud/Chapter3, which is the Bull. LMS paper of the same year).  Report
-- report-dubickas.html theme D: the sets Z = {alpha > 1 : some xi != 0 makes every floor(xi
-- alpha^n) even} and S = (1,infty) \ Z, the alpha-version of Mahler's 1968 question at 3/2.
-- Milestone M2/M3 of the plan: the sign-compensated trace-parity design settling
-- alpha = 1 + sqrt 2 (report section D.1's "best single open case", the P_alpha(1) = -2 boundary
-- that evades every engine of [Dub06EO]), its mod-m generalisation (report section D.4), a
-- constructive Tijdeman engine for [3, infinity) (report section D.6), the golden mean on the S
-- side, and the resulting complete classification of the quadratic Pisot numbers.  No cited
-- axiom anywhere.  Build-only registration; Extract.lean corpusRoots registration + db regen:
-- user's call.
lean_lib SZ where
  globs := #[.submodules `SZ]

-- Bugeaud Problem 10.61 (plans/plan-1061.html, ref "Bug12"): for Pisot alpha > 2 and
-- C(alpha) = {(alpha-1) sum eps_k alpha^{-k}}, the sequence (xi alpha^n) is never u.d. mod 1
-- on C(alpha).  Formal companion of milestone M2 (note-1061-M2.html): the quadratic Route A
-- engine -- the exact splitting {xi alpha^n} = {t_n - S_n} via the integer conjugate-pair
-- recursion (M1 Lemma 2/Prop. 4, degree 2), the finite-candidate covering, and the uniform
-- avoided-interval theorem -- with the capstone at alpha = 2 + sqrt 5, the smallest Pisot
-- number of degree >= 2 where the criterion fires: one explicit interval that every orbit
-- misses at every time, hence not dense and not u.d. mod 1.  Numeric certificate at depth
-- (70,70) discharged by norm_num.  `BB61/Confinement.lean` is M1 Lemma 3 and Prop. 4, the
-- set-level form of the same statement: the window K = range wVal is compact with attained
-- endpoints and diam K >= d-1 = 1, the confinement set X(alpha) = (C(alpha) - K) mod 1 IS the
-- range of the factor map, so it is compact and carries every orbit with no error term, and
-- X(alpha) != T is *equivalent* to a uniformly missed interval (X(alpha) is the orbit
-- closure).  Route A is therefore exactly a proof that X(alpha) != T.  `BB61/Criterion.lean` is
-- M1 Corollary 5: the covering engine, run along the ray (M,M') = (pn,qn), has certificate value
-- (4K+2)(x^n + c y^n) with x = 2^{p+q} alpha^{-p} and y = 2^{p+q} rho^q, so it fires as soon as
-- both ratios are < 1 (`exists_avoided_interval_of_geom`) -- which, taking logarithms, is exactly
-- A(alpha) = log2/log alpha + log2/log(1/rho) < 1 (`routeAExponent`), M2's normal form
-- (L-1)(R-1) > 1.  The dimensions of Cor. 5 are thus not needed for its conclusion; at 2 + sqrt 5
-- the criterion fires at the smallest possible (p,q) = (1,1), reproving the capstone without the
-- depth-(70,70) certificate.  `BB61/BoxDim.lean` then states the dimensions themselves, on
-- `ForMathlib/Topology/MetricSpace/BoxDimension.lean`: dim_B C(alpha) = log2/log alpha EXISTS
-- (upper and lower value agree) by the truncation cover against the 2^M separated words of
-- Lemma 1(iv) -- M1 Lemma 1(iii)'s box half; dim_B K <= log2/log(1/rho) -- M1 Lemma 3; and
-- dim_B X(alpha) <= A(alpha) by subadditivity on difference sets -- M1 Corollary 5; and
-- `dimH_cantorSet_le`/`dimH_confSet_le`, the same two ceilings for Mathlib's Hausdorff
-- dimension via `dimH_le_upperBoxDim` (for Cor. 5 the box detour is the ONLY route: dim_H is
-- not subadditive on difference sets).
-- `BB61/Hausdorff.lean` closes Lemma 1(iii) with the matching Hausdorff FLOOR, so
-- dim_H C(alpha) = dim_B C(alpha) = log2/log alpha.  Mathlib has no IFS theory, so the measure
-- is built here: the fair coin on {0,1}^N (`Measure.infinitePi`), pushed forward by pi.  Lemma
-- 1(iv) read backwards says a set of diameter below g alpha^-M has all its pi-preimages in ONE
-- depth-M cylinder, of coin mass 2^-M; choosing M as large as that allows and using
-- alpha^-d = 1/2 at d = log2/log alpha turns this into the Frostman condition, which
-- `ForMathlib/MeasureTheory/MassDistribution.lean` (`le_dimH_of_frostman`, Mathlib's
-- `Measure.le_hausdorffMeasure` with the constant divided out) converts into the floor.  With
-- Leb-nullity below dimension one that gives the note's OWN route to 10.61,
-- A(alpha) < 1 => Leb(X(alpha)) = 0 => X(alpha) != T, a second proof of the Criterion result and,
-- at 2 + sqrt 5 (where the norm is -1, so rho = 1/alpha and A = log 4 / log alpha < 1 iff
-- alpha > 4), a third proof of the capstone.
-- `BB61/RouteACeiling.lean` is M1 Corollary 5's LOWER bound on rho, the note's last prose
-- clause, and it is done at general degree rather than only at d = 2.  For a monic p in Z[X]
-- with p(0) != 0 whose complex roots are alpha together with a multiset s of modulus <= rho,
-- 1 <= alpha rho^{card s} (`one_le_mul_pow_of_monic_int`): the product of the roots is
-- (-1)^d p(0) (Mathlib's `Splits.coeff_zero_eq_prod_roots_of_monic`, C being algebraically
-- closed), and integrality enters exactly once -- p(0) is a NONZERO rational integer, so at
-- least 1 in modulus.  Irreducibility is never used.  Hence rho >= alpha^{-1/(d-1)}
-- (`rpow_neg_inv_le_of_one_le_mul_pow`), d log2/log alpha <= A(alpha)
-- (`routeA_ge_of_one_le_mul_pow`), and A(alpha) < 1 forces 2^d < alpha
-- (`two_pow_natDegree_lt_of_routeA_lt_one`) -- Route A can fire only above 2^d.  At degree two
-- the whole bound is the single identity alpha |beta| = |b| >= 1
-- (`one_le_alpha_mul_abs_beta`), which is also the PROOF of M0's empirical rho >= 1/alpha that
-- Plateau.lean explains; so 4 < alpha (`four_lt_alpha_of_routeAExponent_lt_one`) and, as the
-- contrapositive, Route A never touches the hard slice 2 < alpha <= 4
-- (`one_le_routeAExponent_of_alpha_le_four`) where all sixteen of M0's certificates live.  The
-- degenerate integer case beta = 0 is the note's d = 1 and is included: the second summand of
-- A(alpha) is then 0 and the ceiling reads 2 < alpha, which holds at either degree
-- (`two_lt_alpha_of_routeAExponent_lt_one`) -- the criterion never reaches outside 10.61's own
-- hypothesis.  That the two halves are one statement is checked, not asserted: `quadPoly` is
-- X^2 - aX - b, `quadPoly_roots` computes its complex roots as {alpha, beta}, and
-- `one_le_alpha_mul_abs_beta_of_monic` re-derives the degree-two bound from the general lemma.
-- Numerics `BB61/m1_cor5.py`, 7/7 verdicts over every monic integer quadratic and cubic in a
-- coefficient box with one real root > 1 and all conjugates inside the unit disc (1561 + 2038):
-- the bound is SHARP at both degrees (min A log2 alpha is exactly 2 and exactly 3, attained at
-- the units), and the smallest alpha where Route A fires is 2 + sqrt 5 itself.  Roots are
-- re-solved with mpmath at 30 digits, np.roots being good to only 1e-8 on a cubic -- enough to
-- report the cubic minimum as 2.9999999985 and make sharpness untestable.
-- `BB61/RouteANormalForm.lean` is M2 Proposition 1, the NORMAL FORM of the criterion -- the
-- clause of note-1061-M2.html section 3 that Criterion.lean's own docstring asserted without
-- proving it.  Writing L = log2 alpha (`logAlpha`) and R = log2(1/rho) (`logRhoInv`), so that
-- A(alpha) = 1/L + 1/R (`routeAExponent_eq_inv_add_inv`), the four statements A(alpha) < 1,
-- (L-1)(R-1) > 1, R > L/(L-1) and rho < 2^{-L/(L-1)} are equivalent -- and the last is the
-- practical one: at a fixed base Route A fires exactly below an explicit threshold on the
-- conjugate (`routeAExponent_lt_one_iff_abs_beta_lt_rpow`).  The proof is one line of algebra
-- on two positive reals, both sides being L + R < LR after clearing denominators; nothing
-- beyond positivity is needed, R <= 1 included (there both sides are false).  Also
-- A(alpha) log2 alpha = 1 + L/R (`routeAExponent_mul_logAlpha`), the quantity
-- RouteACeiling.lean bounds below by the degree.  The normal form is a hyperbola with
-- asymptotes L = 1 and R = 1, and that is stated as theorems rather than drawn: the threshold
-- L/(L-1) is > 1 for every L > 1 (`one_lt_div_sub_one`), strictly decreasing
-- (`div_sub_one_lt_div_sub_one`) and tends to 1 (`tendsto_div_sub_one_atTop`), so R > 1 is
-- necessary however large alpha is (`one_lt_logRhoInv_of_lt_one`) and, by the symmetry of the
-- product, conversely.  Three consumer forms compose it with Criterion.lean
-- (`not_equidistributed_of_normalForm`, `not_equidistributed_of_abs_beta_lt_rpow`,
-- `confCircle_ne_univ_of_normalForm`).  M2 Corollary 6 follows at degree two, where
-- alpha beta = -b gives rho = |b|/alpha EXACTLY (`abs_beta_eq_div`) and hence R = L - log2|b|
-- (`logRhoInv_eq_sub`): A(alpha) < 1 iff (log2 alpha - 1)(log2(alpha/|b|) - 1) > 1
-- (`routeAExponent_lt_one_iff_quadratic`), which at units collapses to alpha > 4
-- (`routeAExponent_lt_one_iff_four_lt`).  That last iff completes RouteACeiling.lean's one-way
-- `four_lt_alpha_of_routeAExponent_lt_one`, so on quadratic units Route A covers EXACTLY
-- (4, infinity) -- 2 + sqrt 5 first, and the hard slice 2 < alpha <= 4 (1 + sqrt 2 included)
-- outside it by a theorem rather than by accident.  All std3, no citation; the note's own QA
-- records that Proposition 1 uses nothing.  Numerics `BB61/m2_prop1_lean.py`, 10/10 verdicts:
-- `m2_verify.py` checks P3/C6 in the note's coordinates (rho, |N|), this one re-runs them in
-- the QuadSetup coordinates the Lean file uses (beta = a - alpha, and the norm as the constant
-- coefficient b), with the 440 quadratic rows recomputed from their integer coefficients at 60
-- digits so that L6/L7 test the identities and not the stored floats.
-- `BB61/RouteADepth.lean` is M2 Theorem 2(i): CERTIFIED DEPTHS EXIST, and along a named ray.
-- Criterion.lean already shows the covering certificate is satisfiable when A(alpha) < 1, but
-- by an existential rational ray out of `exists_rat_btwn`; Theorem 2(i) names the ray -- the
-- BALANCED one, M' = ceil(M L / R) (`balancedDepth`) -- and bounds the covering total
-- T(M,M') = 2^{M+M'}(alpha^{-M} + C rho^{M'}/(1-rho)) (`coverTotal`) on it by an explicit
-- affine function of M: log2 T <= 1 + log2(1 + C/(1-rho)) + M (1-(L-1)(R-1))/R
-- (`logb_coverTotal_balancedDepth_le`).  The proof is three lines, each isolated.
-- `pow_balancedDepth_le`: rho^{M'} <= alpha^{-M}, which is what the balanced ray MEANS -- with
-- alpha = 2^L and rho = 2^{-R} it is R M' >= L M, i.e. `Nat.le_ceil` -- so the window error and
-- the Cantor error collapse into one.  `two_pow_balancedDepth_le`: 2^{M+M'} <= 2 2^{M(1+L/R)},
-- from ceil x < x + 1; that lone factor 2 is the entire price of the ceiling and it is the
-- leading `1 +` of the bound.  `slope_eq`: 1 + L/R - L = (1-(L-1)(R-1))/R, one line of algebra,
-- which is where RouteANormalForm.lean enters -- `slope_neg_iff` says the slope is negative
-- EXACTLY under Proposition 1's normal form, and that single sign is the whole theorem.  Hence
-- T -> 0 (`tendsto_coverTotal_balancedDepth`) and every threshold is eventually cleared
-- (`eventually_coverTotal_balancedDepth_lt`), with an explicit sufficient M
-- (`coverTotal_balancedDepth_lt_of_logb_le`) rather than a limit.  Nothing in that half uses
-- any property of alpha beyond alpha = 2^L: it is a statement about four real numbers, at any
-- degree.  At degree two it meets the engine: the certificate value of Covering.lean is
-- 2(2K+1) times T with C = 1 + rho (`QuadSetup.cert_eq_coverTotal`; the note's own constant is
-- C_alpha = |beta - 1| <= 1 + rho), so `exists_avoided_interval_at_balancedDepth` and
-- `not_equidistributed_at_balancedDepth` re-prove Criterion.lean's conclusion by the note's own
-- route, at a named depth.  The Corollary 3 warning is visible in the statement itself: the
-- slope tends to 0- as A(alpha) climbs to 1, so the certified M grows like 1/(1-(L-1)(R-1)) and
-- the interval count like 2^{Theta(1/(1-A))} -- Theorem 2 proves a gap, it never finds one.
-- Numerics `BB61/m2_thm2i_lean.py`, 10/10 verdicts at 60 dps: the three estimates and the
-- affine bound swept over all 9287 Pisot numbers at ten depths (the bound is attained, not
-- merely valid), the engine identity exact to 0.0, Cor. 3's own pairs reproduced -- T(17,17) =
-- 0.9877 at 2+sqrt5 and T(751,1502) = 0.9994 at X^3-8X^2-1 -- and the Lean engine's own first
-- balanced certified depth at 2+sqrt5 located at M = 63 (the affine bound guarantees M = 75),
-- which brackets the depth-(70,70) certificate `BB61/RouteA.lean` actually discharges.
-- `BB61/RouteAFamily.lean` is M2 Theorem 5: the explicit family X^d - aX^{d-1} - 1 that
-- INHABITS Route A in every degree.  RouteACeiling says where the criterion cannot fire,
-- RouteANormalForm exactly when it does, RouteADepth at what depth; Theorem 5 supplies the
-- numbers.  (i) The root count is done WITHOUT Rouche, which Mathlib does not have.  Every root
-- satisfies |z|^{d-1}|z-a| = 1, so a root with |z| >= 1 has |z-a| <= 1, hence |z| >= a-1 >= 2,
-- hence |z|^{d-1} >= 2, hence |z-a| <= 1/2 and |z| >= a - 1/2 (`le_norm_of_one_le_norm`); a root
-- with |z| < 1 has |z|^{d-1} >= 1/(a+1) (`inv_le_norm_pow_of_norm_lt_one`); and the product of
-- ALL the moduli is 1 because the constant term is -1.  Two large roots would give
-- (a-1/2)^{2(d-1)} <= (a+1)^{d-2} <= (a-1/2)^{2(d-2)}, impossible at base > 1
-- (`card_big_roots_eq_one`) -- integer powers throughout, no rpow, no complex analysis.  The
-- second pass to a - 1/2 is load-bearing: with the cruder a - 1 the chain degenerates to 4 <= 4
-- at a = 3.  Hence alpha is Pisot (`isPisot_family`, on ForMathlib's `IsPisot`), and the SAME
-- product argument run on a monic cofactor of the minimal polynomial gives
-- `minpoly_eq_familyPoly` -- so `familyPoly_irreducible`, degree exactly d
-- (`minpoly_natDegree_family`) and a unit (`minpoly_coeff_zero_family`).  (ii) a|z|^{d-1} <= 2,
-- i.e. |z| <= (2/a)^{1/(d-1)} (`norm_le_familyConjBound`).  (iii) a >= 2^{d+1} forces
-- A(alpha) < 1 (`routeA_family_lt_one`), off 1/(d+1) + (d-1)/d = (d^2+d-1)/(d^2+d) < 1.  (iv) At
-- d = 2 the member IS a QuadSetup (`familyQuad`, alpha = (a+sqrt(a^2+4))/2), so the folder's
-- engine applies and the conclusion is 10.61 itself for every a >= 4
-- (`familyQuad_not_equidistributed`), with the threshold as an IFF
-- (`familyQuad_routeAExponent_lt_one_iff`) and the first member identified as 2+sqrt5, the
-- capstone of BB61/RouteA.lean.  At d = 3 no calculus is needed either: dividing by X - alpha
-- leaves a real quadratic whose discriminant 1/alpha^4 - 4/alpha is negative for free, which
-- both forces the pair to be non-real and computes |z|^2 alpha = 1
-- (`norm_sq_mul_eq_one_cubic`), whence A log2 alpha = 3 -- the cubic members sit ON the Prop. 4
-- ceiling -- and A < 1 iff alpha > 8 iff a >= 8.  All std3, no citation.  Numerics
-- `BB61/m2_thm5_lean.py`, 10/10 verdicts at 60 dps over 91 (d,a) pairs: each step of the count
-- separately, the counting inequality swept to d < 40, and the note's own section 5 rows
-- reproduced exactly -- A(4,16) = 1.00329 misses, A(4,17) = 0.98152 fires; 1.00215/0.99323 at
-- d = 5; 1.00111/0.99736 at d = 6 -- plus irreducibility cross-checked with sympy.
-- `BB61/WindowDiam.lean` is M2 Proposition 7: the width of the window K, and the death of the
-- criterion X7 (`plans/plan-1061.html` section 7, "if 2Delta < g then every orbit misses a fixed
-- interval").  Three layers.  (1) Abstract: for any absolutely summable c : N -> R the
-- subset-sum set K = {sum_m c_m delta_m} has diam K = sum_m |c_m| EXACTLY (`diam_windowOf`) --
-- an identity, not the two-sided estimate M1 Lemma 3 settled for, because the two greedy words
-- hit both endpoints of [-Q, P] -- and hence the note's
-- diam K = -(sum_m c_m) + 2 sum_{c_m>0} c_m (`diam_windowOf_eq_two_mul_posSum`), which is
-- |x| = 2 max(x,0) - x summed and nothing else.  So diam K >= |sum_m c_m| with equality iff no
-- coefficient is positive (`diam_windowOf_eq_neg_tsum_iff`).  (2) Conjugates: for a multiset s
-- inside the unit disc and c_m = Re sum_j (alpha_j - 1) alpha_j^m, every conjugate contributes
-- exactly -1 to sum_m c_m, whatever it is (`hasSum_conjCoefC`, geometric series once per
-- conjugate), so sum_m c_m = -card s and card s <= diam K <= Delta.  (3) X7: g = (alpha-2)/alpha
-- < 1 for every alpha > 0, so 2Delta >= 2 diam K >= 2(d-1) >= 2 > 1 > g and the criterion is
-- EMPTY (`not_x7Criterion`, and `not_x7Criterion_of_natDegree` stated in the degree).  Zero
-- margin, in the strongest sense: on the family X^2 - aX + 1 (`unitQuad`, alpha > 2 a unit of
-- norm +1 with beta = 1/alpha in (0,1)) EVERY inequality of that chain is an equality --
-- Delta = diam K = d-1 = 1 (`conjDelta_unitQuad`, `diam_windowSet_unitQuad`) -- and the one
-- surviving strict inequality degenerates: 2Delta/g decreases to 2 along the family
-- (`tendsto_ratio_unitQuadSeq`), so the constant 2 is the exact infimum, approached and never
-- attained.  `unitQuad 4` is 2+sqrt3.  Also recorded, since the criterion has to compare against
-- something real: C(alpha) does miss the open interval (1/alpha, (alpha-1)/alpha), of length g
-- (`cantorSet_inter_gapIoo_eq_empty`).  At degree two the majorant is exact,
-- Delta = diam K (`diam_windowSet_eq_conjDelta`) -- one conjugate leaves the triangle inequality
-- nothing to lose.  All std3, no citation.  Numerics `BB61/m2_prop7_lean.py`, 10/10 verdicts at
-- 60 dps over all 9287 enumerated Pisot numbers: sum_m c_m = -(d-1) to 0.0e+00, the identity and
-- the equality case on 1514 rows with an explicit float64 tail bound, greedy words never beaten
-- by 4000 random ones, and the note's own minima reproduced -- min 2Delta/g = 2.20/4.81/8.34 at
-- degrees 2/3/4, the 2.20 being X^2 - 22X + 1, a member of the attainment family.  One
-- correction to the note falls out: above degree two Delta = diam K is NOT always strict -- it
-- holds exactly when every conjugate is real and they share a sign, which is 92 of the 2020
-- cubics and none of the 6827 quartics.
-- `BB61/BlockRecoding.lean` is M2 Proposition 8: block recoding is exactly NEUTRAL, so gate
-- G-R's degree of freedom -- proving 10.61 along a single progression n = 0 mod p, i.e. in base
-- alpha^p, licensed on the quadratic-unit class by [BM86] Th. XIII -- is worthless to Route A
-- and to every criterion of its kind.  The note's proof is one sentence ("every p cancels"), so
-- what is formalised is the ACTION and not the cancellation.  (1) Abstract: a criterion of this
-- kind sees only the triple (log #alphabet, log base, log 1/contraction) (`RatioData`), block
-- recoding multiplies all three by p (`RatioData.block`, an instance of `RatioData.scale`), and
-- the two ratios L = log base / log #alphabet and R = log(1/contraction) / log #alphabet are
-- invariant (`ratios_scale`).  Since A = 1/L + 1/R (`expo_eq_inv_add_inv`), dim = 1/L
-- (`dim_eq_inv_L`), the entropy deficit is log #alphabet < log base and Mendes-France's rho <
-- 1/2 is log #alphabet < log(1/contraction), the plan's four named invariants are corollaries
-- of ONE no-go: `apply_ratios_block`, which says that EVERY F of the ratio pair takes the same
-- value before and after.  And the converse holds -- `ratios_eq_iff` proves that two data have
-- the same (L,R) exactly when one is a rescaling of the other, so the fibres of `ratios` ARE the
-- recoding orbits and factoring through them is what neutrality MEANS (`eq_of_ratios_eq`).
-- (2) The recoded contraction is earned, not assumed, which is the point of the note's check P8:
-- `power` builds the actual power polynomial X^2 - t_p X + (-b)^p from the integer trace ladder
-- t_n = alpha^n + beta^n (`traceSeq`, `BB61/Ladder.lean`'s `lad` started at (2,a)), `power_beta`
-- proves its second root is beta^p, and `blockData` is defined from THAT polynomial's roots --
-- `blockData_eq_block` is the theorem that it lands on p times the original triple.
-- Proposition 8's display is `blockRecoding_expo`; the coverage consequence is
-- `routeACriterion_blockData_iff_four_lt`, quadratic units still exactly (4, infinity) at every
-- order p.  `dimH_cantorSet_blockData` grounds the invariant dimension against
-- `BB61/Hausdorff.lean`: the recoded description computes the dimension of the SAME, unchanged
-- set.  (3) The trap, which is what makes the no-go usable as a falsification test:
-- `routeAExponent_power` shows that raising the base WITHOUT enlarging the alphabet divides A by
-- p, so it eventually fires at every alpha (`exists_power_routeAExponent_lt_one`) -- including at
-- 1+sqrt2, where Route A provably does not (`silver_not_routeAExponent_lt_one` against
-- `exists_silver_power_routeAExponent_lt_one`) -- because the binary system at base alpha^p is a
-- thinner Cantor set and not a recoding of C(alpha).  All std3, no citation: [BM86] Th. XIII is
-- what makes the freedom AVAILABLE and is not consumed, the statement proved being that the
-- freedom is neutral.  Numerics `BB61/m2_prop8_lean.py`, 10/10 verdicts at 60 dps: the ladder,
-- the power polynomial's integrality and its second root, the scaling identity and Proposition
-- 8's display on all 9287 enumerated Pisot numbers at eight exponents, the fibre theorem, the
-- note's own three instances ((2+sqrt3)^2 = X^2-14X+1, (1+sqrt2)^2 = X^2-6X+1, (1+sqrt2)^3 =
-- X^2-14X-1) and the trap, with the block-constant sliver identity checked to 7.8e-62 and its
-- properness certified against the tail bound.
-- `BB61/Raster.lean` is M2 Proposition 9: M0's X8 raster criterion, both directions.  The
-- procedure decides, per alpha, whether the confinement set X(alpha) = (C(alpha) - K) mod 1
-- misses an interval -- over-approximate C and K by their depth-(M,M') point sets fattened by
-- the tail bounds, rasterise on G bins, dilate, look for a run of empty bins -- and Proposition
-- 9 says that on Route A's range it is GUARANTEED to find one, at a resolution nameable in
-- advance: T := T(M,M') < 1/3 and G >= 2^(M+M'+3)/(1-3T).  The raster is modelled exactly: bins
-- are the fibres of `binIdx G x = floor(x*G)`, so `bin G i = [i/G, (i+1)/G)` partitions R for
-- free.  Everything then rests on two facts and arithmetic -- a raster never loses a point
-- (`subset_occSet`) and gains less than one bin (`occSet_dist`).  `runSet_inter_occSet_eq_empty`
-- is SOUNDNESS, M0's direction: a reported run is a true gap, which is what makes X8 a proof
-- method rather than a heuristic.  `exists_zeroRun` is COMPLETENESS at a given resolution: an
-- interval of length b-a missing the occupied set contains a run of ell >= (b-a)*G - 2 bins, the
-- 2 being the alignment loss and the only loss, under NO hypothesis on a, b, G.
-- `inter_occSet_eq_empty_of_shrink` adds the implementation's slack e, `exists_certified_gap`
-- composes the three at (b-a-2e)*G - 4, and `gap_pos_of_resolution` is the note's own arithmetic
-- 2^3 > 6.  ONE CORRECTION, in the harmless direction: the note allows "O(1) bins, <= 3/G on
-- each side", i.e. 6/G, where 4/G suffices (1/G per side for the raster, one bin per side for
-- the alignment), so the surviving run is at least HALF the guaranteed gap and not a quarter;
-- both forms are proved, so the displayed choice of G is verified as written.  Section 5
-- instantiates on the quadratic engine: `covSet` is what the procedure rasterises,
-- `orbitFract_mem_covSet` is `exists_cand_near`, `X8Cert` is the certificate,
-- `not_equidistributed_of_X8Cert` turns it into 10.61 at alpha, and `exists_X8Cert_of_cert` is
-- ROUTE A SUBSET X8.  `exists_gap_in_covSet` is `BB61/Covering.lean`'s volume argument restated
-- against the COVERING rather than against the orbit, which is what the procedure needs and what
-- `exists_avoided_interval` throws away.  What is taken as a hypothesis is exactly what the
-- note's proof takes: the true gap of Theorem 2(ii) and its length (1-T)2^-W; the quantitative
-- form of 2(ii) -- N closed arcs of total length T < 1 leave an open arc of length >= (1-T)/N --
-- is a statement about the interval structure of the complement and is not formalised, its
-- qualitative form being enough for the containment.
-- `BB61/GapSqrtThree.lean` is Proposition 9's CONVERSE half, and it makes the containment
-- strict: at alpha = 2+sqrt3 the X8 certificate exists while Route A does not fire.  M0 sec 6.2
-- found this at depth (11,9) on 2^21 raster bins; it is in fact a DEPTH-(2,2) fact, exact in
-- Z[sqrt3], and that is what is proved.  2+sqrt3 is the root of X^2-4X+1: norm +1, so beta =
-- 1/alpha, the window weights |c_m| = (1-beta)beta^m and the Cantor weights (alpha-1)alpha^-(m+1)
-- are the SAME sequence, and both factors truncate at depth 2 with the same ONE-SIDED error
-- beta^2 = 7-4sqrt3.  That one-sidedness is the whole trick: `BB61/Covering.lean`'s two-sided
-- `delta 2 2` is 0.196, which would swallow a gap of 0.0526, while the true error is 0.0718 on
-- each side (`tPart_expand`, `neg_sPart_expand`).  The sharp window bound S_n in [-1,0] that the
-- past expansion needs is `neg_sPart_mem_Icc`, which is M2 Proposition 7's diam K = d-1 = 1 in
-- recursion form.  The covering `covThree` is then nine intervals [w2*p + w1*q, +2(7-4sqrt3)],
-- p,q in {0,1,2}, times two integer shifts, and `covThree_inter_gapIoo_eq_empty` is eighteen
-- exact comparisons in Z[sqrt3] -- TWO OF THEM EQUALITIES, so the covering touches the gap at
-- both ends and the openness of the gap is load-bearing; there is no numerical tolerance
-- anywhere.  The gap is (11-6sqrt3, 5sqrt3-8), of length 11sqrt3-19 = 0.0525589, at 0.60770 --
-- M0 sec 6.2's 0.052558 at 0.6077.  Consequences: `gap_two_add_sqrt3` is one avoided interval
-- uniform in xi and n, and `problem_10_61_two_add_sqrt3_axiom_free` is PROBLEM 10.61 AT 2+SQRT3
-- WITH NO CITATION AND NO AXIOM BEYOND THE STANDARD THREE.  `BB61/Floor.lean` proves the same
-- statement through M3's entropy floor and the root's single cited axiom `LY.entropyRate_floor`;
-- the two proofs are independent and agree, so the root's headline unconditional result no
-- longer rests on a citation.  `exists_zeroRun_two_add_sqrt3` re-reads the certificate as the
-- OUTPUT of `BB61/Raster.lean`'s procedure at every resolution G >= 100 (the threshold is
-- 4/(gapHi-gapLo) = 76.11), and `routeA_subset_X8_strict` is ROUTE A PROPERLY CONTAINED IN X8,
-- Route A's blindness being `not_routeAExponent_lt_one_twoAddSqrt3`: on the quadratic units
-- A(alpha) < 1 is exactly alpha > 4 (M2 Cor. 6) and 2+sqrt3 = 3.732.  Numerics
-- `BB61/m2_prop9_lean.py`, 10/10 verdicts at 60 dps (400 for the orbit test, since {xi alpha^n}
-- at n = 250 needs ~145 digits just to exist): the raster model and both of its directions on
-- random instances, the alignment loss never exceeding 2 bins, the note's arithmetic in exact
-- rationals, the one-sided depth-2 remainders, the nine endpoints and the eighteen comparisons
-- in exact Z[sqrt3] with the two zero margins located, the two gaps reproduced against M0's own
-- FFT-free method, DEPTH 1 GIVING NO GAP AT ALL (so depth 2 is the first that certifies), zero
-- landings in 20000 orbit points, and the run lengths at G = 100, 2^12 and M0's 2^21.
-- `BB61/EntropyBudget.lean` is M3 Corollary 13, and the first file in which the root's two
-- lanes touch: until it, `QuadSetup.routeAExponent` (BB61/Criterion.lean, the Route A exponent
-- A(alpha) = log2/log alpha + log2/log(1/rho)) and `LY.hMin` (CITED/LedrappierYoung.lean, the
-- Ledrappier-Young floor h_min(alpha) = (1/log alpha + 1/log(1/rho))^-1) appeared nowhere in
-- the same statement.  They are the same number twice: `routeAExponent_mul_hMin` is the
-- IDENTITY A(alpha) * h_min(alpha) = log 2, so `routeAExponent_lt_one_iff_log_two_lt_hMin` is
-- Corollary 13, ROUTE A FIRES EXACTLY WHEN THE ENTROPY FLOOR EXCEEDS log 2, and
-- `zero_lt_entropyBudget_iff` is the budget phrasing: the entropy a potential must consume,
-- log 2 - h_min(alpha), is positive precisely when Route A fails.  This is the exact statement
-- of what the M3/M4 pressure lane may NOT hope for -- the floor used alone is Route A's
-- criterion in entropy units, and every alpha it decides is one Route A already decides.  M3
-- checked this numerically at 200 dps over the 42 candidates; here it is an identity at every
-- QuadSetup with beta != 0.  Two readings are recorded:
-- `log_two_lt_hMin_iff_four_lt_of_unit` transports M2 Prop. 1's unit threshold alpha > 4 onto
-- the floor, and `routeAExponent_lt_one_iff_four_lt_of_floor` runs it backwards, a THIRD proof
-- of the unit threshold that goes through h_min = (1/2) log alpha instead of through the logb
-- normal form.  Nothing here consumes the cited axiom `LY.entropyRate_floor`, only the
-- definition `LY.hMin`, so the whole file is axiom-free.  Numerics `BB61/m3_cor13_lean.py`,
-- 6/6 verdicts at 60 dps: both constants recomputed from the polynomial roots of all 42
-- candidates, the identity to 7.8e-62, Corollary 13 with zero exceptions (Route A fires at 6
-- of the 42 and the floor clears log 2 at exactly those 6), the budget at the three named
-- alpha, h_min = (1/2) log alpha on the 9 quadratic units, and both criteria crossing at the
-- single point alpha = 4.
-- `BB61/LadderReduction.lean` is M3 Theorem 4, the reduction that deletes the past from the
-- statement of 10.61.  The note proves it on the torus T^d_Lambda through the characters
-- chi_gamma and the corrected Meyer estimate (Prop. 2); at degree two none of that is needed
-- and the theorem is an IDENTITY BETWEEN REAL NUMBERS,
--   Tr_m * t(omega+) = (an integer) + Ftilde(sigma^m omega) + E_m(omega),
-- with `Tr_m = alpha^m + beta^m` the trace ladder of `BB61/BlockRecoding.lean` and
-- `Ftilde = t(omega+) - S(omega-)` the factor map of `BB61/Factor.lean` before reduction mod
-- one (`traceSeq_mul_piVal_futures`).  The mechanism is one line of `BB61/Bernoulli.lean`
-- read backwards: `trace_pw` says `(alpha-1)alpha^j + (beta-1)beta^j = T_j` is an integer, so
-- `(alpha-1)alpha^j = T_j - c_j` (`futureWeight_eq`) -- the j-th FUTURE weight is an integer
-- minus the j-th WINDOW weight.  Multiplying by alpha^m walks the first m future letters back
-- past the origin and each lands, modulo an integer the character cannot see, on exactly the
-- window weight it would have had in `S((sigma^m omega)-)`: THE PAST COORDINATES WERE THE
-- FUTURE COORDINATES ALL ALONG, and the trace ladder is the change of variables.  What is
-- left over -- the window beyond depth m, and the conjugate leak `beta^m t(omega+)` -- is the
-- error, bounded by `(W+1)|beta|^m` with `W = |beta-1|/(1-|beta|)` (`abs_ladderErr_le`), the
-- note's `W + d - 1` at `d = 2`.  No unit hypothesis and no ergodic theorem: only
-- sigma-invariance.  `thm4` is Theorem 4 for measures,
-- `||nu-hat(h Tr_m) - Phi_h(mu)|| <= 2 pi |h| (W+1) |beta|^m`, `tendsto_futureCoeff` is the
-- limit `Phi_h(mu) = lim_m nu-hat(h Tr_m)`, `exists_tendsto_futureCoeff` is M3 COROLLARY 5 at
-- integer frequencies (THE PLATEAU EXISTS FOR EVERY INVARIANT MEASURE, not only the Bernoulli
-- ones M0 and M1 tested -- which is what turns it from an opportunity into a scope
-- restriction), and `not_equidistributed_of_ladder` is Problem 10.61 at alpha from the future
-- marginal alone.  Two things the note has and the file does not: general frequencies
-- `gamma` in the codifferent (only integer h is formalised, which is the case the criterion
-- uses), and the natural-extension converse, so the note's displayed equivalence is proved in
-- the direction that does not need it.  Numerics `BB61/m3_thm4_lean.py`, 8/8 verdicts at 120
-- dps: the decomposition and the identity at 1e-112, the error bound on 672 instances (worst
-- ratio 0.48, and neither summand of W+1 can be dropped), the 2pi|n|-Lipschitz character with
-- worst ratio 0.9997, the measure estimate on 1248 periodic-orbit instances, Bernoulli(1/2)
-- in closed form converging at or below the proved rate, Cor. 5 on non-Bernoulli measures,
-- and the anchor that `phiCoeff` IS the note's Phi -- it reproduces M0's plateau table value
-- 0.359300 at 2+sqrt3 along M0's own ladder 780, 2911, 10864, ...
-- `BB61/LadderScope.lean` is M3 Corollary 6, the scope restriction that comes attached to
-- Theorem 4, and it is aimed squarely at M1: M1 Prop. 15 identified the ladders as the whole
-- codifferent and M1's finding F8 then measured the difference, the half-ladder 1,1,3,7,17,41
-- at alpha = 1+sqrt2 plateauing at 3.4511464e-2 against the trace ladder's 7.6370923e-5, A
-- FACTOR 452, whence M1's prescription "maximise over gamma in d^-1 / alpha^Z".  Corollary 6
-- says that is a DETECTION instruction and not a PROOF instruction.  The positive half rides
-- on Theorem 4: in ladder coordinates the frequency gamma = n alpha^j has
-- Tr(gamma alpha^k) = n T_{k+j} for the two-sided ladder `traceSeqZ` (grounded at a unit by
-- `traceSeqZ_cast`, T_n = alpha^n + beta^n for every n in Z, the backwards half being
-- T_{-m} = (-b)^m T_m), and `tendsto_futureCoeff_orbit` proves every one of them has THE SAME
-- limit Phi_n(mu) -- AN ALPHA-ORBIT CARRIES ONE CONSTRAINT, NOT INFINITELY MANY, whatever
-- entry point j one chooses.  The negative half is a parity argument, and one divisibility
-- condition does both halves of the corollary: `two_dvd_trForm_iff` proves
-- Tr(Z[alpha]) subset 2Z <=> 2 | a from Tr(u + v alpha) = 2u + av, so 2 | a is exactly when
-- gamma = 1/2 is a legal frequency (M1's own reason at 1+sqrt2, "every Tr(alpha^k) is even"),
-- and exactly then the half-ladder is ODD AT THE ORIGIN while `two_dvd_traceSeqZ` makes every
-- n T_{k+j} even.  So `not_intOrbitLadder_halfLad`: THE SAME CONDITION THAT CREATES THE
-- COMPETITOR DISQUALIFIES IT, and `cor6` puts the two halves together -- every ladder in the
-- orbit of a nonzero integer frequency has vanishing limit under F_*mu = Leb, and the
-- half-ladder is not one of them.  `halfLad_isTraceLadder` is the bridge that keeps this
-- honest, M1 Prop. 15 via `BB61/TraceLadder.lean` certifying that the half-ladder really is
-- Tr(gamma alpha^k) for a genuine codifferent element and not a spurious sequence; and
-- `no_half_character` is the analytic register of "the hypothesis says nothing", e(x/2)
-- changing sign under x -> x+1 so it is not a function on R/Z at all.  WHAT THIS IS NOT: a
-- decision procedure.  Parity certifies inadmissibility, it does not classify -- `lad 2 4` at
-- 1+sqrt2 is even throughout and still outside alpha^Z Z (its frequency is (1+alpha)/2) --
-- and `IntOrbitLadder` is the ladder-level definition of alpha^Z (Z minus 0), justified by
-- `traceSeqZ_cast` plus linearity of the trace rather than derived inside the number-field
-- API.  Numerics `BB61/m3_cor6_lean.py`, 8/8 verdicts at 120 dps: the trace-form criterion
-- against brute force over the order, M1's F8 LADDER TABLE REPRODUCED EXACTLY, the two-sided
-- ladder to 1.1e-99 over [-25,25], an exhaustive search over 0 < |n| <= 400, |j| <= 20 finding
-- no realisation of the half-ladder, M1'S PLATEAU TABLE RECOMPUTED (451.9 at 1+sqrt2 and 3.64
-- the other way at 2+sqrt3, against the note's 452 and 3.6), the orbit limit independent of
-- the entry point to 8.8e-15, the half-character's sign flip, and the lad 2 4 caveat.
-- `BB61/KernelCriterion.lean` is M3 Theorems 7 and 8, the correct B-criterion and the collapse
-- of Route B onto Route D.  It is stated over Gamma subset Z, and M3 Cor. 6 is the licence:
-- outside alpha^Z Z the hypothesis supplies nothing, and by Thm 4 the whole alpha-orbit of an
-- integer h carries the single constraint Phi_h(mu), so the note's integer reach
-- H_Gamma = {h : alpha^m h in Gamma-Gamma} collapses to (Gamma-Gamma) minus 0 and its
-- condition (i) is VACUOUS -- which is what Theorem 8(c) observes.  THE NOTE IMPORTS TWO
-- THEOREMS HERE AND NEITHER IS NEEDED.  (a) Bochner, for Q >= 0 from B psd: put B in Gram form
-- B_{gg'} = sum_k w_k(g) conj(w_k(g')) and `matKernel_gram` computes Q = sum_k |P_k|^2, so
-- positivity is an inspection (`matKernel_gram_nonneg`), `gram_posSemidef` recording that these
-- really are psd matrices.  Positivity turns out to be irrelevant to the VALIDITY of Theorem 7
-- anyway -- the proof never uses it and `not_equidistributed_of_kernel` is stated for an
-- arbitrary matrix; B psd is what makes the criterion SATISFIABLE, not what makes it SOUND.
-- (b) Fejer-Riesz, for the realisation A - G = |P|^2: Mathlib has no such factorisation and the
-- criterion has slack, so ONE explicit sum of squares suffices, and the one-term polynomials
-- 1 - a_h e(h.) do it -- their squared moduli are 1 + |a_h|^2 - 2 Re(a_h e(h.)), so on
-- Gamma = {0} u H one gets Q = c(0) - 2G ON THE NOSE
-- (`exists_kernel_of_trigCertificate`).  The same identity read backwards is Theorem 7:
-- `kernelCertificate` turns a kernel with a uniform gap into a Route D certificate G = c(0) - Q,
-- so ROUTE B AND ROUTE D ARE THE SAME OBJECT UP TO A CHANGE OF SIGN, and that is the whole of
-- Theorem 8.  `no_killer_of_kernel` is 8(a); `no_killer_of_trigCertificate` and
-- `exists_trigCertificate_of_no_killer` are 8(b), the second being M3 Theorem 9's separation
-- (`BB61/Certificate.lean`) with the test family PRESCRIBED rather than extracted -- the
-- Hahn-Banach argument runs in R^{H x Bool}, the real and imaginary parts of the |H| numbers
-- Phi_h(mu); `exists_kernel_iff` is Theorem 8 as a THREE-WAY EQUIVALENCE between an integer
-- kernel, a trigonometric certificate and the master target of M1 Theorem 7.  The note's first
-- sanity check is here too: `exists_gap_of_pointwise` shows the parenthetical strong form
-- sup_Omega Q < c(0) really does supply the uniform gap, and `confCircle_ne_univ_of_kernel`
-- shows it forces X(alpha) != T, because int_T Q = c(0) is the trace -- so A POINTWISE KERNEL IS
-- NEVER MORE THAN M4/X8's CONFINEMENT GAP, and with `BB61/FullSupport.lean` it is EMPTY at
-- 1+sqrt2 and (3+sqrt5)/2 (`silver_not_pointwise_kernel`, `goldenSq_not_pointwise_kernel`).
-- Not here: the second sanity check (block recoding is neutral) is M2 Prop. 8 and is not
-- repeated; Gamma inside the full codifferent, which would need the solenoid characters the
-- repository does not have and which Theorem 8 says are inert; and the converse
-- PosSemidef -> Gram (Cholesky), absent from Mathlib and not needed.  Numerics
-- `BB61/m3_thm78_lean.py`, 8/8 verdicts at 50 dps: the Gram identity to 9.0e-49 with psd
-- eigenvalues, int_T Q = tr B, the measure computation on periodic-orbit measures, the
-- certificate's zero mean, Theorem 8(c)'s identity Q = c(0) - 2G exact, A CHECK THAT THE
-- CONSTRUCTION IS NOT A RE-DERIVATION (this file's Q and the note's A - G differ by at least
-- 3.73 in sup norm), sup_T Q >= c(0) always, and the anchor: an explicit convex combination of
-- 9 periodic orbits at 1+sqrt2 killing the first 4 Fourier modes, after which EVERY kernel of
-- that reach has int Q.F dmu = tr B to 1.8e-16 -- M3 section 7's c(alpha) = 0, re-derived from
-- Theorem 8(a).
-- `BB61/Tube.lean` is M3 Proposition 1, the audit verdict on move 3 of Route B: the tube
-- criterion Haar(T_K) < 1 is VACUOUS.  The plan wanted to kill tau_* lambda = Leb whenever the
-- tube T_K = {(u,w) : w in K_delta} is not all of the torus in measure, read "morally" as
-- Leb_{d-1}(K) small against the covolume of Sigma, with an expected coverage of every
-- quadratic Pisot alpha > 2 with |alpha_2| < 1/2.  THE COVERING QUESTION IS ONE-DIMENSIONAL
-- AND PURELY ALGEBRAIC: the tube is unrestricted in the first coordinate, so the first
-- coordinate of a lattice vector can always be absorbed and only the SHADOW
-- shadow Lambda = Prod.snd '' Lambda is ever tested -- `tube_add_eq_univ_iff` says
-- T_B + Lambda = R^d iff B + shadow Lambda = R^{d-1}, with no topology, no discreteness of
-- Lambda and no restriction on the degree.  `QuotientAddGroup.image_mk_eq_univ_iff` on the new
-- `ForMathlib/Topology/Algebra/DenseCover.lean` carries that to the torus and
-- `add_dense_eq_univ` (same file: non-empty interior plus a dense set is everything) closes it,
-- so `image_mk_tube_eq_univ` is the general-degree theorem with Dense (shadow Lambda) as its
-- ONLY input.  THE NOTE'S PONTRYAGIN DUALITY IS AVOIDABLE, which matters because Mathlib has
-- none: at degree two the shadow is Z + beta Z, beta^n lies in it by the integer recursion
-- (p,q) -> (q b, p + q a) (`beta_pow_mem_shadow`), is non-zero exactly when b != 0 since
-- alpha beta = -b (`alpha_mul_beta`), and tends to 0 -- so 0 is not isolated (`dense_shadow`).
-- No irrationality lemma either: a rational beta would be an integer of modulus < 1.  `prop1`
-- and `measure_prop1` are the two forms of the conclusion; `prop1_thickening` is the note's
-- "for every window K", the plan's tube being over the OPEN set K_delta so that nothing about K
-- is used; `no_tube_criterion` is the verdict.  `exists_tube_small_shadow` refutes the "morally
-- Leb_{d-1}(K)/covolume" reading quantitatively: for every eps > 0 a tube of base measure below
-- eps * covol still covers everything, covol = |alpha - beta| with covol^2 = a^2 + 4b.  THE
-- SHARP FORM IS `tube_window_dichotomy`, and it lands on Route B's own target family: for
-- |beta| < 1/2, M1 Lemma 3 (`BB61/BoxDim.lean`) gives dim_B K < 1, so the EXACT window is
-- Lebesgue-null (`volume_windowSet_eq_zero`) and a null base never covers, its trace
-- B + (Z + beta Z) being a countable union of null translates.  So delta -> Haar(T_{K_delta})
-- is identically 1 on delta > 0 and 0 at delta = 0, WITH NO VALUE IN BETWEEN: a continuous
-- kernel cannot concentrate on a null set, so the fattening is forced, and at every delta the
-- tube is the whole torus.  `silver_tube_window_dichotomy` and `goldenSq_tube_window_dichotomy`
-- instantiate at 1+sqrt2 and (3+sqrt5)/2.  Not here: degree > 2, where Dense (shadow Lambda)
-- stays a hypothesis (true, but the note's proof is duality and the contraction gives only
-- non-discreteness above dimension one); a Haar measure on the torus, which is not needed since
-- the set is everything; and Omega subset T_K, which is M1 and which Proposition 1 does not
-- use.  Numerics `BB61/m3_prop1_lean.py`, 8/8 verdicts at 80 dps, including the anchor P7: the
-- plan's own criterion quantity computed at the four named alpha and compared with the two
-- things it was supposed to be -- the Haar measure is 1 at every delta > 0, the Leb_1(K) it
-- bounds is 0, and it is neither.
-- `BB61/FullSupport.lean` is work package R0 of `plan-BB61-counterexample.html` (note
-- `note-1061-R0.html`), and it is the folder's first POSITIVE instance of confCircle: every
-- other criterion in BB61/ is of the form confCircle != univ, and nothing anywhere said
-- confCircle = univ.  At the two quadratic Pisot units in (2,3] the confinement set is
-- computed EXACTLY -- C(alpha) - K = [-sqrt2/2, 2+sqrt2/2] at alpha = 1+sqrt2
-- (`silver_confSet`, R0 Thm 1) and [0,2] at alpha = (3+sqrt5)/2 (`goldenSq_confSet`, R0
-- Cor. 3) -- so X(alpha) = T at both (`silver_confCircle`, `goldenSq_confCircle`).  The
-- engine is one covering lemma: if n + rL = L and rL >= 1 then the greedy digit
-- min n (Nat.floor w) keeps the residual in [0,L] for ever, so every point of [0,L] is a
-- base-r digit sum with digits in {0..n} (`tsum_covDigit`) -- R0 Lemma 2, whose m = 3 case is
-- Utz's theorem, reproved in SZ/CoverGame.lean.  At a norm +1 unit both halves of F~ are
-- digit systems in the SAME base with the same scale 1-beta, so F~ is a single {0,1,2} system
-- (`sub_wVal_eq_of_beta_eq_inv`) and Cor. 3 is the covering lemma applied once.  At the
-- norm -1 unit 1+sqrt2 the past sits in base -rho, and R0 (S2) removes the sign by the parity
-- relabelling delta_m <-> a_m (`parityFlip`, `tsum_dR_parityFlip`), at the price of the
-- constant sum_{m odd} rho^m -- which is EXACTLY 1/2 at this alpha (`silver_odd_sum`) and, by
-- R0 Prop. 4, at no other quadratic Pisot unit; (S3) then splits the remaining stream into
-- {0,1} + rho E (`silver_sub_wVal`).  The window endpoints come out as P = sqrt2/2 and
-- Q = 1 + sqrt2/2 (`silver_wMax`, `silver_wMin`), so the interval is the full convex hull
-- [-P, 1+Q] of length 1 + diam K = 2 + sqrt2 (`silver_confSet_length`) -- the largest it could
-- be, i.e. Theorem 1 computes the hull rather than covering an interval inside it.
-- Consequence, and the reason R0 is a gate: no support/gap argument can ever prove 10.61 at
-- either alpha (`silver_no_avoided_interval`, `goldenSq_no_avoided_interval`) -- the effective
-- criterion of BB61/Covering.lean is unavailable there, by a proof that uses neither Newhouse
-- thickness nor the gap lemma and carries no citation.  All std3.  Numerics `BB61/r0_lean.py`,
-- 10/10 verdicts at 60 digits: the Lean greedy is a DIFFERENT one from `BB61/r0_support.py`'s
-- (min n (Nat.floor w), not the largest admissible digit), so it produces different words, and
-- the reconstruction of (eps, delta) is re-verified against M1's original definitions of pi
-- and w over 801 targets per alpha, to 6e-61.
-- `BB61/Cantor.lean` is M1 Lemma 1 in full bar the dimension values: the attractor identity
-- and min/max (i), the gap iff alpha > 2 (ii), injectivity + the homeomorphism pi : {0,1}^N ~=
-- C(alpha) and Leb(C(alpha)) = 0 (iii), strong separation (iv), and the conjugacy
-- pi . sigma = tau_alpha . pi with the one-sided full 2-shift (v).  Nullity needs no dimension
-- theory: C(alpha) is the DISJOINT union of two copies of itself scaled by alpha^-1.  The
-- dimension VALUES of (iii) are in `BB61/BoxDim.lean` and `BB61/Hausdorff.lean` above, so
-- Lemma 1 is now machine-checked in full.
-- `BB61/Plateau.lean` is M1 Observation 16(ii), the mechanism behind M0's empirical "rho >= 1/alpha
-- with equality iff quadratic unit".  Division-free Binet (`lad_binet`) turns M7's dead zone into
-- the EXACT shape of the two weight bands of a ladder mode: future weight at depth j is A
-- alpha^{k-j} up to |e_0|(alpha-1)rho^k/((alpha-beta)alpha^j), past weight is (-b)^m B alpha^{k-m}
-- up to |e_0||beta-1|rho^{k+m}/(alpha-beta), both equalities.  The mirror is then one line
-- (`abs_shapePast_profile`): the past profile is the future profile times |b|^d |beta-1|/(alpha-1),
-- a CONSTANT exactly when |b| = 1 -- the whole dichotomy off the single identity alpha rho = |b|.
-- Two corrections to the note's part (i): at norm +1 there is no limit to take (the two one-sided
-- products are equal term by term, at every rung), and at norm -1 the limit converges at rate
-- rho^{2k} (`abs_future_band`, `abs_past_band`), a rate the note does not state.  Numerics
-- `BB61/m1_obs16.py` (mpmath at adaptive precision; float64 dies at k ~ 16/log10 alpha), 9/9 cases.
-- `BB61/WeylProduct.lean` is M1 Observation 16(i), which Plateau.lean left open: the two
-- one-sided Erdos products THEMSELVES.  With ncos x = |cos(pi x)|, futProd h = prod_{j>=1}
-- ncos(h(alpha-1)alpha^-j) and pastProd h = prod_{m>=0} ncos(h c_m) are Multipliable at every
-- real mode (the arguments decay geometrically and |ncos x - 1| <= pi |x - N|).  Along a ladder
-- the future factor converges to biProd(shapeFut) at EVERY quadratic alpha -- unit or not, the
-- note's "the future factor still settles" -- and the past factor to biProd(shapePast) at a unit,
-- where biProd x = prod_{n in Z} ncos(x alpha^n).  Both by the same two-line device: each factor
-- of the two products differs by at most pi times the Plateau profile error, and those errors sum
-- geometrically, so |futProd(h_k) - shapeProd k| <= pi |e_0| rho^k/(alpha-beta) while shapeProd k
-- is a one-sided truncation of biProd taken ever further out.  THE CORRECTION: (i) as stated is
-- FALSE for a general ladder.  The two limits are biProd(lambda(alpha-1)) and
-- biProd(lambda'(alpha-1)) (`biProd_shapePast_eq_shapeFutC`, off the trace identities
-- shapePast alpha^n + shapeFutC beta^n in Z and its mirror); they agree when lambda' = +- alpha^s
-- lambda (`biProd_shapePast_eq_of_pow`, using the two invariances `biProd_mul_alpha`/`biProd_neg`),
-- of which e_0 = -f_0, i.e. 2h_1 = a h_0, i.e. lambda rational, is the s = 0 case -- and BOTH of
-- the note's witnesses satisfy it.  Witness for the failure: alpha = (3+sqrt13)/2 with the ladder
-- 1, 4, 13, 43, 142, ...: future limit 0.4004074010, past limit 0.0126597907.  At norm +1 there
-- is no limit at all (`pastProd_eq_futProd`: the two products are equal at every mode, so
-- `weylProd h = futProd h ^ 2`).  Numerics `BB61/m1_obs16i.py`, 8/8 verdicts, mpmath.
-- `BB61/TraceLadder.lean` is M1 Proposition 15: the integer solutions of alpha's recurrence are
-- exactly the trace ladders Tr(lambda alpha^k) over the codifferent, and lambda |-> (h_k) is a
-- Z-module isomorphism d^-1 = R = Z^d -- so M0's open normalisation question ("is the ladder
-- Tr(alpha^k) or its half?") is answered by "neither, the ladder is the whole module", and the
-- choice of lambda inside it is worth a factor 452 at 1 + sqrt 2.  The mathematics is
-- `ForMathlib/NumberTheory/TraceLadder.lean`; this file adds the corpus attributes and the
-- degree-two bridge `QuadSetup.recModule_eq_range_lad` / `lad_iff_trace_ladder`, which says the
-- M7 ladders of `BB61/Ladder.lean` ARE R at d = 2, hence the trace ladders of any root of
-- X^2 - aX - b -- the licence for M7's search over lambda in the codifferent.
-- `BB61/Admissible.lean` is M1 Proposition 14, the licence for citing the theta-shift
-- literature ([BM86], [BM85]) at C(alpha) at all -- and the third job the hypothesis alpha > 2
-- does (use U3 of the note's section 5; U1 is the gap, U2 the entropy deficit).  The note
-- argues by Parry's criterion, which would need the quasi-greedy expansion d*(1,alpha) and
-- Parry's theorem, neither in Mathlib; the DEFINITION of admissibility is cheaper and gives
-- more.  `greedyExp_boolVal`: for alpha > 2 the greedy Renyi-Parry alpha-expansion of
-- pi(eps)/(alpha-1) = sum eps_k alpha^-k IS eps, so every {0,1}-word is admissible
-- (`isAdmissible_bitZ`; `range_bitZ_subset_closure_admissible` is the note's
-- {0,1}^N subset S_alpha verbatim) and the "(alpha-1) normalization" becomes an identity.
-- alpha > 2 enters through ONE sharp inequality: the tails stay in [0,1) iff the largest of
-- them, (alpha-1)^-1 = pi(1^inf)/(alpha-1), is < 1, i.e. iff alpha > 2
-- (`boolVal_const_true_lt_one_iff`).  The converse (`greedy_tsum`: on [0,1) a point is the sum
-- of its own expansion) makes the statement's "hence" an EQUALITY:
-- `cantorSet_eq_image_boolCoded`, C(alpha) = (alpha-1) B(alpha) with B(alpha) exactly the
-- points of [0,1) whose alpha-expansion is a {0,1}-word.
-- Also M1 Prop. 8 and Cor. 9: the master target of
-- `BB61/Invariant.lean` is an *equivalence*, its ergodic converse in `BB61/Realization.lean`
-- (via the vendored Birkhoff port) and the general one -- saturation of the full shift -- in
-- `BB61/Saturation.lean`, which needs no ergodic theorem: invariance makes the target an exact
-- mean of window averages, `BB61/MeanSelect.lean` realizes a mean by a greedily chosen
-- equal-weight sample, and `BB61/Words.lean` concatenates the samples into one digit word.
-- `BB61/PressureCriterion.lean` is M3 Theorem 12, the pressure criterion, on top of the new
-- `ForMathlib/Dynamics/TopologicalPressure.lean` (topological pressure over a partition and the
-- Jensen half of the variational principle -- neither is in Mathlib, and the Tau Ceti roadmap
-- has nothing on pressure or entropy either).  `BB61/Window.lean` closes the M4 chain at
-- alpha = 2 + sqrt 3: the window state observable, the exact Z[sqrt3] cell tables for all 128
-- words, and the Lebesgue mean of the cell potential, so that 10.61 at 2 + sqrt 3 rests on the
-- cited entropy floor alone (carried there as a hypothesis, not an axiom).  `BB61/Floor.lean`
-- discharges that floor from the root's ONE cited axiom, `LY.entropyRate_floor` of
-- CITED/LedrappierYoung.lean (M3 Thm 11; [You82] at d=2, [LY85], [BPS99]), giving the
-- unconditional `problem_10_61_two_add_sqrt3`.  That axiom is quarantined to CITED/ and appears
-- in exactly four declarations (AxCheck.lean checks it); everything else in BB61/ is std3.
-- Numerics/notes live in BB61/ alongside (m0_*.py, m1_*.py, m2_*.py).  Build-only
-- registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB61 where
  globs := #[.submodules `BB61]

-- Third-party port: the pointwise Birkhoff ergodic theorem, from `lua-vr/pointwise-birkhoff`
-- (Apache-2.0; Lua V. R., Oliver Butterley, Pietro Monticone) -- the one piece of ergodic theory
-- Mathlib still lacks (it has only the mean/von Neumann theorem,
-- `Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean`).  It is the missing input of BB61:
-- `BB61/Realization.lean` consumes it for M1 Prop. 8(i), the ergodic realization converse of the
-- master target of `BB61/Invariant.lean`; M5 Thm 1 needs it too.  (M1 Prop. 8(ii), the general
-- case, does *not*: `BB61/Saturation.lean` is Birkhoff-free.)  The `*PR.lean` modules are the
-- upstream authors' Mathlib-bound extraction lemmas.  Adapted here: `import Mathlib` replaced by
-- the actual dependencies, and the upstream `autoImplicit` binders written out, this package having
-- `autoImplicit := false`.  Per-file authorship is in each header, taken from the upstream `git
-- blame` (kept alongside as `*.lean.blame`).  Build-only registration; Extract.lean corpusRoots
-- registration + db regen: user's call.
lean_lib BirkhoffErgodicThm where
  globs := #[.submodules `BirkhoffErgodicThm]

-- Eliahou--Verger-Gaugry 2025 (C. R. Math. 363, 329--336; arXiv:2504.13716), ref "EVG25" --
-- the 3x+1 function seen through the rational base 3/2 number system of [AFS08].  What the note
-- *proves* about the link is `EVG25/Base3div2Basics.lean` and `EVG25/UniformCorrespondence.lean`,
-- brought over from the author's `../Collatz-Map-Basics` package with its imports, namespace and
-- references retargeted to this repository's CC/ root (`CC.Terras`, `CC.Decomposition`; both files
-- live in namespace `CC`, the digit layer in `CC.Base3div2`): Prop. 6, the equivalence of the
-- Collatz conjecture with "the proportion of even iterates of T tends to 1/2", the digit
-- dictionary <U(n)> = <n>1 or <n>2, the odometer, the parity criterion, and Conjectures 18/19
-- as `Prop` definitions with normality => digit-1 density and Conjecture 18 = the U-orbit
-- density at 0.  `EVG25/Question17.lean` formalizes what the note leaves *open*: Question 17 and
-- the question following Conjecture 18, i.e. whether the Collatz conjecture is equivalent to the
-- density-1/2 behaviour of the digits 1 in the base-3/2 words along U-orbits.  Stated in the
-- `formal-conjectures` idiom, with `answer(sorry)` marking the unknown answer of a yes/no
-- question (`EVG25/Answer.lean` is the trimmed port of that project's elaborator).  It is stated
-- about the CC/ objects themselves -- `CC.conjecture_U_orbit_density`, `CC.conjecture_4_2`, and
-- the 3x+1 conjecture inlined as `forall n >= 1, exists k >= 1, T_iter k n = 1`, per the standing
-- convention that it gets no decl of its own.  Its own sorry-free layer is what CC/ does not
-- carry: the digit counts of a base-3/2 word, the invariance of the digit-0 count along a
-- U-orbit, and the equivalence of the note's *word* form of the density (whose denominator is the
-- word length, growing from |<n0>|) with CC's parity form -- so `CC.numOnesSat` is the honest
-- digit count of <sat k> and `CC.conjecture_4_2` is Conjecture 18 as printed.  Only the `sorry`s
-- of the open statements themselves remain.  Build-only registration; Extract.lean corpusRoots
-- registration + db regen: user's call.
lean_lib EVG25 where
  globs := #[.submodules `EVG25]

-- Bugeaud Problem 10.47 (plans/plan-1047.html, refs "Bug12"/"BKK26"/"BK19"/"AB07") -- the
-- EVENTUAL block complexity p_infty(n, xi, b): the number of length-n blocks occurring
-- INFINITELY OFTEN in the base-b expansion.  Theorem W ("no algebraic irrational has
-- p_infty(n) = n+1 for all n") is open; this root machine-checks the layer of the paper
-- BB47/{M1M2,M3,M4}.tex that is a finite combinatorial statement about ONE one-sided word.
-- `Basic.lean`: recurrent blocks, `pInf`, the non-recurrent prefix `horizon` = [BKK26]'s s_n,
-- and the identity `pInf u n = pComplexity (tail u m) n` for every m >= s_n -- which makes the
-- single word `tail u s_{n+1}` compute p_infty at two consecutive levels, so ordinary
-- Morse-Hedlund gives strict monotonicity of p_infty (the rigidity lemma of M3) in two lines.
-- `Rauzy.lean` and `Degrees.lean`: strong connectivity of the reduced Rauzy graph (it uses the
-- ONE-sidedness of the word essentially), the degree bounds, the out-closed-set exclusion that is
-- the engine of M3's "the Coven-Hedlund non-Sturmian branch cannot occur", and the unique
-- right-/left-special block.  Since WP8 of plans/plan-subshift.html these two files PROVE none of
-- that: `BB47.recFactorSet u = recurrentLanguage u` is `rfl`, so they are thin corpus-facing
-- layers over `ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean`, which states the same results
-- for the language of an arbitrary subshift.  `edgeSrc`/`edgeTgt` are `export`ed, not redefined
-- (one constant, two names); `exists_walk` is retired in favour of `reach_recFactorSet`
-- (reachability as `Relation.ReflTransGen`, the window was never used for anything else); and the
-- degree-sum proof of `exists_unique_rightSpecial` is replaced by ForMathlib's existence +
-- uniqueness, with the bridge `isRightSpecial_iff_two_le_outDeg` and ONE remaining sum identity
-- fixing the exact values 2 and 1.  What stays local is what ForMathlib does not express:
-- `outDeg`/`inDeg` as Finset cards of fibres and `sum_outDeg`/`sum_inDeg`.  `LemmaA0.lean`: the repetition function r(n,w) and the pigeonhole
-- r(n,w) <= s_n + n + p_infty(n) -- the whole combinatorial content of Theorems A/A'.
-- `Cited.lean`: [BK19] Thm. 10.4, both clauses, as cited axioms; [AB07] Thm. 1 is the Subspace-Theorems library's.
-- `TheoremA.lean`: Theorems A and A', the n+k ladder, and the structure corollary.
-- `Certificate.lean`: the M4 certificates -- a finite prefix bounds s_n from BELOW only, and
-- exactly (Prop. 2.4), plus the ceiling (appending a recurrent minimal-complexity tail to ANY
-- prefix restores p_infty(n) = n+1), which is why 10.47 is not a computational question.
-- `PeriodicOrbits.lean`: the Fine-Wilf half of [M3, Lem. 3.3] -- two periodic words that share
-- ONE block of length p + q are shifts of each other, hence have the same language, the same
-- recurrent language and the same p_infty (the conclusion "P_1 = P_2").  No complexity
-- hypothesis, no finite alphabet, no subshift.  Uses `ForMathlib/Combinatorics/FineWilf.lean`.
-- `OmegaLimit.lean` (WP8) is the corpus-facing face of ForMathlib/Dynamics/SymbolicDynamics/ and
-- CLOSES the two items this root used to list as missing.  (i) [M1M2, Prop. 2.4]:
-- `pInf_eq_complexity` says p_infty(n,u) is the factor complexity of the SUBSHIFT Omega(u), whose
-- language is `recFactorSet u n` on the nose, and `coe_omegaLimitSubshift_eq_omegaLimit` says
-- Omega(u) really is Mathlib's omega-limit set of any two-sided extension.  (ii) [M3, Lem. 3.3]
-- COMPLETE: `orbit_eq_of_pInf_eq` -- under p_infty(n,u) = n+1 any two periodic points of Omega(u)
-- lie on the same orbit -- with `orbit_eq_of_pInf_succ_le` the sharper form, which needs the
-- hypothesis only at the single level p+q and does not need p,q least.  THE SHAPE LEMMA
-- [M3, Lem. 3.2] IS NOT NEEDED, only its degree half.  Also `mem_omegaLimitSubshift_iff_...`,
-- i.e. Omega(u) = inverse limit of its Rauzy graphs, the description plans/plan-1047.html Sec 2.2
-- takes as the definition.
-- `TheoremZ.lean` (2026-09-14) is THEOREM Z of BB47/af.md Sec 2, merged as plans/plan2-1047.html
-- Sec 3.1: lim (log p(n,u))/n = lim (log p_infty(n,u))/n for EVERY word over a finite alphabet,
-- both limits existing.  It is the first result in this root from the postponed note M5 rather
-- than from M1M2/M3/M4.  Neither proof in af.md is used: everything follows from the single count
-- p(m*k, u) <= s_m + p_infty(m,u)^k, valid at every (m,k) -- past s_m a length-mk block is a
-- concatenation of k recurrent length-m blocks, the rest live at the s_m early positions -- so
-- there is no Rauzy graph, no lambda_m, and NO FEKETE ARGUMENT, since holding at every m is what
-- subadditivity would have bought.  The additive constant depends on m alone and the exponential
-- on p_infty alone, so dividing by m*k and letting k -> infinity kills the horizon: h(u) is below
-- the LIMINF of (log p_infty(n))/n, while p_infty <= p puts it above the limsup, and all four
-- growth rates collapse at once.  Consequences: under (H) the WHOLE expansion has zero entropy
-- (`wordEntropy_eq_zero_of_pInf_eq_succ`, and `..._of_frequently` stated the way M3 states (H)),
-- although (H) constrains p(n,xi,b) at no fixed scale; and contrapositively
-- `exists_pInf_ne_succ_of_wordEntropy_pos` is CONJECTURE E => PROBLEM 10.47.  Growth rates are
-- `ExpGrowth.expGrowthSup` in `EReal`, the shape Mathlib's own `partitionTopEntropy` uses.
-- Needed and now in ForMathlib/Combinatorics/InfiniteComplexity.lean: `pComplexity_add_le`,
-- submultiplicativity p(a+b) <= p(a)p(b) for a ONE-sided word (the two-sided
-- `Subshift.complexity_add_le` was there from plan-subshift WP5 with nothing connecting it to
-- `Nat -> alpha`), and its k-fold form; `pComplexity_zero` moved there from Sturmian.lean.
-- Written up 2026-09-15 as BB47/M5.tex (17 pp.), whose Secs 1-3 are exactly this file.  The
-- drafting produced one status change for this root: Proposition C -- under (H) the expansion is
-- eventually confined to a proper SFT -- does NOT need balance (M3 Cor. 4.2) and therefore not the
-- Theorem-B chain, since a non-recurrent 01 or 10 forces an eventually periodic tail.  Prop. C(1)
-- and C(2) are the natural next target here: they need only `pInf`, `horizon` and
-- `IsEventuallyPeriodic`, all of which are in this root already.
-- `Confinement.lean` (2026-09-15) does exactly that: PROPOSITION C(1)-(2) of BB47/M5.tex.  (1)
-- `eventually_two_letters` -- p_infty(1)=2 gives two letters a != b carrying the word past s_1,
-- every other letter eventually omitted, with the count `ncard_omitted` = #alphabet - 2; the
-- bridge is `ncard_recLetters`, the number of letters occurring infinitely often IS p_infty(1).
-- (2) `exists_forbidden_square` -- one of the two letters has its square non-recurrent, so past
-- s_2 the tail avoids `aa` (`not_square_of_horizon_le`), which in base 2 is the golden-mean SFT;
-- packaged with (1) as `exists_pair_forbidden_square`.  The engine is
-- `isEventuallyPeriodic_of_no_transition`: past some point only a,b occur and a is never followed
-- by b => eventually periodic, which forbids a MIXED 2-block from being the non-recurrent one.
-- Consumes only `¬ IsEventuallyPeriodic u` and `pInf u 2 = 3` (the latter gives `pInf u 1 = 2` by
-- `pInf_eq_succ_of_le`).  Item C(3), the nested self-similar sets, is NOT formalized.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB47 where
  globs := #[.submodules `BB47]
