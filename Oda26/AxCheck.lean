/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.Family
import Oda26.Jacobsthal
import Oda26.WaitingTime
import Oda26.FiniteSuccess
import Oda26.AllEdge
import Oda26.OneStep
import Oda26.PrimePrefixLong
import Oda26.NormalForm
import Oda26.RankFromCert

/-!
# Axiom hygiene for the `Oda26` root

Every claimed declaration should depend only on `propext, Classical.choice, Quot.sound`.
Rebuild this module to check.  (The [Oda26] obstructions transported to `DubC2.Gen.Checked` live
in `DubC2/Obstruction.lean` and `DubC2/Budget.lean` and are checked in `DubC2/AxCheck.lean`.)
-/

-- WP1: recurrence, orbit basics, word arithmetic
#print axioms Oda.copying
#print axioms Oda.residue_recurrence
#print axioms Oda.composite_frequently_of_recurrent
#print axioms Oda.not_recurrent_of_eventually_prime
#print axioms Oda.pow_dvd_of_carry_period
#print axioms Oda.Qf_succ_gt
#print axioms Oda.carry_mem_alphabet
#print axioms Oda.carryAlphabet_zero
#print axioms Oda.cf_bounds
#print axioms Oda.cf_parity_gcd
#print axioms Oda.WG.cellGraph_zero
#print axioms Oda.window_realized
#print axioms Oda.modEq_of_same_word
#print axioms Oda.theta0_mem
#print axioms Oda.dvd_iff_root
#print axioms Oda.prime_eq_seed
#print axioms Oda.translation_iff
-- App. C (Lemma 52, Proposition 53)
#print axioms Oda.Fam.T_conj
#print axioms Oda.Fam.carries_eq_iff
-- §8.4: Jacobsthal bound
#print axioms Oda.sieveCount_bound
#print axioms Oda.jacobsthal_prod_le
#print axioms Oda.jacobsthal_prime
#print axioms Oda.jacobsthal_mul_primes
-- §6.2: Theorem 27
#print axioms Oda.periodic_stay
#print axioms Oda.waiting_time
-- §3: one-step method
#print axioms Oda.WG.oneStep_zero
#print axioms Oda.WG.oneStep_edge
#print axioms Oda.WG.retained_tail
#print axioms Oda.WG.cell_refine
#print axioms Oda.WG.joint_enlargement
#print axioms Oda.WG.finite_certification
-- §4: word-labelled graphs
#print axioms Oda.WG.eventually_sameSCC
#print axioms Oda.WG.Covers.output_of_certified
#print axioms Oda.WG.exists_delta_ne_zero
#print axioms Oda.WG.models_removal
#print axioms Oda.WG.visits_B
#print axioms Oda.WG.models_contract
#print axioms Oda.WG.models_of_contract
#print axioms Oda.WG.models_lift
#print axioms Oda.WG.models_cellGraph
#print axioms Oda.WG.finite_success
#print axioms Oda.WG.composite_frequently
#print axioms Oda.WG.certified_of_det
#print axioms Oda.WG.all_edge_test
#print axioms Oda.WG.certified_rootPath
#print axioms Oda.WG.rootCert_iff
#print axioms Oda.WG.dvd_delta_iff
-- App. E.1: Lemma 67 (std3) and Theorem 68 (cites `PNT.theta_div_tendsto`, `Shao.narrow_ap`)
#print axioms Oda.transplant
#print axioms Oda.long_prime_prefix
-- §7: Lemmas 29–31, Props 35–36, Theorems 33 and 37 (normal form)
#print axioms Oda.WG.allCert_iff_allPer
#print axioms Oda.WG.label_mem_alphabet
#print axioms Oda.WG.proj_edge
#print axioms Oda.WG.exists_lift
#print axioms Oda.WG.allPer_gPrime_iff
#print axioms Oda.WG.XExec.tracks
#print axioms Oda.WG.XExec.allCert
#print axioms Oda.WG.normal_form
#print axioms Oda.WG.rankCertOf
#print axioms Oda.WG.waiting_time_of_allCert
