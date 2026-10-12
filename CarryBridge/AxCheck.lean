/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryBridge.DubC2
import CarryBridge.DubC2Witness
import CarryBridge.DubC
import CarryBridge.Oda26
import CarryBridge.Z32Cert
import CarryBridge.Z32
import CarryBridge.Z32Type

/-! # Axiom audit of `CarryBridge/` — every theorem must be std3
(`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no `native_decide`.
Regenerate the list when a file is added.  `Z32Balance` is checked in `AxCheckBalance.lean`. -/

-- DubC2.lean
#print axioms CarryBridge.carry_orb
#print axioms CarryBridge.frequently_not_avoid_of_allPer
#print axioms CarryBridge.nuQ_cast
#print axioms CarryBridge.enc_div
#print axioms CarryBridge.enc_mod
#print axioms CarryBridge.enc_injective
#print axioms CarryBridge.rnext_val
#print axioms CarryBridge.cellArc_iff
#print axioms CarryBridge.mem_succList
#print axioms CarryBridge.certGraph_allPer
#print axioms CarryBridge.paramFacts_of_checked
#print axioms CarryBridge.checked_allPer
#print axioms CarryBridge.checked_lnoBranch_det
#print axioms CarryBridge.checked_polyGrowth_det
#print axioms CarryBridge.mem_roundSet_zero
#print axioms CarryBridge.checked_isPeelChain
#print axioms CarryBridge.checked_round_core
#print axioms CarryBridge.checked_isLRank_det
#print axioms CarryBridge.checked_detSim
#print axioms CarryBridge.checked_detTot
#print axioms CarryBridge.certGraph_allPer'
#print axioms CarryBridge.checked_keepGraph_functional
#print axioms CarryBridge.cycChecked_cyc_listed
#print axioms CarryBridge.div_lt_M
#print axioms CarryBridge.enc_dec
#print axioms CarryBridge.adj_of_mem_succList
#print axioms CarryBridge.allPer_certGraph_iff
#print axioms CarryBridge.not_allPer_of_pseudoOrbit
#print axioms CarryBridge.window
#print axioms CarryBridge.hPM_of
#print axioms CarryBridge.hPq_of
#print axioms CarryBridge.cover_genGraph
#print axioms CarryBridge.divisor_set_of_checked'
#print axioms CarryBridge.window_mirror
#print axioms CarryBridge.divisor_set_mirror_of_checked'
#print axioms CarryBridge.divisor_set_of_checked_hull'
#print axioms CarryBridge.entGraph_simulation
#print axioms CarryBridge.entGraph_superEigen
#print axioms CarryBridge.adj_folGraph
#print axioms CarryBridge.folGraph_rightResolving
#print axioms CarryBridge.exists_letter
#print axioms CarryBridge.reach_folGraph_iff
#print axioms CarryBridge.branching_iff
#print axioms CarryBridge.exists_injective_path'
#print axioms CarryBridge.finite_of_checked'
#print axioms CarryBridge.checked_iff_finite'
#print axioms CarryBridge.checkF_isLRank
#print axioms CarryBridge.not_branching_of_checkF'
#print axioms CarryBridge.exists_checked_of_checkF'
#print axioms CarryBridge.adj_folGraphZ
#print axioms CarryBridge.reach_folGraphZ_iff
#print axioms CarryBridge.mem_avoidLang
#print axioms CarryBridge.sofic_of_checked
#print axioms CarryBridge.rnext_mod_eq
#print axioms CarryBridge.shadow_root
#print axioms CarryBridge.shadow_isSimulation
#print axioms CarryBridge.avoidLang_mono'
#print axioms CarryBridge.adj_resGraph
#print axioms CarryBridge.adj_primeGraph
#print axioms CarryBridge.adj_resGraph_iff_piProduct
#print axioms CarryBridge.rstep_eq_detStep
#print axioms CarryBridge.rstep_prodSet
#print axioms CarryBridge.coe_prodR
#print axioms CarryBridge.testBit_mstep_eq
#print axioms CarryBridge.rstep_prodR'
#print axioms DubC2.Gen.dimH_eventually_avoids_le'
-- DubC2Witness.lean
#print axioms CarryBridge.exists_pseudoOrbit_of_horseOK
#print axioms CarryBridge.not_allPer_of_horseOK
#print axioms CarryBridge.not_checked_of_horseOK'
#print axioms CarryBridge.exists_iPath_of_branchOK
#print axioms CarryBridge.not_allPer_of_branchOK
#print axioms CarryBridge.not_checked_of_branchOK'
-- DubC.lean
#print axioms CarryBridge.adj_digitGraph
#print axioms CarryBridge.under_digitGraph
#print axioms CarryBridge.under_digitGraph_eq
#print axioms CarryBridge.cyc_digitGraph
#print axioms CarryBridge.coreClosed_iff
#print axioms CarryBridge.certOK_iff_isRank
#print axioms CarryBridge.digit_eq_of_target
#print axioms CarryBridge.certOK_iff_isLRank
#print axioms CarryBridge.certOK_iff_noBranch
#print axioms CarryBridge.digits_eventually_periodic_of_certOK'
#print axioms CarryBridge.infinite_composites_floorPow_of_certOK'
#print axioms CarryBridge.coreClosed_of_rankOn'
#print axioms CarryBridge.coreClosed_of_rankRevOn'
#print axioms CarryBridge.coreClosed_of_ladder'
#print axioms CarryBridge.noBranch_of_coreCert
#print axioms CarryBridge.exists_certOK_of_coreCert
#print axioms CarryBridge.certOK_iff_polyGrowth
#print axioms CarryBridge.certOK_iff_entropy
#print axioms CarryBridge.certOK_iff_allEvPer
#print axioms CarryBridge.certOK_iff_entropy_labelled
#print axioms CarryBridge.coreClosed_core
#print axioms CarryBridge.coreClosed_of_core_subset
#print axioms CarryBridge.noBranch_six_thirty
#print axioms CarryBridge.noBranch_not_coreDet_four
#print axioms CarryBridge.adj_reducedGraph
#print axioms CarryBridge.cop_natCast
#print axioms CarryBridge.coprime_fourteen_mul
#print axioms CarryBridge.red_eq_val
#print axioms CarryBridge.cop_red
#print axioms CarryBridge.step_val
#print axioms CarryBridge.exists_unit_lift
#print axioms CarryBridge.digitGraph_rightCover
#print axioms CarryBridge.npaths_full_eq_reduced
#print axioms CarryBridge.certOK_full_iff_reduced'
-- Oda26.lean
#print axioms CarryBridge.adj_ofWG
#print axioms CarryBridge.toWG_ofWG
#print axioms CarryBridge.isSingle_toWG
#print axioms CarryBridge.reach_toWG
#print axioms CarryBridge.reach_ofWG
#print axioms CarryBridge.odaAllPer_toWG_iff
#print axioms CarryBridge.odaAllPer_iff
#print axioms CarryBridge.allCert_iff_det
#print axioms CarryBridge.allCert_iff_wordGrowth
#print axioms CarryBridge.isSingle_oneStep
#print axioms CarryBridge.isSingle_oneStepU
#print axioms CarryBridge.isSingle_gPrime
#print axioms CarryBridge.allPer_of_proj
#print axioms CarryBridge.allCert_oneStepU_iff
#print axioms CarryBridge.covers_iff_wCovers
#print axioms CarryBridge.odaAllPer_iff_subdivide
#print axioms CarryBridge.allCert_iff_subdivide
-- Z32Cert.lean
#print axioms CarryBridge.card_blk_le
#print axioms CarryBridge.Cert.exists_carry_period_le'
#print axioms CarryBridge.Cert.exists_escape_le'
#print axioms CarryBridge.adj_rotGraph
#print axioms CarryBridge.rotGraph_functional
#print axioms CarryBridge.allPer_of_functional
#print axioms CarryBridge.blockRank_le
#print axioms CarryBridge.adj_rankAt
#print axioms CarryBridge.isIPath_ranks
#print axioms CarryBridge.carry_eq_branch
#print axioms CarryBridge.isEventuallyPeriodic_carry_of_certifiedK'
#print axioms CarryBridge.exists_carry_period_of_certifiedK'
#print axioms CarryBridge.exists_escape_le_of_certifiedK'
#print axioms CarryBridge.not_confined_of_certifiedK'
#print axioms CarryBridge.Cert.eq_of_memI_block'
#print axioms CarryBridge.Cert.ok_eq_false_of_infinite_hold'
#print axioms CarryBridge.Cert.ok_eq_false_of_infinite_cycles'
-- Z32.lean
#print axioms CarryBridge.adj_blkGraph
#print axioms CarryBridge.mem_outEdges_iff
#print axioms CarryBridge.isLRank_blkGraph
#print axioms CarryBridge.functional_blkGraph
#print axioms CarryBridge.lnoBranch_blkGraph
#print axioms CarryBridge.allPer_blkGraph
#print axioms CarryBridge.isIPath_blocks
#print axioms CarryBridge.Cert.not_confined'
#print axioms CarryBridge.card_modelLang_le_of_cert'
#print axioms CarryBridge.not_cert_and_horse'
-- Z32Type.lean
#print axioms CarryBridge.adj_typeGraph
#print axioms CarryBridge.tlet_cast
#print axioms CarryBridge.typeGraph_rightResolving
#print axioms CarryBridge.sum_arcsFrom
#print axioms CarryBridge.typeGraph_isSuperEigen
#print axioms CarryBridge.typeGraph_isSubEigen
#print axioms CarryBridge.entropy_typeGraph_le
#print axioms CarryBridge.le_entropy_typeGraph
#print axioms CarryBridge.exists_iPath_of_modelOrbit
#print axioms CarryBridge.map_mem_words_of_reads
#print axioms CarryBridge.exists_modelOrbit_of_isWord
#print axioms CarryBridge.card_modelLang_eq_words
