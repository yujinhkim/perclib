/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# Axiom audit for the two-term `q = 0` consumer packet
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.ENNRealBridge
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Sharp
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Diagonal
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.OffDiag

/-! # Axiom audit for the two-term `q = 0` consumer packet -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417QZeroConsumer.one_le_chi
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.cutTwoPoint_eq_toReal
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.one_le_Kpow_diag
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.cutTwoPointE_le_Kpow
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.cutTwoPoint_le_polyK
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.sharpProfile_implies_twoTermStarGap
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.tsum_polyK_row
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.summable_polyK_row
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.tsum_starRHS
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.not_absorbable_ell_one
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.not_absorbable_ell_two
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.source_exponents
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.connCubeMass_toReal_le_of_twoTermStarGap
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.p2ExclError_le_of_twoTermStarGap
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.pointwise_driver_three_obstructed
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.starRHSE_ne_top
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.starRHSE_toReal
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.twoTermStarGapE_toReal
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.twoTermStarGap_toE
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.tsum_cutTwoPoint_row
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.summable_cutTwoPoint_row
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.connCubeMass_toReal_le_of_sharpProfile
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.p2ExclError_le_of_sharpProfile

/-! ## Diagonal and off-diagonal additions -/

#print axioms PercLib.CriticalLRP.I417QZeroConsumer.connCubeVertexMass_zero
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.powMomentAt_cutProb
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.cutMoment_two_sq_le
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.sharpProfile_forces_cutMoment_three
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.sharpProfile_diag_no_go
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.zero_mem_ballF
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.connCubeMass_toReal_le_of_twoTermStarGap_offDiag
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.p2ExclError_le_of_offDiag
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.tau_cutProb
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.tau_cutProb_translate
#print axioms PercLib.CriticalLRP.I417QZeroConsumer.connCubeVertexMass_zero_le
#print axioms
  PercLib.CriticalLRP.I417QZeroConsumer.connCubeMass_toReal_le_of_twoTermStarGap_offDiag_three
