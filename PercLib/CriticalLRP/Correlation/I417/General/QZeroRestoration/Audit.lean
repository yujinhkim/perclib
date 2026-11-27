/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m8`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction d8.

# Axiom audit for the restored two-copy identification
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRestoration.ModelBridge

/-! # Axiom audit for the restored two-copy identification -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.I417Gen

#print axioms cluster_restoreMap_self
#print axioms cluster_restoreMap_eq_of_mem
#print axioms restoredConn_eq_starMoment
#print axioms restoredConn_two_one_eq_starMoment
#print axioms restoredConn_one_two_eq_starMoment
#print axioms restoredConn_one_one_eq_starMoment
#print axioms restoredConn_two_one_eq_one_two
#print axioms restoredTotal_eq_jointMoment
#print axioms restoredDiag_eq_rawDiff
#print axioms starMoment_three_eq_jointMoment
#print axioms starMoment_three_add_rawDiff_two_one

end PercLib.CriticalLRP.I417Gen

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms connCubeVertexMass_eq_restoredConn
#print axioms connCubeVertexMass_add_rawDiff_eq
#print axioms connCubeMass_eq_sum_restoredConn
#print axioms connCubeVertexMass_le_cutPoly_twoTerm_of_source_two_one
#print axioms connCubeVertexMass_le_twoTerm_of_source_two_one

end PercLib.CriticalLRP.Orchestration.SourceModelData
