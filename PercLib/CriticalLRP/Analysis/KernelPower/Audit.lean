/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Check.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Axiom audit for the exports of this development (direction A, member m1).
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Nonvacuity

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelPower

-- definitions
#print axioms KpowF
#print axioms Kpow
#print axioms KpowS

-- finite submatrix level
#print axioms KpowF_eq_matpow
#print axioms posSemidef_entry_sq_le
#print axioms matrix_pow_entry_sq_le
#print axioms KpowF_sq_le

-- infinite level
#print axioms Kpow_one
#print axioms KpowS_mono
#print axioms KpowS_succ
#print axioms Kpow_eq_iSup_KpowS
#print axioms KpowS_le_Kpow
#print axioms Kpow_le_diag

-- translation invariance and the connection kernel
#print axioms Kpow_le_diag_of_shift
#print axioms Kpow_congr
#print axioms Kpow_ofReal_toReal
#print axioms Kpow_add_invariant
#print axioms Kpow_diag_eq
#print axioms tau_Kpow_le_diag
#print axioms tau_Kpow_iSup_diag

-- the two-point function of the long-range model on `Fin d → ℤ`
#print axioms twoPointFunction_eq_tau
#print axioms posSemidef_twoPointFunction
#print axioms toVec_sub_add
#print axioms radialSym_shift
#print axioms cutKernel_shift
#print axioms kernel_shift
#print axioms twoPointFunction_Kpow_le_diag
#print axioms twoPointFunction_Kpow_iSup_diag
#print axioms SourceModelData.cutTwoPoint_Kpow_le_diag
#print axioms SourceModelData.cutTwoPoint_Kpow_iSup_diag
#print axioms SourceModelData.twoPoint_Kpow_le_diag

-- non-vacuity
#print axioms sourceModelData_nonempty
#print axioms exists_sourceModel_cutKpow_iSup_diag

end PercLib.CriticalLRP.KernelPower
