/-
Accepted from Ultramath `smwzg77c3`, member `m4`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Axiom audit for the `q = 0`, `p = 3` reduction packet

Every theorem below must depend only on Lean's three standard axioms.  There is no `sorry`,
no `admit`, no `native_decide`, no custom axiom and no fabricated upstream moment anywhere in
`Defs.lean` / `Main.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroReduction.Main

set_option linter.hashCommand false

/-! # Axiom audit -/

open PercLib.CriticalLRP.M4QZero

-- susceptibility and polygon powers
#print axioms PercLib.CriticalLRP.M4QZero.one_le_clusterVol
#print axioms PercLib.CriticalLRP.M4QZero.one_le_cutMassAt_zero
#print axioms PercLib.CriticalLRP.M4QZero.one_le_chi
#print axioms PercLib.CriticalLRP.M4QZero.chi_nonneg
#print axioms PercLib.CriticalLRP.M4QZero.Kpow_le_succ
#print axioms PercLib.CriticalLRP.M4QZero.Kpow_mono_exponent
#print axioms PercLib.CriticalLRP.M4QZero.polyK_mono_exponent
#print axioms PercLib.CriticalLRP.M4QZero.tau_le_Tpow_three

-- the reduction
#print axioms PercLib.CriticalLRP.M4QZero.hgap_of_treeFour
#print axioms PercLib.CriticalLRP.M4QZero.hgap_of_treeClasses
#print axioms PercLib.CriticalLRP.M4QZero.degree_five_class_not_absorbable
#print axioms PercLib.CriticalLRP.M4QZero.deep_class_not_absorbable
#print axioms PercLib.CriticalLRP.M4QZero.hgap_of_tauChi
#print axioms PercLib.CriticalLRP.M4QZero.hgap_of_KpowTwoTerm
#print axioms PercLib.CriticalLRP.M4QZero.hgap_of_cutPolyTwoTerm
#print axioms PercLib.CriticalLRP.M4QZero.twoTermTarget_polyK

-- invariance
#print axioms PercLib.CriticalLRP.M4QZero.polyK_shift
#print axioms PercLib.CriticalLRP.M4QZero.polyK_root_indep
#print axioms PercLib.CriticalLRP.M4QZero.starMoment_shift
#print axioms PercLib.CriticalLRP.M4QZero.starMoment_root_indep
#print axioms PercLib.CriticalLRP.M4QZero.twoTermTargetAt_iff
#print axioms PercLib.CriticalLRP.M4QZero.chi_root_indep
