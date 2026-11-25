/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Axiom audit for the Case 2 decorrelation development of Proposition I.4.20.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Comparator

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Analysis.I420Case2

#print axioms lintegral_mul_le_rpow_half
#print axioms jointMoment_le_cs
#print axioms jointMoment_le_of_bounds
#print axioms mul_rpow_pow
#print axioms sqrt_bound_le
#print axioms exists_eps_sqrt_mul_lt
#print axioms Mr_eventually_le
#print axioms ballCard_eventually_ge
#print axioms isLittleO_iff_eventually_le
#print axioms case2_decorrelation_error
#print axioms interVol_le_maxClusterInBall
#print axioms jointUpper_eventually_le
#print axioms jointUpper_isLittleO

end PercLib.CriticalLRP.Analysis.I420Case2
