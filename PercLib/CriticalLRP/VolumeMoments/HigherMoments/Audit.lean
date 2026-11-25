/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/Audit.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Main

/-!
# Standard-axiom audit

Each printed declaration must depend only on `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry`, `admit`, `native_decide` or custom axiom in
the proof modules.  The `#print` commands are the only content of this file,
which is why the `linter.hashCommand` style linter is switched off here only.
-/

@[expose] public section

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.middle_sum_eq
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.drivingTerm_regularlyVarying
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.drivingTerm_RVPosData
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.sum_bound
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.mixedMoment_regularlyVarying
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.derivative_bound
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.induction_hypothesis_three
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_three
#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation
#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation_unfolded
