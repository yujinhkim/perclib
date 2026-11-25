/- Integrated from independently rebuilt Ultramath work.
Production base e756a603f08962e545c3c11bf9dd877b46c80d6f.
Scratch source: ../../.ultramath/smwvp122a/m2/M2/Audit.lean.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction.Main

/-!
# Standard-axiom audit

Each printed declaration must depend only on `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry`, `admit`, `native_decide` or custom axiom in
the proof modules.  The `#print` commands are the only content of this file,
which is why the `linter.hashCommand` style linter is switched off here only.
-/

@[expose] public section

open PercLib.CriticalLRP.VolumeMoments.HigherMoments

set_option linter.hashCommand false

#print axioms SecondInduction.abs_weighted_sum_sub_le
#print axioms SecondInduction.weighted_average_abs_le
#print axioms SecondInduction.targetSum_eq_weight_sum
#print axioms SecondInduction.sum_range_p_split
#print axioms SecondInduction.normalizedSum_zero_term
#print axioms SecondInduction.normalizedSum_last_term
#print axioms SecondInduction.targetWeight_mul_mom_one
#print axioms SecondInduction.normalizedSum_mid_term
#print axioms SecondInduction.ratio_abs_le_of_parts
#print axioms SecondInduction.normalizedSum_tendsto
#print axioms SecondInduction.derivative_ratio_tendsto
#print axioms SecondInduction.moment_asymptotic_of_decorrelation
#print axioms SecondInduction.induction_hypothesis_three
#print axioms SecondInduction.moment_three_asymptotic_of_decorrelation
#print axioms SecondInduction.mixedMoment_one
#print axioms SecondInduction.mixedMoment_two
#print axioms SecondInduction.moment_asymptotic_all
