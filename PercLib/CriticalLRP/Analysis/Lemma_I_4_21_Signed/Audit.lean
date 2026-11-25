module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21_Signed.I421Signed
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21_Signed.CrossCheck

/-! Statement and axiom audit for the signed form of Lemma I.4.21. -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Analysis.I421Signed

/-! ### Exact statements -/

#check @exists_shared_error_of_tendsto_signed
#check @exists_shared_error_of_tendsto
#check @exists_shared_error_of_tendsto'
#check @lemma_I_4_21_tendsto_of_hasDerivAt
#check @lemma_I_4_21_regularlyVarying_of_hasDerivAt
#check @lemma_I_4_21_eventually_pos_of_hasDerivAt
#check @lemma_I_4_21_signed
#check @lemma_I_4_21_of_differentiableAt
#check @lemma_I_5_5_branch_of_lt
#check @tendsto_two_term_error_of_driving_ode
#check @signed_hypotheses_with_sign_changing_f
#check @lemma_I_5_26_signed_ode_via_I_4_21

/-! ### Axioms -/

#print axioms exists_shared_error_of_tendsto_signed
#print axioms exists_shared_error_of_tendsto
#print axioms exists_shared_error_of_tendsto'
#print axioms lemma_I_4_21_tendsto_of_hasDerivAt
#print axioms lemma_I_4_21_regularlyVarying_of_hasDerivAt
#print axioms lemma_I_4_21_eventually_pos_of_hasDerivAt
#print axioms lemma_I_4_21_signed
#print axioms lemma_I_4_21_of_differentiableAt
#print axioms lemma_I_5_5_branch_of_lt
#print axioms tendsto_two_term_error_of_driving_ode
#print axioms signed_hypotheses_with_sign_changing_f
#print axioms lemma_I_5_26_signed_ode_via_I_4_21

end PercLib.CriticalLRP.Analysis.I421Signed
