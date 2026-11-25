/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Equal moment generating functions determine the distribution

Mathlib's `Mathlib/Probability/Moments/ComplexMGF.lean` records the TODO
"once we know that equal `mgf` implies equal distributions, we will be able to show that the
`complexMGF` are equal everywhere".  This file does that:

`Measure.eq_of_mgf_eq`: two probability measures on `ℝ` with the same mgf, the mgf being finite in a
neighbourhood of the origin, coincide.

The hypothesis is necessary (an mgf which is infinite near `0` carries no information, e.g. the
Cauchy distribution).  Proof: Mathlib's `eqOn_complexMGF_of_mgf` gives equality of the complex mgfs on
the vertical strip `{z | z.re ∈ interior (integrableExpSet id μ)}`, which contains the imaginary axis;
evaluating there gives equality of the characteristic functions, and `Measure.ext_of_charFun`
concludes.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.MomentProblem

/-- **Equal moment generating functions determine the distribution**, provided the mgf is finite in a
neighbourhood of the origin. -/
theorem Measure.eq_of_mgf_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ProbabilityTheory.mgf id μ = ProbabilityTheory.mgf id ν)
    (h0 : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet id μ)) : μ = ν := by
  have hEq := ProbabilityTheory.eqOn_complexMGF_of_mgf (X := id) (Y := id) h
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hmem : ((t : ℂ) * Complex.I) ∈
      {z : ℂ | z.re ∈ interior (ProbabilityTheory.integrableExpSet id μ)} := by
    simp only [Set.mem_ofPred_eq, Complex.mul_I_re]
    simpa using h0
  have h1 := hEq hmem
  rw [ProbabilityTheory.complexMGF_id_mul_I, ProbabilityTheory.complexMGF_id_mul_I] at h1
  exact h1

end PercLib.CriticalLRP.MomentProblem

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.MomentProblem.Measure.eq_of_mgf_eq
