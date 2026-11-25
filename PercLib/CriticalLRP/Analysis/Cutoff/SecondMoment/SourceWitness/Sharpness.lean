/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.OffCorner
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.LargeRadiusMoments

/-!
# Second-moment off-corner derivative under subcritical sharpness input

The nondegenerate `p = 2` off-corner derivative assembled in `OffCorner.lean` retains finiteness of
the fourth cutoff moment at each radius in its window as its analytic input. The existing
`SourceModelData.cutMoment_ne_top_of_subcritical_first` transfers finite uncut first moments at all
strictly subcritical intensities to every cutoff moment of order at most four. Instantiating it at
`p = 4` produces the required local fourth-moment input exactly, without assuming it at the critical
intensity or asserting a uniform critical-moment bound.

The remaining hypotheses are exactly the source phase-transition sharpness input and positivity of
`betaCrit`, the off-corner window, the interior differentiation point, and the off-sphere
condition. No fourth-moment hypothesis is claimed away from a trivially empty cutoff law.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- **Subcritical sharpness implies the off-corner second-moment derivative at the witness.**

The fourth-moment hypothesis of
`hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner` is discharged through the existing
first-moment transfer. The theorem still requires the uncut mean to be finite at every strictly
subcritical intensity and positivity of the critical parameter; it does not construct those data
or infer them from vanishing percolation probability. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit)
    (hsub : ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
      (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
        ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤)
    {a b r0 : ℝ} (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin har hrb
    (fun t ht => (sourceModelWitness d hd α hα).cutMoment_ne_top_of_subcritical_first
      hβ hsub (p := 4) (by norm_num) (lt_trans hwin.1 ht.1)) hsphere

end PercLib.CriticalLRP.Orchestration.Witness

end

#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical
