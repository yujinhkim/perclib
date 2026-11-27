module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffAllMoments
public import PercLib.CriticalLRP.MomentMonotonicity.ReducedMomentTransfer

/-! # All cutoff moments from subcritical first-moment finiteness -/

@[expose] public section

noncomputable section

open MeasureTheory unitInterval
open scoped ENNReal NNReal

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

/-- At every positive normalized cutoff radius, finite uncut first moments at every
strictly subcritical intensity imply all critical cutoff cluster moments. -/
theorem cutMoment_ne_top_of_subcritical_first (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤)
    {r : ℝ} (hr : 0 < r) (q : ℕ) : M.cutMoment q r ≠ ⊤ := by
  have hfirst : M.cutMoment 1 r ≠ ⊤ := by
    rw [← M.cutMassAt_zero_eq_cutMoment]
    exact M.cutMassAt_ne_top_of_subcritical hβ hsub hr
  exact cutMoment_ne_top_of_one M r hfirst q

#print axioms cutMoment_ne_top_of_subcritical_first

end PercLib.CriticalLRP.Orchestration
