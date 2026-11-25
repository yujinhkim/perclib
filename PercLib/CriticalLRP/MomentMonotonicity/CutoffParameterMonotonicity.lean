module

public import PercLib.CriticalLRP.MomentMonotonicity.MomentTransfer

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.CutoffMomentTransfer

open PercLib.CriticalLRP.CutoffKernel
open PercLib.CriticalLRP.CutoffLimit

/-- Increasing the intensity of a fixed Definition I.1.5 cutoff law cannot decrease
any cluster-volume moment. This follows from the common threshold coupling;
no sharpness or finite-moment hypothesis is made. -/
theorem cutoff_lintegral_clusterVol_pow_mono_beta {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r)
    {β γ : NNReal} (hβγ : β ≤ γ) (o : Fin d → ℤ) (q : ℕ) :
    (∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure (cutoffSymKernel K d r)
      (cutoffSymKernel_nonneg hK hr) β)) ≤
    (∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure (cutoffSymKernel K d r)
      (cutoffSymKernel_nonneg hK hr) γ)) := by
  let hnonneg := CutoffLimit.cutoffSymKernel_nonneg' hK d r
  exact lintegral_clusterVol_pow_mono_of_le
    (fun e => bernoulliEdgeProb_mono (cutoffSymKernel K d r) hnonneg hβγ e) o q

/-- The fourth-moment comparison used in the proof of Proposition I.4.2,
at a fixed cutoff and between any two intensities. -/
theorem cutoff_fourthMoment_mono_beta {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r)
    {β γ : NNReal} (hβγ : β ≤ γ) (o : Fin d → ℤ) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β)) ≤
    (∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) γ)) := by
  simpa only [Percolation.cardFun_eq_encard] using
    cutoff_lintegral_clusterVol_pow_mono_beta hK hr hβγ o 4

#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_lintegral_clusterVol_pow_mono_beta
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_fourthMoment_mono_beta

end PercLib.CriticalLRP.CutoffMomentTransfer
