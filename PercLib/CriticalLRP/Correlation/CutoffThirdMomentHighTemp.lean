module

public import PercLib.CriticalLRP.PowerLawHighTemp
public import PercLib.CriticalLRP.Correlation.CutoffThirdMoment

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.CriticalLRP

namespace PercLib.CriticalLRP.TreeExpansion.Native

/-- At the paper's power-law profile and in the existing high-temperature interval,
the finite-range cutoff has a finite third cluster-volume moment. -/
theorem modelProfile_cutoff_thirdMoment_ne_top_of_highTemperature {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {r : ℝ} {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (FiniteVolume.linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) :
        ℝ≥0∞) < 1) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω 0)) ^ 3
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel (FiniteVolume.modelProfile d α) d r)
        (CutoffLimit.cutoffSymKernel_nonneg'
          (FiniteVolume.modelProfile_antitoneOn d (by positivity)) d r) β)) ≠ ∞ := by
  let K := FiniteVolume.modelProfile d α
  have hKnn : ∀ t : ℝ, 0 < t → 0 ≤ K t :=
    (PowerLawHighTemp.modelProfile_side_conditions hα).1
  have hK0 : K 0 = 0 := (PowerLawHighTemp.modelProfile_side_conditions hα).2
  have hanti : AntitoneOn K (Set.Ioi 0) :=
    FiniteVolume.modelProfile_antitoneOn d (by positivity)
  have huncut :
      (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure
        (TreeExpansion.kernelJ (fun y : Fin d → ℤ => K ((FiniteVolume.linfNorm y : ℕ) : ℝ))
          (CutoffLimit.profile_even (d := d) K))
        (CutoffLimit.uncutKernel_nonneg hKnn hK0 d) β)) ≠ ⊤ :=
    PowerLawHighTemp.modelProfile_uncutFirstMoment_ne_top hd hα hβ 0
  have hfin :
      (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffLimit.cutoffSymKernel_nonneg' hanti d r) β)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top huncut ?_
    exact lintegral_clusterVol_mono_of_le
      (fun e => CutoffDominated.bernoulliEdgeProb_le_of_mul_le
        (CutoffLimit.cutoffSymKernel_nonneg' hanti d r)
        (CutoffLimit.uncutKernel_nonneg hKnn hK0 d)
        (mul_le_mul_of_nonneg_left
          (CutoffLimit.cutoffSymKernel_le_uncut hKnn hK0 r e) β.2)) 0
  refine ne_top_of_le_ne_top ?_ (third_moment_cutoff hanti r β)
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top (by simpa only [Percolation.cardFun_eq_encard] using hfin))

#print axioms PercLib.CriticalLRP.TreeExpansion.Native.modelProfile_cutoff_thirdMoment_ne_top_of_highTemperature

/-- A concrete non-vacuity witness at `β = 0`. -/
example : (∫⁻ ω, (Percolation.cardFun (cluster ω 0)) ^ 3
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel
        (FiniteVolume.modelProfile 1 1) 1 0)
        (CutoffLimit.cutoffSymKernel_nonneg'
          (FiniteVolume.modelProfile_antitoneOn 1 (by norm_num)) 1 0) 0)) ≠ ∞ :=
  modelProfile_cutoff_thirdMoment_ne_top_of_highTemperature (d := 1) le_rfl zero_lt_one (by simp)

end PercLib.CriticalLRP.TreeExpansion.Native
