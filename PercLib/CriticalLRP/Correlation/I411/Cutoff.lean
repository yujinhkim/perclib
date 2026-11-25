/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.Correlation.I411.RealQuotient
public import PercLib.CriticalLRP.VolumeMoments.SecondMomentCutoff

/-
The I.4.11 error estimate at the Definition I.1.5 cutoff law, with the
first-moment and triangle-finiteness inputs explicit.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.I411

open MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

/-- At the source cutoff law, finite expected cluster volume and a finite
windowed triangle diagram imply the covariance error bound of Lemma I.4.11.
No second or third moment is separately assumed. -/

theorem lemma_I_4_11_cutoff_of_firstMoment (K : ℝ → ℝ)
    (hK : AntitoneOn K (Set.Ioi 0)) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (β : NNReal) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (h1 : (∫⁻ ω, Percolation.cardFun (cluster ω 0)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞)
    (hDfin : (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
      twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β 0 a *
        twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β a b *
        twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β b y) ≠ ∞) :
    let A : ℝ≥0∞ := ∫⁻ ω, clusterVol ω 0
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        (B.card : ℝ)⁻¹ * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
              (CutoffKernel.cutoffSymKernel_nonneg hK hr) β 0 a *
            twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
              (CutoffKernel.cutoffSymKernel_nonneg hK hr) β a b *
            twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
              (CutoffKernel.cutoffSymKernel_nonneg hK hr) β b y).toReal := by
  have h2 := Hvol.cutoffSecondMoment_ne_top_of_firstMoment K hK d r hr β 0 h1
  have hnonneg := Hvol.lemma_I_4_7_cutoff_of_secondMoment K hK d r hr β 0 B hB h2
  have hAfin : (∑' w : Fin d → ℤ, twoPointFunction
      (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β 0 w) ≠ ∞ := by
    rw [← lintegral_clusterVol_eq_tsum_twoPoint
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β 0]
    simpa only [Percolation.cardFun_eq_encard] using h1
  have hJfin := Hvol.cutoffJointSecondMoment_ne_top_of_firstMoment K hK d r hr β 0 B h1
  refine ⟨?_, lemma_I_4_11_of_finite (CutoffKernel.cutoffSymKernel_shift K d r)
    (CutoffKernel.cutoffSymKernel_nonneg hK hr) β B hB hAfin hJfin hDfin⟩
  simpa only [Percolation.cardFun_eq_encard] using hnonneg.1

end PercLib.CriticalLRP.I411
