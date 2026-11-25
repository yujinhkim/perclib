/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.Correlation.ThirdMoment.ArmDecomposition
public import PercLib.CriticalLRP.CountableProduct.LRPTailBounds
public import PercLib.CriticalLRP.CutoffDominated

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.Native

open MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.CutoffLimit

variable {V : Type*} [Countable V]

/-- The third-moment tree bound at the loop-safe Definition I.1.5 cutoff kernel.
No moment-finiteness or graph hypothesis remains after translation invariance
of the cutoff profile is discharged. -/
theorem third_moment_cutoff {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (r : ℝ) (β : NNReal) :
    (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 3
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤
      3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ^ 5 := by
  have hcomm (β : NNReal) (a b : Fin d → ℤ) :
      twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β a b
        = twoPointFunction (CutoffKernel.cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β 0 (b - a) :=
    twoPointFunction_eq_origin (CutoffKernel.cutoffSymKernel_shift K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β a b
  have h := third_moment_native (V := Fin d → ℤ)
    (π := bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    (fun a b => by
      simpa only [tau, twoPointFunction, longRangeMeasure, connSet, conn,
        edgeMeasure_eq_law] using hcomm β a b)
  simpa only [longRangeMeasure] using h

end PercLib.CriticalLRP.TreeExpansion.Native

namespace PercLib.CriticalLRP.Hvol

open MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.CutoffLimit

attribute [local instance] Classical.propDecidable

/-- The cutoff error bound after Lemma I.4.7, with the native arm decomposition
instantiated. Only finite first moment remains for the real quotient. -/
theorem cE1_le_three_mul_cube_div_cutoff {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (r : ℝ) (β : NNReal)
    (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω 0)
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        3 * A.toReal ^ 3 / B.card := by
  let := Encodable.ofCountable (Sym2 (Fin d → ℤ))
  simp only [longRangeMeasure] at *
  exact Hrest.cE1_le_three_mul_cube_div_of_finite
    (π := bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    (bernoulliEdgeProb_lt_one (fun e => cutoffSymKernel_nonneg' hK d r e) β)
    0 B hB
    (Percolation.edgeExhaustion (E := Sym2 (Fin d → ℤ)))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover
    (∫⁻ ω, Percolation.cardFun (cluster ω 0)
      ∂(edgeMeasure (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β))) rfl
    (fun y _ => hvol_cardFun
      (bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) 0 y) hAfin
    (by simpa only [longRangeMeasure] using
      TreeExpansion.Native.third_moment_cutoff (K := K) hK r β)

end PercLib.CriticalLRP.Hvol
