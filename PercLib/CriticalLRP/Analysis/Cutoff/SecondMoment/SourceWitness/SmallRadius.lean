/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceWitnessSmallRadius

/-!
# Direct second-moment computation below the witness's shortest edge length

If the closed source ball is contained in the singleton of the origin, then both excluded sums in
`p2RHS` vanish: the only possible summand is excluded by membership of the origin in its own
cluster. At the literal power-law witness this happens for every `r < 2`, while every cutoff moment
is exactly `1`. Thus the real second moment is locally constant on `(-∞, 2)`, and its derivative
is exactly `β_c r^{-d-α-1} (p2RHS r).toReal = 0`.

This is an unconditional computation in the degenerate regime strictly below the shortest source
edge length. No `hfluxMono`, `hfluxConv`, finite-window exhaustion or radius-exchange hypothesis is
used. It does not prove a derivative at or above radius `2`, nor the general Lemma I.4.1.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-- If the ball contains only the origin, its quadratic excluded sum is zero at every
configuration. No law or moment-finiteness assumption is needed. -/
theorem exclSumQuad_eq_zero_of_ballF_subset_singleton_zero {r : ℝ}
    (hB : E1Sign.ballF M r ⊆ ({0} : Finset M.V)) (ω : Config M.V) :
    M.exclSumQuad r ω = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hy0 : y = 0 := by simpa using hB hy
  subst y
  simp [cluster_mem_self]

/-- The same origin-only ball makes the linear excluded sum vanish at every configuration. -/
theorem exclSumLin_eq_zero_of_ballF_subset_singleton_zero {r : ℝ}
    (hB : E1Sign.ballF M r ⊆ ({0} : Finset M.V)) (ω : Config M.V) :
    M.exclSumLin r ω = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hy0 : y = 0 := by simpa using hB hy
  subst y
  simp [cluster_mem_self]

/-- The entire `p = 2` excluded right-hand side vanishes when the source ball is
 contained in the singleton of the origin. -/
theorem p2RHS_eq_zero_of_ballF_subset_singleton_zero {r : ℝ}
    (hB : E1Sign.ballF M r ⊆ ({0} : Finset M.V)) :
    M.p2RHS r = 0 := by
  simp [SourceModelData.p2RHS, SourceModelData.exclMassQuad,
    SourceModelData.exclMassSqLin, M.exclSumQuad_eq_zero_of_ballF_subset_singleton_zero hB,
    M.exclSumLin_eq_zero_of_ballF_subset_singleton_zero hB]

end SourceModelData

namespace Witness

open PercLib.CriticalLRP.Orchestration

/-- Below radius `2`, every lattice point in the closed source ball is the origin. -/
theorem sourceModelWitness_ballF_subset_singleton_zero (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r < 2) :
    E1Sign.ballF (sourceModelWitness d hd α hα) r ⊆
      ({0} : Finset (sourceModelWitness d hd α hα).V) := by
  intro y hy
  simp only [Finset.mem_singleton]
  by_contra hy0
  have hdist : (sourceModelWitness d hd α hα).S.dist y 0 ≤ r :=
    ((sourceModelWitness d hd α hα).mem_ball_iff_dist_le y r).mp
      ((E1Sign.mem_ballF (sourceModelWitness d hd α hα)).mp hy)
  have htwo := sourceModelWitness_two_le_dist d hd α hα hy0
  linarith

/-- The source `p = 2` derivative weight is zero below the shortest edge length. -/
theorem p2RHS_sourceModelWitness_eq_zero_of_lt_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).p2RHS r = 0 :=
  (sourceModelWitness d hd α hα).p2RHS_eq_zero_of_ballF_subset_singleton_zero
    (sourceModelWitness_ballF_subset_singleton_zero d hd α hα hr)

/-- Every real cutoff moment of the source witness is `1` below radius `2`. -/
theorem cutMomentReal_sourceModelWitness_eq_one_of_lt_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) (p : ℕ) {r : ℝ} (hr : r < 2) :
    (sourceModelWitness d hd α hα).cutMomentReal p r = 1 := by
  change ((sourceModelWitness d hd α hα).cutMoment p r).toReal = 1
  rw [sourceModelWitness_cutMoment_eq_one_of_le_two d hd α hα hr.le p]
  exact ENNReal.toReal_one

/-- **Unconditional small-radius `p = 2` off-corner derivative at the power-law witness.**

Equality with the source coefficient times `p2RHS` comes by direct evaluation: locally the real
second moment is `1` and the excluded right-hand side is `0`. This statement covers `r₀ < 2`,
including its nonpositive values where the cutoff data remain degenerate, and takes no flux,
monotonicity, exhaustion or finiteness hypotheses. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_of_lt_two (d : ℕ) (hd : 1 ≤ d)
    (α : ℝ) (hα : 0 < α) {r0 : ℝ} (hr0 : r0 < 2) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have hconst : (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r) =ᶠ[𝓝 r0]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hr0] with r hr
    exact cutMomentReal_sourceModelWitness_eq_one_of_lt_two d hd α hα 2 hr
  have hderiv : HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r) 0 r0 := by
    simpa using (hasDerivAt_const (x := r0) (c := (1 : ℝ))).congr_of_eventuallyEq hconst
  rw [p2RHS_sourceModelWitness_eq_zero_of_lt_two d hd α hα hr0, ENNReal.toReal_zero, mul_zero]
  exact hderiv

end Witness

end PercLib.CriticalLRP.Orchestration

end

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_eq_zero_of_ballF_subset_singleton_zero
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_ballF_subset_singleton_zero
#print axioms PercLib.CriticalLRP.Orchestration.Witness.p2RHS_sourceModelWitness_eq_zero_of_lt_two
#print axioms PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_of_lt_two
