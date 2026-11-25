/-
Critical LRP I: absolute summability of the normalized pivotal mass series.

Swarm `smwv2c2lw`, member `m3`, direction d3.  Self-contained packet: no production writes, no
axioms beyond the three standard ones.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.NormalizedAggregate.Main

/-!
# The normalized pivotal mass is a convergent edge series

`normalizedPivotMass y r` is defined as a real `tsum` over all edges.  This file proves that the
series is absolutely summable whenever the first cutoff moment is finite and the kernel factor
`cutKernelFactor r = β_c (-K'(r)) exp (β_c K r)` does not vanish, so the defining `tsum` is a
genuine convergent series and not Lean's junk value at a divergent `tsum`.

The proof is the landed per-edge domination of the singleton flux by the touching probability
(`pivotalFlux_singleton_le_touchProb`) together with the landed first-moment majorant
`summable_hdom_of_cutMoment`, transported through the exact factorization
`cutEdgeDeriv = cutKernelFactor * cutPivotFactor`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Absolute summability of the singleton flux series** at a positive radius with finite first
cutoff moment.  No kernel-factor nonvanishing is needed here. -/
theorem summable_cutEdgeDeriv_mul_pivotalFlux_singleton {y : M.V} {r : ℝ} (hr : 0 < r)
    (hvol : M.cutMoment 1 r ≠ ⊤) :
    Summable fun e : Sym2 M.V => M.cutEdgeDeriv r e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  classical
  have hdom := M.summable_hdom_of_cutMoment hr hvol
  have hpivnonneg : ∀ e : Sym2 M.V, 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    intro e
    rw [pivotalFlux]
    exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω
  have hterm : ∀ e : Sym2 M.V,
      |M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
        ≤ |M.cutEdgeDeriv r e| *
          (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
    intro e
    rw [abs_mul, abs_of_nonneg (hpivnonneg e)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hpiv := M.pivotalFlux_singleton_le_touchProb (r := r) y e
    rw [M.cutLaw_eq_edgeMeasure r] at *
    linarith [measureReal_nonneg (μ := edgeMeasure (M.cutProb r))
      (s := {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})]
  have habs : Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e| :=
    hdom.of_nonneg_of_le (fun e => abs_nonneg _) hterm
  exact habs.of_abs

/-- **Absolute summability of the normalized pivotal mass series.**  At a positive radius with
finite first cutoff moment, nonzero critical parameter and nonzero kernel derivative, the edge
series defining `normalizedPivotMass y r` is absolutely summable. -/
theorem summable_normalizedPivotMass_series {y : M.V} {r : ℝ} (hr : 0 < r)
    (hvol : M.cutMoment 1 r ≠ ⊤) (hβ : (M.betaCrit : ℝ) ≠ 0) (hK' : deriv M.K r ≠ 0) :
    Summable fun e : Sym2 M.V => M.cutPivotFactor r e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  classical
  have hκ : M.cutKernelFactor r ≠ 0 := by
    rw [cutKernelFactor]
    exact mul_ne_zero (mul_ne_zero hβ (neg_ne_zero.mpr hK')) (Real.exp_ne_zero _)
  have hflux := M.summable_cutEdgeDeriv_mul_pivotalFlux_singleton (y := y) hr hvol
  have hrel : ∀ e : Sym2 M.V, M.cutPivotFactor r e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = (M.cutKernelFactor r)⁻¹ * (M.cutEdgeDeriv r e *
        pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) := by
    intro e
    rw [M.cutEdgeDeriv_eq_kernelFactor_mul_pivotFactor r e]
    field_simp
  exact (hflux.mul_left (M.cutKernelFactor r)⁻¹).congr fun e => (hrel e).symm

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms summable_cutEdgeDeriv_mul_pivotalFlux_singleton
#print axioms summable_normalizedPivotMass_series
