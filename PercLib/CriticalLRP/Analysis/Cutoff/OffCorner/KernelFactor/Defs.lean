/-
Critical LRP I: kernel-factor split of the off-corner cutoff derivative weight.

Swarm `smwuinbxz`, member `m3`, direction d3.  Self-contained definitions only: no production
writes, no new axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main

/-!
# Kernel factor and normalized pivotal mass of the off-corner cutoff flux

The cutoff edge weight of a non-loop edge of length `d ≤ r` is

`β_c (-K'(r)) · exp (-(β_c (K d - K r)))`.

Every activated edge shares the factor `β_c (-K'(r)) exp (β_c K r)`, and the remaining factor
`exp (-(β_c K d))` is *independent of the radius* except for the activation condition `d ≤ r`.
Splitting the weight this way separates the two sources of `r`-dependence of the infinite
singleton flux: the kernel derivative `K'` (through `cutKernelFactor`) and the law (through the
normalized pivotal mass `normalizedPivotMass`).

The definitions here are used by `OffCornerKernelFactor/Main.lean`, which proves the factorization
and derives from it both the continuity transfer and the necessary regularity of `deriv M.K`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The kernel factor `β_c (-K'(r)) exp (β_c K r)` common to every activated edge weight at
radius `r`. -/
noncomputable def cutKernelFactor (r : ℝ) : ℝ :=
  (M.betaCrit : ℝ) * (-(deriv M.K r)) * Real.exp ((M.betaCrit : ℝ) * M.K r)

/-- The normalized cutoff factor of an edge: `exp (-(β_c K d))` on the non-loop edges of length
`d ≤ r`, and `0` on loops and beyond the cutoff radius. -/
noncomputable def cutPivotFactor (r : ℝ) : Sym2 M.V → ℝ :=
  radialSym M.S (fun s => if s ≤ r then Real.exp (-((M.betaCrit : ℝ) * M.K s)) else 0)

/-- The normalized total pivotal mass of the singleton cluster indicator `1{y ∈ K_0}` at cutoff
radius `r`: the sum over all edges of the normalized cutoff factor times the single-edge pivotal
flux. -/
noncomputable def normalizedPivotMass (y : M.V) (r : ℝ) : ℝ :=
  ∑' e : Sym2 M.V, M.cutPivotFactor r e *
    pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e

end SourceModelData

end PercLib.CriticalLRP.Orchestration
