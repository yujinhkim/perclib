/-
# Definitions for cutoff flux localisation and open-coordinate resampling

Independently reviewed intermediate packet from swarm `smwtvrwnn` member `m6`, direction D1A.
The finite transport needed for a summable per-vertex majorant is not supplied by these definitions.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv
public import PercLib.CriticalLRP.BK.TwoCopy

/-!
Cutoff cluster densities and standardized edge weights.  The standardized weight divides by the
open-edge probability and therefore requires a positive-probability premise in its applications.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- `E_b[|K_0| · 1{y ∈ K_0}]`: the mixed density whose sum over `y` is the full quadratic
cutoff moment. -/
noncomputable def mixedFluxDensity (b : ℝ) (y : M.V) : ℝ := by
  classical
  exact (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
    (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b)).toReal

/-- The probability that the single edge `e` is open under the cut law at radius `r`. -/
noncomputable def openProb (r : ℝ) (e : Sym2 M.V) : ℝ :=
  (M.cutLaw r).real {ω : Config M.V | e ∈ ω}

/-- The **standardized** cut-off edge weight `c_r(e) / q_e(r)`. -/
noncomputable def stdEdgeWeight (r : ℝ) (e : Sym2 M.V) : ℝ :=
  M.cutEdgeDeriv r e / M.openProb r e

end SourceModelData

end PercLib.CriticalLRP.Orchestration
