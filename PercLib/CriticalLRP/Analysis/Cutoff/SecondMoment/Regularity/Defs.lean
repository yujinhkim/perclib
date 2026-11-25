/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The three monotone marked window masses of the `p = 2` excluded RHS

Swarm `smwvauwsr`, member `m1`, direction `d1`.  Definitions only: no proof, no axiom.

The landed `p = 1` radius machinery can only compare integrands that are *monotone* in the cut-off
radius, and the `p = 2` excluded window sums of Hutchcroft, *Critical long-range percolation I*,
Lemma I.4.1 carry the antitone indicator `1(y ∉ K_0)`.  This file names the three unexcluded marked
window masses that replace them exactly (see `P2Regularity/Split.lean` for the splits):

* `quadPairFun r` / `quadPairMass r`   — integrand and mass of `E[|K_0| ∑_{y∈B_r}|K_y|²]`,
  the `ℓ = 0` window sum of (I.4.1) at `p = 2` without the excluded indicator;
* `sqLinPairFun r` / `sqLinPairMass r` — integrand and mass of `E[|K_0|² ∑_{y∈B_r}|K_y|]`,
  the `ℓ = 1` window sum without the excluded indicator;
* `connCubeFun r` / `connCubeMass r`   — integrand and mass of `E[|K_0|³ · #(K_0 ∩ B_r)]`,
  the `y ∈ K_0` part that is subtracted by both splits (the landed `connMarkFun` with mark
  weight `|K_0|³`).

Everything is stated in the common mark space `markMeasure M.V` of `atParameter (M.cutProb r)`, on the
*closed* window `E1Sign.ballF M r`, exactly as `SecondMoment/Defs.lean` states the excluded sums.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs

/-!
# Unexcluded window masses for the second cutoff moment

Three marked window masses on the closed source ball, with monotonicity and
radius-increment comparisons.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The three monotone marked window masses -/

/-- The mark-space integrand of `E[|K_0| ∑_{y∈B_r}|K_y|²]`: the `ℓ = 0` window sum of
(I.4.1) at `p = 2` *without* the excluded indicator. -/
noncomputable def quadPairFun (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u *
    ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y ^ 2

/-- `E[|K_0| ∑_{y∈B_r}|K_y|²]`, the unexcluded `ℓ = 0` companion of `exclMassQuad`. -/
noncomputable def quadPairMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.quadPairFun r u ∂(markMeasure M.V)

/-- The mark-space integrand of `E[|K_0|² ∑_{y∈B_r}|K_y|]`: the `ℓ = 1` window sum of
(I.4.1) at `p = 2` *without* the excluded indicator. -/
noncomputable def sqLinPairFun (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u ^ 2 *
    ∑ y ∈ E1Sign.ballF M r, clusterVol (atParameter (M.cutProb r) u) y

/-- `E[|K_0|² ∑_{y∈B_r}|K_y|]`, the unexcluded `ℓ = 1` companion of `exclMassSqLin`. -/
noncomputable def sqLinPairMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.sqLinPairFun r u ∂(markMeasure M.V)

/-- The mark-space integrand of `E[|K_0|³ #(K_0 ∩ B_r)]`, the `y ∈ K_0` part of both `p = 2`
window sums.  It is the landed `connMarkFun` with the mark weight `|K_0|³` instead of
`|K_0|²`. -/
noncomputable def connCubeFun (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u ^ 3 *
    ∑ y ∈ E1Sign.ballF M r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y

/-- `E[|K_0|³ #(K_0 ∩ B_r)]`. -/
noncomputable def connCubeMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.connCubeFun r u ∂(markMeasure M.V)


end SourceModelData

end PercLib.CriticalLRP.Orchestration
