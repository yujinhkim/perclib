/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The strict-window marked window masses of the `p = 2` excluded RHS

Swarm `smwvc1d9z`, member `m4`, direction `d3`.

Integration donor: `.ultramath/smwvc1d9z/m4`; independently checked at
`4bb37c4a38e226728ba0b9d8732d9ddebbbdded3`.  Definitions only: no proof, no axiom.

`SecondMoment/Regularity/Defs` names the three monotone marked window masses

* `quadPairMass r  = E[|K_0| ∑_{y∈B_r}|K_y|²]`,
* `sqLinPairMass r = E[|K_0|² ∑_{y∈B_r}|K_y|]`,
* `connCubeMass r  = E[|K_0|³ #(K_0 ∩ B_r)]`

on the *closed* window `E1Sign.ballF M r = {y | ρ y ≤ r}`, and `SecondMoment/Regularity/Main`
proves that `p2RHS = quadPairMass + 2 sqLinPairMass - 3 connCubeMass` and that each of the three is
right continuous in the cut-off radius.

The fixed-radius masses are *not* continuous from the left when the closed window is used: as
`r ↑ r₀` the closed window `B_r` only exhausts the strict window `{ρ < r₀} = M.ballFLt r₀`, so the
left limit is a strict-window mass at the same law `cutLaw r₀`.  This file is the definition layer
of that statement: the same three integrands with `E1Sign.ballF M r` replaced by `M.ballFLt r`.
The masses are the `p = 2` companions of `connMassLt`/`pairMassLt`, i.e. of the strict-window
objects whose left limits are the landed `ConnMassRegularity`/`PairMassRegularity` statements.

Nothing here differentiates in the radius, assumes a moment, or converts `⊤` to a real number; every
object is `ℝ≥0∞`-valued.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.ConnMassRegularity.Main

/-!
# The strict-window marked masses at `p = 2`

`quadPairFunLt`/`quadPairMassLt`, `sqLinPairFunLt`/`sqLinPairMassLt` and
`connCubeFunLt`/`connCubeMassLt` are the exact strict-window (`{ρ < r}`) companions of the three
closed-window masses of `SecondMoment/Regularity/Defs`.
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

/-! ## 1. The strict-window integrands -/

/-- The mark-space integrand of `E[|K_0| ∑_{y∈B_{<r}}|K_y|²]`: the `ℓ = 0` marked window sum of
(I.4.1) at `p = 2` over the *strict* window `M.ballFLt r = {y | ρ y < r}` and at the law
`cutLaw r`.  It is `quadPairFun` with the closed window replaced by the strict one. -/
noncomputable def quadPairFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u *
    ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y ^ 2

/-- `E[|K_0| ∑_{y∈B_{<r}}|K_y|²]`, the strict-window companion of `quadPairMass`. -/
noncomputable def quadPairMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.quadPairFunLt r u ∂(markMeasure M.V)

/-- The mark-space integrand of `E[|K_0|² ∑_{y∈B_{<r}}|K_y|]`: the `ℓ = 1` marked window sum of
(I.4.1) at `p = 2` over the strict window and at the law `cutLaw r`. -/
noncomputable def sqLinPairFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u ^ 2 *
    ∑ y ∈ M.ballFLt r, clusterVol (atParameter (M.cutProb r) u) y

/-- `E[|K_0|² ∑_{y∈B_{<r}}|K_y|]`, the strict-window companion of `sqLinPairMass`. -/
noncomputable def sqLinPairMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.sqLinPairFunLt r u ∂(markMeasure M.V)

/-- The mark-space integrand of `E[|K_0|³ #(K_0 ∩ B_{<r})]`, the `y ∈ K_0` part of the `p = 2`
window sums, over the strict window and at the law `cutLaw r`.  It is `connCubeFun` with the
closed window replaced by the strict one. -/
noncomputable def connCubeFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u ^ 3 *
    ∑ y ∈ M.ballFLt r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y

/-- `E[|K_0|³ #(K_0 ∩ B_{<r})]`, the strict-window companion of `connCubeMass`. -/
noncomputable def connCubeMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.connCubeFunLt r u ∂(markMeasure M.V)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.quadPairMassLt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sqLinPairMassLt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMassLt
