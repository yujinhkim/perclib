/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Defs

/-!
# The strict-window excluded mass at a cut-off corner

Swarm `smwv6er9k`, member `m5`, direction B5.

`E1Sign.exclMass M r` integrates the excluded expectation
`E_{β_c,r}[|K| ∑_{y ∈ B_r} 1(y ∉ K) |K_y|]` over the *closed* lattice window
`B_r = {ρ ≤ r}`.  When `r` crosses an attained radius (`M.attainedRadii = M.cornerRadii`,
the norms of lattice points) the window acquires the sphere `{ρ = r}`, so the excluded mass
has no reason to be continuous there, and only the *strict* window survives a left limit.
This definition layer names the strict-window objects and the sphere layer of the pair mass:

* `exclMarkFunLt M r` — the mark-space integrand of the strict-window excluded mass;
* `exclMassLt M r` — the strict-window excluded mass, in `ℝ≥0∞`;
* `exclScalarLt M r` — its `ℝ`-form, the candidate left limit of `M.exclScalar`;
* `rhsScalarLt M r = β_c (-K'(r)) · exclScalarLt` — the candidate left-hand derivative value;
* `pairSphereMass M r` — the closed-window sphere layer `{ρ = r}` of the pair mass.

No continuity, finiteness, or limit statement is asserted here; those are in the consumer
module `LeftExcludedMass.Main`, each with its moment hypotheses explicit.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The mark-space integrand of the *strict*-window excluded mass: the expression of
`E1Sign.exclMass`, with the closed window `B_r` replaced by `{ρ < r}`. -/
noncomputable def exclMarkFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => M.markVol r u *
    ∑ y ∈ M.ballFLt r,
      ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
        (fun _ => (1 : ℝ≥0∞)) y * clusterVol (atParameter (M.cutProb r) u) y

/-- The strict-window excluded mass.  This is the `ℝ≥0∞` object whose `toReal` is the left
limit of `M.exclScalar`; it is the excluded expectation over `{ρ < r}` at the cutoff `r`. -/
noncomputable def exclMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.exclMarkFunLt r u ∂(markMeasure M.V)

/-- The strict-window excluded mass in `ℝ`. -/
noncomputable def exclScalarLt (r : ℝ) : ℝ := (M.exclMassLt r).toReal

/-- The scalar factor of the *left-hand* derivative at a corner, `β_c (-K'(r))` times the
strict-window excluded mass. -/
noncomputable def rhsScalarLt (r : ℝ) : ℝ := M.coeffRHS r * M.exclScalarLt r

/-- The closed-window sphere layer `{ρ = r}` of the pair mass.  It is the exact difference
between `E1Sign.pairMass M r` and the strict-window pair mass `M.pairMassLt r`. -/
noncomputable def pairSphereMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.markVol r u *
    ∑ y ∈ (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) = r),
      clusterVol (atParameter (M.cutProb r) u) y ∂(markMeasure M.V)

end SourceModelData

end PercLib.CriticalLRP.Orchestration
