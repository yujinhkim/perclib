/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.EdgeMajorant

/-!
# The scalar outer factor of the off-corner Russo derivative: definitions

The off-corner derivative value produced by the landed conditional theorem is the product
`β_c (-K'(r)) (exclMass r).toReal`.  This file names its two scalar factors and their product:

* `exclScalar r = (E1Sign.exclMass M r).toReal`, the excluded mass in `ℝ`;
* `coeffRHS r = β_c (-K'(r))`, the coefficient;
* `rhsScalar r = coeffRHS r * exclScalar r`.

Nothing is proved here.  The window bounds for `exclMass` and `rhsScalar`, the reduction of the
continuity of `rhsScalar` to the continuity of `exclScalar`, and the endpoint form of the landed
conditional derivative are in `ScalarFactor.Main`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- The excluded mass as a real number: the scalar that multiplies `β_c (-K'(r))`. -/
noncomputable def exclScalar (r : ℝ) : ℝ := (E1Sign.exclMass M r).toReal

/-- The coefficient `β_c (-K'(r))` of the off-corner derivative value. -/
noncomputable def coeffRHS (r : ℝ) : ℝ := (M.betaCrit : ℝ) * (-(deriv M.K r))

/-- The scalar factor `β_c (-K'(r)) (exclMass r).toReal` of the off-corner derivative value. -/
noncomputable def rhsScalar (r : ℝ) : ℝ := M.coeffRHS r * M.exclScalar r

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclScalar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.coeffRHS
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.rhsScalar

end PercLib.CriticalLRP.Orchestration
