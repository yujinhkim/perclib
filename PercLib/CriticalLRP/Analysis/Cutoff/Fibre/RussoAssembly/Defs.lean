/-
# Standardized excluded-flux assembly: the named definitions

Definitions only, for swarm `smwu62ffl` member `m1` direction D1C.  Three objects are needed by
both the pointwise closed-event bridge and the expectation-level assembly, so they live here and
`D1CMain` imports this module.

* `exclIncr` — the real, closed-event excluded increment of the truncated cluster moment
  `|K_o ∩ A|`.  This is the integrand of the landed
  `SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_excl` with `o = 0`, given a name so that the
  `ℝ ↔ ℝ≥0∞` bridge can be stated once.
* `windowSum` — the ordered-pair excluded increment `pairIncr` summed over a square vertex window
  `X × X` at a finite truncation `A`; the right-hand side of the finite-window flux identity.
* `windowSumFull` — the same with the untruncated cluster volume `|K_c|` in place of
  `|K_c ∩ A|`.

No proof, no measure, no moment and no derivative enters: these are three definitions.

-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Full

/-!
The closed-event excluded increment `exclIncr` and the truncated / untruncated window sums
`windowSum`, `windowSumFull`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The excluded increment of the truncated cluster moment `|K_o ∩ A|` at the closed event of the
edge `{x,y}`: `|K_y ∩ A|` when `o ↔ x` but `o ↮ y`, `|K_x ∩ A|` in the mirror case.

This is the real integrand of the landed `SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_excl`
(with `o = 0`), given a name so that the `ℝ ↔ ℝ≥0∞` bridge below can be stated once. -/
noncomputable abbrev exclIncr (ω : Config V) (o : V) (A : Finset V) (x y : V) : ℝ :=
  (if Connects ω o x ∧ ¬ Connects ω o y then sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0) +
    (if Connects ω o y ∧ ¬ Connects ω o x then sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0)

/-- The ordered-pair excluded increment summed over the square window `X × X`, at truncation
`A`.  The object that the finite-window flux identity produces on its right-hand side. -/
noncomputable def windowSum (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A X : Finset V) : ℝ≥0∞ :=
  ∑ x ∈ X, ∑ y ∈ X, pairIncr d ω o A x y

/-- The untruncated window sum: the same with the full cluster volume `|K_c|`. -/
noncomputable def windowSumFull (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (X : Finset V) : ℝ≥0∞ :=
  ∑ x ∈ X, ∑ y ∈ X, pairIncrFull d ω o x y

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit of the definitions -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.exclIncr
#print axioms PercLib.CriticalLRP.Orchestration.windowSum
#print axioms PercLib.CriticalLRP.Orchestration.windowSumFull

end PercLib.CriticalLRP.Orchestration
