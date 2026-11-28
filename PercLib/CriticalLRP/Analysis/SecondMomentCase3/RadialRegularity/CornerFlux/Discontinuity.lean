/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m3.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m3/Discontinuity.lean`.
-/

module

/-
Direction (F), capstone: from two-point non-degeneracy to a corner of the summed flux.

`Corner.lean` proves that the pivotal mass of the direct edge at the attained radius `‖y‖` is
exactly the two-point gap `1 - τ_{β_c,‖y‖}(0,y)`, and `SumLevel.lean` proves that a positive
corner pivotal mass forces the full first-moment flux to be discontinuous at `‖y‖`.  Here we
supply the two-point input from the *uncut* critical two-point function, using the model's own
monotone comparison `cutoff_mono_beta_and_le_uncut`:

* `cutTwoPoint_le_twoPoint`:  `τ_{β_c,r}(0,y) ≤ τ_{β_c}(0,y)` for every `r ≥ 0`;
* `directPivot_pos_of_twoPoint_lt_one`: `τ_{β_c}(0,y) < 1 ⇒` positive corner pivotal mass;
* `not_continuousAt_firstFlux_of_twoPoint_lt_one`: the summed flux has a corner at `‖y‖`.

The remaining measure-side residual is exactly `τ_{β_c}(0,y) < 1`, which is what the paper's
two-point upper bounds (HD Cases 2 and 3 of `Orchestration.Defs.HD`) provide at large `‖y‖`.
-/
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerFlux.Summed
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelMoments

/-! ## Direct-pivotal mass and the summed singleton flux at attained radii -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Strict non-degeneracy of the critical two-point function gives positive corner pivotal
mass at the attained radius**, through the model's own cutoff-to-uncut comparison
`cutTwoPoint_le_twoPoint`. -/
theorem directPivot_pos_of_twoPoint_lt_one {y : M.V}
    (hτ : M.twoPoint M.betaCrit (0 : M.V) y < 1) :
    0 < M.directPivot y (M.S.dist 0 y) := by
  rw [M.directPivot_eq_one_sub_twoPoint]
  have hle := M.cutTwoPoint_le_twoPoint (M.S.dist 0 y) (0 : M.V) y
  have heq : (M.cutLaw (M.S.dist 0 y)).real (M.connEvent y)
      = M.cutTwoPoint (M.S.dist 0 y) (0 : M.V) y := rfl
  rw [heq]
  linarith

/-- **Capstone: strict two-point non-degeneracy at `y` forces a corner of the summed
first-moment flux at the attained radius `‖y‖`.** -/
theorem not_continuousAt_firstFlux_of_twoPoint_lt_one {y : M.V} (hy : y ≠ (0 : M.V)) {ρ C : ℝ}
    (hτ : M.twoPoint M.betaCrit (0 : M.V) y < 1)
    (hsρ : M.S.dist 0 y < ρ) (hC0 : 0 ≤ C)
    (hCb : ∀ r ∈ Icc (M.S.dist 0 y / 2) (M.S.dist 0 y), -(deriv M.K r) ≤ C)
    (hKρ : deriv M.K ρ < 0) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (hK : ContinuousAt (fun r : ℝ => deriv M.K r) (M.S.dist 0 y))
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hK' : deriv M.K (M.S.dist 0 y) ≠ 0) :
    ¬ ContinuousAt (M.firstFlux y) (M.S.dist 0 y) :=
  M.not_continuousAt_firstFlux_of_corner hy hsρ hC0 hCb hKρ hvol hK hβ hK'
    (M.directPivot_pos_of_twoPoint_lt_one hτ)

end SourceModelData

/-! ## Axiom audit -/

set_option linter.hashCommand false in
#print axioms SourceModelData.directPivot_pos_of_twoPoint_lt_one
#print axioms SourceModelData.not_continuousAt_firstFlux_of_twoPoint_lt_one

end PercLib.CriticalLRP.Orchestration
