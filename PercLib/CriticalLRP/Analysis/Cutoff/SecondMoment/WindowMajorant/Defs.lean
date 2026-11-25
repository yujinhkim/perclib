/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvi25ua`, member `m1`, direction (A).

Definitions of the uniform-in-radius majorant of the `p = 2` window fluxes.

The majorant is the candidate

  `G(t) = 2 * (M.rhsScalarTwo t + 3 C (M.cutMoment 4 b).toReal)`,

i.e. twice the accepted `p = 2` right-hand side at the radius `t`, plus an explicit constant
multiple of the fourth cutoff moment evaluated at the *right endpoint* `b` of the radius window.
The two halves of the majorant estimate are proved in `WindowMajorant/Main.lean`:

* `M.windowFlux (S n) t ≤ M.windowMajorant C b t` for every window index `n` and every
  `t ∈ Ioc a b`, from the almost-sure ghost envelope of `FluxConv/Envelope`;
* `IntervalIntegrable (M.windowMajorant C b) volume a b`, from the explicit coefficient bound
  `|M.coeffRHS t| ≤ C` and finiteness of the fourth cutoff moment at `b`.

The predicate `IsWindowFluxMajorant` packages both, which is the exact input consumed by
`Integrated/RadiusFTC.hasDerivAt_cutMomentReal_two_of_window_majorant` (with `G` specialised).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Summable
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.RadiusFTC
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Assembly
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Defs

/-!
# The uniform-in-radius window majorant

Definitions only (plus their elementary API).  No estimate is asserted here.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The constant part of the uniform-in-radius majorant: `3 C (cutMoment 4 b).toReal`, where `C`
bounds `|M.coeffRHS|` on the radius window and `b` is its right endpoint.  It is the explicit
bound for the constant fourth-moment term `3 M.coeffRHS t (cutMoment 4 t).toReal` of the per-edge
sum, using monotonicity of the cutoff moments in the radius. -/
noncomputable def windowMajorantConst (C b : ℝ) : ℝ :=
  3 * C * (M.cutMoment 4 b).toReal

/-- **The uniform-in-radius majorant of the `p = 2` window fluxes**:
`t ↦ 2 * (M.rhsScalarTwo t + 3 C (cutMoment 4 b).toReal)`.

The factor `2` is the one carried by the per-edge coefficient inequality
`two_deriv_mul_integral_envelope_le`; the second summand is the explicit bound on the cubic
correction, with the fourth cutoff moment frozen at the right endpoint `b` of the radius window.
It is a function of the radius alone: no window index occurs, and no monotonicity of the fluxes in
the window index is used anywhere. -/
noncomputable def windowMajorant (C b : ℝ) : ℝ → ℝ :=
  fun t => 2 * (M.rhsScalarTwo t + M.windowMajorantConst C b)

@[simp]
theorem windowMajorant_apply (C b : ℝ) (t : ℝ) :
    M.windowMajorant C b t = 2 * (M.rhsScalarTwo t + M.windowMajorantConst C b) := rfl

/-- The majorant as an affine function of the radius, the form used for interval integrability. -/
theorem windowMajorant_eq_affine (C b : ℝ) :
    M.windowMajorant C b
      = fun t => 2 * M.rhsScalarTwo t + 2 * M.windowMajorantConst C b := by
  funext t
  rw [windowMajorant_apply]
  ring

/-- The constant part of the majorant is nonnegative as soon as `C` is. -/
theorem windowMajorantConst_nonneg {C b : ℝ} (hC : 0 ≤ C) :
    0 ≤ M.windowMajorantConst C b :=
  mul_nonneg (mul_nonneg (by norm_num) hC) ENNReal.toReal_nonneg

/-- The majorant is nonnegative at radii where the right-hand side is. -/
theorem windowMajorant_nonneg {C b t : ℝ} (hC : 0 ≤ C) (h : 0 ≤ M.rhsScalarTwo t) :
    0 ≤ M.windowMajorant C b t :=
  mul_nonneg (by norm_num) (add_nonneg h (M.windowMajorantConst_nonneg hC))

/-- **The full majorant statement.**  The window fluxes are dominated on `Ioc a b` by the single
radius function `M.windowMajorant C b`, and that function is interval integrable on `a..b`.
This is exactly the pair of hypotheses (`hfluxMaj`, `hG`) of
`SourceModelData.hasDerivAt_cutMomentReal_two_of_window_majorant`, with the explicit candidate
`G = M.windowMajorant C b`; it says nothing about a radius derivative. -/
def IsWindowFluxMajorant (a b C : ℝ) (S : ℕ → Finset (Sym2 M.V)) : Prop :=
  IsWindowMajorantOn (fun n t => M.windowFlux (S n) t) (M.windowMajorant C b) (Set.Ioc a b) ∧
    IntervalIntegrable (M.windowMajorant C b) volume a b

end SourceModelData

namespace Witness

/-- The explicit coefficient constant of the witness on `[1/2, ∞)`:
`C = |β_c| (1/2)^{-d-α-1} = powLawCoeffBound β_c d α (1/2)`. -/
noncomputable def witnessCoeffConst (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) : ℝ :=
  powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α (1 / 2)

end Witness

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms windowMajorantConst
#print axioms windowMajorant
#print axioms windowMajorant_eq_affine
#print axioms windowMajorantConst_nonneg
#print axioms windowMajorant_nonneg

end PercLib.CriticalLRP.Orchestration.SourceModelData
