/-
Critical LRP I: edge touch mass and the radius majorant of the normalized pivotal mass.

Swarm `smwv2c2lw`, member `m3`, direction d3.  Self-contained definitions only: no production
writes, no new axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.KernelFactor.Defs

/-!
# Edge touch mass and the pivotal majorant of the normalized pivotal mass

The normalized pivotal mass of the singleton cluster indicator is

`normalizedPivotMass y r = ∑' e, cutPivotFactor r e * pivotalFlux (cutProb r) 1{y ∈ K_0} e`.

The whole edge series is dominated, uniformly in a neighbourhood of an off-corner radius `r0`, by
the *edge touch mass* at one strictly larger radius `R`:

* `edgeTouchMass r e` is the sum, over the two endpoints `x` of the edge `e`, of the connection
  probability `cutTwoPoint r 0 x`, i.e. the probability that `x` lies in the cluster of the origin;
* `pivotMajorant r0 R e = cutPivotFactor r0 e * edgeTouchMass R e`.

The single-edge pivotal flux is at most the probability that `e` touches the cluster of the origin
(any pivotal edge must touch it), and that event is contained in the union over the two endpoints
of "the endpoint lies in the cluster".  Summing the majorant over all edges therefore reduces to
the first cutoff moment `∑'_x cutTwoPoint R 0 x = cutMassReal R` through the fixed-radius incident
count `#(ball r0)`, and not to an infinite tail over edges.

Nothing here asserts continuity of the pivotal flux, of the normalized pivotal mass, or of the
singleton flux.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Edge touch mass.**  At cutoff radius `r`, the sum over the two endpoints of an edge of the
probability that the endpoint lies in the cluster of the origin.  This bounds the probability that
the edge touches the cluster of the origin. -/
noncomputable def edgeTouchMass (r : ℝ) : Sym2 M.V → ℝ :=
  Sym2.lift ⟨fun x y => M.cutTwoPoint r 0 x + M.cutTwoPoint r 0 y,
    fun x y => add_comm (M.cutTwoPoint r 0 x) (M.cutTwoPoint r 0 y)⟩

theorem edgeTouchMass_mk (r : ℝ) (x y : M.V) :
    M.edgeTouchMass r s(x, y) = M.cutTwoPoint r 0 x + M.cutTwoPoint r 0 y := rfl

theorem edgeTouchMass_nonneg (r : ℝ) (e : Sym2 M.V) : 0 ≤ M.edgeTouchMass r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [edgeTouchMass_mk]
    exact add_nonneg (cutTwoPoint_nonneg M r 0 x) (cutTwoPoint_nonneg M r 0 y)

/-- **Pivotal majorant.**  The normalized cutoff factor at the base radius `r0` times the edge
touch mass at the comparison radius `R`.  This is the radius-uniform edge majorant used to
dominate the normalized pivotal mass on a neighbourhood of `r0`. -/
noncomputable def pivotMajorant (r0 R : ℝ) : Sym2 M.V → ℝ :=
  fun e => M.cutPivotFactor r0 e * M.edgeTouchMass R e

end SourceModelData

end PercLib.CriticalLRP.Orchestration
