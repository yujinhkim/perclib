/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m5.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m5/Defs.lean`.

Swarm `smwznoz6j`, member `m5`, direction `d1` — (F) I.4.20 Case-3 dependency closure.

Production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`, branch `work/yujinhkim-critical-lrp-orchestration`.

# The two §I.4.1 structural inputs of the Case-3 estimates, bundled

Proposition I.4.15 (second assertion) and its Case-3 proof consume two structural inputs of §I.4.1:

* `hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤` — Kozma's triangle
  condition `∇_{β_c} < ∞`, which the paper *assumes* separately;
* `hF` / `hTail` — the logarithmic integrability and vanishing of the open-triangle tail
  `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`, i.e. Lemma I.4.3 under Case 3 of (HD), as consumed by
  `I420Case3` in the shape `Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0)`.

`SecondMomentCase3/TriangleFromHD` derives both from Case 3 of (HD) alone.  This file names the
pair `Case3TriangleTailData M`, so that the Case-3 assemblies in `Main.lean` can carry one
explicit structural hypothesis instead of loose conjunctions.  No model input is assumed here.

## Layout

* `Case3TriangleTailData M` — the pair `(∇_{β_c}(0,0) < ⊤, IsLogErrorFunction ∇_r)`.
* `case3TriangleTailData_of_case3HD` — that pair follows from the literal HD(3) predicate.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

open Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The two §I.4.1 structural inputs of the Case-3 estimates**: finiteness of the open triangle at
the origin (`hTri`, Kozma's `∇_{β_c} < ∞`) and the log-integrability + vanishing of the
open-triangle tail (`hF`, Lemma I.4.3), the latter in the `M.nablaTail` shape used by
`I420Case3`.

Both components are *derived* from Case 3 of (HD) by `case3TriangleTailData_of_case3HD`; this
predicate only records what the downstream Case-3 consumers need. -/
def Case3TriangleTailData : Prop :=
  TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ ∧
    Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal)

/-- First projection: the triangle condition. -/
theorem Case3TriangleTailData.openTriangle_lt_top (h : M.Case3TriangleTailData) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  h.1

/-- The log-integrability component of (I.4.13) / Lemma I.4.3. -/
theorem Case3TriangleTailData.isLogErrorFunction (h : M.Case3TriangleTailData) :
    Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal) :=
  h.2

/-- Second projection, in the `Tendsto`-to-zero shape used by the `I420Case3` consumers. -/
theorem Case3TriangleTailData.tendsto_nablaTail (h : M.Case3TriangleTailData) :
    Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) :=
  h.2.2

#print axioms Case3TriangleTailData.openTriangle_lt_top
#print axioms Case3TriangleTailData.isLogErrorFunction
#print axioms Case3TriangleTailData.tendsto_nablaTail

end SourceModelData
end PercLib.CriticalLRP.Orchestration
