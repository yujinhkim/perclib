/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwtrtcqs`, member `m8`, direction D7.

Discharge of the hypothesis of the landed module `PercLib.CriticalLRP.Analysis.Polygon.TailLog`
(accepted from `smwp648b3`, direction D2) by the pointwise logarithmic bound.

`TailLog.isLogErrorFunction_nablaTail_add_rpow_neg` is *conditional* on

`hTail : IsLogErrorFunction (fun r => (M.nablaTail r).toReal)`,

and its file comment says explicitly "No decay beyond the input hypothesis is inferred".  That
input is exactly what `OpenTriangleLogTail.isLogErrorFunction_nablaTail` produces from the
pointwise estimate (I.4.13); this file records the composition so that the tail-logarithmic step of
§I.4.18 no longer carries `hTail` as a hypothesis once the pointwise bound is available.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.Polygon.TailLog

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration

/-- **The polygon tail's additive error term is a logarithmic error**, given the pointwise
logarithmic bound on the uncut open triangle.  This is
`Analysis.isLogErrorFunction_nablaTail_add_rpow_neg` with its `hTail` hypothesis discharged. -/
theorem isLogErrorFunction_nablaTail_add_rpow_neg_of_logRadialBound (M : SourceModelData)
    {C p c : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hc : 0 < c)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail (r ^ c)).toReal + r ^ (-c)) :=
  Analysis.isLogErrorFunction_nablaTail_add_rpow_neg M
    (isLogErrorFunction_nablaTail M hC hp hF) hc

end PercLib.CriticalLRP.Orchestration.SourceModelData
