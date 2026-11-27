/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m2`, direction `d1`.

# The vertexwise ℓ = 3 hypothesis `hT3` of `SecondMomentCase3` is false

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.18 (p. 46) and
proof of Proposition I.4.15, Case 3 (p. 47).

`SecondMomentCase3.connCubeMass_le_of_windowGap` and
`SourceModelData.connCubeMass_toReal_le_of_perVertex_gap` both carry the hypothesis

```
hT3 : ∀ r ≥ 1, ∀ y : M.V, T^3_{β_c,r}(0,y) ≤ Cp · (∇_{r^c} + r^{-c}),
```

the vertexwise `ℓ = 3` instance of Lemma I.4.18.  The printed display of Lemma I.4.18 for
`ℓ = 3` reads `sup_x T^3_{β_c,r}(0,x) = T^3_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c})(E|K|)^0`, and
its left side is `≥ 1` at *every* cutoff: the cutoff two-point matrix has `T(y,y) = 1` and
`I420Case3.one_le_polyK_three_of_chi_ne_top` gives `1 ≤ T^3_{β_c,r}(0,0)`.  Since the right side
tends to `0`, `hT3` is not a theorem of the model.

This file records that refutation.  It is the obstruction that
`SummedThree.sum_polyK_three_ballF_le_card_mul_case3ThreeDriver` repairs: the ℓ = 3 term is
only needed *summed over the window*, and the summed version holds with the honest
window-averaged driver `M.case3ThreeDriver`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Main

/-! # Refutation of the vertexwise ℓ = 3 Case-3 hypothesis -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology BigOperators

set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

/-- **`hT3` is refutable.**  For any constants `Cp ≥ 0`, `c > 0`, any model whose uncut
open-triangle tail vanishes at infinity and whose cutoff first moment is finite at every
`r ≥ 1`, the vertexwise `ℓ = 3` bound

`∀ r ≥ 1, ∀ y, T^3_{β_c,r}(0,y) ≤ Cp (∇_{r^c} + r^{-c})`

fails.  The witness is `y = 0`: the diagonal threefold power of the cutoff two-point matrix is
at least `1` (`I420Case3.one_le_polyK_three_of_chi_ne_top`), while the driver is `o(1)`.

The conclusion is the exact negation of the hypothesis `hT3` printed in
`SecondMomentCase3.connCubeMass_le_of_windowGap` (with `1 ≤ r` in place of `1 ≤ r` there, and
`M.case3Driver c r = (∇_{r^c}).toReal + r^{-c}`), so no Case-3 assembly can discharge `hT3`
from the triangle condition alone. -/
theorem not_forall_polyK_three_le_case3Driver (M : SourceModelData) (Cp c : ℝ)
    (hc : 0 < c)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ¬ ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r := by
  intro h
  -- the driver vanishes
  have hfirst : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) :=
    hTail.comp (tendsto_rpow_atTop hc)
  have hsecond : Tendsto (fun r : ℝ => r ^ (-c)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  have hdriver : Tendsto (fun r : ℝ => Cp * M.case3Driver c r) atTop (𝓝 0) := by
    have hsum : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal + r ^ (-c))
        atTop (𝓝 0) := by
      simpa using hfirst.add hsecond
    have := hsum.const_mul Cp
    simpa only [case3Driver, mul_zero] using this
  -- but the bound forces it to stay above `1`
  have hge : ∀ᶠ r : ℝ in atTop, (1 : ℝ) ≤ Cp * M.case3Driver c r := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact le_trans (I420Case3.one_le_polyK_three_of_chi_ne_top M r (hχ r hr)) (h r hr 0)
  have h10 : (1 : ℝ) ≤ 0 := ge_of_tendsto hdriver hge
  norm_num at h10

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

end
