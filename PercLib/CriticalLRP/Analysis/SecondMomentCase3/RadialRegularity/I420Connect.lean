/-
Ultramath swarm `smwzlje3f`, member `m7`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m7/I420Connect.lean`.

# Proposition I.4.15, Case 3 in the `momOf` vocabulary of Proposition I.4.20

The `p = 3` second induction of Proposition I.4.20 consumes the regular variation of index `3α` of
the second cutoff moment in the spelling
`fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r`.  That function *is*
`r ↦ (M.cutMoment 2 r).toReal` definitionally (`momOf_cutProb_eq_toReal_cutMoment`), so the Case-3
theorem of Proposition I.4.15 applies to it directly.

This file records the transport.  For the input `hF` (Lemma I.4.13's pointwise open-triangle
log-radial bound) the reader is referred to `TailRoute.lean`, where the same function is produced
from the strictly weaker vanishing of the open-triangle tail and is plugged into the `p = 3`
induction of Proposition I.4.20.

No `sorry`, `admit`, `native_decide`, `sorryAx` or custom axiom.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.ACAE

/-! # The `momOf` form of the Case-3 second moment -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

namespace SourceModelData

variable (M : SourceModelData)

/-- **The `hRV2` function of the `p = 3` induction is regularly varying of index `3α`**, from the
I.4.15 Case-3 source hypotheses: Proposition I.4.15, Case 3 in the `momOf` vocabulary of I.4.20
(`momOf_cutProb_eq_toReal_cutMoment` is definitional), with `hac`, `hae`, `h1`, `hmR` discharged by
`regularlyVarying_two_of_source_p21_no_ac`. -/
theorem rv2_momOf_cutProb_of_case3 {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) := by
  have h := regularlyVarying_two_of_source_p21_no_ac M M.hα hr₀ hβ h2 hP hTri hC₀ hp hF
    hc3 hgm
  simpa only [I420Case3.momOf_cutProb_eq_toReal_cutMoment] using h

end SourceModelData

end PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.rv2_momOf_cutProb_of_case3
