/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.Analysis.KaramataPrimitive

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-- A regularly varying function with index bigger than `-1` has a divergent
primitive, in both the positive- and negative-index cases. -/
theorem tendsto_integral_atTop_of_regularlyVarying_gt_neg_one {φ : ℝ → ℝ} {ρ : ℝ}
    (hρ : -1 < ρ) (hφm : Measurable φ) (hφrv : RegularlyVaryingAtTop φ ρ)
    (hpos : ∀ᶠ x in atTop, 0 < φ x)
    (hloc : ∀ x y : ℝ, 1 ≤ x → x ≤ y → IntervalIntegrable φ volume x y) :
    Tendsto (fun r => ∫ s in 1..r, φ s) atTop atTop := by
  let T : ℝ → ℝ := (Ioi 1).indicator φ
  have hTm : Measurable T := hφm.indicator measurableSet_Ioi
  have hTpos : ∀ᶠ x in atTop, 0 < T x := by
    filter_upwards [hpos, eventually_gt_atTop 1] with x hx hx1
    simpa [T, hx1] using hx
  have hTrv : RegularlyVaryingAtTop T ρ := regularlyVarying_indicator_Ioi hφrv
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable
      (fun x y hx hxy => hloc x y hx hxy)
  have hK : Tendsto (fun r => (∫ s in 1..r, T s) / (r * T r)) atTop (𝓝 (1 / (ρ + 1))) :=
    lemma_I_2_10_of_regularlyVarying hρ hTm hTloc hTpos hTrv
  have hden : Tendsto (fun r => r * T r) atTop atTop :=
    tendsto_r_mul_of_potter hρ hTpos
      (hasPotterBounds_of_regularlyVarying hTm hTrv)
  have hsum : 0 < ρ + 1 := by linarith [hρ]
  have hleft : Tendsto (fun r => ∫ s in 1..r, T s) atTop atTop :=
    Filter.Tendsto.num hden (one_div_pos.mpr hsum) hK
  have hsum : 0 < ρ + 1 := by linarith [hρ]
  have hleft : Tendsto (fun r => ∫ s in 1..r, T s) atTop atTop :=
    Filter.Tendsto.num hden (one_div_pos.mpr hsum) hK
  apply hleft.congr'
  filter_upwards [eventually_gt_atTop 1, hTpos] with r hr hph
  have hrpos : 0 < r := one_pos.trans hr
  have hseg : (∫ s in 1..r, T s) = ∫ s in 1..r, φ s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le hr.le] at hx
    exact Set.indicator_of_mem hx.1 φ
  rw [hseg]

#print axioms PercLib.CriticalLRP.Analysis.tendsto_integral_atTop_of_regularlyVarying_gt_neg_one

end PercLib.CriticalLRP.Analysis
