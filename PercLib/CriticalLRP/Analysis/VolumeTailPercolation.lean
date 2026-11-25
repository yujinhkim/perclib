/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The percolation lower-tail specialization of Proposition I.3.1(1)

Canonical full-law domination of the lower-tail estimate from a uniform
size-biased band and a doubling inverse scale.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailLower
public import PercLib.CriticalLRP.Analysis.VolumeTailModel

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis.I32

open PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- The lower-tail part of Proposition I.3.1 specialized to canonical
cutoff/full percolation volume laws. -/
theorem exists_volume_tail_lower_of_inverse_doubling
    {π : ℝ → Sym2 V → unitInterval} {πinf : Sym2 V → unitInterval} {o : V}
    {f g : ℝ → ℝ} {c C a q D α : ℝ}
    (hρπ : ∀ r e, π r e ≤ πinf e) (hc : 0 < c) (hcC : c ≤ C)
    (ha : 0 < a) (hq : 0 < q) (hα : 0 < α)
    (hfin : ∀ᵐ ω ∂edgeMeasure πinf, clusterVol ω o ≠ ⊤)
    (hL1 : ∀ r : ℝ, 1 ≤ r → Integrable (fun x : ℝ => x) (volumeLaw (π r) o))
    (hmean : ∀ r : ℝ, 1 ≤ r → a * r ^ α ≤ mean (volumeLaw (π r) o))
    (hband : ∀ r : ℝ, 1 ≤ r →
      q ≤ (sizeBiasedBaseLaw (volumeLaw (π r) o)
        (Icc (c * f r) (C * f r))).toReal)
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hD : 0 < D) (hdouble : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x)
    (hgAtTop : Tendsto g atTop atTop) (hgf : ∀ x : ℝ, 0 < x → f (g x) = x) :
    ∃ N κ : ℝ, 0 < κ ∧
      ∀ n : ℝ, N ≤ n → κ * (g n) ^ α / n ≤ (volumeLaw πinf o (Ici n)).toReal := by
  have hpos : ∀ r : ℝ, 1 ≤ r → 0 < mean (volumeLaw (π r) o) := by
    intro r hr
    have hrpos : 0 < r := one_pos.trans_le hr
    exact lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hrpos α)) (hmean r hr)
  have hbase : ∀ r : ℝ, 1 ≤ r →
      IsProbabilityMeasure (sizeBiasedBaseLaw (volumeLaw (π r) o)) := by
    intro r hr
    exact isProbabilityMeasure_sizeBiasedBaseLaw _ (volumeLaw_Iio_zero _ _)
      (hL1 r hr) (hpos r hr)
  apply exists_lower_tail_of_inverse_doubling
    (μ := fun r => volumeLaw (π r) o)
    (T := fun n => (volumeLaw πinf o (Ici n)).toReal)
    hbase hc hcC ha hq hα hmean hband ?_ hgmono hgpos hD hdouble hgAtTop hgf
  intro r n
  exact volumeLaw_tail_toReal_mono (hρπ r) o
    (ae_finite_of_volumeLaw_mono (hρπ r) o hfin) hfin

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.exists_volume_tail_lower_of_inverse_doubling
