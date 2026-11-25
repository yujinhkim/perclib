/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# From the Proposition I.3.2 MGF asymptotic to the volume-tail asymptotic

The normalizing scale is the inverse-scale product `g(x)^α / x`. If `g` is
regularly varying of index `1/(a*α)`, then `A3 * g(x)^α / x` is regularly varying
of index `1/a - 1`. The completed Karamata--Tauberian equivalence therefore maps an
MGF asymptotic directly to the tail formula of Proposition I.3.2 and its constant
`A4 = A3 / Gamma(1/a)`. The proposition's MGF asymptotic and inverse scale are inputs,
not claims made by this module. The Tauberian-domain restriction `1/a ≤ 1` remains
explicit as well.
-/
module

public import PercLib.CriticalLRP.Analysis.RVInversePotter
public import PercLib.CriticalLRP.Analysis.TauberianConverseComplete

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal
open PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.VolumeTail

/-- The candidate tail normalizer in the Proposition I.3.2 MGF package. -/
noncomputable def normalizer (A3 α : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := A3 * (g x ^ α / x)

/-- Its regular-variation index, from the reciprocal-index scaling hypothesis. -/
theorem regularlyVaryingAtTop_normalizer {a α A3 : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hα : 0 < α) (hA3 : A3 ≠ 0)
    (hrv : RegularlyVaryingAtTop g (1 / (a * α))) (hgpos : ∀ᶠ x in atTop, 0 < g x) :
    PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop (normalizer A3 α g) (1 / a - 1) := by
  have hpow := (hrv.rpow hgpos (a := α)).mul (PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_rpow (-1))
  have hindex : 1 / (a * α) * α + (-1 : ℝ) = 1 / a - 1 := by
    field_simp
    ring
  rw [hindex] at hpow
  have hmul := PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.const_mul hA3 hpow
  change RegularlyVaryingAtTop (fun x => A3 * (g x ^ α / x)) (1 / a - 1)
  simpa only [div_eq_mul_inv, Real.rpow_neg_one] using hmul

/-- Evaluating the normalizer reciprocally gives the MGF weight without further algebra. -/
theorem normalizer_inv (A3 α : ℝ) (g : ℝ → ℝ) (h : ℝ) :
    normalizer A3 α g (1 / h) = A3 * (g (1 / h) ^ α * h) := by
  unfold normalizer
  rw [one_div, div_eq_mul_inv, inv_inv]

/-- **Tail conclusion of Proposition I.3.2 from its MGF and inverse-scaling inputs.**

The function `g` is measurable, eventually positive, and regularly varying with reciprocal index
`1/(a*α)`. The MGF Laplace asymptotic and `0 < c < 1` with `c = 1/a` are the remaining analytic
inputs. Consequently the tail has exactly the source's constant `A3/Gamma(1/a)`. This is the tail
implication, not a claim to have proved the MGF or constructed a generalized inverse. -/
theorem tail_asymptotic_of_mgf_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {a α A3 : ℝ} (ha : 0 < a) (hα : 0 < α) (ha1 : 1 / a ≤ 1)
    {g : ℝ → ℝ} (hmeas : Measurable g) (hrv : RegularlyVaryingAtTop g (1 / (a * α)))
    (hgpos : ∀ᶠ x in atTop, 0 < g x) (hA3 : A3 ≠ 0)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (A3 * (g (1 / h) ^ α * h)))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => (μ (Ici x)).toReal /
      ((A3 / Real.Gamma (1 / a)) * (g x ^ α / x))) atTop (𝓝 1) := by
  have ha0 : 0 ≤ 1 - 1 / a := by linarith
  have ha1' : 1 - 1 / a < 1 := by linarith [one_div_pos.mpr ha]
  have hfn := regularlyVaryingAtTop_normalizer ha hα hA3 hrv hgpos
  have hnorm : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (normalizer A3 α g (1 / h)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hmain.congr' ?_
    filter_upwards with h
    rw [normalizer_inv]
  have hfmeas : Measurable (normalizer A3 α g) := by
    have hgpow : Measurable fun x => g x ^ α := by fun_prop
    exact measurable_const.mul (hgpow.div measurable_id)
  have hfn' : RegularlyVaryingAtTop (normalizer A3 α g) (-(1 - 1 / a)) := by
    convert hfn using 1
    ring
  have htail := (PercLib.CriticalLRP.Analysis.laplace_asymptotic_iff_tail_ge
    (f := normalizer A3 α g) (α := 1 - 1 / a) μ hμ ha0 ha1' hfmeas hfn').mp hnorm
  have hgamma : Real.Gamma (1 - (1 - 1 / a)) = Real.Gamma (1 / a) := by
    congr 1
    ring
  rw [hgamma] at htail
  simpa only [normalizer, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using htail

end PercLib.CriticalLRP.VolumeTail
