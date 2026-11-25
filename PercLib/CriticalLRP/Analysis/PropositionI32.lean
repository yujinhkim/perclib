/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Proposition I.3.2 from moments, weak convergence, and restoration

The final analytic assembly keeps the source's hypotheses (1)-(4): moment
asymptotics, weak convergence of normalized size-biased laws, and absence of a
zero atom. The full-law restoration inequality is an explicit named probabilistic
input, and `fullLawGhostRatio_of_restoration` discharges the multiplicative ghost
comparison inside the proof. The normalized limit defining `A3` and positivity of
`A3` are conclusions, not assumptions.
-/
module

public import PercLib.CriticalLRP.Analysis.A3Limit

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis.I32

noncomputable section

/-- **Proposition I.3.2, MGF and tail, from its probabilistic restoration estimate.**
The source hypotheses are represented by the actual cluster-volume laws, their first
and second moments, weak convergence of the normalized size-biased laws, and the
full-law restoration estimate. `D` is the project’s infimum-based generalized inverse
constructed from the source's own moment ratio, not an order-isomorphism hypothesis. -/
theorem prop_I_3_2_of_restoration
    (mu : ℝ → Measure ℝ) (muinf : Measure ℝ) (Qinf : Measure ℝ)
    {f : ℝ → ℝ} {a α A1 A2 C : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hA1 : 0 < A1) (hA2 : 0 < A2) (hC : 0 < C)
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (a * α))
    (hmuProb : ∀ r, IsProbabilityMeasure (mu r)) [IsProbabilityMeasure muinf]
    (hmu : ∀ r, mu r (Iio 0) = 0) (hmuinf : muinf (Iio 0) = 0)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    [IsProbabilityMeasure Qinf]
    (hQinf : Qinf (Iio 0) = 0) (hQinf0 : Qinf {(0 : ℝ)} = 0)
    (hconv : Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
      (𝓝 (Measure.toProbabilityMeasure Qinf)))
    (hE1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hψ2 : Tendsto (fun r => sbMean (mu r) / (A2 * f r)) atTop (𝓝 1))
    (hI35 : ∀ᶠ r in atTop, ∀ h > 0,
      lapDefect (mu r) h ≤ lapDefect muinf h ∧
      lapDefect muinf h ≤ lapDefect (mu r) h +
        C * r ^ (-α) * (∫ x, x * Real.exp (-(h * x)) ∂(mu r)) * lapDefect muinf h) :
    ∃ A3 : ℝ, 0 < A3 ∧ Tendsto (A3cand A1 A2 a Qinf) atTop (𝓝 A3) ∧
      let D : RVPosData f (a * α) := RVPosData.of_moment (by positivity) hmeas hrv hA2
        (Filter.Eventually.of_forall fun r => I32Endpoint.sbMean_nonneg (hint2 r) (hEpos r)) hψ2
      Tendsto (fun h : ℝ => lapDefect muinf h /
          (A3 * (D.genInv (1 / h) ^ α * h))) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
        Tendsto (fun x : ℝ => (muinf (Ici x)).toReal /
          ((A3 / Real.Gamma (1 / a)) * (D.genInv x ^ α / x))) atTop (𝓝 1) := by
  let := fun r => hmuProb r
  let D : RVPosData f (a * α) := RVPosData.of_moment (by positivity) hmeas hrv hA2
    (Filter.Eventually.of_forall fun r => I32Endpoint.sbMean_nonneg (hint2 r) (hEpos r)) hψ2
  have hψnonneg : ∀ᶠ r in atTop, 0 ≤ sbMean (mu r) :=
    Filter.Eventually.of_forall fun r => I32Endpoint.sbMean_nonneg (hint2 r) (hEpos r)
  have hψdiv : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2) := by
    have h := hψ2.const_mul A2
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hrv.1] with r hf
    field_simp
  have hGhost : FullLawGhostRatio muinf mu D.genInv A2 :=
    fullLawGhostRatio_of_restoration mu muinf Qinf D hmu hmuinf hEpos hSpos hprob hQinf0
      hconv hA1 hA2 hα hC hE1 hψdiv hI35
  have hmain := prop_I_3_2_of_fullLawGhostRatio mu muinf Qinf D hmuProb hmu hmuinf
    hint1 hint2 hEpos hSpos hprob hQinf hQinf0 hconv hA1 hA2 ha hα rfl hE1 hψdiv hGhost
  dsimp only [D] at hmain ⊢
  exact hmain

end

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.prop_I_3_2_of_restoration
