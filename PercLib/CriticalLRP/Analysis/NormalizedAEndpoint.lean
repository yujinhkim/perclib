module

public import PercLib.CriticalLRP.Analysis.I32Endpoint

set_option autoImplicit false

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.I32Endpoint

open PercLib.CriticalLRP.Analysis PercLib.CriticalLRP.Analysis.I32

/-- The source hypotheses 1–2, with their stated normalizations, force `a ≥ 1`.
No ghost-restoration limit, Tauberian conclusion, or positivity of `A₃` is assumed.
The second-moment integrability required by `I32Endpoint.is_sbMean_prop` includes
hypothesis (2)'s meaning of `sbMean = secMoment / mean`; Jensen then gives
`mean ≤ sbMean`. -/
theorem one_le_of_normalized_moment_asymptotics
    (mu : ℝ → Measure ℝ) (hmu : ∀ r, IsProbabilityMeasure (mu r))
    (hmu0 : ∀ r, mu r (Iio 0) = 0)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
    (hmeanpos : ∀ r, 0 < mean (mu r))
    {f : ℝ → ℝ} {A1 A2 α a : ℝ} (hmeas : Measurable f)
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hα : 0 < α) (ha : 0 < a)
    (hrv : RegularlyVaryingAtTop f (a * α))
    (h1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => sbMean (mu r) / f r) atTop (𝓝 A2)) :
    1 ≤ a := by
  let := fun r => hmu r
  have h2norm : Tendsto (fun r => sbMean (mu r) / (A2 * f r)) atTop (𝓝 1) := by
    have hdiv := h2.div_const A2
    rw [div_self hA2.ne'] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [hrv.1] with r hr
    show sbMean (mu r) / f r / A2 = sbMean (mu r) / (A2 * f r)
    field_simp [hA2.ne', hr]
  have hφ : ∀ᶠ r in atTop, 0 ≤ sbMean (mu r) :=
    Filter.Eventually.of_forall fun r => sbMean_nonneg (hint2 r) (hmeanpos r)
  have hge : ∀ᶠ r in atTop, mean (mu r) ≤ sbMean (mu r) :=
    Filter.Eventually.of_forall fun r =>
      mean_le_sbMean (hmu0 r) (hint1 r) (hint2 r) (hmeanpos r)
  exact one_le_of_moment_asymptotics hA1 hA2 hα ha hmeas hrv hφ hge h1 h2norm

#print axioms PercLib.CriticalLRP.I32Endpoint.one_le_of_normalized_moment_asymptotics

end PercLib.CriticalLRP.I32Endpoint
