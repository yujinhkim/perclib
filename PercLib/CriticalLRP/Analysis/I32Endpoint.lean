/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The moment endpoint for Proposition I.3.2

For probability laws on `[0, ∞)`, Jensen's inequality gives `mean μ ≤ sbMean μ`.
Consequently hypotheses 1 and 2 of Proposition I.3.2 force `1 ≤ a`; no monotonicity
or continuity of the regularly varying function is needed. The low-index case is
therefore impossible for actual moment laws, while `a = 1` is included in the
Karamata correspondence. This is not an added restriction on the source statement.

The normalizer `g` and the MGF asymptotic remain separate obligations; this file
only supplies the endpoint and its Tauberian-domain consequence. It does not claim
existence or positivity of the `A₃` limit.
-/
module

public import PercLib.CriticalLRP.Analysis.VolumeTail
public import PercLib.CriticalLRP.Analysis.SizeBiasedMGF
public import PercLib.CriticalLRP.Analysis.ChiSquareA3

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.I32Endpoint

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.I32

/-! ## The size-biased mean dominates the mean -/

/-- **`E|K| ≤ Ê|K|` for a probability law on `[0,∞)`.**  This is Jensen's
inequality for `t ↦ t²`: `(E|K|)² ≤ E|K|²`, so `E|K| ≤ E|K|²/E|K|` whenever
`E|K| > 0`.  The source uses this comparison only implicitly (it is what makes
hypothesis 2 compatible with hypothesis 1). -/
theorem mean_le_sbMean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) (h1 : Integrable (fun x : ℝ => x) μ)
    (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < mean μ) :
    mean μ ≤ sbMean μ := by
  have hjensen : (mean μ) ^ 2 ≤ secMoment μ := by
    have hconv : ConvexOn ℝ (Ici (0 : ℝ)) (fun t : ℝ => t ^ 2) := convexOn_pow 2
    have hcont : ContinuousOn (fun t : ℝ => t ^ 2) (Ici (0 : ℝ)) := by fun_prop
    have hae : ∀ᵐ x ∂μ, (id x : ℝ) ∈ Ici (0 : ℝ) := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hμ] with x hx
      simpa using hx
    have h := hconv.map_integral_le hcont isClosed_Ici hae h1 (by simpa [Function.comp] using h2)
    simpa [mean, secMoment, Function.comp] using h
  rw [sbMean, le_div_iff₀ hpos]
  calc mean μ * mean μ = (mean μ) ^ 2 := by ring
    _ ≤ secMoment μ := hjensen

/-! ## Regular variation against a strictly larger power -/

/-- **A measurable regularly varying function is `o(x^σ)` above its index.**
If `f` is regularly varying of index `ρ` and `σ > ρ`, then `f x / x^σ → 0`.
This is the elementary Potter consequence used to rule out the endpoint `a < 1`
of Proposition I.3.2.  No monotonicity or continuity of `f` is used. -/
theorem tendsto_div_rpow_zero_of_regularlyVarying {f : ℝ → ℝ} {ρ σ : ℝ}
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f ρ) (hσ : ρ < σ) :
    Tendsto (fun x : ℝ => f x / x ^ σ) atTop (𝓝 0) := by
  obtain ⟨ε, hε0, hεσ⟩ : ∃ ε : ℝ, 0 < ε ∧ ρ + ε < σ :=
    ⟨(σ - ρ) / 2, by linarith, by linarith⟩
  obtain ⟨X, hX1, hpot⟩ := hasPotterBounds_of_regularlyVarying hmeas hrv ε hε0
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  set C : ℝ := (1 + ε) * |f X| * X ^ (-(ρ + ε)) with hC
  have hkey : ∀ x : ℝ, X ≤ x → ‖f x / x ^ σ‖ ≤ C * x ^ (-(σ - (ρ + ε))) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hXpos hx
    have hupper : |f x| ≤ (1 + ε) * (x / X) ^ (ρ + ε) * |f X| := (hpot x X le_rfl hx).2
    have hxX : (x / X) ^ (ρ + ε) = x ^ (ρ + ε) / X ^ (ρ + ε) :=
      Real.div_rpow hxpos.le hXpos.le (ρ + ε)
    have hXpow : 0 < X ^ (ρ + ε) := Real.rpow_pos_of_pos hXpos _
    have hxp : 0 < x ^ σ := Real.rpow_pos_of_pos hxpos σ
    have hsplit : x ^ (ρ + ε) / x ^ σ = x ^ ((ρ + ε) - σ) := (Real.rpow_sub hxpos _ _).symm
    have hXeq : X ^ (-(ρ + ε)) = (X ^ (ρ + ε))⁻¹ := by
      rw [Real.rpow_neg hXpos.le]
    have hneg : -(σ - (ρ + ε)) = (ρ + ε) - σ := by ring
    rw [hneg, Real.norm_eq_abs, abs_div, abs_of_pos hxp]
    calc |f x| / x ^ σ
        ≤ ((1 + ε) * (x / X) ^ (ρ + ε) * |f X|) / x ^ σ := by
          apply div_le_div_of_nonneg_right hupper hxp.le
      _ = C * x ^ ((ρ + ε) - σ) := by
          have hCeq : C * x ^ (ρ + ε) = (1 + ε) * (x / X) ^ (ρ + ε) * |f X| := by
            rw [hC, hXeq, hxX, div_eq_mul_inv]
            ring
          have h1 : x ^ ((ρ + ε) - σ) * x ^ σ = x ^ (ρ + ε) := by
            rw [← Real.rpow_add hxpos]
            ring_nf
          have hfin : C * x ^ ((ρ + ε) - σ)
              = ((1 + ε) * (x / X) ^ (ρ + ε) * |f X|) / x ^ σ := by
            rw [eq_div_iff hxp.ne']
            rw [show C * x ^ ((ρ + ε) - σ) * x ^ σ
                = C * (x ^ ((ρ + ε) - σ) * x ^ σ) from by ring]
            rw [h1, hCeq]
          exact hfin.symm
  have hlim : Tendsto (fun x : ℝ => C * x ^ (-(σ - (ρ + ε)))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ (-(σ - (ρ + ε)))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    simpa [mul_comm] using hbase.const_mul C
  exact squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop X] with x hx
    exact hkey x hx) hlim

/-! ## The endpoint theorem: hypotheses 1 and 2 force `1 ≤ a` -/

/-- **Proposition I.3.2 forces `a ≥ 1`.**  Let `ψ r = E_r|K|` satisfy
hypothesis 1 (`ψ r ∼ A₁ r^α`) and `φ r = Ê_r|K|` satisfy hypothesis 2
(`φ r ∼ A₂ f r`, `f` regularly varying of index `a · α`), and suppose
`ψ ≤ φ` eventually (true for every actual cluster law, by `mean_le_sbMean`).

Then `1 ≤ a`.  Indeed `A₂ f r ≳ φ r ≥ ψ r ≳ A₁ r^α` forces
`f r / r^α` to stay bounded below, while regular variation of index
`a α < α` forces `f r / r^α → 0`.

So the proposition's range `a > 0` is really `a ≥ 1`; in particular the
Tauberian-domain requirement `1/a ≤ 1` is not an additional hypothesis. -/
theorem one_le_of_moment_asymptotics {f ψ φ : ℝ → ℝ} {A1 A2 α a : ℝ}
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hα : 0 < α) (ha : 0 < a)
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (a * α))
    (hφ : ∀ᶠ r in atTop, 0 ≤ φ r)
    (hge : ∀ᶠ r in atTop, ψ r ≤ φ r)
    (h1 : Tendsto (fun r => ψ r / (A1 * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => φ r / (A2 * f r)) atTop (𝓝 1)) :
    1 ≤ a := by
  by_contra hcon
  push Not at hcon
  -- `f` is eventually positive, hence so is `A₂ f`.
  have hfpos : ∀ᶠ r in atTop, 0 < f r :=
    eventually_pos_of_tendsto_div hA2 hφ h2
  -- `f r / r ^ α → 0` because the index `a α` is smaller than `α`.
  have hidx : a * α < α := by
    have : a * α < 1 * α := by exact mul_lt_mul_of_pos_right hcon hα
    simpa using this
  have hdecay := tendsto_div_rpow_zero_of_regularlyVarying hmeas hrv hidx
  -- Lower bound for `ψ`, hence for `φ`, hence for `f`.
  have hψlow : ∀ᶠ r in atTop, A1 / 2 * r ^ α ≤ ψ r := by
    have hclose : ∀ᶠ r in atTop, |ψ r / (A1 * r ^ α) - 1| < 1 / 2 := by
      have := (Metric.tendsto_nhds.1 h1) (1 / 2) (by norm_num)
      simpa [Real.dist_eq] using this
    filter_upwards [hclose, eventually_gt_atTop (0:ℝ)] with r hr hrpos
    have hden : 0 < A1 * r ^ α := mul_pos hA1 (Real.rpow_pos_of_pos hrpos α)
    have hlt : 1 - 1 / 2 < ψ r / (A1 * r ^ α) := by
      have := (abs_lt.1 hr).1
      linarith
    rw [lt_div_iff₀ hden] at hlt
    nlinarith
  have hφup : ∀ᶠ r in atTop, φ r ≤ 2 * A2 * f r := by
    have hclose : ∀ᶠ r in atTop, φ r / (A2 * f r) < 2 :=
      h2.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))
    filter_upwards [hclose, hfpos] with r hr hfr
    have hden : 0 < A2 * f r := mul_pos hA2 hfr
    rw [div_lt_iff₀ hden] at hr
    linarith
  have hlow : ∀ᶠ r in atTop, A1 / (4 * A2) ≤ f r / r ^ α := by
    filter_upwards [hψlow, hφup, hge, eventually_gt_atTop (0:ℝ)] with r h1r h2r h3r hrpos
    have hstep : A1 / 2 * r ^ α ≤ 2 * A2 * f r := h1r.trans (h3r.trans h2r)
    have h2A : 0 < 2 * A2 := by linarith
    have hdiv : (A1 / 2 * r ^ α) / (2 * A2) ≤ f r := by
      rw [div_le_iff₀ h2A]
      calc A1 / 2 * r ^ α ≤ 2 * A2 * f r := hstep
        _ = f r * (2 * A2) := by ring
    have heq : (A1 / 2 * r ^ α) / (2 * A2) = A1 / (4 * A2) * r ^ α := by
      field_simp
      ring
    have hdiv' : A1 / (4 * A2) * r ^ α ≤ f r := by rwa [heq] at hdiv
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hrpos α)).mpr hdiv'
  have hsmall : ∀ᶠ r in atTop, f r / r ^ α < A1 / (4 * A2) :=
    hdecay.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨r, hr1, hr2⟩ := (hlow.and hsmall).exists
  linarith

/-! ## The Tauberian-domain hypothesis is not an extra assumption -/

/-- `sbMean` of a probability law on `[0,∞)` is nonnegative. -/
theorem sbMean_nonneg {μ : Measure ℝ} (hint2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hpos : 0 < mean μ) : 0 ≤ sbMean μ := by
  have hnn : 0 ≤ secMoment μ := integral_nonneg fun x => sq_nonneg x
  exact div_nonneg hnn hpos.le

/-- **Volume tail of Proposition I.3.2 from the source's hypotheses 1-2 and the
MGF asymptotic**, with the Tauberian-domain hypothesis `1/a ≤ 1` *discharged*.

The source states hypothesis 2 with `a > 0`.  `one_le_of_moment_asymptotics`
shows that hypotheses 1 and 2 together force `a ≥ 1`, which is precisely the
domain `1/a ≤ 1` required by `tail_asymptotic_of_mgf_inverse`.  Hence the
Tauberian step is legitimate for every instance of the proposition, and the
endpoint `a = 1` (index `0` of the normalizer) is included.

The remaining analytic input `hmain` is the MGF asymptotic (I.3.2) itself; the
construction of the inverse scale `g` and the proof of `hmain` are separate
obligations (they are not claimed here). -/
theorem tail_asymptotic_of_source_hypotheses
    (mu : ℝ → Measure ℝ) (hmu : ∀ r, IsProbabilityMeasure (mu r))
    (hmu0 : ∀ r, mu r (Iio 0) = 0)
    (hint1 : ∀ r, Integrable (fun x : ℝ => x) (mu r))
    (hint2 : ∀ r, Integrable (fun x : ℝ => x ^ 2) (mu r))
    (hmeanpos : ∀ r, 0 < mean (mu r))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {a α A1 A2 A3 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (hα : 0 < α) (ha : 0 < a)
    {f : ℝ → ℝ} (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (a * α))
    (h1 : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r => sbMean (mu r) / (A2 * f r)) atTop (𝓝 1))
    {g : ℝ → ℝ} (hgmeas : Measurable g)
    (hgrv : RegularlyVaryingAtTop g (1 / (a * α)))
    (hgpos : ∀ᶠ x in atTop, 0 < g x) (hA3 : A3 ≠ 0)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (A3 * (g (1 / h) ^ α * h)))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => (μ (Ici x)).toReal /
      ((A3 / Real.Gamma (1 / a)) * (g x ^ α / x))) atTop (𝓝 1) := by
  have hφ : ∀ᶠ r in atTop, 0 ≤ sbMean (mu r) :=
    Eventually.of_forall fun r => sbMean_nonneg (hint2 r) (hmeanpos r)
  have hge : ∀ᶠ r in atTop, mean (mu r) ≤ sbMean (mu r) :=
    Eventually.of_forall fun r =>
      mean_le_sbMean (hmu0 r) (hint1 r) (hint2 r) (hmeanpos r)
  have hone : 1 ≤ a :=
    one_le_of_moment_asymptotics hA1 hA2 hα ha hmeas hrv hφ hge h1 h2
  have ha1 : 1 / a ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hone
  exact PercLib.CriticalLRP.VolumeTail.tail_asymptotic_of_mgf_inverse
    μ hμ ha hα ha1 hgmeas hgrv hgpos hA3 hmain

/-! ## The constants at the endpoint `a = 1` -/

/-- At `a = 1` the source's `A₃ = (A₁/A₂^{1/a}) · lim` has exponent `1/a = 1`. -/
theorem A3const_at_one (A1 A2 L : ℝ) :
    PercLib.CriticalLRP.Anchor.A3const A1 A2 1 L = A1 / A2 * L := by
  simp [PercLib.CriticalLRP.Anchor.A3const]

/-- At `a = 1` the tail constant is `A₄ = A₃/Γ(1) = A₃`: the Gamma factor is one,
consistently with the Tauberian exponent `1 - 1/a = 0`. -/
theorem A4const_at_one (A3 : ℝ) : PercLib.CriticalLRP.Anchor.A4const A3 1 = A3 := by
  simp [PercLib.CriticalLRP.Anchor.A4const]
