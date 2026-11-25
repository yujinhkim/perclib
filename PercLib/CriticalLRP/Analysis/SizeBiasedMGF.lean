/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Size-biased Laplace expectations and the fixed-rate cutoff limit

This module isolates the weighting and normalization steps of the MGF argument
in Proposition I.3.2. `sizeBiasedLaw` is the law of the normalized volume under
the proper size-biased probability measure. The identities prove that the
ordinary Laplace defect and the exponential-weighted first moment have the
expected forms under this law. The kernel estimates are explicit about
nonnegativity and the unused junk value at zero.

`stage1_mgf_ratio` then gives the resulting fixed-rate cutoff limit along any
family whose scaled size-biased mean tends to the positive rate, with the
corresponding weak-kernel convergence supplied as the distinct probabilistic
input. It is an analytic intermediate step, not the completed Proposition I.3.2.
-/
module

public import PercLib.CriticalLRP.Analysis.GeneralInverse

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

/-! ### Cluster-volume moments and the size-biased normalisation -/

/-- First moment `E|K|` of a cluster-volume law. -/
noncomputable def mean (mu : Measure ℝ) : ℝ := ∫ x, x ∂mu

/-- Second moment `E|K|^2` of a cluster-volume law. -/
noncomputable def secMoment (mu : Measure ℝ) : ℝ := ∫ x, x ^ 2 ∂mu

/-- The size-biased mean `Ehat|K| = E|K|^2/E|K|`. -/
noncomputable def sbMean (mu : Measure ℝ) : ℝ := secMoment mu / mean mu

/-- The **size-biased law rescaled to have mean one**, i.e. the paper's `Q_r`:
the law of `|K|/Ehat|K|` under the size-biased measure `Phat`. -/
noncomputable def sizeBiasedLaw (mu : Measure ℝ) : Measure ℝ :=
  (mu.withDensity fun x => ENNReal.ofReal (x / mean mu)).map fun x => x / sbMean mu

/-- The paper's kernel `x |-> (1 - e^{-lambda x})/x`.  At `x = 0` the real-valued
formula takes the value `0`, which is exactly the convention under which the
size-biased change of variables is an identity. -/
noncomputable def kern (s y : ℝ) : ℝ := (1 - Real.exp (-(s * y))) / y

/-! ### Elementary bounds for the kernel -/

theorem kern_nonneg {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) : 0 ≤ kern s y := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  · have hle : Real.exp (-(s * y)) ≤ 1 := by
      have : -(s * y) ≤ 0 := by nlinarith
      simpa using Real.exp_le_one_iff.mpr this
    exact div_nonneg (by linarith) h.le

theorem kern_le_rate {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) : kern s y ≤ s := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp [hs.le]
  · rw [div_le_iff₀ h]
    have h1 : 1 - Real.exp (-(s * y)) ≤ s * y := by
      have := Real.add_one_le_exp (-(s * y))
      linarith
    linarith

theorem kern_mono_rate {y s t : ℝ} (hy : 0 ≤ y) (hst : s ≤ t) : kern s y ≤ kern t y := by
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  · apply div_le_div_of_nonneg_right _ h.le
    have : -(t * y) ≤ -(s * y) := by nlinarith
    linarith [Real.exp_le_exp.mpr this]

/-- The two halves of the `1`-Lipschitz bound, for `0 <= a <= b`. -/
theorem kern_pair_le {y a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y) :
    kern a y ≤ kern b y ∧ kern b y - kern a y ≤ b - a := by
  refine ⟨kern_mono_rate hy hab, ?_⟩
  unfold kern
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, div_zero]; linarith
  · rw [div_sub_div_same, div_le_iff₀ h]
    have hexp : Real.exp (-(a * y)) ≤ 1 := by
      have : -(a * y) ≤ 0 := by nlinarith
      simpa using Real.exp_le_one_iff.mpr this
    have hkey : 1 - Real.exp (-((b - a) * y)) ≤ (b - a) * y := by
      have := Real.add_one_le_exp (-((b - a) * y))
      linarith
    have hnn : 0 ≤ 1 - Real.exp (-((b - a) * y)) := by
      have : -((b - a) * y) ≤ 0 := by nlinarith
      linarith [Real.exp_le_one_iff.mpr this]
    have hring : 1 - Real.exp (-(b * y)) - (1 - Real.exp (-(a * y)))
        = Real.exp (-(a * y)) - Real.exp (-(b * y)) := by ring
    have hfac : Real.exp (-(a * y)) - Real.exp (-(b * y))
        = Real.exp (-(a * y)) * (1 - Real.exp (-((b - a) * y))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    rw [hring, hfac]
    calc Real.exp (-(a * y)) * (1 - Real.exp (-((b - a) * y)))
        ≤ 1 * (1 - Real.exp (-((b - a) * y))) :=
          mul_le_mul_of_nonneg_right hexp hnn
      _ ≤ (b - a) * y := by rw [one_mul]; exact hkey

/-- `kern . y` is `1`-Lipschitz in its rate, on nonnegative arguments. -/
theorem abs_kern_sub_kern_le {s t y : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    |kern s y - kern t y| ≤ |s - t| := by
  rcases le_total s t with hst | hts
  · obtain ⟨h1, h2⟩ := kern_pair_le hs hst hy
    have e1 : |kern s y - kern t y| = -(kern s y - kern t y) := abs_of_nonpos (by linarith)
    have e2 : |s - t| = t - s := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1, e2]; linarith
  · obtain ⟨h1, h2⟩ := kern_pair_le ht hts hy
    have e1 : |kern s y - kern t y| = kern s y - kern t y := abs_of_nonneg (by linarith)
    have e2 : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [e1, e2]; linarith

/-! ### The size-biased law is a probability law carried by `[0,inf)` -/

theorem sizeBiasedLaw_Iio_zero {mu : Measure ℝ} (hmu : mu (Iio 0) = 0)
    (hE : 0 < sbMean mu) :
    sizeBiasedLaw mu (Iio 0) = 0 := by
  unfold sizeBiasedLaw
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun x : ℝ => x / sbMean mu) ⁻¹' Iio 0 = Iio 0 := by
    ext x
    simp only [mem_preimage, mem_Iio, div_lt_iff₀ hE, zero_mul]
  rw [hpre, MeasureTheory.withDensity_apply _ measurableSet_Iio]
  show (∫⁻ x, ENNReal.ofReal (x / mean mu) ∂(mu.restrict (Iio 0))) = 0
  rw [Measure.restrict_eq_zero.mpr hmu, lintegral_zero_measure]

theorem isProbabilityMeasure_sizeBiasedLaw (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : mu (Iio 0) = 0) (hint : Integrable (fun x : ℝ => x) mu) (hpos : 0 < mean mu) :
    IsProbabilityMeasure (sizeBiasedLaw mu) := by
  constructor
  unfold sizeBiasedLaw
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  have hnn : 0 ≤ᵐ[mu] fun x : ℝ => x / mean mu := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    exact div_nonneg hx hpos.le
  have hint' : Integrable (fun x : ℝ => x / mean mu) mu := hint.div_const _
  have hof := ofReal_integral_eq_lintegral_ofReal hint' hnn
  rw [Measure.restrict_univ, ← hof, integral_div]
  show ENNReal.ofReal (mean mu / mean mu) = 1
  rw [div_self hpos.ne', ENNReal.ofReal_one]

/-- **Size-biased change of variables.**  For every bounded test function
`E_{Q}[g] = E[|K| g(|K|/Ehat)]/E|K|`, the identity behind the paper's rewriting
of both `P_{r,h}(0 <-> G)` and the error term. -/
theorem integral_sizeBiasedLaw {mu : Measure ℝ} (hmu : mu (Iio 0) = 0) (hpos : 0 < mean mu)
    (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ y, g y ∂(sizeBiasedLaw mu) = (1 / mean mu) * ∫ x, x * g (x / sbMean mu) ∂mu := by
  unfold sizeBiasedLaw
  rw [integral_map (by fun_prop) hg.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => g (x / sbMean mu))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
  simp only [mem_compl_iff, mem_Iio, not_lt] at hx
  have hxE : 0 ≤ x / mean mu := div_nonneg hx hpos.le
  rw [smul_eq_mul, ENNReal.toReal_ofReal hxE]
  ring


theorem measurable_kern (s : ℝ) : Measurable (kern s) := by
  unfold kern; fun_prop

/-! ### The two size-biased identities of the proof -/

/-- **Laplace transform as a size-biased kernel integral.**
`E_mu[1 - e^{-h|K|}] = (E|K| / Ehat|K|) * E_{Q}[(1 - e^{-h Ehat|K| y})/y]`. -/
theorem laplace_eq_sizeBiased {mu : Measure ℝ} (hmu : mu (Iio 0) = 0)
    (hE : 0 < mean mu) (hS : 0 < sbMean mu) (h : ℝ) :
    ∫ x, (1 - Real.exp (-(h * x))) ∂mu
      = (mean mu / sbMean mu) * ∫ y, kern (h * sbMean mu) y ∂(sizeBiasedLaw mu) := by
  have htr := integral_sizeBiasedLaw hmu hE (kern (h * sbMean mu)) (measurable_kern _)
  have hpw : ∫ x, x * kern (h * sbMean mu) (x / sbMean mu) ∂mu
      = ∫ x, sbMean mu * (1 - Real.exp (-(h * x))) ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    unfold kern
    by_cases hx : x = 0
    · simp [hx]
    · have h1 : h * sbMean mu * (x / sbMean mu) = h * x := by field_simp
      rw [h1]
      field_simp
  rw [hpw, integral_const_mul] at htr
  rw [htr]
  field_simp

/-- **Exponential moment as a size-biased integral.** -/
theorem exp_eq_sizeBiased {mu : Measure ℝ} (hmu : mu (Iio 0) = 0)
    (hE : 0 < mean mu) (hS : 0 < sbMean mu) (c : ℝ) :
    ∫ x, x * Real.exp (-(c * x)) ∂mu
      = mean mu * ∫ y, Real.exp (-(c * sbMean mu * y)) ∂(sizeBiasedLaw mu) := by
  have htr := integral_sizeBiasedLaw hmu hE
    (fun y => Real.exp (-(c * sbMean mu * y))) (by fun_prop)
  have hpw : ∫ x, x * Real.exp (-(c * sbMean mu * (x / sbMean mu))) ∂mu
      = ∫ x, x * Real.exp (-(c * x)) ∂mu := by
    apply integral_congr_ae
    filter_upwards with x
    have h1 : -(c * sbMean mu * (x / sbMean mu)) = -(c * x) := by field_simp
    rw [h1]
  rw [hpw] at htr
  rw [htr, ← mul_assoc, mul_one_div, div_self hE.ne', one_mul]

/-! ### Bounds for the size-biased kernel integrals -/

/-- `Q` is carried by `[0,inf)` when it is a size-biased law. -/
theorem ae_nonneg_of_Iio {Q : Measure ℝ} (hQ : Q (Iio 0) = 0) :
    ∀ᵐ y ∂Q, 0 ≤ y := by
  filter_upwards [compl_mem_ae_iff.mpr hQ] with y hy
  simpa using hy

/-- On `[0,inf)` the kernel integral is bounded by the rate. -/
theorem integral_kern_le {Q : Measure ℝ} [IsFiniteMeasure Q] (hQ : Q (Iio 0) = 0) {s : ℝ}
    (hs : 0 < s) :
    ∫ y, kern s y ∂Q ≤ s * (Q Set.univ).toReal := by
  have hsup := ae_nonneg_of_Iio hQ
  have hb' : ∀ᵐ y ∂Q, ‖kern s y‖ ≤ s := by
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg hs hy)]
    exact kern_le_rate hs hy
  have hb : ∀ᵐ y ∂Q, kern s y ≤ s := by
    filter_upwards [hsup] with y hy
    exact kern_le_rate hs hy
  have hle := integral_mono_ae (Integrable.of_bound (measurable_kern s).aestronglyMeasurable s hb')
    (integrable_const s) hb
  have h2 : ∫ _x, (s : ℝ) ∂Q = s * (Q Set.univ).toReal := by
    rw [integral_const, smul_eq_mul, Measure.real, mul_comm]
  rw [h2] at hle
  exact hle

/-- `E_Q[kern .]` is `1`-Lipschitz in the rate, for laws carried by `[0,inf)`. -/
theorem abs_integral_kern_sub_le {Q : Measure ℝ} [IsFiniteMeasure Q] (hQ : Q (Iio 0) = 0) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    |(∫ y, kern s y ∂Q) - ∫ y, kern t y ∂Q| ≤ |s - t| * (Q Set.univ).toReal := by
  have hsup := ae_nonneg_of_Iio hQ
  have hi1 : Integrable (fun y => kern s y) Q := by
    refine Integrable.of_bound (measurable_kern s).aestronglyMeasurable s ?_
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg hs hy)]
    exact kern_le_rate hs hy
  have hi2 : Integrable (fun y => kern t y) Q := by
    refine Integrable.of_bound (measurable_kern t).aestronglyMeasurable t ?_
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg ht hy)]
    exact kern_le_rate ht hy
  have hb : ∀ᵐ y ∂Q, ‖kern s y - kern t y‖ ≤ |s - t| := by
    filter_upwards [hsup] with y hy
    rw [Real.norm_eq_abs]
    exact abs_kern_sub_kern_le hs.le ht.le hy
  rw [← integral_sub hi1 hi2]
  calc |∫ y, kern s y - kern t y ∂Q| ≤ ∫ y, |kern s y - kern t y| ∂Q :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, |s - t| ∂Q := by
        exact integral_mono_ae (hi1.sub hi2).norm (integrable_const _) hb
    _ = |s - t| * (Q Set.univ).toReal := by rw [integral_const, smul_eq_mul, Measure.real, mul_comm]



/-! ### Stage 1: the fixed-rate limit along the cutoff family -/

/-- **Stage 1 of the proof of Proposition I.3.2.**  For a fixed rate `lam`, along any
cutoff family with `h r * Ê_r → lam`, the normalised cut-off Laplace transform
converges to `A1 * (∫ (1-e^{-lamy})/y dQ_inf) / lam`.  No regular-variation input is
used here: this is the analytic core of the paper's display (I.3.7). -/
theorem stage1_mgf_ratio
    (mu : ℝ → Measure ℝ) (Qinf : Measure ℝ)
    (hmu : ∀ r, mu r (Iio 0) = 0)
    (hEpos : ∀ r, 0 < mean (mu r))
    (hSpos : ∀ r, 0 < sbMean (mu r))
    (hprob : ∀ r, IsProbabilityMeasure (sizeBiasedLaw (mu r)))
    {A1 α lam : ℝ} (hA1 : 0 < A1) (hlam : 0 < lam)
    (h : ℝ → ℝ) (hhpos : ∀ᶠ r in atTop, 0 < h r)
    (hE : Tendsto (fun r => mean (mu r) / (A1 * r ^ α)) atTop (𝓝 1))
    (hrate : Tendsto (fun r => h r * sbMean (mu r)) atTop (𝓝 lam))
    (hker : Tendsto (fun r => ∫ y, kern lam y ∂(sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, kern lam y ∂Qinf))) :
    Tendsto (fun r => (∫ x, (1 - Real.exp (-(h r * x))) ∂(mu r)) / (r ^ α * h r))
      atTop (𝓝 (A1 * (∫ y, kern lam y ∂Qinf) / lam)) := by
  have hJ := hker
  have hposr : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  have heq : ∀ᶠ r in atTop,
      (∫ x, (1 - Real.exp (-(h r * x))) ∂(mu r)) / (r ^ α * h r)
        = (mean (mu r) / (A1 * r ^ α)) * (A1 / (h r * sbMean (mu r)))
          * (∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r))) := by
    filter_upwards [hhpos, hposr] with r hr hrpos
    rw [laplace_eq_sizeBiased (hmu r) (hEpos r) (hSpos r) (h r)]
    have hrp : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hrpos α).ne'
    have hs : sbMean (mu r) ≠ 0 := (hSpos r).ne'
    have hA : A1 ≠ 0 := hA1.ne'
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hstep2 : Tendsto (fun r => A1 / (h r * sbMean (mu r))) atTop (𝓝 (A1 / lam)) :=
    tendsto_const_nhds.div hrate hlam.ne'
  have hstep3 : Tendsto
      (fun r => ∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r))) atTop
      (𝓝 (∫ y, kern lam y ∂Qinf)) := by
    have hbd : ∀ᶠ r in atTop,
        |(∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r)))
          - (∫ y, kern lam y ∂Qinf)|
        ≤ |h r * sbMean (mu r) - lam|
          + |(∫ y, kern lam y ∂(sizeBiasedLaw (mu r))) - (∫ y, kern lam y ∂Qinf)| := by
      filter_upwards [hhpos] with r hr
      have := hprob r
      have h1 : |(∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r)))
            - (∫ y, kern lam y ∂(sizeBiasedLaw (mu r)))|
          ≤ |h r * sbMean (mu r) - lam| * ((sizeBiasedLaw (mu r)) Set.univ).toReal :=
        abs_integral_kern_sub_le (sizeBiasedLaw_Iio_zero (hmu r) (hSpos r))
          (mul_pos hr (hSpos r)) hlam
      have h2 : ((sizeBiasedLaw (mu r)) Set.univ).toReal = 1 := by
        rw [measure_univ]; rfl
      calc |(∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r)))
            - (∫ y, kern lam y ∂Qinf)|
          ≤ |(∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r)))
              - (∫ y, kern lam y ∂(sizeBiasedLaw (mu r)))|
            + |(∫ y, kern lam y ∂(sizeBiasedLaw (mu r))) - (∫ y, kern lam y ∂Qinf)| :=
            abs_sub_le _ _ _
        _ ≤ |h r * sbMean (mu r) - lam| * 1
            + |(∫ y, kern lam y ∂(sizeBiasedLaw (mu r))) - (∫ y, kern lam y ∂Qinf)| := by
            rw [h2] at h1; linarith
        _ = _ := by ring
    have hzero : Tendsto (fun r => |h r * sbMean (mu r) - lam|
        + |(∫ y, kern lam y ∂(sizeBiasedLaw (mu r))) - (∫ y, kern lam y ∂Qinf)|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r => |h r * sbMean (mu r) - lam|) atTop (𝓝 0) := by
        have := hrate.sub_const lam
        simpa using this.abs
      have h2 : Tendsto (fun r => |(∫ y, kern lam y ∂(sizeBiasedLaw (mu r)))
          - (∫ y, kern lam y ∂Qinf)|) atTop (𝓝 0) := by
        have hsub : Tendsto (fun r => (∫ y, kern lam y ∂(sizeBiasedLaw (mu r)))
            - (∫ y, kern lam y ∂Qinf)) atTop (𝓝 0) := by
          simpa using hJ.sub_const (∫ y, kern lam y ∂Qinf)
        simpa using hsub.abs
      simpa using h1.add h2
    have hzero' : Tendsto (fun r => |(∫ y, kern (h r * sbMean (mu r)) y ∂(sizeBiasedLaw (mu r)))
          - (∫ y, kern lam y ∂Qinf)|) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun r => abs_nonneg _) hbd hzero
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hzero'
  have hlim := (hE.mul hstep2).mul hstep3
  have hval : 1 * (A1 / lam) * (∫ y, kern lam y ∂Qinf)
      = (A1 * (∫ y, kern lam y ∂Qinf)) / lam := by
    field_simp
  rwa [hval] at hlim
