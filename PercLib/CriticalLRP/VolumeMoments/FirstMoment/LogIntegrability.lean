/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Member m5, swarm smwg5u3az — direction E (HD first-moment asymptotics).

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.13 (p. 39).

  "If `h : (0,∞) → ℝ` is a logarithmically integrable error function then so are
   the functions `r ↦ r^a ∫_r^∞ s^{-a-1} h(s) ds` and `r ↦ r^{-a}∫_1^r s^{a-1} h(s) ds`
   for every `a > 0`."

Paper's proof: Tonelli on the triangle `{(r,s) : 1 ≤ r ≤ s}`,
`∫_1^∞ [r^a ∫_r^∞ |h s| s^{-a-1} ds] dr/r = ∫_1^∞ |h s| s^{-a-1} ∫_1^s r^{a-1} dr ds
 ≤ (1/a) ∫_1^∞ |h s| ds/s`.

Formalization notes (explicit deviations, none hidden):
* `LogarithmicallyIntegrable h` (repository definition) is `Measurable h ∧
  ∃ r₀ > 0, IntegrableOn (fun r => |h r| / r) (Ioi r₀)`.  The paper's "error
  function" also carries `h → 0` and local integrability; neither is used in the
  Tonelli computation.
* Local integrability of `h` near `0` is *not* implied by the definition, so the
  measurability of the parametric integral `r ↦ ∫ s in Ioi r, s^{-a-1} h s` is
  carried as an explicit hypothesis in the packaged statements
  `lemma_I_4_13_upper` / `lemma_I_4_13_lower`.  The integrability content — the
  actual mathematical assertion of Lemma I.4.13 — is proved unconditionally in
  `integrableOn_hardyUpper`.  In the application (Proposition I.4.2)
  measurability of the error profile is supplied by measurability of
  `r ↦ E_{β,r}|K|`.
-/
module

public import PercLib.CriticalLRP.Analysis.ODE_I_4_5_three

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-! ### Closure properties of `LogarithmicallyIntegrable` -/

theorem logIntegrable_mono {g h : ℝ → ℝ} (hg : Measurable g)
    (hh : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h)
    (hle : ∀ r, 0 < r → |g r| ≤ |h r|) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable g := by
  obtain ⟨hm, r₀, hr₀, hint⟩ := hh
  refine ⟨hg, r₀, hr₀, ?_⟩
  refine Integrable.mono hint (Measurable.aestronglyMeasurable (hg.abs.div measurable_id)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans hr₀ hr
  have hgnn : 0 ≤ |g r| / r := by positivity
  have hhnn : 0 ≤ |h r| / r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgnn, abs_of_nonneg hhnn]
  exact div_le_div_of_nonneg_right (hle r hr0) hr0.le

theorem logIntegrable_const_mul {h : ℝ → ℝ} (c : ℝ)
    (hh : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable (fun r => c * h r) := by
  obtain ⟨hm, r₀, hr₀, hint⟩ := hh
  refine ⟨measurable_const.mul hm, r₀, hr₀, ?_⟩
  refine Integrable.mono (hint.const_mul |c|)
    (Measurable.aestronglyMeasurable ((measurable_const.mul hm).abs.div measurable_id)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans hr₀ hr
  have h1 : 0 ≤ |c| * (|h r| / r) := by positivity
  have h2 : 0 ≤ |c * h r| / r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2, abs_of_nonneg h1, abs_mul]
  rw [mul_div_assoc]

theorem logIntegrable_neg {h : ℝ → ℝ}
    (hh : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable (fun r => -h r) := by
  have := logIntegrable_const_mul (-1) hh
  simpa using this

theorem logIntegrable_add {g h : ℝ → ℝ}
    (hg : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable g)
    (hh : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable (fun r => g r + h r) := by
  obtain ⟨hgm, r₀, hr₀, hgint⟩ := hg
  obtain ⟨hhm, r₁, hr₁, hhint⟩ := hh
  refine ⟨hgm.add hhm, max r₀ r₁, lt_max_of_lt_left hr₀, ?_⟩
  have hsub_g : Ioi (max r₀ r₁) ⊆ Ioi r₀ := Ioi_subset_Ioi (le_max_left _ _)
  have hsub_h : Ioi (max r₀ r₁) ⊆ Ioi r₁ := Ioi_subset_Ioi (le_max_right _ _)
  have h1 : IntegrableOn (fun r => |g r| / r) (Ioi (max r₀ r₁)) := hgint.mono_set hsub_g
  have h2 : IntegrableOn (fun r => |h r| / r) (Ioi (max r₀ r₁)) := hhint.mono_set hsub_h
  have hsum : IntegrableOn (fun r => |g r| / r + |h r| / r) (Ioi (max r₀ r₁)) := h1.add h2
  refine Integrable.mono hsum
    (Measurable.aestronglyMeasurable ((hgm.add hhm).abs.div measurable_id)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans (lt_max_of_lt_left hr₀) hr
  have h3 : 0 ≤ |g r + h r| / r := by positivity
  have h4 : 0 ≤ |g r| / r + |h r| / r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3, abs_of_nonneg h4]
  have h5 : |g r + h r| ≤ |g r| + |h r| := abs_add_le _ _
  calc |g r + h r| / r ≤ (|g r| + |h r|) / r := div_le_div_of_nonneg_right h5 hr0.le
    _ = |g r| / r + |h r| / r := by ring

/-! ### Tonelli on the triangle `{c < r < s}` -/

theorem lintegral_triangle {p q : ℝ → ℝ≥0∞} (hp : Measurable p) (hq : Measurable q) {c : ℝ} :
    ∫⁻ r in Ioi c, p r * (∫⁻ s in Ioi r, q s)
      = ∫⁻ s in Ioi c, q s * (∫⁻ r in Ioo c s, p r) := by
  set T : Set (ℝ × ℝ) := {a : ℝ × ℝ | c < a.1 ∧ a.1 < a.2} with hT
  have hTmeas : MeasurableSet T :=
    measurableSet_lt measurable_const measurable_fst |>.inter
      (measurableSet_lt measurable_fst measurable_snd)
  set F : ℝ × ℝ → ℝ≥0∞ := T.indicator (fun a : ℝ × ℝ => p a.1 * q a.2) with hF
  have hFmeas : AEMeasurable F (volume.prod volume) :=
    (Measurable.indicator (hp.comp measurable_fst |>.mul (hq.comp measurable_snd))
      hTmeas).aemeasurable
  have hslice1 : ∀ r, ∫⁻ s, F (r, s) = (Ioi c).indicator (fun r => p r * ∫⁻ s in Ioi r, q s) r := by
    intro r
    by_cases hr : c < r
    · rw [Set.indicator_of_mem (show r ∈ Ioi c from hr)]
      have hfun : (fun s => F (r, s)) = fun s => p r * (Ioi r).indicator q s := by
        funext s
        simp only [hF, hT, Set.indicator, mem_ofPred_eq, mem_Ioi]
        by_cases h2 : r < s <;> simp [hr, h2]
      rw [hfun]
      rw [lintegral_const_mul'' (p r) (f := fun s => (Ioi r).indicator q s)
        (Measurable.indicator hq measurableSet_Ioi).aemeasurable]
      congr 1
      exact lintegral_indicator measurableSet_Ioi q
    · rw [Set.indicator_of_notMem (show r ∉ Ioi c from hr)]
      have hfun : (fun s => F (r, s)) = fun s => 0 := by
        funext s
        simp only [hF, hT, Set.indicator, mem_ofPred_eq]
        simp [hr]
      rw [hfun]
      simp
  have hslice2 : ∀ s, ∫⁻ r, F (r, s) = (Ioi c).indicator (fun s => q s * ∫⁻ r in Ioo c s, p r) s := by
    intro s
    by_cases hs : c < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi c from hs)]
      have hfun : (fun r => F (r, s)) = fun r => (Ioo c s).indicator (fun r => p r * q s) r := by
        funext r
        by_cases h1 : c < r
        · by_cases h2 : r < s
          · simp [hF, hT, Set.indicator, h1, h2]
          · simp [hF, hT, Set.indicator, h1, h2]
        · simp [hF, hT, Set.indicator, h1]
      rw [hfun, lintegral_indicator measurableSet_Ioo,
        mul_comm (q s) (∫⁻ r in Ioo c s, p r),
        lintegral_mul_const'' (q s) (f := p) hp.aemeasurable]
    · rw [Set.indicator_of_notMem (show s ∉ Ioi c from hs)]
      have hfun : (fun r => F (r, s)) = fun r => 0 := by
        funext r
        simp only [hF, hT, Set.indicator, mem_ofPred_eq]
        by_cases h1 : c < r
        · have h2 : ¬ r < s := fun h => hs (lt_trans h1 h)
          simp [h1, h2]
        · simp [h1]
      rw [hfun]
      simp
  calc ∫⁻ r in Ioi c, p r * (∫⁻ s in Ioi r, q s)
      = ∫⁻ r, (Ioi c).indicator (fun r => p r * ∫⁻ s in Ioi r, q s) r :=
        (lintegral_indicator measurableSet_Ioi _).symm
    _ = ∫⁻ r, ∫⁻ s, F (r, s) := lintegral_congr fun r => (hslice1 r).symm
    _ = ∫⁻ a : ℝ × ℝ, F a := (MeasureTheory.lintegral_prod F hFmeas).symm
    _ = ∫⁻ s, ∫⁻ r, F (r, s) := MeasureTheory.lintegral_prod_symm F hFmeas
    _ = ∫⁻ s, (Ioi c).indicator (fun s => q s * ∫⁻ r in Ioo c s, p r) s :=
        lintegral_congr hslice2
    _ = ∫⁻ s in Ioi c, q s * (∫⁻ r in Ioo c s, p r) := lintegral_indicator measurableSet_Ioi _

set_option maxHeartbeats 1000000 in
/-- The explicit value of the inner integral appearing in the triangle computation,
for `0 < c ≤ s`.  (The restriction `c ≤ s` avoids `Real.rpow`'s junk value on
negative bases; only the case `0 < c ≤ s` is used below.) -/
theorem lintegral_Ioo_ofReal_rpow {a c s : ℝ} (ha : 0 < a) (hc : 0 < c) (hcs : c ≤ s) :
    ∫⁻ r in Ioo c s, ENNReal.ofReal (r ^ (a - 1)) = ENNReal.ofReal ((s ^ a - c ^ a) / a) := by
  have hii : IntervalIntegrable (fun r : ℝ => r ^ (a - 1)) volume c s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hIoc : IntegrableOn (fun r : ℝ => r ^ (a - 1)) (Ioc c s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcs).1 hii
  have hIoo : IntegrableOn (fun r : ℝ => r ^ (a - 1)) (Ioo c s) :=
    hIoc.congr_set_ae Ioo_ae_eq_Ioc
  have hnonneg : ∀ᵐ r ∂(volume.restrict (Ioo c s)), (0:ℝ) ≤ r ^ (a - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg (le_of_lt (lt_trans hc hr.1)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hIoo hnonneg]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcs,
    integral_rpow (Or.inl (by linarith : -1 < a - 1))]
  norm_num



/-! ### The parametric integral is measurable -/

/-- The parametric integral `r ↦ ∫ s in Ioi r, s^{-a-1}|h s|` is measurable
whenever `h` is.  (No integrability is needed: the Bochner integral is defined
for every function, with junk value `0` off the integrable set.) -/
theorem measurable_param_hardy {h : ℝ → ℝ} (hm : Measurable h) (a : ℝ) :
    Measurable (fun r => ∫ s in Ioi r, s ^ (-a - 1) * |h s|) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hfun : Measurable (fun p : ℝ × ℝ => p.2 ^ (-a - 1) * |h p.2|) := by
    fun_prop
  have hite : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then p.2 ^ (-a - 1) * |h p.2| else 0) :=
    Measurable.ite hset hfun measurable_const
  have hjoint : Measurable (Function.uncurry fun r s : ℝ =>
      (Ioi r).indicator (fun s => s ^ (-a - 1) * |h s|) s) := by
    convert hite using 1
    ext p
    simp [Function.uncurry, Set.indicator]
  have hres := hjoint.stronglyMeasurable.integral_prod_right (ν := volume)
  have hsm : StronglyMeasurable (fun r => ∫ s in Ioi r, s ^ (-a - 1) * |h s|) := by
    convert hres using 1
    ext r
    exact (integral_indicator (μ := volume) (s := Ioi r)
      (f := fun s => s ^ (-a - 1) * |h s|) measurableSet_Ioi).symm
  exact hsm.measurable

/-! ### The majorant of Lemma I.4.13 -/

/-- Pointwise identification of `ofReal` of the majorant with the `lintegral`
expression to which Tonelli applies. -/
theorem ofReal_hardyMajorant {h : ℝ → ℝ} {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hm : Measurable h)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r)) :
    ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|)
      = ENNReal.ofReal (r ^ (a - 1))
        * ∫⁻ s in Ioi r, ENNReal.ofReal (s ^ (-a - 1) * |h s|) := by
  set g : ℝ → ℝ := fun s => s ^ (-a - 1) * |h s| with hg
  have hgnn : ∀ s ∈ Ioi r, 0 ≤ g s := by
    intro s hs
    have hs0 : 0 < s := lt_trans hr hs
    exact mul_nonneg (Real.rpow_nonneg hs0.le _) (abs_nonneg _)
  have hdom : ∀ s ∈ Ioi r, |g s| ≤ r ^ (-a) * (|h s| / s) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hr hs
    have hsr : r ≤ s := le_of_lt hs
    have hpow : s ^ (-a - 1) ≤ r ^ (-a) * s⁻¹ := by
      have h1 : s ^ (-a - 1) = s ^ (-a) * s ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hs0]; ring_nf
      rw [h1, Real.rpow_neg_one]
      have hra : r ^ (-a) = (r ^ a)⁻¹ := Real.rpow_neg hr.le a
      have hsa : s ^ (-a) = (s ^ a)⁻¹ := Real.rpow_neg hs0.le a
      rw [hra, hsa]
      exact mul_le_mul_of_nonneg_right
        (inv_anti₀ (Real.rpow_pos_of_pos hr a) (Real.rpow_le_rpow hr.le hsr ha.le))
        (by positivity)
    calc |g s| = s ^ (-a - 1) * |h s| := by
          rw [hg, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_abs]
      _ ≤ (r ^ (-a) * s⁻¹) * |h s| := mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ = r ^ (-a) * (|h s| / s) := by rw [div_eq_mul_inv]; ring
  have hgm : Measurable g := by
    have : Measurable fun s : ℝ => s ^ (-a - 1) := by fun_prop
    exact this.mul hm.abs
  have hgint : IntegrableOn g (Ioi r) := by
    refine Integrable.mono (hint.const_mul (r ^ (-a))) hgm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hb : 0 ≤ r ^ (-a) * (|h s| / s) := by
      have hr0 : 0 < r := hr
      have hs0 : 0 < s := lt_trans hr hs
      exact mul_nonneg (Real.rpow_nonneg hr0.le _) (by positivity)
    have hb' : ‖r ^ (-a) * (|h s| / s)‖ = r ^ (-a) * (|h s| / s) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hb]
    rw [hb']
    exact hdom s hs
  have hgnn_ae : 0 ≤ᵐ[volume.restrict (Ioi r)] g :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => hgnn s hs
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
    ofReal_integral_eq_lintegral_ofReal hgint hgnn_ae]

/-- **The Tonelli bound of Lemma I.4.13 (first clause)**: the `r`-weighted
integral of the Hardy majorant of `|h|` is bounded by `(1/a) ∫ |h s| ds/s`. -/
theorem lintegral_hardyMajorant_le {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hm : Measurable h)
    (hint : IntegrableOn (fun r => |h r| / r) (Ioi r₀)) :
    ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|)
      ≤ ENNReal.ofReal (1 / a) * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
  set p : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (a - 1)) with hp
  set q : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-a - 1) * |h s|) with hq
  have hpm : Measurable p := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  have hqm : Measurable q := by
    refine Measurable.ennreal_ofReal ?_
    have h1 : Measurable fun s : ℝ => s ^ (-a - 1) := by fun_prop
    exact h1.mul hm.abs
  have hint' : ∀ r, r₀ < r → IntegrableOn (fun s => |h s| / s) (Ioi r) := by
    intro r hr
    exact hint.mono_set (Ioi_subset_Ioi hr.le)
  -- the pointwise identification on `Ioi r₀`
  have hcongr : ∀ᵐ r ∂(volume.restrict (Ioi r₀)),
      ENNReal.ofReal (r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) = p r * ∫⁻ s in Ioi r, q s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact ofReal_hardyMajorant ha (lt_trans hr₀ hr) hm (hint' r hr)
  rw [lintegral_congr_ae hcongr, lintegral_triangle hpm hqm]
  have hinner : ∀ s ∈ Ioi r₀, ∫⁻ r in Ioo r₀ s, p r = ENNReal.ofReal ((s ^ a - r₀ ^ a) / a) := by
    intro s hs
    exact lintegral_Ioo_ofReal_rpow ha hr₀ (le_of_lt hs)
  have hcongr2 : ∀ᵐ s ∂(volume.restrict (Ioi r₀)),
      q s * ∫⁻ r in Ioo r₀ s, p r = q s * ENNReal.ofReal ((s ^ a - r₀ ^ a) / a) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => by rw [hinner s hs]
  rw [lintegral_congr_ae hcongr2]
  have hstep : ∫⁻ s in Ioi r₀, q s * ENNReal.ofReal ((s ^ a - r₀ ^ a) / a)
      ≤ ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s / a) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr₀ hs
    have hrpow : s ^ (-a - 1) * s ^ a = s⁻¹ := by
      rw [← Real.rpow_add hs0, show -a - 1 + a = -1 by ring, Real.rpow_neg_one]
    have hfac : s ^ (-a - 1) * |h s| * ((s ^ a - r₀ ^ a) / a)
        = (|h s| / a) * (s ^ (-a - 1) * (s ^ a - r₀ ^ a)) := by ring
    have hle1 : s ^ a - r₀ ^ a ≤ s ^ a := by
      have h0 : 0 ≤ r₀ ^ a := Real.rpow_nonneg hr₀.le a
      linarith
    have h2 : s ^ (-a - 1) * (s ^ a - r₀ ^ a) ≤ s ^ (-a - 1) * s ^ a :=
      mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hs0.le _)
    have h3 : (|h s| / a) * (s ^ (-a - 1) * (s ^ a - r₀ ^ a)) ≤ (|h s| / a) * s⁻¹ := by
      rw [← hrpow]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hkey : (|h s| / a) * s⁻¹ = |h s| / s / a := by
      rw [div_eq_mul_inv]
      ring
    show q s * ENNReal.ofReal ((s ^ a - r₀ ^ a) / a) ≤ ENNReal.ofReal (|h s| / s / a)
    rw [hq, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hfac]
    exact le_trans h3 (le_of_eq hkey)
  refine le_trans hstep ?_
  have hfin : ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s / a)
      = ENNReal.ofReal (1 / a) * ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s) := by
    have h1 : ∫⁻ s in Ioi r₀, ENNReal.ofReal (|h s| / s / a)
        = ∫⁻ s in Ioi r₀,
          ENNReal.ofReal (1 / a) * ENNReal.ofReal (|h s| / s) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_trans hr₀ hs
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [one_div, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h1]
    exact lintegral_const_mul'' _
      (by fun_prop : AEMeasurable (fun s : ℝ => ENNReal.ofReal (|h s| / s))
        (volume.restrict (Ioi r₀)))
  rw [hfin]

/-- **Lemma I.4.13, first clause — integrability content**, unconditionally. -/
theorem integrableOn_hardyUpper {h : ℝ → ℝ} {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hm : Measurable h)
    (hint : IntegrableOn (fun r => |h r| / r) (Ioi r₀)) :
    IntegrableOn (fun r => r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) (Ioi r₀) := by
  have hmeas : Measurable (fun r => r ^ (a - 1) * ∫ s in Ioi r, s ^ (-a - 1) * |h s|) := by
    have h1 : Measurable fun r : ℝ => r ^ (a - 1) := by fun_prop
    exact h1.mul (measurable_param_hardy hm a)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans hr₀ hr
    exact mul_nonneg (Real.rpow_nonneg hr0.le _)
      (integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := lt_trans hr0 hs
        exact mul_nonneg (Real.rpow_nonneg hs0.le _) (abs_nonneg _))))]
  refine lt_of_le_of_lt (lintegral_hardyMajorant_le ha hr₀ hm hint) ?_
  rw [ENNReal.mul_lt_top_iff]
  refine Or.inl ⟨ENNReal.ofReal_lt_top, ?_⟩
  exact hint.setLIntegral_lt_top

end PercLib.CriticalLRP.VolumeMoments.FirstMoment
