/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The Tauberian converse of Hutchcroft, Theorem I.2.11** (arXiv:2508.18807v1, p. 26).

This file develops, sorry-free and on the standard axioms only, the converse direction of
Theorem I.2.11 for an *antitone* tail function `F`.

Structure of the argument (all steps formalised here):

* `integral_exp_sigma_mul_div`: the rescaling identity
  `∫_0^∞ e^{-σu}F(u/h) = σ⁻¹ ∫_0^∞ e^{-u}F(u/(σh))`;
* `tendsto_laplace_family`: the hypothesis holds at **every** scale `σ > 0`:
  `∫_0^∞ e^{-σu}(F(u/h)/f(1/h)) → σ^{α-1}`;
-/
module

public import PercLib.CriticalLRP.Analysis.TauberianLaplace

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### The rescaling identity for the Laplace family -/

/-- For `F` antitone and nonnegative, `u ↦ e^{-u} F (u/h)` is integrable on `(0,∞)`. -/
theorem integrableOn_exp_mul_div_of_antitone {F : ℝ → ℝ} (hanti : Antitone F)
    (hF0 : ∀ x, 0 ≤ F x) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * F (u/h)) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-u) * F 0) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := (-1:ℝ)) (by norm_num) (0:ℝ)
    have h' : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by simpa using h
    exact h'.mul_const (F 0)
  refine Integrable.mono' hbase ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Real.measurable_exp.comp measurable_id.neg).mul
      (hanti.measurable.comp (measurable_id.div_const h))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : 0 < u := hu
    have hx : (0:ℝ) ≤ u/h := (div_pos hupos hh).le
    have hle : F (u/h) ≤ F 0 := hanti hx
    have hnn : 0 ≤ F (u/h) := hF0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hnn)]
    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- The rescaling identity `∫_0^∞ e^{-σu}F(u/h) du = σ⁻¹ ∫_0^∞ e^{-u}F(u/(σh)) du`. -/
theorem integral_exp_sigma_mul_div (F : ℝ → ℝ) {σ h : ℝ} (hσ : 0 < σ) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)
      = σ⁻¹ * ∫ w in Ioi (0:ℝ), Real.exp (-w) * F (w/(σ*h)) := by
  have h := integral_comp_mul_left_Ioi (fun w : ℝ => Real.exp (-w) * F (w/(σ*h))) (a := (0:ℝ)) hσ
  have hzero : σ * 0 = (0:ℝ) := by ring
  rw [hzero, smul_eq_mul] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro u _
  field_simp

/-! ### The hypothesis at every scale -/

/-- **The Laplace family.**  Under the hypothesis `∫ e^{-u}F(u/h) ~ f(1/h)`, the same
asymptotic holds with the exponential weight `e^{-σu}` for every fixed `σ > 0`, with the
regular-variation factor `σ^{α-1}`. -/
theorem tendsto_laplace_family
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1))
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h))
      (𝓝[>] 0) (𝓝 (σ^(α-1))) := by
  -- the rescaled sequence tends to zero
  have hshift : Tendsto (fun h : ℝ => σ * h) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun h : ℝ => σ * h := continuous_const.mul continuous_id
      simpa using hc.tendsto' 0 0 (by ring) |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact mul_pos hσ hh
  -- the hypothesis at the rescaled scale
  have hcomp : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/(σ*h))) / f (1/(σ*h)))
      (𝓝[>] 0) (𝓝 1) := hmain.comp hshift
  -- regular variation at ratio `1/σ`
  have hinv : Tendsto (fun x : ℝ => f ((1/σ) * x) / f x) atTop (𝓝 ((1/σ)^(-α))) :=
    hrv.2 (1/σ) (by positivity)
  have hhalf : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hratio : Tendsto (fun h : ℝ => f (1/(σ*h)) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 (σ^α)) := by
    have h := hinv.comp hhalf
    have hval : (1/σ)^(-α) = σ^α := by
      rw [one_div, Real.inv_rpow (le_of_lt hσ), Real.rpow_neg (le_of_lt hσ), inv_inv]
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards with h
    simp only [Function.comp_apply]
    congr 2
    field_simp
  -- combine
  have hprod : Tendsto (fun h : ℝ => σ⁻¹ *
      ((∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/(σ*h))) / f (1/(σ*h))) *
      (f (1/(σ*h)) / f (1/h))) (𝓝[>] 0) (𝓝 (σ⁻¹ * 1 * σ^α)) :=
    ((hcomp.const_mul σ⁻¹).mul hratio)
  have hval : σ⁻¹ * 1 * σ^α = σ^(α-1) := by
    rw [mul_one, ← Real.rpow_neg_one (x := σ), ← Real.rpow_add hσ,
      show (-1:ℝ) + α = α - 1 from by ring]
  rw [hval] at hprod
  refine hprod.congr' ?_
  -- the algebraic rewriting, done on the set where the denominators do not vanish
  have hne1 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (1/h) ≠ 0 := by
    filter_upwards [hhalf.eventually hrv.1] with h hh using hh
  have hhalfσ : Tendsto (fun h : ℝ => 1/(σ*h)) (𝓝[>] (0:ℝ)) atTop := by
    have h1 : Tendsto (fun h : ℝ => (1/σ) * (1/h)) (𝓝[>] (0:ℝ)) atTop :=
      hhalf.const_mul_atTop (by positivity)
    refine h1.congr' ?_
    filter_upwards with h
    field_simp
  have hne2 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (1/(σ*h)) ≠ 0 := by
    filter_upwards [hhalfσ.eventually hrv.1] with h hh using hh
  filter_upwards [self_mem_nhdsWithin, hne1, hne2] with h hh h1 h2
  rw [integral_exp_sigma_mul_div F hσ]
  field_simp

/-! ### The normalised antitone profile and its bounds -/

/-- The normalised profile `u ↦ Γ(1-α) F(u/h)/f(1/h)`; the conclusion of Theorem I.2.11 is
`Φ h 1 → 1`. -/
noncomputable def Phi (α : ℝ) (F f : ℝ → ℝ) (h u : ℝ) : ℝ :=
  Real.Gamma (1 - α) * F (u/h) / f (1/h)

/-- Eventual positivity of the normalising factor. -/
theorem eventually_pos_f_inv {F f : ℝ → ℝ}
    (hF0 : ∀ x, 0 ≤ F x)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1)) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), 0 < f (1/h) := by
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      0 < (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h) :=
    hmain.eventually (eventually_gt_nhds zero_lt_one)
  filter_upwards [hpos, self_mem_nhdsWithin] with h hh hhpos
  have hint : 0 ≤ ∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h) :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => mul_nonneg (Real.exp_pos _).le (hF0 _))
  rcases lt_trichotomy (f (1/h)) 0 with hlt | heq | hgt
  · have hle : (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hint hlt.le
    linarith
  · rw [heq, div_zero] at hh
    linarith
  · exact hgt

/-- Integrability with a general exponential weight `e^{-σu}`. -/
theorem integrableOn_exp_sigma_mul_div_of_antitone {F : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hanti : Antitone F) (hF0 : ∀ x, 0 ≤ F x) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * F (u/h)) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * F 0) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -σ) (by linarith) (0:ℝ)
    have h' : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u))) (Ioi 0) := by
      simpa [neg_mul] using h
    exact h'.mul_const (F 0)
  refine Integrable.mono' hbase ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).mul
      (hanti.measurable.comp (measurable_id.div_const h))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : 0 < u := hu
    have hx : (0:ℝ) ≤ u/h := (div_pos hupos hh).le
    have hle : F (u/h) ≤ F 0 := hanti hx
    have hnn : 0 ≤ F (u/h) := hF0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hnn)]
    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- **The antitone upper bound (crude form).**  If the Laplace hypothesis holds and `F` is
antitone, then `F(u₀/h)/f(1/h)` is eventually bounded by
`(3/2) σ^(α-1) e^{σ u₀}/u₀` for every `σ > 0`. -/
theorem antitone_ratio_eventually_le
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1))
    {u₀ σ : ℝ} (hu₀ : 0 < u₀) (hσ : 0 < σ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      F (u₀/h) / f (1/h) ≤ (3/2) * σ^(α-1) * Real.exp (σ*u₀) / u₀ := by
  classical
  have hfam := tendsto_laplace_family hFmeas hF0 hanti hfmeas hrv hmain hσ
  have hfpos := eventually_pos_f_inv hF0 hmain
  have hσpos : (0:ℝ) < σ^(α-1) := Real.rpow_pos_of_pos hσ _
  have hbdd : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h) ≤ (3/2) * σ^(α-1) := by
    refine hfam.eventually (eventually_le_nhds ?_)
    linarith
  filter_upwards [hfpos, hbdd, self_mem_nhdsWithin] with h hfpos' hbdd' hh
  -- monotone comparison with the constant lower bound `e^{-σ u₀}` on `(0,u₀)`
  have hmono : F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀)
      ≤ ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h) := by
    have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * F (u₀/h)) (Ioo 0 u₀) := by
      have hint : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u))) (Ioi (0:ℝ)) := by
        have h := integrableOn_exp_mul_Ioi (a := -σ) (by linarith : (-σ:ℝ) < 0) (0:ℝ)
        simpa [neg_mul] using h
      exact (hint.mono_set (fun u hu => hu.1)).mul_const (F (u₀/h))
    have hint2 : IntegrableOn (fun u : ℝ => Real.exp (-(σ*u)) * F (u/h)) (Ioo (0:ℝ) u₀) :=
      (integrableOn_exp_sigma_mul_div_of_antitone hσ hanti hF0 hh).mono_set
        (fun u hu => hu.1)
    have hlow : F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀)
        ≤ ∫ u in Ioo (0:ℝ) u₀, Real.exp (-(σ*u)) * F (u₀/h) := by
      have hc : ∫ u in Ioo (0:ℝ) u₀, (Real.exp (-(σ*u₀)) * F (u₀/h))
          = F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀) := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
          smul_eq_mul]
        ring
      rw [← hc]
      have hintc : IntegrableOn (fun _ : ℝ => Real.exp (-(σ*u₀)) * F (u₀/h)) (Ioo 0 u₀) :=
        integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      refine setIntegral_mono_on hintc hint1 measurableSet_Ioo ?_
      intro u hu
      rw [mem_Ioo] at hu
      have hexp : Real.exp (-(σ*u₀)) ≤ Real.exp (-(σ*u)) := by
        rw [Real.exp_le_exp]
        nlinarith [hu.1]
      exact mul_le_mul_of_nonneg_right hexp (hF0 _)
    calc F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀)
        ≤ ∫ u in Ioo (0:ℝ) u₀, Real.exp (-(σ*u)) * F (u₀/h) := hlow
      _ ≤ ∫ u in Ioo (0:ℝ) u₀, Real.exp (-(σ*u)) * F (u/h) := by
          refine setIntegral_mono_on hint1 hint2 measurableSet_Ioo ?_
          intro u hu
          rw [mem_Ioo] at hu
          have hle : u/h ≤ u₀/h := by
            rw [div_le_div_iff_of_pos_right hh]
            exact le_of_lt hu.2
          exact mul_le_mul_of_nonneg_left (hanti hle) (Real.exp_pos _).le
      _ ≤ ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h) :=
          setIntegral_mono_set
            (integrableOn_exp_sigma_mul_div_of_antitone hσ hanti hF0 hh)
            (Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (hF0 _)))
            (Filter.Eventually.of_forall
              (fun u (hu : u ∈ Ioo (0:ℝ) u₀) => Ioo_subset_Ioi_self hu))
  -- finish
  have hA : F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀) ≤ (3/2) * σ^(α-1) * f (1/h) := by
    have h1 : (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h) * f (1/h)
        = ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h) := div_mul_cancel₀ _ hfpos'.ne'
    calc F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀)
        ≤ ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h) := hmono
      _ = (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h) * f (1/h) := h1.symm
      _ ≤ (3/2) * σ^(α-1) * f (1/h) := mul_le_mul_of_nonneg_right hbdd' hfpos'.le
  have hpos2 : (0:ℝ) < Real.exp (-(σ*u₀)) * u₀ := mul_pos (Real.exp_pos _) hu₀
  rw [div_le_iff₀ hfpos']
  calc F (u₀/h)
      = F (u₀/h) * (Real.exp (-(σ*u₀)) * u₀) / (Real.exp (-(σ*u₀)) * u₀) := by
        field_simp
    _ ≤ ((3/2) * σ^(α-1) * f (1/h)) / (Real.exp (-(σ*u₀)) * u₀) :=
        div_le_div_of_nonneg_right hA hpos2.le
    _ = (3/2) * σ^(α-1) * Real.exp (σ*u₀) / u₀ * f (1/h) := by
        rw [Real.exp_neg]
        field_simp

/-- **The near-mass bound.**  With `σ = 1/δ`, the mass of the normalised profile on `(0,δ)` is
eventually at most `2 e δ^{1-α}`. -/
theorem near_mass_eventually_le
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      ∫ u in Ioo (0:ℝ) δ, F (u/h) / f (1/h) ≤ 2 * Real.exp 1 * δ^(1-α) := by
  classical
  set σ := 1/δ with hσdef
  have hσ : 0 < σ := by positivity
  have hfam := tendsto_laplace_family hFmeas hF0 hanti hfmeas hrv hmain hσ
  have hfpos := eventually_pos_f_inv hF0 hmain
  have hbdd : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      (∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h) ≤ 2 * σ^(α-1) := by
    refine hfam.eventually (eventually_le_nhds ?_)
    linarith [Real.rpow_pos_of_pos hσ (α-1)]
  have hσval : σ^(α-1) = δ^(1-α) := by
    rw [hσdef, one_div, Real.inv_rpow (le_of_lt hδ), ← Real.rpow_neg (le_of_lt hδ) (α - 1),
      show -(α-1) = 1-α from by ring]
  filter_upwards [hfpos, hbdd, self_mem_nhdsWithin] with h hfpos' hbdd' hh
  have hstep : ∫ u in Ioo (0:ℝ) δ, F (u/h) / f (1/h)
      ≤ Real.exp 1 * ((∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h)) := by
    rw [show (∫ u in Ioo (0:ℝ) δ, F (u/h) / f (1/h))
        = (∫ u in Ioo (0:ℝ) δ, F (u/h)) / f (1/h) from by
      rw [integral_div]]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hfpos']
    calc ∫ u in Ioo (0:ℝ) δ, F (u/h)
        ≤ ∫ u in Ioo (0:ℝ) δ, Real.exp 1 * (Real.exp (-(σ*u)) * F (u/h)) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo ?_
          · have hb : IntegrableOn (fun _ : ℝ => F 0) (Ioo (0:ℝ) δ) :=
              integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
            refine hb.mono' ?_ ?_
            · exact (hanti.measurable.comp (measurable_id.div_const h)).aestronglyMeasurable
            · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
              have hu' : (0:ℝ) < u := hu.1
              have h1 : F (u/h) ≤ F 0 := hanti (div_pos hu' hh).le
              rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
              exact h1
          · exact ((integrableOn_exp_sigma_mul_div_of_antitone hσ hanti hF0 hh).mono_set
              (fun u (hu : u ∈ Ioo (0:ℝ) δ) => Ioo_subset_Ioi_self hu)).const_mul
              (Real.exp 1) |>.congr
              (Filter.Eventually.of_forall (fun u => by ring))
          · intro u hu
            rw [mem_Ioo] at hu
            have hσδ : σ*δ = 1 := by rw [hσdef]; field_simp
            have hexp : (1:ℝ) ≤ Real.exp 1 * Real.exp (-(σ*u)) := by
              rw [← Real.exp_add]
              refine Real.one_le_exp ?_
              have hle : σ*u ≤ σ*δ := mul_le_mul_of_nonneg_left hu.2.le hσ.le
              linarith
            calc F (u/h) = 1 * F (u/h) := by ring
              _ ≤ (Real.exp 1 * Real.exp (-(σ*u))) * F (u/h) :=
                  mul_le_mul_of_nonneg_right hexp (hF0 _)
              _ = Real.exp 1 * (Real.exp (-(σ*u)) * F (u/h)) := by ring
      _ = Real.exp 1 * ∫ u in Ioo (0:ℝ) δ, Real.exp (-(σ*u)) * F (u/h) := by
          rw [integral_const_mul]
      _ ≤ Real.exp 1 * ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
          exact setIntegral_mono_set
            (integrableOn_exp_sigma_mul_div_of_antitone hσ hanti hF0 hh)
            (Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (hF0 _)))
            (Filter.Eventually.of_forall
              (fun u (hu : u ∈ Ioo (0:ℝ) δ) => Ioo_subset_Ioi_self hu))
  calc ∫ u in Ioo (0:ℝ) δ, F (u/h) / f (1/h)
      ≤ Real.exp 1 * ((∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * F (u/h)) / f (1/h)) := hstep
    _ ≤ Real.exp 1 * (2 * σ^(α-1)) := by
        refine mul_le_mul_of_nonneg_left hbdd' (Real.exp_pos 1).le
    _ = 2 * Real.exp 1 * δ^(1-α) := by rw [hσval]; ring

/-- `∫_0^∞ e^{-σu} u^{-α} du = Γ(1-α) σ^{α-1}` — the target profile's Laplace transform. -/
theorem integral_exp_mul_rpow_neg_eq {α : ℝ} (hα1 : α < 1) {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * u ^ (-α) = Real.Gamma (1 - α) * σ ^ (α - 1) := by
  have h := integral_comp_mul_left_Ioi (fun w : ℝ => Real.exp (-w) * w ^ (-α)) (a := (0:ℝ)) hσ
  have hzero : σ * 0 = (0:ℝ) := by ring
  rw [hzero, smul_eq_mul] at h
  have h' : ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * (σ*u) ^ (-α)
      = σ⁻¹ * ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (-α) := h
  have hpt : ∀ u ∈ Ioi (0:ℝ), Real.exp (-(σ*u)) * u ^ (-α)
      = σ ^ α * (Real.exp (-(σ*u)) * (σ*u) ^ (-α)) := by
    intro u hu
    have hu : (0:ℝ) < u := hu
    rw [Real.mul_rpow hσ.le hu.le, Real.rpow_neg hσ.le, Real.rpow_neg hu.le]
    field_simp
  have hσ1 : σ ^ α * σ⁻¹ = σ ^ (α - 1) := by
    rw [← Real.rpow_neg_one (x := σ), ← Real.rpow_add hσ, show α + -1 = α - 1 from by ring]
  calc ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * u ^ (-α)
      = ∫ u in Ioi (0:ℝ), σ ^ α * (Real.exp (-(σ*u)) * (σ*u) ^ (-α)) :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ = σ ^ α * ∫ u in Ioi (0:ℝ), Real.exp (-(σ*u)) * (σ*u) ^ (-α) := integral_const_mul _ _
    _ = σ ^ α * (σ⁻¹ * ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (-α)) := by rw [h']
    _ = (∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (-α)) * σ ^ (α - 1) := by
        rw [← mul_assoc, hσ1, mul_comm]
    _ = Real.Gamma (1 - α) * σ ^ (α - 1) := by rw [Gamma_one_sub_eq_integral hα1]

/-! ### The compactness step -/

/-- The explicit bound on the normalised profile at a rational argument `q > 0`,
`Γ(1-α)·(3/2)·e·q^{-α}` (obtained from `antitone_ratio_eventually_le` with `σ = 1/q`). -/
noncomputable def profileBound (α : ℝ) (q : ℝ) : ℝ :=
  Real.Gamma (1 - α) * ((3/2) * Real.exp 1 * q ^ (-α))

theorem profileBound_nonneg {α : ℝ} (hα1 : α < 1) {q : ℝ} (hq : 0 < q) :
    0 ≤ profileBound α q := by
  have hΓ : (0:ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  refine mul_nonneg hΓ ?_
  have : (0:ℝ) < q ^ (-α) := Real.rpow_pos_of_pos hq _
  positivity

/-- Eventual nonnegativity and the profile bound at each rational argument. -/
theorem eventually_profile_bound
    {F f : ℝ → ℝ} {α : ℝ}
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1))
    (hα1 : α < 1) {q : ℝ} (hq : 0 < q) :
    ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      0 ≤ Phi α F f h q ∧ Phi α F f h q ≤ profileBound α q := by
  have hfpos := eventually_pos_f_inv hF0 hmain
  have hΓ : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hbound := antitone_ratio_eventually_le hFmeas hF0 hanti hfmeas hrv hmain
    (u₀ := q) (σ := 1/q) hq (by positivity)
  have hsimp : (3/2) * (1/q:ℝ)^(α-1) * Real.exp ((1/q)*q) / q
      = profileBound α q / Real.Gamma (1 - α) := by
    rw [profileBound]
    have h1 : (1/q:ℝ)^(α-1) = q^(1-α) := by
      rw [one_div, Real.inv_rpow hq.le, ← Real.rpow_neg hq.le (α - 1),
        show -(α-1) = 1-α from by ring]
    have h2 : (1/q)*q = 1 := by field_simp
    rw [h1, h2]
    have h3 : q ^ (1 - α) / q = q ^ (-α) := by
      rw [show q ^ (1-α) = q ^ (-α) * q from by
        rw [show (1:ℝ) - α = -α + 1 from by ring, Real.rpow_add hq, Real.rpow_one]]
      field_simp
    rw [← h3]
    field_simp
  filter_upwards [hfpos, hbound, self_mem_nhdsWithin] with h hfpos' hbd' hh
  constructor
  · exact div_nonneg (mul_nonneg hΓ.le (hF0 _)) hfpos'.le
  · have hb' : F (q/h) / f (1/h) ≤ profileBound α q / Real.Gamma (1 - α) := by
      rw [← hsimp]; exact hbd'
    rw [Phi]
    calc Real.Gamma (1 - α) * F (q/h) / f (1/h)
        = Real.Gamma (1 - α) * (F (q/h) / f (1/h)) := by ring
      _ ≤ Real.Gamma (1 - α) * (profileBound α q / Real.Gamma (1 - α)) :=
          mul_le_mul_of_nonneg_left hb' hΓ.le
      _ = profileBound α q := by field_simp

/-- **Compactness.**  For any sequence `hseq ↓ 0` there are a subsequence and limit values at the
positive rationals, bounded by `profileBound`. -/
theorem exists_rational_limit
    {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hanti : Antitone F) (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h)) (𝓝[>] 0) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0)) :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ q : {q : ℚ // 0 < q}, 0 ≤ L q ∧ L q ≤ profileBound α (q:ℝ)) ∧
      (∀ q : {q : ℚ // 0 < q},
        Tendsto (fun k => Phi α F f (hseq (ns k)) (q:ℝ)) atTop (𝓝 (L q))) := by
  classical
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Filter.Eventually.of_forall hpos⟩
  -- eventual bounds at each rational
  have hPB : ∀ q : {q : ℚ // 0 < q}, ∀ᶠ n in atTop,
      0 ≤ Phi α F f (hseq n) (q:ℝ) ∧ Phi α F f (hseq n) (q:ℝ) ≤ profileBound α (q:ℝ) :=
    fun q => hseq_mem.eventually
      (eventually_profile_bound hFmeas hF0 hanti hfmeas hrv hmain hα1 (by exact_mod_cast q.2))
  -- the clamped family
  set G : ℕ → (Π q : {q : ℚ // 0 < q}, Set.Icc (0:ℝ) (profileBound α (q:ℝ))) :=
    fun n q => ⟨min (max (Phi α F f (hseq n) (q:ℝ)) 0) (profileBound α (q:ℝ)),
      le_min (le_max_right _ _) (profileBound_nonneg hα1 (by exact_mod_cast q.2)),
      min_le_right _ _⟩ with hG
  obtain ⟨L, ns, hns, hL⟩ := CompactSpace.tendsto_subseq G
  -- convergence of the clamped values
  have hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq (ns k)) (q:ℝ)) atTop (𝓝 ((L q).val)) := by
    intro q
    have h1 : Tendsto (fun k => G (ns k) q) atTop (𝓝 (L q)) := tendsto_pi_nhds.1 hL q
    have h2 : Tendsto (fun k => (G (ns k) q).val) atTop (𝓝 (L q).val) :=
      (continuous_subtype_val.tendsto (L q)).comp h1
    refine h2.congr' ?_
    have h3 : ∀ᶠ k in atTop, (G (ns k) q).val = Phi α F f (hseq (ns k)) (q:ℝ) := by
      filter_upwards [hns.tendsto_atTop.eventually (hPB q)] with k hk
      have h4 : min (max (Phi α F f (hseq (ns k)) (q:ℝ)) 0) (profileBound α (q:ℝ))
          = Phi α F f (hseq (ns k)) (q:ℝ) := by
        rw [min_eq_left (max_le hk.2 (profileBound_nonneg hα1 (by exact_mod_cast q.2))),
          max_eq_left hk.1]
      show min (max (Phi α F f (hseq (ns k)) (q:ℝ)) 0) (profileBound α (q:ℝ)) = _
      exact h4
    filter_upwards [h3] with k hk
    exact hk
  exact ⟨fun q => (L q).val, ns, hns, fun q => (L q).property, hconv⟩

/-- The limit values `L` at the positive rationals are antitone. -/
theorem antitone_of_rational_limit
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hanti : ∀ n, Antitone (fun u : ℝ => Phi α F f (hseq n) u))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q))) :
    ∀ q q' : {q : ℚ // 0 < q}, (q:ℝ) ≤ (q':ℝ) → L q' ≤ L q := by
  intro q q' hqq
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hlt : ∀ᶠ k in atTop, Phi α F f (hseq k) (q:ℝ) < L q + ε :=
    (hconv q).eventually (eventually_lt_nhds (by linarith))
  have hle : ∀ᶠ k in atTop, Phi α F f (hseq k) (q':ℝ) ≤ Phi α F f (hseq k) (q:ℝ) :=
    Filter.Eventually.of_forall (fun k => hanti k hqq)
  refine le_of_tendsto (hconv q') ((hle.and hlt).mono (fun k hk => le_of_lt (lt_of_le_of_lt hk.1 hk.2)))

/-- `profileBound` is antitone on `(0,∞)`. -/
theorem profileBound_antitone {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) : profileBound α v ≤ profileBound α u := by
  refine mul_le_mul_of_nonneg_left ?_ (Real.Gamma_pos_of_pos (by linarith)).le
  have h1 : (0:ℝ) < (3/2) * Real.exp 1 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h1.le
  rw [Real.rpow_neg (le_of_lt (lt_of_lt_of_le hu huv)), Real.rpow_neg hu.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_le_rpow hu.le huv hα0)

/-- **The limit profile** `ψ u = sup {L q : u < q}` attached to rational limit values `L`. -/
noncomputable def limitProfile (L : {q : ℚ // 0 < q} → ℝ) (u : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q:ℝ) ∧ L q = x}

theorem limitProfile_bddAbove {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) {u : ℝ} (hu : 0 < u) :
    BddAbove {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q:ℝ) ∧ L q = x} := by
  refine ⟨profileBound α u, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  exact le_trans (hLb q) (profileBound_antitone hα0 hα1 hu (le_of_lt hq))

theorem limitProfile_nonempty {L : {q : ℚ // 0 < q} → ℝ} {u : ℝ} (hu : 0 < u) :
    {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q:ℝ) ∧ L q = x}.Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_gt u
  have hq0 : (0:ℚ) < q := by exact_mod_cast (lt_trans hu hq : (0:ℝ) < (q:ℝ))
  exact ⟨L ⟨q, hq0⟩, ⟨⟨q, hq0⟩, hq, rfl⟩⟩

theorem le_limitProfile {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) {u : ℝ} (hu : 0 < u)
    {q : {q : ℚ // 0 < q}} (hq : u < (q:ℝ)) : L q ≤ limitProfile L u :=
  le_csSup (limitProfile_bddAbove hα0 hα1 hLb hu) ⟨q, hq, rfl⟩

theorem limitProfile_le_bound {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) {u : ℝ} (hu : 0 < u) :
    limitProfile L u ≤ profileBound α u :=
  csSup_le (limitProfile_nonempty hu) (by
    rintro x ⟨q, hq, rfl⟩
    exact le_trans (hLb q) (profileBound_antitone hα0 hα1 hu (le_of_lt hq)))

theorem limitProfile_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) (hLnn : ∀ q, 0 ≤ L q)
    {u : ℝ} (hu : 0 < u) : 0 ≤ limitProfile L u := by
  obtain ⟨x, hx⟩ := limitProfile_nonempty (L := L) hu
  refine le_trans ?_ (le_csSup (limitProfile_bddAbove hα0 hα1 hLb hu) hx)
  rcases hx with ⟨q, -, rfl⟩
  exact hLnn q

theorem limitProfile_antitone {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) :
    ∀ u v : ℝ, 0 < u → u ≤ v → limitProfile L v ≤ limitProfile L u := by
  intro u v hu huv
  refine csSup_le (limitProfile_nonempty (lt_of_lt_of_le hu huv)) ?_
  rintro x ⟨q, hq, rfl⟩
  exact le_limitProfile hα0 hα1 hLb hu (lt_of_le_of_lt huv hq)

theorem limitProfile_spec {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : {q : ℚ // 0 < q} → ℝ}
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) {u : ℝ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : {q : ℚ // 0 < q}, u < (q:ℝ) ∧ limitProfile L u - ε < L q := by
  by_contra hcon
  push Not at hcon
  have hle : limitProfile L u ≤ limitProfile L u - ε := by
    refine csSup_le (limitProfile_nonempty hu) ?_
    rintro x ⟨q, hq, rfl⟩
    exact hcon q hq
  linarith

/-- The limit profile is antitone after extending by a constant below any `c > 0`. -/
theorem antitone_limitProfile_ext {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {L : {q : ℚ // 0 < q} → ℝ} (hLb : ∀ q, L q ≤ profileBound α (q:ℝ)) {c : ℝ} (hc : 0 < c) :
    Antitone (fun u : ℝ => if u ≤ c then limitProfile L c else limitProfile L u) := by
  intro u v huv
  change (if v ≤ c then limitProfile L c else limitProfile L v)
    ≤ (if u ≤ c then limitProfile L c else limitProfile L u)
  by_cases hv : v ≤ c
  · rw [ite_eq_left hv, ite_eq_left (le_trans huv hv)]
  · rw [ite_eq_right hv]
    have hcv : c < v := lt_of_not_ge hv
    by_cases hu : u ≤ c
    · rw [ite_eq_left hu]
      exact limitProfile_antitone hα0 hα1 hLb c v hc (le_of_lt hcv)
    · rw [ite_eq_right hu]
      exact limitProfile_antitone hα0 hα1 hLb u v (lt_trans hc (lt_of_not_ge hu)) huv

/-- **Almost-everywhere convergence to the limit profile** on `(c, ∞)`. -/
theorem ae_tendsto_limitProfile_ge
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hanti : ∀ k, Antitone (fun u : ℝ => Phi α F f (hseq k) u))
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q)))
    {c : ℝ} (hc : 0 < c) :
    ∀ᵐ u ∂(volume.restrict (Ioi c)),
      Tendsto (fun k => Phi α F f (hseq k) u) atTop (𝓝 (limitProfile L u)) := by
  classical
  set Λe : ℝ → ℝ := fun u => if u ≤ c then limitProfile L c else limitProfile L u with hΛe
  have hΛe_anti : Antitone Λe := antitone_limitProfile_ext hα0 hα1 hLb hc
  have hΛe_count : {u : ℝ | ¬ ContinuousAt Λe u}.Countable := hΛe_anti.countable_not_continuousAt
  have hΛe_null : volume {u : ℝ | ¬ ContinuousAt Λe u} = 0 := hΛe_count.measure_zero volume
  -- the eventual convergence at a continuity point `u > c`
  have key : ∀ u : ℝ, c < u → ContinuousAt Λe u →
      Tendsto (fun k => Phi α F f (hseq k) u) atTop (𝓝 (limitProfile L u)) := by
    intro u hu hcont
    have hΛu : Λe u = limitProfile L u := by
      rw [hΛe]; exact ite_eq_right (not_le_of_gt hu)
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hε2 : (0:ℝ) < ε/2 := by linarith
    obtain ⟨q, hq, hqL⟩ := limitProfile_spec hα0 hα1 hLb (lt_trans hc hu) hε2
    have hlow : ∀ᶠ k in atTop, limitProfile L u - ε/2 ≤ Phi α F f (hseq k) u := by
      have h1 : ∀ᶠ k in atTop, limitProfile L u - ε/2 ≤ Phi α F f (hseq k) (q:ℝ) :=
        (hconv q).eventually (eventually_ge_nhds (by linarith [hqL]))
      filter_upwards [h1] with k hk
      have h2 : Phi α F f (hseq k) (q:ℝ) ≤ Phi α F f (hseq k) u := hanti k (le_of_lt hq)
      linarith only [hk, h2]
    have hup : ∀ᶠ k in atTop, Phi α F f (hseq k) u ≤ limitProfile L u + ε/2 := by
      have hltmem : ∀ᶠ v in 𝓝[<] u, c < v :=
        (eventually_gt_nhds hu).filter_mono nhdsWithin_le_nhds
      have hev : ∀ᶠ v in 𝓝[<] u, Λe v < Λe u + ε/2 :=
        (hcont.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε2))).filter_mono
          nhdsWithin_le_nhds
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := ((hev.and self_mem_nhdsWithin).and hltmem).exists
      have hvpos : c < v := hv3
      obtain ⟨r, hrv, hru⟩ := exists_rat_btwn hv2
      have hr0 : (0:ℚ) < r := by
        have : (0:ℝ) < (r:ℝ) := lt_trans hc (lt_trans hvpos hrv)
        exact_mod_cast this
      have hΛev : Λe v = limitProfile L v := by
        show (if v ≤ c then limitProfile L c else limitProfile L v) = limitProfile L v
        exact ite_eq_right (not_le_of_gt hvpos)
      have hLr : L ⟨r, hr0⟩ ≤ Λe v := by
        rw [hΛev]
        exact le_limitProfile hα0 hα1 hLb (lt_trans hc hvpos) hrv
      have hLr2 : L ⟨r, hr0⟩ < Λe u + ε/2 := lt_of_le_of_lt hLr hv1
      have h1 : ∀ᶠ k in atTop, Phi α F f (hseq k) ((⟨r, hr0⟩ : {q : ℚ // 0 < q}) : ℝ)
          ≤ Λe u + ε/2 :=
        (hconv ⟨r, hr0⟩).eventually (eventually_le_nhds (by linarith [hLr2]))
      filter_upwards [h1] with k hk
      have h2 : Phi α F f (hseq k) u ≤ Phi α F f (hseq k) ((⟨r, hr0⟩ : {q : ℚ // 0 < q}) : ℝ) :=
        hanti k (le_of_lt hru)
      linarith only [hk, h2, hΛu]
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 hlow
    obtain ⟨N2, hN2⟩ := eventually_atTop.1 hup
    refine ⟨max N1 N2, fun k hk => ?_⟩
    have h1 := hN1 k (le_trans (le_max_left _ _) hk)
    have h2 := hN2 k (le_trans (le_max_right _ _) hk)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [h1, h2, hε2, hε]
  -- a.e. continuity of the extension on `(c,∞)`
  have hmeas : MeasurableSet {u : ℝ | ¬ ContinuousAt Λe u} := hΛe_count.measurableSet
  have hcont_ae : ∀ᵐ u ∂(volume.restrict (Ioi c)), ContinuousAt Λe u := by
    rw [MeasureTheory.ae_iff, Measure.restrict_apply hmeas]
    exact measure_mono_null Set.inter_subset_left hΛe_null
  filter_upwards [hcont_ae, ae_restrict_mem measurableSet_Ioi] with u hcont hu
  exact key u hu hcont

/-- The full a.e. convergence on `(0,∞)`, obtained by covering `(0,∞)` by the sets `(1/(m+1),∞)`. -/
theorem ae_tendsto_limitProfile
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hanti : ∀ k, Antitone (fun u : ℝ => Phi α F f (hseq k) u))
    (hLb : ∀ q, L q ≤ profileBound α (q:ℝ))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Phi α F f (hseq k) (q:ℝ)) atTop (𝓝 (L q))) :
    ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))),
      Tendsto (fun k => Phi α F f (hseq k) u) atTop (𝓝 (limitProfile L u)) := by
  classical
  set P : ℝ → Prop := fun u => Tendsto (fun k => Phi α F f (hseq k) u) atTop (𝓝 (limitProfile L u))
    with hP
  have hbad : volume {u : ℝ | 0 < u ∧ ¬ P u} = 0 := by
    have hsub : {u : ℝ | 0 < u ∧ ¬ P u} ⊆
        ⋃ m : ℕ, {u : ℝ | 1/((m:ℝ)+1) < u ∧ ¬ P u} := by
      intro u hu
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hu.1
      exact Set.mem_iUnion.2 ⟨m, hm, hu.2⟩
    refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
    have h := ae_tendsto_limitProfile_ge hα0 hα1 hanti hLb hconv
      (c := 1/((m:ℝ)+1)) (by positivity)
    have h' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (1/((m:ℝ)+1)) → P u :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).1 h
    rw [MeasureTheory.ae_iff] at h'
    convert h' using 2 with u
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, not_imp, not_lt]
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hbad
  intro u hu
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi, not_imp, not_lt] at hu ⊢
  exact hu

end PercLib.CriticalLRP.Analysis
