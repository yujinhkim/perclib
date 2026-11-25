/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Logarithmic integrability under power and constant rescalings

Lemma I.4.19 of Hutchcroft, *Critical long-range percolation I*: if `h` is
logarithmically integrable then so is `r ↦ h (C r^c)` for `c,C>0`.
The proof uses the measured image-substitution theorem, with no monotonicity
assumption on `h` and no continuity upgrade.
-/
module

public import PercLib.CriticalLRP.Analysis.RegularVariation

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

/-- **Lemma I.4.19.** Power-rescaling preserves logarithmic integrability. -/
theorem logarithmicallyIntegrable_comp_rpow_const_mul (h : ℝ → ℝ)
    (hlog : LogarithmicallyIntegrable h) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    LogarithmicallyIntegrable (fun r => h (C * r ^ c)) := by
  obtain ⟨hmeas, r₀, hr₀, hint⟩ := hlog
  have hmeas' : Measurable (fun r => h (C * r ^ c)) := by fun_prop
  refine ⟨hmeas', ?_⟩
  let R : ℝ := max (max r₀ 1) ((r₀ / C) ^ (1 / c))
  have hR0 : 0 < R := by dsimp [R]; positivity
  let F : ℝ → ℝ := fun r => C * r ^ c
  let F' : ℝ → ℝ := fun r => C * c * r ^ (c - 1)
  have hFRpos : 0 < F R := by
    exact mul_pos hC (Real.rpow_pos_of_pos hR0 _)
  have hmono : StrictMonoOn F (Ici R) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le hR0 hx
    have hrp := Real.rpow_lt_rpow hxpos.le hxy hc
    exact mul_lt_mul_of_pos_left hrp hC
  have hderiv : ∀ x ∈ Ioi R, HasDerivWithinAt F (F' x) (Ioi R) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hR0 (le_of_lt hx)
    have hd : HasDerivAt (fun r : ℝ => C * r ^ c) (C * (c * x ^ (c - 1))) x :=
      (Real.hasDerivAt_rpow_const (x := x) (p := c) (Or.inl hxpos.ne')).const_mul C
    simpa [F, F', mul_assoc] using hd.hasDerivWithinAt
  have himage : F '' Ioi R = Ioi (F R) := by
    have hco : ContinuousOn F (Ici R) := by fun_prop
    have hft : Tendsto F atTop atTop := by
      exact (tendsto_rpow_atTop hc).const_mul_atTop hC
    exact hco.image_Ioi_of_strictMonoOn hmono hft
  have hint_old : IntegrableOn (fun s => |h s| / s) (Ioi (F R)) := by
    apply hint.mono_set
    intro x hx
    have hroot : F ((r₀ / C) ^ (1 / c)) = r₀ := by
      dsimp [F]
      rw [← Real.rpow_mul (div_nonneg hr₀.le hC.le), one_div_mul_cancel hc.ne',
        Real.rpow_one, mul_div_cancel₀ r₀ hC.ne']
    rw [← hroot]
    change F ((r₀ / C) ^ (1 / c)) < x
    apply lt_of_le_of_lt ?_ hx
    have hrootle : (r₀ / C) ^ (1 / c) ≤ R := le_max_right _ _
    have hbase : 0 ≤ (r₀ / C) ^ (1 / c) :=
      Real.rpow_nonneg (div_nonneg hr₀.le hC.le) (y := 1 / c)
    have hpowle : ((r₀ / C) ^ (1 / c)) ^ c ≤ R ^ c :=
      Real.rpow_le_rpow hbase hrootle hc.le
    exact mul_le_mul_of_nonneg_left hpowle hC.le
  have hsource : IntegrableOn (fun s => |h s| / s) (F '' Ioi R) := by
    rw [himage]
    exact hint_old
  have hconverted : IntegrableOn
      (fun x => |F' x| • ((fun s => |h s| / s) (F x))) (Ioi R) := by
    have hinj : InjOn F (Ioi R) := hmono.injOn.mono Ioi_subset_Ici_self
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hderiv hinj (fun s => |h s| / s)).mp hsource
  have hmul : IntegrableOn (fun x => c * (|h (C * x ^ c)| / x)) (Ioi R) := by
    apply (integrableOn_congr_fun (s := Ioi R) ?_ measurableSet_Ioi).mp hconverted
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hR0 (le_of_lt hx)
    have hpow : 0 < x ^ c := Real.rpow_pos_of_pos hxpos c
    have hf'pos : 0 < F' x := by
      dsimp [F']
      exact mul_pos (mul_pos hC hc) (Real.rpow_pos_of_pos hxpos _)
    change |F' x| * (|h (F x)| / (F x)) = c * (|h (C * x ^ c)| / x)
    rw [abs_of_pos hf'pos]
    dsimp [F, F']
    rw [show C * c * x ^ (c - 1) * (|h (C * x ^ c)| / (C * x ^ c)) =
        c * (|h (C * x ^ c)| / x) by
      have hCne : C ≠ 0 := hC.ne'
      have hxne : x ≠ 0 := hxpos.ne'
      have hpne : x ^ c ≠ 0 := hpow.ne'
      rw [Real.rpow_sub hxpos, Real.rpow_one]
      field_simp]
  refine ⟨R, hR0, ?_⟩
  have hRle : 0 ≤ c := hc.le
  have hone : IntegrableOn (fun x => c⁻¹ * (c * (|h (C * x ^ c)| / x))) (Ioi R) :=
    hmul.const_mul c⁻¹
  have htarget : ∀ x ∈ Ioi R,
      c⁻¹ * (c * (|h (C * x ^ c)| / x)) = |h (C * x ^ c)| / x := by
    intro x hx
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact (integrableOn_congr_fun (s := Ioi R) htarget measurableSet_Ioi).mp hone

/-- The integrating factor `exp H` has regular variation index `a`
whenever `H' = a (1-h) / r` with `h → 0`. -/
theorem regularlyVarying_exp_of_hasDerivAt_log {a r₀ : ℝ} (ha : 0 < a)
    (hr₀ : 0 < r₀) {H h : ℝ → ℝ}
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt H ((1 - h t) * a / t) t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r => Real.exp (H r)) a := by
  refine lemma_I_2_12_rv (f := fun r => Real.exp (H r))
    (f' := fun r => a * (1 - h r) * Real.exp (H r) / r) ha hr₀ ?_ ?_ ?_ hmeas h0
  · intro t ht
    have hd : HasDerivAt H ((1 - h t) * a / t) t := hderiv t ht
    convert hd.exp using 1
    have ht0 : 0 < t := lt_of_lt_of_le hr₀ ht
    field_simp
  · intro t ht
    exact Real.exp_pos _
  · intro t ht
    rfl


/-- **Regular variation of the exponential integrating weight.**
The additional interval-integrability input is on the whole positive tail,
not merely on intervals near infinity. -/
theorem regularlyVarying_exp_integral_of_tendsto_zero
    {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) {δ : ℝ → ℝ}
    (hδmeas : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => (1 - δ s) * a / s) volume x y) :
    RegularlyVaryingAtTop
      (fun r => Real.exp (∫ s in r₀..r, (1 - δ s) * a / s)) a := by
  constructor
  · filter_upwards with x
    exact (Real.exp_pos _).ne'
  intro l hl
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, r₀ ≤ R ∧ ∀ s, R ≤ s → |δ s| ≤ 1 := by
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hδ0 1 one_pos
    refine ⟨max r₀ R, le_max_left _ _, ?_⟩
    intro s hs
    have h := hR s (le_trans (le_max_right _ _) hs)
    rw [Real.dist_eq, sub_zero] at h
    linarith
  have hdiv : ∀ x y : ℝ, R ≤ x → x ≤ y →
      IntervalIntegrable (fun s => δ s * a / s) volume x y := by
    intro x y hx hxy
    refine intervalIntegrable_div_of_bounded (g := fun s => δ s * a) (C := |a|)
      (lt_of_lt_of_le hr₀ (le_trans hR0 hx)) hxy (by fun_prop) ?_
    intro s hs
    have hb := mul_le_mul_of_nonneg_right (hR s (le_trans hx hs)) ha.le
    simpa only [abs_mul, abs_of_pos ha, one_mul] using hb
  have hdiv' : ∀ x y : ℝ, R ≤ x → R ≤ y →
      IntervalIntegrable (fun s => δ s * a / s) volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hdiv x y hx hxy
    · exact (hdiv y x hy hyx).symm
  have hbase : ∀ x y : ℝ, 0 < x → x ≤ y →
      IntervalIntegrable (fun s => a / s) volume x y := by
    intro x y hx hxy
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxy]
    intro s hs
    have hs0 : 0 < s := hx.trans_le hs.1
    exact (ContinuousAt.div continuousAt_const continuousAt_id
      (ne_of_gt hs0)).continuousWithinAt
  have hbase' : ∀ x y : ℝ, 0 < x → 0 < y →
      IntervalIntegrable (fun s => a / s) volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hbase x y hx hxy
    · exact (hbase y x hy hyx).symm
  have hint' : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y →
      IntervalIntegrable (fun s => (1 - δ s) * a / s) volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hint x y hx hxy
    · exact (hint y x hy hyx).symm
  have hcosc : ∀ x : ℝ, 0 < x →
      (∫ s in x..l * x, δ s * a / s) = a * ∫ s in x..l * x, δ s / s := by
    intro x hx
    calc (∫ s in x..l * x, δ s * a / s)
        = ∫ s in x..l * x, a * (δ s / s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          ring
      _ = a * ∫ s in x..l * x, δ s / s := intervalIntegral.integral_const_mul _ _
  have hToLog : ∀ x : ℝ, 0 < x →
      (∫ s in x..l * x, a / s) = a * Real.log l := by
    intro x hx
    rw [show (fun s => a / s) = (fun s => a * (1 / s)) by
      funext s; rw [mul_one_div], intervalIntegral.integral_const_mul]
    rw [integral_one_div_of_pos hx (mul_pos hl hx)]
    rw [show l * x / x = l by field_simp]
  have hsplit : ∀ x : ℝ, 0 < x → R ≤ x → R ≤ l * x →
      (∫ s in x..l * x, (1 - δ s) * a / s)
        = a * Real.log l - a * (∫ s in x..l * x, δ s / s) := by
    intro x hx hxR hxlR
    have hcog : (∫ s in x..l * x, (1 - δ s) * a / s) =
        ∫ s in x..l * x, a / s - δ s * a / s := by
      apply intervalIntegral.integral_congr
      intro s hs
      ring
    rw [hcog]
    rw [intervalIntegral.integral_sub (hbase' x (l * x) hx (mul_pos hl hx))
      (hdiv' x (l * x) hxR hxlR)]
    rw [hToLog x hx, hcosc x hx]
  have hosc : Tendsto (fun x : ℝ => ∫ s in x..l * x, δ s / s) atTop (𝓝 0) :=
    tendsto_intervalIntegral_div_of_tendsto_zero hδmeas hδ0 l hl
  have hmain : Tendsto (fun x : ℝ => (l : ℝ) ^ a * Real.exp (-(a * ∫ s in x..l * x, δ s / s)))
      atTop (𝓝 (l ^ a)) := by
    have hzero : Tendsto (fun x : ℝ => -(a * ∫ s in x..l * x, δ s / s)) atTop (𝓝 0) := by
      simpa using (hosc.const_mul a).neg
    have hexp : Tendsto (fun x : ℝ => Real.exp (-(a * ∫ s in x..l * x, δ s / s))) atTop
        (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using
        (Real.continuous_exp.tendsto 0).comp hzero
    have hmul := hexp.const_mul ((l : ℝ) ^ a)
    simpa using hmul
  have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hl).mpr tendsto_id
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop r₀,
    hscale.eventually (eventually_ge_atTop R),
    hscale.eventually (eventually_ge_atTop r₀)] with x hxR hxr₀ hxlR hxlr₀
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr₀
  have hratio : Real.exp (∫ s in r₀..l * x, (1 - δ s) * a / s) /
        Real.exp (∫ s in r₀..x, (1 - δ s) * a / s)
      = Real.exp (∫ s in x..l * x, (1 - δ s) * a / s) := by
    rw [← Real.exp_sub, ← intervalIntegral.integral_add_adjacent_intervals
      (hint' r₀ x le_rfl hxr₀) (hint' x (l * x) hxr₀ hxlr₀)]
    congr 1
    ring
  have hpow : (l : ℝ) ^ a = Real.exp (a * Real.log l) := by
    rw [Real.rpow_def_of_pos hl]
    ring
  calc (l : ℝ) ^ a * Real.exp (-(a * ∫ s in x..l * x, δ s / s))
      = Real.exp (a * Real.log l) * Real.exp (-(a * ∫ s in x..l * x, δ s / s)) := by
        rw [hpow]
    _ = Real.exp (a * Real.log l - a * ∫ s in x..l * x, δ s / s) := by
        rw [← Real.exp_add, sub_eq_add_neg]
    _ = Real.exp (∫ s in x..l * x, (1 - δ s) * a / s) := by
        rw [hsplit x hxpos hxR hxlR]
    _ = Real.exp (∫ s in r₀..l * x, (1 - δ s) * a / s) /
          Real.exp (∫ s in r₀..x, (1 - δ s) * a / s) := hratio.symm

end PercLib.CriticalLRP.Analysis

#print axioms PercLib.CriticalLRP.Analysis.logarithmicallyIntegrable_comp_rpow_const_mul
