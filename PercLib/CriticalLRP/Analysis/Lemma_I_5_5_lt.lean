/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.5.5 in the lower-order case `b < a`

The source-driven homogeneous weight makes the driving term integrable at
infinity: its power index is strictly less than `-1`.  Consequently `f/w`
has a finite positive limit, and regular-variation algebra recovers `f` from
`w * (f/w)`.  The reported index is negative for `h/f`, which gives `h/f → 0`.

The normalized derivative is then proved from the shared-error ODE as
`(1-δ) * (af + h)/(af)` and tends to `1`.  Positive initial weight and the
nonnegative tail identify the positive limit.  This file intentionally contains
only the `b < a` case; the critical `a = b` case and Lemma I.5.6 are separate.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_22

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

/-- A function with a finite positive limit is slowly varying. -/
theorem regularlyVarying_of_tendsto_pos {q : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hl : Tendsto q atTop (𝓝 L)) : RegularlyVaryingAtTop q 0 := by
  constructor
  · exact hl.eventually (eventually_gt_nhds hL) |>.mono (fun x hx => hx.ne')
  · intro l hl'
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hl').mpr tendsto_id
    have ht : Tendsto (fun x => q (l * x) / q x) atTop (𝓝 (L / L)) :=
      (hl.comp hscale).div hl hL.ne'
    simpa [div_self hL.ne'] using ht

/-- Eventual equality preserves the index of regular variation. -/
theorem RegularlyVaryingAtTop.congr_of_eventuallyEq {f g : ℝ → ℝ} {a : ℝ}
    (hf : RegularlyVaryingAtTop f a) (hfg : f =ᶠ[atTop] g) :
    RegularlyVaryingAtTop g a := by
  constructor
  · filter_upwards [hf.1, hfg] with x hx heq
    rw [← heq]
    exact hx
  · intro l hl
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hl).mpr tendsto_id
    apply (hf.2 l hl).congr'
    filter_upwards [hfg, hscale.eventually hfg] with x hx hlx
    rw [hx, hlx]

/-- The `b < a` form of Lemma I.5.5: the inhomogeneity is negligible. -/
theorem lemma_I_5_5_of_lt_measurable {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : b < a)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hfm : Measurable f)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f a ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto D ha hpos hfpos hderiv hasym
  let w := powerExpWeight r₀ a δ
  let v : ℝ → ℝ := fun s => h s / w s
  let g : ℝ → ℝ := fun s => v s / s
  let T : ℝ → ℝ := (Ioi r₀).indicator g
  let q : ℝ → ℝ := fun r => f r * (w r)⁻¹
  have hr₀pos : 0 < r₀ := hr₀
  have hwrv : RegularlyVaryingAtTop w a := regularlyVarying_powerExpWeight ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_powerExpWeight hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := by
    intro s hs
    dsimp [w, powerExpWeight]
    exact mul_pos (Real.rpow_pos_of_pos hs a) (Real.exp_pos _)
  have hvr : RegularlyVaryingAtTop v (b - a) := by
    have hh := D.rv.mul hwrv.inv
    have hidx : b + -a = b - a := by ring
    rw [hidx] at hh
    simpa [v, div_eq_mul_inv] using hh
  have hvm : Measurable v := D.measurable_f.div hwm
  have hgrv : RegularlyVaryingAtTop g (b - a - 1) := by
    have hh := hvr.mul (regularlyVaryingAtTop_rpow 1).inv
    have hidx : b - a + -1 = b - a - 1 := by ring
    rw [hidx] at hh
    simpa [g, v, div_eq_mul_inv, Real.rpow_one] using hh
  have hgm : Measurable g := hvm.div measurable_id
  have hgp : ∀ᶠ s in atTop, 0 < g s := by
    filter_upwards [eventually_ge_atTop r₀] with s hs
    exact div_pos (div_pos (hpos s (lt_of_lt_of_le hr₀ hs)) (hwpos s (lt_of_lt_of_le hr₀ hs))) (lt_of_lt_of_le hr₀ hs)
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    have he : ContinuousAt (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) s := by
      apply Real.continuous_exp.continuousAt.comp
      exact ((continuous_errorIntegral hr₀ hδm hδ1).continuousAt.const_mul a).neg
    change ContinuousWithinAt (fun r => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) (Ici r₀) s
    have hfun : (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) =
        (fun r : ℝ => r ^ a) * (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) := by rfl
    rw [hfun]
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul he).continuousWithinAt
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s (lt_of_lt_of_le hr₀ (le_trans hx hs.1)))]
      exact hC s (le_trans hrD hx |>.trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [g, v, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hIc.mul_continuousOn hcont isCompact_Icc
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hgint
  have hTrv : RegularlyVaryingAtTop T (b - a - 1) := by
    simpa [T] using regularlyVarying_indicator_Ioi hgrv
  have hTm : Measurable T := hgm.indicator measurableSet_Ioi
  have hbase : IntegrableOn T (Ioi r₀) :=
    integrableOn_Ioi_of_regularlyVarying (by linarith : b - a - 1 < -1) hTm hTloc hTrv r₀ hr₀
  have hdom : IntegrableOn (fun s => 2 * ‖T s‖) (Ioi r₀) := hbase.norm.const_mul 2
  have hbound : ∀ x, r₀ < x → ‖(1 - δ x) * g x‖ ≤ 2 * ‖T x‖ := by
    intro x hx
    have hd := hδ1 x hx.le
    have hfac : |1 - δ x| ≤ 2 := by
      calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
        _ ≤ 2 := by rw [abs_one]; linarith
    rw [show T x = g x by simp [T, hx]]
    calc ‖(1 - δ x) * g x‖ = |1 - δ x| * ‖g x‖ := norm_mul _ _
      _ ≤ 2 * ‖g x‖ := mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
  have hweighted : IntegrableOn (fun s => (1 - δ s) * g s) (Ioi r₀) := by
    apply Integrable.mono' hdom ((measurable_const.sub hδm).mul hgm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg (norm_nonneg _)] using hbound x hx
  have hlimint : Tendsto (fun r => ∫ s in r₀..r, (1 - δ s) * g s) atTop
      (𝓝 (∫ s in Ioi r₀, (1 - δ s) * g s)) :=
    intervalIntegral_tendsto_integral_Ioi r₀ hweighted tendsto_id
  have hqinc : ∀ᶠ R in atTop, q R - q r₀ = ∫ s in r₀..R, (1 - δ s) * g s := by
    filter_upwards [eventually_ge_atTop r₀] with R hR
    simpa [q, g, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      normalized_increment_of_driving_ode (D := D) (a := a) (r₀ := r₀) (R := R)
        ha hr₀ hR hrD (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx)) hδm hδ1 hode
  have hlimq : Tendsto q atTop (𝓝 (q r₀ + ∫ s in Ioi r₀, (1 - δ s) * g s)) := by
    have hdiff : Tendsto (fun r => q r - q r₀) atTop (𝓝 (∫ s in Ioi r₀, (1 - δ s) * g s)) :=
      hlimint.congr' (by filter_upwards [hqinc] with r hr; exact hr.symm)
    simpa using hdiff.const_add (q r₀)
  have hq0 : 0 < q r₀ := by
    dsimp [q]
    exact mul_pos (hfpos r₀ hr₀) (inv_pos.mpr (hwpos r₀ hr₀))
  have hgpos : ∀ s, 0 < s → 0 < g s := by
    intro s hs
    exact div_pos (div_pos (hpos s hs) (hwpos s hs)) hs
  have htail : 0 ≤ ∫ s in Ioi r₀, (1 - δ s) * g s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : r₀ < s := hs
    have hd := (abs_le.1 (hδ1 s hs0.le)).2
    have hs_pos : 0 < s := lt_of_lt_of_le hr₀ (le_of_lt hs)
    exact mul_nonneg (sub_nonneg.mpr hd) (hgpos s hs_pos).le
  have hqpos : 0 < q r₀ + ∫ s in Ioi r₀, (1 - δ s) * g s :=
    add_pos_of_pos_of_nonneg hq0 htail
  have hqrv : RegularlyVaryingAtTop q 0 := regularlyVarying_of_tendsto_pos hqpos hlimq
  have hwprod : RegularlyVaryingAtTop (fun r => w r * q r) a := by
    simpa using hwrv.mul hqrv
  have hfrv : RegularlyVaryingAtTop f a := hwprod.congr_of_eventuallyEq (by
    filter_upwards [hwrv.1] with r hr
    dsimp [q]
    field_simp [hr])
  have hf0 : Tendsto (fun r => h r / f r) atTop (𝓝 0) := by
    have hratio : RegularlyVaryingAtTop (fun r => h r / f r) (b - a) := by
      have hd := D.rv.mul hfrv.inv
      have hi : b + -a = b - a := by ring
      rw [hi] at hd
      simpa [div_eq_mul_inv] using hd
    exact (isLogErrorFunction_of_regularlyVarying (by linarith : b - a < 0)
      (D.measurable_f.div hfm) hratio).2
  refine ⟨hfrv, hf0, ?_⟩
  have htotal : Tendsto (fun r => (a * f r + h r) / (a * f r)) atTop (𝓝 1) := by
    have hz : Tendsto (fun r => 1 + a⁻¹ * (h r / f r)) atTop (𝓝 1) := by
      simpa using (hf0.const_mul a⁻¹).const_add 1
    apply hz.congr'
    filter_upwards [hfrv.1] with r hr
    field_simp [ha.ne', hr]
  have hterm : Tendsto (fun r => (1 - δ r) * ((a * f r + h r) / (a * f r))) atTop (𝓝 1) := by
    have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub hδ0
    have hm := hd.mul htotal
    simpa using hm
  apply hterm.congr'
  filter_upwards [eventually_ge_atTop r₀, hfrv.1] with r hr hfr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  rw [hode r hr]
  field_simp [ha.ne', hfr, hrpos.ne']


/-- **Lemma I.5.5 in the case `b < a`**, without an additional global
measurability premise on `f`. -/
theorem lemma_I_5_5_of_lt {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : b < a)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f a ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hf0m : Measurable f₀ := measurable_ite_pos_of_hasDerivAt hderiv
  have hf0d : ∀ x, 0 < x → HasDerivAt f₀ (f' x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  have hf0pos : ∀ x, 0 < x → 0 < f₀ x := by
    intro x hx
    simpa [f₀, hx] using hfpos x hx
  have hf₀eq : ∀ x, 0 < x → f₀ x = f x := by intro x hx; simp [f₀, hx]
  have hasym0 : Tendsto (fun r => f' r / ((a * f₀ r + h r) / r)) atTop (𝓝 1) := by
    apply hasym.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hf₀eq x hx]
  obtain ⟨hfrv, hf0, hder⟩ := lemma_I_5_5_of_lt_measurable D ha hab hpos hf0pos hf0m hf0d hasym0
  refine ⟨hfrv.congr_of_eventuallyEq ?_, hf0.congr' ?_, hder.congr' ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [f₀, hx]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [f₀, hx]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hf₀eq x hx]

#print axioms PercLib.CriticalLRP.Analysis.regularlyVarying_of_tendsto_pos
#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.congr_of_eventuallyEq
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_5_of_lt_measurable
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_5_of_lt

end PercLib.CriticalLRP.Analysis
