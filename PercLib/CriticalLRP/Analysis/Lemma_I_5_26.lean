/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.5.26 (signed ODE) via the integrating factor `r ↦ r^{-a}`

Source: T. Hutchcroft, *Critical long-range percolation I*, Lemma I.5.26 (p. 83).

The paper proves the signed ODE lemma by adding `λ ∫_{r₀}^r h s/s ds` to `f`,
which requires differentiating the primitive `∫ h s / s ds` at every point —
a step that is only available almost everywhere for a merely measurable,
locally bounded `h`.  This file proves the lemma by a route that avoids the
primitive altogether: multiply the ODE by the integrating factor `r^{-a}`.
Then `q r = f r * r^{-a}` is absolutely continuous on every `[r₀, R]` (only `f`
is differentiated, and `f` is differentiable by hypothesis), with

`q R - q r₀ = ∫_{r₀}^{R} ((a ± o(1)) f + (A ± o(1)) h)/s * s^{-a} ds`
            `= ∫_{r₀}^{R} (A + ε s) (h s * s^{-(a+1)}) ds`

for a single signed error `ε → 0`: the error on `f` is absorbed into the `h`
term because `|f| = O(h)`.  Because `b > a`, the integrand `s ↦ h s * s^{-(a+1)}`
is regularly varying of index `b - a - 1 > -1`, so Karamata's theorem gives

`∫_{r₀}^{R} h s * s^{-(a+1)} ds = (1/(b-a) + o(1)) h R * R^{-a}`,

and the same theorem with multiplier `1 - ε` shows that the error contributes
only `o(h R * R^{-a})`.  Dividing by `h R * R^{-a}` gives `f R / h R → A/(b-a)`.

Main results:

* `increment_integrating_factor` — the exact increment identity (no shift, no
  primitive, no smoothness of `h`; `f` is differentiated on all of `[r₀,R]`);
* `tendsto_div_of_signed_weighted_ode` — the analytic core: an ODE
  `f' = (a f + (A + ε) h)/r` with a single measurable error `ε → 0`, `|ε| ≤ 1`,
  forces `f/h → A/(b-a)`;
* `lemma_I_5_26_two_errors` — the paper's literal two-error form (with
  `|f| = O(h)`, used only to absorb the error on `f`);
* `lemma_I_5_26_signed_ode` — a strictly stronger folded form
  `(r f' - a f)/h → A`, which needs *no* bound `|f| = O(h)` because the
  homogeneous solution grows like `r^a = o(h)` when `b > a`;
* `lemma_I_5_26` — the paper's Lemma I.5.26 from the paper's raw hypotheses
  (`h` measurable, regularly varying of index `b > 0`, eventually positive);
* `lemma_I_5_26_isLittleO` / `lemma_I_5_26_isLittleO'` — the paper's conclusion
  `f = (A/(b-a) ± o(1)) h` as `(f - (A/(b-a)) h) = o(h)`;
* `lemma_I_5_26_example` — non-vacuity: `h r = r^2`, `a = 1`, `b = 2`, `A = 3`,
  `f r = 3 r^2` satisfies the hypotheses and yields `f/h → 3 = A/(b-a)`.

Compile with (from the repository root)

`lake env lean CriticalPercLib.CriticalLRP/Analysis/Lemma_I_5_26.lean`

Axiom audit at the end of the file: only `propext`, `Classical.choice`,
`Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-! ### The exact increment identity -/

/-- **Exact increment identity for the signed ODE, weighted by `r^{-a}`.**

If `f` is differentiable on `[r₀, R]` with derivative `f'` solving
`f' x = (a f x + (A + ε x) h x)/x` there, then

`f R * R^{-a} - f r₀ * r₀^{-a} = ∫_{r₀}^{R} (A + ε s) * (h s * s^{-(a+1)}) ds`.

No regularity of `h` is used and no primitive of `h s/s` is ever differentiated:
the only differentiation is that of `f` and of the explicit power `x^{-a}`,
both of which hold everywhere on `[r₀,R]`.  (The absolute-continuity input is
`absolutelyContinuousOnInterval_of_hasDerivAt_bounded` applied to the explicit
bound on `f'` obtained from bounds for `f` and `h`.) -/
theorem increment_integrating_factor {h f f' ε : ℝ → ℝ} {a A r₀ R Cf Ch : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (a * f x + (A + ε x) * h x) / x)
    (hCf : ∀ x ∈ uIcc r₀ R, |f x| ≤ Cf)
    (hCh : ∀ x ∈ uIcc r₀ R, |h x| ≤ Ch) :
    f R * R ^ (-a) - f r₀ * r₀ ^ (-a) =
      ∫ s in r₀..R, (A + ε s) * (h s * s ^ (-(a + 1))) := by
  have hfb : ∀ x ∈ uIcc r₀ R, x ∈ uIcc r₀ R → |f x| ≤ Cf := fun x hx _ => hCf x hx
  have hCf0 : 0 ≤ Cf := (abs_nonneg (f r₀)).trans (hCf r₀ (by rw [uIcc_of_le hR]; exact ⟨le_rfl, hR⟩))
  have hCh0 : 0 ≤ Ch := (abs_nonneg (h r₀)).trans (hCh r₀ (by rw [uIcc_of_le hR]; exact ⟨le_rfl, hR⟩))
  have hf'bound : ∀ x ∈ uIcc r₀ R, ‖f' x‖ ≤ (|a| * Cf + (|A| + 1) * Ch) / r₀ := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hfx : |f x| ≤ Cf := hCf x (by rw [uIcc_of_le hR]; exact hx)
    have hhx : |h x| ≤ Ch := hCh x (by rw [uIcc_of_le hR]; exact hx)
    have hεx : |ε x| ≤ 1 := hε1 x hx.1
    have hK0 : 0 ≤ |a| * Cf + (|A| + 1) * Ch :=
      add_nonneg (mul_nonneg (abs_nonneg a) hCf0)
        (mul_nonneg (by have := abs_nonneg A; linarith) hCh0)
    have hsum : |a * f x + (A + ε x) * h x| ≤ |a| * Cf + (|A| + 1) * Ch := by
      have h1 : |a * f x| ≤ |a| * Cf := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hfx (abs_nonneg a)
      have h2 : |A + ε x| ≤ |A| + 1 := by
        have := abs_add_le A (ε x); linarith
      have h3 : |(A + ε x) * h x| ≤ (|A| + 1) * Ch := by
        rw [abs_mul]
        exact mul_le_mul h2 hhx (abs_nonneg _) (by positivity)
      calc |a * f x + (A + ε x) * h x| ≤ |a * f x| + |(A + ε x) * h x| := abs_add_le _ _
        _ ≤ |a| * Cf + (|A| + 1) * Ch := add_le_add h1 h3
    rw [hode x hx.1, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    calc |a * f x + (A + ε x) * h x| / x
        ≤ (|a| * Cf + (|A| + 1) * Ch) / x := div_le_div_of_nonneg_right hsum hx0.le
      _ ≤ (|a| * Cf + (|A| + 1) * Ch) / r₀ := div_le_div_of_nonneg_left hK0 hr₀ hx.1
  have hfAC : AbsolutelyContinuousOnInterval f r₀ R := by
    apply absolutelyContinuousOnInterval_of_hasDerivAt_bounded
      (C := (|a| * Cf + (|A| + 1) * Ch) / r₀)
    · intro x hx
      rw [uIcc_of_le hR] at hx
      exact hderiv x hx.1
    · exact hf'bound
  have hpowAC : AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ (-a)) r₀ R :=
    absolutelyContinuousOnInterval_rpow hr₀ hR
  let q : ℝ → ℝ := fun x => f x * x ^ (-a)
  have hqAC : AbsolutelyContinuousOnInterval q r₀ R := hfAC.mul hpowAC
  have hqderiv : ∀ᵐ x ∂volume, x ∈ Ioc r₀ R →
      deriv q x = (A + ε x) * (h x * x ^ (-(a + 1))) := by
    filter_upwards with x hxmem
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hxd : HasDerivAt q (f' x * x ^ (-a) + f x * (-a * x ^ (-a - 1))) x :=
      (hderiv x hxmem.1.le).mul
        (Real.hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl (ne_of_gt hx0)))
    have h1 : x ^ (-a) = x * x ^ (-(a + 1)) := by
      have h := Real.rpow_add hx0 (1 : ℝ) (-(a + 1))
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have h2 : x ^ (-a - 1) = x ^ (-(a + 1)) := by
      congr 1
      ring
    rw [hxd.deriv, hode x hxmem.1.le, h1, h2]
    have hxne : x ≠ 0 := ne_of_gt hx0
    field_simp
    ring
  calc f R * R ^ (-a) - f r₀ * r₀ ^ (-a)
      = q R - q r₀ := by rfl
    _ = ∫ s in r₀..R, deriv q s := hqAC.integral_deriv_eq_sub.symm
    _ = ∫ s in r₀..R, (A + ε s) * (h s * s ^ (-(a + 1))) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx hxu
        exact hx (by rwa [uIoc_of_le hR] at hxu)


/-! ### The analytic core: a single signed error `ε → 0` -/

/-- **Lemma I.5.26, analytic core (integrating-factor route).**

Let `h` be measurable, positive above a threshold and regularly varying of index
`b > a`, let `f` be differentiable on `[r₀, ∞)` with derivative `f'`, and suppose

`f' x = (a f x + (A + ε x) h x)/x`  for `x ≥ r₀`,

where `ε` is measurable, `ε → 0` and `|ε x| ≤ 1`.  Then `f r/h r → A/(b-a)`.

No positivity of `f`, no continuity of `h`, no differentiability of the
primitive `∫ h s/s ds` and no shift by such a primitive is used.  The signed
error may be arbitrary: it is the *same* `ε` in both terms only because the
error on `f` has been absorbed into `h` using `f = O(h)`. -/
theorem tendsto_div_of_signed_weighted_ode {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {a A : ℝ} {f f' ε : ℝ → ℝ} {r₀ : ℝ}
    (_ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀) (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hεm : Measurable ε) (hε0 : Tendsto ε atTop (𝓝 0)) (hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (a * f x + (A + ε x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hb : 0 < b := D.pos_index
  set φ : ℝ → ℝ := fun s => h s * s ^ (-(a + 1)) with hφdef
  set v : ℝ → ℝ := fun r => h r * r ^ (-a) with hvdef
  have hvr : ∀ r, 0 < r → r * φ r = v r := by
    intro r hr
    have h1 : r * r ^ (-(a + 1)) = r ^ (-a) := by
      have h := Real.rpow_add hr (1 : ℝ) (-(a + 1))
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    calc r * φ r = r * (h r * r ^ (-(a + 1))) := by rw [hφdef]
      _ = h r * (r * r ^ (-(a + 1))) := by ring
      _ = h r * r ^ (-a) := by rw [h1]
      _ = v r := by rw [hvdef]
  have hφm : Measurable φ := by
    have hhm : Measurable h := D.measurable_f
    have hp : Measurable (fun r : ℝ => r ^ (-(a + 1))) := by fun_prop
    rw [hφdef]
    exact Measurable.mul hhm hp
  have hvm : Measurable v := by
    have hhm : Measurable h := D.measurable_f
    have hp : Measurable (fun r : ℝ => r ^ (-a)) := by fun_prop
    rw [hvdef]
    exact Measurable.mul hhm hp
  have hφrv : RegularlyVaryingAtTop φ (b - a - 1) := by
    have hm := D.rv.mul (regularlyVaryingAtTop_rpow (-(a + 1)))
    have hidx : b + (-(a + 1)) = b - a - 1 := by ring
    rw [hidx] at hm
    simpa [hφdef] using hm
  have hφpos : ∀ᶠ x in atTop, 0 < φ x := by
    filter_upwards [eventually_ge_atTop D.threshold, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    simp only [hφdef]
    exact mul_pos (D.pos_above x hx) (Real.rpow_pos_of_pos hx0 _)
  have hhint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable h volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
    rw [uIcc_of_le hxy] at hs
    rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s (le_trans hrD (le_trans hx hs.1)))]
    exact hC s (le_trans hrD (le_trans hx hs.1)) hs.2
  have hφint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable φ volume x y := by
    intro x y hx hxy
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).1 (hhint x y hx hxy)
    have hcont : ContinuousOn (fun s : ℝ => s ^ (-(a + 1))) (Icc x y) := by
      intro s hs
      exact (Real.continuousAt_rpow_const s (-(a + 1))
        (Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hs.1)))).continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [hφdef, mul_comm, mul_left_comm, mul_assoc] using
      hIc.mul_continuousOn hcont isCompact_Icc
  have hIntεφ : ∀ r, r₀ ≤ r → IntervalIntegrable (fun s => ε s * φ s) volume r₀ r := by
    intro r hr
    refine (hφint r₀ r le_rfl hr).mono_fun (hεm.mul hφm).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hr] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hs0 : |ε s| ≤ 1 := hε1 s hs.1.le
    calc |ε s| * |φ s| ≤ 1 * |φ s| := mul_le_mul_of_nonneg_right hs0 (abs_nonneg _)
      _ = |φ s| := one_mul _
  -- Karamata: the normalizing primitive
  have hA0 : Tendsto (fun r => (∫ s in r₀..r, φ s) / v r) atTop (𝓝 (1 / (b - a))) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (g := φ) (δ := fun _ => 0)
      (r₀ := r₀) (c := b - a - 1) (by linarith) hr₀ hr₀1 hφm hφrv hφpos hφint
      measurable_const tendsto_const_nhds (fun x _ => by simp)
    have h1 : (1 : ℝ) / ((b - a - 1) + 1) = 1 / (b - a) := by
      rw [show (b - a - 1) + 1 = b - a by ring]
    rw [h1] at hk
    refine hk.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [hvr r hr]
    simp
  -- Karamata: the same with multiplier `1 - ε`
  have hA1 : Tendsto (fun r => (∫ s in r₀..r, (1 - ε s) * φ s) / v r) atTop
      (𝓝 (1 / (b - a))) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (g := φ) (δ := ε)
      (r₀ := r₀) (c := b - a - 1) (by linarith) hr₀ hr₀1 hφm hφrv hφpos hφint
      hεm hε0 hε1
    have h1 : (1 : ℝ) / ((b - a - 1) + 1) = 1 / (b - a) := by
      rw [show (b - a - 1) + 1 = b - a by ring]
    rw [h1] at hk
    refine hk.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [hvr r hr]
  -- the error term is `o(v)`
  have hAε : Tendsto (fun r => (∫ s in r₀..r, ε s * φ s) / v r) atTop (𝓝 0) := by
    have hsub := hA0.sub hA1
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop r₀, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
    have h1 : (∫ s in r₀..r, (1 - ε s) * φ s) =
        (∫ s in r₀..r, φ s) - ∫ s in r₀..r, ε s * φ s := by
      rw [← intervalIntegral.integral_sub (hφint r₀ r le_rfl hr) (hIntεφ r hr)]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [h1, sub_div]
    have hvne : v r ≠ 0 := by
      rw [hvdef]
      exact (mul_pos (D.pos_above r (le_trans hrD hr)) (Real.rpow_pos_of_pos hrpos _)).ne'
    field_simp
    ring
  -- the driving integral, normalized
  have hA2 : Tendsto (fun r => (∫ s in r₀..r, (A + ε s) * φ s) / v r) atTop
      (𝓝 (A / (b - a))) := by
    have h1 : Tendsto (fun r => A * ((∫ s in r₀..r, φ s) / v r) +
        (∫ s in r₀..r, ε s * φ s) / v r) atTop (𝓝 (A * (1 / (b - a)) + 0)) :=
      (hA0.const_mul A).add hAε
    rw [add_zero] at h1
    have hAval : A * (1 / (b - a)) = A / (b - a) := by ring
    rw [hAval] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hstep : (∫ s in r₀..r, (A + ε s) * φ s) =
        A * (∫ s in r₀..r, φ s) + ∫ s in r₀..r, ε s * φ s := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hφint r₀ r le_rfl hr).const_mul A) (hIntεφ r hr)]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [hstep, add_div, mul_div_assoc]
  -- bounds for `f` and `h` on compact tails, feeding the increment identity
  have hfbdd : ∀ R, r₀ ≤ R → ∃ Cf, ∀ x ∈ uIcc r₀ R, |f x| ≤ Cf := by
    intro R hR
    have hfc : ContinuousOn f (Icc r₀ R) := fun x hx =>
      (hderiv x hx.1).continuousAt.continuousWithinAt
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
    exact ⟨Cf, fun x hx => by
      rw [uIcc_of_le hR] at hx
      simpa [Real.norm_eq_abs] using hCf x hx⟩
  have hhbdd : ∀ R, r₀ ≤ R → ∃ Ch, ∀ x ∈ uIcc r₀ R, |h x| ≤ Ch := by
    intro R hR
    obtain ⟨Ch, hCh⟩ := D.bddAbove_Icc R
    refine ⟨Ch, fun x hx => ?_⟩
    rw [uIcc_of_le hR] at hx
    rw [abs_of_pos (D.pos_above x (le_trans hrD hx.1))]
    exact hCh x (le_trans hrD hx.1) hx.2
  have hinc : ∀ᶠ R in atTop, f R * R ^ (-a) - f r₀ * r₀ ^ (-a) =
      ∫ s in r₀..R, (A + ε s) * φ s := by
    filter_upwards [eventually_ge_atTop r₀] with R hR
    obtain ⟨Cf, hCf⟩ := hfbdd R hR
    obtain ⟨Ch, hCh⟩ := hhbdd R hR
    exact increment_integrating_factor (a := a) (A := A) hr₀ hR
      (fun x hx => hderiv x hx) hε1 hode hCf hCh
  have hqdiff : Tendsto (fun r => (f r * r ^ (-a) - f r₀ * r₀ ^ (-a)) / v r) atTop
      (𝓝 (A / (b - a))) := by
    refine hA2.congr' ?_
    filter_upwards [hinc] with r hr
    rw [hr]
  have hvD : RVPosData v (b - a) := by
    refine RVPosData.of (by linarith) hvm ?_ ?_
    · have hm := D.rv.mul (regularlyVaryingAtTop_rpow (-a))
      have hidx : b + -a = b - a := by ring
      rw [hidx] at hm
      simpa [hvdef] using hm
    · filter_upwards [eventually_ge_atTop D.threshold, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      simp only [hvdef]
      exact mul_pos (D.pos_above x hx) (Real.rpow_pos_of_pos hx0 _)
  have hvtop : Tendsto v atTop atTop := hvD.tendsto_atTop_self
  have hq0 : Tendsto (fun r => (f r₀ * r₀ ^ (-a)) / v r) atTop (𝓝 0) := by
    have h := hvtop.inv_tendsto_atTop.const_mul (f r₀ * r₀ ^ (-a))
    rw [mul_zero] at h
    simpa [div_eq_mul_inv, Pi.inv_apply, mul_comm] using h
  have hq : Tendsto (fun r => (f r * r ^ (-a)) / v r) atTop (𝓝 (A / (b - a))) := by
    have h := hqdiff.add hq0
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards with r
    ring
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop D.threshold, eventually_ge_atTop r₀] with r hr hrr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hrr
  have hhr : h r ≠ 0 := (D.pos_above r hr).ne'
  have hpr : r ^ (-a) ≠ 0 := (Real.rpow_pos_of_pos hrpos (-a)).ne'
  simp only [hvdef]
  field_simp


/-! ### Lemma I.5.26 from the paper's driving-ratio hypothesis -/

/-- **Lemma I.5.26, driving-ratio form.**

Let `h` be measurable, positive above a threshold and regularly varying of index
`b > a > 0`, and let `f` be differentiable on `(0, ∞)` with derivative `f'`
satisfying the paper's asymptotic ODE (I.5.34)

`f' r = ((a ± o(1)) f r + (A ± o(1)) h r)/r`,

encoded as `(r f' r - a f r)/h r → A` (the `a` term is split off exactly; the
error on `f` is part of the same little-`o`).  Then `f r/h r → A/(b-a)`.

Note that no bound `|f| = O(h)` is needed in this form: the homogeneous solution
of the ODE grows like `r^a`, which is `o(h r)` because `b > a`. -/
theorem lemma_I_5_26_signed_ode {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {a A : ℝ} (ha : 0 < a) (hab : a < b) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hode : Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 A)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hf0m : Measurable f₀ := measurable_ite_pos_of_hasDerivAt hderiv
  have hf0eq : ∀ x, 0 < x → f₀ x = f x := by
    intro x hx
    simp [f₀, hx]
  have hf0d : ∀ x, 0 < x → HasDerivAt f₀ (f' x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  -- the signed error of the paper's ODE
  set g : ℝ → ℝ := fun x => (x * deriv f₀ x - a * f₀ x) / h x - A with hgdef
  have hgm : Measurable g := by
    have h1 : Measurable (fun x : ℝ => x * deriv f₀ x - a * f₀ x) :=
      (measurable_id.mul (measurable_deriv f₀)).sub (measurable_const.mul hf0m)
    exact (h1.div D.measurable_f).sub measurable_const
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hraw : Tendsto (fun r => (r * f' r - a * f r) / h r - A) atTop (𝓝 0) := by
      have h := hode.sub_const A
      rwa [sub_self] at h
    refine hraw.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [hgdef]
    rw [hf0eq x hx, (hf0d x hx).deriv]
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hg0 1 one_pos
  set r₀ : ℝ := max (max 1 D.threshold) B with hr₀def
  have hr₀1 : 1 ≤ r₀ := le_trans (le_max_left 1 D.threshold) (le_max_left _ _)
  have hrD : D.threshold ≤ r₀ := le_trans (le_max_right 1 D.threshold) (le_max_left _ _)
  have hr₀B : B ≤ r₀ := le_max_right _ _
  have hr₀ : 0 < r₀ := lt_of_lt_of_le one_pos hr₀1
  let ε : ℝ → ℝ := (Ici r₀).indicator g
  have hεm : Measurable ε := hgm.indicator measurableSet_Ici
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    refine hg0.congr' ?_
    filter_upwards [eventually_gt_atTop r₀] with x hx
    exact (Set.indicator_of_mem (Set.mem_Ici.2 hx.le) g).symm
  have hε1 : ∀ x, r₀ ≤ x → |ε x| ≤ 1 := by
    intro x hx
    rw [show ε x = g x from Set.indicator_of_mem (Set.mem_Ici.2 hx) g]
    have hb := hB x (le_trans hr₀B hx)
    rw [Real.dist_eq, sub_zero] at hb
    linarith
  have hode' : ∀ x, r₀ ≤ x → f' x = (a * f x + (A + ε x) * h x) / x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hx
    have hhr : h x ≠ 0 := (D.pos_above x (le_trans hrD hx)).ne'
    have hεx : ε x = (x * f' x - a * f x) / h x - A := by
      rw [show ε x = g x from Set.indicator_of_mem (Set.mem_Ici.2 hx) g]
      simp only [hgdef]
      rw [hf0eq x hxpos, (hf0d x hxpos).deriv]
    rw [hεx]
    field_simp
    ring
  exact tendsto_div_of_signed_weighted_ode D ha hab hr₀ hr₀1 hrD
    (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx)) hεm hε0 hε1 hode'

/-- **Lemma I.5.26 in the paper's `f = (A/(b-a) ± o(1)) h` form.** -/
theorem lemma_I_5_26_isLittleO {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {a A : ℝ} (ha : 0 < a) (hab : a < b) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hode : Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 A)) :
    (fun r => f r - (A / (b - a)) * h r) =o[atTop] h := by
  have hlim := lemma_I_5_26_signed_ode D ha hab hderiv hode
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ r in atTop, |f r / h r - A / (b - a)| < c := by
    have hball := hlim.eventually (Metric.ball_mem_nhds (A / (b - a)) hc)
    simpa [Real.dist_eq, Metric.mem_ball] using hball
  filter_upwards [hev, eventually_ge_atTop D.threshold] with r hr hhr
  have hpos : 0 < h r := D.pos_above r hhr
  have hkey : f r - (A / (b - a)) * h r = h r * (f r / h r - A / (b - a)) := by
    field_simp
  rw [hkey, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  nlinarith [abs_nonneg (f r / h r - A / (b - a))]


/-- **Lemma I.5.26 in the paper's literal two-error form.**

The paper assumes `f' r = ((a ± o(1)) f r + (A ± o(1)) h r)/r`, i.e. *two*
independent error terms, together with `|f| = O(h)`.  The bound on `f` is used
here for exactly one purpose: the error on `f` is absorbed into the `h` term,
`ε₁ f + (A + ε₂) h = (A + ε₁ f/h + ε₂) h`, which needs `|f/h| ≤ C`.  After that
absorption the analytic core `tendsto_div_of_signed_weighted_ode` applies. -/
theorem lemma_I_5_26_two_errors {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {a A C : ℝ} (ha : 0 < a) (hab : a < b) {f f' ε₁ ε₂ : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hO : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hbdd : ∀ᶠ r in atTop, |f r / h r| ≤ C := by
    filter_upwards [hO, eventually_ge_atTop D.threshold] with r hr hrt
    have hpos := D.pos_above r hrt
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hr
  have hprod : Tendsto (fun x => ε₁ x * (f x / h x)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ x in atTop, ‖ε₁ x * (f x / h x)‖ ≤ |ε₁ x| * C := by
      filter_upwards [hbdd] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have hup : Tendsto (fun x => |ε₁ x| * C) atTop (𝓝 0) := by
      have h := hε₁.abs.mul_const C
      rwa [abs_zero, zero_mul] at h
    exact squeeze_zero_norm' hbound hup
  have heq : ∀ᶠ x in atTop, (x * f' x - a * f x) / h x = ε₁ x * (f x / h x) + A + ε₂ x := by
    filter_upwards [hode, eventually_ge_atTop D.threshold] with x hx hxt
    have hhr : h x ≠ 0 := (D.pos_above x hxt).ne'
    have hx0 : x ≠ 0 := (lt_of_lt_of_le (lt_of_lt_of_le one_pos D.one_le_threshold) hxt).ne'
    rw [hx]
    field_simp
    ring
  have hlim : Tendsto (fun x => ε₁ x * (f x / h x) + A + ε₂ x) atTop (𝓝 A) := by
    have h := (hprod.add_const A).add hε₂
    simpa only [zero_add, add_zero] using h
  have hratio : Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 A) := by
    refine hlim.congr' ?_
    filter_upwards [heq] with x hx
    exact hx.symm
  exact lemma_I_5_26_signed_ode D ha hab hderiv hratio


/-! ### Non-vacuity check

The hypotheses of `lemma_I_5_26_signed_ode` are simultaneously satisfiable and
the conclusion is the expected one: with `h r = r^2` (index `b = 2`), `a = 1`,
`A = 3` and `f r = 3 r^2`, the driving ratio is identically `3` and
`f r/h r → 3 = A/(b - a)`. -/

/-- `h r = r^2`, `a = 1`, `b = 2`, `A = 3`, `f r = 3 r^2`: the hypotheses of
Lemma I.5.26 hold and the conclusion is `f/h → 3 = A/(b-a)`. -/
theorem lemma_I_5_26_example :
    Tendsto (fun r : ℝ => (3 * r ^ (2:ℝ)) / r ^ (2:ℝ)) atTop (𝓝 3) := by
  have hrv : RegularlyVaryingAtTop (fun r : ℝ => r ^ (2:ℝ)) 2 := regularlyVaryingAtTop_rpow 2
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < x ^ (2:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact Real.rpow_pos_of_pos hx 2
  let D := RVPosData.of (by norm_num)
    (by fun_prop : Measurable (fun r : ℝ => r ^ (2:ℝ))) hrv hpos
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun r : ℝ => 3 * r ^ (2:ℝ)) (6 * x) x := by
    intro x hx
    have hd : HasDerivAt (fun r : ℝ => 3 * r ^ (2:ℝ)) (3 * (2 * x ^ ((2:ℝ) - 1))) x :=
      (Real.hasDerivAt_rpow_const (x := x) (p := 2) (Or.inl (ne_of_gt hx))).const_mul 3
    have hc : 3 * (2 * x ^ ((2:ℝ) - 1)) = 6 * x := by
      rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      ring
    rwa [hc] at hd
  have hode : Tendsto (fun r : ℝ => (r * (6 * r) - 1 * (3 * r ^ (2:ℝ))) / r ^ (2:ℝ)) atTop (𝓝 3) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    rw [Real.rpow_two]
    field_simp
    ring
  have hlim := lemma_I_5_26_signed_ode (h := fun r : ℝ => r ^ (2:ℝ)) (b := 2) D
    (a := 1) (A := 3) (by norm_num) (by norm_num) (f := fun r : ℝ => 3 * r ^ (2:ℝ))
    (f' := fun r : ℝ => 6 * r) hderiv hode
  have hval : (3:ℝ) / (2 - 1) = 3 := by norm_num
  rw [hval] at hlim
  exact hlim


/-- **Lemma I.5.26 with only the paper's hypotheses** (no `RVPosData` bundle):
`h` measurable, regularly varying of index `b > 0` and eventually positive;
`a, b > 0` with `a < b`; `f` differentiable on `(0,∞)`; `|f| = O(h)`; and the
two-error driving ODE

`f' r = ((a + ε₁ r) f r + (A + ε₂ r) h r)/r`, `ε₁, ε₂ → 0`.

Then `f r/h r → A/(b-a)`. -/
theorem lemma_I_5_26 {h : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x : ℝ in atTop, 0 < h x)
    {a A C : ℝ} (ha : 0 < a) (hab : a < b) {f f' ε₁ ε₂ : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hO : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) :=
  lemma_I_5_26_two_errors (RVPosData.of hb hmeas hrv hpos) ha hab hderiv hO hε₁ hε₂ hode

/-- **Lemma I.5.26, paper's conclusion form with the paper's hypotheses**:
`f r = (A/(b-a) ± o(1)) h r`. -/
theorem lemma_I_5_26_isLittleO' {h : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hmeas : Measurable h) (hrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ᶠ x : ℝ in atTop, 0 < h x)
    {a A C : ℝ} (ha : 0 < a) (hab : a < b) {f f' ε₁ ε₂ : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hO : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    (fun r => f r - (A / (b - a)) * h r) =o[atTop] h := by
  have hlim := lemma_I_5_26 hb hmeas hrv hpos ha hab hderiv hO hε₁ hε₂ hode
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ r in atTop, |f r / h r - A / (b - a)| < c := by
    have hball := hlim.eventually (Metric.ball_mem_nhds (A / (b - a)) hc)
    simpa [Real.dist_eq, Metric.mem_ball] using hball
  filter_upwards [hev, hpos] with r hr hhr
  have hkey : f r - (A / (b - a)) * h r = h r * (f r / h r - A / (b - a)) := by
    field_simp
  rw [hkey, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hhr]
  nlinarith [abs_nonneg (f r / h r - A / (b - a))]
/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.increment_integrating_factor
#print axioms PercLib.CriticalLRP.Analysis.tendsto_div_of_signed_weighted_ode
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_signed_ode
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_isLittleO
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_two_errors
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_isLittleO'
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_26_example

end PercLib.CriticalLRP.Analysis
