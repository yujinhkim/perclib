/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwytmnfc`, member `m1`,
direction (E).

# The absolute-continuity hypothesis of the second-moment ODE-to-RV engine is essential

`PercLib.CriticalLRP.SecondMomentRV.secondMoment_regularlyVarying` (and its actual-model
specialization `PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_regularlyVarying_of_ae_linear_ode`)
concludes regular variation of index `3α` from

* positivity of `f` on the tail,
* **absolute continuity of `f` on every compact window of the tail** (`hac`),
* the a.e. linear ODE `f' = 3α (1 - E) f / r`,
* measurability of the error `E` and `E → 0`.

This file shows that `hac` is not a convenience: it cannot be replaced by positivity plus
monotonicity plus the a.e. ODE.  The witness is the monotone step-modulated power law

  `stepPow a r = r ^ a * 2 ^ (Nat.floor r)`,

which is locally a constant multiple of `r ↦ r ^ a`, hence satisfies the ODE
`f' = a f / r` at every non-integer radius (so the error is `E ≡ 0`, which is measurable
and tends to 0), is positive and increasing on `(0,∞)`, and yet is **not** regularly
varying of index `a`: at `t = n+1` the ratio `f (2t) / f t` equals `2 ^ a * 2 ^ (n+1)`,
which diverges.  The jumps at the integers are exactly the failure of absolute
continuity.

This is a sharpness statement about the analytic interface only.  It says nothing about
whether the model's cutoff second moment is absolutely continuous (it is expected to be,
and that is a genuine model obligation carried explicitly as `hac`); it says that the
obligation cannot be discharged from the remaining hypotheses of the engine.
-/

module

public import PercLib.CriticalLRP.Analysis.SecondMomentRV
public import PercLib.CriticalLRP.Analysis.SecondMomentObstruction.Defs

/-! # Absolute continuity is essential for the ODE-to-RV conclusion -/

noncomputable section

open Filter Topology Set MeasureTheory

open scoped Topology

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.ACSharpness

open PercLib.CriticalLRP.Analysis


theorem measurable_stepPow (a : ℝ) : Measurable (stepPow a) := by
  have h1 : Measurable fun r : ℝ => r ^ a := Measurable.pow_const measurable_id a
  have h2 : Measurable fun r : ℝ => (2 : ℝ) ^ Nat.floor r :=
    measurable_const.pow Nat.measurable_floor
  exact h1.mul h2

theorem stepPow_pos {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 < r) : 0 < stepPow a r := by
  unfold stepPow
  exact mul_pos (Real.rpow_pos_of_pos hr a) (by positivity)

theorem monotoneOn_stepPow {a : ℝ} (ha : 0 < a) : MonotoneOn (stepPow a) (Ioi 0) := by
  intro x hx y hy hxy
  unfold stepPow
  have h1 : x ^ a ≤ y ^ a := Real.rpow_le_rpow hx.le hxy ha.le
  have h2 : (2 : ℝ) ^ (Nat.floor x) ≤ (2 : ℝ) ^ (Nat.floor y) :=
    pow_le_pow_right₀ (by norm_num) (Nat.floor_mono hxy)
  exact mul_le_mul h1 h2 (pow_pos (by norm_num) _).le (Real.rpow_nonneg hy.le a)

/-- Off the lattice of natural numbers, the multiplier `2 ^ ⌊r⌋` is locally constant. -/
theorem floor_eventually_eq {t : ℝ} (ht1 : 1 ≤ t)
    (ht : t ∉ Set.range ((↑) : ℕ → ℝ)) :
    ∀ᶠ r in 𝓝 t, Nat.floor r = Nat.floor t := by
  set n : ℕ := Nat.floor t
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hle : (n : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  have hne : t ≠ (n : ℝ) := fun h => ht ⟨n, h.symm⟩
  have hnlt : (n : ℝ) < t := lt_of_le_of_ne hle (Ne.symm hne)
  set δ : ℝ := min (t - (n : ℝ)) ((n : ℝ) + 1 - t) with hδ
  have hδpos : 0 < δ := lt_min (sub_pos.mpr hnlt) (sub_pos.mpr hlt)
  have hδ1 : δ ≤ t - (n : ℝ) := min_le_left _ _
  have hδ2 : δ ≤ (n : ℝ) + 1 - t := min_le_right _ _
  refine Filter.eventually_of_mem
    (Ioo_mem_nhds (a := t - δ) (b := t + δ) (by linarith) (by linarith)) ?_
  intro r hr
  have hr1 : (n : ℝ) ≤ r := by linarith [hr.1]
  have hr2 : r < (n : ℝ) + 1 := by linarith [hr.2]
  exact (Nat.floor_eq_iff (show (0 : ℝ) ≤ r by linarith)).mpr ⟨hr1, hr2⟩

/-- The a.e. linear ODE `f' = a f / r` at every non-integer radius. -/
theorem hasDerivAt_stepPow {a : ℝ} {t : ℝ} (ht1 : 1 ≤ t)
    (ht : t ∉ Set.range ((↑) : ℕ → ℝ)) :
    HasDerivAt (stepPow a) (a * stepPow a t / t) t := by
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  set c : ℝ := (2 : ℝ) ^ (Nat.floor t) with hc
  have hbase : HasDerivAt (fun r : ℝ => c * r ^ a) (c * (a * t ^ (a - 1))) t :=
    (Real.hasDerivAt_rpow_const (p := a) (Or.inl htne)).const_mul c
  have hval : c * (a * t ^ (a - 1)) = a * stepPow a t / t := by
    rw [Real.rpow_sub htpos a 1, Real.rpow_one, hc]
    unfold stepPow
    field_simp
  rw [← hval]
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [floor_eventually_eq ht1 ht] with r hr
  unfold stepPow
  rw [hr, hc]
  ring

/-- Consequently the ODE holds almost everywhere on the tail. -/
theorem ae_hasDerivAt_stepPow (a : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Ici 1)), HasDerivAt (stepPow a) (a * stepPow a t / t) t := by
  have hcount : (Set.range ((↑) : ℕ → ℝ)).Countable := Set.countable_range _
  have hzero : volume (Set.range ((↑) : ℕ → ℝ) : Set ℝ) = 0 :=
    hcount.measure_zero volume
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ Set.range ((↑) : ℕ → ℝ) := by
    rw [ae_iff]
    have h : {a : ℝ | ¬ a ∉ Set.range ((↑) : ℕ → ℝ)} = Set.range ((↑) : ℕ → ℝ) := by
      ext x
      simp
    rw [h]
    exact hzero
  filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ici] with t htmem htI
  exact hasDerivAt_stepPow htI htmem

/-- The doubling ratio at `t = n + 1`. -/
theorem stepPow_two_mul_ratio (a : ℝ) (n : ℕ) :
    stepPow a (2 * ((n : ℝ) + 1)) / stepPow a ((n : ℝ) + 1)
      = (2 : ℝ) ^ a * (2 : ℝ) ^ (n + 1) := by
  have h1 : Nat.floor (2 * ((n : ℝ) + 1)) = 2 * (n + 1) := by
    have hcast : 2 * ((n : ℝ) + 1) = ((2 * (n + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Nat.floor_natCast]
  have h2 : Nat.floor ((n : ℝ) + 1) = n + 1 := by
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Nat.floor_natCast]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold stepPow
  rw [h1, h2, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpos.le]
  have hsplit : (2 : ℝ) ^ (2 * (n + 1)) = (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) := by
    rw [show 2 * (n + 1) = (n + 1) + (n + 1) from by ring, pow_add]
  rw [hsplit]
  have hane : ((n : ℝ) + 1) ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hpos a)
  have h2ne : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  field_simp

/-- **`stepPow a` is not regularly varying of index `a`.** -/
theorem not_regularlyVarying_stepPow {a : ℝ} (ha : 0 < a) :
    ¬ RegularlyVaryingAtTop (stepPow a) a := by
  intro hRV
  have hlim : Tendsto (fun x : ℝ => stepPow a (2 * x) / stepPow a x) atTop
      (𝓝 ((2 : ℝ) ^ a)) := hRV.2 2 (by norm_num)
  have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hcomp := hlim.comp hseq
  have hvalues : ∀ n : ℕ,
      stepPow a (2 * ((n : ℝ) + 1)) / stepPow a ((n : ℝ) + 1)
        = (2 : ℝ) ^ a * (2 : ℝ) ^ (n + 1) := stepPow_two_mul_ratio a
  have hconst : Tendsto (fun n : ℕ => (2 : ℝ) ^ a * (2 : ℝ) ^ (n + 1)) atTop
      (𝓝 ((2 : ℝ) ^ a)) := hcomp.congr' (Eventually.of_forall hvalues)
  have hpowlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop (𝓝 1) := by
    have h2a : (2 : ℝ) ^ a ≠ 0 := by positivity
    have h := hconst.div_const ((2 : ℝ) ^ a)
    rw [div_self h2a] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    field_simp
  have hbig : ∀ᶠ n : ℕ in atTop, (2 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    have hshift : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
      have h0 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * (2 : ℝ) ^ 1) atTop atTop :=
        h0.atTop_mul_const (by norm_num : (0 : ℝ) < 2 ^ 1)
      simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using h1
    exact hshift.eventually_gt_atTop 2
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (n + 1) < 2 :=
    hpowlim.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨n, hn1, hn2⟩ := (hbig.and hsmall).exists
  exact absurd hn1 (not_lt.mpr hn2.le)

/-- **Sharpness of `hac`.**  The ODE-to-RV engine fails if the absolute-continuity
hypothesis is dropped, even retaining eventual positivity, monotonicity and a vanishing
measurable error. -/
theorem ae_linear_ode_does_not_imply_regularlyVarying :
    ¬ ∀ (f E : ℝ → ℝ) (a : ℝ), 0 < a → Measurable E → Tendsto E atTop (𝓝 0) →
      (∀ᶠ t in atTop, 0 < f t) → MonotoneOn f (Ioi 0) →
      (∀ᵐ t ∂(volume.restrict (Ici 1)),
        HasDerivAt f (a * (1 - E t) * f t / t) t) →
      RegularlyVaryingAtTop f a := by
  intro h
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < stepPow 1 t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact stepPow_pos (by norm_num) (by linarith)
  have hmono : MonotoneOn (stepPow 1) (Ioi 0) := monotoneOn_stepPow (by norm_num)
  have hae : ∀ᵐ t ∂(volume.restrict (Ici 1)),
      HasDerivAt (stepPow 1) (1 * (1 - (fun _ : ℝ => (0 : ℝ)) t) * stepPow 1 t / t) t := by
    filter_upwards [ae_hasDerivAt_stepPow 1] with t ht
    simpa using ht
  have hRV := h (stepPow 1) (fun _ => 0) 1 (by norm_num) measurable_const
    tendsto_const_nhds hpos hmono hae
  exact not_regularlyVarying_stepPow (a := 1) (by norm_num) hRV

/-- The counterexample attributes, packaged. -/
theorem exists_monotone_ae_ode_not_regularlyVarying :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ᶠ t in atTop, 0 < f t) ∧ MonotoneOn f (Ioi 0) ∧
      (∀ᵐ t ∂(volume.restrict (Ici 1)), HasDerivAt f (1 * f t / t) t) ∧
      ¬ RegularlyVaryingAtTop f 1 :=
  ⟨stepPow 1, measurable_stepPow 1,
    by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact stepPow_pos (by norm_num) (by linarith),
    monotoneOn_stepPow (by norm_num),
    ae_hasDerivAt_stepPow 1,
    not_regularlyVarying_stepPow (a := 1) (by norm_num)⟩


/-- The doubling ratio of the witness diverges along `t = n + 1`. -/
theorem tendsto_ratio_stepPow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => stepPow a (2 * ((n : ℝ) + 1)) / stepPow a ((n : ℝ) + 1))
      atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ a * ((2 : ℝ) ^ n * 2)) atTop atTop := by
    have h0 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * 2) atTop atTop :=
      h0.atTop_mul_const (by norm_num : (0 : ℝ) < 2)
    exact h1.const_mul_atTop (by positivity)
  have hcongr : ∀ n : ℕ, stepPow a (2 * ((n : ℝ) + 1)) / stepPow a ((n : ℝ) + 1)
      = (2 : ℝ) ^ a * ((2 : ℝ) ^ n * 2) := by
    intro n
    rw [stepPow_two_mul_ratio a n, pow_succ']
    ring
  exact hpow.congr' (Eventually.of_forall fun n => (hcongr n).symm)

/-- **The `~ A r ^ a` refinement also fails for the witness**: `stepPow a r / r ^ a`
equals `2 ^ ⌊r⌋`, which is unbounded. -/
theorem not_tendsto_div_rpow_stepPow {a : ℝ} (ha : 0 < a) :
    ¬ ∃ A : ℝ, Tendsto (fun r : ℝ => stepPow a r / r ^ a) atTop (𝓝 A) := by
  rintro ⟨A, hA⟩
  have hrat : ∀ r : ℝ, 0 < r → stepPow a r / r ^ a = (2 : ℝ) ^ Nat.floor r := by
    intro r hr
    unfold stepPow
    have hne : r ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr a)
    field_simp
  have hseq : Tendsto (fun n : ℕ => (((n : ℝ) + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hcomp := hA.comp hseq
  have hval : ∀ n : ℕ, stepPow a ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ a
      = (2 : ℝ) ^ (n + 1) := by
    intro n
    refine (hrat ((n : ℝ) + 1) (by positivity)).trans ?_
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Nat.floor_natCast]
  have hconst : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop (𝓝 A) :=
    hcomp.congr' (Eventually.of_forall hval)
  have hshift : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    have h0 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * 2) atTop atTop :=
      h0.atTop_mul_const (by norm_num : (0 : ℝ) < 2)
    exact h1.congr' (Eventually.of_forall fun n => by simp [pow_succ])
  have hev : ∀ᶠ n : ℕ in atTop,
      (A + 1 < (2 : ℝ) ^ (n + 1)) ∧ ((2 : ℝ) ^ (n + 1) < A + 1) :=
    (hshift.eventually_gt_atTop (A + 1)).and
      (hconst.eventually (Iio_mem_nhds (by linarith : A < A + 1)))
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd hn.1 (not_lt.mpr hn.2.le)

/-- **The absolute-continuity hypothesis of `secondMoment_regularlyVarying` is not
removable.**  The statement below is the engine's conclusion from its hypotheses with
`hac` deleted (and `α` fixed, `r₀ = 1`); it is false. -/
theorem secondMoment_regularlyVarying_needs_ac {α : ℝ} (hα : 0 < α) :
    ¬ ∀ (f E : ℝ → ℝ),
        (∀ t : ℝ, 1 ≤ t → 0 < f t) →
        (∀ᵐ t ∂(volume.restrict (Ici 1)),
          HasDerivAt f (3 * α * (1 - E t) * f t / t) t) →
        Measurable E → Tendsto E atTop (𝓝 0) → RegularlyVaryingAtTop f (3 * α) := by
  intro h
  have hpos : ∀ t : ℝ, 1 ≤ t → 0 < stepPow (3 * α) t := by
    intro t ht
    exact stepPow_pos (by positivity) (by linarith)
  have hae : ∀ᵐ t ∂(volume.restrict (Ici 1)),
      HasDerivAt (stepPow (3 * α))
        (3 * α * (1 - (fun _ : ℝ => (0 : ℝ)) t) * stepPow (3 * α) t / t) t := by
    filter_upwards [ae_hasDerivAt_stepPow (3 * α)] with t ht
    simpa using ht
  have hRV := h (stepPow (3 * α)) (fun _ => 0) hpos hae measurable_const tendsto_const_nhds
  exact not_regularlyVarying_stepPow (a := 3 * α) (by positivity) hRV

/-!
## Summary

* `stepPow a r = r ^ a * 2 ^ ⌊r⌋` is measurable, positive on `(0,∞)` and monotone there;
* `HasDerivAt (stepPow a) (a * stepPow a t / t) t` at every non-integer `t`,
  hence almost everywhere on `Ici 1` (`ae_hasDerivAt_stepPow`);
* `stepPow a` is **not** regularly varying of index `a` (`not_regularlyVarying_stepPow`),
  with doubling ratio `2 ^ a * 2 ^ (n+1)` at `t = n+1` (`tendsto_ratio_stepPow`), and the
  `~ A r ^ a` refinement fails as well (`not_tendsto_div_rpow_stepPow`);
* consequently the ODE-to-RV engine is false with positivity + monotonicity + vanishing
  error in place of absolute continuity (`ae_linear_ode_does_not_imply_regularlyVarying`,
  `secondMoment_regularlyVarying_needs_ac`).

The witness has jump discontinuities at every natural number; that is precisely the
failure of absolute continuity, and it is what the `hac` field of
`secondMoment_regularlyVarying` and of
`Orchestration.SourceModelData.momOf_two_regularlyVarying_of_ae_linear_ode` records.
Nothing here asserts anything about the cutoff second moment: the model's `hac` is a
genuine obligation, and this file shows that the remaining hypotheses of the engine
cannot supply it.
-/

#print axioms measurable_stepPow
#print axioms stepPow_pos
#print axioms monotoneOn_stepPow
#print axioms floor_eventually_eq
#print axioms hasDerivAt_stepPow
#print axioms ae_hasDerivAt_stepPow
#print axioms stepPow_two_mul_ratio
#print axioms not_regularlyVarying_stepPow
#print axioms ae_linear_ode_does_not_imply_regularlyVarying
#print axioms exists_monotone_ae_ode_not_regularlyVarying
#print axioms tendsto_ratio_stepPow
#print axioms not_tendsto_div_rpow_stepPow
#print axioms secondMoment_regularlyVarying_needs_ac

end PercLib.CriticalLRP.ACSharpness
