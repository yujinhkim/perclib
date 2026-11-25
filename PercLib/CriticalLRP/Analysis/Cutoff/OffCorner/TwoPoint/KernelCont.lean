/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Continuity of the cutoff kernel profile and Lipschitz bounds for the edge-open profile.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity.Defs

/-!
# Continuity in the cutoff radius of a single cut edge

At a radius `r₀` that is not the length of any nonzero lattice displacement, the cutoff
profile `FiniteVolume.cutoffProfile M.K r s = K s - K r` (for `s ≤ r`) is continuous in `r`
at `r = r₀`, for every fixed edge length `s ≠ r₀`: the branch changes only at `s = r`, and
`K` is continuous at `r₀ > 0` by `K_diff`.

The consequences recorded here are

* `SourceModelData.continuousAt_cutProb`: `r ↦ (M.cutProb r e : ℝ)` is continuous at an
  off-corner radius, for each fixed edge `e`;
* `SourceModelData.abs_cutProb_sub_le`: the edge-open probabilities are Lipschitz in the
  kernel value with constant `β_c`;
* `SourceModelData.tendsto_sum_abs_cutProb`: the `ℓ¹` variation of the edge-open profile
  over a fixed finite edge set tends to `0` at an off-corner radius.

Nothing here uses a moment hypothesis: these are pointwise statements about one edge.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-- Derivative of the damped exponential. -/
theorem deriv_exp_neg (t : ℝ) : deriv (fun t : ℝ => Real.exp (-t)) t = -Real.exp (-t) := by
  have h1 : HasDerivAt (fun t : ℝ => -t) (-1) t := hasDerivAt_neg t
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t h1
  rw [show Real.exp (-t) * (-1) = -Real.exp (-t) by ring] at h2
  exact h2.deriv

/-- **The damped exponential is `1`-Lipschitz on the nonnegative axis.** -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have hdiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ (fun t : ℝ => Real.exp (-t)) t := by
    intro t _
    exact ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).differentiableAt
  have hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖deriv (fun t : ℝ => Real.exp (-t)) t‖ ≤ 1 := by
    intro t ht
    rw [Set.mem_Ici] at ht
    rw [deriv_exp_neg t, norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ici (0:ℝ)) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm] at h
  have h' : |Real.exp (-x) - Real.exp (-y)| ≤ |y - x| := by simpa using h
  rwa [abs_sub_comm x y]

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The cutoff kernel on an explicit pair.**  Loops vanish; a non-loop carries
`cutoffProfile M.K r (M.S.dist a b) = K (dist) - K r` when the edge is inside the radius and
`0` when it is outside. -/
theorem cutKernel_sym2 (r : ℝ) (a b : M.V) :
    M.cutKernel r s(a, b) =
      if a = b then 0 else FiniteVolume.cutoffProfile M.K r (M.S.dist a b) := by
  rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]

/-- **Continuity of a single cut edge in the cutoff radius.**  Off the corner radii and at a
positive radius, `r ↦ M.cutKernel r s(a,b)` is continuous. -/
theorem continuousAt_cutKernel {r0 : ℝ} (hr0 : 0 < r0) {a b : M.V} (hab : a ≠ b)
    (hoff : r0 ∉ M.S.attainedRadii) :
    ContinuousAt (fun r : ℝ => M.cutKernel r s(a, b)) r0 := by
  have hK : ContinuousAt M.K r0 :=
    M.K_diff.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hr0))
  have hne : M.S.dist a b ≠ r0 := fun h => hoff (h ▸ M.S.mem_attainedRadii_of_dist hab)
  have hfun : (fun r : ℝ => M.cutKernel r s(a, b))
      = fun r : ℝ => FiniteVolume.cutoffProfile M.K r (M.S.dist a b) := by
    funext r
    rw [M.cutKernel_sym2 r a b, ite_eq_right hab]
  rw [hfun]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcont : ContinuousAt (fun r : ℝ => M.K (M.S.dist a b) - M.K r) r0 :=
      continuousAt_const.sub hK
    refine hcont.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.eventually_mem hlt] with r hr
    exact FiniteVolume.cutoffProfile_of_le hr.le
  · have hev : (fun r : ℝ => FiniteVolume.cutoffProfile M.K r (M.S.dist a b))
        =ᶠ[𝓝 r0] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.eventually_mem hgt] with r hr
      exact FiniteVolume.cutoffProfile_of_lt hr
    exact continuousAt_const.congr_of_eventuallyEq hev

/-- **Lipschitz bound for the edge-open probability in the cutoff kernel.** -/
theorem abs_cutProb_sub_le (r r' : ℝ) (e : Sym2 M.V) :
    |(M.cutProb r e : ℝ) - (M.cutProb r' e : ℝ)|
      ≤ (M.betaCrit : ℝ) * |M.cutKernel r e - M.cutKernel r' e| := by
  rw [SourceModelData.cutProb, SourceModelData.cutProb, bernoulliEdgeProb_coe,
    bernoulliEdgeProb_coe]
  have hx : 0 ≤ (M.betaCrit : ℝ) * M.cutKernel r e :=
    mul_nonneg (NNReal.coe_nonneg _) (M.cutKernel_nonneg r e)
  have hy : 0 ≤ (M.betaCrit : ℝ) * M.cutKernel r' e :=
    mul_nonneg (NNReal.coe_nonneg _) (M.cutKernel_nonneg r' e)
  have hkey := abs_exp_neg_sub_exp_neg_le (x := (M.betaCrit : ℝ) * M.cutKernel r e)
    (y := (M.betaCrit : ℝ) * M.cutKernel r' e) hx hy
  have hsub : (M.betaCrit : ℝ) * M.cutKernel r e - (M.betaCrit : ℝ) * M.cutKernel r' e
      = (M.betaCrit : ℝ) * (M.cutKernel r e - M.cutKernel r' e) := by ring
  have hstep : (1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)))
      - (1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e)))
      = Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e))
        - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) := by ring
  calc |(1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)))
        - (1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e)))|
      = |Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e))
          - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e))| := by rw [hstep]
    _ = |Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e))
          - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e))| := abs_sub_comm _ _
    _ ≤ |(M.betaCrit : ℝ) * M.cutKernel r e - (M.betaCrit : ℝ) * M.cutKernel r' e| := hkey
    _ = (M.betaCrit : ℝ) * |M.cutKernel r e - M.cutKernel r' e| := by
        rw [hsub, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]

/-- **The `ℓ¹` variation of the edge-open profile over a fixed finite edge set tends to `0`**
at every positive radius. -/
theorem tendsto_sum_abs_cutProb {r0 : ℝ} (hr0 : 0 < r0) (D : Finset (Sym2 M.V)) :
    Tendsto (fun r : ℝ => ∑ e ∈ D, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)|)
      (𝓝 r0) (𝓝 0) := by
  have hcont : ContinuousAt
      (fun r : ℝ => ∑ e ∈ D, |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)|) r0 := by
    classical
    induction D using Finset.induction_on with
    | empty =>
      have hfun : (fun r : ℝ => ∑ e ∈ (∅ : Finset (Sym2 M.V)),
          |(M.cutProb r e : ℝ) - (M.cutProb r0 e : ℝ)|) = fun _ => 0 := by
        funext r
        simp
      rw [hfun]
      exact continuousAt_const
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (((M.continuousAt_cutProb r0 hr0 a).sub continuousAt_const).abs).add ih
  have h := hcont.tendsto
  have hzero : (∑ e ∈ D, |(M.cutProb r0 e : ℝ) - (M.cutProb r0 e : ℝ)|) = 0 := by
    simp
  simpa only [hzero] using h

/-- **Corner radii exclude edge lengths.**  An off-corner radius is not the length of any
non-loop edge. -/
theorem dist_ne_of_cornerRadii {r0 : ℝ} (hoff : r0 ∉ M.cornerRadii) {a b : M.V}
    (hab : a ≠ b) : M.S.dist a b ≠ r0 := by
  intro h
  refine hoff ?_
  rw [← M.attainedRadii_eq_cornerRadii, ← h]
  exact M.S.mem_attainedRadii_of_dist hab

/-- **Membership in the box edge set.** -/
theorem mem_boxEdges_sym2 (R : ℝ) (a b : M.V) :
    s(a, b) ∈ M.boxEdges R ↔ a ∈ M.ball R ∧ b ∈ M.ball R := by
  rw [SourceModelData.boxEdges, Finset.mem_sym2_iff]
  constructor
  · intro h
    exact ⟨(Set.Finite.mem_toFinset _).mp (h a (Sym2.mem_mk_left a b)),
      (Set.Finite.mem_toFinset _).mp (h b (Sym2.mem_mk_right a b))⟩
  · rintro ⟨ha, hb⟩ c hc
    rcases Sym2.mem_iff.mp hc with rfl | rfl
    · exact (Set.Finite.mem_toFinset _).mpr ha
    · exact (Set.Finite.mem_toFinset _).mpr hb

/-- **Monotonicity of the cutoff law in the radius** on increasing events. -/
theorem cutLaw_mono_of_le {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    {A : Set (Config M.V)} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    (M.cutLaw r) A ≤ (M.cutLaw r') A :=
  longRangeMeasure_mono_kernel (M.cutKernel_mono_r hr hr' h) (M.cutKernel_nonneg r)
    (M.cutKernel_nonneg r') M.betaCrit hA hinc

end SourceModelData

end PercLib.CriticalLRP.Orchestration
