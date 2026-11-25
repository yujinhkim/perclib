/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/Monotone.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
The truncated family is monotone in the cutoff and dominated by the uncut law.

Two fidelity facts that the `ℓ = 3` question turns on:

* `cutTwoPointE_le_twoPointE`, `cutTwoPoint_le_twoPoint`: cutting the kernel off at `r` can
  only lower connection probabilities (production `edgeMeasure_mono_of_le`), so the truncated
  two-point function is dominated by the uncut one at the same parameter;
* `cutTwoPointE_mono_r`, `cutTwoPoint_mono_r`: the truncated family increases with `r`
  (production `cutoffProfile_mono_r`), and `cutThreefold_le_uncutThreefold` lifts the
  domination to the threefold convolution, which is the model-level content of
  `T³_{β_c,r}(0,0) ≤ ∇(0,0)` used to replace the (false) `ℓ = 3` instance of I.4.18.

Nothing is assumed.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.PSD

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- `x ↦ 1 - exp(-β x)` is monotone on `x ≥ 0`. -/
theorem bernoulliEdgeProb_mono_kernel {J J' : Sym2 M.V → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJ' : ∀ e, 0 ≤ J' e) (h : ∀ e, J e ≤ J' e) (e : Sym2 M.V) :
    bernoulliEdgeProb J hJ M.betaCrit e ≤ bernoulliEdgeProb J' hJ' M.betaCrit e := by
  rw [← Subtype.coe_le_coe, bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.2
  have hmul : (M.betaCrit : ℝ) * J e ≤ (M.betaCrit : ℝ) * J' e :=
    mul_le_mul_of_nonneg_left (h e) hβ
  have hexp : Real.exp (-((M.betaCrit : ℝ) * J' e)) ≤ Real.exp (-((M.betaCrit : ℝ) * J e)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The truncated kernel is pointwise at most the full kernel. -/
theorem cutKernel_le_uncut (r : ℝ) (e : Sym2 M.V) :
    M.cutKernel r e ≤ M.kernel e := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy' := M.S.dist_pos (x := x) (y := y)
    rw [SourceModelData.cutKernel, SourceModelData.kernel, cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      rcases lt_or_ge 0 r with hr | hr
      · exact FiniteVolume.cutoffProfile_le M.K_nonneg (hxy' hxy) hr
      · rw [FiniteVolume.cutoffProfile_of_lt (lt_of_le_of_lt hr (hxy' hxy))]
        exact M.K_nonneg _ (hxy' hxy)

/-- The truncated kernel increases with the cutoff. -/
theorem cutKernel_mono_r {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (e : Sym2 M.V) :
    M.cutKernel r e ≤ M.cutKernel r' e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutKernel, cutRadialSym, radialSym_mk, cutKernel, cutRadialSym, radialSym_mk]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      exact FiniteVolume.cutoffProfile_mono_r M.K_antitone hr hr' (M.S.dist_pos hxy) h

/-- Cutting off at `r` can only lower connection probabilities. -/
theorem cutTwoPointE_le_twoPointE (r : ℝ) (x y : M.V) :
    M.cutTwoPointE r x y ≤ M.twoPointE M.betaCrit x y := by
  rw [cutTwoPointE, cutLaw, longRangeMeasure, twoPointE, law, longRangeMeasure]
  exact edgeMeasure_mono_of_le
    (fun e => M.bernoulliEdgeProb_mono_kernel (M.cutKernel_nonneg r) M.kernel_nonneg
      (fun e => M.cutKernel_le_uncut r e) e)
    (measurableSet_connects x y) (isIncreasing_connects x y)

theorem law_le_one (β : ℝ≥0) (s : Set (Config M.V)) : M.law β s ≤ 1 := by
  have h := measure_mono (μ := M.law β) (Set.subset_univ s)
  rwa [measure_univ] at h

theorem cutTwoPoint_le_twoPoint (r : ℝ) (x y : M.V) :
    M.cutTwoPoint r x y ≤ M.twoPoint M.betaCrit x y := by
  rw [cutTwoPoint, twoPoint, Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (M.law_le_one M.betaCrit _))
    (M.cutTwoPointE_le_twoPointE r x y)

/-- The truncated two-point function increases with the cutoff. -/
theorem cutTwoPointE_mono_r {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (x y : M.V) :
    M.cutTwoPointE r x y ≤ M.cutTwoPointE r' x y := by
  rw [cutTwoPointE, cutTwoPointE, cutLaw, cutLaw, longRangeMeasure, longRangeMeasure]
  exact edgeMeasure_mono_of_le
    (fun e => M.bernoulliEdgeProb_mono_kernel (M.cutKernel_nonneg r) (M.cutKernel_nonneg r')
      (fun e => M.cutKernel_mono_r hr hr' h e) e)
    (measurableSet_connects x y) (isIncreasing_connects x y)

theorem cutTwoPoint_mono_r {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (x y : M.V) :
    M.cutTwoPoint r x y ≤ M.cutTwoPoint r' x y := by
  rw [cutTwoPoint, cutTwoPoint, Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (M.cutLaw_le_one r' _))
    (M.cutTwoPointE_mono_r hr hr' h x y)

/-- The `ℓ = 3` convolution of the truncated matrix is dominated by the uncut one, which is
the model-level input the `ℓ = 3` case of I.4.18 has to use in place of the (false) displayed
bound. -/
theorem cutThreefold_le_uncutThreefold (r : ℝ) :
    M.cutThreefold r ≤ M.uncutThreefold M.betaCrit := by
  rw [cutThreefold, uncutThreefold]
  refine ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z => ?_
  gcongr
  · exact M.cutTwoPointE_le_twoPointE r 0 y
  · exact M.cutTwoPointE_le_twoPointE r y z
  · exact M.cutTwoPointE_le_twoPointE r z 0

end SourceModelData

end PercLib.CriticalLRP.Orchestration
