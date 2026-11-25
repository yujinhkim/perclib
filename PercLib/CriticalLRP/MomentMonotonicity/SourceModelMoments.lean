/-
# Definition I.1.5 comparisons at an arbitrary normalized source norm

The reduced-parameter coefficient `1 - K r / K 1` belongs to the raw sup-norm
interface.  It is not used here.  This file proves the monotonicity comparison
for the actual `SourceModelData.cutKernel` at any admissible source norm, by the
pointwise `cutoffProfile_le` bound and the common threshold coupling.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.CutoffMomentConvergence
public import PercLib.CriticalLRP.Orchestration.Defs

set_option autoImplicit false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume CutoffMomentTransfer

/-- The loop-safe cutoff kernel is bounded by the uncut kernel for an arbitrary
admissible source norm.  Loops vanish in both kernels. -/
theorem SourceModelData.cutKernel_le_kernel (M : SourceModelData) {r : ℝ}
    (hr : 0 < r) (e : Sym2 M.V) : M.cutKernel r e ≤ M.kernel e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk,
      SourceModelData.kernel, radialSym_mk]
    by_cases hxy : x = y
    · simp [hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      exact cutoffProfile_le M.K_nonneg (M.S.dist_pos hxy) hr

/-- At zero cutoff, the normalized loop-safe kernel is identically zero. -/
theorem SourceModelData.cutKernel_zero (M : SourceModelData) (e : Sym2 M.V) :
    M.cutKernel 0 e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      exact FiniteVolume.cutoffProfile_of_lt (by have := M.S.dist_pos hxy; linarith)

/-- The uncut comparison also holds at the zero-cutoff boundary. -/
theorem SourceModelData.cutKernel_le_kernel_of_nonneg (M : SourceModelData) {r : ℝ}
    (hr : 0 ≤ r) (e : Sym2 M.V) : M.cutKernel r e ≤ M.kernel e := by
  by_cases hpos : 0 < r
  · exact M.cutKernel_le_kernel hpos e
  · have hzero : r = 0 := le_antisymm (le_of_not_gt hpos) hr
    subst r
    rw [M.cutKernel_zero]
    exact M.kernel_nonneg e

/-- **The general-norm I.4.g7 comparison.**  For `β ≤ γ`, the cutoff law is
stochastically monotone in intensity and is dominated by the uncut law at `γ`.
The conclusion covers increasing measurable events, every natural cluster
moment, and the two-point function.  No moment-finiteness premise is used. -/
theorem SourceModelData.cutoff_mono_beta_and_le_uncut (M : SourceModelData)
    {β γ : NNReal} (hβγ : β ≤ γ) {r : ℝ} (hr : 0 ≤ r) :
    (∀ A : Set (Config M.V), MeasurableSet A → IsIncreasing A →
      longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β A ≤
        longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) γ A ∧
      longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) γ A ≤ M.law γ A) ∧
    (∀ (o : M.V) (k : ℕ),
      (∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)) ≤
        ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (M.cutKernel r)
          (M.cutKernel_nonneg r) γ) ∧
      (∫⁻ ω, clusterVol ω o ^ k
        ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) γ)) ≤
        ∫⁻ ω, clusterVol ω o ^ k ∂(M.law γ)) ∧
    (∀ x y : M.V,
      twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) β x y ≤
        twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) γ x y ∧
      twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) γ x y ≤
        twoPointFunction M.kernel M.kernel_nonneg γ x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA hinc
    exact ⟨longRangeMeasure_mono_apply (M.cutKernel_nonneg r) hβγ hA hinc,
      longRangeMeasure_mono_kernel (M.cutKernel_le_kernel_of_nonneg hr)
        (M.cutKernel_nonneg r) M.kernel_nonneg γ hA hinc⟩
  · intro o k
    exact ⟨lintegral_clusterVol_pow_mono_of_le
        (fun e => bernoulliEdgeProb_mono (M.cutKernel r) (M.cutKernel_nonneg r) hβγ e) o k,
      lintegral_clusterVol_pow_mono_of_le
        (fun e => bernoulliEdgeProb_mono_kernel (M.cutKernel_le_kernel_of_nonneg hr)
          (M.cutKernel_nonneg r) M.kernel_nonneg γ e) o k⟩
  · intro x y
    exact ⟨twoPointFunction_mono (M.cutKernel_nonneg r) hβγ x y,
      longRangeMeasure_mono_kernel (M.cutKernel_le_kernel_of_nonneg hr)
        (M.cutKernel_nonneg r) M.kernel_nonneg γ
        (measurableSet_connects x y) (isIncreasing_connects x y)⟩

/-- The fourth-moment part of the general-norm comparison. -/
theorem SourceModelData.cutoff_fourthMoment_mono_beta_and_le_uncut
    (M : SourceModelData) {β γ : NNReal} (hβγ : β ≤ γ) {r : ℝ} (hr : 0 ≤ r)
    (o : M.V) :
    (∫⁻ ω, clusterVol ω o ^ 4
      ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)) ≤
      ∫⁻ ω, clusterVol ω o ^ 4 ∂(longRangeMeasure (M.cutKernel r)
        (M.cutKernel_nonneg r) γ) ∧
    (∫⁻ ω, clusterVol ω o ^ 4
      ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) γ)) ≤
      ∫⁻ ω, clusterVol ω o ^ 4 ∂(M.law γ) :=
  (M.cutoff_mono_beta_and_le_uncut hβγ hr).2.1 o 4

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_kernel
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_kernel_of_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutoff_mono_beta_and_le_uncut
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutoff_fourthMoment_mono_beta_and_le_uncut

end PercLib.CriticalLRP.Orchestration
