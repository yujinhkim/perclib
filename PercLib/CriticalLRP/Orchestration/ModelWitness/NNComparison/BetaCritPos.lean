/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
/-
Positivity of `β_c` for the explicit source-model witness.

`SourceModelData.betaCrit = criticalBeta kernel kernel_nonneg` is the infimum of the set of
`β ≥ 0` at which an infinite cluster exists almost surely (Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, §I.1.2).  For the explicit witness of
`Orchestration/ModelWitness/Defs.lean` the kernel is the literal power law
`J_w(x,y) = (2‖x-y‖∞)^{-d-α}/(d+α)`.

Contents:

* `criticalBetaSet_eq_setOf_infiniteClusterProb_pos`: for the project's literal
  `criticalBetaSet = {β | P_β(∃ infinite cluster) = 1}` — the paper's own definition —
  the zero–one law of `CountableProduct/ZeroOne.lean` makes membership *equivalent* to
  `0 < infiniteClusterProb`.  So the set means `θ = 1`, and this is the same as `θ > 0`;
  the two readings cannot disagree.
* `sourceModelWitness_infiniteClusterProb_eq_zero_of_mul_lt_one`: an unconditional
  high-temperature criterion.  The witness has no infinite cluster a.s. at every `β` with
  `(c β) M < 1`, where `c = rescaleConstant d α = 2^{-d-α}/(d+α)` and
  `M = ∑_z ‖z‖∞^{-d-α}`; this is
  `PowerLawHighTemp.lrKernel_infiniteClusterProb_eq_zero` transported across the kernel
  rescaling of `KernelBridge.lean`.
* `sourceModelWitness_exists_pos_infiniteClusterProb_eq_zero`: the same statement in
  existential form, with the explicit parameter `β₀ = (c(M+1))⁻¹ > 0`.
* `sourceModelWitness_betaCrit_pos_of_nonempty`: **`0 < β_c`** given only that the model
  percolates at some parameter.
* `sourceModelWitness_betaCrit_pos_iff_nonempty`: the exact characterisation
  `0 < β_c ⟺ ∃ β, P_β(∃ infinite cluster) = 1` (for `NNReal` the infimum of `∅` is `0`).
  Read carefully: this says the lower half and the upper half of `0 < β_c < ∞` are the
  same obligation in this encoding, not that either half has been proved.
* `infiniteClusterProb_lrKernel_of_nnKernel`: nearest-neighbour percolation on `ℤ^d`
  forces percolation of the power-law model, by pairwise kernel domination.
* `sourceModelWitness_betaCrit_pos_of_NNSupercritical` and
  `sourceModelWitness_betaCrit_pos_and_nonempty_of_NNSupercritical`: the reduction
  `NNSupercritical d → 0 < β_c` for `d ≥ 2`, together with the percolating parameter.

The single remaining input is `NNSupercritical d`, i.e. `p_c(ℤ^d, bond) < 1` (`d ≥ 2`):
supercritical nearest-neighbour bond percolation.  It is not in the campaign tree, and it is
the `β_c < ∞` half of the dichotomy — the other half, non-percolation at small `β`, is
proved here unconditionally.  Note that nearest-neighbour critical *positivity*
(`0 < p_c`) is not what this reduction needs.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Orchestration.ModelWitness.NNComparison.KernelBridge
public import PercLib.CriticalLRP.PowerLawHighTemp

/-!
# Positivity of `β_c` for the explicit source-model witness

The high-temperature half of `0 < β_c < ∞` is proved unconditionally for the witness; the
supercritical half is reduced to the named hypothesis `NNSupercritical d`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration.Witness.NNComparison

open PercLib.CriticalLRP Orchestration Witness

/-! ## `criticalBetaSet` is the set where `θ = 1`, equivalently where `θ > 0` -/

/-- **`criticalBetaSet` means `θ = 1`, and by the zero–one law this is the same as `θ > 0`.**
The project's `criticalBetaSet` is the paper's literal set of parameters at which an infinite
cluster exists almost surely; `percolationEventProb_zero_or_one` shows the percolation
probability only takes the values `0` and `1`, so "almost sure percolation" and "positive
probability of percolation" define literally the same subset of `NNReal`. -/
theorem mem_criticalBetaSet_iff_infiniteClusterProb_pos {V : Type*} [Countable V]
    {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e} (β : NNReal) :
    β ∈ criticalBetaSet J hJ ↔ 0 < infiniteClusterProb J hJ β := by
  rw [mem_criticalBetaSet_iff]
  constructor
  · rintro h
    rw [h]
    exact zero_lt_one
  · intro h
    rcases percolationEventProb_zero_or_one J hJ β with h0 | h1
    · rw [h0] at h
      exact absurd h (lt_irrefl (0 : ℝ≥0∞))
    · exact h1

/-- The set-level form of `mem_criticalBetaSet_iff_infiniteClusterProb_pos`. -/
theorem criticalBetaSet_eq_setOf_infiniteClusterProb_pos {V : Type*} [Countable V]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) :
    criticalBetaSet J hJ = {β : NNReal | 0 < infiniteClusterProb J hJ β} :=
  Set.ext fun β => mem_criticalBetaSet_iff_infiniteClusterProb_pos β

/-- The named nearest-neighbour hypothesis is exactly nonemptiness of the
nearest-neighbour percolation set, i.e. `p_c(ℤ^d, bond) < ∞`. -/
theorem NNSupercritical_iff_criticalBetaSet_nonempty (d : ℕ) :
    NNSupercritical d ↔ (criticalBetaSet (nnKernel d) (nnKernel_nonneg d)).Nonempty :=
  Iff.rfl

/-! ## Pointwise congruence and the exact rescaling of the law -/

theorem longRangeMeasure_congr {V : Type*} [Countable V] {J J' : Sym2 V → ℝ}
    (h : ∀ e, J e = J' e) (hJ : ∀ e, 0 ≤ J e) (hJ' : ∀ e, 0 ≤ J' e) (β : NNReal) :
    longRangeMeasure J hJ β = longRangeMeasure J' hJ' β := by
  rw [longRangeMeasure, longRangeMeasure]
  congr 1
  funext e
  apply Subtype.ext
  rw [bernoulliEdgeProb_coe, bernoulliEdgeProb_coe, h e]

/-- The law of the witness at `β` is the paper's law for `lrKernel` at the rescaled
parameter `cβ`, where `J_w = c • lrKernel` and `c` is any constant realising the kernel
identity. -/
theorem sourceModelWitness_law_eq_const_mul {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {c : ℝ} (hc : 0 ≤ c)
    (hker : (sourceModelWitness d hd α hα).kernel = fun e => c * lrKernel d α e)
    (β : NNReal) :
    (sourceModelWitness d hd α hα).law β
      = longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α) (Real.toNNReal c * β) := by
  rw [show (sourceModelWitness d hd α hα).law β
      = longRangeMeasure (sourceModelWitness d hd α hα).kernel
          (sourceModelWitness d hd α hα).kernel_nonneg β from rfl]
  rw [← longRangeMeasure_const_mul (lrKernel d α) hc β
    (fun e => mul_nonneg hc (lrKernel_nonneg d α e)) (lrKernel_nonneg d α)]
  exact longRangeMeasure_congr (fun e => congrFun hker e)
    (sourceModelWitness d hd α hα).kernel_nonneg
    (fun e => mul_nonneg hc (lrKernel_nonneg d α e)) β

/-- **The exact rescaling of the witness law**, with the explicit constant
`c = rescaleConstant d α = 2^{-d-α}/(d+α)` and no hypothesis about the kernel. -/
theorem sourceModelWitness_law_eq_lrKernel_law {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (β : NNReal) :
    (sourceModelWitness d hd α hα).law β
      = longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α)
          (Real.toNNReal (rescaleConstant d α) * β) :=
  sourceModelWitness_law_eq_const_mul hd α hα (rescaleConstant_pos hα).le
    (sourceModelWitness_kernel_eq hd α hα) β

/-- `cβ (c⁻¹ γ) = γ` for the rescaling of the parameter. -/
theorem toNNReal_mul_inv_mul {c : ℝ} (hc : 0 < c) (γ : NNReal) :
    Real.toNNReal c * (Real.toNNReal c⁻¹ * γ) = γ := by
  rw [← mul_assoc, ← Real.toNNReal_mul hc.le, mul_inv_cancel₀ hc.ne', Real.toNNReal_one,
    one_mul]

/-! ## High temperature: no percolation at small `β` -/

/-- The row mass `M = ∑_z ‖z‖∞^{-d-α}` appearing in the high-temperature criterion is a
finite sum: the power-law profile is summable on `ℤ^d` as soon as the exponent exceeds `d`
(`PowerLawHighTemp.summable_powerProfile`).  So `(c β) M < 1` is a genuine constraint on `β`
and not a degenerate one. -/
theorem summable_sourceModelWitness_rowMass {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    Summable (fun z : Fin d → ℤ => (FiniteVolume.linfNorm z : ℝ) ^ (-((d : ℝ) + α))) :=
  PowerLawHighTemp.summable_powerProfile hd (by linarith)

/-- **High-temperature non-percolation for the witness.**  The witness has no infinite
cluster almost surely at every parameter `β` whose rescaled value satisfies `(c β) M < 1`,
where `c = rescaleConstant d α` and `M = ∑_z ‖z‖∞^{-d-α}` is the row mass. -/
theorem sourceModelWitness_infiniteClusterProb_eq_zero_of_mul_lt_one
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : NNReal}
    (hβ : ((Real.toNNReal (rescaleConstant d α) * β : NNReal) : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (FiniteVolume.linfNorm z : ℝ) ^
        (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) :
    infiniteClusterProb (sourceModelWitness d hd α hα).kernel
      (sourceModelWitness d hd α hα).kernel_nonneg β = 0 := by
  have hlaw := sourceModelWitness_law_eq_lrKernel_law hd α hα β
  have hz := PowerLawHighTemp.lrKernel_infiniteClusterProb_eq_zero (d := d) hd hα hβ
  have hgoal := congrArg (fun μ : Measure (Config (Fin d → ℤ)) =>
    μ (existsInfiniteClusterEvent (Fin d → ℤ))) hlaw
  exact hgoal.trans hz

/-- **Unconditional high-temperature non-percolation for the witness.**  There is an
explicit `β₀ > 0` at which the witness almost surely has no infinite cluster.  The row mass
`M = ∑_z ‖z‖∞^{-d-α}` is finite, and `β₀ = (c(M+1))⁻¹` with `c = rescaleConstant d α` puts
`c β₀ M = M/(M+1) < 1` inside the high-temperature region of
`PowerLawHighTemp.lrKernel_infiniteClusterProb_eq_zero`. -/
theorem sourceModelWitness_exists_pos_infiniteClusterProb_eq_zero
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : NNReal, 0 < β₀ ∧ infiniteClusterProb (sourceModelWitness d hd α hα).kernel
        (sourceModelWitness d hd α hα).kernel_nonneg β₀ = 0 := by
  classical
  set M : ℝ := ∑' z : Fin d → ℤ, (FiniteVolume.linfNorm z : ℝ) ^ (-((d : ℝ) + α)) with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun z => Real.rpow_nonneg (by positivity) _
  set c : ℝ := rescaleConstant d α with hc
  have hcpos : 0 < c := rescaleConstant_pos hα
  set β₀ : NNReal := ⟨1 / (c * (M + 1)), le_of_lt (by positivity)⟩ with hβ₀
  have hβ₀pos : 0 < β₀ := by
    rw [← NNReal.coe_pos]
    change (0 : ℝ) < 1 / (c * (M + 1))
    positivity
  refine ⟨β₀, hβ₀pos, sourceModelWitness_infiniteClusterProb_eq_zero_of_mul_lt_one hd hα ?_⟩
  have hval : ((Real.toNNReal c * β₀ : NNReal) : ℝ) = 1 / (M + 1) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal c hcpos.le]
    change c * (1 / (c * (M + 1))) = 1 / (M + 1)
    field_simp
  rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, NNReal.coe_one,
    NNReal.coe_mul, hval, ← hM, Real.coe_toNNReal M hM0]
  rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
  linarith

/-! ## `β_c > 0` from nonemptiness of the percolation set -/

/-- **`β_c > 0` for the witness.**  The only input is that percolation happens at some
parameter; the high-temperature end is unconditional. -/
theorem sourceModelWitness_betaCrit_pos_of_nonempty (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α)
    (hne : (criticalBetaSet (sourceModelWitness d hd α hα).kernel
      (sourceModelWitness d hd α hα).kernel_nonneg).Nonempty) :
    0 < (sourceModelWitness d hd α hα).betaCrit := by
  obtain ⟨β₀, hβ₀, hzero⟩ := sourceModelWitness_exists_pos_infiniteClusterProb_eq_zero hd hα
  exact lt_of_lt_of_le hβ₀
    (le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty hne hzero)

/-- **Exact characterisation for the witness**: `β_c > 0` is equivalent to the existence of
a parameter at which the model percolates.  (For `NNReal` the infimum of the empty set is
`0`, so once the high-temperature end is known, positivity of the infimum is exactly
nonemptiness of the percolation set.) -/
theorem sourceModelWitness_betaCrit_pos_iff_nonempty (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    0 < (sourceModelWitness d hd α hα).betaCrit ↔
      (criticalBetaSet (sourceModelWitness d hd α hα).kernel
        (sourceModelWitness d hd α hα).kernel_nonneg).Nonempty := by
  refine ⟨fun h => ?_, sourceModelWitness_betaCrit_pos_of_nonempty d hd α hα⟩
  by_contra hne
  have hempty : criticalBetaSet (sourceModelWitness d hd α hα).kernel
      (sourceModelWitness d hd α hα).kernel_nonneg = ∅ := by
    rwa [Set.not_nonempty_iff_eq_empty] at hne
  have h0 : (sourceModelWitness d hd α hα).betaCrit = 0 := by
    change sInf (criticalBetaSet (sourceModelWitness d hd α hα).kernel
      (sourceModelWitness d hd α hα).kernel_nonneg) = 0
    rw [hempty]
    simp
  rw [h0] at h
  exact lt_irrefl (0 : NNReal) h

/-! ## Nearest-neighbour domination -/

/-- The nearest-neighbour intensity is dominated by the power law: on a nearest-neighbour
pair the power law equals `1`, elsewhere the nearest-neighbour intensity is `0`.  No
hypothesis on `α` is needed: the exponent only enters through `1^p = 1`. -/
theorem nnKernel_le_lrKernel (d : ℕ) (α : ℝ) : nnKernel d ≤ lrKernel d α := by
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    change (if ‖x - y‖ = 1 then (1 : ℝ) else 0) ≤ ‖x - y‖ ^ (-((d : ℝ) + α))
    split_ifs with h
    · rw [h, Real.one_rpow]
    · exact Real.rpow_nonneg (norm_nonneg _) _

/-- Pairwise domination of kernels implies domination of the percolation probabilities at
the same parameter (stochastic monotonicity of the edge measure). -/
theorem infiniteClusterProb_mono_kernel {V : Type*} [Countable V]
    {J J' : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (h : ∀ e, J e ≤ J' e)
    (hJ' : ∀ e, 0 ≤ J' e) (β : NNReal) :
    infiniteClusterProb J hJ β ≤ infiniteClusterProb J' hJ' β := by
  rw [infiniteClusterProb, infiniteClusterProb]
  refine edgeMeasure_mono_of_le (fun e => ?_) measurableSet_existsInfiniteCluster
    isIncreasing_existsInfiniteCluster
  rw [← Subtype.coe_le_coe, bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have hmul : (β : ℝ) * J e ≤ (β : ℝ) * J' e :=
    mul_le_mul_of_nonneg_left (h e) hβ
  have hexp : Real.exp (-((β : ℝ) * J' e)) ≤ Real.exp (-((β : ℝ) * J e)) :=
    Real.exp_le_exp.2 (by linarith)
  linarith

/-- Percolation of the nearest-neighbour model forces percolation of the power-law model at
the same parameter. -/
theorem infiniteClusterProb_lrKernel_of_nnKernel {d : ℕ} {α : ℝ}
    {γ : NNReal} (hγ : infiniteClusterProb (nnKernel d) (nnKernel_nonneg d) γ = 1) :
    infiniteClusterProb (lrKernel d α) (lrKernel_nonneg d α) γ = 1 := by
  have hmono := infiniteClusterProb_mono_kernel (nnKernel_nonneg d) (nnKernel_le_lrKernel d α)
    (lrKernel_nonneg d α) γ
  rw [hγ] at hmono
  exact le_antisymm (infiniteClusterProb_le_one _ _ _) hmono

/-! ## Transfer of percolation between the witness and `lrKernel` -/

/-- The percolation sets of the witness and of the paper's `lrKernel` are nonempty
simultaneously: the kernels differ by the positive constant `2^{-d-α}/(d+α)`, which is
absorbed by rescaling `β`. -/
theorem sourceModelWitness_percolation_iff_lrKernel (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    (∃ β : NNReal, infiniteClusterProb (sourceModelWitness d hd α hα).kernel
        (sourceModelWitness d hd α hα).kernel_nonneg β = 1) ↔
      ∃ γ : NNReal, infiniteClusterProb (lrKernel d α) (lrKernel_nonneg d α) γ = 1 := by
  have hcpos : 0 < rescaleConstant d α := rescaleConstant_pos hα
  have key : ∀ β : NNReal, infiniteClusterProb (sourceModelWitness d hd α hα).kernel
      (sourceModelWitness d hd α hα).kernel_nonneg β
      = longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α)
          (Real.toNNReal (rescaleConstant d α) * β)
          (existsInfiniteClusterEvent (Fin d → ℤ)) := fun β =>
    congrArg (fun μ : Measure (Config (Fin d → ℤ)) =>
      μ (existsInfiniteClusterEvent (Fin d → ℤ)))
      (sourceModelWitness_law_eq_lrKernel_law hd α hα β)
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨Real.toNNReal (rescaleConstant d α) * β, ?_⟩
    exact (key β).symm.trans hβ
  · rintro ⟨γ, hγ⟩
    refine ⟨Real.toNNReal (rescaleConstant d α)⁻¹ * γ, ?_⟩
    have hmiddle : longRangeMeasure (lrKernel d α) (lrKernel_nonneg d α)
        (Real.toNNReal (rescaleConstant d α) *
          (Real.toNNReal (rescaleConstant d α)⁻¹ * γ))
          (existsInfiniteClusterEvent (Fin d → ℤ)) = 1 := by
      rw [toNNReal_mul_inv_mul hcpos γ]
      exact hγ
    exact (key (Real.toNNReal (rescaleConstant d α)⁻¹ * γ)).trans hmiddle

/-- **Positivity of the witness's `β_c` is equivalent to the paper's `lrKernel` model
percolating at some parameter.**  The right-hand side is *literally* the `hne` hypothesis of
the production theorem `PowerLawHighTemp.lrKernel_criticalBeta_pos_of_nonempty`, so the
witness's `0 < β_c` and the paper-literal `0 < β_c` stand or fall together, and the missing
supercritical half (`β_c < ∞`) is the same obligation in both formulations. -/
theorem sourceModelWitness_betaCrit_pos_iff_lrKernel_nonempty (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    0 < (sourceModelWitness d hd α hα).betaCrit ↔
      (criticalBetaSet (lrKernel d α) (lrKernel_nonneg d α)).Nonempty := by
  rw [sourceModelWitness_betaCrit_pos_iff_nonempty]
  exact sourceModelWitness_percolation_iff_lrKernel d hd α hα

/-! ## The conditional reduction -/

/-- **`β_c > 0` for the explicit witness, conditional on nearest-neighbour
supercriticality.**  For `d ≥ 2`, percolation of the unit nearest-neighbour intensity on
`ℤ^d` at some parameter `γ` (that is, `p_c(ℤ^d, bond) < 1`) forces
`0 < (sourceModelWitness d hd α hα).betaCrit`.

The nearest-neighbour input `NNSupercritical d` is the only unproved ingredient;
everything else, including the high-temperature end and the kernel rescaling, is proved
here. -/
theorem sourceModelWitness_betaCrit_pos_of_NNSupercritical (d : ℕ) (hd2 : 2 ≤ d)
    (α : ℝ) (hα : 0 < α) (hNN : NNSupercritical d) :
    0 < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit := by
  have hd : 1 ≤ d := le_trans (by norm_num) hd2
  obtain ⟨γ, hγ⟩ := hNN
  have hlr : infiniteClusterProb (lrKernel d α) (lrKernel_nonneg d α) γ = 1 :=
    infiniteClusterProb_lrKernel_of_nnKernel hγ
  obtain ⟨β, hβ⟩ := (sourceModelWitness_percolation_iff_lrKernel d hd α hα).mpr ⟨γ, hlr⟩
  exact sourceModelWitness_betaCrit_pos_of_nonempty d hd α hα ⟨β, hβ⟩

/-- **The two-sided conclusion `0 < β_c < ∞`** for the witness, conditional on
nearest-neighbour supercriticality: the percolation set is nonempty (the `β_c < ∞` content in
an `NNReal` encoding) *and* the critical parameter is strictly positive. -/
theorem sourceModelWitness_betaCrit_pos_and_nonempty_of_NNSupercritical (d : ℕ) (hd2 : 2 ≤ d)
    (α : ℝ) (hα : 0 < α) (hNN : NNSupercritical d) :
    (criticalBetaSet (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).kernel
        (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).kernel_nonneg).Nonempty ∧
      0 < (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit := by
  have hd : 1 ≤ d := le_trans (by norm_num) hd2
  obtain ⟨γ, hγ⟩ := hNN
  have hlr : infiniteClusterProb (lrKernel d α) (lrKernel_nonneg d α) γ = 1 :=
    infiniteClusterProb_lrKernel_of_nnKernel hγ
  obtain ⟨β, hβ⟩ := (sourceModelWitness_percolation_iff_lrKernel d hd α hα).mpr ⟨γ, hlr⟩
  exact ⟨⟨β, hβ⟩, sourceModelWitness_betaCrit_pos_of_nonempty d hd α hα ⟨β, hβ⟩⟩

/-- **The target statement in the form `β_c ≠ 0`**, conditional on nearest-neighbour
supercriticality. -/
theorem sourceModelWitness_betaCrit_ne_zero_of_NNSupercritical (d : ℕ) (hd2 : 2 ≤ d)
    (α : ℝ) (hα : 0 < α) (hNN : NNSupercritical d) :
    (sourceModelWitness d (le_trans (by norm_num) hd2) α hα).betaCrit ≠ 0 :=
  ne_of_gt (sourceModelWitness_betaCrit_pos_of_NNSupercritical d hd2 α hα hNN)

end PercLib.CriticalLRP.Orchestration.Witness.NNComparison
