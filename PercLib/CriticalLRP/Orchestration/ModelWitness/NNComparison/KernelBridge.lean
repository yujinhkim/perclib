/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
/-
Bridge from the explicit source-model witness to the paper's long-range kernel.

The witness `Witness.sourceModelWitness d hd α hα` uses the normalized sup norm
`ρ v = 2‖v‖∞` and the source kernel `K r = r^{-d-α}/(d+α)`, hence
`J_w(x,y) = (2‖x-y‖∞)^{-d-α}/(d+α)`.  Here we record the exact relation with the
paper-literal kernel `lrKernel d α` of `CountableProduct/Critical.lean`:
`J_w = c • lrKernel` with `c = rescaleConstant d α = 2^{-d-α}/(d+α) > 0`, and the
resulting rescaling of the parameter `β` in the law, `1 - exp(-β (cJ)) = 1 - exp(-(cβ) J)`,
which is the observable content of the source's normalization convention (Definition I.1.3,
display `(∗)` and the sentence after it: changing the norm and the kernel "changes the value
of `β_c` but does not change other features of the model at criticality").
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.CriticalLRP.Orchestration.ModelWitness.NNComparison.Defs

/-!
# Bridge from the source-model witness kernel to the paper's `lrKernel`

The witness kernel is the paper-literal power law times the positive constant
`rescaleConstant d α`, and rescaling the kernel by a constant rescales the parameter `β`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration.Witness.NNComparison

open PercLib.CriticalLRP Orchestration Witness

/-! ## The witness norm and kernel -/

/-- The normalized sup norm of the witness, evaluated on integer vectors, is twice the
lattice sup norm: `ρ(toVec z) = 2‖z‖`. -/
theorem norm_toVec {d : ℕ} (z : Fin d → ℤ) : ‖toVec z‖ = ‖z‖ := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have h : ‖toVec z i‖ = ‖z i‖ := by
      rw [Int.norm_eq_abs]
      simp [toVec, Real.norm_eq_abs]
    rw [h]
    exact norm_le_pi_norm z i
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [Int.norm_eq_abs]
    have h : |((z i : ℤ) : ℝ)| = ‖toVec z i‖ := by simp [toVec]
    rw [h]
    exact norm_le_pi_norm (toVec z) i

/-- The normalized source distance of the witness is `2‖x-y‖∞`. -/
theorem sourceNormWitness_dist {d : ℕ} (x y : Fin d → ℤ) :
    (sourceNormWitness d).dist x y = 2 * ‖x - y‖ := by
  change 2 * ‖toVec (x - y)‖ = 2 * ‖x - y‖
  rw [norm_toVec]

/-- **The witness kernel is the paper's `lrKernel` rescaled.**  The normalized sup norm
`ρ = 2‖·‖∞` contributes `2^{-d-α}` and the source-normalized derivative
`|K' r| = r^{-d-α-1}` contributes `(d+α)⁻¹`. -/
theorem sourceModelWitness_kernel_apply {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (x y : Fin d → ℤ) :
    (sourceModelWitness d hd α hα).kernel s(x, y) =
      rescaleConstant d α * lrKernel d α s(x, y) := by
  rw [show (sourceModelWitness d hd α hα).kernel s(x, y)
      = radialSym (sourceNormWitness d) (sourceModelWitness d hd α hα).K s(x, y) from rfl]
  rw [radialSym_mk]
  by_cases hxy : x = y
  · subst hxy
    rw [ite_eq_left rfl, lrKernel_diag d hα, mul_zero]
  · rw [ite_eq_right hxy, sourceNormWitness_dist]
    have hexp : (-(d : ℝ) - α) = -((d : ℝ) + α) := by ring
    have hK : (sourceModelWitness d hd α hα).K (2 * ‖x - y‖)
        = (2 * ‖x - y‖) ^ (-(d : ℝ) - α) / ((d : ℝ) + α) := rfl
    rw [hK, hexp, rescaleConstant]
    simp only [lrKernel, Sym2.lift_mk]
    rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
    ring_nf

theorem sourceModelWitness_kernel_eq {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).kernel =
      fun e => rescaleConstant d α * lrKernel d α e := by
  funext e
  induction e using Sym2.ind with
  | _ x y => exact sourceModelWitness_kernel_apply hd α hα x y

/-! ## Rescaling the parameter -/

/-- Rescaling the kernel by `c ≥ 0` rescales the parameter by `c`:
`1 - exp(-β (cJ)) = 1 - exp(-(cβ) J)`. -/
theorem bernoulliEdgeProb_const_mul {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    {c : ℝ} (hc : 0 ≤ c) {β : NNReal}
    (hcJ : ∀ e, 0 ≤ c * J e) (hJ : ∀ e, 0 ≤ J e) :
    bernoulliEdgeProb (fun e => c * J e) hcJ β
      = bernoulliEdgeProb J hJ (Real.toNNReal c * β) := by
  funext e
  apply Subtype.ext
  rw [bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hcβ : ((Real.toNNReal c * β : NNReal) : ℝ) = c * (β : ℝ) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal c hc]
  have harg : -((β : ℝ) * (c * J e)) = -(((Real.toNNReal c * β : NNReal) : ℝ) * J e) := by
    rw [hcβ]; ring
  rw [harg]

theorem longRangeMeasure_const_mul {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (β : NNReal)
    (hcJ : ∀ e, 0 ≤ c * J e) (hJ : ∀ e, 0 ≤ J e) :
    longRangeMeasure (fun e => c * J e) hcJ β
      = longRangeMeasure J hJ (Real.toNNReal c * β) := by
  rw [longRangeMeasure, longRangeMeasure, bernoulliEdgeProb_const_mul J hc hcJ hJ]

theorem infiniteClusterProb_const_mul {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (β : NNReal)
    (hcJ : ∀ e, 0 ≤ c * J e) (hJ : ∀ e, 0 ≤ J e) :
    infiniteClusterProb (fun e => c * J e) hcJ β
      = infiniteClusterProb J hJ (Real.toNNReal c * β) := by
  rw [infiniteClusterProb, infiniteClusterProb, longRangeMeasure_const_mul J hc β hcJ hJ]

/-- Inverting the rescaling: percolation at `γ` for the rescaled kernel is percolation at
`c⁻¹ γ` for the original one. -/
theorem infiniteClusterProb_const_mul_inv {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    {c : ℝ} (hc : 0 < c) (γ : NNReal)
    (hcJ : ∀ e, 0 ≤ c * J e) (hJ : ∀ e, 0 ≤ J e) :
    infiniteClusterProb (fun e => c * J e) hcJ (Real.toNNReal c⁻¹ * γ)
      = infiniteClusterProb J hJ γ := by
  rw [infiniteClusterProb_const_mul J hc.le _ hcJ hJ]
  congr 1
  rw [← mul_assoc, ← Real.toNNReal_mul hc.le, mul_inv_cancel₀ hc.ne', Real.toNNReal_one,
    one_mul]

/-! ## Normalization checks and the direction of the comparison -/

/-- A nearest-neighbour pair of `ℤ^d` sits at normalized source radius `2`
(`ρ = 2‖·‖∞` and the lattice distance is `1`). -/
theorem sourceNormWitness_dist_of_unit {d : ℕ} {x y : Fin d → ℤ} (h : ‖x - y‖ = 1) :
    (sourceNormWitness d).dist x y = 2 := by
  rw [sourceNormWitness_dist, h]
  norm_num

/-- The witness kernel at normalized radius `2`, i.e. on a nearest-neighbour pair:
`K 2 = 2^{-d-α}/(d+α)`. -/
theorem sourceModelWitness_K_two (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    (sourceModelWitness d hd α hα).K 2 = rescaleConstant d α := rfl

/-- Sanity check of the value of the rescaling constant in the lowest case: at `d = 1`,
`α = 1` the witness intensity on a nearest-neighbour pair is `1/8`. -/
theorem rescaleConstant_one_one : rescaleConstant 1 1 = 1 / 8 := by
  rw [rescaleConstant]
  norm_num

/-- **The comparison with nearest-neighbour percolation is not reversible.**  The power law
puts positive intensity on pairs at sup-norm distance `2`, where the nearest-neighbour
intensity vanishes.  Consequently kernel monotonicity can only transport *percolation of the
nearest-neighbour model* to the long-range model (an upper bound on `β_c`); it cannot
transport non-percolation, so nearest-neighbour critical *positivity* cannot yield
`0 < β_c` for the witness by this route. -/
theorem not_lrKernel_le_nnKernel (d : ℕ) (α : ℝ) (i : Fin d) : ¬ lrKernel d α ≤ nnKernel d := by
  intro h
  have hpt := h s(0, fun j => if j = i then (2 : ℤ) else 0)
  simp only [lrKernel, Sym2.lift_mk, nnKernel_mk] at hpt
  have hdist : ‖(0 : Fin d → ℤ) - (fun j => if j = i then (2 : ℤ) else 0)‖ = 2 := by
    refine le_antisymm ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      by_cases hj : j = i
      · rw [hj, Int.norm_eq_abs]
        norm_num
      · rw [Int.norm_eq_abs]
        simp [Pi.sub_apply, hj]
    · have h0 : ‖((0 : Fin d → ℤ) - (fun j => if j = i then (2 : ℤ) else 0)) i‖ = 2 := by
        rw [Int.norm_eq_abs]
        simp
      rw [← h0]
      exact norm_le_pi_norm _ i
  rw [hdist] at hpt
  have hne : ¬ ((2 : ℝ) = 1) := by norm_num
  have hle : (2 : ℝ) ^ (-((d : ℝ) + α)) ≤ 0 := by
    simpa [hne] using hpt
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℝ) + α)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

end PercLib.CriticalLRP.Orchestration.Witness.NNComparison
