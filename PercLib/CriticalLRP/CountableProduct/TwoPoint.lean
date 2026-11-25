/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The two-point function `τ_β(x,y) = P_β(x ↔ y)` and monotonicity of the law in the kernel.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  The two-point function at `β_c` is the quantity appearing in
hypotheses 2 and 3 of (HD), §I.1.3 p. 9:

  2. `d > 6` and `P_{β_c}(x ↔ y) ⪯ ‖x - y‖^{-d+2}` for all `x ≠ y`;
  3. `d = 6`, `α = 2`, and `P_{β_c}(x ↔ y) ⪯ (log ‖x-y‖)^{-1} ‖x-y‖^{-d+2}`.

The kernel monotonicity `J ≤ J' ⇒ P_β(J) ⪯ P_β(J')` is the stochastic domination used on
p. 7 for the cut-off kernels (`J_r ≤ (1-ε)J`).

No `sorry`, no custom axioms.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.CriticalLRP.CountableProduct.Marks

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

section TwoPoint

variable {V : Type*} [Countable V]

/-- The **two-point function** `τ_β(x,y) = P_β(x ↔ y)`: the probability that `x` and `y` are
connected by a path of open edges. -/
noncomputable def twoPointFunction (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) : ℝ≥0∞ :=
  longRangeMeasure J hJ β {ω : Config V | Connects ω x y}

theorem twoPointFunction_comm (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : V) :
    twoPointFunction J hJ β x y = twoPointFunction J hJ β y x := by
  rw [twoPointFunction, twoPointFunction]
  congr 1
  ext ω
  exact ⟨connects_symm, connects_symm⟩

theorem twoPointFunction_self (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x : V) :
    twoPointFunction J hJ β x x = 1 := by
  rw [twoPointFunction, show {ω : Config V | Connects ω x x} = Set.univ from ?_, measure_univ]
  ext ω
  exact ⟨fun _ => Set.mem_univ _, fun _ => connects_refl ω x⟩

theorem twoPointFunction_le_one (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : V) :
    twoPointFunction J hJ β x y ≤ 1 := by
  rw [twoPointFunction, ← measure_univ (μ := longRangeMeasure J hJ β)]
  exact measure_mono (Set.subset_univ _)

theorem twoPointFunction_mono {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β β' : NNReal}
    (h : β ≤ β') (x y : V) : twoPointFunction J hJ β x y ≤ twoPointFunction J hJ β' x y :=
  longRangeMeasure_mono_apply hJ h (measurableSet_connects x y) (isIncreasing_connects x y)

end TwoPoint

section KernelMono

variable {V : Type*} [Countable V]

/-- Increasing the kernel pointwise increases every edge-open probability. -/
theorem bernoulliEdgeProb_mono_kernel {J J' : Sym2 V → ℝ} (hJJ' : ∀ e, J e ≤ J' e)
    (hJ : ∀ e, 0 ≤ J e) (hJ' : ∀ e, 0 ≤ J' e) (β : NNReal) (e : Sym2 V) :
    bernoulliEdgeProb J hJ β e ≤ bernoulliEdgeProb J' hJ' β e := by
  rw [← Subtype.coe_le_coe, bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have hexp : Real.exp (-((β : ℝ) * J' e)) ≤ Real.exp (-((β : ℝ) * J e)) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hJJ' e]
  linarith

/-- **Stochastic domination under pointwise domination of the kernel**: if `J ≤ J'`, then
`P_β(J)` gives every increasing measurable event no more probability than `P_β(J')`
(p. 7, the domination of the cut-off measure `P_{β_c,r}` by `P_{(1-ε)β_c}` uses the
combination of this with the monotonicity in `β`). -/
theorem longRangeMeasure_mono_kernel {J J' : Sym2 V → ℝ} (hJJ' : ∀ e, J e ≤ J' e)
    (hJ : ∀ e, 0 ≤ J e) (hJ' : ∀ e, 0 ≤ J' e) (β : NNReal)
    {A : Set (Config V)} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    longRangeMeasure J hJ β A ≤ longRangeMeasure J' hJ' β A :=
  edgeMeasure_mono_of_le (fun e => bernoulliEdgeProb_mono_kernel hJJ' hJ hJ' β e) hA hinc

end KernelMono

end PercLib.CriticalLRP
