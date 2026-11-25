/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The long-range edge law: (2.8) for the model's own probabilities

The repo's model gives an edge with parameters `β, J ≥ 0` the open probability
`longRangeEdgeProbability β J = 1 - exp (-(β * J))` (`FiniteBernoulli.lean`).  This file

* proves that this probability is *strictly* below `1` for **every** `β, J : ℝ` (no side condition:
  `exp` is positive), so the hypothesis `p e < 1` of `meets_pow_bound` — hence of the iterated BK
  inequality `bk_fin` — is met by the model;
* packages `e ↦ longRangeEdgeProbability β (J e)` as a `unitInterval`-valued family `modelP`;
* specialises `meets_pow_bound` (i.e. (2.8) of arXiv:2008.11197v2) to that family.

No claim is made for `p e = 1`: that case does not arise for finite `β J`, but the passage to the
`J e = ∞` / `β = ∞` limits is not formalised here.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.MaxClusterPower
public import PercLib.CriticalLRP.FiniteBernoulli

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP PercLib.CriticalLRP.Percolation Hutchcroft MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
  [Nonempty E]

/-- The model's edge probability is strictly less than `1`, for **all** real `β` and `J`. -/
theorem longRangeEdgeProbability_lt_one (β J : ℝ) : longRangeEdgeProbability β J < 1 := by
  have hpos : 0 < Real.exp (-(β * J)) := Real.exp_pos _
  simp only [longRangeEdgeProbability]
  linarith

/-- The long-range edge probabilities `e ↦ 1 - exp (-(β * J e))` as `unitInterval`-valued
parameters of the Bernoulli edge law. -/
noncomputable def modelP (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    E → unitInterval :=
  fun e => ⟨longRangeEdgeProbability β (J e), longRangeEdgeProbability_mem_Icc hβ (hJ e)⟩

theorem modelP_coe (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (e : E) :
    (modelP J β hβ hJ e : ℝ) = longRangeEdgeProbability β (J e) := rfl

/-- The model's edge probabilities are strictly subcritical, in the form required by `bk_fin`. -/
theorem modelP_lt_one (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e, modelP J β hβ hJ e < 1 := by
  intro e
  have h2 : (modelP J β hβ hJ e : ℝ) < ((1 : unitInterval) : ℝ) := by
    rw [modelP_coe]
    simpa using longRangeEdgeProbability_lt_one β (J e)
  exact h2

/-- **(2.8) of arXiv:2008.11197v2 for the long-range edge law itself**, finite volume, integer
thresholds: with `p e = 1 - exp (-(β * J e))`, `β ≥ 0`, `J ≥ 0`,

  `P_β(|K_max(Λ)| ≥ 3^k lam) ≤ P_β(|K_max(Λ)| ≥ lam) ^ (3^(k-1)+1)`. -/
theorem model_meets_pow_bound (G : BondGraph V E) (Λ : Finset V) {lam k : ℕ}
    (hlam : 2 ≤ lam) (hk : 1 ≤ k) (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (edgeLaw (modelP J β hβ hJ)).real (MaxMeets G Λ (3 ^ k * lam)) ≤
      (edgeLaw (modelP J β hβ hJ)).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1) + 1) :=
  meets_pow_bound G Λ hlam hk _ (modelP_lt_one J β hβ hJ)

end Hutchcroft
