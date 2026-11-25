/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Stochastic monotonicity of the finite Bernoulli law, for Hutchcroft,
"Critical long-range percolation I", arXiv:2508.18807v1.

Definition I.1.5 uses the cut-off kernel `J_r` and asserts: "for every `r < ∞`
there exists `ε = ε(r) > 0` such that `J_r(x,y) ≤ (1-ε)J(x,y)` for every
`x ≠ y`, so that `P_{β_c,r}` is stochastically dominated by the subcritical
measure `P_{(1-ε)β_c}`".

`KernelGeometry.cutoffProfile_dominated` supplies the pointwise kernel
inequality. This file supplies the passage from *pointwise domination of the
edge probabilities* to *stochastic domination of the laws*, i.e.

`p ≤ q` pointwise and `X` increasing ⟹ `E_p X ≤ E_q X`,

proved by differentiating along the line `t ↦ p + t (q - p)`: the derivative is
`∑_e (q_e - p_e) · pivotalMass_e ≥ 0` by `RussoFinite.pivotalMass_nonneg`, and
a function with nonnegative derivative on `[0,1]` is monotone
(`monotoneOn_of_deriv_nonneg`).

No `sorry`, no extra axioms.
-/
module

public import PercLib.CriticalLRP.RussoFinite
public import PercLib.CriticalLRP.KernelGeometry
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `1 - e^{-βJ}` is increasing in the product `βJ`. -/
theorem longRangeEdgeProbability_le_of_mul_le {β₁ J₁ β₂ J₂ : ℝ}
    (h : β₁ * J₁ ≤ β₂ * J₂) :
    longRangeEdgeProbability β₁ J₁ ≤ longRangeEdgeProbability β₂ J₂ := by
  have hle : -(β₂ * J₂) ≤ -(β₁ * J₁) := neg_le_neg h
  have hexp : Real.exp (-(β₂ * J₂)) ≤ Real.exp (-(β₁ * J₁)) := Real.exp_le_exp.mpr hle
  unfold longRangeEdgeProbability
  linarith

/-- The cut-off profile is nonnegative for every positive `r` (it vanishes for
`s > r` and is `J(s) - J(r) ≥ 0` otherwise). -/
theorem cutoffProfile_nonneg_of_pos {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    {r s : ℝ} (hs : 0 < s) (hr : 0 < r) : 0 ≤ cutoffProfile K r s := by
  rcases le_or_gt s r with h | h
  · exact cutoffProfile_nonneg hK hs hr h
  · rw [cutoffProfile_of_lt h]

/-- Derivative of the edge probability along the line `p + t (q - p)`. -/
theorem hasDerivAt_linePath (p q : E → ℝ) (e : E) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => p e + t' * (q e - p e)) (q e - p e) t := by
  have h : HasDerivAt (fun t' : ℝ => t' * (q e - p e)) (1 * (q e - p e)) t :=
    (hasDerivAt_id t).mul_const (q e - p e)
  have h2 := h.const_add (p e)
  simpa [one_mul] using h2

/-- The edge probabilities along the line `p + t (q - p)` stay in `[0,1]` when
`0 ≤ p ≤ q ≤ 1` and `t ∈ [0,1]`. -/
theorem linePath_mem_Icc {p q : E → ℝ} {e : E} {t : ℝ}
    (hp0 : 0 ≤ p e) (hpq : p e ≤ q e) (hq1 : q e ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ p e + t * (q e - p e) ∧ p e + t * (q e - p e) ≤ 1 := by
  obtain ⟨ht0, ht1⟩ := ht
  have hdiff : 0 ≤ q e - p e := by linarith
  constructor
  · have : 0 ≤ t * (q e - p e) := mul_nonneg ht0 hdiff
    linarith
  · have h1 : t * (q e - p e) ≤ 1 * (q e - p e) :=
      mul_le_mul_of_nonneg_right ht1 hdiff
    nlinarith

/-- **Stochastic monotonicity of the finite Bernoulli law**: if `0 ≤ p ≤ q ≤ 1`
pointwise, then for every increasing observable `X` the expectation under `q`
dominates that under `p`. -/
theorem expectation_mono_of_le {p q : E → ℝ} (hp0 : ∀ e, 0 ≤ p e)
    (hpq : ∀ e, p e ≤ q e) (hq1 : ∀ e, q e ≤ 1) {X : Configuration E → ℝ}
    (hX : Monotone X) : expectation p X ≤ expectation q X := by
  classical
  set f : ℝ → ℝ := fun t => expectation (fun e => p e + t * (q e - p e)) X with hf
  set g : ℝ → ℝ := fun t =>
    ∑ e, (q e - p e) * pivotalMass (fun e => p e + t * (q e - p e)) e X with hg
  have hderiv : ∀ t : ℝ, HasDerivAt f (g t) t := by
    intro t
    have h := hasDerivAt_expectation (P := fun e t' => p e + t' * (q e - p e))
      (P' := fun e => q e - p e) (fun e => hasDerivAt_linePath p q e t) X
    simpa [hf, hg] using h
  have hg_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t := by
    intro t ht
    refine Finset.sum_nonneg fun e _ => ?_
    have h1 : 0 ≤ q e - p e := by linarith [hpq e]
    have h2 : 0 ≤ pivotalMass (fun e => p e + t * (q e - p e)) e X := by
      refine pivotalMass_nonneg (fun e' => ?_) (fun e' => ?_) hX e
      · exact (linePath_mem_Icc (hp0 e') (hpq e') (hq1 e') ht).1
      · exact (linePath_mem_Icc (hp0 e') (hpq e') (hq1 e') ht).2
    exact mul_nonneg h1 h2
  have hdiff : Differentiable ℝ f := fun t => (hderiv t).differentiableAt
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hdiff.continuous.continuousOn
      hdiff.differentiableOn ?_
    intro t ht
    rw [(hderiv t).deriv]
    exact hg_nonneg t (interior_subset ht)
  have h01 : f 0 ≤ f 1 :=
    hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  have h0 : f 0 = expectation p X := by
    simp [hf]
  have h1 : f 1 = expectation q X := by
    simp only [hf]
    congr 1
    funext e
    ring
  rw [h0, h1] at h01
  exact h01

/-- Event form: if `p ≤ q` pointwise then any increasing event is at least as
likely under `q`. -/
theorem probability_mono_of_le {p q : E → ℝ} (hp0 : ∀ e, 0 ≤ p e)
    (hpq : ∀ e, p e ≤ q e) (hq1 : ∀ e, q e ≤ 1) (A : Set (Configuration E))
    (hA : ∀ ⦃s⦄, s ∈ A → ∀ ⦃t⦄, s ⊆ t → t ∈ A) :
    probability p A ≤ probability q A := by
  classical
  have key : ∀ s t : Configuration E, s ⊆ t →
      (if s ∈ A then (1 : ℝ) else 0) ≤ if t ∈ A then 1 else 0 := by
    intro s t hst
    by_cases hs : s ∈ A
    · have ht : t ∈ A := hA hs hst
      rw [ite_eq_left hs, ite_eq_left ht]
    · rw [ite_eq_right hs]
      split <;> norm_num
  have hmono : Monotone (fun s : Configuration E => if s ∈ A then (1 : ℝ) else 0) :=
    fun s t hst => key s t hst
  simpa only [probability] using expectation_mono_of_le hp0 hpq hq1 hmono

/-- **Stochastic domination for the cut-off model in `r`**: for `0 < r ≤ r'`
and an increasing observable, the cut-off law at `r` is dominated by the one
at `r'`. -/
theorem expectation_cutoff_mono_r {len : E → ℝ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {β r r' : ℝ} (hβ : 0 ≤ β) (hr : 0 < r)
    (hr' : 0 < r') (hrr' : r ≤ r') (hlen : ∀ e, 0 < len e) {X : Configuration E → ℝ}
    (hX : Monotone X) :
    expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) X
      ≤ expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e))) X := by
  refine expectation_mono_of_le ?_ ?_ ?_ hX
  · intro e
    exact longRangeEdgeProbability_nonneg hβ (cutoffProfile_nonneg_of_pos hK (hlen e) hr)
  · intro e
    exact longRangeEdgeProbability_mono_J hβ (cutoffProfile_mono_r hK hr hr' (hlen e) hrr')
  · intro e
    exact longRangeEdgeProbability_le_one hβ
      (cutoffProfile_nonneg_of_pos hK (hlen e) hr')

/-- **Stochastic domination for the cut-off model in the kernel.** If the
cut-off kernel is pointwise at most `(1-ε)` times a nonnegative kernel `K'`,
and it is nonnegative, then the cut-off law at `β` is dominated by the law with
kernel `K'` at parameter `(1-ε)β`. This is the paper's "so that `P_{β_c,r}` is
stochastically dominated by the subcritical measure `P_{(1-ε)β_c}`". -/
theorem expectation_cutoff_dominated {len : E → ℝ} {K' : E → ℝ} {K : ℝ → ℝ} {β ε : ℝ}
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hK'0 : ∀ e, 0 ≤ K' e)
    (hprof0 : ∀ e, 0 ≤ cutoffProfile K r (len e))
    (hdom : ∀ e, cutoffProfile K r (len e) ≤ (1 - ε) * K' e)
    {X : Configuration E → ℝ} (hX : Monotone X) :
    expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) X
      ≤ expectation (fun e => longRangeEdgeProbability ((1 - ε) * β) (K' e)) X := by
  have hβ' : 0 ≤ (1 - ε) * β := mul_nonneg (by linarith) hβ
  refine expectation_mono_of_le ?_ ?_ ?_ hX
  · intro e
    exact longRangeEdgeProbability_nonneg hβ (hprof0 e)
  · intro e
    refine longRangeEdgeProbability_le_of_mul_le ?_
    have hle : β * cutoffProfile K r (len e) ≤ β * ((1 - ε) * K' e) :=
      mul_le_mul_of_nonneg_left (hdom e) hβ
    calc β * cutoffProfile K r (len e) ≤ β * ((1 - ε) * K' e) := hle
      _ = ((1 - ε) * β) * K' e := by ring
  · intro e
    exact longRangeEdgeProbability_le_one hβ' (hK'0 e)

/-- **Monotonicity in `β`**: for `0 ≤ β ≤ β'`, a nonnegative kernel and
increasing `X`, the law at `β` is dominated by the law at `β'`. -/
theorem expectation_mono_beta {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e) {β β' : ℝ}
    (hβ : 0 ≤ β) (hββ' : β ≤ β') {X : Configuration E → ℝ} (hX : Monotone X) :
    expectation (fun e => longRangeEdgeProbability β (J e)) X
      ≤ expectation (fun e => longRangeEdgeProbability β' (J e)) X := by
  refine expectation_mono_of_le ?_ ?_ ?_ hX
  · intro e
    exact longRangeEdgeProbability_nonneg hβ (hJ e)
  · intro e
    exact longRangeEdgeProbability_mono_beta (hJ e) hββ'
  · intro e
    exact longRangeEdgeProbability_le_one (le_trans hβ hββ') (hJ e)

end PercLib.CriticalLRP.FiniteVolume
