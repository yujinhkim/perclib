/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The `r`-derivative of a cutoff-model expectation: Lemma I.4.1, abstract part.

Hutchcroft, "Critical long-range percolation I", arXiv:2508.18807v1, Lemma I.4.1
asserts

  ∂/∂r E_{β,r}|K|^p = β|J'(r)| ∑_{ℓ=0}^{p-1} binom(p,ℓ)
      E_{β,r}[ |K|^{ℓ+1} ∑_{y ∈ B_r} 1(y ∉ K) |K_y|^{p−ℓ} ],

and the proof has two ingredients: Russo's formula in the form

  ∂/∂r E_{β,r} X = β|J'(r)| E_{β,r}[ ∑_{x∈K} ∑_{y ∈ B_r(x)} 1(y ∉ K)
        (X(ω with {x,y} open) − X(ω)) ],

with the bare factor `β|J'(r)|`, and then the mass-transport principle plus the
binomial expansion. This file proves the first ingredient exactly, for an
arbitrary observable `X` of the finite edge configuration, and with the
open-edge probabilities of the cutoff kernel of Definition I.1.5.

The key point is the cancellation that produces the bare `β|J'(r)|`: the
derivative of the cutoff edge probability is `β|J'(r)|(1 − q_e)`, and the
`(1 − q_e)` combines with the sliced weight into the full product law
restricted to configurations in which `e` is closed. See
`one_sub_mul_pivotalMass`.
-/
module

public import PercLib.CriticalLRP.RussoFinite
public import PercLib.CriticalLRP.KernelGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset Filter Topology

namespace PercLib.CriticalLRP.FiniteVolume

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `(1 − q_e)` times the slice mass is the full law restricted to `e` closed. -/
theorem one_sub_mul_pivotalMass (q : E → ℝ) (e : E) (X : Configuration E → ℝ) :
    (1 - q e) * pivotalMass q e X
      = ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw q τ * (X (insert e τ) - X τ) := by
  classical
  rw [pivotalMass, Finset.mul_sum]
  refine sum_congr rfl fun τ hτ => ?_
  rw [mem_filter] at hτ
  have hnot : e ∉ τ := hτ.2
  have hlaw : configurationLaw q τ = (1 - q e) * sliceWeight q e τ := by
    rw [configurationLaw_eq_sliceWeight q e τ]
    simp [hnot]
  rw [hlaw]; ring

/-- Derivative in `r` of the open probability of a single edge of length `s`
under the cutoff kernel: it is `β|J'(r)|(1 − q)` when `s < r` and `0` when
`s > r`. (At `s = r` the function has a corner; see the faithfulness note in
`KernelGeometry`.) -/
theorem hasDerivAt_cutoffEdgeProbability_if {K : ℝ → ℝ} {K' r s : ℝ} (hne : s ≠ r)
    (hK : HasDerivAt K (-K') r) (β : ℝ) :
    HasDerivAt (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (if s ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r s)) else 0) r := by
  rcases lt_or_gt_of_ne hne with hsr | hrs
  · rw [ite_eq_left hsr.le]
    exact hasDerivAt_cutoffEdgeProbability hsr hK β
  · rw [ite_eq_right (not_le.mpr hrs)]
    have hev : ∀ᶠ r' in 𝓝 r, r' < s := eventually_lt_nhds hrs
    refine (hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with r' hr'
    rw [cutoffProfile_of_lt hr', longRangeEdgeProbability_zero_right]

/-- Derivative of the cutoff-model expectation. This is Russo's formula with
the paper's constant `β|J'(r)|`: the sum runs over the edges of length `≤ r`
whose state is pivotal for `X`, weighted by the full cutoff law. -/
theorem hasDerivAt_expectation_cutoff
    (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ) {r β : ℝ}
    (hne : ∀ e, len e ≠ r)
    (hK : HasDerivAt K (-K') r) (X : Configuration E → ℝ) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e))) X)
      (β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (X (insert e τ) - X τ)) r := by
  classical
  set q : E → ℝ := fun e => longRangeEdgeProbability β (cutoffProfile K r (len e)) with hq
  have hP : ∀ e, HasDerivAt
      (fun r' => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
      (if len e ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r (len e))) else 0) r :=
    fun e => hasDerivAt_cutoffEdgeProbability_if (hne e) hK β
  have hmain := hasDerivAt_expectation
    (fun e r' => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
    (fun e => if len e ≤ r then β * K' * Real.exp (-(β * cutoffProfile K r (len e))) else 0)
    hP X
  -- rewrite the derivative value
  have hval : (∑ e, (if len e ≤ r then
        β * K' * Real.exp (-(β * cutoffProfile K r (len e))) else 0) * pivotalMass q e X)
      = β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw q τ * (X (insert e τ) - X τ) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases h : len e ≤ r
    · rw [ite_eq_left h, ite_eq_left h, ← one_sub_mul_pivotalMass q e X]
      have hexp : Real.exp (-(β * cutoffProfile K r (len e))) = 1 - q e := by
        rw [hq]; exact (one_sub_cutoffEdgeProbability).symm
      rw [hexp]; ring
    · rw [ite_eq_right h, ite_eq_right h]; ring
  rw [← hval]
  exact hmain

end PercLib.CriticalLRP.FiniteVolume
