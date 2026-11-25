/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

The exact one-edge increment of a finite product-law expectation, and the integrated
(incremental) Russo identity obtained by moving all edge probabilities along the affine path
from the old to the new parameter vector.  Everything here is finite-volume: the only sums are
over the finite edge type and the finite set of configurations, so no interchange of an
infinite sum with a derivative or an integral is used anywhere.

Reference: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1
and its proof (the Russo step), together with `CutoffRusso.lean` for the corner-free derivative.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The slice weight does not see its own coordinate -/

theorem sliceWeight_update (p : E → ℝ) (e : E) (c : ℝ) (s : Configuration E) :
    sliceWeight (Function.update p e c) e s = sliceWeight p e s := by
  classical
  refine prod_congr rfl fun e' he' => ?_
  have hne : e' ≠ e := (mem_erase.mp he').1
  simp only [Function.update, hne, ↓reduceDIte]

/-! ### The one-edge increment identity -/

/-- **Exact one-edge increment.**  Raising the open probability of the single edge `e` from
`p e` to `c` changes the expectation of `X` by `(c − p e)` times the pivotal mass of `e`. -/
theorem expectation_update_sub (p : E → ℝ) (e : E) (c : ℝ) (X : Configuration E → ℝ) :
    expectation (Function.update p e c) X - expectation p X
      = (c - p e) * pivotalMass p e X := by
  classical
  have h1 := expectation_eq_sliceWeight p e X
  have h2 := expectation_eq_sliceWeight (Function.update p e c) e X
  rw [h1, h2, pivotalMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun τ _ => ?_
  simp only [sliceWeight_update, Function.update_self]
  ring

/-! ### The affine parameter path -/

/-- Every coordinate of the affine path is differentiable in `t`, with derivative `q e - p e`. -/
theorem hasDerivAt_pathParam_apply (p q : E → ℝ) (e : E) (t : ℝ) :
    HasDerivAt (fun t' => pathParam p q t' e) (q e - p e) t := by
  have h1 : HasDerivAt (fun t' : ℝ => p e + t' * (q e - p e)) (q e - p e) t := by
    have h2 : HasDerivAt (fun t' : ℝ => t' * (q e - p e)) (q e - p e) t := by
      simpa using (hasDerivAt_id t).mul_const (q e - p e)
    simpa [add_comm] using h2.const_add (p e)
  exact h1

/-- **Russo's formula along the affine path**, exactly as `hasDerivAt_expectation` gives it. -/
theorem hasDerivAt_expectation_path (p q : E → ℝ) (X : Configuration E → ℝ) (t : ℝ) :
    HasDerivAt (fun t' => expectation (pathParam p q t') X)
      (∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X) t := by
  have h := hasDerivAt_expectation (fun e t' => pathParam p q t' e) (fun e => q e - p e)
    (fun e => hasDerivAt_pathParam_apply p q e t) X
  exact h

/-! ### Continuity of the pivotal flux along the path -/

theorem continuous_pathParam_apply (p q : E → ℝ) (e : E) :
    Continuous (fun t : ℝ => pathParam p q t e) := by
  have h : (fun t : ℝ => pathParam p q t e) = fun t : ℝ => p e + t * (q e - p e) := rfl
  rw [h]
  exact continuous_const.add (continuous_id.mul continuous_const)

theorem continuous_sliceWeight_path (p q : E → ℝ) (e : E) (s : Configuration E) :
    Continuous (fun t : ℝ => sliceWeight (pathParam p q t) e s) := by
  have h : (fun t : ℝ => sliceWeight (pathParam p q t) e s)
      = fun t : ℝ => ∏ e' ∈ (univ : Finset E).erase e,
          (if e' ∈ s then pathParam p q t e' else 1 - pathParam p q t e') := rfl
  rw [h]
  refine continuous_finsetProd _ fun e' _ => ?_
  by_cases hs : e' ∈ s
  · simpa [hs] using continuous_pathParam_apply p q e'
  · have h : Continuous (fun t : ℝ => (fun _ => (1 : ℝ)) t - pathParam p q t e') :=
      continuous_const.sub (continuous_pathParam_apply p q e')
    simpa [hs] using h

theorem continuous_pivotalMass_path (p q : E → ℝ) (e : E) (X : Configuration E → ℝ) :
    Continuous (fun t : ℝ => pivotalMass (pathParam p q t) e X) := by
  have h : (fun t : ℝ => pivotalMass (pathParam p q t) e X)
      = fun t : ℝ => ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          sliceWeight (pathParam p q t) e τ * (X (insert e τ) - X τ) := rfl
  rw [h]
  refine continuous_finsetSum _ fun τ _ => ?_
  exact (continuous_sliceWeight_path p q e τ).mul continuous_const

theorem continuous_flux (p q : E → ℝ) (c : E → ℝ) (X : Configuration E → ℝ) :
    Continuous (fun t : ℝ => ∑ e, c e * pivotalMass (pathParam p q t) e X) := by
  refine continuous_finsetSum _ fun e _ => ?_
  exact continuous_const.mul (continuous_pivotalMass_path p q e X)

theorem continuous_pathFlux (p q : E → ℝ) (X : Configuration E → ℝ) :
    Continuous (fun t : ℝ => ∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X) :=
  continuous_flux p q (fun e => q e - p e) X

/-! ### The integrated (incremental) Russo identity -/

/-- **Incremental Russo identity (finite volume, exact).**  Moving every edge probability
linearly from `p` to `q` and integrating Russo's formula along the path gives the increment of
the expectation as the integral of the pivotal flux.  There is no interchange of an infinite sum
with an integral: the flux is a finite sum of finite sums. -/
theorem expectation_sub_eq_integral_path (p q : E → ℝ) (X : Configuration E → ℝ) :
    expectation q X - expectation p X
      = ∫ t in (0 : ℝ)..1, ∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t' : ℝ => expectation (pathParam p q t') X)
        (∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X) t :=
    fun t _ => hasDerivAt_expectation_path p q X t
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X) volume 0 1 :=
    (continuous_pathFlux p q X).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [pathParam_one, pathParam_zero] at h
  exact h.symm

/-- Positivity of the flux along the path, for increasing observables and `0 ≤ p ≤ q ≤ 1`.
This is the finite-volume content of "the derivative of an increasing event's probability in a
monotone coupling is nonnegative". -/
theorem pivotalMass_path_nonneg {p q : E → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hpq : ∀ e, p e ≤ q e)
    (hq1 : ∀ e, q e ≤ 1) {X : Configuration E → ℝ} (hX : Monotone X) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (e : E) :
    0 ≤ pivotalMass (pathParam p q t) e X := by
  refine pivotalMass_nonneg (fun e' => ?_) (fun e' => ?_) hX e
  · have h : pathParam p q t e' = p e' + t * (q e' - p e') := rfl
    have h1 : 0 ≤ q e' - p e' := by linarith [hpq e']
    have h2 : 0 ≤ t * (q e' - p e') := mul_nonneg ht0 h1
    rw [h]; linarith [hp0 e']
  · have h : pathParam p q t e' = p e' + t * (q e' - p e') := rfl
    have h1 : t * (q e' - p e') ≤ 1 * (q e' - p e') := by
      exact mul_le_mul_of_nonneg_right ht1 (by linarith [hpq e'])
    have hq' : p e' + t * (q e' - p e') ≤ q e' := by nlinarith [h1, hpq e', hp0 e']
    rw [h]; linarith [hq1 e']

/-- The increment identity with a nonnegative integrand. -/
theorem expectation_sub_eq_integral_path_nonneg {p q : E → ℝ} (hp0 : ∀ e, 0 ≤ p e)
    (hpq : ∀ e, p e ≤ q e) (hq1 : ∀ e, q e ≤ 1) {X : Configuration E → ℝ} (hX : Monotone X) :
    expectation q X - expectation p X
      = ∫ t in (0 : ℝ)..1, ∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X :=
  expectation_sub_eq_integral_path p q X

/-- The increment is nonnegative when the observable is increasing and all probabilities move up:
the finite-volume monotonicity of the law in its parameter vector. -/
theorem expectation_mono_of_monotone {p q : E → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hpq : ∀ e, p e ≤ q e)
    (hq1 : ∀ e, q e ≤ 1) {X : Configuration E → ℝ} (hX : Monotone X) :
    expectation p X ≤ expectation q X := by
  have h := expectation_sub_eq_integral_path_nonneg hp0 hpq hq1 hX
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1,
      ∑ e, (q e - p e) * pivotalMass (pathParam p q t) e X := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
    refine Finset.sum_nonneg fun e _ => ?_
    exact mul_nonneg (by linarith [hpq e]) (pivotalMass_path_nonneg hp0 hpq hq1 hX ht.1 ht.2 e)
  linarith [h, hnn]

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
