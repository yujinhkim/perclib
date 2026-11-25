/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Finite-volume Bernoulli calculus and Russo's formula for the long-range
percolation model of Hutchcroft, "Critical long-range percolation I",
arXiv:2508.18807v1, Section I.4 (Lemma I.4.1 and its proof).

Everything here is finite-volume and exact: for a finite edge type `E` with
edge-dependent open probabilities `p : E → ℝ`, we prove

* the slice (`erase`-`insert`) decomposition of the product law;
* the derivative of an expectation with respect to a parameter on which the
  edge probabilities depend, in the "flip" form

      d/dt E[X] = ∑ e (p_e)'(t) * ∑_{τ ∌ e} w_{E∖{e}}(τ) (X (insert e τ) - X τ),

  which is Russo's formula; the inner sum is the mass of configurations where
  the state of `e` is pivotal for `X`, and it is nonnegative for increasing `X`.
-/
module

public import PercLib.CriticalLRP.FiniteBernoulli
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

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

/-- The weight of the configuration `s` with the factor of the edge `e`
deleted from the product defining the law. This depends on the values of `p`
at the edges other than `e` only. -/
noncomputable def sliceWeight (p : E → ℝ) (e : E) (s : Configuration E) : ℝ :=
  ∏ e' ∈ (univ : Finset E).erase e, if e' ∈ s then p e' else 1 - p e'

theorem sliceWeight_insert (p : E → ℝ) (e : E) (s : Configuration E) :
    sliceWeight p e (insert e s) = sliceWeight p e s := by
  unfold sliceWeight
  refine prod_congr rfl fun e' he' => ?_
  have hne : e' ≠ e := (mem_erase.mp he').1
  simp only [mem_insert, hne, false_or]

/-- Splitting the product law into the factor of `e` and the rest. -/
theorem configurationLaw_eq_sliceWeight (p : E → ℝ) (e : E) (s : Configuration E) :
    configurationLaw p s
      = (if e ∈ s then p e else 1 - p e) * sliceWeight p e s := by
  unfold configurationLaw sliceWeight
  have hmem : e ∈ (univ : Finset E) := mem_univ e
  conv_lhs => rw [← mul_prod_erase (univ : Finset E)
    (fun e' => if e' ∈ s then p e' else 1 - p e') hmem]

/-- Pairing lemma: summing over all configurations is the same as summing over
the configurations in which `e` is absent the two values obtained by forcing
`e` closed and open. -/
theorem sum_eq_sum_filter_add (e : E) (g : Configuration E → ℝ) :
    ∑ s : Configuration E, g s
      = ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          (g τ + g (insert e τ)) := by
  classical
  rw [← sum_filter_add_sum_filter_not (s := (univ : Finset (Configuration E)))
    (p := fun τ => e ∈ τ)]
  rw [sum_add_distrib]
  have hA : ∑ x ∈ (univ : Finset (Configuration E)).filter (fun x => e ∈ x), g x
      = ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ), g (insert e τ) := by
    refine sum_nbij' (fun a => a.erase e) (fun b => insert e b) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact notMem_erase e a
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb ⊢
      exact mem_insert_self e b
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      exact insert_erase ha
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact erase_insert hb
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      rw [insert_erase ha]
  rw [hA, add_comm]

/-- Slice decomposition of the expectation: the state of the edge `e` can be
integrated out. -/
theorem expectation_eq_sliceWeight (p : E → ℝ) (e : E) (X : Configuration E → ℝ) :
    expectation p X
      = ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          sliceWeight p e τ * ((1 - p e) * X τ + p e * X (insert e τ)) := by
  classical
  have hstep : expectation p X
      = ∑ s : Configuration E,
          sliceWeight p e s * ((if e ∈ s then p e else 1 - p e) * X s) := by
    rw [expectation]
    refine sum_congr rfl fun s _ => ?_
    rw [configurationLaw_eq_sliceWeight]
    ring
  rw [hstep, sum_eq_sum_filter_add e]
  refine sum_congr rfl fun τ hτ => ?_
  rw [mem_filter] at hτ
  have hnot : e ∉ τ := hτ.2
  have hin : e ∈ insert e τ := mem_insert_self e τ
  have h1 : (if e ∈ τ then p e else 1 - p e) = 1 - p e := by simp [hnot]
  have h2 : (if e ∈ insert e τ then p e else 1 - p e) = p e := by simp [hin]
  rw [h1, h2, sliceWeight_insert]
  ring

/-! ### The pivot mass and Russo's formula -/

/-- Generic reindexing: a sum over the configurations in which `e` is open is
the same as a sum over the configurations in which `e` is closed, with `e`
inserted. -/
theorem sum_filter_mem_eq (e : E) (F : Configuration E → ℝ) :
    ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∈ s), F s
      = ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ), F (insert e τ) := by
  classical
  refine sum_nbij' (fun a => a.erase e) (fun b => insert e b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact notMem_erase e a
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact mem_insert_self e b
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    exact insert_erase ha
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    exact erase_insert hb
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    rw [insert_erase ha]

/-- The mass of configurations, weighted by the law with the edge `e` removed,
on which flipping `e` from closed to open changes the observable `X` by the
stated amount. This is `E[X(ω with e open) - X(ω)]` under the sliced law. -/
noncomputable def pivotalMass (p : E → ℝ) (e : E) (X : Configuration E → ℝ) : ℝ :=
  ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
    sliceWeight p e τ * (X (insert e τ) - X τ)

theorem pivotalMass_nonneg {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {X : Configuration E → ℝ} (hX : Monotone X) (e : E) : 0 ≤ pivotalMass p e X := by
  classical
  refine sum_nonneg fun τ _ => ?_
  have hsub : τ ⊆ insert e τ := subset_insert e τ
  have hle : X τ ≤ X (insert e τ) := hX hsub
  have hw : 0 ≤ sliceWeight p e τ := by
    refine prod_nonneg fun e' _ => ?_
    by_cases h : e' ∈ τ
    · rw [ite_eq_left h]; exact hp e'
    · rw [ite_eq_right h]; linarith [hp1 e']
  exact mul_nonneg hw (sub_nonneg.mpr hle)

/-- Derivative of one factor of the product law in the parameter `t`. -/
theorem hasDerivAt_weightFactor (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ}
    (hP : ∀ e, HasDerivAt (P e) (P' e) t) (e : E) (s : Configuration E) :
    HasDerivAt (fun t' => if e ∈ s then P e t' else 1 - P e t')
      (if e ∈ s then P' e else -P' e) t := by
  by_cases h : e ∈ s
  · have hfun : (fun t' => if e ∈ s then P e t' else 1 - P e t') = P e := by
      funext t'; simp [h]
    have hder : (if e ∈ s then P' e else -P' e) = P' e := by simp [h]
    rw [hfun, hder]; exact hP e
  · have hfun : (fun t' => if e ∈ s then P e t' else 1 - P e t')
        = fun t' => 1 - P e t' := by
      funext t'; simp [h]
    have hder : (if e ∈ s then P' e else -P' e) = -P' e := by simp [h]
    rw [hfun, hder]; exact HasDerivAt.const_sub (1 : ℝ) (hP e)

/-- Derivative of the weight of a single configuration in the parameter `t`. -/
theorem hasDerivAt_configurationLaw (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ}
    (hP : ∀ e, HasDerivAt (P e) (P' e) t) (s : Configuration E) :
    HasDerivAt (fun t' => configurationLaw (fun e => P e t') s)
      (∑ e, sliceWeight (fun e => P e t) e s * (if e ∈ s then P' e else -P' e)) t := by
  have h := HasDerivAt.finsetProd (u := (univ : Finset E))
    (f := fun e t' => if e ∈ s then P e t' else 1 - P e t')
    (f' := fun e => if e ∈ s then P' e else -P' e)
    (fun i _ => hasDerivAt_weightFactor P P' hP i s)
  convert h using 1
  · funext t'
    simp only [configurationLaw, Finset.prod_apply]
  · simp only [sliceWeight, smul_eq_mul]

/-- **Russo's formula** (finite volume, expectation form): if each edge
probability `P e` is differentiable at `t` with derivative `P' e`, then

`d/dt E_{P t}[X] = ∑ e P' e * (mass of configurations where e is pivotal)`.

This is the exact finite-volume identity used in the proof of Lemma I.4.1. -/
theorem hasDerivAt_expectation (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ}
    (hP : ∀ e, HasDerivAt (P e) (P' e) t) (X : Configuration E → ℝ) :
    HasDerivAt (fun t' => expectation (fun e => P e t') X)
      (∑ e, P' e * pivotalMass (fun e => P e t) e X) t := by
  classical
  set pt : E → ℝ := fun e => P e t with hpt
  have hterm : ∀ s : Configuration E,
      HasDerivAt (fun t' => configurationLaw (fun e => P e t') s * X s)
        ((∑ e, sliceWeight pt e s * (if e ∈ s then P' e else -P' e)) * X s) t :=
    fun s => (hasDerivAt_configurationLaw P P' hP s).mul_const (X s)
  have hsum := HasDerivAt.sum (u := (univ : Finset (Configuration E)))
    (fun s _ => hterm s)
  -- rewrite the derivative value
  have hkey : ∀ e : E, ∑ s : Configuration E,
        sliceWeight pt e s * (if e ∈ s then P' e else -P' e) * X s
      = P' e * pivotalMass pt e X := by
    intro e
    rw [← sum_filter_add_sum_filter_not (s := (univ : Finset (Configuration E)))
      (p := fun s => e ∈ s)
      (f := fun s => sliceWeight pt e s * (if e ∈ s then P' e else -P' e) * X s)]
    have h1 : ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∈ s),
        sliceWeight pt e s * (if e ∈ s then P' e else -P' e) * X s
        = P' e * ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∈ s),
            sliceWeight pt e s * X s := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun s hs => ?_
      rw [mem_filter] at hs
      have hif : (if e ∈ s then P' e else -P' e) = P' e := by simp [hs.2]
      rw [hif]; ring
    have h2 : ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => ¬ e ∈ s),
        sliceWeight pt e s * (if e ∈ s then P' e else -P' e) * X s
        = -(P' e * ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∉ s),
            sliceWeight pt e s * X s) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine sum_congr rfl fun s hs => ?_
      rw [mem_filter] at hs
      have hif : (if e ∈ s then P' e else -P' e) = -P' e := by simp [hs.2]
      rw [hif]; ring
    rw [h1, h2]
    have hstep : P' e * ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∈ s),
          sliceWeight pt e s * X s
        + -(P' e * ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∉ s),
          sliceWeight pt e s * X s)
        = P' e * ((∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∈ s),
              sliceWeight pt e s * X s)
            - ∑ s ∈ (univ : Finset (Configuration E)).filter (fun s => e ∉ s),
              sliceWeight pt e s * X s) := by ring
    rw [hstep]
    congr 1
    rw [sum_filter_mem_eq e (fun s => sliceWeight pt e s * X s)]
    unfold pivotalMass
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun τ _ => by rw [sliceWeight_insert]; ring
  have hval : (∑ s : Configuration E,
        (∑ e, sliceWeight pt e s * (if e ∈ s then P' e else -P' e)) * X s)
      = ∑ e, P' e * pivotalMass pt e X := by
    calc ∑ s : Configuration E,
          (∑ e, sliceWeight pt e s * (if e ∈ s then P' e else -P' e)) * X s
        = ∑ s : Configuration E, ∑ e,
            (sliceWeight pt e s * (if e ∈ s then P' e else -P' e)) * X s := by
          simp only [Finset.sum_mul]
      _ = ∑ e, ∑ s : Configuration E,
            (sliceWeight pt e s * (if e ∈ s then P' e else -P' e)) * X s :=
          Finset.sum_comm
      _ = ∑ e, P' e * pivotalMass pt e X := by
          exact sum_congr rfl fun e _ => hkey e
  have hfun : (fun t' => expectation (fun e => P e t') X)
      = (∑ i : Configuration E, fun t' => configurationLaw (fun e => P e t') i * X i) := by
    funext t'
    simp only [expectation, Finset.sum_apply]
  rw [hfun, ← hval]
  exact hsum

end PercLib.CriticalLRP.FiniteVolume
