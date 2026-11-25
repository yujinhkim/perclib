/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Second-order (pair-pivotal) finite-volume Russo identities.

The repository's `CriticalPercLib.CriticalLRP/RussoFinite.lean` proves the
first-order finite-volume Russo formula

  d/dt E_{P t}[X] = ∑ e (P e)'(t) * pivotalMass (P t) e X,

where `pivotalMass p e X` is the sliced mass of the configurations in which the
edge `e` is pivotal for `X`.  Lemma I.4.1 of Hutchcroft, "Critical long-range
percolation I" (arXiv:2508.18807v1), is used there at first order only.

This file supplies the second order.  For distinct edges `e ≠ f` we define the
pair-pivotal mass of the pair `{e, f}`,

  pairPivotalMass p e f X
    = ∑_{τ ∌ e, f} w_{E∖{e,f}}(τ) * Δ_e Δ_f X (τ),

with `Δ` the forced-open/forced-closed difference, prove that it is exactly the
derivative of the first-order pivotal mass in a further edge parameter, and
obtain the second derivative of the finite expectation along a linear profile
`p + t·v`:

  d²/dt² E_{p + t·v}[X]
    = ∑ e ∑_{f ≠ e} v e * v f * pairPivotalMass (p + t·v) e f X.

The double sum avoids the diagonal: `p ↦ E_p[X]` is multilinear, so the second
derivative in a single coordinate vanishes.  Nothing here assumes
nonnegativity, monotonicity or a probability interpretation of `X`; all
identities are exact finite sums.
-/
module

public import PercLib.CriticalLRP.RussoFinite
public import PercLib.CriticalLRP.KernelGeometry
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-! ### Weights over an arbitrary finite coordinate set -/

/-- The weight of the coordinates in `K`: the product of the open/closed
factors of the edges of `K` only.  `sliceWeight p e` is the case
`K = univ.erase e`. -/
noncomputable def weightProd (p : E → ℝ) (K : Finset E) (s : Configuration E) : ℝ :=
  ∏ e ∈ K, if e ∈ s then p e else 1 - p e

theorem sliceWeight_eq_weightProd (p : E → ℝ) (e : E) (s : Configuration E) :
    sliceWeight p e s = weightProd p ((univ : Finset E).erase e) s := rfl

omit [Fintype E] in
/-- A product over `K` splits off the factor of a member. -/
theorem weightProd_eq_mul_erase (p : E → ℝ) {K : Finset E} {e : E} (he : e ∈ K)
    (s : Configuration E) :
    weightProd p K s
      = (if e ∈ s then p e else 1 - p e) * weightProd p (K.erase e) s := by
  unfold weightProd
  exact (Finset.mul_prod_erase K (fun e' => if e' ∈ s then p e' else 1 - p e') he).symm

omit [Fintype E] in
/-- The weight over `K.erase e` does not see the state of `e`. -/
theorem weightProd_erase_insert {K : Finset E} {e : E}
    (p : E → ℝ) (s : Configuration E) :
    weightProd p (K.erase e) (insert e s) = weightProd p (K.erase e) s := by
  unfold weightProd
  refine Finset.prod_congr rfl fun e' he' => ?_
  have hne : e' ≠ e := (Finset.mem_erase.mp he').1
  simp only [Finset.mem_insert, hne, false_or]

/-- Product rule for the coordinate weight, in the parameter `t`. -/
theorem hasDerivAt_weightProd (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ}
    (hP : ∀ e, HasDerivAt (P e) (P' e) t) (K : Finset E) (s : Configuration E) :
    HasDerivAt (fun t' => weightProd (fun e => P e t') K s)
      (∑ f ∈ K, (if f ∈ s then P' f else -P' f) *
        weightProd (fun e => P e t) (K.erase f) s) t := by
  unfold weightProd
  have h := HasDerivAt.finsetProd (u := K)
    (f := fun f t' => if f ∈ s then P f t' else 1 - P f t')
    (f' := fun f => if f ∈ s then P' f else -P' f)
    (fun i _ => hasDerivAt_weightFactor P P' hP i s)
  convert h using 1
  · funext t'
    simp only [Finset.prod_apply]
  · refine Finset.sum_congr rfl fun f hf => ?_
    simp only [smul_eq_mul, mul_comm]

/-! ### The signed pair-pivotal mass -/

/-- The signed pair-pivotal mass of the ordered pair `(e, f)`.  It is the
derivative of `pivotalMass p e X` in the parameter of the edge `f`: summing over
the configurations in which `e` is closed and weighting the pair `{e, f}` by the
sign of the state of `f`.  Its unconditional form is `pairPivotalMass` below. -/
noncomputable def pairPivotalMassSigned (p : E → ℝ) (e f : E)
    (X : Configuration E → ℝ) : ℝ :=
  ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
    (if f ∈ τ then (1 : ℝ) else -1) *
      weightProd p (((univ : Finset E).erase e).erase f) τ * (X (insert e τ) - X τ)

/-- **Russo's formula at second order.**  The derivative of the first-order
pivotal mass of `e` in the parameter controlling the remaining edges is the
`P'`-weighted signed pair-pivotal mass.  `X` is arbitrary; no monotonicity or
sign assumption is used. -/
theorem hasDerivAt_pivotalMass (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ}
    (hP : ∀ e, HasDerivAt (P e) (P' e) t) (e : E) (X : Configuration E → ℝ) :
    HasDerivAt (fun t' => pivotalMass (fun e => P e t') e X)
      (∑ f ∈ (univ : Finset E).erase e, P' f *
        pairPivotalMassSigned (fun e => P e t) e f X) t := by
  classical
  have hterm : ∀ τ : Configuration E,
      HasDerivAt
        (fun t' => weightProd (fun e => P e t') ((univ : Finset E).erase e) τ *
          (X (insert e τ) - X τ))
        ((∑ f ∈ (univ : Finset E).erase e, (if f ∈ τ then P' f else -P' f) *
          weightProd (fun e => P e t) (((univ : Finset E).erase e).erase f) τ) *
          (X (insert e τ) - X τ)) t :=
    fun τ => (hasDerivAt_weightProd P P' hP _ τ).mul_const _
  have hsum := HasDerivAt.sum
    (u := (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ))
    (A := fun τ t' => weightProd (fun e => P e t') ((univ : Finset E).erase e) τ *
      (X (insert e τ) - X τ))
    (A' := fun τ => (∑ f ∈ (univ : Finset E).erase e, (if f ∈ τ then P' f else -P' f) *
      weightProd (fun e => P e t) (((univ : Finset E).erase e).erase f) τ) *
      (X (insert e τ) - X τ))
    (fun τ _ => hterm τ)
  have hval : (∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
        (∑ f ∈ (univ : Finset E).erase e, (if f ∈ τ then P' f else -P' f) *
          weightProd (fun e => P e t) (((univ : Finset E).erase e).erase f) τ) *
        (X (insert e τ) - X τ))
      = ∑ f ∈ (univ : Finset E).erase e, P' f *
        pairPivotalMassSigned (fun e => P e t) e f X := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    unfold pairPivotalMassSigned
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ hτ => by
      by_cases h : f ∈ τ
      · simp only [h, ite_true]; ring
      · simp only [h, ite_false]; ring
  have hfun : (fun t' => pivotalMass (fun e => P e t') e X)
      = fun t' => ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          weightProd (fun e => P e t') ((univ : Finset E).erase e) τ *
            (X (insert e τ) - X τ) := by
    funext t'
    rw [pivotalMass]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [sliceWeight_eq_weightProd]
  have hsum_fun :
      (∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          fun t' => weightProd (fun e => P e t') ((univ : Finset E).erase e) τ *
            (X (insert e τ) - X τ))
        = fun t' => ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
            weightProd (fun e => P e t') ((univ : Finset E).erase e) τ *
              (X (insert e τ) - X τ) := by
    funext t'
    rw [Finset.sum_apply]
  rw [hsum_fun] at hsum
  rw [hfun]
  rw [← hval]
  exact hsum

/-! ### The unconditional (mixed-difference) pair-pivotal mass -/

/-- The configurations in which the edge `e` is closed. -/
def closedSlices (e : E) : Finset (Configuration E) :=
  (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ)

/-- The forced-open/forced-closed mixed difference of `X` at the pair of edges
`{e, f}`: open `e` and `f`, open `e` only, open `f` only, open neither. -/
def pairDifference (X : Configuration E → ℝ) (e f : E) (τ : Configuration E) : ℝ :=
  X (insert e (insert f τ)) - X (insert e τ) - X (insert f τ) + X τ

/-- The unconditional pair-pivotal mass of the pair `{e, f}`: the sliced mass of
`Δ_e Δ_f X`, weighted by the law of the remaining edges only. -/
noncomputable def pairPivotalMass (p : E → ℝ) (e f : E)
    (X : Configuration E → ℝ) : ℝ :=
  ∑ τ ∈ (closedSlices e).filter (fun τ => f ∉ τ),
    weightProd p (((univ : Finset E).erase e).erase f) τ * pairDifference X e f τ

/-- Splitting off the slices in which `f` is open: `τ ↦ τ.erase f` is a
bijection with the slices in which `f` is closed. -/
theorem sum_closed_open_eq {e f : E} (hne : e ≠ f) (W Y : Configuration E → ℝ) :
    ∑ τ ∈ (closedSlices e).filter (fun τ => f ∈ τ), W τ * Y τ
      = ∑ σ ∈ (closedSlices e).filter (fun σ => f ∉ σ),
          W (insert f σ) * Y (insert f σ) := by
  classical
  refine Finset.sum_nbij' (fun τ => τ.erase f) (fun σ => insert f σ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [closedSlices, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨fun h => ha.1 (Finset.mem_of_mem_erase h), Finset.notMem_erase f a⟩
  · intro a ha
    simp only [closedSlices, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    refine ⟨fun h => ?_, Finset.mem_insert_self f a⟩
    rcases Finset.mem_insert.mp h with h' | h'
    · exact absurd h' hne
    · exact ha.1 h'
  · intro a ha
    simp only [closedSlices, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.insert_erase ha.2
  · intro a ha
    simp only [closedSlices, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.erase_insert ha.2
  · intro a ha
    simp only [closedSlices, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Finset.insert_erase ha.2]

/-- The signed form of the pair-pivotal mass is its mixed-difference form.  This
is the percolation content of the second derivative: the sign of the state of
`f` in the slices where `e` is closed is exactly the `f`-difference of
`Δ_e X`. -/
theorem pairPivotalMassSigned_eq {e f : E} (hne : e ≠ f) (p : E → ℝ)
    (X : Configuration E → ℝ) :
    pairPivotalMassSigned p e f X = pairPivotalMass p e f X := by
  classical
  have hW : ∀ σ : Configuration E,
      weightProd p (((univ : Finset E).erase e).erase f) (insert f σ)
        = weightProd p (((univ : Finset E).erase e).erase f) σ :=
    fun σ => weightProd_erase_insert (K := (univ : Finset E).erase e) (e := f) p σ
  have h1 : ∑ τ ∈ (closedSlices e).filter (fun τ => f ∈ τ),
        (if f ∈ τ then (1 : ℝ) else -1) *
          weightProd p (((univ : Finset E).erase e).erase f) τ *
          (X (insert e τ) - X τ)
      = ∑ τ ∈ (closedSlices e).filter (fun τ => f ∈ τ),
          weightProd p (((univ : Finset E).erase e).erase f) τ *
            (X (insert e τ) - X τ) := by
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Finset.mem_filter] at hτ
    simp only [hτ.2, ite_true, one_mul]
  have h2 : ∑ τ ∈ (closedSlices e).filter (fun τ => ¬ f ∈ τ),
        (if f ∈ τ then (1 : ℝ) else -1) *
          weightProd p (((univ : Finset E).erase e).erase f) τ *
          (X (insert e τ) - X τ)
      = ∑ τ ∈ (closedSlices e).filter (fun τ => ¬ f ∈ τ),
          -(weightProd p (((univ : Finset E).erase e).erase f) τ *
            (X (insert e τ) - X τ)) := by
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [Finset.mem_filter] at hτ
    simp only [hτ.2, ite_false]
    ring
  have hstep : ∑ σ ∈ (closedSlices e).filter (fun σ => f ∉ σ),
        weightProd p (((univ : Finset E).erase e).erase f) (insert f σ) *
          (X (insert e (insert f σ)) - X (insert f σ))
      = ∑ σ ∈ (closedSlices e).filter (fun σ => f ∉ σ),
          weightProd p (((univ : Finset E).erase e).erase f) σ *
            (X (insert e (insert f σ)) - X (insert f σ)) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hW σ]
  have hcombine : ∑ σ ∈ (closedSlices e).filter (fun σ => f ∉ σ),
        weightProd p (((univ : Finset E).erase e).erase f) σ *
          (X (insert e (insert f σ)) - X (insert f σ))
      + ∑ τ ∈ (closedSlices e).filter (fun τ => ¬ f ∈ τ),
          -(weightProd p (((univ : Finset E).erase e).erase f) τ *
            (X (insert e τ) - X τ))
      = ∑ σ ∈ (closedSlices e).filter (fun σ => f ∉ σ),
          weightProd p (((univ : Finset E).erase e).erase f) σ *
            pairDifference X e f σ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [pairDifference]
    ring
  have hA : pairPivotalMassSigned p e f X
      = ∑ τ ∈ closedSlices e, (if f ∈ τ then (1 : ℝ) else -1) *
          weightProd p (((univ : Finset E).erase e).erase f) τ *
          (X (insert e τ) - X τ) := rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := closedSlices e) (p := fun τ => f ∈ τ)
    (f := fun τ => (if f ∈ τ then (1 : ℝ) else -1) *
      weightProd p (((univ : Finset E).erase e).erase f) τ * (X (insert e τ) - X τ))
  rw [hA, ← hsplit, h1, h2]
  rw [sum_closed_open_eq hne
    (fun τ => weightProd p (((univ : Finset E).erase e).erase f) τ)
    (fun τ => X (insert e τ) - X τ), hstep, hcombine]
  rfl

/-! ### First and second derivatives along a linear profile -/

omit [Fintype E] [DecidableEq E] in
/-- Derivative of the linear profile `t ↦ p e + t * v e`. -/
theorem hasDerivAt_linearProfile (p v : E → ℝ) (t : ℝ) :
    ∀ e, HasDerivAt (fun t' => p e + t' * v e) (v e) t := fun e => by
  simpa using (hasDerivAt_id t).mul_const (v e) |>.const_add (p e)

/-- First derivative of the finite expectation along a linear profile: Russo's
formula with the edge weights `v`. -/
theorem hasDerivAt_expectation_add_mul (p v : E → ℝ) (X : Configuration E → ℝ)
    (t : ℝ) :
    HasDerivAt (fun t' => expectation (fun e => p e + t' * v e) X)
      (∑ e, v e * pivotalMass (fun e => p e + t * v e) e X) t :=
  hasDerivAt_expectation (fun e t' => p e + t' * v e) v
    (hasDerivAt_linearProfile p v t) X

/-- **Russo's formula at second order.**  The derivative of the first-order
pivotal sum along a linear profile is the `v`-weighted double sum of pair
pivotal masses, with the diagonal `f = e` absent because the finite expectation
is multilinear in the edge probabilities. -/
theorem hasDerivAt_pivotalSum_add_mul (p v : E → ℝ) (X : Configuration E → ℝ)
    (t : ℝ) :
    HasDerivAt (fun t' => ∑ e, v e * pivotalMass (fun e => p e + t' * v e) e X)
      (∑ e, ∑ f ∈ (univ : Finset E).erase e, v e * v f *
        pairPivotalMass (fun e => p e + t * v e) e f X) t := by
  have hP := hasDerivAt_linearProfile p v t
  have hconv : ∀ e : E,
      (∑ f ∈ (univ : Finset E).erase e,
          v f * pairPivotalMassSigned (fun e => p e + t * v e) e f X)
        = ∑ f ∈ (univ : Finset E).erase e,
            v f * pairPivotalMass (fun e => p e + t * v e) e f X := by
    intro e
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [pairPivotalMassSigned_eq (Ne.symm (Finset.mem_erase.mp hf).1)]
  have hterm : ∀ e : E,
      HasDerivAt (fun t' => v e * pivotalMass (fun e => p e + t' * v e) e X)
        (v e * ∑ f ∈ (univ : Finset E).erase e,
          v f * pairPivotalMass (fun e => p e + t * v e) e f X) t := by
    intro e
    have h := (hasDerivAt_pivotalMass (P := fun e t' => p e + t' * v e) (P' := v)
      hP e X).const_mul (v e)
    rw [hconv e] at h
    exact h
  have hsum := HasDerivAt.sum (u := (univ : Finset E))
    (A := fun e t' => v e * pivotalMass (fun e => p e + t' * v e) e X)
    (A' := fun e => v e * ∑ f ∈ (univ : Finset E).erase e,
      v f * pairPivotalMass (fun e => p e + t * v e) e f X)
    (fun e _ => hterm e)
  have hval : (∑ e : E, v e * ∑ f ∈ (univ : Finset E).erase e,
        v f * pairPivotalMass (fun e => p e + t * v e) e f X)
      = ∑ e, ∑ f ∈ (univ : Finset E).erase e, v e * v f *
          pairPivotalMass (fun e => p e + t * v e) e f X := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hsum_fun : (∑ e : E, fun t' => v e * pivotalMass (fun e => p e + t' * v e) e X)
      = fun t' => ∑ e : E, v e * pivotalMass (fun e => p e + t' * v e) e X := by
    funext t'
    rw [Finset.sum_apply]
  rw [hsum_fun] at hsum
  rw [hval] at hsum
  exact hsum

/-- **The second derivative of a finite Bernoulli expectation.**  Along the
linear profile `p + t * v` the second derivative of `E[X]` is the pair-pivotal
double sum. -/
theorem deriv_deriv_expectation_add_mul (p v : E → ℝ) (X : Configuration E → ℝ)
    (t : ℝ) :
    deriv (deriv fun s => expectation (fun e => p e + s * v e) X) t
      = ∑ e, ∑ f ∈ (univ : Finset E).erase e, v e * v f *
          pairPivotalMass (fun e => p e + t * v e) e f X := by
  have hfirst : deriv (fun s => expectation (fun e => p e + s * v e) X)
      = fun s => ∑ e, v e * pivotalMass (fun e => p e + s * v e) e X := by
    funext s
    exact (hasDerivAt_expectation_add_mul p v X s).deriv
  rw [hfirst]
  exact (hasDerivAt_pivotalSum_add_mul p v X t).deriv

/-! ### Consequences: zero diagonal and the event form -/

/-- The finite expectation is affine in each single edge probability, so its
second derivative in a single coordinate vanishes.  This is why the second-order
Russo formula carries no diagonal terms. -/
theorem deriv_deriv_single_coordinate (p : E → ℝ) (e : E) (X : Configuration E → ℝ)
    (t : ℝ) :
    deriv (deriv fun s =>
        expectation (fun f => p f + s * (if f = e then (1 : ℝ) else 0)) X) t = 0 := by
  classical
  rw [deriv_deriv_expectation_add_mul]
  refine Finset.sum_eq_zero fun e' _ => ?_
  by_cases he' : e' = e
  · rw [he']
    refine Finset.sum_eq_zero fun f hf => ?_
    have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
    simp [hfe]
  · refine Finset.sum_eq_zero fun f hf => ?_
    simp [he']

/-- Event form of the second-order Russo formula: the second derivative of the
probability of a finite event along a linear profile is the pair-pivotal
double sum of its indicator. -/
theorem deriv_deriv_probability_add_mul (p v : E → ℝ) (A : Set (Configuration E))
    (t : ℝ) :
    deriv (deriv fun s => probability (fun e => p e + s * v e) A) t
      = ∑ e, ∑ f ∈ (univ : Finset E).erase e, v e * v f *
          pairPivotalMass (fun e => p e + t * v e) e f
            (A.indicator fun _ => (1 : ℝ)) := by
  classical
  have h : (fun s => probability (fun e => p e + s * v e) A)
      = fun s => expectation (fun e => p e + s * v e)
          (A.indicator fun _ => (1 : ℝ)) := by
    funext s
    rfl
  rw [h]
  exact deriv_deriv_expectation_add_mul p v _ t

/-! ### Second order for a general coordinate parametrisation -/

/-- **Second-order finite Russo formula for a general parametrisation.**  If each
edge probability `P e` has derivative `P' e` at every parameter value and, at
`t`, `P' e` is differentiable, then

`d²/dt² E_{P t}[X] = ∑ e [ (P' e)'(t) * pivotalMass_e + P' e(t) * ∑_{f ≠ e} P' f(t) * pairPivotalMass_{ef} ]`.

The first summand is the second derivative of the individual edge probability;
the second is the genuine pair-pivotal term.  For an affine profile the first
summand vanishes and this reduces to `deriv_deriv_expectation_add_mul`. -/
theorem deriv_deriv_expectation_general (P : E → ℝ → ℝ) (P' : E → ℝ → ℝ)
    (hP : ∀ e, ∀ s : ℝ, HasDerivAt (P e) (P' e s) s) {t : ℝ}
    (hP' : ∀ e, DifferentiableAt ℝ (P' e) t) (X : Configuration E → ℝ) :
    deriv (deriv fun s => expectation (fun e => P e s) X) t
      = ∑ e, (deriv (P' e) t * pivotalMass (fun e => P e t) e X +
          P' e t * ∑ f ∈ (univ : Finset E).erase e,
            P' f t * pairPivotalMass (fun e => P e t) e f X) := by
  classical
  have hfirst : deriv (fun s => expectation (fun e => P e s) X)
      = fun s => ∑ e, P' e s * pivotalMass (fun e => P e s) e X := by
    funext s
    exact (hasDerivAt_expectation P (fun e => P' e s) (fun e => hP e s) X).deriv
  rw [hfirst]
  have hconv : ∀ e : E,
      (∑ f ∈ (univ : Finset E).erase e,
          P' f t * pairPivotalMassSigned (fun e => P e t) e f X)
        = ∑ f ∈ (univ : Finset E).erase e,
            P' f t * pairPivotalMass (fun e => P e t) e f X := by
    intro e
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [pairPivotalMassSigned_eq (Ne.symm (Finset.mem_erase.mp hf).1)]
  have hterm : ∀ e : E,
      HasDerivAt (fun s => P' e s * pivotalMass (fun e => P e s) e X)
        (deriv (P' e) t * pivotalMass (fun e => P e t) e X +
          P' e t * ∑ f ∈ (univ : Finset E).erase e,
            P' f t * pairPivotalMass (fun e => P e t) e f X) t := by
    intro e
    have h1 : HasDerivAt (fun s => P' e s * pivotalMass (fun e => P e s) e X)
        (deriv (P' e) t * pivotalMass (fun e => P e t) e X +
          P' e t * ∑ f ∈ (univ : Finset E).erase e,
            P' f t * pairPivotalMassSigned (fun e => P e t) e f X) t :=
      (hP' e).hasDerivAt.mul
        (hasDerivAt_pivotalMass (P := P) (P' := fun e => P' e t) (fun e => hP e t) e X)
    rwa [hconv e] at h1
  have hsum := HasDerivAt.sum (u := (univ : Finset E))
    (A := fun e s => P' e s * pivotalMass (fun e => P e s) e X)
    (A' := fun e => deriv (P' e) t * pivotalMass (fun e => P e t) e X +
      P' e t * ∑ f ∈ (univ : Finset E).erase e,
        P' f t * pairPivotalMass (fun e => P e t) e f X)
    (fun e _ => hterm e)
  have hsum_fun :
      (∑ e : E, fun s => P' e s * pivotalMass (fun e => P e s) e X)
        = fun s => ∑ e : E, P' e s * pivotalMass (fun e => P e s) e X := by
    funext s
    rw [Finset.sum_apply]
  rw [hsum_fun] at hsum
  exact hsum.deriv

/-! ### The long-range model: second derivative in `β` -/

/-- Derivative in `β` of the derivative `J exp (-(β J))` of the long-range edge
probability. -/
theorem hasDerivAt_longRangeEdgeProbability_deriv (J : ℝ) (β : ℝ) :
    HasDerivAt (fun s => J * Real.exp (-(s * J))) (-(J ^ 2) * Real.exp (-(β * J))) β := by
  have h1 : HasDerivAt (fun s : ℝ => -(s * J)) (-(1 * J)) β :=
    ((hasDerivAt_id β).mul_const J).neg
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(s * J)))
      (Real.exp (-(β * J)) * -(1 * J)) β :=
    h1.exp
  have h3 := h2.const_mul J
  convert h3 using 1
  ring

/-- **Second derivative of the finite long-range expectation in `β`.**  This is
the two-term form of the second-order Russo formula for the model of Definition
I.1.3: the derivative of each edge weight contributes a first-order pivotal
mass, and the remaining term is the pair-pivotal double sum. -/
theorem deriv_deriv_longRangeExpectation (J : E → ℝ) (X : Configuration E → ℝ)
    (β : ℝ) :
    deriv (deriv fun s => expectation (fun e => longRangeEdgeProbability s (J e)) X) β
      = ∑ e, (-(J e ^ 2) * Real.exp (-(β * J e)) *
            pivotalMass (fun e => longRangeEdgeProbability β (J e)) e X +
          (J e * Real.exp (-(β * J e))) * ∑ f ∈ (univ : Finset E).erase e,
            (J f * Real.exp (-(β * J f))) *
              pairPivotalMass (fun e => longRangeEdgeProbability β (J e)) e f X) := by
  have hP : ∀ e : E, ∀ s : ℝ,
      HasDerivAt (fun s => longRangeEdgeProbability s (J e))
        (J e * Real.exp (-(s * J e))) s :=
    fun e s => by simpa [mul_comm] using hasDerivAt_longRangeEdgeProbability s (J e)
  have hP' : ∀ e : E, DifferentiableAt ℝ (fun s => J e * Real.exp (-(s * J e))) β :=
    fun e => (hasDerivAt_longRangeEdgeProbability_deriv (J e) β).differentiableAt
  rw [deriv_deriv_expectation_general
    (P := fun e s => longRangeEdgeProbability s (J e))
    (P' := fun e s => J e * Real.exp (-(s * J e))) hP hP' X]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [(hasDerivAt_longRangeEdgeProbability_deriv (J e) β).deriv]

end PercLib.CriticalLRP.FiniteVolume
