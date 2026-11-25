/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from NearCritical/FiniteExpectation.lean at
tomhutchcroft/near-critical-diffusivity@c820fea91a7482c1755de0ec94ecb9f59ccfcacc,
under Tom Hutchcroft's reuse permission (docs/DECISIONS.md R-3).
The native upstream file has no licence header; no upstream Apache licence is asserted.
Changed on 2026-11-14: Set configurations, PercLib namespace and boundary examples.
-/
module

public import PercLib.Probability.ProductExpectation
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Powerset

/-!
# Homogeneous finite expectation as a polynomial

This is algebra on arbitrary real parameters. ProductExpectation connects it to
the existing probability law for unit-interval parameters. The profile derivative
and Russo formula are separate results.
-/

@[expose] public section

namespace PercLib.Probability

open Polynomial MeasureTheory
open scoped Classical

variable {E : Type*} [Fintype E]

/-- The polynomial averaging an observable over independent homogeneous coordinates. -/
noncomputable def annealedPolynomial (f : Set E → ℝ) : Polynomial ℝ := by
  classical
  exact ∑ ω : Set E, C (f ω) * ∏ e : E, if e ∈ ω then X else 1 - X

/-- The explicit finite expectation, extended algebraically to every real parameter. -/
noncomputable def finiteExpectation (p : ℝ) (f : Set E → ℝ) : ℝ := by
  classical
  exact ∑ ω : Set E, f ω * ∏ e : E, if e ∈ ω then p else 1 - p

theorem eval_annealedPolynomial (p : ℝ) (f : Set E → ℝ) :
    (annealedPolynomial f).eval p = finiteExpectation p f := by
  classical
  simp [annealedPolynomial, finiteExpectation, Polynomial.eval_finsetSum,
    Polynomial.eval_prod, apply_ite]

/-- Differentiability holds on the whole real line, including probability endpoints. -/
theorem finiteExpectation_hasDerivAt (p : ℝ) (f : Set E → ℝ) :
    HasDerivAt (fun q => finiteExpectation q f)
      ((annealedPolynomial f).derivative.eval p) p := by
  simpa only [eval_annealedPolynomial] using (annealedPolynomial f).hasDerivAt p

/-- On the unit interval the algebraic expectation is the existing product-law integral. -/
theorem finiteExpectation_eq_integral (p : unitInterval) (f : Set E → ℝ) :
    finiteExpectation (p : ℝ) f = ∫ ω, f ω ∂prodBernoulli (fun _ => p) := by
  rw [integral_prodBernoulli]
  rfl

/-- The polynomial evaluated at a probability parameter is the canonical expectation. -/
theorem eval_annealedPolynomial_eq_integral (p : unitInterval) (f : Set E → ℝ) :
    (annealedPolynomial f).eval (p : ℝ) = ∫ ω, f ω ∂prodBernoulli (fun _ => p) := by
  rw [eval_annealedPolynomial, finiteExpectation_eq_integral]

example (p : ℝ) (f : Set Empty → ℝ) : finiteExpectation p f = f ∅ := by
  classical
  simp [finiteExpectation]
  exact congrArg f (Subsingleton.elim _ _)

example (p : ℝ) : finiteExpectation p (fun _ : Set E => 0) = 0 := by
  classical
  simp [finiteExpectation]

example (p : ℝ) : finiteExpectation p (fun ω : Set Unit => if () ∈ ω then 1 else 0) = p := by
  classical
  unfold finiteExpectation
  rw [Finset.sum_eq_single (Set.univ : Set Unit)]
  · simp
  · intro ω _ hω
    have hu : () ∉ ω := by
      intro h
      apply hω
      ext u
      simpa using h
    simp [hu]
  · simp

end PercLib.Probability
