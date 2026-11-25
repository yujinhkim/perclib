/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1 — the ODE engine behind Lemma I.4.9.

The paper's Lemma I.4.5(1) (`\label{lem:f'=f^2}`) is stated for a differentiable
`f : (0,∞) → (0,∞)` with `f' ≥ A r^{-α-1} f²`.  Its proof integrates `f'/f²`,
which needs `f'` continuous.  That hypothesis is *not* needed: the same
conclusion follows from the monotonicity of

  `H(r) = 1/f(r) - (A/α) r^{-α}`,

whose derivative is `-f'/f² + A r^{-α-1} ≤ 0`.  This matters for our use: in
Lemma I.4.9 the "derivative" is `(1-𝓔_{1,r,β}) β r^{-α-1} F²`, and the error
term `𝓔` has no continuity property to offer.  So we prove the continuity-free
form `lemma_I_4_5_one_nocont` here and do not import the extra hypothesis.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments

/-- **Lemma I.4.5(1)** without a continuity hypothesis on `f'`:
if `f > 0` and `f'(r) ≥ A r^{-α-1} f(r)²` for all `r ≥ r₀`, then
`f(r) ≤ (α/A) r^α` for all `r ≥ r₀`. -/
theorem lemma_I_4_5_one_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hineq : ∀ x, r₀ ≤ x → A * x ^ (-α - 1) * (f x) ^ 2 ≤ f' x) :
    ∀ r, r₀ ≤ r → f r ≤ α / A * r ^ α := by
  -- the auxiliary function
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  -- its derivative on `(r₀, ∞)`
  have hHderiv : ∀ x, r₀ < x → HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at this
    have h2 : HasDerivAt (fun y : ℝ => x ^ (-α)) 0 x := hasDerivAt_const x _
    have h3 : HasDerivAt (fun y : ℝ => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h3
  -- the derivative is nonpositive
  have hHnonpos : ∀ x, r₀ < x → -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) ≤ 0 := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : A * x ^ (-α - 1) ≤ f' x / (f x) ^ 2 := by
      rw [le_div_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))
        = -(f' x / (f x) ^ 2 - A * x ^ (-α - 1)) := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  -- hence `H` is antitone on `[r₀, ∞)`
  have hanti : AntitoneOn H (Ici r₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici r₀) ?_ ?_ ?_
    · -- continuity of `H` on `[r₀, ∞)`
      intro x hx
      rw [mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx' | hx'
      · subst hx'
        have hfcont : ContinuousAt f r₀ := (hderiv r₀ le_rfl).continuousAt
        have h1 : ContinuousAt (fun y => (f y)⁻¹) r₀ :=
          hfcont.inv₀ (ne_of_gt (hpos r₀ le_rfl))
        have h2 : ContinuousAt (fun y : ℝ => (A / α) * y ^ (-α)) r₀ :=
          (Real.continuousAt_rpow_const r₀ (-α) (Or.inl (ne_of_gt hr₀))).const_mul (A / α)
        exact (h1.sub h2).continuousWithinAt
      · exact (hHderiv x hx').differentiableAt.continuousAt.continuousWithinAt
    · -- differentiability on the interior
      intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · -- derivative sign
      intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonpos x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  -- `H r ≥ H R ≥ -(A/α) R^{-α}` for all `R ≥ r`, hence `H r ≥ 0`
  have hkey : 0 ≤ H r := by
    have hmono : ∀ R, r ≤ R → H R ≤ H r := fun R hR =>
      hanti (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have hlow : ∀ R, r ≤ R → -((A / α) * R ^ (-α)) ≤ H r := by
      intro R hR
      have hRpos : 0 < R := lt_of_lt_of_le hrpos hR
      have h1 : (0 : ℝ) ≤ (f R)⁻¹ := inv_nonneg.2 (le_of_lt (hpos R (le_trans hr hR)))
      have h2 : (f R)⁻¹ - (A / α) * R ^ (-α) ≤ H r := hmono R hR
      linarith
    have htend : Tendsto (fun R : ℝ => -((A / α) * R ^ (-α))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      simpa using (h0.const_mul (A / α)).neg
    exact le_of_tendsto htend (eventually_atTop.2 ⟨r, hlow⟩)
  -- conclude
  have hfr : 0 < f r := hpos r hr
  have hH' : (A / α) * r ^ (-α) ≤ (f r)⁻¹ := by
    have := hkey
    simp only [hH] at this
    linarith
  have h1 : (A / α) * r ^ (-α) * f r ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_right hH' (le_of_lt hfr)
    rwa [inv_mul_cancel₀ (ne_of_gt hfr)] at h2
  have h2 : f r ≤ 1 / ((A / α) * r ^ (-α)) := by
    rw [le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using h1
  have h3 : 1 / ((A / α) * r ^ (-α)) = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, one_div, mul_inv]
    field_simp
  linarith [h2, h3.le, h3.symm.le]

end PercLib.CriticalLRP.VolumeMoments
