/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I*, Lemma I.4.5(2), p. 35.

The divergent lower comparison requires no continuity hypothesis on `f'`.  If
`f > 0`, `f → ∞`, and `f' ≤ A r^(-α-1) f²` on `[r₀,∞)`, then the auxiliary
function `1/f − (A/α)r^(-α)` is nondecreasing and tends to zero.  It is
therefore nonpositive at every finite scale, which yields
`(α/A)r^α ≤ f r`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.ODENocont

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

/-- **Lemma I.4.5(2)** without a continuity hypothesis on `f'`. -/
theorem lemma_I_4_5_two_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hinf : Tendsto f atTop atTop)
    (hineq : ∀ x, r₀ ≤ x → f' x ≤ A * x ^ (-α - 1) * (f x) ^ 2) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r := by
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  have hHderiv : ∀ x, r₀ < x →
      HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have h := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at h
    have h2 : HasDerivAt (fun y => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h2
  have hHnonneg : ∀ x, r₀ < x →
      0 ≤ -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : f' x / (f x) ^ 2 ≤ A * x ^ (-α - 1) := by
      rw [div_le_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) =
        A * x ^ (-α - 1) - f' x / (f x) ^ 2 := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  have hmonoOn : MonotoneOn H (Ici r₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici r₀) ?_ ?_ ?_
    · intro x hx
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
    · intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonneg x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hkey : H r ≤ 0 := by
    have hmono : ∀ R, r ≤ R → H r ≤ H R := fun R hR =>
      hmonoOn (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have htend : Tendsto H atTop (𝓝 0) := by
      have hinv : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
      have hpow : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      have hlim := hinv.sub (hpow.const_mul (A / α))
      simpa only [hH, mul_zero, sub_zero] using hlim
    exact ge_of_tendsto htend (eventually_atTop.2 ⟨r, hmono⟩)
  have hfr : 0 < f r := hpos r hr
  have hbound : (f r)⁻¹ ≤ (A / α) * r ^ (-α) := by
    have h := hkey
    simp only [hH] at h
    linarith
  have hposB : 0 < (A / α) * r ^ (-α) := by positivity
  have hinv := (inv_le_comm₀ hfr hposB).mp hbound
  have heq : ((A / α) * r ^ (-α))⁻¹ = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, mul_inv, inv_inv]
    field_simp
  exact heq ▸ hinv

end PercLib.CriticalLRP.VolumeMoments

#print axioms PercLib.CriticalLRP.VolumeMoments.lemma_I_4_5_two_nocont
