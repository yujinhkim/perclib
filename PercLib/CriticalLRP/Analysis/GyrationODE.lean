/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Proposition I.5.2 from a gyration ODE: the exact ODE, its solution, and the
three regime asymptotics

Source: T. Hutchcroft, *Critical long-range percolation I*,
  - `prop:radius_of_gyration` (book draft Prop. I.5.2),
  - `lem:gyration_derivative` (Lemma I.5.7),
  - `lem:gyration_derivative2` (Lemma I.5.8).

Lemma I.5.7 states

  d/dr E_{β_c,r}[ Σ_{x ∈ K} <x,u>² ]  ~  (2α/r) E_{β_c,r}[Σ_{x∈K}<x,u>²]
        + (α²/β_c) r^{2+α-1} ∫_B <y,u>² dy .

Writing `F r = E_{β_c,r}[Σ_{x∈K}<x,u>²]`, `c = α²/β_c` and `Q = ∫_B <y,u>² dy`,
the *exact* equation

  F'(r) = (2α/r) F(r) + c Q r^{α+1}

is an explicitly solvable linear ODE.  This file solves it rigorously
(`gyration_ratio_form`, `gyration_ratio_form_two`, `gyration_exact`) using the
integrating factor `r ↦ r^{-2α}` and the constancy of a function with vanishing
derivative on the connected set `(0,∞)` — no primitive derivative is assumed and
no continuity of any error term is needed.  Consequences proved here:

* `tendsto_div_rpow_of_lt` (`α < 2`): `F r / r^{2+α} → c Q/(2-α)`.
* `tendsto_div_rpow_log` (`α = 2`):  `F r / (r^4 log r) → c Q`.
* `tendsto_div_rpow_of_gt` (`α > 2`): `F r / r^{2α} → F 1 + c Q/(α-2)`.

The corresponding regular-variation statements are in `GyrationRV.lean`; the
passage from the *asymptotic* statement of Lemma I.5.7 (via the project's
formalised Lemmas I.4.21, I.5.5, I.5.6) is in `GyrationReduction.lean`.
-/

module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.Gyration

/-! ### The exact ODE and the explicit solution for `α ≠ 2` -/

/-- Derivative of the integrating factor: for `α ≠ 2` the function
`s ↦ F s * s^{-2α} - c Q s^{2-α}/(2-α)` has vanishing derivative at every `s > 0`
whenever `F' = 2α F/s + c Q s^{α+1}`. -/
theorem hasDerivAt_gyration_primitive {F : ℝ → ℝ} {α c Q : ℝ} (hα : α ≠ 2)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r) :
    ∀ r : ℝ, 0 < r →
      HasDerivAt (fun s => F s * s ^ (-(2 * α)) - c * Q * s ^ (2 - α) / (2 - α)) 0 r := by
  intro r hr
  have hrne : r ≠ 0 := hr.ne'
  have h4 : (2 : ℝ) - α ≠ 0 := sub_ne_zero.mpr hα.symm
  have hp1 : HasDerivAt (fun s : ℝ => s ^ (-(2 * α))) ((-(2 * α)) * r ^ (-(2 * α) - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hrne)
  have hmul := (hF r hr).mul hp1
  have hp2 : HasDerivAt (fun s : ℝ => s ^ (2 - α)) ((2 - α) * r ^ (2 - α - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hrne)
  have hdiv : HasDerivAt (fun s : ℝ => c * Q * s ^ (2 - α) / (2 - α))
      (c * Q * ((2 - α) * r ^ (2 - α - 1)) / (2 - α)) r :=
    (hp2.const_mul (c * Q)).div_const (2 - α)
  refine (hmul.sub hdiv).congr_deriv ?_
  have hA : r ^ (-(2 * α) - 1) = r ^ (-(2 * α)) / r := by
    rw [Real.rpow_sub hr, Real.rpow_one]
  have hB : r ^ (2 - α - 1) = r ^ (1 - α) := by
    rw [show 2 - α - 1 = 1 - α by ring]
  have hC : r ^ (1 - α) = r ^ (α + 1) * r ^ (-(2 * α)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hv : ((2 * α / r) * F r + c * r ^ (α + 1) * Q) * r ^ (-(2 * α)) +
        F r * (-(2 * α) * r ^ (-(2 * α) - 1)) -
        c * Q * ((2 - α) * r ^ (2 - α - 1)) / (2 - α)
      = 2 * α * F r * (r ^ (-(2 * α)) / r) - 2 * α * F r * r ^ (-(2 * α) - 1) +
        c * Q * (r ^ (α + 1) * r ^ (-(2 * α))) - c * Q * r ^ (2 - α - 1) := by
    field_simp
    ring
  rw [hv, hA, hB, ← hC]
  ring

/-- **Solution of the exact gyration ODE, ratio form** (`α ≠ 2`). -/
theorem gyration_ratio_form {F : ℝ → ℝ} {α c Q : ℝ} (hα : α ≠ 2)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r) :
    ∀ r : ℝ, 0 < r →
      F r * r ^ (-(2 * α)) = F 1 - c * Q / (2 - α) + c * Q * r ^ (2 - α) / (2 - α) := by
  set H : ℝ → ℝ := fun s => F s * s ^ (-(2 * α)) - c * Q * s ^ (2 - α) / (2 - α) with hH
  have hderivH : ∀ s : ℝ, 0 < s → HasDerivAt H 0 s := hasDerivAt_gyration_primitive hα hF
  have hdiff : DifferentiableOn ℝ H (Set.Ioi 0) := fun x hx =>
    (hderivH x hx).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv H) 0 (Set.Ioi 0) := by
    intro x hx
    rw [(hderivH x hx).deriv]
    rfl
  intro r hr
  have heq : H r = H 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hr
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  simp only [hH, Real.one_rpow, mul_one] at heq
  linarith

/-- **Solution of the exact gyration ODE** (`α ≠ 2`). -/
theorem gyration_exact {F : ℝ → ℝ} {α c Q : ℝ} (hα : α ≠ 2)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r) :
    ∀ r : ℝ, 0 < r →
      F r = r ^ (2 * α) * F 1 + (c * Q / (2 - α)) * (r ^ (2 + α) - r ^ (2 * α)) := by
  intro r hr
  have hmain := gyration_ratio_form hα hF r hr
  have h1 : r ^ (-(2 * α)) * r ^ (2 * α) = 1 := by
    rw [← Real.rpow_add hr]
    simp
  have h2 : r ^ (2 - α) * r ^ (2 * α) = r ^ (2 + α) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hmul : F r = (F 1 - c * Q / (2 - α) + c * Q * r ^ (2 - α) / (2 - α)) * r ^ (2 * α) := by
    have h := congr_arg (fun t => t * r ^ (2 * α)) hmain
    rwa [show F r * r ^ (-(2 * α)) * r ^ (2 * α) = F r by rw [mul_assoc, h1, mul_one]]
      at h
  rw [hmul, ← h2]
  field_simp
  ring

/-! ### The three regime asymptotics -/

/-- `r^{α-2} → 0` when `α < 2`. -/
theorem tendsto_rpow_sub_two {α : ℝ} (hα : α < 2) :
    Tendsto (fun r : ℝ => r ^ (α - 2)) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (y := 2 - α) (by linarith)
  refine h.congr' ?_
  filter_upwards with r
  rw [show -(2 - α) = α - 2 by ring]

/-- **`α < 2`, exact ODE:** `F r / r^{2+α} → c Q/(2-α)`. -/
theorem tendsto_div_rpow_of_lt {F : ℝ → ℝ} {α c Q : ℝ} (hα : α < 2)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r) :
    Tendsto (fun r => F r / r ^ (2 + α)) atTop (𝓝 (c * Q / (2 - α))) := by
  have hα2 : α ≠ 2 := ne_of_lt hα
  have htend := tendsto_rpow_sub_two hα
  have hlim : Tendsto (fun r : ℝ =>
      (F 1 - c * Q / (2 - α)) * r ^ (α - 2) + c * Q / (2 - α)) atTop (𝓝 (c * Q / (2 - α))) := by
    simpa using (htend.const_mul (F 1 - c * Q / (2 - α))).add tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hmain := gyration_ratio_form hα2 hF r hr
  have hsplit : F r / r ^ (2 + α) = (F r * r ^ (-(2 * α))) * r ^ (α - 2) := by
    have h1 : r ^ (-(2 * α)) * r ^ (α - 2) = (r ^ (2 + α))⁻¹ := by
      rw [← Real.rpow_add hr, ← Real.rpow_neg (le_of_lt hr)]
      congr 2
      ring
    rw [div_eq_mul_inv, mul_assoc, h1]
  have hshift : r ^ (2 - α) * r ^ (α - 2) = 1 := by
    rw [← Real.rpow_add hr]
    simp
  have hfinal : (F 1 - c * Q / (2 - α) + c * Q * r ^ (2 - α) / (2 - α)) * r ^ (α - 2)
      = (F 1 - c * Q / (2 - α)) * r ^ (α - 2) + c * Q / (2 - α) := by
    have hsplit2 : c * Q * r ^ (2 - α) / (2 - α) * r ^ (α - 2)
        = c * Q / (2 - α) * (r ^ (2 - α) * r ^ (α - 2)) := by ring
    rw [add_mul, hsplit2, hshift]
    ring
  rw [hsplit, hmain, hfinal]

/-- **`α > 2`, exact ODE:** `F r / r^{2α} → F 1 + c Q/(α-2)`. -/
theorem tendsto_div_rpow_of_gt {F : ℝ → ℝ} {α c Q : ℝ} (hα : 2 < α)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r) :
    Tendsto (fun r => F r / r ^ (2 * α)) atTop (𝓝 (F 1 + c * Q / (α - 2))) := by
  have hα2 : α ≠ 2 := ne_of_gt hα
  have htend : Tendsto (fun r : ℝ => r ^ (2 - α)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := α - 2) (by linarith)
    refine h.congr' ?_
    filter_upwards with r
    rw [show -(α - 2) = 2 - α by ring]
  have hlim : Tendsto (fun r : ℝ =>
      (F 1 - c * Q / (2 - α)) + c * Q * r ^ (2 - α) / (2 - α)) atTop
      (𝓝 (F 1 - c * Q / (2 - α))) := by
    have h0 : Tendsto (fun r : ℝ => c * Q * r ^ (2 - α) / (2 - α)) atTop (𝓝 0) := by
      simpa using (htend.const_mul (c * Q)).div_const (2 - α)
    simpa using tendsto_const_nhds.add h0
  have hconst : F 1 - c * Q / (2 - α) = F 1 + c * Q / (α - 2) := by
    have h5 : α - 2 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < α - 2)
    have h4 : (2 : ℝ) - α ≠ 0 := sub_ne_zero.mpr hα2.symm
    field_simp
    ring
  have key : Tendsto (fun r => F r / r ^ (2 * α)) atTop (𝓝 (F 1 - c * Q / (2 - α))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hmain := gyration_ratio_form hα2 hF r hr
    have hsplit : F r / r ^ (2 * α) = F r * r ^ (-(2 * α)) := by
      have h1 : r ^ (-(2 * α)) = (r ^ (2 * α))⁻¹ := Real.rpow_neg (le_of_lt hr) (2 * α)
      rw [div_eq_mul_inv, h1]
    rw [hsplit, hmain]
  rwa [hconst] at key

/-! ### The critical case `α = 2` -/

/-- **Critical `α = 2`:** the primitive `F s * s^{-4} - c Q log s` has zero derivative. -/
theorem hasDerivAt_gyration_primitive_two {F : ℝ → ℝ} {c Q : ℝ}
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((4 / r) * F r + c * r ^ ((2 : ℝ) + 1) * Q) r) :
    ∀ r : ℝ, 0 < r →
      HasDerivAt (fun s => F s * s ^ (-(4 : ℝ)) - c * Q * Real.log s) 0 r := by
  intro r hr
  have hrne : r ≠ 0 := hr.ne'
  have hp1 : HasDerivAt (fun s : ℝ => s ^ (-(4 : ℝ))) ((-(4 : ℝ)) * r ^ (-(4 : ℝ) - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hrne)
  have hmul := (hF r hr).mul hp1
  have hlog : HasDerivAt (fun s : ℝ => c * Q * Real.log s) (c * Q * r⁻¹) r :=
    (Real.hasDerivAt_log hrne).const_mul (c * Q)
  refine (hmul.sub hlog).congr_deriv ?_
  have hA : r ^ (-(4 : ℝ) - 1) = r ^ (-(4 : ℝ)) / r := by
    rw [Real.rpow_sub hr, Real.rpow_one]
  have h1 : r ^ (-(4 : ℝ) - 1) = r ^ (-(4 : ℝ)) * r⁻¹ := by
    rw [hA, div_eq_mul_inv]
  have h3 : r ^ ((2 : ℝ) + 1) * r ^ (-(4 : ℝ)) = r⁻¹ := by
    rw [← Real.rpow_add hr, show (2:ℝ) + 1 + -(4:ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h3' : c * r ^ ((2 : ℝ) + 1) * Q * r ^ (-(4 : ℝ)) = c * Q * r⁻¹ := by
    calc c * r ^ ((2 : ℝ) + 1) * Q * r ^ (-(4 : ℝ))
        = c * Q * (r ^ ((2 : ℝ) + 1) * r ^ (-(4 : ℝ))) := by ring
      _ = c * Q * r⁻¹ := by rw [h3]
  rw [div_eq_mul_inv, h1, add_mul, h3']
  ring

/-- **Solution of the exact gyration ODE at `α = 2`, ratio form.** -/
theorem gyration_ratio_form_two {F : ℝ → ℝ} {c Q : ℝ}
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((4 / r) * F r + c * r ^ ((2 : ℝ) + 1) * Q) r) :
    ∀ r : ℝ, 0 < r → F r * r ^ (-(4 : ℝ)) = F 1 + c * Q * Real.log r := by
  set H : ℝ → ℝ := fun s => F s * s ^ (-(4 : ℝ)) - c * Q * Real.log s with hH
  have hderivH : ∀ s : ℝ, 0 < s → HasDerivAt H 0 s := hasDerivAt_gyration_primitive_two hF
  have hdiff : DifferentiableOn ℝ H (Set.Ioi 0) := fun x hx =>
    (hderivH x hx).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv H) 0 (Set.Ioi 0) := by
    intro x hx
    rw [(hderivH x hx).deriv]
    rfl
  intro r hr
  have heq : H r = H 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hr
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  simp only [hH, Real.one_rpow, Real.log_one, mul_zero, sub_zero] at heq
  linarith

/-- **`α = 2`, exact ODE:** `F r / (r^4 log r) → c Q`. -/
theorem tendsto_div_rpow_log {F : ℝ → ℝ} {c Q : ℝ}
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((4 / r) * F r + c * r ^ ((2 : ℝ) + 1) * Q) r) :
    Tendsto (fun r => F r / (r ^ (4 : ℝ) * Real.log r)) atTop (𝓝 (c * Q)) := by
  have hlog : Tendsto (fun r : ℝ => Real.log r) atTop atTop := Real.tendsto_log_atTop
  have hlim : Tendsto (fun r : ℝ => F 1 / Real.log r + c * Q) atTop (𝓝 (c * Q)) := by
    have h0 : Tendsto (fun r : ℝ => F 1 / Real.log r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    simpa using h0.add tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  have hlogpos : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
  have hmain := gyration_ratio_form_two hF r hr0
  have hsplit : F r / (r ^ (4 : ℝ) * Real.log r) = (F r * r ^ (-(4 : ℝ))) / Real.log r := by
    have h1 : (r ^ (4 : ℝ) * Real.log r)⁻¹ = r ^ (-(4 : ℝ)) / Real.log r := by
      rw [mul_inv, Real.rpow_neg (le_of_lt hr0), div_eq_mul_inv]
    rw [div_eq_mul_inv, h1, div_eq_mul_inv]
    ring
  rw [hsplit, hmain]
  field_simp

end PercLib.CriticalLRP.Analysis.Gyration
