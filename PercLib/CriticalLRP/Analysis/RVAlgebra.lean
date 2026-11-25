/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Algebra of regular variation and of Potter's bounds.

These are the manipulations used in the paper when it passes from one regularly
varying quantity to another (e.g. in the proof of Lemma I.4.21, where the
integrand `s^{-1} h(s) exp(-∫ (1-δ)a/t)` is asserted to be regularly varying of
index `b - a - 1 > -1` and then fed into Lemma I.2.10), together with the
corresponding preservation statements for the Potter bounds consumed by
`lemma_I_2_10`.

None of these need the uniform convergence theorem: products, reciprocals and
powers are handled pointwise from the definition `RegularlyVaryingAtTop`, and
the Potter bounds for `x ↦ x^a f x` follow from those of `f` because the factor
`x^a` is exact.
-/
module

public import PercLib.CriticalLRP.Analysis.Karamata
public import PercLib.CriticalLRP.Analysis.RegularVariation

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-! ### Products, reciprocals and powers of regularly varying functions -/

/-- The product of regularly varying functions is regularly varying, with the
sum of the indices. -/
theorem RegularlyVaryingAtTop.mul {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVaryingAtTop f α) (hg : RegularlyVaryingAtTop g β) :
    RegularlyVaryingAtTop (fun x => f x * g x) (α + β) := by
  constructor
  · filter_upwards [hf.1, hg.1] with x hx hy
    exact mul_ne_zero hx hy
  · intro l hl
    have h1 := hf.2 l hl
    have h2 := hg.2 l hl
    have h3 : Tendsto (fun x => f (l * x) / f x * (g (l * x) / g x)) atTop (𝓝 (l ^ α * l ^ β)) :=
      h1.mul h2
    rw [← Real.rpow_add hl] at h3
    refine h3.congr' ?_
    filter_upwards [hf.1, hg.1] with x hx hy
    field_simp

/-- The pointwise reciprocal of a regularly varying function is regularly varying
with negated index. -/
theorem RegularlyVaryingAtTop.inv {f : ℝ → ℝ} {α : ℝ} (hf : RegularlyVaryingAtTop f α) :
    RegularlyVaryingAtTop (fun x => (f x)⁻¹) (-α) := by
  constructor
  · filter_upwards [hf.1] with x hx
    simp [hx]
  · intro l hl
    have h1 : Tendsto (fun x => (f (l * x) / f x)⁻¹) atTop (𝓝 (l ^ (-α))) := by
      have h0 : Tendsto (fun x => (f (l * x) / f x)⁻¹) atTop (𝓝 ((l ^ α)⁻¹)) :=
        (hf.2 l hl).inv₀ (by positivity)
      rw [← Real.rpow_neg hl.le α] at h0
      exact h0
    refine h1.congr' ?_
    filter_upwards [hf.1] with x hx
    field_simp

/-- `x ↦ x ^ a` is regularly varying of index `a`. -/
theorem regularlyVaryingAtTop_rpow (a : ℝ) : RegularlyVaryingAtTop (fun x : ℝ => x ^ a) a := by
  constructor
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact ne_of_gt (Real.rpow_pos_of_pos hx a)
  · intro l hl
    have h : (fun x : ℝ => (l * x) ^ a / x ^ a) =ᶠ[atTop] fun _ => l ^ a := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [Real.mul_rpow hl.le hx.le, mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx a))]
    exact tendsto_const_nhds.congr' h.symm

/-- Positive powers of regularly varying functions are regularly varying, with the index
multiplied by the exponent. Eventual positivity is needed for the quotient of powers. -/
theorem RegularlyVaryingAtTop.rpow {f : ℝ → ℝ} {ρ a : ℝ}
    (hf : RegularlyVaryingAtTop f ρ) (hp : ∀ᶠ x in atTop, 0 < f x) :
    RegularlyVaryingAtTop (fun x => (f x) ^ a) (ρ * a) := by
  constructor
  · filter_upwards [hp] with x hx
    exact (Real.rpow_pos_of_pos hx a).ne'
  · intro l hl
    have hpow : ContinuousAt (fun y : ℝ => y ^ a) (l ^ ρ) :=
      Real.continuousAt_rpow_const _ _ (Or.inl (Real.rpow_pos_of_pos hl ρ).ne')
    have hlim := hpow.tendsto.comp (hf.2 l hl)
    rw [← Real.rpow_mul hl.le] at hlim
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop := tendsto_id.const_mul_atTop hl
    refine hlim.congr' ?_
    filter_upwards [hp, hscale.eventually hp] with x hx hlhx
    exact Real.div_rpow hlhx.le hx.le a

/-! ### Algebra of Potter's bounds -/

/-- Potter's bounds are preserved when multiplying by an exact power `x ^ a`
(the index shifts by `a`).  This is the step by which `lemma_I_2_10` is applied
to an integrand of the form "power of `r` times a regularly varying `h`". -/
theorem HasPotterBounds.mul_rpow {f : ℝ → ℝ} {α : ℝ} (hpot : HasPotterBounds f α) (a : ℝ) :
    HasPotterBounds (fun x => x ^ a * f x) (α + a) := by
  intro ε hε
  obtain ⟨X, hX1, hX⟩ := hpot ε hε
  refine ⟨max X 1, le_trans hX1 (le_max_left _ _), fun x y hy hyx => ?_⟩
  have hXy : X ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hxpos : 0 < x := lt_of_lt_of_le hypos hyx
  obtain ⟨hlo, hhi⟩ := hX x y hXy hyx
  have hyn : |y ^ a * f y| = y ^ a * |f y| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hypos.le a)]
  have hxn : |x ^ a * f x| = x ^ a * |f x| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hxpos.le a)]
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hxpos.le a
  have hya : 0 ≤ y ^ a := Real.rpow_nonneg hypos.le a
  have hdiv : 0 < x / y := div_pos hxpos hypos
  have hkey2 : x ^ a = (x / y) ^ a * y ^ a := by
    rw [Real.div_rpow hxpos.le hypos.le,
      div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hypos a))]
  have hkey3 : (x / y) ^ (α - ε) * x ^ a = (x / y) ^ (α + a - ε) * y ^ a := by
    rw [hkey2, ← mul_assoc, ← Real.rpow_add hdiv, show α - ε + a = α + a - ε by ring]
  have hkey4 : (x / y) ^ (α + ε) * x ^ a = (x / y) ^ (α + a + ε) * y ^ a := by
    rw [hkey2, ← mul_assoc, ← Real.rpow_add hdiv, show α + ε + a = α + a + ε by ring]
  constructor
  · rw [hyn, hxn]
    have hshape : (1 - ε) * (x / y) ^ (α + a - ε) * (y ^ a * |f y|)
        = (1 - ε) * ((x / y) ^ (α - ε) * x ^ a) * |f y| := by
      rw [hkey3]
      ring
    rw [hshape]
    calc (1 - ε) * ((x / y) ^ (α - ε) * x ^ a) * |f y|
        = (1 - ε) * (x / y) ^ (α - ε) * |f y| * x ^ a := by ring
      _ ≤ |f x| * x ^ a := mul_le_mul_of_nonneg_right hlo hxa
      _ = x ^ a * |f x| := by ring
  · rw [hxn, hyn]
    calc x ^ a * |f x|
        ≤ x ^ a * ((1 + ε) * (x / y) ^ (α + ε) * |f y|) :=
          mul_le_mul_of_nonneg_left hhi hxa
      _ = (1 + ε) * ((x / y) ^ (α + ε) * x ^ a) * |f y| := by ring
      _ = (1 + ε) * (x / y) ^ (α + a + ε) * (y ^ a * |f y|) := by
          rw [hkey4]; ring

/-- Potter's bounds are preserved when multiplying by a nonzero constant. -/
theorem HasPotterBounds.const_mul {f : ℝ → ℝ} {α c : ℝ} (hpot : HasPotterBounds f α)
    (hc : c ≠ 0) : HasPotterBounds (fun x => c * f x) α := by
  intro ε hε
  obtain ⟨X, hX1, hX⟩ := hpot ε hε
  refine ⟨max X 1, le_trans hX1 (le_max_left _ _), fun x y hy hyx => ?_⟩
  obtain ⟨hlo, hhi⟩ := hX x y (le_trans (le_max_left _ _) hy) hyx
  have hcabs : 0 < |c| := abs_pos.2 hc
  constructor
  · rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left hlo hcabs.le
    linarith [this]
  · rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left hhi hcabs.le
    linarith [this]


/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.mul
#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.inv
#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.rpow
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_rpow
#print axioms PercLib.CriticalLRP.Analysis.HasPotterBounds.mul_rpow
#print axioms PercLib.CriticalLRP.Analysis.HasPotterBounds.const_mul
