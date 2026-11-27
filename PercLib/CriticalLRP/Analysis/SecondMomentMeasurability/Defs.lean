/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Dyadic right-approximants on the real line

Swarm `smwyvlg99`, member `m2`, direction `d2` (measurability of the `p = 2` second-moment
source).  The only new *definition* of the packet: the dyadic point immediately to the right of
`x` on the grid `2⁻ⁿ ℤ`,

`dyadicRight n x = (⌊2ⁿ x⌋ + 1) / 2ⁿ`.

The point of the definition is the strict inequality `x < dyadicRight n x`: the approximant
approaches `x` **from the right, strictly**, so a right-continuity hypothesis of the form
`Tendsto f (𝓝[>] x) (𝓝 (f x))` (which is exactly the shape produced by the landed radius
regularity of the second-moment source) applies to it without any `𝓝[≥]` weakening.  Every
function `x ↦ f (dyadicRight n x)` is measurable for *arbitrary* `f` (no regularity at all), because
the approximant factors through the countable type `ℤ`; that is the content of
`measurable_comp_dyadicRight`.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Dyadic right-approximants -/

set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Topology

namespace PercLib.CriticalLRP.Orchestration.Measurability

/-- The dyadic point immediately to the right of `x` on the grid `2⁻ⁿ ℤ`:
`(⌊2ⁿ x⌋ + 1) / 2ⁿ`. -/
def dyadicRight (n : ℕ) (x : ℝ) : ℝ := (((⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ) + 1) / (2 : ℝ) ^ n

theorem two_pow_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by positivity

/-- The approximant lies strictly to the right of `x`. -/
theorem lt_dyadicRight (n : ℕ) (x : ℝ) : x < dyadicRight n x := by
  have hpos := two_pow_pos n
  have h := Int.lt_floor_add_one ((2 : ℝ) ^ n * x)
  rw [dyadicRight, lt_div_iff₀ hpos]
  nlinarith [h]

/-- The approximant exceeds `x` by at most `2⁻ⁿ`. -/
theorem dyadicRight_le_add (n : ℕ) (x : ℝ) :
    dyadicRight n x ≤ x + ((2 : ℝ) ^ n)⁻¹ := by
  have hpos := two_pow_pos n
  have h := Int.floor_le ((2 : ℝ) ^ n * x)
  have hkey : (x + ((2 : ℝ) ^ n)⁻¹) * (2 : ℝ) ^ n = (2 : ℝ) ^ n * x + 1 := by
    field_simp
  rw [dyadicRight, div_le_iff₀ hpos, hkey]
  linarith [h]

/-- `2⁻ⁿ → 0`. -/
theorem tendsto_two_pow_inv : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The dyadic right-approximants of a fixed point converge to it. -/
theorem tendsto_dyadicRight (x : ℝ) :
    Tendsto (fun n : ℕ => dyadicRight n x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_two_pow_inv
  rw [Real.dist_eq, abs_of_nonneg (by linarith [lt_dyadicRight n x])]
  linarith [dyadicRight_le_add n x]

/-- The approximants approach `x` **from the right**: the filterised form actually used below. -/
theorem tendsto_dyadicRight_nhdsGT (x : ℝ) :
    Tendsto (fun n : ℕ => dyadicRight n x) atTop (𝓝[>] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_dyadicRight x, ?_⟩
  exact Eventually.of_forall fun n => lt_dyadicRight n x

/-- The floor of a dyadic multiple is measurable as a `ℤ`-valued function. -/
theorem measurable_floor_two_pow_mul (n : ℕ) :
    Measurable fun x : ℝ => ⌊(2 : ℝ) ^ n * x⌋ := by
  refine measurable_to_countable' fun k => ?_
  have hpos := two_pow_pos n
  have hset : (fun x : ℝ => ⌊(2 : ℝ) ^ n * x⌋) ⁻¹' {k}
      = Set.Ico ((k : ℝ) / (2 : ℝ) ^ n) (((k : ℝ) + 1) / (2 : ℝ) ^ n) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico, Int.floor_eq_iff,
      div_le_iff₀ hpos, lt_div_iff₀ hpos]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  rw [hset]
  exact measurableSet_Ico

/-- **Composition with a dyadic right-approximant is measurable for an arbitrary function.**

No measurability of `f` is used: the map factors through the countable type `ℤ`. -/
theorem measurable_comp_dyadicRight (f : ℝ → ℝ) (n : ℕ) :
    Measurable fun x : ℝ => f (dyadicRight n x) := by
  have h1 := measurable_floor_two_pow_mul n
  have h2 : Measurable fun k : ℤ => f (((k : ℝ) + 1) / (2 : ℝ) ^ n) :=
    measurable_of_countable _
  have h3 := h2.comp h1
  simpa [dyadicRight, Function.comp_def] using h3

end PercLib.CriticalLRP.Orchestration.Measurability

#print axioms PercLib.CriticalLRP.Orchestration.Measurability.measurable_comp_dyadicRight
#print axioms PercLib.CriticalLRP.Orchestration.Measurability.tendsto_dyadicRight_nhdsGT
