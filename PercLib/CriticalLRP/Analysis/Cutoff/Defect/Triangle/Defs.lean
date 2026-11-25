/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Cutoff two-point functions and window triangles

Reviewed from Ultramath `smwtrtcqs`, member `m5`. These definitions use the
actual source norm; comparison with the uncut triangle and finite-moment
hypotheses are handled separately in the proof module.
-/

module

/-
Candidate definitions for the model-level window triangle of Lemma I.4.11.

These are the actual cutoff two-point function and its windowed triangle diagram
`∇_r(0,y) = ∑_a ∑_b τ_r(0,a) τ_r(a,b) τ_r(b,y)` at `SourceModelData`, i.e. at the
Definition I.1.5 cutoff law with an arbitrary normalized norm `M.S.ρ`.
-/

public import PercLib.CriticalLRP.Correlation.I411.Cutoff
public import PercLib.CriticalLRP.Orchestration.Defs

/-! # Cutoff two-point and triangle definitions -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The cutoff two-point function `τ_r(x,y) = P_{β_c,r}(x ↔ y)` of the source model. -/
noncomputable def cutTau (r : ℝ) (x y : M.V) : ℝ≥0∞ :=
  twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit x y

/-- `τ_r` is the model's own cutoff law evaluated at the connection event. -/
theorem cutTau_eq_cutLaw (r : ℝ) (x y : M.V) :
    cutTau M r x y = M.cutLaw r {ω : Config M.V | Connects ω x y} := rfl

/-- The windowed cutoff triangle diagram `∇_r(0,y)`. -/
noncomputable def cutTriangleNabla (r : ℝ) (y : M.V) : ℝ≥0∞ :=
  ∑' a : M.V, ∑' b : M.V, cutTau M r 0 a * cutTau M r a b * cutTau M r b y

/-- The windowed triangle sum `∑_{y∈B} ∇_r(0,y)` over a finite window `B`. -/
noncomputable def windowTriangle (r : ℝ) (B : Finset M.V) : ℝ≥0∞ :=
  ∑ y ∈ B, cutTriangleNabla M r y

/-- Unfolding form of `windowTriangle`: the sum of triple convolutions over the window. -/
theorem windowTriangle_eq (r : ℝ) (B : Finset M.V) :
    windowTriangle M r B = ∑ y ∈ B, ∑' a : M.V, ∑' b : M.V,
      twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit 0 a *
        twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b *
          twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit b y := rfl

end E1Sign
end PercLib.CriticalLRP
