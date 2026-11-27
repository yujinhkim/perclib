/-
Integrated and independently rebuilt from accepted Ultramath `smwywszgo`, member `m8`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwywszgo`, member `m8`, direction `d3`.

# End-to-end check: the `hae` hypothesis of the consumer, with no flux hypothesis

`OffCornerIdentity.lean` in this directory is a *copy* (for type-checking only) of member `m2`'s
direction-`d1` deliverable; it is not mine and is not part of my deliverable.  This file checks
that its off-corner five-tuple `ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two`
plugs into my corner elimination
`SmwywszgoM8.ae_hasDerivAt_toReal_two_tail_of_offCorner_identity`, giving the consumer's `hae` on
the whole tail `[r₀,∞)` with

* no off-corner hypothesis on the tail,
* no fixed-radius window-flux convergence `hfluxConv`,
* no window majorant,

the remaining inputs being `0 < r₀`, a monotone edge-exhausting window family, tail finiteness of
the second cutoff moment (the consumer's own `h2`), and a bound on `|M.coeffRHS|` on the tail.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentAllWindowAe
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.OffCornerIdentity

/-! # Composing off-corner identity with corner elimination -/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

variable (M : SourceModelData)

/-- **`hae` on the whole tail, from the off-corner identity alone.** -/
theorem ae_hasDerivAt_toReal_two_tail_noFlux {r₀ : ℝ} (hr₀ : 0 < r₀)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r : ℝ, r₀ ≤ r → |M.coeffRHS r| ≤ C) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  refine ae_hasDerivAt_toReal_two_tail_of_offCorner_identity M hr₀ ?_
  intro u v hru huv hoff
  have hcr : r₀ ≤ u := hru.le
  have hwin : M.IsOffCornerWindow u v := ⟨lt_trans hr₀ hru, huv.le, hoff⟩
  obtain ⟨-, -, -, hid, hint⟩ :=
    M.ac_and_ae_hasDerivAt_cutMomentReal_two_offCorner_of_cutMoment_two hwin S hSmono hS
      (h2 v (le_trans hcr huv.le)) hC0 (fun r hr => hC r (le_trans hcr hr.1))
  exact ⟨hint, hid⟩

/-- **The same with the coefficient bound discharged** by the model's sharpness field. -/
theorem ae_hasDerivAt_toReal_two_tail_noFlux_uniform :
    ∃ R : ℝ, ∀ ⦃r₀ : ℝ⦄, R ≤ r₀ → 0 < r₀ →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      (∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) →
      ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  obtain ⟨R, hR⟩ := exists_uniform_coeffRHS_bound_tail M
  refine ⟨R, fun {r₀} hRr₀ hr₀ S hSmono hS h2 => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hR r₀ hRr₀ hr₀
  exact ae_hasDerivAt_toReal_two_tail_noFlux M hr₀ S hSmono hS h2 hC0 hC

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM8

#print axioms ae_hasDerivAt_toReal_two_tail_noFlux
#print axioms ae_hasDerivAt_toReal_two_tail_noFlux_uniform

end PercLib.CriticalLRP.Orchestration.SmwywszgoM8
