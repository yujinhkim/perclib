/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Limit
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.PaperSum

/-!
# `PivotFlux.paperSum` as the truncation limit of the model's summed excluded increments

Combining the identification of `paperSum` with the untruncated ordered-pair (respectively
edge) `tsum` of `Fibre.PaperSum` with the truncation limit of `Fibre.Limit`:

* `paperSum_eq_iSup_tsum_pairIncr`:
  `paperSum M r ω = ⨆ A, Σ'_p pairIncr (cutDist M r) ω 0 A p.1 p.2`;
* `paperSum_eq_iSup_tsum_edgeIncr`:
  `paperSum M r ω = ⨆ A, Σ'_e edgeIncr (cutDist M r) hd ω 0 A e`.

So the paper's double sum is exactly the supremum, over finite vertex truncations, of the summed
*excluded increment* of the model — on the open (ordered-pair) or the closed (edge) side.  This is
still a statement about the integrand only: no expectation, no derivative, no infinite moment.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

/-- The paper's double sum is the supremum over finite vertex truncations of the summed
ordered-pair excluded increment. -/
theorem paperSum_eq_iSup_tsum_pairIncr (M : SourceModelData) (r : ℝ) (ω : Config M.V) :
    PivotFlux.paperSum M r ω
      = ⨆ A : Finset M.V, ∑' p : M.V × M.V,
          pairIncr (cutDist M r) ω 0 A p.1 p.2 := by
  rw [paperSum_eq_tsum_pairIncrFull]
  exact (iSup_tsum_pairIncr_eq_tsum_pairIncrFull (cutDist M r) ω 0).symm

/-- The paper's double sum is the supremum over finite vertex truncations of the summed
edge excluded increment. -/
theorem paperSum_eq_iSup_tsum_edgeIncr (M : SourceModelData) (r : ℝ) (ω : Config M.V) :
    PivotFlux.paperSum M r ω
      = ⨆ A : Finset M.V, ∑' e : Sym2 M.V,
          edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e := by
  rw [paperSum_eq_tsum_edgeIncrFull]
  exact (iSup_tsum_edgeIncr_eq_tsum_edgeIncrFull (cutDist M r) (cutDist_symm M r) ω 0).symm

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.paperSum_eq_iSup_tsum_pairIncr
#print axioms PercLib.CriticalLRP.Orchestration.paperSum_eq_iSup_tsum_edgeIncr

end PercLib.CriticalLRP.Orchestration
