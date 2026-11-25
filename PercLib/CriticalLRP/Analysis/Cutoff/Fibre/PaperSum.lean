/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Full

/-!
# `PivotFlux.paperSum` as an unordered-edge sum

The paper's double sum `PivotFlux.paperSum M r ω = Σ_b Σ_c pivotWeight M r ω 0 b c` is the
ordered-pair (open-coordinate) form of the excluded flux at the source model's own two-point
distance predicate `cutDist M r`.  Composing

* `pairIncrFull_cutDist_eq_pivotWeight`: the paper's pivotal weight *is* the untruncated
  ordered-pair increment;
* `paperSum_eq_tsum_pairIncrFull`: the double sum is the `tsum` over ordered pairs;
* `tsum_pairIncrFull_eq_tsum_edgeIncrFull`: the ordered-pair `tsum` is the edge `tsum`;

gives `paperSum_eq_tsum_edgeIncrFull`, the closed-coordinate (edge) form of `paperSum` — the
combinatorial step left open by the per-edge excluded-flux packet.

No derivative, no moment and no interchange of derivative with a sum is used or claimed.
-/

set_option autoImplicit false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

/-- The paper's standardized pivotal weight at the anchor `0` is exactly the untruncated
ordered-pair excluded increment at the source's own distance predicate. -/
theorem pairIncrFull_cutDist_eq_pivotWeight (M : SourceModelData) (r : ℝ) (ω : Config M.V)
    (b c : M.V) :
    pairIncrFull (cutDist M r) ω 0 b c = PivotFlux.pivotWeight M r ω 0 b c := by
  simp only [pairIncrFull, cutDist, PivotFlux.pivotWeight, configIndicator, Set.indicator_apply,
    Set.mem_ofPred_eq]
  by_cases h1 : Connects ω 0 b <;> by_cases h2 : M.S.dist c b ≤ r <;>
    by_cases h3 : Connects ω b c <;> simp [h1, h2, h3]

/-- **The paper's double sum is the `tsum` of the untruncated ordered-pair increments.** -/
theorem paperSum_eq_tsum_pairIncrFull (M : SourceModelData) (r : ℝ) (ω : Config M.V) :
    PivotFlux.paperSum M r ω
      = ∑' p : M.V × M.V, pairIncrFull (cutDist M r) ω 0 p.1 p.2 := by
  calc PivotFlux.paperSum M r ω
      = ∑' b : M.V, ∑' c : M.V, PivotFlux.pivotWeight M r ω 0 b c := rfl
    _ = ∑' b : M.V, ∑' c : M.V, pairIncrFull (cutDist M r) ω 0 b c :=
        tsum_congr fun b => tsum_congr fun c =>
          (pairIncrFull_cutDist_eq_pivotWeight M r ω b c).symm
    _ = ∑' p : M.V × M.V, pairIncrFull (cutDist M r) ω 0 p.1 p.2 :=
        (ENNReal.tsum_prod (f := fun b c : M.V => pairIncrFull (cutDist M r) ω 0 b c)).symm

/-- **The paper's double sum as an unordered-edge sum.**  This is the closed-coordinate form of
`PivotFlux.paperSum` at `p = 1`: summing the standardized excluded weight over the edges of the
lattice, with the cluster volume `|K_c|` of the far endpoint, reproduces the paper's double sum
over ordered pairs. -/
theorem paperSum_eq_tsum_edgeIncrFull (M : SourceModelData) (r : ℝ) (ω : Config M.V) :
    PivotFlux.paperSum M r ω
      = ∑' e : Sym2 M.V, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω 0 e := by
  rw [paperSum_eq_tsum_pairIncrFull]
  exact tsum_pairIncrFull_eq_tsum_edgeIncrFull (cutDist M r) (cutDist_symm M r) ω 0

/-- **The finite-window form at the paper's own weight**: on a symmetric window `X` of vertices
the paper's ordered-pair double sum equals the edge sum of the untruncated edge increments. -/
theorem sum_pivotWeight_eq_sum_edgeIncrFull (M : SourceModelData) (r : ℝ) (ω : Config M.V)
    (X : Finset M.V) :
    ∑ x ∈ X, ∑ y ∈ X, PivotFlux.pivotWeight M r ω 0 x y
      = ∑ e ∈ X.sym2, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω 0 e := by
  rw [← sum_pairIncrFull_eq_sum_edgeIncrFull (cutDist M r) (cutDist_symm M r) ω 0 X]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    (pairIncrFull_cutDist_eq_pivotWeight M r ω x y).symm

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.pairIncrFull_cutDist_eq_pivotWeight
#print axioms PercLib.CriticalLRP.Orchestration.paperSum_eq_tsum_pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.paperSum_eq_tsum_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.sum_pivotWeight_eq_sum_edgeIncrFull

end PercLib.CriticalLRP.Orchestration
