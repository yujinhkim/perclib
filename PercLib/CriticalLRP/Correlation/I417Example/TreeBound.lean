/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/TreeBound.lean ; module path rewritten only.
-/

/-
# The three-terminal tree-graph inequality for the canonical model

For a configuration in which `x₁`, `x₂` and `w` all lie in the cluster of `x`, the two-level
branch decomposition (`I417Example/Branch.exists_two_level_branch`) produces one of the three five-edge
diagrams `D2`, `D3a`, `D3b`.  A union bound over the interior vertices `(u, v)` and the iterated
BK inequality (`I417Example/BK.tree5_le`) therefore give

  `P(x₁, x₂, w ∈ Kx) ≤ ∑_{u,v} τ(x,u)τ(u,w)τ(u,v)τ(v,x₁)τ(v,x₂)`
  `                 + ∑_{u,v} τ(x,v)τ(v,u)τ(u,w)τ(u,x₁)τ(v,x₂)`
  `                 + ∑_{u,v} τ(x,u)τ(u,v)τ(v,w)τ(u,x₁)τ(v,x₂)`,

where `τ = P(· ↔ ·)`.  This is the tree-graph expansion of the printed proof ("expanding each of
these probabilities out as in the proof of the tree-graph inequality") at `p = 2`, in the exact
form in which the weighted vertices `w` (the mark) and `x₁, x₂` (the two cluster-volume terms)
enter.

Only `π e < 1` is assumed (BK for the canonical model).
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Branch
public import PercLib.CriticalLRP.Correlation.I417Example.BK

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

variable {V : Type*} [Countable V]

/-- **Three-terminal tree-graph inequality.**  The probability that three prescribed vertices
`x₁`, `x₂`, `w` all lie in the cluster of `x` is at most the sum of the three five-edge tree
diagrams with interior vertices summed over. -/
theorem threeLeaf_treeGraph (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x w x₁ x₂ : V) :
    (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) ≤
      (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
          (edgeMeasure π) (connSet u v) * (edgeMeasure π) (connSet v x₁) *
          (edgeMeasure π) (connSet v x₂)) +
        (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
          (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u x₁) *
          (edgeMeasure π) (connSet v x₂)) +
        (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
          (edgeMeasure π) (connSet v w) * (edgeMeasure π) (connSet u x₁) *
          (edgeMeasure π) (connSet v x₂)) := by
  classical
  -- the deterministic cover
  have hcover : connSet x x₁ ∩ connSet x x₂ ∩ connSet x w ⊆
      ((⋃ u : V, ⋃ v : V, D2 x w x₁ x₂ u v) ∪ (⋃ u : V, ⋃ v : V, D3a x w x₁ x₂ u v)) ∪
        (⋃ u : V, ⋃ v : V, D3b x w x₁ x₂ u v) := by
    rintro ω ⟨⟨h1, h2⟩, hw⟩
    rcases exists_two_level_branch (ω := ω) hw h1 h2 with ⟨u, v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, h⟩⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, h⟩⟩))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, h⟩⟩)
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
    · -- the `D2` family
      refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun u => ?_)
      refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun v => ?_)
      exact tree5_le π hπ _ _ _ _ _ (isUpper_connSet x u) (isUpper_connSet u w)
        (isUpper_connSet u v) (isUpper_connSet v x₁) (isUpper_connSet v x₂)
        (finiteWitness_connSet x u) (finiteWitness_connSet u w) (finiteWitness_connSet u v)
        (finiteWitness_connSet v x₁) (finiteWitness_connSet v x₂)
    · -- the `D3a` family
      refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun u => ?_)
      refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun v => ?_)
      exact tree5_le π hπ _ _ _ _ _ (isUpper_connSet x v) (isUpper_connSet v u)
        (isUpper_connSet u w) (isUpper_connSet u x₁) (isUpper_connSet v x₂)
        (finiteWitness_connSet x v) (finiteWitness_connSet v u) (finiteWitness_connSet u w)
        (finiteWitness_connSet u x₁) (finiteWitness_connSet v x₂)
  · -- the `D3b` family
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun u => ?_)
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun v => ?_)
    exact tree5_le π hπ _ _ _ _ _ (isUpper_connSet x u) (isUpper_connSet u v)
      (isUpper_connSet v w) (isUpper_connSet u x₁) (isUpper_connSet v x₂)
      (finiteWitness_connSet x u) (finiteWitness_connSet u v) (finiteWitness_connSet v w)
      (finiteWitness_connSet u x₁) (finiteWitness_connSet v x₂)

end PercLib.CriticalLRP.I417Example
