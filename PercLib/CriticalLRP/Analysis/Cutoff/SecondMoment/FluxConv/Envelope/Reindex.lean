/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvgnqju`, member `m1`, direction (A).

# Edge-to-vertex reindexing of the unexcluded ghost weight

`Main.lean` proves the pointwise envelope domination.  The present file proves only the
`2`-to-`1` edge/ordered-pair reindexing.  `Compare.lean`, `Correction.lean` and `Summable.lean`
then use it to bound and sum the coefficient-weighted envelope means and to feed the landed
insertion theorem `FluxConv.Insertion.tendsto_windowFlux_of_envelope`.

The summability is the paper's `p = 2` window-mass estimate.  On the differentiating support the
envelope is the unexcluded ghost, and

  `∑_e E[unexclEdgeWeight e] = E[∑_b ∑_c unexclPairWeight b c]`

by the (reproved, for this weight) edge-to-vertex identity.  The unexcluded double sum is the
paper's excluded double sum plus the `b ↔ c` part:

  `∑_{b,c} 1(0↔b) 1(|c-b|≤r) (2|K_b||K_c| + |K_c|²)`
    `= p2PaperSum + 3 |K_0|² ∑_b 1(0↔b) #(K_b ∩ B_r(b))`
    `≤ p2PaperSum + 3 |K_0|⁴`,

because on `0 ↔ b`, `b ↔ c` one has `|K_b| = |K_c| = |K_0|`, and `#(K_b ∩ B_r(b)) ≤ |K_b|`.  Hence

  `∑_e E[unexclEdgeWeight e] ≤ E[p2PaperSum] + 3 E[|K_0|⁴] = p2RHS r + 3 cutMoment 4 r`,

which is finite under a finite fourth cutoff moment (`PivotFlux.lintegral_p2PaperSum_eq_p2RHS`).
The `cutEdgeClosedWeight ≤ 1` factor of the source's coefficient needs the single-coordinate
closure probability only through the constant `1`, so no product structure is used.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Insertion
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Main

/-!
# Summability of the envelope and the fixed-radius limit
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The edge-to-vertex identity for the unexcluded weight -/

/-- The finite weighted `2`-to-`1` double count for the unexcluded pair weight. -/
theorem sum_sum_mul_unexclPairWeight (r : ℝ) (ω : Config M.V) (o : M.V)
    (h : Sym2 M.V → ℝ≥0∞) (B : Finset M.V) :
    (∑ b ∈ B, ∑ c ∈ B, h s(b, c) * unexclPairWeight M r ω o b c)
      = ∑ e ∈ B.sym2, h e * unexclEdgeWeight M r ω o e := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert a B' ha ih =>
    have hdisj : Disjoint ((insert a B').image (fun b => s(a, b))) B'.sym2 := by
      refine Finset.disjoint_left.mpr ?_
      intro e he hf
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp he
      exact ha ((Finset.mem_sym2_iff.mp hf) a (Sym2.mem_mk_left a b))
    have hinj : Set.InjOn (fun b => s(a, b)) ↑(insert a B') := by
      intro b _ b' _ hb
      rw [Sym2.eq_iff] at hb
      rcases hb with ⟨-, h1⟩ | ⟨h1, h2⟩
      · exact h1
      · exact h2.trans h1
    have hswap : ∀ b : M.V, h s(a, b) = h s(b, a) := fun b => by rw [Sym2.eq_swap]
    have hL : (∑ b ∈ insert a B', ∑ c ∈ insert a B',
          h s(b, c) * unexclPairWeight M r ω o b c)
        = (∑ c ∈ B', h s(a, c) * unexclPairWeight M r ω o a c)
          + (∑ b ∈ B', h s(b, a) * unexclPairWeight M r ω o b a)
          + (∑ b ∈ B', ∑ c ∈ B', h s(b, c) * unexclPairWeight M r ω o b c) := by
      rw [Finset.sum_insert ha]
      conv_lhs => rw [Finset.sum_insert ha]
      rw [Finset.sum_congr rfl (fun b _ => Finset.sum_insert ha)]
      rw [Finset.sum_add_distrib, unexclPairWeight_self, mul_zero, zero_add]
      ac_rfl
    have hR : (∑ e ∈ (insert a B').sym2, h e * unexclEdgeWeight M r ω o e)
        = (∑ c ∈ B', h s(a, c) * unexclPairWeight M r ω o a c)
          + (∑ b ∈ B', h s(b, a) * unexclPairWeight M r ω o b a)
          + (∑ b ∈ B', ∑ c ∈ B', h s(b, c) * unexclPairWeight M r ω o b c) := by
      rw [Finset.sym2_insert, Finset.sum_union hdisj, ← ih, Finset.sum_image hinj,
        Finset.sum_insert ha]
      rw [unexclEdgeWeight_diag, mul_zero, zero_add]
      simp only [unexclEdgeWeight_mk]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ B') =>
        mul_add (h s(a, b)) (unexclPairWeight M r ω o a b) (unexclPairWeight M r ω o b a))]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ B') =>
        congrArg (fun z => z * unexclPairWeight M r ω o b a) (hswap b))]
    rw [hL, hR]

/-- Cofinality of the edge windows for the unexcluded weight. -/
theorem iSup_sum_sym2_unexcl_eq (r : ℝ) (ω : Config M.V) (o : M.V) :
    (⨆ B : Finset M.V, ∑ e ∈ B.sym2, unexclEdgeWeight M r ω o e)
      = ⨆ t : Finset (M.V × M.V), ∑ p ∈ t, unexclPairWeight M r ω o p.1 p.2 := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le fun B => ?_
    have h1 : (∑ e ∈ B.sym2, unexclEdgeWeight M r ω o e)
        = ∑ p ∈ B ×ˢ B, unexclPairWeight M r ω o p.1 p.2 := by
      rw [Finset.sum_product]
      simpa using (sum_sum_mul_unexclPairWeight M r ω o (fun _ => (1 : ℝ≥0∞)) B).symm
    rw [h1]
    exact le_iSup (fun t : Finset (M.V × M.V) => ∑ p ∈ t,
      unexclPairWeight M r ω o p.1 p.2) (B ×ˢ B)
  · refine iSup_le fun t => ?_
    set B : Finset M.V := t.image Prod.fst ∪ t.image Prod.snd with hB
    have hsub : t ⊆ B ×ˢ B := by
      intro p hp
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image_of_mem Prod.fst hp)
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem Prod.snd hp)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)) ?_
    have h1 : (∑ p ∈ B ×ˢ B, unexclPairWeight M r ω o p.1 p.2)
        = ∑ e ∈ B.sym2, unexclEdgeWeight M r ω o e := by
      rw [Finset.sum_product]
      simpa using sum_sum_mul_unexclPairWeight M r ω o (fun _ => (1 : ℝ≥0∞)) B
    rw [h1]
    exact le_iSup (fun B : Finset M.V => ∑ e ∈ B.sym2, unexclEdgeWeight M r ω o e) B

/-- **The edge-to-vertex identity for the unexcluded weight.** -/
theorem tsum_unexclEdgeWeight_eq (r : ℝ) (ω : Config M.V) (o : M.V) :
    ∑' e : Sym2 M.V, unexclEdgeWeight M r ω o e
      = ∑' b : M.V, ∑' c : M.V, unexclPairWeight M r ω o b c := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum' (fun B : Finset M.V => B.sym2)
      (fun t => exists_finset_sym2_subset t),
    ← ENNReal.tsum_prod, ENNReal.tsum_eq_iSup_sum]
  exact iSup_sum_sym2_unexcl_eq M r ω o

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms sum_sum_mul_unexclPairWeight
#print axioms iSup_sum_sym2_unexcl_eq
#print axioms tsum_unexclEdgeWeight_eq

end PercLib.CriticalLRP.Orchestration.SourceModelData
