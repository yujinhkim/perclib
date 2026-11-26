/- Independently rebuilt and integrated from accepted UltraMath solution `smwwzy3xm` m1.
Production integration revision: `ca165b334f2970daf35034762d79fa32b83639d2`.

UltraMath swarm `smwwzy3xm`, member `m1`.  Lean 4.35.0.
Production read-only reference
`/workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/`
`critical-lrp-orchestration`, committed revision
`4478d0f5a412be93a92b607d6e30a20cbd89bdb6` plus the focused-built uncommitted
`Correlation/I417/MarkedJoint/Transversal/{Transversal,Main,Depth}.lean` sources.
Nothing outside `.ultramath/smwwzy3xm/m1/` is written; there is no commit and no package build.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth

/-!
# Per-depth marked shape coefficients: the definitions

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17, the marked (base) side.  The per-depth coefficient of the
marked diagram expansion is counted twice in production, in two different label conventions:

* `PercLib.CriticalLRP.I417Marked.markedCount p ℓ` counts the **plane** fully labelled trees over
  `I417Marked.Label p = Fin p ⊕ PUnit` (marking label `markLabel p = Sum.inr ⟨⟩`) whose marked
  leaf has depth `ℓ`;
* `PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ` counts **one plane
  representative per child-swap orbit** of the fully labelled `Fin (p+1)`-labelled shapes
  (marking label `Fin.last p`) whose marked leaf has depth `ℓ`.

The only proved relation between the two families up to now is the *total* one
(`sum_markedCount_eq_plane_count`, `sum_nonplaneMarkedCount`), obtained by summing over all
depths.  The purpose of this development is the per-depth identity

`markedCount p ℓ = 2 ^ p * nonplaneMarkedCount p ℓ`  for every `p` and `ℓ`,

which needs the marked leaf position and its depth to be transported along the relabelling and
along child swaps — not merely the internal positions (`iposMapLabelEquiv`) or the total
cardinality.

## The objects defined here

* `leafPosMapLabel f t : RTree.LeafPos t ≃ RTree.LeafPos (t.mapLabel f)` -- the leaf-position
  analogue of production's internal-position equivalence `iposMapLabelEquiv`.  The two position
  types are different: `RTree.IPos` is the type of internal vertices and `RTree.LeafPos` the type
  of leaves, and only the latter carries the marking label.  Recursing on the tree, a leaf goes
  to a leaf and a node splits into the two children; there is no `PUnit` root summand.

* `markedFilterLabel p ℓ`, `markedFilterFin p ℓ` -- the depth-`ℓ` marked subfamilies of the
  `LTon`-families `LTon (Label p) univ` and `LTon (Fin (p+1)) univ`, filtered on the depth of
  the leaf position carrying the marking label.

* `planeMarkedFiber p ℓ` -- the same depth filter over the fully labelled plane family
  `RTree.LT (Fin (p+1))`, the family on which the child-swap orbits live.

No probability statement, no graph law and no finite-set division occurs in this file; all three
families are finite `Finset`s built from `Finset.univ`, and every filter predicate is decidable.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedPerDepth

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Marked (Label markLabel markPos)

universe u

/-! ### Leaf positions along a leaf relabelling -/

/-- **Leaf positions are transported along a leaf relabelling.**  The tree shape is unchanged by
`RTree.mapLabel`, so the leaves of `t.mapLabel f` and of `t` are in canonical bijection: a leaf of
a single-leaf tree is its unique position, and at a node the two children are handled
independently.  This is the `LeafPos` analogue of `I417MarkedRelabel.iposMapLabelEquiv`, which
transports *internal* positions and therefore cannot be used for the marked leaf. -/
noncomputable def leafPosMapLabel {α : Type u} {β : Type u} (f : α → β) :
    (t : RTree α) → (RTree.LeafPos t ≃ RTree.LeafPos (t.mapLabel f))
  | RTree.leaf _ => Equiv.refl PUnit
  | RTree.node l r => (leafPosMapLabel f l).sumCongr (leafPosMapLabel f r)

/-- The equivalence acts as the identity on the unique leaf of a leaf. -/
theorem leafPosMapLabel_leaf {α : Type u} {β : Type u} (f : α → β) (a : α) :
    leafPosMapLabel f (RTree.leaf a) = Equiv.refl PUnit := rfl

/-- At a node the equivalence is the sum of the equivalences of the two children. -/
theorem leafPosMapLabel_node {α : Type u} {β : Type u} (f : α → β) (l r : RTree α) :
    leafPosMapLabel f (RTree.node l r)
      = (leafPosMapLabel f l).sumCongr (leafPosMapLabel f r) := rfl

/-! ### `LTon` and `RTree.LT`: the same fully labelled trees -/

/-- **The `LTon` and `RTree.LT` presentations of the fully labelled `Fin (p+1)` family agree.**
`LTon α Finset.univ` records injectivity plus the leaf set `univ`, `RTree.LT α` records
injectivity plus the leaf *count* `Fintype.card α`; on a finite label type these are the same
predicate, and the underlying tree is unchanged in both directions. -/
noncomputable def ltOnFinEquivLT (p : ℕ) :
    LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))) ≃ RTree.LT (Fin (p + 1)) where
  toFun t := ⟨t.1, t.2.1, by
    rw [← List.toFinset_card_of_nodup t.2.1, t.2.2, Finset.card_univ]⟩
  invFun t := ⟨t.1, t.2.1, by
    refine Finset.eq_univ_of_card _ ?_
    rw [List.toFinset_card_of_nodup t.2.1, t.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The depth-filtered marked families -/

/-- The **depth-`ℓ` marked subfamily of the `Fin p ⊕ PUnit` labelling**: the fully labelled
trees on all of `Fin p ⊕ PUnit` whose leaf carrying the marking label `markLabel p` has depth
`ℓ`.  This is the index family of `I417Marked.markedCount p ℓ` before the image under
`A ↦ ⟨A.1, markPos (markLabel p) A.1⟩` is taken. -/
noncomputable def markedFilterLabel (p ℓ : ℕ) :
    Finset (LTon (Label p) (Finset.univ : Finset (Label p))) :=
  Finset.univ.filter (fun t => RTree.depth t.1 (markPos (markLabel p) t.1) = ℓ)

/-- The **depth-`ℓ` marked subfamily of the `Fin (p+1)` labelling**: the fully labelled trees on
all of `Fin (p+1)` whose leaf carrying the marking label `Fin.last p` has depth `ℓ`.  This is the
family on which `finLabelEquiv p` transports `markedFilterLabel p ℓ`. -/
noncomputable def markedFilterFin (p ℓ : ℕ) :
    Finset (LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1)))) :=
  Finset.univ.filter (fun t => RTree.depth t.1 (markPos (Fin.last p) t.1) = ℓ)

/-- The **depth-`ℓ` marked subfamily of the fully labelled plane family**, with the marking label
`Fin.last p`.  Its child-swap orbits have exactly `2 ^ p` elements and the marked depth is
constant on each orbit, so this is the family whose orbit decomposition gives the non-plane
coefficient `I417MarkedTransversal.nonplaneMarkedCount p ℓ`. -/
noncomputable def planeMarkedFiber (p ℓ : ℕ) : Finset (RTree.LT (Fin (p + 1))) :=
  Finset.univ.filter (fun t => RTree.depth t.val (markPos (Fin.last p) t.val) = ℓ)

end PercLib.CriticalLRP.I417MarkedPerDepth
