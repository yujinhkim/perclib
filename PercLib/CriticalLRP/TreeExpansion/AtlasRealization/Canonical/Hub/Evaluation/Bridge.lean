/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

The canonical hub evaluation bridge: from the production joint hub event (three arms of a
3-star, one configuration, pairwise edge-disjoint ambient witnesses) to the physical
three-point function at the hub, and the separate BK product.

Source: Lemma I.4.16 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, pp. 43--45; the `p = 3`, `k = 1` case is the displayed
computation on p. 44.

## What is proved

1. `disjFam_subset_of_isUpperSet` -- a joint (disjoint-occurrence) event implies each of its
   slots, provided the slot event is increasing.  This is the *only* structural fact needed to
   compare a disjoint occurrence with an intersection event, and it is exactly where the
   disjoint-witness requirement is dropped.
2. `hubArmJoint_subset_pair` and `edgeMeasure_hubArmJoint_le_jointP` -- the joint three-arm
   value at the physical hub `c` is at most the three-point function `jointP π (far i) (far j) c`
   at the same hub, for any two arms `i ≠ j`.  This is the source's "three-point function"
   slot, obtained by dropping disjointness, *not* by a product of two-point factors.
3. `edgeMeasure_hubArmJoint_le_prod` -- the BK product bound `∏ᵢ τ (far i) c`, which is a
   strictly different object: it is the product of three two-point functions, and it is what
   the ordinary tree-graph inequality uses.  Both bounds hold; neither is an identity.
4. `hubStarJoint_subset_downPair`, `edgeMeasure_hubStarJoint_le_jointP` -- the same evaluation
   for the *production* canonical hub event `CanonAtlas.hubStarJoint`, at the two down arms of
   the 3-star, with the physical hub identified with `φ v`.  Slot bookkeeping: the 3-star of
   `v` consists of the two down edges `Sum.inl (v, false)`, `Sum.inl (v, true)` (whose `srcPos`
   is `φ v`) and the up edge `RTree.upEdge` (whose `dstPos` is `φ v`); the pair used here is
   the two down arms, and the up (parent) arm is the slot that the source contracts to carry
   the origin pair.  See `HubJointEval/SourceDiag.lean` for that slot assignment.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Defs

/-!
# Hub evaluation bridge
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)
open PercLib.CriticalLRP.Percolation (DisjFam bk_disjFam)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge srcPos dstPos hubStarAEdges hubStarAEdges_eq srcPos_inl)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubJointEval

variable {V : Type*}

/-! ### Dropping disjointness: a joint event implies each of its slots -/

/-- **A disjoint occurrence implies each of its slots.**  If every slot event is increasing, then
a configuration with pairwise disjoint witnesses for all slots satisfies each slot separately.
This is where the disjoint-witness requirement of `DisjFam` is dropped, and it is the reason a
joint three-arm value is bounded by an *intersection* (a three-point function) rather than by a
product. -/
theorem disjFam_subset_of_isUpperSet {E ι : Type*} {A : ι → Set (Set E)}
    (hA : ∀ i, IsUpperSet (A i)) (i : ι) :
    DisjFam A ⊆ A i := by
  rintro ω ⟨W, hsub, hmem, -⟩
  exact hA i (hsub i) (hmem i)

/-- The production connection event and the bond connection event are the same set. -/
theorem connSet_eq_conn [Countable V] (x y : V) :
    connSet x y = PercLib.Percolation.Bond.conn x y := rfl

/-- The connection event is symmetric in its two endpoints. -/
theorem connSet_comm [Countable V] (x y : V) : connSet x y = connSet y x := by
  ext ω
  exact ⟨PercLib.CriticalLRP.connects_symm, PercLib.CriticalLRP.connects_symm⟩

/-- `jointP` is the measure of the hub pair event. -/
theorem jointP_eq_edgeMeasure_hubPairJoint [Countable V] (π : Sym2 V → unitInterval)
    (a b c : V) : jointP π a b c = edgeMeasure π (hubPairJoint a b c) := by
  rw [jointP, hubPairJoint, connSet_eq_conn, connSet_eq_conn]

/-- The three-point function is at most the two-point function of either of its points: the
intersection is contained in each single connection event.  So `jointP` sits between the joint
three-arm value and `tau`, and it is not a product of two two-point factors. -/
theorem jointP_le_tau_right [Countable V] (π : Sym2 V → unitInterval) (a b c : V) :
    jointP π a b c ≤ PercLib.Percolation.Bond.tau π b c := by
  unfold jointP PercLib.Percolation.Bond.tau
  exact measure_mono (Set.inter_subset_right)

/-- The three-point function is at most the two-point function of its first point. -/
theorem jointP_le_tau_left [Countable V] (π : Sym2 V → unitInterval) (a b c : V) :
    jointP π a b c ≤ PercLib.Percolation.Bond.tau π a c := by
  unfold jointP PercLib.Percolation.Bond.tau
  exact measure_mono (Set.inter_subset_left)

/-! ### The three-arm hub value is bounded by the three-point function at the hub -/

/-- **Collapsing three arms to a joint pair.**  The joint three-arm value at the hub `c` implies
the three-point function `hubPairJoint (far i) (far j) c` for any two distinct arms: both arms are
connected to the hub in the same configuration.  Nothing is assumed about the third arm and no
independent copy is made; in particular repeated physical vertices are harmless. -/
theorem hubArmJoint_subset_pair [Countable V] (c : V) (far : Fin 3 → V) (i j : Fin 3) :
    hubArmJoint c far ⊆ hubPairJoint (far i) (far j) c := by
  rintro ω ⟨W, hsub, hmem, -⟩
  exact ⟨PercLib.CriticalLRP.isUpper_connSet (far i) c (hsub i) (hmem i),
    PercLib.CriticalLRP.isUpper_connSet (far j) c (hsub j) (hmem j)⟩

/-- **The hub evaluation: three arms cost at most the three-point function at the hub.** -/
theorem edgeMeasure_hubArmJoint_le_jointP [Countable V] (π : Sym2 V → unitInterval)
    (c : V) (far : Fin 3 → V) (i j : Fin 3) :
    edgeMeasure π (hubArmJoint c far) ≤ jointP π (far i) (far j) c := by
  rw [jointP_eq_edgeMeasure_hubPairJoint]
  exact measure_mono (hubArmJoint_subset_pair c far i j)

/-- **The three-fold BK product at the hub.**  The same joint three-arm value is at most the
product of the three two-point factors `τ (far i) c`.

This is a *different* upper bound from `edgeMeasure_hubArmJoint_le_jointP`: it is the ordinary
tree-graph product, and it is not the three-point function of the source.  Neither of the two
bounds implies the other in general. -/
theorem edgeMeasure_hubArmJoint_le_prod [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (c : V) (far : Fin 3 → V) :
    edgeMeasure π (hubArmJoint c far) ≤ ∏ i, PercLib.Percolation.Bond.tau π (far i) c := by
  have h := bk_disjFam π hπ (A := fun i : Fin 3 => connSet (far i) c)
    (fun i => PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun i => PercLib.CriticalLRP.finiteWitness_connSet _ _)
  refine h.trans (le_of_eq ?_)
  exact Finset.prod_congr rfl fun i _ => by
    rw [PercLib.Percolation.Bond.tau, connSet_eq_conn]

/-! ### The same evaluation for the production hub layer -/

section Production

variable {α : Type*} [DecidableEq α]

/-- The two down edges of the 3-star of a hub belong to the star. -/
theorem downEdge_mem_hubStarAEdges (t : RTree α) (v : t.IPos) (b : Bool) :
    (Sum.inl (v, b) : AEdge t) ∈ hubStarAEdges t v := by
  rw [hubStarAEdges_eq]
  cases b <;> simp

/-- **The production canonical joint hub event is contained in the three-point function at the
physical hub, with the two down arms as the two points.**

Slot bookkeeping.  The 3-star of `v` has three edges: the two *down* edges `Sum.inl (v, false)`
and `Sum.inl (v, true)`, whose upper end `srcPos` is `φ v` and whose lower ends are the two child
positions, and the *up* (parent) edge `RTree.upEdge`, whose lower end `dstPos` is `φ v`.  The
pair taken here is the two down arms, so the joint three-arm value at `φ v` yields
`jointP π (childFalse) (childTrue) (φ v)` with the hub as the *centre* of the joint pair.

This is the legitimate `hubStarJoint → jointP` comparison.  It is not the source's own slot
choice: at `p = 3`, `k = 1` the source contracts the *parent* arm and pins the origin there, so
that the pair is `(origin, non-hub internal point)` at the hub `w`; that object is
`hubDiagJoint o x y z w` (`HubJointEval/SourceDiag.lean`), and its slot is the pair slot, not
one of the two leaf arms used here.  The two are different canonical joint objects and are not
identified. -/
theorem hubStarJoint_subset_downPair [Countable V] (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    CanonAtlas.hubStarJoint y c t φ v ⊆
      hubPairJoint (dstPos t φ y (Sum.inl (v, false)))
        (dstPos t φ y (Sum.inl (v, true))) (φ v) := by
  classical
  rintro ω ⟨W, hsub, hmem, -⟩
  have hL := hmem ⟨Sum.inl (v, false), downEdge_mem_hubStarAEdges t v false⟩
  have hR := hmem ⟨Sum.inl (v, true), downEdge_mem_hubStarAEdges t v true⟩
  have hL' : (W ⟨Sum.inl (v, false), downEdge_mem_hubStarAEdges t v false⟩ : Set (Sym2 V))
      ∈ connSet (dstPos t φ y (Sum.inl (v, false))) (φ v) := by
    rw [connSet_comm]
    simpa [CanonAtlas.atlasConnEvent, srcPos_inl] using hL
  have hR' : (W ⟨Sum.inl (v, true), downEdge_mem_hubStarAEdges t v true⟩ : Set (Sym2 V))
      ∈ connSet (dstPos t φ y (Sum.inl (v, true))) (φ v) := by
    rw [connSet_comm]
    simpa [CanonAtlas.atlasConnEvent, srcPos_inl] using hR
  exact ⟨PercLib.CriticalLRP.isUpper_connSet _ _ (hsub _) hL',
    PercLib.CriticalLRP.isUpper_connSet _ _ (hsub _) hR'⟩

/-- **The hub evaluation in the production canonical layer**: the measure of the joint hub event
at the 3-star of `v` is at most the three-point function at the physical hub `φ v` whose two
points are the two down (child) ends. -/
theorem edgeMeasure_hubStarJoint_le_jointP [Countable V] (π : Sym2 V → unitInterval)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    edgeMeasure π (CanonAtlas.hubStarJoint y c t φ v) ≤
      jointP π (dstPos t φ y (Sum.inl (v, false)))
        (dstPos t φ y (Sum.inl (v, true))) (φ v) := by
  rw [jointP_eq_edgeMeasure_hubPairJoint]
  exact measure_mono (hubStarJoint_subset_downPair y c t φ v)

/-- **The single two-point bound.**  Consequently the joint hub value at the 3-star is at most
one two-point function `τ (childFalse) (φ v)`: the three-point function is contained in a single
connection event.  Note that this is *weaker* than the BK product
`edgeMeasure_hubArmJoint_le_prod`, and that neither of `jointP` and the BK product is an identity
for the joint hub value.

Only the two down arms are transported here (`srcPos` is definitionally `φ v` on them); the up
arm's upper end is the parent position (or the root leaf position `c`), which is why the
transport of the full three-arm family needs the parity/root case split of the hub layer and is
documented as a remaining gap rather than asserted. -/
theorem edgeMeasure_hubStarJoint_le_tau
    [Countable V] (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    edgeMeasure π (CanonAtlas.hubStarJoint y c t φ v) ≤
      PercLib.Percolation.Bond.tau π (dstPos t φ y (Sum.inl (v, false))) (φ v) :=
  (edgeMeasure_hubStarJoint_le_jointP π y c t φ v).trans
    (jointP_le_tau_left π _ _ _)

end Production

end HubJointEval
