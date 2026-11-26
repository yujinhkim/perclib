/-
Independently reviewed and integrated from the partial artifact
`.ultramath/smwx6p0op/m3/HubEval`. Production integration revision:
`57e71d7ca447d7d83bfa761bb296fde27f6eb970`. This is a concrete one-shape
hub evaluation, not a general mixed-moment theorem.
-/
/-
The one-hub block of `t3` at `hubI`: the event-level cover and the BK measure bound.

Independently built for swarm `smwx6p0op`, member `m3`, direction HUB-EVALUATED-BLOCK.

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.16 (pp. 44--45).  The printed argument partitions the
`2p - 1` edges of the tree into the 3-stars of the distinguished hubs and the remaining
`2p - 1 - 3k` edges, applies BK to that partition, and then charges each hub block two units.

What is proved here for the shape `t3` (`p = 3`, `2p - 1 = 5` edges) and the hub set
`{hubI}` (`k = 1`, `3` star edges, `2` off-hub edges):

* `canonAtlasEvent_subset_hubSlots` -- a canonical atlas realization of the *whole* shape implies
  the four-slot family `hubSlots`: the two up/false star edges are merged into one joint pair at
  the hub, and the *three* remaining edges each keep their own witness.  No arm is dropped and no
  edge of the shape is charged twice; the merge uses only that distinct atlas edges have disjoint
  witnesses inside one realization;
* `edgeMeasure_canonAtlasEvent_le_hubBlock` -- the BK measure form: the atlas measure at `t3` is at
  most one joint factor at the hub times the three retained two-point factors.

The quantifiers are deliberately per-shape and per-position: nothing is summed here, no shape
family is quantified over, and no moment hypothesis is introduced.  The summations are in
`Summed.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Block.Defs
public import PercLib.CriticalLRP.BK.FiniteIndex.Canonical

/-!
# The cover and the BK bound of the `t3` one-hub block
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config connSet edgeMeasure)
open PercLib.CriticalLRP.Percolation (DisjFam bk_disjFam)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge srcPos dstPos childPos srcPos_inl dstPos_inl)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.HubEval

variable {V : Type*}

/-- Slot `some i` is the connection event of `armEdge i`, with any base point `c` (the source of a
`Sum.inl` atlas edge does not depend on it). -/
theorem armSlot_apply_base (y : Fin 3 → V) (φ : t3.IPos → V) (c : V) (i : Fin 3) :
    armSlot y φ i = connSet (srcPos t3 φ c (armEdge i)) (dstPos t3 φ y (armEdge i)) := by
  fin_cases i <;> rfl

/-- The hub's own two down arms and the root edge are exactly the three edges of its 3-star. -/
theorem hubStarAEdges_eq :
    PercLib.CriticalLRP.TreeExpansion.Real.hubStarAEdges t3 hubI =
      ({upEdge, hubFalseEdge, hubTrueEdge} : Finset (AEdge t3)) := by
  decide

/-- The two off-hub edges of the hub set `{hubI}` are the two down edges of `innerI`. -/
theorem offHubAEdges_eq :
    PercLib.CriticalLRP.TreeExpansion.Real.offHubAEdges t3 {hubI} =
      ({Sum.inl (innerI, false), Sum.inl (innerI, true)} : Finset (AEdge t3)) := by
  decide

/-- The hub is the root internal vertex of `t3`, so its up arm's own source is the root leaf. -/
theorem isRootIpos_hubI : HubUpArm.IsRootIpos t3 hubI := by
  change (PercLib.CriticalLRP.TreeExpansion.RTree.pathOf t3 hubI).1 = []
  rfl

theorem hubUpSrc_hubI [DecidableEq V] (φ : t3.IPos → V) (c : V) :
    HubUpArm.hubUpSrc t3 φ c hubI = c :=
  HubUpArm.hubUpSrc_eq_root t3 φ c hubI isRootIpos_hubI

theorem srcPos_upEdge (φ : t3.IPos → V) (c : V) : srcPos t3 φ c upEdge = c := rfl

theorem dstPos_upEdge (φ : t3.IPos → V) (y : Fin 3 → V) : dstPos t3 φ y upEdge = φ hubI := rfl

theorem srcPos_hubFalseEdge (φ : t3.IPos → V) (c : V) :
    srcPos t3 φ c hubFalseEdge = φ hubI := rfl

theorem dstPos_hubFalseEdge (φ : t3.IPos → V) (y : Fin 3 → V) :
    dstPos t3 φ y hubFalseEdge = φ innerI := rfl

/-! ### The raw arms are distinct atlas edges, and none of them is one of the hub pair's -/

theorem armEdge_ne_upEdge (i : Fin 3) : armEdge i ≠ upEdge := by
  fin_cases i <;> decide

theorem armEdge_ne_hubFalseEdge (i : Fin 3) : armEdge i ≠ hubFalseEdge := by
  fin_cases i <;> decide

theorem armEdge_injective : Function.Injective armEdge := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-! ### The cover -/

/-- **The whole canonical atlas of `t3` implies the one-hub block, all four slots.**

The hub pair is witnessed by the *union* of the root edge's witness (the up arm) and the `false`
down arm's witness; the three other slots keep their own witnesses.  All witnesses are the
realization's own, hence pairwise disjoint, and no edge of the shape is dropped.  No position
assignment is assumed injective, so every coincidence of `c`, `φ hubI`, `φ innerI` and the three
labelled leaves is allowed. -/
theorem canonAtlasEvent_subset_hubSlots [DecidableEq V] [Countable V] (y : Fin 3 → V) (c : V)
    (φ : t3.IPos → V) :
    CanonAtlas.CanonAtlasEvent y c t3 φ ⊆ DisjFam (hubSlots y c φ) := by
  rintro ω ⟨W, hsub, hdisj, hconn⟩
  refine ⟨fun o => match o with
      | none => W upEdge ∪ W hubFalseEdge
      | some i => W (armEdge i), ?_, ?_, ?_⟩
  · rintro (_ | i)
    · simp only [Finset.coe_union]
      exact Set.union_subset (hsub _) (hsub _)
    · exact hsub _
  · rintro (_ | i)
    · constructor
      · have h1 : (W upEdge : Set (Sym2 V)) ∈
            connSet (HubUpArm.hubUpSrc t3 φ c hubI) (φ hubI) := by
          simpa only [srcPos_upEdge, dstPos_upEdge, hubUpSrc_hubI, connSet, Set.mem_ofPred_eq]
            using hconn upEdge
        refine PercLib.CriticalLRP.isUpper_connSet _ _
          (Finset.coe_subset.mpr Finset.subset_union_left) h1
      · have h1 : (W hubFalseEdge : Set (Sym2 V)) ∈ connSet (φ innerI) (φ hubI) := by
          rw [HubJointEval.connSet_comm]
          simpa only [srcPos_hubFalseEdge, dstPos_hubFalseEdge, childPos_hub_false, connSet,
            Set.mem_ofPred_eq] using hconn hubFalseEdge
        refine PercLib.CriticalLRP.isUpper_connSet _ _
          (Finset.coe_subset.mpr Finset.subset_union_right) h1
    · change (W (armEdge i) : Set (Sym2 V)) ∈ armSlot y φ i
      rw [armSlot_apply_base y φ c i]
      exact hconn (armEdge i)
  · rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact Finset.disjoint_union_left.mpr
        ⟨hdisj _ _ (fun h => armEdge_ne_upEdge j h.symm),
          hdisj _ _ (fun h => armEdge_ne_hubFalseEdge j h.symm)⟩
    · exact (Finset.disjoint_union_left.mpr
        ⟨hdisj _ _ (fun h => armEdge_ne_upEdge i h.symm),
          hdisj _ _ (fun h => armEdge_ne_hubFalseEdge i h.symm)⟩).symm
    · exact hdisj _ _ (fun h => hij (congrArg some (armEdge_injective h)))

/-! ### The BK measure bound -/

theorem isUpperSet_hubSlots [Countable V] (y : Fin 3 → V) (c : V) (φ : t3.IPos → V)
    (o : Option (Fin 3)) : IsUpperSet (hubSlots y c φ o) := by
  rcases o with _ | i
  · exact HubJointEval.isUpperSet_hubPairJoint _ _ _
  · change IsUpperSet (armSlot y φ i)
    rw [armSlot_apply_base y φ c i]
    exact PercLib.CriticalLRP.isUpper_connSet _ _

theorem finiteWitness_hubSlots [Countable V] (y : Fin 3 → V) (c : V) (φ : t3.IPos → V)
    (o : Option (Fin 3)) : PercLib.CriticalLRP.Percolation.FiniteWitness (hubSlots y c φ o) := by
  rcases o with _ | i
  · exact HubJointEval.finiteWitness_hubPairJoint _ _ _
  · change PercLib.CriticalLRP.Percolation.FiniteWitness (armSlot y φ i)
    rw [armSlot_apply_base y φ c i]
    exact PercLib.CriticalLRP.finiteWitness_connSet _ _

/-- **The BK measure form**: the canonical atlas measure of `t3` at any positions is at most the
block value, i.e. at most the BK product of the merged hub pair and the three retained raw arms.

This is the `p = 3`, `k = 1` block of the source's partition *with all five atlas edges of the
shape present*: three inside the hub block, two off-hub. -/
theorem edgeMeasure_canonAtlasEvent_le_hubBlock [DecidableEq V] [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (y : Fin 3 → V) (c : V)
    (φ : t3.IPos → V) :
    edgeMeasure π (CanonAtlas.CanonAtlasEvent y c t3 φ) ≤ hubBlockValue π y c φ :=
  (measure_mono (canonAtlasEvent_subset_hubSlots y c φ)).trans
    (bk_disjFam π hπ (isUpperSet_hubSlots y c φ) (finiteWitness_hubSlots y c φ))

/-- **The block evaluated**: one joint factor at the hub -- the joint pair with the root leaf `c`
as its first point and the `false` child end as its second -- times the three retained raw
two-point factors, one for the hub's `true` down arm and one for each of the two off-hub edges.

That is `4 = 3 + 1` factors for the `5` atlas edges of the shape, which is exactly the source's
partition at `p = 3`, `k = 1`: the merged hub pair stands for the `3` star edges, the remaining
`2 = 2p - 1 - 3k` edges are single two-point factors.  The first point of the joint pair is the
root leaf -- `hubUpSrc t3 φ c hubI = c` -- never the hub, and the up arm is never dropped. -/
theorem hubBlockValue_eq [DecidableEq V] [Countable V] (π : Sym2 V → unitInterval) (y : Fin 3 → V)
    (c : V) (φ : t3.IPos → V) :
    hubBlockValue π y c φ =
      jointP π c (φ innerI) (φ hubI) *
        (PercLib.Percolation.Bond.tau π (φ hubI) (y 2) *
          (PercLib.Percolation.Bond.tau π (φ innerI) (y 0) *
            PercLib.Percolation.Bond.tau π (φ innerI) (y 1))) := by
  have hfun : (fun o : Option (Fin 3) => edgeMeasure π (hubSlots y c φ o)) =
      (fun o => edgeMeasure π (match o with
        | none => HubJointEval.hubPairJoint c (φ innerI) (φ hubI)
        | some i => armSlot y φ i)) := by
    funext o
    rcases o with _ | i
    · rw [hubSlots, hubUpSrc_hubI, childPos_hub_false]
    · rw [hubSlots]
  unfold hubBlockValue
  rw [hfun, Fintype.prod_option, Fin.prod_univ_three, mul_assoc]
  simp only [armSlot_zero, armSlot_one, armSlot_two, HubJointEval.edgeMeasure_connSet_eq_tau]
  rw [HubJointEval.jointP_eq_edgeMeasure_hubPairJoint]

end PercLib.CriticalLRP.TreeExpansion.HubEval
