/-
The parent-aware inclusion from the joint hub event to a joint three-point function.

Prepared from `.ultramath/smwx4z71g/m1/HubUpArm/ParentIncl.lean` at production revision
`5e579c30ee2c5caa2d151372f1929efd8ed587fb`.  The independently rebuilt coordinator
integration updates production imports and repairs the merged-witness BK proof without changing
its statement.  Definitions are in `Hub/UpArm/Defs.lean`; endpoint results are in
`Hub/UpArm/UpArm.lean`.

`CanonAtlas.hubStarJoint y c t φ v` is the disjoint occurrence of the three arms of the 3-star of
`v`.  Its arms have, at one end, the hub position `φ v`, and at the other end the three *physical*
points `hubFar t φ y c v`:

* `hubFar … 0 = childPos t φ y v false`, `hubFar … 1 = childPos t φ y v true` --
  the two child ends (an internal child's position `φ u`, or the terminal `y a` of a leaf child);
* `hubFar … 2 = hubUpSrc t φ c v` -- the up arm's own end: the root leaf `c` at
  the root hub, and `φ (parentIPos t v h)` for a non-root hub (`UpArm.lean`,
  `srcPos_hubUpEdge`).

Proved here:

* `hubStarJoint_subset_threePoint` -- the joint hub event implies the parent-aware joint
  three-point function `hubThreePoint`: `φ v` is connected to *all three* of those ends in one
  configuration.  This is the intersection form (disjointness dropped), which is the only valid
  direction: `HubJointEval/Obstruction.lean` shows the converse fails;
* `hubStarJoint_subset_upPair` -- the sharper slot form used by the source: the joint hub event
  implies the three-point function `P(up-arm end ↔ φ v, child end ↔ φ v)`, i.e. the
  joint pair at the hub whose two points are the **up arm's own end** and a child end.
  This is the parent-aware
  comparison: the first pair point is `c` (root) or `φ (parent v)`, never the hub itself;
* `edgeMeasure_hubStarJoint_le_jointP` -- the measure form: the joint hub value is at most
  `jointP π (hubUpSrc) (childPos v b) (φ v)`;
* `edgeMeasure_hubStarJoint_le_jointP_mul_tau` -- the source-shaped block bound: merging the up
  arm and one child arm into a single witness set and applying the two-fold BK inequality gives
  the joint hub value at most `jointP π (hubUpSrc) (childPos v false) (φ v)` times one two-point
  factor `τ π (φ v) (childPos v true)`.  One factor is a three-point (joint)
  quantity, the other a raw two-point quantity -- not three two-point factors;
* `canonAtlasEvent_subset_upPair`, `canonAtlasEvent_subset_threePoint` -- the same for a full
  canonical atlas realization, through production's
  `CanonAtlas.canonAtlasEvent_subset_hubStarJoint`.

Nothing here is a moment statement: the results are per-shape, per-hub slot statements, and no
claim about `p = 3`, `k = 1` or about any sum over shapes and positions is made.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.UpArm.UpArm
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.SourceDiag

/-!
# The parent-aware inclusion `hubStarJoint ⊆ joint three-point function at φ v`
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)
open PercLib.CriticalLRP.Percolation (DisjFam bk_disjFam)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge atlasEdgeEquiv srcPos dstPos childPos hubStarAEdges hubStarAEdges_eq srcPos_inl dstPos_inl)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubUpArm

variable {V : Type*} [DecidableEq V] [Countable V]
variable {α : Type*} [DecidableEq α]

/-! ### The three arms inside the joint hub event -/

/-- **Each arm of the joint hub event connects its own two ends.**  This is the only structural
step: a witness of the disjoint occurrence, being a subset of the configuration, satisfies the
connection event of its arm in the whole configuration. -/
theorem hubStarJoint_arm_connects {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {v : t.IPos} {ω : Config V} (hω : ω ∈ CanonAtlas.hubStarJoint y c t φ v)
    (e : AEdge t) (he : e ∈ hubStarAEdges t v) :
    Connects ω (srcPos t φ c e) (dstPos t φ y e) := by
  obtain ⟨W, hsub, hmem, -⟩ := hω
  exact PercLib.CriticalLRP.isUpper_connSet _ _ (hsub ⟨e, he⟩) (hmem ⟨e, he⟩)

/-- **The up arm of the joint hub event connects the up-arm source to the hub position**: `c` at
the root, `φ (parent v)` for a non-root hub, and in both cases to `φ v`.  This is the arm that
carries the parent slot of the source. -/
theorem hubStarJoint_up_connects {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {v : t.IPos} {ω : Config V} (hω : ω ∈ CanonAtlas.hubStarJoint y c t φ v) :
    Connects ω (hubUpSrc t φ c v) (φ v) := by
  have h := hubStarJoint_arm_connects hω (hubUpEdge t v) (hubUpEdge_mem_hubStarAEdges t v)
  simpa only [srcPos_hubUpEdge, dstPos_hubUpEdge] using h

/-- **A child arm of the joint hub event connects the hub position to the child's end.** -/
theorem hubStarJoint_child_connects {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {v : t.IPos} {ω : Config V} (hω : ω ∈ CanonAtlas.hubStarJoint y c t φ v) (b : Bool) :
    Connects ω (φ v) (childPos t φ y v b) := by
  have h := hubStarJoint_arm_connects hω (Sum.inl (v, b))
    (by rw [hubStarAEdges_eq]; cases b <;> simp)
  simpa only [srcPos_inl, dstPos_inl] using h

/-! ### The parent-aware three-point inclusion -/

/-- **The joint hub event implies the parent-aware joint three-point function at `φ v`.**  All
three arms are incident with `φ v` (the two child arms start there, the up arm ends there), so one
configuration connects `φ v` to each of the three *physical* far ends of `hubFar` -- the root leaf
`c` or the parent's position included. -/
theorem hubStarJoint_subset_threePoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) :
    CanonAtlas.hubStarJoint y c t φ v ⊆ hubThreePoint y c t φ v := by
  intro ω hω
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hubStarJoint_child_connects hω false
  · exact hubStarJoint_child_connects hω true
  · exact PercLib.CriticalLRP.connects_symm (hubStarJoint_up_connects hω)

/-- **The source's joint pair at the hub, parent-aware**: the joint hub event implies the
three-point function `P(up-arm end ↔ φ v, child end ↔ φ v)`, i.e. `HubJointEval.hubPairJoint`
with the pair `(hubUpSrc t φ c v, childPos t φ y v b)` and centre `φ v`.

The first pair point is the up arm's *own* end (`c` at the root, `φ (parent v)` otherwise); this is
what the source's parent slot carries.  It is neither `φ v` nor a generic alias for it. -/
theorem hubStarJoint_subset_upPair (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) (b : Bool) :
    CanonAtlas.hubStarJoint y c t φ v ⊆
      HubJointEval.hubPairJoint (hubUpSrc t φ c v) (childPos t φ y v b) (φ v) := by
  intro ω hω
  refine ⟨hubStarJoint_up_connects hω, ?_⟩
  exact PercLib.CriticalLRP.connects_symm (hubStarJoint_child_connects hω b)

/-- **Measure form of the parent-aware inclusion**: the joint hub value at the 3-star of `v` is at
most the three-point function `jointP π (up-arm end) (child end) (φ v)` at the physical hub. -/
theorem edgeMeasure_hubStarJoint_le_jointP (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (v : t.IPos) (b : Bool) :
    edgeMeasure π (CanonAtlas.hubStarJoint y c t φ v) ≤
      jointP π (hubUpSrc t φ c v) (childPos t φ y v b) (φ v) := by
  rw [HubJointEval.jointP_eq_edgeMeasure_hubPairJoint]
  exact measure_mono (hubStarJoint_subset_upPair y c t φ v b)

/-- **The root case**: at the root hub the parent-aware pair is `(c, child end)` at the hub
position, with `c` the root leaf's vertex.  No parent vertex occurs. -/
theorem hubStarJoint_subset_rootPair (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) (b : Bool) (h : IsRootIpos t v) :
    CanonAtlas.hubStarJoint y c t φ v ⊆
      HubJointEval.hubPairJoint c (childPos t φ y v b) (φ v) := by
  have h' := hubStarJoint_subset_upPair y c t φ v b
  rwa [hubUpSrc_eq_root t φ c v h] at h'

/-- **The non-root case**: at a non-root hub the parent-aware pair is `(φ (parent v), child end)`
at the hub position.  The parent vertex is a genuine internal vertex, different from `v`. -/
theorem hubStarJoint_subset_parentPair (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) (b : Bool) (h : ¬ IsRootIpos t v) :
    CanonAtlas.hubStarJoint y c t φ v ⊆
      HubJointEval.hubPairJoint (φ (parentIPos t v h)) (childPos t φ y v b) (φ v) := by
  have h' := hubStarJoint_subset_upPair y c t φ v b
  rwa [hubUpSrc_eq_parent t φ c v h] at h'

/-! ### The source-shaped block: three-point function times a two-point factor -/

/-- The merged slot family: the up arm and the `false` child arm are carried by **one** witness
set (their union), the `true` child arm by its own.  Merging is sound because the two witnesses of
the joint event are disjoint and both lie in the configuration. -/
theorem hubStarJoint_subset_mergedBK (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) :
    CanonAtlas.hubStarJoint y c t φ v ⊆
      DisjFam (fun i : Fin 2 =>
        if i = 0 then
          HubJointEval.hubPairJoint (hubUpSrc t φ c v) (childPos t φ y v false) (φ v)
        else connSet (φ v) (childPos t φ y v true)) := by
  classical
  intro ω hω
  obtain ⟨W, hsub, hmem, hdisj⟩ := hω
  -- The three slots of the 3-star, named.
  set iu : {e : AEdge t // e ∈ hubStarAEdges t v} :=
    ⟨hubUpEdge t v, hubUpEdge_mem_hubStarAEdges t v⟩ with hiu
  set if0 : {e : AEdge t // e ∈ hubStarAEdges t v} :=
    ⟨Sum.inl (v, false), by rw [hubStarAEdges_eq]; simp⟩ with hif0
  set it1 : {e : AEdge t // e ∈ hubStarAEdges t v} :=
    ⟨Sum.inl (v, true), by rw [hubStarAEdges_eq]; simp⟩ with hit1
  -- The two distinctness facts that the disjointness of the merged family needs.
  have hne_u : iu ≠ it1 := by
    rw [hiu, hit1]
    intro he
    exact hubUpEdge_ne_downEdge t v true (congrArg Subtype.val he)
  have hne_f : if0 ≠ it1 := by
    rw [hif0, hit1]
    intro he
    have hval : (Sum.inl (v, false) : AEdge t) = Sum.inl (v, true) := congrArg Subtype.val he
    have h2 : (v, false) = (v, true) := Sum.inl.inj hval
    exact absurd (congrArg Prod.snd h2) (by simp)
  refine ⟨fun k => if k = 0 then W iu ∪ W if0 else W it1, ?_, ?_, ?_⟩
  · -- every merged witness is open in ω
    intro k
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, Finset.coe_union]
      exact Set.union_subset (hsub iu) (hsub if0)
    · simp only [hk, ↓reduceIte]
      exact hsub it1
  · -- and each merged witness satisfies its slot event
    intro k
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, Finset.coe_union]
      refine ⟨?_, ?_⟩
      · refine PercLib.CriticalLRP.isUpper_connSet _ _ Set.subset_union_left ?_
        simpa only [hiu, CanonAtlas.atlasConnEvent, srcPos_hubUpEdge, dstPos_hubUpEdge]
          using hmem iu
      · refine PercLib.CriticalLRP.isUpper_connSet _ _ Set.subset_union_right ?_
        simpa only [hif0, CanonAtlas.atlasConnEvent, srcPos_inl, dstPos_inl,
          HubJointEval.connSet_comm] using hmem if0
    · simp only [hk, ↓reduceIte]
      exact PercLib.CriticalLRP.isUpper_connSet _ _
        (Set.Subset.refl _) (by
          simpa only [hit1, CanonAtlas.atlasConnEvent, srcPos_inl, dstPos_inl]
            using hmem it1)
  · -- the merged witnesses are pairwise disjoint
    intro k l hkl
    by_cases hk : k = 0
    · have hl : l ≠ 0 := fun hl => hkl (hk.trans hl.symm)
      simp only [hk, hl, ↓reduceIte]
      exact Finset.disjoint_union_left.mpr ⟨hdisj iu it1 hne_u, hdisj if0 it1 hne_f⟩
    · have hl : l = 0 := by
        fin_cases k <;> fin_cases l <;> simp_all
      simp only [hk, hl, ↓reduceIte]
      exact (Finset.disjoint_union_left.mpr
        ⟨hdisj iu it1 hne_u, hdisj if0 it1 hne_f⟩).symm

/-- **The source-shaped parent-aware block bound.**  The joint hub value at the 3-star of `v` is at
most the three-point function `jointP π (up-arm end) (child false end) (φ v)` times the single
two-point factor `τ π (φ v) (child true end)`.

This is the shape of the source's per-hub block (one joint three-point factor and raw two-point
factors), obtained here by two-fold BK on the merged slot family.  It is a per-hub slot statement:
no summation, no moment, and no replacement of the joint pair by a product of two-point factors. -/
theorem edgeMeasure_hubStarJoint_le_jointP_mul_tau (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    edgeMeasure π (CanonAtlas.hubStarJoint y c t φ v) ≤
      jointP π (hubUpSrc t φ c v) (childPos t φ y v false) (φ v) *
        PercLib.Percolation.Bond.tau π (φ v) (childPos t φ y v true) := by
  have hbk := bk_disjFam π hπ
    (A := fun i : Fin 2 =>
      if i = 0 then
        HubJointEval.hubPairJoint (hubUpSrc t φ c v) (childPos t φ y v false) (φ v)
      else connSet (φ v) (childPos t φ y v true))
    (fun i => by
      by_cases hi : i = 0
      · rw [ite_eq_left hi]
        exact HubJointEval.isUpperSet_hubPairJoint _ _ _
      · rw [ite_eq_right hi]
        exact PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun i => by
      by_cases hi : i = 0
      · rw [ite_eq_left hi]
        exact HubJointEval.finiteWitness_hubPairJoint _ _ _
      · rw [ite_eq_right hi]
        exact PercLib.CriticalLRP.finiteWitness_connSet _ _)
  refine (measure_mono (hubStarJoint_subset_mergedBK y c t φ v)).trans ?_
  refine hbk.trans (le_of_eq ?_)
  rw [Fin.prod_univ_two]
  have h1 : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [h1, ↓reduceIte]
  rw [HubJointEval.jointP_eq_edgeMeasure_hubPairJoint, HubJointEval.edgeMeasure_connSet_eq_tau]

/-! ### The same for a full canonical atlas realization -/

/-- **A full canonical atlas realization implies the parent-aware joint three-point function at
every hub.**  Composing production's `CanonAtlas.canonAtlasEvent_subset_hubStarJoint` with the
parent-aware inclusion above: the realization's own witnesses give the connection of `φ v` to the
root leaf `c` / the parent's position, not merely to the two child ends. -/
theorem canonAtlasEvent_subset_threePoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) :
    CanonAtlas.CanonAtlasEvent y c t φ ⊆ hubThreePoint y c t φ v :=
  (CanonAtlas.canonAtlasEvent_subset_hubStarJoint y c t φ v).trans
    (hubStarJoint_subset_threePoint y c t φ v)

/-- **A full canonical atlas realization implies the parent-aware joint pair at every hub**, with
the up-arm's own end as the first point of the pair. -/
theorem canonAtlasEvent_subset_upPair (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) (b : Bool) :
    CanonAtlas.CanonAtlasEvent y c t φ ⊆
      HubJointEval.hubPairJoint (hubUpSrc t φ c v) (childPos t φ y v b) (φ v) :=
  (CanonAtlas.canonAtlasEvent_subset_hubStarJoint y c t φ v).trans
    (hubStarJoint_subset_upPair y c t φ v b)

end HubUpArm
