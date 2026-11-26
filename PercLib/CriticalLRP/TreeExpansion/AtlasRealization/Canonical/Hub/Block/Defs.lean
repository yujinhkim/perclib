/-
Independently reviewed and integrated from the partial artifact
`.ultramath/smwx6p0op/m3/HubEval`. Production integration revision:
`57e71d7ca447d7d83bfa761bb296fde27f6eb970`. This is a concrete one-shape
hub evaluation, not a general mixed-moment theorem.
-/
/-
Independently built for swarm `smwx6p0op`, member `m3`, direction HUB-EVALUATED-BLOCK.

Production base: read-only checkout `.scratch/critical-lrp-orchestration` at local HEAD
`9be3dd2832bf4fe01e33a70c2c3192ab4c837d88`.  Nothing outside this member directory is modified.

# A one-hub block of the generalized tree-graph inequality at a *genuine tree shape*

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.16 and its proof (pp. 43--44).
The printed proof partitions the `2p - 1` edges of a binary tree rooted at a leaf into the
3-stars around the `k` distinguished internal vertices and the remaining `2p - 1 - 3k` edges, and
charges each hub **two** units (`E|K|^2`) rather than three, because "the vertices in the
distinguished set are not summed over".

This file fixes one shape and one hub, and keeps *every* edge of the shape:

* `t3` is the smallest tree with a hub that has off-hub edges: two internal vertices and three
  labelled leaves, `node (node leaf 0 leaf 1) leaf 2`.  It has `2 * 3 - 1 = 5` atlas edges.
* `hubI` is its root internal vertex.  Taking the hub set `S = {hubI}` (trivially independent),
  the 3-star of `hubI` is `{root edge, down false, down true}` -- exactly `3` edges -- and
  `offHubAEdges t3 {hubI} = {down (innerI false), down (innerI true)}` -- exactly `2 = 2p-1-3`
  edges, both carried by the *other* internal vertex `innerI`.  (`offHubAEdges_eq`.)

The block of `hubSlots` therefore has four slots, and it keeps all three arms of the hub:

* `none` -- the **merged joint pair at the hub** `φ hubI`: the up arm (whose own source is the root
  leaf `c`, production `HubUpArm.hubUpSrc`) and the `false` down arm, carried by one witness set
  each and merged into one joint event `HubJointEval.hubPairJoint`;
* `some 0` -- the hub's `true` down arm, a raw two-point event;
* `some 1`, `some 2` -- the two off-hub edges of `innerI`, raw two-point events.

Two things this file deliberately does *not* do.  It does not drop the hub's `true` down arm
(the earlier hub-slot assembly dropped it, and an upper bound with one arm of the shape deleted is
not a block of the shape any more).  And it does not identify `hubBlockValue` with the source's
total moment: `pinnedHubPairSum` is the source's `E|K|^2` slot (both far ends of a joint pair at a
**pinned** hub, summed) and it is a *different* object from `hubBlockValue`, whose hub pair has the
root leaf `c` as one fixed point.

Definitions only in this file; every proof is in the sibling modules `Assembly.lean`,
`Summed.lean` and `Audit.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.UpArm.ParentIncl
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Defs

/-!
# Definitions: the three-leaf one-hub block and its evaluated sums
-/

@[expose] public section

open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config connSet edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge childPos srcPos dstPos)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.HubEval

variable {V : Type*}

/-! ### The shape, its hub, and the other internal vertex -/

/-- **The shape**: a binary tree with two internal vertices and three labelled leaves, the root
internal vertex carrying one leaf and one internal child.  It has `5 = 2 * 3 - 1` atlas edges, so a
one-hub block of it has `2 = 2 * 3 - 1 - 3` off-hub edges. -/
def t3 : RTree (Fin 3) :=
  RTree.node (RTree.node (RTree.leaf 0) (RTree.leaf 1)) (RTree.leaf 2)

/-- **The hub**: the root internal vertex of `t3`.  Its up arm's own source is the root leaf. -/
def hubI : t3.IPos := Sum.inr (Sum.inr ⟨⟩)

/-- The other internal vertex of `t3`, the child of the hub in the `false` direction.  Both its
down edges are off-hub edges of the hub set `{hubI}`. -/
def innerI : t3.IPos := Sum.inl (Sum.inr (Sum.inr ⟨⟩))

/-- The hub's `false` down arm ends at the other internal vertex. -/
theorem childPos_hub_false (φ : t3.IPos → V) (y : Fin 3 → V) :
    childPos t3 φ y hubI false = φ innerI := rfl

/-- The hub's `true` down arm ends at the labelled leaf `2`. -/
theorem childPos_hub_true (φ : t3.IPos → V) (y : Fin 3 → V) :
    childPos t3 φ y hubI true = y 2 := rfl

/-- The off-hub edge `innerI false` ends at the labelled leaf `0`. -/
theorem childPos_inner_false (φ : t3.IPos → V) (y : Fin 3 → V) :
    childPos t3 φ y innerI false = y 0 := rfl

/-- The off-hub edge `innerI true` ends at the labelled leaf `1`. -/
theorem childPos_inner_true (φ : t3.IPos → V) (y : Fin 3 → V) :
    childPos t3 φ y innerI true = y 1 := rfl

/-! ### The block: one merged hub pair plus the three retained raw arms -/

/-! ### The five atlas edges of `t3`, named -/

/-- The root edge of `t3`: the hub's up arm. -/
def upEdge : AEdge t3 := Sum.inr ⟨⟩

/-- The hub's `false` down arm, which ends at the other internal vertex. -/
def hubFalseEdge : AEdge t3 := Sum.inl (hubI, false)

/-- The hub's `true` down arm, which ends at the labelled leaf `2`. -/
def hubTrueEdge : AEdge t3 := Sum.inl (hubI, true)

/-- The raw arms of the block, as atlas edges: the hub's third arm first, then the two off-hub
edges of `innerI`. -/
def armEdge : Fin 3 → AEdge t3 :=
  ![hubTrueEdge, Sum.inl (innerI, false), Sum.inl (innerI, true)]

/-- The three retained raw two-point arms of the block, as the connection events of `armEdge`.
Index `0` is the hub's own third arm; indices `1` and `2` are the two off-hub edges of `innerI`.
Reading them through `srcPos`/`dstPos` is what makes the atlas comparison definitional. -/
noncomputable def armSlot (y : Fin 3 → V) (φ : t3.IPos → V) : Fin 3 → Set (Config V) :=
  fun i => connSet (srcPos t3 φ (φ hubI) (armEdge i)) (dstPos t3 φ y (armEdge i))

/-- Slot `some i` of the block is the connection event of the atlas edge `armEdge i`. -/
theorem armSlot_apply (y : Fin 3 → V) (φ : t3.IPos → V) (i : Fin 3) :
    armSlot y φ i = connSet (srcPos t3 φ (φ hubI) (armEdge i)) (dstPos t3 φ y (armEdge i)) := rfl

/-- Slot `0`: the hub's `true` down arm, a raw two-point event. -/
theorem armSlot_zero (y : Fin 3 → V) (φ : t3.IPos → V) :
    armSlot y φ 0 = connSet (φ hubI) (y 2) := rfl

/-- Slot `1`: the off-hub edge of `innerI` in the `false` direction. -/
theorem armSlot_one (y : Fin 3 → V) (φ : t3.IPos → V) :
    armSlot y φ 1 = connSet (φ innerI) (y 0) := rfl

/-- Slot `2`: the off-hub edge of `innerI` in the `true` direction. -/
theorem armSlot_two (y : Fin 3 → V) (φ : t3.IPos → V) :
    armSlot y φ 2 = connSet (φ innerI) (y 1) := rfl

/-- **The slot family of the one-hub block of `t3` at the hub `hubI`.**  Index `none` is the merged
joint pair at the hub (up arm + `false` down arm, one witness set each, merged into one joint
event); index `some i` is the raw arm `armSlot y φ i`.  All *five* atlas edges of `t3` occur: the
hub's three star edges through `none` and `some 0`, and the two off-hub edges through
`some 1`, `some 2`. -/
noncomputable def hubSlots (y : Fin 3 → V) (c : V) (φ : t3.IPos → V) :
    Option (Fin 3) → Set (Config V)
  | none =>
    HubJointEval.hubPairJoint (HubUpArm.hubUpSrc t3 φ c hubI) (childPos t3 φ y hubI false)
      (φ hubI)
  | some i => armSlot y φ i

/-- **The block value**: the BK product over the slots of the block.  `Assembly.lean`,
`hubBlockValue_eq`, evaluates it as the joint pair at the hub (with the root leaf `c` as its first
point, so the up arm is present and never identified with the hub) times the three retained raw
two-point factors -- one *joint* factor and three two-point factors, never four two-point factors.

Keeping the definition as the slot product makes the BK step exact, and puts the whole content of
"the block is `joint × 3` two-point factors" into the named evaluation. -/
noncomputable def hubBlockValue (π : Sym2 V → unitInterval) (y : Fin 3 → V) (c : V)
    (φ : t3.IPos → V) : ℝ≥0∞ :=
  ∏ o : Option (Fin 3), edgeMeasure π (hubSlots y c φ o)

/-- **The evaluated leaf sum of the block.**  The three labelled leaves of `t3` are the only free
positions of the block once the hub pair's two points and the hub position are named, so the
diagram sum over the leaf labels is the iterated sum below.  `Summed.lean`, `tsum_hubBlockValue`,
evaluates it exactly. -/
noncomputable def leafSumBlock (π : Sym2 V → unitInterval) (c : V) (φ : t3.IPos → V) :
    ℝ≥0∞ :=
  ∑' z0 : V, ∑' z1 : V, ∑' z2 : V,
    jointP π c (φ innerI) (φ hubI) *
      (PercLib.Percolation.Bond.tau π (φ hubI) z2 *
        (PercLib.Percolation.Bond.tau π (φ innerI) z0 *
          PercLib.Percolation.Bond.tau π (φ innerI) z1))

/-- **The source's `E|K|^2` hub slot**: a joint pair at the *pinned* hub `a` with **both** far ends
summed.  This is the quantity the printed proof charges one hub `2` units for, and
`Summed.lean`, `pinnedHubPairSum_eq`, identifies it with the second cluster moment. -/
noncomputable def pinnedHubPairSum (π : Sym2 V → unitInterval) (a : V) : ℝ≥0∞ :=
  ∑' u : V, ∑' w : V, jointP π u w a

/-- **The free arm sum at a vertex**: `∑_z τ(a,z)`.  This is one summed leaf position, i.e. one
copy of the source's first moment, and `Summed.lean`, `armSum_eq_of_const_rowSum`, turns it into
the constant `χ` under the paper's constant-row-sum hypothesis. -/
noncomputable def armSum (π : Sym2 V → unitInterval) (a : V) : ℝ≥0∞ :=
  ∑' z : V, PercLib.Percolation.Bond.tau π a z

end PercLib.CriticalLRP.TreeExpansion.HubEval
