/- Independently rebuilt and integrated from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

Joint hub-value evaluation for the smallest mixed-moment case `p = 3`, `k = 1` of
Lemma I.4.16 (generalized tree-graph inequality) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45.

Production is read only (`.scratch/critical-lrp-orchestration`, HEAD
`c491c66109f24f38fa27cbccbcc52d11a14a8c33`); this module only *adds*.

## What is defined here

The source's `p = 3`, `k = 1` computation (p. 44) is

  `E|K|^3 = sum_{x,y,z} P(0 <-> x, y, z)`
  `       <= 3 sum_{x,y,z,w} P(0 <-> x, w) P(w <-> y) P(w <-> z)`
  `        = 3 E|K|^2 (E|K|)^2`,

where `P(0 <-> x, w)` is the three-point function at the branch point `w`: the joint event that
`w` is connected to *both* `0` and `x`.  Three objects are needed, and they are kept apart:

* `hubPairJoint a b c` -- the **three-point function at the hub** as an event:
  `a <-> c` and `b <-> c` in one configuration.  Its law is `FivePoint.jointP pi a b c`.
  This is an *intersection* of two connection events, not a product, and not a disjoint
  occurrence.
* `hubArmJoint c far` -- the **joint three-arm value at the physical hub `c`**: one
  configuration supplying three pairwise edge-disjoint open witnesses, one for each arm
  `far i <-> c` (`i : Fin 3`).  This is the canonical collapse of the production hub layer's
  `CanonAtlas.hubStarJoint` (three edges of a 3-star, one configuration, pairwise disjoint
  witnesses) to the three arms as seen from the physical hub vertex.
* `hubDiagJoint o x y z w` -- the **hub-indexed source diagram**: the pair `o, x` is carried
  *jointly* on the parent arm of the hub `w` (one witness set for `o <-> w` and `x <-> w`),
  and the two leaf arms `w <-> y`, `w <-> z` carry one witness each, all three witness sets
  pairwise edge-disjoint.  This is exactly the slot assignment of the source's
  `{0 <-> x, w} o {w <-> y} o {w <-> z}`.

The distinction between `hubArmJoint` and `hubPairJoint` is the point of the exercise: BK gives
`law (hubArmJoint c far) <= prod_i tau (far i) c` (a product of *three* two-point factors),
whereas the source's three-point block is `jointP` (a joint pair at the hub) times two
two-point factors.  Neither is an identity; see the sibling modules for what is proved in each
direction.

## Degenerate data

Nothing below is injective: `far` may repeat a vertex, the hub `c` may equal one of the `far i`,
and `o, x, y, z` may coincide with `w`.  An arm whose two ends coincide is connected by the
empty witness (production `connSet_self`), so it is satisfied and consumes no open edge; the
definitions below therefore do not need (and do not assume) distinctness of the data.  The
duplication is retained: each slot keeps its own witness, and a repeated physical vertex does
not merge two slots into one.
-/
module

public import PercLib.CriticalLRP.Correlation.CubicMixed.Moments
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Transport
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.StarEnds

/-!
# Definitions: hub pair joint, hub three-arm joint, hub-indexed source diagram

All definitions only; every proof is in the sibling modules.
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config connSet)
open PercLib.CriticalLRP.Percolation (DisjFam)

namespace HubJointEval

variable {V : Type*}

/-! ### The three-point function at the hub -/

/-- **The three-point function at the hub `c`**, as an event: the configuration joins `a` to `c`
and `b` to `c`.

Its `law π`-measure is the project's `jointP π a b c`, i.e. `law π (conn a c ∩ conn b c)`.
It is an intersection of two connection events: no disjointness of witnesses is required, and
it is *not* the product `tau π a c * tau π b c`. -/
def hubPairJoint (a b c : V) : Set (Config V) :=
  connSet a c ∩ connSet b c

/-- **The joint three-arm value at the physical hub `c`.**  One configuration, three pairwise
edge-disjoint finite open witness sets, one for each arm `far i <-> c`.

This is the physical-hub form of the production canonical layer's
`CanonAtlas.hubStarJoint` (three edges of a 3-star, one configuration, pairwise disjoint ambient
`Finset (Sym2 V)` witnesses); the arms are indexed by `Fin 3` here and the common end is the
single physical vertex `c`.  It is a joint event: it is not a product of three two-point
events, and BK only bounds its measure by such a product. -/
def hubArmJoint (c : V) (far : Fin 3 → V) : Set (Config V) :=
  DisjFam fun i : Fin 3 => connSet (far i) c

/-- **The hub-indexed source diagram at `p = 3`, `k = 1`**, with the hub at `w` and the slot
assignment of the source: the *parent* slot carries the joint pair `o, x` in one witness set,
the two *leaf* slots carry `w <-> y` and `w <-> z`, and the three witness sets are pairwise
edge-disjoint.

The pair slot is deliberately the joint event `hubPairJoint o x w` and not two separate arms:
this is the "three-point function" slot that survives the summation over `x` and `w` as a second
moment.  `HubJointEval.hubDiagJoint_eq_starPairEvent` identifies this event with production's
`PercLib.CriticalLRP.TreeExpansion.StarPairEvent`. -/
def hubDiagJoint (o x y z w : V) : Set (Config V) :=
  DisjFam fun i : Fin 3 => ![hubPairJoint o x w, connSet w y, connSet w z] i

/-! ### The evaluated hub blocks -/

/-- **The evaluated hub-split block** of the source: the three-point function at the hub times
the two remaining two-point factors, `P(o <-> x, w) P(w <-> y) P(w <-> z)`.

This is the value of one hub diagram after the BK step at the hub, and it is the quantity that
is summed over the hub position `w` and the free pair point `x`. -/
noncomputable def hubSplitValue (π : Sym2 V → unitInterval) (o x y z w : V) : ℝ≥0∞ :=
  PercLib.CriticalLRP.TreeExpansion.FivePoint.jointP π o x w *
    (PercLib.Percolation.Bond.tau π w y * PercLib.Percolation.Bond.tau π w z)

/-- **The hub-indexed three-point sum**: the three-point function summed over the hub position
`w` (outer sum) and the free pair point `x`.  `HubJointEval.hubPairSum_eq_secondMoment`
identifies it with the native second cluster moment. -/
noncomputable def hubPairSum (π : Sym2 V → unitInterval) (o : V) : ℝ≥0∞ :=
  ∑' w, ∑' x, PercLib.CriticalLRP.TreeExpansion.FivePoint.jointP π o x w

/-- **The fully summed hub evaluation** at `p = 3`, `k = 1`: the hub position outermost, then
the pair point and the two free leaf endpoints.  This is the sum of `hubSplitValue` over
`(w, x, y, z)`, the quantity that equals `3 E|K|^2 (E|K|)^2` in the source. -/
noncomputable def hubSplitSum (π : Sym2 V → unitInterval) (o : V) : ℝ≥0∞ :=
  ∑' w, ∑' x, ∑' y, ∑' z, hubSplitValue π o x y z w

/-- The configuration on `Fin 2` with the single open pair `{0, 1}`, used to prove that a
joint three-point event need not carry three disjoint witnesses. -/
def oneEdgeConfig : Set (Sym2 (Fin 2)) := {s(0, 1)}

end HubJointEval
