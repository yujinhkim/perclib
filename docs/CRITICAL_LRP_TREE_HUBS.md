# General hub deselection for Lemma I.4.16

`TreeExpansion/Atlas` formalizes the finite combinatorial second step of the
proof of Lemma I.4.16 for every production `RTree`. It does **not** prove the
BK inequality, the probability bound, or the general moment estimate in the
lemma's conclusion.

Write `p = t.numLeaves`. The atlas of `t` consists of `t` with one additional
root leaf. Its leaves are `atlasLeaves t`, of cardinality `p + 1`; its edges
are `AtlasEdge t`, of cardinality `2p - 1`. The type `IPos t` identifies the
`p - 1` internal vertices. `ipaths` and `lpaths` give equivalent address-based
presentations, with the round trips in `Bridge.lean`.

## Main results

For every `k ≤ ⌈(p-1)/2⌉`:

* `RTree.exists_hubSet_ipos` selects `k` internal vertices in one depth-parity
  class. Distinct vertices in this class cannot be parent and child.
* Each `RTree.star` has three edges. Stars at vertices of the selected class
  are pairwise disjoint, so they use exactly `3k` edges.
* `RTree.exists_hub_edge_partition_ipos` partitions the atlas into the star
  edges and off-hub edges, with cardinalities `3k` and `2p - 1 - 3k`.
* `RTree.leaf_arms_at_ipos` provides three pairwise disjoint, nonempty sets of
  atlas leaves at every hub. Their union is the entire leaf set, and the third
  part contains the root leaf.
* `RTree.three_mul_le_two_mul_sub_one` proves `3k ≤ 2p - 1` when `p ≥ 2`, so
  the displayed natural-number subtraction is not a hidden truncation.
  `RTree.moment_exponent` records `2p - 1 - k = 2k + (2p - 1 - 3k)`.
* `RTree.exists_hub_structure` packages the hub set, parity, disjoint stars,
  three arms, edge partition and exponent arithmetic in one consumer theorem.

`Check.lean` includes a six-leaf non-vacuity example for the `p = 6,k = 2`
use in the proof of Proposition I.4.15, Case 2. This example is not used to
claim the corresponding moment bound.

The remaining work is the probabilistic step: expand the joint connection
event over rooted atlases, use the leaf arms and disjoint stars to apply BK,
sum the three-point and two-point diagrams with the exact multiplicities, and
obtain

```text
E|K|^p ≤ (2p - 3)!! (E|K|²)^k (E|K|)^(2p - 1 - 3k).
```

The abstract edge split alone does not supply that estimate. In particular,
no inhomogeneous moment inequality without the necessary translation
invariance is inferred here.

## Finite graph configuration realization and BK union bound

`TreeExpansion/AtlasRealization` now supplies a substantial part of the missing
all-configurations step. `Real.exists_realization` constructs, recursively, a
rooted binary shape for every nonempty finite terminal-label set connected
through a finite open witness, with distinct atlas positions and pairwise
edge-disjoint witnesses for all `2p - 1` atlas-edge events. Terminal labels are
distinct; image vertices need not be. The all-coincident case uses empty paths,
not fictitious open edges. This is not a permutation sweep over one chain.

`Real.prob_le_sum_shapes` applies general finite-index [`BKIncreasing`] and
finite unions to obtain the probability bound as a sum over all labelled shapes
and internal-vertex positions. `ex_realization` and `ex_cover` prove a concrete
interior-root path instance with `∅`, `{0}`, `{1}` witnesses. This is not less
than diagram combinatorics: it proves realization and its precise finite BK
probability bound, with only standard axioms in the independent and package
audits.

`WeightBridge.posSumWt_eq_wtL` and `posSumWtE_eq_wtE` now prove the internal
position sum equals the ordinary tree weight, recursively through root and child
edges. `AtlasRealization.Hub` separately transports the hub edge partition to the
realized atlas, proves every hub star's three edges share the intended vertex,
groups the product into `3k` versus `2p - 1 - 3k` factors, and applies BK to
finite shape sums. It distinguishes the joint three-point event from its product
bound.

## Child-swap transport and finite ordinary moments

`AtlasRealization/Transport` constructs a bijection between internal positions and
atlas edges for any two plane representatives of a child-swap class. It preserves
both ends of every atlas edge, carries the same finite witness sets, and therefore
proves equality of the unions of diagram events over all internal positions.
The position sums of diagram-event probabilities are equal as well.

`AtlasRealization/OrbitCount` supplies finite orbit partitions, a chosen transversal,
and exact transversal sums of invariant weights. `AtlasRealization/Closure` joins
these results and proves `treeGraphBound_of_atlasRealization` and
`moment_bound_of_atlasRealization`. The latter is the ordinary tree-moment bound
with coefficient `(2q-3)!!`, under BK and explicit translation invariance on a
finite additive commutative group. The residual `SwapTransport` premise is
eliminated by the checked realization transport.

These results still have finite edge configurations and finite vertex sets.
These finite-ambient results do not by themselves prove a canonical countable-model
moment formula, the general mixed hub/star evaluation of Lemma I.4.16, or model
sharpness. Independently, `AtlasRealization/ExactCount` now proves the exact
non-plane enumeration.

## Case 3 decorrelation wrapper

`HigherMoments/I420Case3` assembles the triangle-condition decorrelation chain
from the actual excluded mixed expectations, tree polygons, finite moment
conversions, little-o comparison, and the smaller-moment IH. It explicitly retains
I.4.17/I.4.18 as inputs plus homogeneity, finite moments and the separate first
versus p-moment comparison; it doesn't prove general tree expansions, Polygon
model hypotheses, or I.4.20 itself.


## Source/counting notes

The lemma statement has coefficient `(2p-3)!!`. The proof text mentions
`(2p-1)!!` for the tree count; this is an index discrepancy in the source's
proof commentary, not an altered hypothesis in these files.

The existing `TreeExpansion/Basic.lean` docstring mentions `RTree.card_labelled`
as an intended tree-count interface; there is no Lean declaration of that name
in the current implementation. `Count.card_LT_fin_le` is the older plane upper
bound, not an exact cardinal count.

`AtlasRealization/ExactCount` supplies the missing inverse direction:
`RTree.insertMap_injective`, `RTree.card_LT_sum_eq`, and
`RTree.card_LT_fin_eq`. The canonical `peel` recovers the original tree, the
position chain and the side of insertion. Consequently
`RTree.card_swapOrbits_fin_eq_dfactorial` proves exactly `(2p-3)!!`
child-swap classes for `p ≥ 1`. The separate statements
`card_swapOrbits_fin_zero` and `card_swapOrbits_fin_zero_ne_M` show why `p = 0`
must be excluded rather than interpreted as one labelled tree.

## Parent-aware up-arm slots

`Canonical/Hub/UpArm` integrates the independently rebuilt `smwx4z71g/m1`
artifact.  Relative to the address-level `src_upEdge`, it names the actual
parent vertex and gives per-hub comparisons for Lemma I.4.16's joint hub
blocks (paper pp. 43--44).

* `HubUpArm.IsRootIpos`, `parentIPos`, and `hubUpSrc` distinguish the root-leaf
  coordinate `c` from the position of the internal parent.  `srcPos_hubUpEdge`
  computes the up arm's source exactly; `dstPos_hubUpEdge` gives its
  destination `φ v`.  These are not both identified with `φ v`.
* `hubUpEdge_eq_rootEdge` identifies the root up arm with the atlas root edge.
  `hubUpEdge_eq_parentDown` identifies a non-root up arm with the down arm of
  `parentIPos`.  The position map need not be injective for either identity.
* `hubFar` records the two child positions and the up-arm source;
  `hubThreePoint` is one configuration connecting all three to `φ v`.
  `hubStarJoint_subset_threePoint` drops disjoint occurrence but retains this
  actual physical three-point event.
* `edgeMeasure_hubStarJoint_le_jointP_mul_tau` merges the up arm and one down
  arm into one joint-pair witness and applies two-fold BK with the other down
  arm.  The result is a genuine joint three-point factor times one two-point
  factor.  It does not replace the three-point value by `hubStarProd`, and it
  does not assert a converse joint-event inclusion.

These are shape-indexed, per-hub slot statements.  They do not sum all labels
or hubs and do not prove general `k`, a new mixed moment, or an atlas event
cover.  The full mixed-`k` evaluation remains open.  The parent and root cases
keep arbitrary coincident positions; only the separately named
`hubUpSrc_eq_hubPos_iff` characterization uses `Function.Injective φ`.

## The concrete three-leaf hub block

`Canonical/Hub/Block`, from the independently rebuilt partial `smwx6p0op/m3`
artifact, evaluates one genuine shape without discarding any of its five atlas
edges. The shape is `node (node (leaf 0) (leaf 1)) (leaf 2)`, with root internal
hub `hubI` and the other internal vertex `innerI`.

* `canonAtlasEvent_subset_hubSlots` merges the root up arm and the hub's
  `false` down arm into one joint pair, but retains the `true` down arm and the
  two off-hub arms as three pairwise-disjoint raw slots. This repairs the
  omitted-arm defect of the earlier candidate per-position assembly. Every
  coincidence of physical positions remains allowed.
* `edgeMeasure_canonAtlasEvent_le_hubBlock` applies BK to the four slots.
  `hubBlockValue_eq` expands it as
  `jointP π c (φ innerI) (φ hubI)` times the three raw two-point factors.
  `tsum_hubBlockValue` evaluates the sum over the three labelled leaf positions
  exactly as that joint factor times the three free arm sums;
  `tsum_atlasValue_le_const` supplies the constant row-sum form.
* `pinnedHubPairSum_eq` identifies a separate pinned joint-pair sum with the
  second cluster moment, and `tsum_tau_mul_pinnedHubPairSum` evaluates its
  sum against an incoming two-point factor under translation invariance.
  The concrete shape's pair has root leaf `c` as one point and `φ innerI` as the
  other, so this separate slot is **not** an evaluation of the concrete sum.
  The divergence of the unweighted pinned sum does not by itself supply the
  paper's total moment or explain away the remaining coupled positions.

This is a finite-shape BK and summation evaluation, not a general mixed-`k`
realization, a completed event cover, or a new high-order moment bound. Its
purpose is to retain every arm while exposing, rather than hiding, the missing
summation over the coupled hub and internal positions. All 48 declarations
introduced by the package are included in its local axiom audit and the global
production axiom audit.

## Candidate two-centre evaluations at `p = 5`, `k = 2`

`Correlation/SixPoint/MixedK2/TwoCentre` records the verified algebraic part of
`smwx8o5tv/m3`. These are candidate diagram slots, not a new event cover or an
unconditional two-hub moment theorem.

* `hubChainA_leaf` sums the two joint pairs at fixed centres to two second
  cluster moments. `hubChainA_tsum_root_single`, `..._root_single2`,
  `..._root_joint`, and `..._root_joint'` evaluate four root placements under
  full translation invariance, yielding `(E|K|²)² χ³` after the three remaining
  two-point sums. The ears of the other joint pair are not covered by these
  declarations.
* `hubTwoCentre_leaf` and its root-in-arm evaluation give the same target
  normalization for a second candidate shape with one joint pair at each
  centre. `jointP_le_tau_left/right` supplies the marginal bounds and
  `firstMoment_le_secondMoment` keeps the first/second-moment comparison
  explicit.

What remains is the actual `SixPoint.CombSystem`-certificate realization of
these slots, all seven arm positions, arbitrary root placements, and the event
cover and final moment assembly. No `hpoint` premise is discharged.
`MixedK2/Counterexample`, independently rebuilt from `smwxb4a1l/m3`, now
proves `Line6.hpoint_false`: on the six-vertex line with each of its five
edges open independently with probability `1/64`, the five-leaf event costs
`ε⁵`, while **every** family of 105 slot labellings is bounded by
`105 * 36 * ε⁷ < ε⁵`. The reachability formulas, cylinder probabilities,
`τ` formula and finite exponent check are Lean proofs with only the standard
axioms. The bound `ε⁷` is attained, while the profile is on non-transitive
`Fin 6`, not an admissible translation-invariant model. Thus this refutes the
raw candidate two-hub premise, **not** the paper's Lemma I.4.16 and not a
repaired admissible-class event cover. No transport from the line to
`ZMod 6` is needed by that package.

`Counterexample.Cycle6`, independently rebuilt from `smwxcafk7/m3`, proves
the stronger admissible-class obstruction. Its `stepProfile` opens the six
edges of a six-cycle independently with probability `1/64`. The proof gives
full translation invariance `hq_stepProfile`, the two arc dichotomy and an
`ε³` lower bound from one three-edge arc. Every two-hub term has exponent
at least `6`; allowing the five two-point bounds costs
`105 * 1152 * ε⁶ < ε³`. Hence `Cycle6.hpoint_false` refutes the raw premise
at `(0,3,3,3,3)` for every fixed 105-pattern family. This is **not** a
counterexample to the paper's Lemma I.4.16 or its finite moment bounds. It
shows that a different, source-faithful branch-point/hub realization and
event-cover registration are required.

`SixPoint.TwoJointThree`, independently rebuilt from `smwxdrsgz/m3`, gives one
such genuine event-level construction for the middle split `j = 2`. The first
joint group uses `p0 ++ s1` and `p1 ++ s1` for `conn b0 v ∩ conn b1 v`; the
second uses `p3`, `p4` and the reversed second spine for `conn b3 v ∩ conn b4 v`.
Together with the three split-arm witness sets these form finite, pairwise
edge-disjoint certificates. `combSystem_twoJointThree_le` applies the actual
fivefold finite BK theorem without using the refuted pointwise premise.
Both joint functions are nevertheless parametrized by `v`, so their slot
evaluation needs a separate argument. The other six split cases, normalization
and `Fin 15 × Fin 7` assembly are not proved by that helper alone.

`SixPoint.TwoJointEval`, reconstructed from the completed work in
`smwxenel0/m1`, carries that middle-split evaluation to completion for all
fifteen labelled patterns. `combSystem_union_le` absorbs the internal
spine/meeting witnesses *inside the event before taking union bounds*;
`midSlotK2_tsum_root_joint` and `midSlotK2_tsum_root_chain` give exactly
`(E|K|²)²(E|K|)³`, each under full profile translation invariance. The free
pairs use `secondMoment_eq` and root independence, while the anchored pair
uses `tsum_jointP_centre`; the residual order `t`, `b2`, `c` gives
`(E|K|)³` by two-point column sums. No independence of percolation events or
moment-finiteness assumption is introduced. This remains the middle split,
not the other six splits or the complete moment assembly.

`SixPoint.SplitPattern`, independently rebuilt from `smwxenel0/m2`, supplies
the explicit finite classification of all seven macro-edge split positions.
There are exactly three independent internal star pairs at each, with three
source-bipartition choices at the middle position and two at the others.
`fiveGroup_of_two_stars` retains each star's shared spine within its joint
certificate. The structurally new cases `j = 0`, `j = 5` and `j = 6` now have
exact finite two-joint/three-single certificates.

`SixPoint.SplitEvents`, independently rebuilt from `smwxfstjy/m3`, now closes
the remaining cases `j = 1,3,4` as well. `combSystem_certified` provides the
genuine finite certificate through its two star groups and three singleton
groups for **every** `j : Fin 7`; `law_combSystem_le` applies the actual
fivefold BK product bound at that position. `usedStars_mem` selects a genuine
admissible independent internal pair at each split, and
`residual_eq_usedSingles` verifies that the singleton factors are exactly its
residual macro-edges. No independence hypothesis, moment hypothesis or refuted
`hpoint` premise is used. The remaining step is the **evaluation** of these
groups, followed by the final terminal/moment assembly, not the finite
certificate layer.

`SixPoint.SplitEvaluation`, independently rebuilt from `smwxfstjy/m2`, provides
the analytic evaluations of the three additional configurations. Their values
at the displayed root placements are exactly `(E|K|²)²(E|K|)³`, obtained by
peeling two-point row/column sums, then the free and anchored three-point
functions. Arbitrary terminal-order slot identities and event-union bounds are
also proved. The final anchored ear is fixed: `b₁` at `j = 0`, `b₂` at `j = 5`,
and terminal `t` at `j = 6`. `combSystem_swap01` and `one_tsum_le` give the
arm-symmetry transport to one further root slot at `j = 1`. These are not
identities for every root placement or every pattern. Missing root slots at
`j = 1,5`, both comb-root roles at `j = 0,6`, and evaluations of `j = 3,4`
remain open. In particular this does not close the `105`-pattern k = 2 moment
assembly.

`SixPoint.K2Mass`, independently rebuilt from `smwxh86dl/m3`, makes the
residual precise without inventing an event-cover premise.
`fifth_moment_le_sum_shapeTotal` proves that the fifth moment is at most the
sum over all true six-terminal shape masses. `shapeTotal_mid_le` discharges
all fifteen of those masses at the middle split.

`SixPoint.K2Mass.RootCollapse`, independently rebuilt and accepted from
`smwxii2d9/m3` at production head `f3bb3eb`, now proves the previously open
reindexing. `shapeTotal5_rootSlot0/2` identifies each labelled pattern with
one of two canonical patterns by an explicit `Fin 5` coordinate permutation.
The root and sixth terminal are held fixed, while the four internal witnesses
remain inside the measured shape event. No invariance or moment-finiteness
hypothesis is used for these equalities. Consequently `rootClass_collapse`
discharges the former collapse premise, and
`fifth_moment_k2_le_of_rootSlot_bounds` leaves only the twelve off-middle
root-class mass bounds. Those bounds are **not** proved: the complete
`p = 5, k = 2` fifth-moment inequality remains open, and Lemma I.4.16 stays
partial.

`SplitEval2.RootSocket`, independently rebuilt and accepted from
`smwxii2d9/m1`, supplies fifteen genuine slot-product evaluations: both
pattern root sockets at every split, plus the third admissible socket at
`j = 0`. These equalities use only full profile invariance. Each statement
sums seven variables--five nonroot comb terminals and two interior vertices--in
its explicitly stated peel order. The pin uses `tsum_jointP_centre` for an
arbitrary held vertex, not an independence or moment-finiteness premise.
These are socket-level identities, not shape-mass bounds: the event-level
bridges at `j = 3,4`, the permutation from each peel order to the assembly's
pattern order, and the final fifth-moment assembly remain open.
