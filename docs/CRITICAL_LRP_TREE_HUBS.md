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

Still missing are the equality of each position sum to the normalized tree
weight, transport of the hub star partition into `k` three-point factors, and
conversion from finite `V`, `E`, real-valued Bernoulli configurations to the
canonical countable independent-edge law. The source moment estimate is not
discharged merely by this finite cover.


## Source/counting notes

The lemma statement has coefficient `(2p-3)!!`. The proof text mentions
`(2p-1)!!` for the tree count; this is an index discrepancy in the source's
proof commentary, not an altered hypothesis in these files.

The existing `TreeExpansion/Basic.lean` docstring mentions `RTree.card_labelled`
as an intended tree-count interface; there is no Lean declaration of that name
in the current implementation. The available `Count.card_LT_fin_le` is instead
an **upper bound** for plane trees. No exact atlas-cardinality theorem is
claimed by the realization work either: the shape set is a genuine labelled
binary family, but its exact unlabelled cardinality remains a separate issue.
