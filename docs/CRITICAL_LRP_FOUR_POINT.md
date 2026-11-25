# The deterministic four-point pairing cover

`Correlation/FourPoint` proves the graph-theoretic cover used by the `p = 3`
branch-point example in the proof of Lemma I.4.16. It does not yet complete
the BK and summation steps or the general-`p` moment bound.

For vertices `o,x,y,z` in one connected component of an arbitrary simple graph,
`cover_of_reachable` supplies `w`, a partition `{t,u,v} = {x,y,z}`, and walks
`P : o → w`, `Q : t → w`, `R : u → w`, `S : v → w` with

```text
(P.edges ++ Q.edges) disjoint R.edges,
(P.edges ++ Q.edges) disjoint S.edges,
R.edges disjoint S.edges.
```

Here `P ∪ Q` is a connected witness for all of `o,t,w`, but `P` and `Q` need not
be edge-disjoint from one another. The two other arms are disjoint from that
joint cluster and from each other, as required by BK. Either arm may be an
empty walk (`u = w` or `v = w`). The joint terminal is selected as part of the
proof, so all three of the paper's root pairings remain available; no single
fixed pairing is imposed.

`disjoint_of_dist_add` is the metric lemma: geodesics satisfying the five
betweenness identities are forced to have these edge-disjointness properties,
including when one is empty. `exists_three_arm_data` constructs the required
three pairwise disjoint geodesic arms from any three terminals connected to a
common point, by minimizing the sum of their lengths. On a tree, two paths
ending at the centre and meeting elsewhere share their last edge, so only one
arm can conflict with the root's arm. Giving that terminal the joint role
proves `tree_cover`. `cover_of_reachable` then transports the tree result via
injective graph homomorphisms from a spanning tree of the root's connected
component. The theorem is not merely a finite-model computation.

`ProofBKHelpers.mem_disjOcc3_of_walks` converts these walks into the appropriate
threefold disjoint occurrence on finite open-witness sets, and
`prob_union_le` is available for the union bound. `pair_eq_of_triple` is used
only at the subsequent unpacking stage, where distinctness assumptions are
explicit.

## What remains open

The paper's inequality at `p = 3` still needs the union bound over the centre
`w` and over all three joint-terminal alternatives, the threefold BK product
bound, and the exact sum yielding the coefficient `3`. That BK/summation
assembly is not included in this module. The cover does not by itself prove
`E|K|³ ≤ 3 E|K|² (E|K|)²`, and I.4.16 in general remains open.

The earlier withdrawn claim that the source's three-pairing cover is false is
not adopted here: the full union, not one fixed alternative, is the correct
statement, and the collinear case genuinely requires an empty arm.
