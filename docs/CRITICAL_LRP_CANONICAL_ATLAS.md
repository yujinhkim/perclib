# Canonical atlas realization and finite-index BK

This note records the canonical countable-model parts of the atlas proof behind
Lemma I.4.16 of Hutchcroft, *Critical long-range percolation I*. It is not a claim
that the full generalized mixed-moment inequality is complete.

## Finite witnesses, not a finite-box model

`TreeExpansion/AtlasRealization/Canonical` defines `CanonAtlas.IsCanonRealization`.
For a shape with root at the leaf vertex `c`, terminal values `y a`, and internal
positions `φ`, each atlas edge carries a **finite set of ambient open edges**.
Distinct atlas edges have pairwise-disjoint finite witnesses, and each witness
connects the actual source and destination assigned to that atlas edge. An empty
witness is allowed only when its two endpoints coincide: the small-leaf examples
and the diagonal theorem make this case honest rather than free of witnesses.

Given a configuration in the canonical model, finite witnesses for the terminal
connections are extracted from that configuration. The finite graph on the
resulting subset of edges is transported to the ambient canonical graph on
`Sym2 V`. There is no finiteness assumption on the ambient vertex or edge type,
no radius-dependent cluster truncation, and no pretence that the selected witness
is the whole cluster. The full shape and internal-position cover is nevertheless
countable, as appropriate for an infinite vertex type.

The `labelEvent` connection event for a nonempty finite family was proved to be
included in the canonical atlas cover (`conn_subset_canonCover`). For `q = 0`, the
cover is empty and there is an explicit negative boundary example rather than a
spurious one-point atlas.

## BK over a finite index

`BK/FiniteIndex` introduces `Percolation.DisjFam`: a finite family of events
occurs with a separate finite witness set for each index, all witnesses are open,
and the witnesses are pairwise edge-disjoint. `disjFam_finiteWitness`,
`disjFam_upper`, and the empty/diagonal examples record its structural properties.

The module proves a genuine set equality

```text
DisjFam A = Percolation.DisjointOccurrenceList (List.ofFn A)
```

for a finite index, by explicitly constructing the witness families in both
directions. It does not assume that nested disjoint occurrence is automatically
the same as arbitrary pairwise disjoint occurrence. The existing canonical BK
for lists therefore applies without changing the event or replacing the graph by
an artificial finite-box graph. `Percolation.bk_disjFam` gives the corresponding
`ℝ≥0∞` bound, and `Percolation.bk_disjFam_real` gives its real-valued version.

In particular, `edgeMeasure_bk_connSet_fam` states that, for finite `ι` and
endpoints `uᵢ, vᵢ` in an arbitrary countable vertex type,

```text
P(all connections uᵢ ↔ vᵢ with disjoint witnesses)
  ≤ ∏ᵢ P(uᵢ ↔ vᵢ).
```

The diagonal connection event has probability one and consumes no open edge.
BK for the family of connections at the actual atlas edges is
`edgeMeasure_bk_atlas`.

## The completed canonical union-bound component

`CanonAtlas.canonAtlasEvent_eq_disjFam` identifies the event carried by the
canonical realization with the finite-index family exactly. This is the joining
step, not a claim that one construction is a convenient schematic version of the
other. Consequently `CanonAtlas.Measure.canonAtlasEvent_bk` discharges the
remaining per-diagram BK input in the older union-bound wrapper.

The exported aggregate statements are
`CanonAtlas.Measure.measure_labelEvent_le_tsum_bk` and
`CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk`. For `q ≥ 1`, they
bound the probability that a root is connected to every labelled terminal by the
sum over all labelled shapes `t : LTon (Fin q) univ` and all internal positions
of the product of the connection probabilities along the `2q-1` atlas edges.
The split version places the internal-position sum inside the shape sum so that
it can subsequently be identified with the tree weight.

The sum uses the genuine `edgeMeasure` law and countable subadditivity. The
`Example` and `CanonAtlas.Audit` modules supply small realization checks and
standard-axiom checks for the components.

## Canonical child-swap transport and the transversal bound

`Canonical/Transversal` transports `IsCanonRealization` across a child swap using
the existing `SwapIso`. The physical leaf labelling and root are unchanged, and
the same finite ambient witness sets are reindexed by `aedgeEquiv`. Consequently
both the event and the ENNReal `tsum` over internal positions are invariant on a
swap orbit. The same transport reindexes `atlasProduct`, without a finiteness
assumption on `V` or on any `tsum`.

`canonCover_subset_transversal_iUnion` replaces the full plane-shape cover by one
representative from `RTree.transversal`. The exported
`measure_labelEvent_le_sum_transversal_bk` therefore bounds the probability of a
nonempty finite labelled connection event by a finite sum over orbit
representatives, with an unrestricted ENNReal position sum for each one. This
removes the plane multiplicity rather than merely counting the shapes.
`tsum_shapes_eq_two_pow_mul_sum_transversal` establishes the exact multiplicative
relationship with the earlier plane-shape sum, and
`measure_labelEvent_le_tsum_shapes_bk'` rederives that earlier bound from the
stronger transversal statement.

## Remaining work

The transversal position sum is definitionally `Real.posSumWtE`, and
`tsum_atlasProduct_eq_wtE` evaluates it by the already existing countable
ENNReal bridge `Real.posSumWtE_eq_wtE`. Hence
`measure_labelEvent_le_wtE_transversal_bk` gives the same bound as a sum of
`I417Base.wtE` tree weights, without a new weight definition or finiteness
assumption.

## Remaining work

This does not prove a mixed-`k` hub-star evaluation, a general-p cluster-volume
moment, or I.4.17. The orbit-representative weighted non-plane bound and the
double-factorial coefficient are not inferred from the shape multiplicity alone.

`TreeExpansion/AtlasRealization/ExactCount` independently closes the exact
non-plane shape enumeration for `p ≥ 1`. The hub-star evaluation,
translation-invariant first/second moments, regularity inputs, and model
sharpness remain separate obligations.

The small `q = 1` realization and explicit `q = 0` boundary check are evidence of
non-vacuity, not substitutes for the general moment induction.
