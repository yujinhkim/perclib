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

## Remaining work

This does not by itself prove a mixed-`k` hub-star evaluation, a general-p
cluster volume moment, or I.4.17. The aggregate still runs over plane labelled
shapes and needs the appropriate child-swap/orbit treatment before a non-plane
coefficient is inferred. It also does not supply the general non-plane shape
cardinality, the hub position-sum evaluation, translation-invariant first/second
moments, regularity inputs, or model sharpness. Those are separate obligations.

The small `q = 1` realization and explicit `q = 0` boundary check are evidence of
non-vacuity, not substitutes for the general moment induction.
