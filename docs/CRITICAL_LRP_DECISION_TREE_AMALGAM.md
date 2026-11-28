# Finite decision-tree amalgamation

`Correlation/Gladkov/DecisionTree` proves the finite-graph independence result
underlying Gladkov's Lemma 3.1 and [GZ24, Lemma 4.2]. This is the procedural
hypothesis itself, not the earlier countable-family self-determination case.

## Transcript model and hypothesis

A strategy reads records containing an edge, its class (`S` or its complement),
and the two copies' values at that edge. It chooses the next fresh edge and
its class using only the previous transcript, **before** the two current values
are read. `Consistent σ` requires distinct queried edges along every path.
The finite edge type supplies the source's finite-graph hypothesis.

The tree terminates within `Fintype.card ι` steps. Query values from the final
record are stored, but no later strategy reads them, so this harmless
strengthening does not change the produced revealed set or amalgamations.
Unqueried edges do not belong to the revealed set.

## Reconstruction and independence

`treeConfig` encodes the two amalgamations by permuting the two copies at each
edge. The map is not assumed injective. The reconstruction theorem proves that
running the strategy from the encoded pair reproduces the exact transcript;
`unamal` is an explicit inverse. Each query keeps both values when assigned to
`S`, and exchanges them otherwise, so each configuration atom retains its
product-Bernoulli weight.

Independence for arbitrary events then follows by finite summation rather than
by conditioning on a guessed revealed set or borrowing its probability weight.
The main theorem is `prodBernoulli_treeFirst_second_indep`, with original-law
corollaries for both amalgamations, a product-form push-forward law, and the
measure-preserving bijection `map_treeConfig`. No `SelfDetermined` or countable
family of candidate revealed sets is assumed.

`Examples` and `FixedSet` recover the empty, singleton, and arbitrary fixed-set
cases. `AdaptiveExample` constructs a two-edge tree whose revealed set is not
self-determined. It therefore checks the missing procedural case of the earlier
packet rather than merely checking it again under the old hypothesis.

## Scope

The proof covers finite graphs. It does not prove infinite-product amalgamation,
decision-tree HK or vdBK, the DFS witness combinatorics, or Theorem I.2.7
itself. The stronger joint-independence operation sometimes required in later
steps is not asserted. Sources:
[Gladkov, Lemma 3.1](https://arxiv.org/html/2408.08457v2#S3.Thmtheorem1) and
[Gladkov–Zimin, Lemma 4.2](https://arxiv.org/html/2404.08873v2#S4.Thmtheorem2).
All seven modules passed an independent dependency-ordered strict rebuild and
full axiom audit, with only subsets of `propext`, `Classical.choice`, and
`Quot.sound` reported.
