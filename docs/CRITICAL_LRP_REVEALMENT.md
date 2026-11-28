# Finite cluster exploration and revealment

`Analysis/SecondMomentCase3/CriticalVolumeTail/Entropy/Revealment` proves an
unconditional finite cluster-exploration/revealment estimate. Finite vertex and
edge types have endpoint maps `lft rgt` and real edge weights `J`. The source's
product Bernoulli model is reused through `confWeight` and `evProb`.

At each step the exploration selects a new edge incident to the discovered
vertex set, then reads that edge. If open, it adds the far endpoint. No queried
edge is repeated, `disc` stays inside the open root cluster and has at most `n`
vertices, and open queried edges have both endpoints discovered. Once it stops,
the discovered set has exactly `|K| ∧ n` vertices.

The bound is
$$\sum_e J_e P_\beta(e\text{ is revealed by time }k)
 \le A\sum_{j=1}^n P_\beta(|K|\ge j),$$
provided every vertex has incident weight sum `weightAt = A`. This is the
homogeneity/transitivity assumption used to replace a vertexwise charge by
`A times #disc`; the inhomogeneous form keeps the weighted sum explicit. It is
a genuine probability of `e ∈ quer`, not a path-multiplicity or a raw inductive
count. `revealment_budget_stopped` states the bound at `Fintype.card E` steps.
A one-edge example computes the revealment probability and unit cluster-tail
term explicitly, so the interfaces are not vacuous.

## Remaining source assumptions

The theorem is finite-dimensional. It does not prove convergence of restricted
explorations or revealment sums, compatibility of the source's infinite
transcript space with this finite class outline, or
`TwoIntensityTailComparison`; the separate canonical layer-cake and
finite-window results are in
[the canonical-tail note](CRITICAL_LRP_CANONICAL_TAIL.md). The source's
root-cluster computation and
weighted incidence assumptions must be established separately for the canonical
infinite long-range model.
