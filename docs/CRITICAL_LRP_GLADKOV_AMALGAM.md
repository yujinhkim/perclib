# Fixed-revealed-set amalgamation for the Gladkov route

`Correlation/Gladkov/Amalgam` proves the deterministic restriction of the
amalgamation lemma used in decision-tree percolation arguments. **It does not
prove Theorem I.2.7 or the random decision-tree version of the lemma.**

## Statement and model

Two independent inhomogeneous Bernoulli configurations are encoded by
`prodBernoulli (twoProfile q)` on `Set (ι × Bool)`. For a fixed `T : Set ι`,
`amalFirst T` agrees with the first copy on `T` and the second off `T`;
`amalSecond T` reverses those roles.

For measurable sets of configurations `A` and `B`, `amalgam_indep` proves
$$P(C_1\to_T C_2\in A,\ C_2\to_T C_1\in B)=P(A)P(B).$$
`map_amalFirst` proves that each amalgamated configuration has the original
law. The companion results `map_copy`, `flipConfig_map`, and `copy_indep`
prove the copy marginals, invariance under flipping copies off `T`, and
independence of events on the two disjoint copy-coordinate blocks. The flip
sends the amalgamated pair to the original pair, yielding the desired identity.
The choices $T=\varnothing$ and $T=\mathrm{univ}$ give explicit nondegenerate
identities.

## Remaining source ingredients

A random $S(C_1,C_2)$ constructed by a decision tree needs measurability and
cylindrical invariance of each $\{S=T\}$, followed by a countable partition
into the fixed-set result above. That induction, the decision-tree Harris and
van den Berg--Kahn--Reimer theorems, the influence-weighted Cauchy--Schwarz
step, and the DFS witness combinatorics remain unproved here. Consequently
`GladkovInput` must remain an explicit literature input rather than being
relabelled as proved.

The integrated module passes the project's strict elaboration and its five
audited main theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
This establishes proof status for the fixed-set packet, not source coverage of
I.2.7.

## Countable self-determined random revealed sets

See [the random-amalgamation note](CRITICAL_LRP_RANDOM_AMALGAM.md) for the new
countable-family independence theorem, a genuinely random non-vacuity example,
and compiled counterexamples. This advances beyond fixed `T` while retaining
an explicit self-determination condition. The actual finite decision-tree
transcript formulation and the full Gladkov inequality remain unproved.
