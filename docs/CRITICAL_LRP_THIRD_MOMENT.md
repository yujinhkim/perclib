# Unconditional native third-moment bound

`Correlation/ThirdMoment.lean` proves the native `ℝ≥0∞` tree-graph reduction of
the third cluster moment. `Correlation/ThirdMoment/ArmDecomposition.lean`
proves its previously missing graph hypothesis on an arbitrary simple graph.
The resulting infinite-volume bound has no finite-ambient-graph or
moment-finiteness premise.

## Tree-graph ingredients

* `prodBernoulli_five_wit_le` is fivefold BK for increasing events having
  pairwise-disjoint finite open witnesses. The five events are the two cluster
  connections at the two branch vertices plus the spine connection.
* `lintegral_cardFun_cube_eq` identifies expected `|K_x|³` with the triple sum
  of joint connection probabilities by Tonelli, without a summability premise.
* `tsum_row_eq` and `tsum_col_eq` show that a translation-invariant two-point
  function has the same row and column sums. Homogeneity is essential: the
  analogous inhomogeneous cubic second-moment inequality has explicit finite
  counterexamples.
* Each of the three labelled binary trees on four leaves has five-factor sum
  exactly `(E|K|)⁵`, including degenerate star terms where the two branch
  vertices coincide. Summing all three gives the required factor `3`.

## The arm decomposition is proved

`ShapeWitness` and `ShapeEvent` are in `Correlation/ThirdMoment/Defs.lean`.
They retain the five asymmetric roles `(root,u)`, `(a,u)`, `(b,v)`, `(c,v)`,
and `(u,v)`, with pairwise-disjoint edge lists. Taking `u = v` includes stars.

`shapeWitness_or` constructs one of the three labelled binary tree shapes for
any four vertices in a common component of an arbitrary simple graph. First,
`exists_three_arms_general` applies the branch-point minimality argument to the
other three terminals, uses `Walk.bypass` to obtain `Nodup` supports, and shows
that these supports meet pairwise only at their centre. It then takes a
shortest walk from the root to the union of the three supports. Minimality
forces attachment only at the final vertex. Splitting the arm containing that
vertex into `takeUntil` and `dropUntil` gives the appropriate labelling.
Coinciding terminals, trivial attachments and degenerate stars are included.

Consequently the following declarations need no `harm` hypothesis:

* `TreeExpansion.Native.arm_decomposition_native`;
* `TreeExpansion.Native.four_point_native`;
* `TreeExpansion.Native.third_moment_native`, proving
  `E|K_0|³ ≤ 3 (E|K_0|)⁵` for Bernoulli percolation on a countable abelian
  group with its stated translation-invariant two-point function.

The alternative finite Steiner-tree/minimal-subgraph program was not used.
The shortest-root-attachment construction avoids its degree-suppression and
finite-tree classification obligations and works directly for infinite graphs.

## Loop-safe cutoff instantiation

`Correlation/CutoffThirdMoment.lean` exports
`TreeExpansion.Native.third_moment_cutoff` at the Definition I.1.5 law built
from `CutoffKernel.cutoffSymKernel`. Its only kernel premise is
`AntitoneOn K (Set.Ioi 0)`, already used for nonnegative loop-safe edge
probabilities. It assumes neither `K 0 = 0` nor finiteness of any moment.
Translation invariance of the cutoff law is proved from
`CutoffKernel.cutoffSymKernel_shift`; `edgeMeasure_eq_law` and the native
`conn` definition identify the product-law spellings.

The cutoff construction has also been fed into the existing covariance/error
consumer. `Hvol.cE1_le_three_mul_cube_div_cutoff` proves
`0 ≤ cE1 ≤ 3 (E|K|)³ / |B|` for every nonempty finite window `B`, assuming
`E|K| ≠ ∞`. Translation invariance and fivefold BK are discharged internally.
Thus only the finite-first-moment premise needed by the real quotient remains
in this corollary; it is not asserted for the critical law.

## What this does not complete

A single common-centre four-arm product would be wrong; all three labelled
binary trees and multiplicity three remain in the proof. The completed native
third-moment bound is only one ingredient of I.2.2 and I.4.9. It does not give
arbitrary higher-point tree-graph formulas, higher-k or mixed moments, finite
upstream susceptibility/sharpness, uniform finite-volume convergence,
finite-windowed triangle diagrams, or uncapped cutoff derivative regularity.
The source-ledger statuses therefore remain unchanged.

Compilation and axiom audits are local evidence on a specified revision, not
upstream CI or a statement-fidelity audit of the full paper.
