# Proposition I.4.20: proof status

The general scalar second-induction assembly is proved separately under its
stated decorrelation inputs. It is **not** an unconditional proof of the higher
moments of the canonical cutoff model.

## Case 1 (`d > 3α`)

`VolumeMoments/HigherMoments/I420Case1` proves the Case 1 decorrelation at the
actual independent-edge law `edgeMeasure π`, for countable vertex type `V`.
It uses the loop-independent cardinalities and real-valued expectations, not a
finite-vertex test graph.

- `mixedExcl π o a b B` is
  `E[|K_o|^a ∑_{y∈B} 1(y∉K_o) |K_y|^b]`;
  `prodFactor π o a b B = ∑_{y∈B} E|K_o|^a E|K_y|^b`;
  `windowMoment π o k B = E[|K_o|^k |K_o ∩ B|]`.
- `mixedExcl_le_prodFactor` comes from BK, and
  `prodFactor_le_mixedExcl_add_window` comes from Harris–FKG plus equality of
  the two clusters on a connection event. Neither discrepancy inequality is
  hypothesized.
- `discrepancy_toReal` uses finite product/window moments, so the real-valued
  subtraction does not exploit `ENNReal.toReal ⊤ = 0`.
- `case1_decorrelation` proves the required ratio with `a=ℓ+1`, `b=p−ℓ`,
  ℓ≤p, from explicit homogeneity, higher-moment finiteness, upper tree-graph
  order `(2p+3)α`, and lower product order `d+2pα`.
- `wMom_order_of_treegraph` and `prodFactor_order_of_asymptotics` separate the
  exponent bookkeeping. In particular the first's
  `E|K|^(p+2)` tree-graph assumption and the sources' regular-variation order
  assumptions are retained, not manufactured.

The equality case at zero opening probabilities checks the exact exclusion and
window normalizations. It is not a lattice sharpness computation.

## What is not closed

- Case 2 and Case 3 require different decorrelation routes.
- The ordinary general-index tree-graph bound must still be transported to
  the canonical law at the desired order, and first/second moment asymptotics
  must be derived from the source model.
- The second induction remains a correctly conditional consequence of the
  paper's decorrelation estimates, not a substitute for their three probabilistic cases.

Independent strict builds and axiom audits show only standard axioms for the
Case 1 results.
