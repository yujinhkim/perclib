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

## Case 2 (`d = 3α`, hydrodynamic condition)

`VolumeMoments/HigherMoments/I420Case2` proves the cutoff-model
Cauchy–Schwarz comparison. `jointMoment_le_cs` uses ENNReal Hölder and
preserves infinite moments. `jointMoment_le_of_bounds` inserts (I.4.19) at
order `2p+2` and universal tightness `E[|K∩B|²] ≤ M_r E|K|`. The resulting
factor is `√(C (M₂/M₁)^(2p+1) M₁) √(M_r M₁)`.

`case2_decorrelation_error` and `jointUpper_isLittleO` compare that factor to
`|B_r| (M₂/M₁)^(p−1) M₁²` at `d = 3α`. The account uses both sides of
`E|K| ≍ r^α`, `M₂/M₁ ≤ γ (E|K|)²`, `M_r = o(r^((d+α)/2))`, and the actual
Lemma I.4.6 ball-volume asymptotic. They remain explicit inputs except the
last two, whose definition of `Hydro` and `M.ball_count` are instantiated.

The earlier BK/FKG Case 1 discrepancy supplies the identification of the
mixed-window moment with the excluded-moment discrepancy needed in the final
application, but doesn't supply (I.4.19) at order `2p+2`, universal-tightness,
or moment–asymptotic inputs. This is therefore the Case 2 error estimate, not
an unconditional second-induction or sharpness result.

## What is not closed

- Case 3 requires the triangle-condition decorrelation route.
- The ordinary general-index tree-graph bound must still be transported to
  the canonical law at the desired order, and first/second moment asymptotics
  must be derived from the source model.
- The second induction remains a correctly conditional consequence of the
  paper's decorrelation estimates, not a substitute for their three probabilistic cases.

Independent strict builds and axiom audits show only standard axioms for the
Case 1 results.
