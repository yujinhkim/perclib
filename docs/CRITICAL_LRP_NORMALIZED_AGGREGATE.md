# Normalized pivotal mass: dominated edge-series continuity

Accepted from Ultramath `smwv2c2lw`, member `m3`. Production modules:
`Analysis/Cutoff/OffCorner/NormalizedAggregate/{Defs,Main,Finiteness}.lean`.

`edgeTouchMass` assigns to an edge the sum of its two endpoint connection probabilities.
`pivotMajorant r₀ R` multiplies that mass at `R` by the normalized cutoff factor frozen at `r₀`.
The singleton pivotal difference is nonnegative and dominated by the touching event, and touching
an edge means at least one endpoint belongs to the cluster of the origin. No two-arm or BK step
is used.

At each vertex, the activated normalized edge factors are at most one and at most the number of
points in the cutoff lattice ball weigh nonzero. Exchanging the edge/vertex sums therefore gives
summability of the majorant from a finite first cutoff moment alone, with a bound leading to
`2 #ball(r₀) · ∑_x P_R(0 ↔ x)`. No unjustified second-moment inference is involved. The support
uses only finitely many distance scales, though it is not a finite set of actual edges.

At a positive off-corner `r₀`, `cutPivotFactor r e = cutPivotFactor r₀ e` on a whole corner-free
neighbourhood. For `R > r₀` with `cutMoment 1 R ≠ ⊤`, dominated convergence then proves
`continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux` **provided the fixed-edge pivotal
flux is continuous at `r₀` for every activated edge**. This is the infinite real edge series, not
its truncated version. There are also variants from a finite second cutoff moment, per-vertex
continuity (`hcontinf`) from derivative continuity and that same fixed-edge input, and an
envelope-endpoint wrapper retaining its other orthogonal hypotheses.

`Finiteness.lean` separately proves absolute summability of the defining flux series from finite
first moment, of `normalizedPivotMass` when additionally `β_c ≠ 0` and `deriv M.K r ≠ 0`, using
the exact kernel-factor division. Its stronger hypotheses must not be read into the first-moment
majorant result above.

Full two-sided fixed-edge pivotal continuity is **not proved here**. The separate
`RadiusHorizon` packet does prove it from the left, and `NormalizedAggregate/Left` uses that
with this same dominating majorant to prove left continuity of the full weighted normalized mass.
It also proves singleton-flux left continuity under continuity of `deriv K`. This does not
supply right-hand continuity, full `hcontinf`, `hGcont`, large-radius moments, or the ODE.
The definitions were built before the proofs, then all declarations were independently rebuilt
with strict flags and found to use only `propext`, `Classical.choice`, and `Quot.sound`.

## Fixed-edge continuity supplied by two-point localization

The later `TwoPoint/PivotalFlux` proof establishes the fixed-edge hypothesis directly from
finite first cutoff mass at a strictly larger radius. Its finite-box variation/escape argument
also treats forced-open and forced-closed events, with no monotonicity assumption on their
difference. `TwoPoint/Capstone` composes it with the aggregate reduction to establish both
first- and second-cutoff-moment forms of normalized-pivotal continuity at off-corner radii.
This complements `Left` for left-only one-sided structure; it does not construct a finite first
cutoff moment at arbitrary large radius or derive a complete ODE.
