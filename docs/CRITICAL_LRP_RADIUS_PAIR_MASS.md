# Pair-mass and excluded-mass radius continuity

Accepted from Ultramath `smwv0yn27`, member `m1`, and split into production
`Analysis/Cutoff/OffCorner/PairMassRegularity/{Defs,Main}.lean`.

For `r₀ > 0` with no lattice point on the sphere `{ρ = r₀}`, `continuousAt_pairMassReal` proves
continuity of `(pairMass r).toReal` from `r₀ < r₁` and `cutMoment 2 r₁ ≠ ⊤`. The pair integrand
`|K₀| ∑_{y ∈ B_r} |K_y|` is monotone in radius. The left limit is obtained by monotone
convergence on the mark space, and identifies the strict-window pair mass. At an off-sphere
radius the strict and closed windows coincide.

The right limit uses newly proved general-base escape control. `markEscapeAt`, `markEscapeUnion`,
`cluster_subset_of_eq_on_box_gen`, and `clusterVol_eq_of_notMem` apply to arbitrary roots. On a
right neighbourhood the window is constant, so the pair integrand is fixed off a finite box-change
event and a union of escape events for the required finite set of roots. The finite pair mass at
the larger radius dominates both error integrals and lets them vanish separately. This is the
actual infinite-volume law, not a finite-box substitute.

`E1Sign.pairMass_eq` then yields `exclScalar = pairMassReal - connMassReal` wherever the required
finiteness is available. With `cutMoment 2 r₁ ≠ ⊤` and `cutMoment 3 r₁ ≠ ⊤` at some `r₁ > r₀`,
`continuousAt_exclScalar` proves continuity of the excluded-mass scalar. The third moment is
needed by the previously landed `continuousAt_connMassReal`; it is not silently inferred from the
second. The equivalence between pair-mass and excluded-scalar continuity is also proved, as are
left-limit versions with their explicit moment and no-sphere hypotheses. These are **not**
unconditional left-continuity statements.

This supplies excluded-mass regularity where its moment inputs are known, but does not produce
large-radius second/third moments, `hcontinf`, normalized-pivotal-mass continuity, derivative
continuity, or a complete ODE. It also bypasses the optional uniform-cylinder reduction: that
uniform approximation itself is still open, rather than being claimed a consequence of this
independent one-sided assembly.

All 48 declaration names were preserved from the reviewed packet; its five new definitions were
placed in `Defs.lean` before independent definition/proof builds. Every audited declaration uses
only the standard axioms.

A second local assembly, `OffCorner/RadiusExcludedMass.lean`, proves that the off-corner condition
satisfies the required no-sphere hypothesis, and supplies `hGcont_of_excludedMoments` for a whole
off-corner window. It uses continuity of `deriv M.K` and explicit finite second and third moments
at the endpoint. The envelope and tail endpoint variants `_of_moments` consume that derivation;
`hcontinf` and derivative continuity remain inputs. All four assembly declarations were rebuilt
with the strict flags and use only the standard axioms.
