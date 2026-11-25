# Cylinder continuity and the frozen-window approximation gap

Accepted from Ultramath `smwv0yn27`, member `m2`. Production module:
`Analysis/Cutoff/OffCorner/RadiusFrozenCylinder.lean`.

Finite-cylinder expectations are continuous under a continuously varying family of independent
Bernoulli edge probabilities. The proof reduces to finite products with
`configurationLaw`/`expectation`, so it applies to the exact infinite product law restricted to
each finite edge set. `continuousAt_integral_cutLaw_cylinder` and its `ENNReal.ofReal`/`toReal`
variant specialize this to every positive cutoff radius. `continuousAt_integral_cutFun_cutLaw`
wraps the same result in the Russo tower's window vocabulary. Finiteness for `toReal` comes from
the finite-range cylinder observable, not a junk conversion.

`frozenWindow_integrand_le_pairMass` and `frozenWindow_lintegral_ne_top` prove that the actual
infinite-volume frozen-window integrand has finite moment on a frozen window whenever the second
cutoff moment is finite. `tendsto_frozenWindow_escape` proves the vanishing of its escape-tail
moment at one fixed radius, using decreasing events and finite moment domination.

`continuousAt_of_uniform_approx` and `continuousAt_toReal_lintegral_of_cylinder_approx` transfer
uniform cylinder approximation to continuity of a real-valued infinite-volume moment. The
excluded-scalar, `hGcont`, and endpoint-derivative wrappers instantiate this with the exact frozen
window. Their `hcyl` hypotheses still require one finite cylinder observable to approximate the
moment within `ε` **simultaneously for all radii in a neighbourhood**. This uniform-in-radius
estimate is not proved. In particular, excluded-mass continuity, frozen-window continuity,
`hGcont`, `hcontinf`, and the full ODE remain open; the fixed-radius escape-tail result is not a
replacement for that missing uniformity.

All 15 proof declarations were independently rebuilt with strict flags and use only
`propext`, `Classical.choice`, and `Quot.sound`.
