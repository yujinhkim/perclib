# Exact left limit of excluded mass at attained radii

`Analysis/Cutoff/OffCorner/AttainedExcludedLeft.lean` gives the genuine left limit
of excluded mass between the closed and the strict moving windows.

For `r₀ > 0`, with finite second and third cutoff moments at that radius:

```lean
Tendsto M.exclScalar (𝓝[<] r₀)
  (𝓝 ((M.pairMassLt r₀).toReal - (M.connMassLt r₀).toReal))
```

The two pieces come from different existing limits:

- the pair mass tends to its strict-window `pairMassLt`, which uses the finite set and
  closed law at the endpoint rather than pretending the closed-window pair mass is the
  limit;
- the connected mass tends to `connMassLt`, whose exact strict-ball decomposition is
  `connMass = connMassLt + sphereMass`.

The new `pairMassLt_le_pairMass` comparison supplies the pair moment finiteness needed
for this limit from the closed second moment. The closed-window excluded identity
`exclScalar = pairMass.toReal − connMass.toReal` identifies the corresponding target on
the left. No empty-sphere condition or off-corner hypothesis is required, and there is
no new standalone excluded-mass definition replacing the actual moving-window object.

That standalone limit theorem establishes the left limit at attained as well as
non-attained radii. It does not itself prove a left or right derivative at attained
radii, show that the strict and closed values coincide there, or complete Lemma I.4.1. The finite second/third cutoff moment
inputs remain explicit; alternative sources of a finite first moment can supply them
through the native moment bridges.

The exact strict-window realization, its right-hand companion, shell positivity, and the
assembled one-sided derivative consequences are recorded in
`docs/CRITICAL_LRP_EXCLUDED_MASS_CORNERS.md`.
