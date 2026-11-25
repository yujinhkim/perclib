# Radius-independent envelope for off-corner singleton flux

Recovered from the abandoned `smwuges40/m1` artifact in
`Analysis/Cutoff/OffCorner/RadiusEnvelope.lean`.

`m1_real_touchSet_mono_radius` shows that the touching probability at an edge is nondecreasing in
the cutoff radius, complementing the monotone cut probability. `m1_abs_cutEdgeDeriv_le_scale`
compares a derivative weight on `[a', b']` to its value at an **interior** radius `ρ ≥ b'`: if
`-K' ≤ C` on the window and `K'(ρ) < 0`, put

`Λ = (C / (-K'(ρ))) * exp (β_c (K a' - K ρ))`.

The support and exponential factors are handled separately; no false comparison simply taking
`ρ = b'` is asserted.

`m1_exists_uniform_fluxEnvelope` gives a summable function of the edge, namely
`Λ * |cutEdgeDeriv ρ e| * (2 * P_{b'}(e ∈ touchSet ω 0))`, which bounds every
`|cutEdgeDeriv r e * singletonPivotalFlux(r,y,e)|` for `r ∈ [a',b']`. Its summability uses the
new unstandardized hdom at `ρ`, from `cutMoment 1 ρ ≠ ⊤`.
`m1_abs_infFlux_le_envSum` gives the same finite summable majorant for the whole infinite
singleton flux at each interval radius. Arithmetic signs, absolute values, and endpoint
inclusions are handled explicitly.

`m1_stronglyMeasurableAtFilter_infFlux_of_window` upgrades window-flux measurability to infinite
measurability-at-filter via `tendsto_windowFlux`. This avoids relying on continuity of window
fluxes but does not prove per-`y` continuity `hcontinf`, summed continuity `hGcont`, interval
integrability, or an ODE.

The exact remaining hypotheses are `0 < a'`, `a' ≤ b' ≤ ρ`, a local bound on `-K'`, negative
`K'(ρ)`, and a finite first cutoff moment at `ρ`. The last condition is not instantiated from
zero percolation or the tail derivative bound here, and no moment is claimed to exist at an
arbitrary radius.

All nine main declarations/audit summaries depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
