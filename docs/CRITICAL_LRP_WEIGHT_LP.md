# Sharp `ℓ^p` membership of the power–log radial weight

`Analysis/LatticeConvolution/WeightLp.lean`, accepted from follow-up swarm `smwtxo95t` member `m3`, determines exactly when the campaign profile `Wt e c` is summable on the sup-norm lattice.

For `0 < d` and `0 ≤ c`, `summable_Wt_iff` proves
`Summable (Wt e c ‖·‖) ↔ d < e ∨ (e = d ∧ 1 < c)`.
One direction uses the existing sharp positive-exponent and pure-log tails; the other uses nonnegative lower layer bounds and divergence of the critical and subcritical series. `summable_abs_rpow_Wt_iff` transfers this to `p`-th powers, yielding the exact log-critical condition `p c > 1` at `p γ = d`.

The column section proves square-summability under upper kernel domination when `2(d−a) > d`, with a column-independent bound, and divergence under positive lower domination when `2(d−a) < d`. This gives the precise `ℓ²`/Hilbert–Schmidt threshold: at equality `2(d−a)=d`, one needs `2ac > 1`. It does not state a Hilbert–Schmidt operator norm, create a bounded or critical operator, or infer properties of a percolation two-point function. Upper domination alone is not used to claim divergence below the threshold.
