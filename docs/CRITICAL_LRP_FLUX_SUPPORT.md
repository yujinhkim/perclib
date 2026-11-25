# Exact support of the cutoff flux

`Analysis/Cutoff/FluxSupport/Defs.lean` defines `inSupport` as the non-loop edges of length at most `r`. `Analysis/Cutoff/FluxSupport.lean`, accepted from swarm `smwtvrwnn` member `m3` under d10, proves loop invisibility and exact zero-weight support filtering for finite edge-window sums.

`openGraph_insert_loop` and `openGraph_sdiff_loop` follow because `fromEdgeSet` discards loops; therefore connectivity, clusters, truncated cluster volumes and every truncated-moment pivotal flux are unchanged by inserting or deleting a loop. `pivotalFlux_sMomentTrunc_loop` gives zero pivotal flux for every law, not just the cut law. Independently of invisibility, `cutEdgeDeriv_loop` makes the weight itself zero on loops.

`cutEdgeDeriv_eq_zero_of_lt_dist` gives zero weight beyond the interaction range, and `cutEdgeDeriv_eq_zero_of_not_support` combines that with the loop case. `sum_filter_inSupport_eq` proves the general finite-edge sum filter identity, and `sum_cutEdgeDeriv_mul_pivotalFlux_support` instantiates it precisely for `cutEdgeDeriv · pivotalFlux`.

This completes only the support calculus needed by a later fibre reindexing argument. It does not perform the fibre reindexing, identify the whole standardized excluded sum with `exclMass`, establish a moment or majorant, or prove a model-level Russo derivative.
