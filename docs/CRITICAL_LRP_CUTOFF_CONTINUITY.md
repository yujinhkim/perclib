# Continuity of the cutoff cluster mass

`Analysis/Cutoff/Continuity/Defs.lean` contains the mark-space escape and
box-change objects. `Analysis/Cutoff/Continuity.lean` proves radial profile
continuity, monotone convergence from below, and two-sided continuity from
finiteness at a strictly larger cutoff.

For `χ(r) = (M.cutMassAt r 0).toReal` at positive radius `r0`, left continuity
follows from monotone convergence, with the finite-mean input needed only for
`toReal`. Right continuity uses the common mark space: the finite box-change
probabilities tend to zero, and the escape term is controlled by finite mass at
the larger radius. No zero-percolation-probability inference is used.

`continuousAt_cutMassReal`, `continuousOn_cutMassReal`, and the corresponding
`cutMassReal_absolutelyContinuousOn_of_finite` consumer are therefore available
with an explicit finite larger-cutoff-mass premise. Small-radius finiteness is
established independently. Large-radius continuity still needs one of the
existing conditional finite-mean inputs.

This was recovered from the uncompleted long-running member `m4` of
`smwtrtcqs`, reviewed in full, and independently compiled and axiom-audited.
Its `ContinuousOn` premise is supplied here, not assumed. The actual off-corner
derivative bound remained necessary for the AC consumer and is not established
by this continuity proof.
