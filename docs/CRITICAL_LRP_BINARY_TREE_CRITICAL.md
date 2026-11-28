# The binary tree: exact critical intensity and infinite critical mean

`Models/BinaryTree/CriticalPoint` completes the existing binary-tree witness
without using it as a stand-in for the lattice model.

## Proved at the paper's measure interface

For the nonzero `binaryTreeKernel` on `List (Fin 2)`, in the same
`longRangeMeasure`, `criticalBeta`, cluster-volume and infinite-cluster
interfaces as the main project:

* `criticalBeta_binaryTreeKernel_eq_logTwo` identifies the critical intensity
  exactly as `log 2`.
* `lintegral_clusterVol_binaryTreeKernel_criticalBeta_eq_top` proves infinite
  critical mean at that intensity.
* `percolationFunction_binaryTreeKernel_criticalBeta_eq_zero` proves zero
  percolation probability at the same critical intensity, for every vertex.
* `lintegral_clusterVol_binaryTreeKernel_lt_top_iff_lt_criticalBeta` identifies
  finite mean exactly with intensity below the critical intensity.
* `criticalBetaSet_binaryTreeKernel_eq_Ioi` identifies the percolating set as
  the open interval above the critical intensity.

The missing structural step uses the proved preconnected support, together with
`law_cluster_infinite_pos_iff_of_preconnected`, to transfer vanishing percolation
from the root to every vertex. The zero–one law and nonemptiness of the
percolating set yield the lower bound `log 2 ≤ criticalBeta`; pre-existing tree
computations supply the other inequality and the mean formulas. This supplies
an attained non-degenerate model where zero percolation probability and an
infinite critical mean coexist.

## The three-way cutoff residual

`SourceModelData.cutMomentAt` generalizes the cutoff moment to arbitrary
intensity. At criticality it agrees definitionally with `cutMoment`.

The new `iSup_cutMomentAt_eq` and `exists_uniform_cutoff_bound_iff_uncut_ne_top`
show that a radius-uniform cutoff bound exists exactly when the uncut moment is
finite. `criticalDivergence_iff_no_uniform_cutoff` is the equivalent divergence
form. `subcriticalFinite_iff_forall_uniform_cutoff` permits the bound to depend
on the intensity, so subcritical finiteness is weaker than a uniform critical
bound. This separates those quantifiers rather than swapping them.

`criticalDivergence_of_cutMassAt_asymptotic` also verifies from the literal
first-moment limit alone that the uncut critical mean is infinite. Conversely,
the existing critical-divergence plus ODE package derives that limit. Chains
already using `hP` therefore need no extra divergence premise, but this is not
a derivation of `hP` for a canonical lattice.

## What the tail argument establishes and does not

`mul_measure_tail_le_lintegral` proves Markov's tail bound;
`tailProb_le_uncut_toReal_div` converts it when the mean is finite. Hence
`criticalVolumeTail_of_uncut_ne_top` gives the cited envelope from finite uncut
mean, optionally with constant equal to its real value. That is only a one-way
implication: it cannot make a divergent mean finite, and it does not replace
the cited transitive-graph tail theorem.

`exists_lintegral_clusterVol_law_eq_top_of_betaCrit_lt` gives only the existence
of a vertex with infinite mean for supercritical intensity; translation to the
root is explicitly left pending. No root-specific claim is made.

No power-law lattice sharpness, uncut critical volume tail, uniform differential
susceptibility comparison, or I.4.15/I.4.20 completion follows. All binary-tree
critical-point and residual exports rebuild with standard axioms.
