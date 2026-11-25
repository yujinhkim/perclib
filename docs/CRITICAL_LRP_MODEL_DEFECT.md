# Model-level cutoff defect sign

`Analysis/Cutoff/Defect/Defs.lean` defines the finite ball, pair moment,
connected moment, and excluded moment at the actual normalized source cutoff
law. `Analysis/Cutoff/Defect.lean` proves cluster-volume expansions and the
weighted two-cluster inequalities needed to bound them.

The main result is `E1Sign.cE1_mem_Icc`: for nonnegative `r` and finite second
cutoff moment, the source defect lies between zero and the normalized connected
window moment. The lower half does not need nonnegative `r`, because the sign
argument does not divide by a proved positive window denominator. The
`I411.exclMoment` used here is definitionally the excluded moment it bounds;
there is no substitution of `disjSet` for `apartSet` in its comparison chain.

`E1Sign.chiLower_E1_nonneg` and
`E1Sign.eventually_cutMassAt_rpow_le_of_model_defect` expose the exact lower
comparison consumer at the same model's defect. They retain the model ODE,
positivity, divergence, normalization-error limit, and second-moment finiteness
as separate premises.

The second-moment premise is not inferred from zero percolation probability or
finite boxes. `Analysis/Cutoff/RowMassSmall.lean` independently supplies it on
an unconditional small-radius interval. Large radii still need the reduced
subcritical moment, a priori upper-bound transfer, or a lower comparison. This
package does not prove that model ODE, absolute continuity, or Case 3.
