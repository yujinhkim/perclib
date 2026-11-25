# A binary-tree witness for finite subcritical susceptibility

Source model: rooted nearest-neighbour bond percolation on the binary tree of
words in `Fin 2`, using the existing `PercLib.Models` exact computations.

`Models/BinaryTree/Subcritical/Basic.lean` packages this model in the paper's
own `longRangeMeasure J hJ β` interface. It is a supporting witness, not a new
proof of sharpness for the long-range lattice.

## Exact statements

The kernel `binaryTreeKernel` is one on parent/child edges and zero elsewhere,
including the diagonal. Its nonzero edge has open probability
`p(β) = 1 - exp(-β)`. Hence it is not a degenerate universal-open model.

The root first moment is

```text
(1 - 2 p(β))⁻¹, finite exactly when β < log 2,
and ⊤ when β ≥ log 2.
```

For every parameter strictly larger than `log 2`, root percolation has positive
probability, and hence the code's `criticalBeta` is at most `log 2`. In
particular, every `β < criticalBeta binaryTreeKernel _` has finite mean.

`percolationFunction_eq_zero_of_lt_criticalBeta` records that below the code's
percolation threshold the root has zero probability of an infinite cluster.
At `β = log 2`, however, root percolation remains zero while expected volume is
`⊤`. The declaration `not_forall_theta_zero_imp_lintegral_lt_top` formulates
precisely that the inference `θ = 0 ⇒ finite mean` is false as a general
implication in the interface.

## What this does not identify

Only `criticalBeta binaryTreeKernel _ ≤ logTwo` is proved, not equality. The
missing structural step for equality would identify every infinite component
with a rooted infinite forward subtree, not merely use the root calculation.

This model also does not establish

```text
β < criticalBeta (lrKernel d α) _ ⇒ E_β|K| < ⊤
```

for the source power-law lattice kernel. The sharpness step there requires a
uniform bound for cutoff first moments, which the current library does not yet
supply. `CutoffLimit.le_of_forall_lintegral_clusterVol_cutoff_le` transfers
such a uniform bound to the uncut mean, but does not construct it.

In particular, starting from `infiniteClusterProb = 0` cannot by itself close
the lattice sharpness gap. The tree example above is a kernel-level counter-
example to that shortcut.

## General percolation/moment consequences

The module also proves that an infinite percolation event forces infinite mean
at some vertex, and that a finite first moment at **every** vertex excludes an
infinite cluster almost surely. The quantifier over all vertices is essential;
a finite root expectation alone does not preclude unbounded expectation at
some other root.

## Verification

The module passes focused `lake build --wfail` compilation and all 37 focused
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. These are
local checks on the integrated candidate, not upstream CI or a claim of source
lattice sharpness.
