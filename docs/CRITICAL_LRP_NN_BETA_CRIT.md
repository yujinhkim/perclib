# Nearest-neighbour comparison and critical positivity

`Orchestration/ModelWitness/NNComparison/{Defs,KernelBridge,BetaCritPos}.lean`
separates the large-temperature fact that `β_c` is nonzero from the unresolved
supercriticality fact, rather than claiming `0 < β_c < ∞` outright.

For the literal `sourceModelWitness`, the kernel is exactly the paper's `lrKernel` times
`c = 2^{-d-α}/(d+α)`. Law rescaling carries through multiplication by `c`. The conditional
power-law row mass appears explicitly at non-loop nearest-neighbour edges, whose
normalized radius is `2`.

The high-temperature conclusion is unconditional:
there is a positive explicit parameter with zero infinite-cluster probability.
Consequently `0 < β_c` holds if `criticalBetaSet` is nonempty; in the NNReal infimum
encoding, positivity is actually **equivalent** to nonemptiness. Membership is
`infiniteClusterProb = 1`; the existing zero-one theorem converts this to strictly
positive percolation probability. The zero-one law is an already-proved dependency,
not a new axiom.

The nearest-neighbour inequality goes the useful direction for finite criticality:
a unit nearest-neighbour kernel is bounded by the long-range kernel, so NN
supercriticality forces percolation for the long-range law. It cannot be reversed into
non-percolation from NN critical positivity. The named input

```lean
NNSupercritical d := ∃ γ, infiniteClusterProb (nnKernel d) (nnKernel_nonneg d) γ = 1
```

is a standard nearest-neighbour **supercritical** theorem for `d ≥ 2`, but it is not
proved in the current library. Conditional on this input and this input alone, the
module proves `0 < β_c`, nonzero `β_c`, and a nonempty percolating set together with
positivity (`0 < β_c < ∞` in the NNReal formulation). No nearest-neighbour supercritical
parameter is supplied by the module.

The result also identifies the paper's original `lrKernel` critical set with the
witness's, via the exact inverse rescaling `c⁻¹ γ`. This is a reduction of the external
nearest-neighbour input, not a proof that subcritical sharpness or any main theorem of
the paper has been established.
