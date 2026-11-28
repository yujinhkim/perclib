# Parameter and hypothesis audit for HD and HD+

`Orchestration.HDRegime` is a parameter-level audit, not a proof that a critical
model satisfies a high-dimensional estimate. It was independently reviewed and
rebuilt at `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`.

## Boundary statements

The `defs` exports name the source's two-point power and logarithmic bounds and
then prove:

* on `d = 3α`, the first HD alternative is false; on `d = 3α < 6`, `HDplus` is
  equivalent to `Hydro`;
* at `d = 6`, `α = 2`, `HDplus` reduces exactly to the source's log-corrected
  two-point upper bound;
* `HDplus` implies `3α < d`, `3α = d`, or `2 < α` with `d > 6`; in particular the
  excluded long-range-low-dimensional and short-range-low-dimensional regions
  are made explicit;
* at `d = 6` the alternatives force `α ≤ 2`; at dimensions at most `5`, only the
  first and hydrodynamic alternatives are available; and alternatives 1 and 2
  can overlap;
* the marginal hydro exponent is `2α`, while `r^{2α} log r` is not `o(r^{2α})`.

The proof that `log r` does not vanish is a regime obstruction, not a proof of
or against Hydro. At the marginal curve the theorem's additional hydrodynamic
input cannot be inferred just from the Gaussian prefactor's logarithm.

## RV index algebra and source-model witnesses

`zeta_eta_regularlyVarying` derives indices `2α` and `−α` for the source's `ζ`
and `η` ratios from two supplied regular-variation inputs of indices `α` and
`3α`. No dimension identity or Hydro is needed for this algebra. The input
propositions I.4.2 and I.4.15 are not proved by this theorem.

Explicit `Witness.sourceModelWitness` constructions establish non-emptiness of
the source-model carriers at the parameter loci and provide alternative-1 HD
witnesses. They are not instantiations of the critical log-corrected two-point
estimate at `(6,2)`. In particular `exists_six_two` supplies only a model with
`d=6` and `α=2`, not a model satisfying HDplus at that point.

At zero critical intensity, the log-corrected estimate can hold for trivial
Dirac-law reasons if every nonzero lattice distance is at least `1`. If a
nonzero distance is below `1`, positivity of the probabilities contradicts its
negative logarithmic factor. This caveat is about the totalized Lean formula;
it neither supplies nor refutes the intended nontrivial critical estimate.

No critical two-point estimate, `Hydro`, critical volume tail, moment
asymptotic, or `HasCovBound` is proved in this package. All exports report only
`propext`, `Classical.choice` and `Quot.sound` in their focused axiom audit.
