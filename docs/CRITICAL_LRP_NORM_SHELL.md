# Shell estimates at arbitrary normalized source norms

`Analysis/LatticeConvolution/NormShell/Defs.lean` supplies explicit norm-dependent lower, upper, counting, logarithmic and tail constants. `Analysis/LatticeConvolution/NormShell.lean`, accepted from follow-up swarm `smwtxo95t` member `m5`, transfers the earlier sup-norm ball and tail shells to an arbitrary `SourceNormData` radius `ρ (toVec y)`, equivalently `dist 0 y`.

The lower comparison `srcLowerUnit * ‖v‖ ≤ ρ v` comes from finite-dimensional norm equivalence, with `srcLowerUnit > 0` proved. The upper comparison is proved directly by expansion in the standard basis and sublinearity; its constant is independent of every radius. `srcLowerConst` is an `sSup` and is not claimed to have a simpler closed-form value.

The package proves the source-radius ball-counting estimate, transferred finite ball-shell and A1/A2-contribution bounds, and both finite and unrestricted-tail estimates for `γ > 0`. It also transfers the pure-log `c > 1` tail with exponent `c - 1`, not the false unreduced exponent `c`. The outer-radius rescaling has separate norm-dependent power and logarithmic constants; all are independent of the outer radius itself. Strict and closed ball conventions are preserved.

This is geometric and analytic infrastructure only. It does not instantiate a percolation kernel or cutoff moment and does not assert the already separate sup-norm convolution assembly at arbitrary norms. That transfer can be developed by repeating the generic region proof with these comparisons, or by reusing the frozen generic region bounds added by this package. No criticality, Kozma identity, HD theorem, or cutE1 integrability is claimed.
