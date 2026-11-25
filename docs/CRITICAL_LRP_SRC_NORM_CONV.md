# Strict convolution in an arbitrary normalized source norm

Accepted from `smwtzmkep/m1` and integrated under `Analysis/LatticeConvolution/SrcNormConv`.  `conv_tsum_le_srcNorm` and `conv_tsum_le_srcDist` prove, for `a,b>0`, `a+b<d`, nonnegative logarithmic exponents and nonnegative coefficients, that a signed convolution dominated by the two corresponding `Wt` source-norm profiles is summable and has the uniform bound

`Cf*Cg*srcConvConst S a b ah bh * Wt (d-a-b) (ah+bh) (S.dist 0 x)`.

The `Defs` layer records the explicitly norm-dependent constants.  The main proof rederives the three geometric contributions in `S.ρ`, using the triangle inequality on `toVec`, the landed `NormShell` ball and pure-power tail estimates, and the correct `srcUpperConst` rescaling of the tail radius.  It proves summability of the nonnegative product majorant before applying it to the signed functions; it does not merely bind a `tsum` under an assumed summability premise.

`conv_tsum_le_srcNorm_via_sup` is a second route from the landed strict sup-norm theorem.  It transfers the two domination hypotheses with `Wt_srcNorm_le` and the result back with `Wt_linfNorm_le_srcNorm`; its constant differs from the direct region proof.  `conv_modelKernel_le_srcDist` supplies a non-vacuous model-kernel instance.

This is the strict regime only.  No marginal log loss, percolation-kernel instantiation, HD estimate, source Lemma I.4.3 completion, derivative or ODE result is claimed.  Fresh strict builds of all five source modules had only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports.
