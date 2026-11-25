# Marginal convolution for arbitrary normalized source norms

Accepted from `smwu10gjo/m1` and integrated in `Analysis/LatticeConvolution/MargSrcNorm/{Defs,Main}.lean`.

For `a,b>0`, `a+b=d`, `ah,bh≥0`, `ah+bh>1`, and nonnegative coefficients, `conv_tsum_le_marg_srcNorm` proves summability of a signed convolution dominated by the corresponding source-norm weights, together with

`Cf*Cg*(srcMargConst S a b ah bh * srcMargTarget S ah bh x)`.

Here `srcMargTarget = Wt 0 (ah+bh-1) (S.ρ (toVec x))`, so `conv_tsum_le_marg_srcNorm_log` gives the explicit logarithmic profile `(log (2+S.ρ (toVec x)))^(1-ah-bh)`.  `one_le_of_add_eq` derives positive dimension rather than taking it as an extra hypothesis.

The hypothesis side uses `Wt_srcNorm_le` with `d-a,d-b>0`.  The target conversion uses `Wt_linfNorm_le_srcNorm` at power exponent zero, leaving `srcLogConstUpper^(ah+bh-1)`.  `srcMargConst` combines these transfers with the explicit frozen sup-norm `margConst`; it is nonnegative under the same hypotheses.  The proofs establish majorant-level summability and bounds before treating general signed functions.  `conv_tsum_le_marg_srcDist` gives the `S.dist 0` formulation, and model-kernel and source-outer-factor variants are included.

The exponent is the required `ah+bh-1`, not the false unreduced exponent.  All 28 definition/theorem axiom reports contained only the three standard axioms in an independent fresh build of the actual files, which the agent had placed under the worktree-local `.ultramath` directory.  This package does not instantiate a percolation open triangle or prove Lemma I.4.3, HD or a moment identity.