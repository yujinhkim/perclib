# Marginal weighted lattice convolution

Accepted from `smwtzmkep/m2` and integrated under `Analysis/LatticeConvolution/MargConv`.  On `Fin d → ℤ` with the lattice sup norm, `conv_tsum_le_marg` and `conv_tsum_le_marg_explicit` prove the signed convolution bound when `a,b>0`, `a+b=d`, `ah,bh≥0`, and `1<ah+bh`.  Summability is a conclusion, not a premise.  The explicit target is

`Cf*Cg*margConst d a b ah bh * (log (2+‖x‖))^(1-ah-bh)`,

with `margConst` independent of `x` and the signed functions.  `margTarget` is the same statement as `Wt 0 (ah+bh-1)`.

The near-ball regions preserve the ball-shell and half-radius arguments from the strict assembly and pay an explicit factor for weakening the logarithm.  In the far region the smaller of `‖y‖` and `‖x-y‖` gives a `Wt d (ah+bh)` majorant, so the proved pure-log tail shell reduces the exponent `ah+bh` to `ah+bh-1`.  This is the required one-logarithm loss; the packet does not use the false unreduced-`c` pure-log tail.  `summable_convMajorant_zero_iff` also proves the sharp summability threshold for the product majorant at the origin, with divergence when `ah+bh≤1`.

The package itself does not transfer this marginal result to arbitrary source norms, identify a percolation Case 2 open triangle, or prove HD or Lemma I.4.3 as a whole.  The separate normalized-norm transfer is now available in `Analysis/LatticeConvolution/MargSrcNorm` (see `CRITICAL_LRP_MARGINAL_SRC_NORM.md`).  Fresh strict builds of all three modules in this base packet had only the three standard foundational axioms.
