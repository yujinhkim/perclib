# Generic convolution assembly (`a + b < d`)

`Analysis/LatticeConvolution/ConvAssembly/`, accepted from follow-up swarm `smwtxo95t` member `m4`, assembles the previously proved ball and tail shells into the full generic discrete convolution estimate in the strictly subcritical exponential regime.

For `a, b > 0`, `a + b < d`, nonnegative logarithmic exponents, and real `f,g` dominated pointwise by constants times `Wt(d-a,â)` and `Wt(d-b,b̂)`, `conv_tsum_le` proves that `y ↦ f y * g (x-y)` is summable and that its absolute `tsum` is bounded by `Cf * Cg * convConst * Wt(d-a-b, â+b̂) ‖x‖`. The explicit `convConst` is independent of `x`. The majorant bound is therefore both an infinite-series summability theorem and an estimate of the signed convolution, not merely a finite-region calculation.

The proof splits into a half-ball around the origin, a half-ball around `x`, and two complementary far tails. It uses the reverse triangle inequality, profile freezing, the centred ball estimate, and the existing sharp shell sums. `PaperForm` supplies the monomial-normalized and pure-power forms as well as the outer-factor comparison.

This completes the analytic generic-convolution step for the strict regime of (I.4.12) on the sup-norm lattice. It does not handle `a+b=d`, transfer to an arbitrary normalized `SourceNormData` norm, instantiate the percolation two-point kernel, or prove Lemma I.4.3 in full. These are separate remaining steps.
