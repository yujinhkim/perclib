# Convolution profile tools (partial)

`Analysis/LatticeConvolution/Defs.lean` defines the logarithmic radial profile,
its specialization on `ℝ`, and a power/log-corrected weight.
`Analysis/LatticeConvolution.lean` proves monotonicity and doubling comparisons,
mean-value power gaps, finite layer-cake summation for arbitrary nonnegative
antitone weights, and an upper bound for one-step increments of that profile.

These are the ingredients needed for shell-sum estimates and then the A1/A2/A3
convolution argument at logarithmic corrections. They keep explicit counting
functions instead of substituting an unjustified global polynomial ball bound,
so only finite combinatorial input is needed at this layer.

The weighted shell estimates and the three-region assembly are **not** included.
This is not a proof of Lemma I.4.3, or of estimates (I.4.11)/(I.4.12), and is not
a statement about the two-point kernel or the open triangle. It is a saved
analytic base for follow-up work, not a claimed source-theorem closure.
