# Weighted lattice tail shells

`Analysis/LatticeConvolution/TailShell/Defs.lean` stores the explicit constants. `Analysis/LatticeConvolution/TailShell.lean`, accepted from swarm `smwtvrwnn` member `m5`, proves finite-sum weighted-tail bounds on `Fin d → ℤ` with the sup norm `linfNorm`.

For `d ≥ 1`, `γ > 0`, `c ≥ 0`, and `S ≥ 0`, `sum_Wt_tail_le` bounds every finite weighted sum over points satisfying `S < ‖y‖∞` by `tailShellConst d γ * Wt γ c S`. Equivalently, the weight `(1 + ‖y‖)^(-(d+γ)) (log(2 + ‖y‖))^(-c)` is bounded by an explicit `S`-independent multiple of `(1 + S)^(-γ) (log(2 + S))^(-c)`. `tsum_Wt_tail_le` gives the corresponding bound for the whole far-region subtype; its proof constructs summability internally using the uniform finite-partial-sum bound.

For the marginal case `γ = 0`, `c > 1`, `sum_Wt_tail_le_pureLog` gives a finite-sum bound with `Wt 0 (c - 1) S`, hence logarithmic exponent `c - 1`, not `c`. This exponent loss is mathematically necessary: the pure-log tail has the same marginal logarithmic behavior as the source's `a + b = d` convolution regime. The package does not assert the false unreduced-log bound and currently gives this marginal variant in finite-sum form only.

The proof uses sharp box-layer cardinalities and telescoping power/logarithmic gaps. It is a raw-sup-norm analytic lattice estimate, not an arbitrary `SourceNormData` theorem. It contains no two-point-kernel, cutoff-law, triangle, or moment input and does not prove the A1/A2 ball shells, the three-region convolution assembly, (I.4.12), or Lemma I.4.3.
