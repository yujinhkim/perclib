# Weighted lattice ball-shell bounds

`Analysis/LatticeConvolution/BallShell/Defs.lean` defines the power–log profiles `Sfun`, `Tfun` and the explicit threshold and constant used by the core estimate. `Analysis/LatticeConvolution/BallShell.lean`, accepted from swarm `smwtvrwnn` member `m1`, proves the weighted ball-shell sums.

`core_sum_bound` gives the sharp discrete comparison `∑_{n<M} (1+n)^(a-1) (log(2+n))^(-c) ≤ coreConst a c * (1+M)^a (log(2+M))^(-c)` for `a > 0` and `c ≥ 0`. The thresholded one-step argument handles the nonmonotone profile and the finite initial segment explicitly; `c = 0` is included.

`ball_shell_bound` applies this to a finite set with a nonnegative radius and an explicit ball-counting bound, giving `∑ Wt(d-a) c ρy ≤ K(1+S)^a (log(2+S))^(-c)` for `0 < a < d`, `c ≥ 0`, and `S ≥ 0`, with `K` independent of `S`. `ball_shell_bound_latticeInt` discharges the counting bound for the usual norm on `Fin D → ℤ`.

`A1_contribution_bound` multiplies the general ball estimate by the source's outer power/log factor and obtains the normalized A1/A2 contribution exponent, with A2 obtained by interchanging parameters. This is an analytic region-contribution bound, not the geometric A1/A2/A3 decomposition or a full convolution theorem. The tail region is supplied separately by `Analysis/LatticeConvolution/TailShell.lean`; the three-region assembly and Lemma I.4.3 remain open. No percolation measure, cutoff, two-point kernel, or triangle estimate is used.
