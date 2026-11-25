# Strict cutoff domination at an arbitrary source norm

`MomentMonotonicity/StrictCutoffEpsilon.lean` proves Definition I.1.5's strict
domination for the genuine `SourceModelData`, with any admissible normalized
source norm. It resolves the audit's warning that the historical `J(0⁺)`
coefficient is degenerate for the normalized power law.

`SourceNormData.exists_attained_lattice_min` chooses a nonzero integer vector
and minimizes its length over the finite set of nonzero lattice vectors no
farther away. Finiteness comes from the actual cell-packing proof. Every other
nonzero vector is at least as far away, and the minimum is attained and positive.

`SourceModelData.exists_deriv_bounds` uses the normalization error to bound
`|K'|` between comparable negative powers on a tail. Integrability and
`K_eq_integral` then prove `K r > 0` at every positive radius. If
`t₀` is a positive lower bound on lattice distances, the coefficient used is

```text
ε(r) = min (1/2) (K r / (2 K t₀)).
```

Since `K r` and `K t₀` are positive, `0 < ε(r) < 1`. For lattice distance
`s ≤ r`, we have `K s ≤ K t₀` and hence `ε(r) K s ≤ K r/2 ≤ K r`; for `s > r`,
the cutoff vanishes. Therefore `cutRadialSym_le_scaled` and
`SourceModelData.cutKernel_le_scaled` prove `J_r ≤ (1−ε(r))J` on every pair,
including loops.  Small cutoffs are handled directly: there is no nonzero
vector of length at most `r` if `r < t₀`.

`SourceModelData.exists_epsilon_domination_attained` exposes the attained
minimum formulation; `cutLaw_le_reduced` gives
`P_{βc,r} ⪯ P_{(1−ε)βc}` on increasing measurable events, and
`cutLaw_infiniteClusterProb_eq_zero` gives the printed no-infinite-cluster
conclusion with the required `0 < β_c` premise. Flat-normalized examples and
the explicit `ε = 1/16` coefficient are included.

This file proves strict domination only. It does not prove finite cluster
moments, which still needs a subcritical first-moment estimate and a
higher-order moment-comparison input.

## Reduced-parameter moment transfer

`MomentMonotonicity/ReducedMomentTransfer.lean` composes this domination with
monotone coupling at the actual `SourceModelData.cutLaw`. For every `r > 0`
and every natural order `p`, it bounds the cutoff `p`-th moment by the uncut
`p`-th moment at `β_C c`, with `0 < c < 1`. For each `R > 0`, one coefficient
works throughout `(0,R]`, so one stipulated finite reduced moment controls the
whole window.

`SourceModelData.cutMassAt_ne_top_of_subcritical` derives finiteness of every
positive-radius cutoff first moment from `0 < β_C` and finite uncut first
moments at every strictly subcritical parameter. With critical uncut-mean
divergence as a separate input,
`tendsto_cutMassAt_toReal_atTop_of_subcritical` gives real cutoff-mass
divergence. `not_exists_uniform_strict_coefficient` proves that a single
strict coefficient cannot cover all positive radii.

The uncut subcritical moment hypothesis remains explicit: this is a transfer,
not sharpness or a proof that zero percolation probability gives finite mean.
The higher-order theorem consumes finiteness at the same order `p`; it does not
reduce higher moments to the first moment.

## Unconditional finite moments at small cutoffs

`Analysis/Cutoff/RowMassSmall.lean` proves the independent, unconditional
small-radius result `SmallCutoffRowMass.exists_forall_cutMoment_ne_top_small_radius`.
It produces $0<t_0<r_1$ such that every natural cluster moment is finite for
every positive cutoff below $r_1$, without any subcritical-mean hypothesis.
The same conclusion is available at arbitrary parameter $\beta$.

Nearest-neighbour support lies in a finite ball and has intensity at most
$\beta|B_{t_0+1}|(K(t_0)-K(r))$. Continuity of $K$ at the attained minimum
$t_0$ makes this row budget smaller than one near $t_0$ from the right. The
BFS high-temperature envelope then controls **every** natural moment. Below
$t_0$ the off-diagonal cutoff row is empty.

This does not prove finiteness at large cutoffs or the eventual-at-infinity
hypothesis of the critical divergence consumer. That larger range still needs
the reduced-parameter finite-mean hypothesis or a genuine first-moment
comparison. No zero-percolation-probability shortcut is used.
