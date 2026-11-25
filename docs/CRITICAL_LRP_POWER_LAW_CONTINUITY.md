# Power-law cutoff continuity and first-moment derivative

Production modules:

- `Analysis/Cutoff/OffCorner/SourceCutoffMoments.lean`;
- `Analysis/Cutoff/OffCorner/PowerLawContinuity.lean`.

## Exact norm-rescaling bridge

For `M : SourceModelData`, suppose there is `c > 0` such that every integer lattice
vector has source norm `c` times its `ℓ∞` norm. Then

```lean
M.cutKernel r = CutoffKernel.cutoffSymKernel (fun t => M.K (c * t)) M.d (r / c)
```

`cutMoment_eq_native` carries this identity to every cluster-volume moment. The native
translation-invariant tree-graph third-moment estimate implies that a finite first
cutoff moment gives finite third and second cutoff moments. The theorem does not
assert this bridge for an arbitrary source norm, and does not produce the finite first
moment. The explicit witness uses `c = 2`, corresponding to `ρ = 2‖·‖∞`.

## Application to the explicit power-law model

`OffCorner/PowerLawContinuity` first uses the two-point capstone to prove continuity of
`normalizedPivotMass` on off-corner windows. It supplies the per-vertex continuity input
of `OffCorner/PowerLawDeriv`, constructs `codeWindow`/`Finset.sym2` exhaustions, and
turns one off-corner radius into a suitable corner-free window.

The final wrapper
`sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment` proves, for
`0 < r₀ < R`, `r₀ ∉ cornerRadii`, and `cutMoment 1 R ≠ ⊤`, that the explicit
`sourceModelWitness` has

```lean
HasDerivAt M.cutMassReal (M.betaCrit * r₀ ^ (-d - α - 1) * M.exclScalar r₀) r₀
```

after coercion of `β_c` to the reals. The separate moment-transfer result supplies the
second and third moments consumed internally by excluded-mass continuity. Neither
`β_c > 0` nor an auxiliary `T,S` exhaustion is a premise of this wrapper.

The unconditional small-radius existence theorem is a boundary consistency check: its
constructed radius is below `2`, where the witness has no attained radius from a
nonzero lattice vector and hence no nonloop positive-distance edge. It is not a proof
of the paper's large-radius ODE.

## Fourth cutoff moment

`OffCorner/SourceCutoffFourthMoments` uses the generic native fourth-moment estimate
$\mathbb E|K|^4 \le 15(\mathbb E|K|)^7$ under translation-invariant two-point
probabilities. It states `fourth_moment_cutoff` without a moment hypothesis, proves
`cutoff_fourthMoment_ne_top_of_firstMoment` for the native loop-safe cutoff, then
transports both the inequality and its finiteness corollary across the same exact
kernel rescaling. The source-level `cutMoment_four_le` and
`sourceModelWitness_cutMoment_four_le` are genuine unconditional extended-real
inequalities; the finiteness corollaries still require a finite first cutoff moment.
This is not an all-moment or asymptotic theorem, and does not provide the first moment.

## Remaining gaps

This package does not construct finite first cutoff moments at arbitrary large radii,
prove `β_c > 0`, extend the derivative formula to attained radii, prove all-order
moment asymptotics, or establish any principal main theorem of the paper. The residual
qualification of Lemma I.4.1 and the relationship between off-corner and one-sided
statements are source-fidelity questions, not completed paper results.

Integration independently rebuilt the capstone packet and moment bridge with
`warningAsError`, `autoImplicit=false`, and the strict Mathlib linter. The bridge's
original report had missed three lint failures; integration repaired the module header,
a `show`/`change` linter issue, and the audit-command option before rebuilding. All
new theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
