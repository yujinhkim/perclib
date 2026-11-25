# Proposition I.4.2, Case 3: divergence of the cutoff first moment

## Proved reduction

`VolumeMoments/FirstMoment/Divergence.lean` establishes the following, in namespace
`PercLib.CriticalLRP.I42C`:

* `lintegral_uncut_clusterVol_eq_tsum` identifies the uncut critical first moment with the
  site sum of the two-point function.
* `uncutFirstMoment_eq_top_of_rpow_lower` proves that the lower half of Theorem I.2.14 forces
  the uncut critical first moment to be infinite. Its actual hypotheses are a positive constant
  `c`, `0 < α < d`, and `c ‖x‖^{-d+α} ≤ P_{β_c}(0↔x)` for every nonzero `x`, evaluated at the
  model's normalized distance. It does not infer this lower bound from finite triangle mass.
* `tendsto_cutMassAt_atTop_nhds_top` transfers the divergence to the cutoff masses using the
  actual uncut-to-cutoff moment limit.
* `tendsto_cutMassAt_toReal_atTop` obtains the real-valued `f → ∞` input of the analytic ODE
  solver, with eventual cutoff-moment finiteness still explicit. This requirement cannot be
  ignored because `ENNReal.toReal ⊤ = 0`.
* `exists_bounded_solution_ratio_zero` gives a constant solution of the other ODE/error inputs
  whose ratio tends to zero. It demonstrates that divergence is not a removable hypothesis in
  scalar `FirstMoment.first_moment_asymptotic`, independently of any percolation statement.
* `first_moment_asymptotic_of_rpow_lower` combines the divergence with the scalar solver. It
  still assumes the actual cutoff model derivative, vanishing error term, eventual finiteness
  and positivity of the critical parameter.

The finite-ball argument uses the actual model seminorm and the normalized lattice count. It is
not a finite-torus substitute for an infinite-lattice result. All six declarations are audited
in `FirstMoment/DivergenceAudit.lean` with only `propext`, `Classical.choice`, and `Quot.sound`.

## Corner-safe analytic hand-off

`VolumeMoments/FirstMoment/CornerSafe.lean` replaces everywhere differentiability with
absolute continuity on each compact interval plus an almost-everywhere derivative equation.
It proves the exact reciprocal ODE identity, the display (I.4.7), first-moment asymptotics,
and the associated logarithmic-error and one-sided comparison results, all in the
corner-safe formulation. The exceptional radii are a countable set of model edge lengths.

The a.e. FTC step preserves compact positivity and splits the interval integrals before
taking limits. It does not claim a two-sided derivative at a cutoff corner. All 23 exports
are audited in `CornerSafeAudit.lean`, with only the standard foundational axioms.

This is the analytic part of the hand-off, not its model instantiation. Absolute continuity of
`(M.cutMassAt r 0).toReal` on each bounded interval, the real cutoff ODE, the vanishing
multiplicative errors, the source normalization hypotheses, and measurability of the
normalized error remain obligations. The normalized error's measurability is an explicit
input, not claimed silently. We use the sufficiency given by these theorems; no general
"if and only if" claim about vanishing pointwise error is introduced by this file.

## Conditional tail-error rescaling

`Analysis/Polygon/TailLog.lean` provides the corresponding rescaling of an existing logarithmic
error function. If `(M.nablaTail r).toReal` is a logarithmic error function, then
`(M.nablaTail (r^c)).toReal + r^{-c}` also is, for every positive `c`. Both logarithmic
integrability and convergence to zero are included. This uses the established power-rescaling
theorem and the negative-power error constructor, not a mistaken `(∇_r)^c` reading and not a
proof that the probabilistic tail decays or is absolutely continuous.

## Lower comparison from the ODE and the error sign

`Analysis/Polygon/ChiLower.lean` adds the weaker lower-comparison route. The pointwise sign
`(1-E₀)(1-E₁) ≤ 1` supplies the derivative comparison used by Lemma I.4.5(2). With `E₀ → 0`
and `E₁ ≥ 0`, the library also obtains the eventual lower bound `(α/(2β_c)) r^α`, and then a
single positive constant and finiteness for every positive radius. Its polygon assembly replaces
the sharp ratio asymptotic by these ODE inputs, while preserving diagonal-maximality and the
usual tail factor for `ℓ ≥ 4`.

This is not a replacement for the full Proposition I.4.2 asymptotic where that conclusion is
needed. The actual cutoff derivative and `χ r → ∞` remain hypotheses, and `E₁ ≥ 0` is explicit,
not silently derived from finiteness of the triangle. `exists_normalizationError` derives the
matching `E₀` from `M.exists_error` and the normalized ball count. The separate
`bounded_defect_insufficient` example is useful here: if one drops the error-sign hypothesis, a
bounded defect alone need not produce the lower comparison.

## Still open for the full Case 3

1. **Theorem I.2.14 itself.** In particular, the lower off-diagonal critical two-point bound
   used above. The current coverage ledger marks it as not formalized.
2. **The model-level ODE.** `first_moment_asymptotic_of_rpow_lower` takes the real derivative
   and its defect `h` as hypotheses. Corner-free/one-sided cutoff differentiation cannot be
   silently upgraded to differentiability at every corner.
3. **The vanishing error term.** The source invokes vanishing spatial open-triangle tails
   through I.4.11 and a ball average. It must not be read off from finite diagonal or a
   moment bound alone. `TriTail.tendsto_openTriangleTail_iff` is only a criterion for decay,
   not its proof.
4. **Eventual cutoff-moment finiteness.** This is genuinely separate from divergence and
   from absence of infinite clusters. The real `ENNReal.toReal` convergence argument needs it.
5. **The logarithmic-error half.** The stronger Case 3 account also needs the relevant
   tail/logarithmic-integrability input, not just the first-order limit.

Accordingly, the source coverage remains partial. These proofs reduce explicit dependencies;
they do not claim Proposition I.4.2 Case 3, ∇-tail decay, a critical finite full-lattice
susceptibility, or any of the main high-dimensional asymptotic theorems.
