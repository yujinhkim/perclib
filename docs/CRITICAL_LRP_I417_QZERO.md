# The `q = 0` star moment and the remaining Case-3 numerator gap

## What the new modules prove

`Correlation/I417/General/QZeroStar/Defs.lean` defines
`I417Gen.starMoment π x y p` as the `ℝ≥0∞` expectation of
`1(x ↔ y) |K_x|^p`. `Main.lean` proves:

* `rawDiff_add_starMoment`: the raw disconnected expectation plus this
  connected star moment is exactly the product moment at `q = 0`;
* `momentProd_sub_rawDiff_right_zero` and `momentGap_toReal_right_zero`:
  the subtractive and real-valued forms, under explicit finiteness
  hypotheses (there is no conversion of an infinite value using `toReal ⊤ = 0`);
* `starMoment_eq_tsum_labelEvent`: the star moment is
  `∑_{f : Fin p → V} P(f ⊆ K_x ∧ x ↔ y)`, an exact one-copy
  `(p+1)`-point expansion in `ℝ≥0∞`; and
* `starMoment_le_momentPow`: the elementary bound by the plain `p`-th moment.

The general marked family is indexed by `Fin q × V`. At `q = 0` it is
therefore empty and evaluates to zero (`markedFamily_q_zero_eq_zero`). If
`T(x,y) > 0`, the star moment is positive and strictly exceeds that empty
family (`markedFamily_q_zero_lt_starMoment`). Thus the existing general
marked-family expression cannot simply be specialized at `q = 0`; this is a
statement about that representation, not a claim that no separate argument
can prove the source lemma there.

## Identification with the Case-3 numerator

`connCubeVertexMass_eq_starMoment` gives, at the actual cutoff law,
`connCubeVertexMass r y = starMoment (M.cutProb r) 0 y 3`.
Hence the per-vertex Case-3 numerator is the one-copy four-point star
`E[|K_0|³ 1(y ∈ K_0)]`, as required by the `p = 3, q = 0` gap. Its labelled
form is
`∑_{x₁,x₂,x₃} P(x₁,x₂,x₃,y ∈ K_0)`.

`connCubeVertexMass_eq_momentGap_of_cutMoment` identifies it with the
corresponding `momentProd − rawDiff` when the third cutoff moment is finite.
`connCubeMass_eq_sum_starMoment` identifies the window numerator with the sum
of these per-vertex star moments. `connCubeVertexMass_le_cutMoment_three`
records the elementary bound by the third cutoff moment; summing that bound
introduces an unabsorbed window factor and does not solve the error-decay
problem.

## What remains open

The new packet does **not** prove the tree-count inequality. The missing
source input is still the estimate

`starMoment (M.cutProb r) 0 y 3 ≤
 C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`

in its exact real-valued normalized form. This requires the binary-tree
expansion with seven edges and two pinned vertices, retaining the `ℓ = 3`
and `ℓ = 4` diagram counts. It is separate from the additional uniform
`ℓ = 3` driver bound `hT3`. The existing conditional Case-3 wrapper therefore
remains conditional on these genuine inputs.

The naive diagonal column-sum alternative is not a substitute: it produces a
residual that has only yielded Case-1 decay in the current assembly. The
correct off-diagonal estimate, an origin correction, or a repaired
consumer-side cancellation is still required.

## Degenerate printed source scope

`momentProd_sub_rawDiff_zero_zero` evaluates the `p = q = 0` gap as `T(x,y)`.
The printed right-hand sum is empty there, so it cannot bound a positive
connectivity probability; the printed lemma needs an appropriate nondegenerate
scope condition. For `p = 3, q = 0`, the source indices are `ℓ ∈ {3,4}`, so this
degeneracy does not affect the Case-3 application.

This source-scope observation concerns the degenerate printed display, not a
weakening or correction of the `p = 3, q = 0` estimate accepted here as the
remaining target. The source statements and proof transitions at pages 45–47
were checked independently during review. No source defect is silently
repaired in the Lean statements.

## Validation

The submitted proof was independently elaborated with
`-DwarningAsError=true -DautoImplicit=false`
`-Dweak.linter.mathlibStandardSet=true`. The complete axiom audit lists only
`propext`, `Classical.choice`, and `Quot.sound`. Production integration merely
places the definition in `Defs.lean`, separates theorem modules, and applies
the repository's normal audit/linter conventions.
