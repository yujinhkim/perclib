# Continuation: logarithmic integrability at the end of Lemma I.4.9

Source: supplied PDF, final sentence of the statement of Lemma I.4.9 on page 37.

`Analysis.isLogErrorFunction_of_eventually_rpow_bound` proves a general
comparison result. If a measurable real function `E` satisfies, for some
`a > 0`, `c ≥ 0`, and positive threshold `r₀`,

`0 ≤ E r ≤ c * r^(-a)` for every `r ≥ r₀`,

then `E` is a logarithmically integrable error function. The tail integrability
comparison uses the existing `isLogErrorFunction_const_rpow_neg`; the same
power bound and `squeeze_zero'` prove convergence to zero.

`VolumeMoments.FirstMoment.lemma_I_4_9_logIntegrable` instantiates this with
`a = d - 3α` and the paper's constant `16α³ / βc³`. It therefore proves exactly
the final logarithmic-integrability assertion from the displayed eventual bound

`0 ≤ E₁,r ≤ (16α³ / βc³) r^(3α-d)` for `r ≥ r₀`.

The hypotheses include `0 < α`, `0 < βc`, `3α < d`, `0 < r₀`, measurability of
the error, and the displayed eventual nonnegative bound. This is a conditional
corollary of that bound, not a claim that the bootstrap producing it has been
completed. The full first-moment estimate in I.4.9 remains open, so its coverage
classification remains PARTIAL.

## Validation

On the exact pre-commit working tree:

- `lake build --wfail PercLib` passes with 9,465 jobs;
- `python3 scripts/check_import_closure.py PercLib` reports all 418 modules;
- both new declarations' `#print axioms` reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`;
- the comment-aware placeholder scan and `git diff --check` pass.

These are local checks, not upstream CI or completion of the full lemma.
