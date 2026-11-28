# Independent fidelity and normalization audit

`Orchestration/SourceFidelity/{Defs,Audit}` and this note record the m8 source
review of the Case-1/2, HD, tail and corner packages. It checks exact
constants and quantifiers, not merely elaboration.

## Kernel-checked supporting facts

The new statements verify the `(2p−3)!! = 945` instance and its admissible
exponent; that `SixthMomentMixed` with finite second moment yields finite sixth
moment; the Case-2 exponent identity; `1 < ρ` where the literal HD(3) has
positive two-point value; and `C ≥ 1` for either the uncut or radius-uniform
critical-tail leaf. All 54 representative production theorems in `Audit.lean`
independently report only the standard axioms.

`hgm_of_volumeTail` calls the tail's optimization at the exact consumer
interface, preserving first-moment finiteness assumptions. That is proof of the
conditional edge, not proof of the cited tail.

## Normalization finding N1

The printed Theorem I.1.6 and Proposition I.4.20 use a common factor `α/β_c` in
`I16rhs`. Proposition I.4.15 instead uses a power of its normalized second
moment's leading constant. These constants are related, not identical:

```text
E|K|^p ∼ (2p−3)!! A_{4.15}^{p−1} (α/β_c)^{2−p} r^(2p−1)α,
```

so the leading constant called `A` in the frozen I.1.6 statement is
`A_{4.15}/(α/β_c)`. `I16rhs_eq_scaled` verifies this algebra with the nonzero
normalizing premise. Existential quantification makes the formula consistent,
but a future assembly must not substitute Case-1's `A` directly into `I16rhs`.
The critical-dimension mutual-inverse quantities require equal care.

## Packaging defect R1: fixed

The Case-2 provenance header violated the strict long-line limit. After wrapping
it and supplying the missing module docstring, `SecondMomentCase2.Source.Defs`
passes the strict focused check with all its proof axioms standard. No theorem
was altered. `SecondMomentCase2.RegularVariation` is independently integrated
and passes the full production build.

## Large-distance defect F1: repaired

The original HD(3) closures used literal `Case3HD` everywhere, including the
I.4.21/direct-ratio consumers. That literal formula is refutable at a short
normalized distance in a model whose nearest-neighbour connectivity is
positive—even though only its far-distance part is used.

`I420Case3.HDClosure.LargeDistance` now proves
`exists_case3_i421_cutPoly_source_of_case3HDLarge`, its all-index counterpart,
and `case3_hAend_hAmid_cutPoly_source_of_case3HDLarge`. These use
`hTri_of_case3HDLarge`, `hTail_of_case3HDLarge` and
`case3TriangleTailData_of_case3HDLarge`. The critical-tail, sharpness,
continuity, defect, and derivative inputs remain unchanged. Older literal-only
conditional wrappers remain legacy and are not called unconditional.

## Findings not repaired by compilation

* The AE corner theorem does not itself imply a pointwise continuity premise,
  and local Weierstrass still needs pivotal continuity plus a summable
  dominator. The corrected coefficient result is not yet a summed-flux
  discontinuity proof; see the separate `CornerFlux` module for that conditional
  step.
* `hHlog` for Case 1 is still an explicit premise of its sharp second-moment
  asymptotic and cube comparison. The source proves it in that case; the
  Case-1 producer is not supplied here.
* `hK`, `hex`, `hcontinf`, and `h0` remain extra analytic data, not automatic
  consequences of the model's measurable error function. No global continuity
  transfer into radial identities is inferred.
* Case 3 uses the cited uncut tail with full content, not a zero-constant
  approximation or an unsupported Gaussian substitute.
* The off-diagonal covariance remains unproved: only the sharp diagonal
  instantiation and the sufficient two-point-weighted star constraint are
  established.

## Next distinct paper segment

The most illuminating genuine next assembly is the moment-to-uncut-tail route
through I.3.2/Theorems I.1.6 and I.1.15. The Tauberian machinery and the Case-1
and conditional Case-2/3 moment analyses are separate today; the model
moment-to-tail application is not in production. The N1 normalization is a hard
constraint on that assembly. Superprocess limits and full random-measure
convergence remain distinct work and are not claimed here.
