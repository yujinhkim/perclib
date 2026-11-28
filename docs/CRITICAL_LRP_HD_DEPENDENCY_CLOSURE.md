# Case-3 dependency closure, uniform cutoff limits, and the diagonal covariance

This note records the `smwznoz6j` additions reviewed at production commit
`16d9f2aa1e83afeda3fc66117e38ed3352b2e567`. They are checked reductions. They
do not instantiate the critical two-point estimates, prove the uncut critical
volume tail, or finish Proposition I.4.20.

## HD(3) inputs consumed by the higher-moment interfaces

`VolumeMoments/HigherMoments/I420Case3/HDClosure` connects the already-proved
`TriangleFromHD` results to actual Case-3 consumers. In particular:

* `case3_hAend_hAmid_cutPoly_source_of_case3HD_of_critical_divergence` and
  `case3_i421_cutPoly_source_of_case3HD_of_critical_divergence` remove their
  separate `hTri` premise;
* `firstMomentAsymptotic_of_critical_divergence_ae` derives eventual cutoff-mass
  finiteness from the second cutoff moment and the uniform defect bound from
  the defect limit; and
* `exists_case3_i421_cutPoly_source_of_case3HD`, its all-index counterpart, and
  `case3_hAend_hAmid_cutPoly_source_of_case3HD` derive `hTri`, tail decay, `hP`,
  `hgm` and root-moment finiteness through the existing cited-tail and
  finite-cutoff-first-moment routes.

These are not unconditional model theorems. They still assume literal HD(3),
the uncut critical mean divergence, second-moment and off-corner envelope /
continuity data, vanishing of `cutError`, the cited uncut volume tail, and first
cutoff-moment finiteness at the specified radii. The normalized discrepancy at
(I.4.21) keeps the same `discR` and `biasTarget`; the all-index theorem covers
`ℓ+1 ≤ p`. The I.4.22 ODE and the higher-moment limit are not supplied here.

The same file records the exact effect of the totalized logarithm. `Case3HD`
forces the normalized source norm to exceed `1` at every pair having positive
connection probability. A norm at or below `1` with positive two-point mass is
incompatible with it, unlike a literal real-analysis reading that regards the
inverse logarithm as infinite at unit distance. The norm `2‖·‖_∞` avoids this
issue because every nonzero lattice distance is at least `2`; this does not
provide the required critical two-point upper estimate.

## Uniform cutoff convergence does not prove a uniform tail bound

`CriticalVolumeTail/UniformCutoff` proves two cutoff-limit identities: one for
cluster-volume tails and one for any increasing event with finite witnesses.
The uncut mass is written as the supremum over all positive cutoff radii. Hence

```text
CriticalVolumeTail C ↔
  ∀ r > 0, ∀ n ≥ 1, P_{β_c,r}(|K| ≥ n) ≤ C / sqrt n.
```

This is an exact reformulation of the unresolved input. A radius-dependent tail
constant is not enough to infer a single uncut bound through this equivalence,
and the identity supplies no such constant. `momentGap_of_uniform_cutTail`
retains finite second cutoff moment at the selected radius. No triangle-to-tail
proof, uniform critical moment bound, or subcritical sharpness result follows.

## Third moment and the diagonal covariance instance

`Correlation/I417/General/QZeroRepairAudit/Diagonal` instantiates the established
native third-moment tree inequality at the model's own normalized-norm cutoff
law, not only at the separate sup-norm cutoff. It proves

```text
cutMoment 3 r ≤ 3 * cutMoment 1 r ^ 5
```

without moment-finiteness assumptions, by the ordinary (I.2.3) tree bound. It
also bounds the covariance and star uniformly by the third moment, proves their
real `3 χ^5` bounds under finite first moment, and proves the diagonal
`HasCovBound` instance for every `C₅ ≥ 3`, including the infinite-χ case.

`HasUniformWeightStar` deliberately weights the last `χ^5` term by `1`, not by
`T(0,y)`. Its `(1,2,3)` assembly is not the source's two-point-weighted additive
star and does not prove the missing off-diagonal `HasCovBound`. The source's
essential Case-3 argument uses the proved product gap, not this alternative
covariance route. No general mixed `E|K|³ ≤ 3 E|K|² χ²` theorem is claimed.

## Verification

All four candidate packages were independently elaborated with strict flags at
`16d9f2aa` and their axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. After qualifying package imports and correcting the above
comment-only norm statement, the integrated aggregate also passes

```sh
lake build --wfail PercLib.CriticalLRP.Analysis.SecondMomentCase3.Audit
```

See `CRITICAL_LRP_REGIME_AUDIT.md` for the independent parameter-boundary audit
and `CRITICAL_LRP_CASE1_SOURCE.md` for the Case-1 conditional I.4.15 package.
