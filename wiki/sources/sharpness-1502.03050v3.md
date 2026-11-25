# Sharpness reading map: 1502.03050v3

Version: [arXiv v3](https://arxiv.org/abs/1502.03050v3), submitted 21 January 2018. Locators below use the [23-page PDF](https://arxiv.org/pdf/1502.03050v3), whose printed date is 23 January 2018, rather than the experimental HTML's displayed date. Inspected 15 November 2026.

This is a reading inventory, not a complete prose treatment or a compiled correspondence certificate. The existing [sharpness article](articles/sharpness.md) is a starting point. Proof additions in the [critical-methods bundle at a401eba](https://github.com/tomhutchcroft/lrp/blob/a401ebabd0e37411be6a864df733cf8ac2d8a51a/wiki/articles/integrated-susceptibility.md) and its [spatial-decay consequence](https://github.com/tomhutchcroft/lrp/blob/a401ebabd0e37411be6a864df733cf8ac2d8a51a/wiki/articles/exponential-moments.md) are unmerged and are not part of this analytics snapshot. Their stated summability and geometry hypotheses must be compared with each source occurrence before claiming correspondence.

The canonical finite-size results and USAC are in the [foundations/models bundle at fa3d1bd](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/boundary-laws.md), also unmerged. YLZV retains the finite-size contraction; the redundant tag 8IFN is retired. These cross-bundle references preserve the existing registry rather than allocating parallel assertions.

## Numbered statements and definitions

| Source locator | Topic | Wiki coverage task |
| --- | --- | --- |
| [Theorem 1.1, p. 2](https://arxiv.org/pdf/1502.03050v3#page=2) | Percolation sharpness | DYUM/6THJ are existing statements. [L0TE](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L44) supplies threshold identification; compare the spatial conclusion separately with YVJT. |
| [Proposition 1.2, p. 4](https://arxiv.org/pdf/1502.03050v3#page=4) | Critical susceptibility | [RDF0](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L65) is the canonical susceptibility characterization and endpoint argument; 5LNL supplies a quantitative intensity-increment alternative. |
| [Proposition 1.3, p. 5](https://arxiv.org/pdf/1502.03050v3#page=5) | Critical field bound | 36PN proves a saturated all-field bound under explicit finite-critical-intensity hypotheses; source-specific correspondence remains unreviewed. |
| [Lemma 1.4, p. 5](https://arxiv.org/pdf/1502.03050v3#page=5) | Exit derivative | [HATE](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L25) is the canonical exact wired derivative. The alternative exposition retains the finite-wiring justification; redundant tag N880 is retired. |
| [Lemma 1.5, p. 6](https://arxiv.org/pdf/1502.03050v3#page=6) | First-exit inequality | [USAC](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/boundary-laws.md) proves the restricted-domain inequality for countable independent bonds, allowing infinite domains and a suffix that returns to the inner set. The source occurrence is pending review. |
| [Lemma 1.6, p. 8](https://arxiv.org/pdf/1502.03050v3#page=8) | Field derivative | F7SW proves finite increments and an almost-everywhere derivative form; everywhere differentiability is not claimed. |
| [Theorem 2.1, p. 9](https://arxiv.org/pdf/1502.03050v3#page=9) | Ising sharpness | No dedicated Ising treatment in this snapshot. |
| [Proposition 2.2, p. 11](https://arxiv.org/pdf/1502.03050v3#page=11) | Critical Ising susceptibility | No dedicated treatment. |
| [Proposition 2.3, p. 11](https://arxiv.org/pdf/1502.03050v3#page=11) | Critical Ising field bound | No dedicated treatment; field range also requires correction. |
| [Definition 2.4, p. 11](https://arxiv.org/pdf/1502.03050v3#page=11) | Currents and sources | Definitions and conventions still to reconcile. |
| [Lemma 2.5, p. 12](https://arxiv.org/pdf/1502.03050v3#page=12) | Current switching | No proof or correspondence recorded. |
| [Lemma 2.6, p. 13](https://arxiv.org/pdf/1502.03050v3#page=13) | Finite-volume derivative | Keep both finite-volume correction terms; no treatment recorded. |
| [Lemma 2.7, p. 19](https://arxiv.org/pdf/1502.03050v3#page=19) | Modified Simon inequality | No proof or correspondence recorded. |
| [Lemma 2.8, p. 21](https://arxiv.org/pdf/1502.03050v3#page=21) | Ising field derivative | No proof or correspondence recorded. |

## Arguments beyond the numbered statements

| Source passage | Additional inventory work |
| --- | --- |
| General notation; Sections 1.1 and 2.1 | Model, boundary, range and parameter conventions. |
| Sections 1.2 and 2.2 | Nearest-neighbour/site variants, planar consequences, locality discussion and dependent/oriented models. IU3W/468P cover the bond-probability bound and lower semicontinuity in the unmerged bundle; the other comments remain separate. |
| Sections 1.3–1.5 | Remarks 1.1–1.2; approximation, iteration and field arguments. |
| Sections 2.3–2.6 | Remark 2.1; current/backbone identities, properties P1–P3, Claims 1–2 within Lemma 2.6, limiting arguments. |

The tables locate the numbered definitions/results and the remaining argument groups. They do not certify every unnumbered assertion, reference, conjecture or proof step as covered. No new permanent assertion tags or source occurrences are allocated by this map.

## Proof-passage concordance

These thirteen pointers refine the broad argument groups above. Source pages are PDF pages, counted from one. Article links pin unmerged snapshots; they indicate where to compare arguments, not approved source occurrences or compiled status. The scope notes describe the wiki's present obligations.

| Source page and passage | Existing argument or remaining obligation |
| --- | --- |
| [p. 5: Threshold integration](https://arxiv.org/pdf/1502.03050v3#page=5) | [L0TE](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L44) integrates above the finite-size threshold and then exhausts the vertex set. Its endpoint conventions include an infinite threshold; it does not prove critical nonpercolation. |
| [p. 6: Boundary conditioning and Remark 1.1](https://arxiv.org/pdf/1502.03050v3#page=6) | [HATE](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L25) works on a finite wired graph with summable exterior intensities. The derivative uses closed pivotality, and the factorization specifies which bonds each event reads. This avoids an unsupported exchange of infinite differentiation and summation. |
| [p. 7: Finite-volume susceptibility bound](https://arxiv.org/pdf/1502.03050v3#page=7) | [YLZV](https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/boundary-laws.md#L51) is the canonical finite-size contraction argument. Its finite-volume bound precedes exhaustion; no rearrangement of an infinite susceptibility is justified by writing the same formal inequality. |
| [p. 7: Finite-range iteration](https://arxiv.org/pdf/1502.03050v3#page=7) | [YVJT](https://github.com/tomhutchcroft/lrp/blob/1a86901c5c2e124baf3be7237dfcb364acee7d0b/wiki/articles/exponential-moments.md#L53) supplies the spatial conclusion by a different route, through cluster-volume tails. It is a consequence-level pointer, not a claim that the source iteration has been reproduced. |
| [p. 8: Positive-field differentiation](https://arxiv.org/pdf/1502.03050v3#page=8) | [F7SW](https://github.com/tomhutchcroft/lrp/blob/1a86901c5c2e124baf3be7237dfcb364acee7d0b/wiki/articles/ghost-fields.md#L39) proves finite intensity increments and an almost-everywhere intensity derivative. The wiki must retain this regularity qualification when comparing it with a differential argument. |
| [p. 9: Critical-field integration and Remark 1.2](https://arxiv.org/pdf/1502.03050v3#page=9) | 36PN remains an alternative moment-interpolation proof of a saturated percolation bound. The field-range correction below is recorded provisionally and source correspondence remains unreviewed; the Ising case is not covered by that argument. |
| [p. 12: Backbone properties P1–P3](https://arxiv.org/pdf/1502.03050v3#page=12) | No wiki proof is recorded for the ordered backbone construction, concatenation or domain comparison. These require their own definitions and arguments; neither bond BK nor an abstract path decomposition discharges them. |
| [p. 13: Finite-volume correction limits](https://arxiv.org/pdf/1502.03050v3#page=13) | No Ising counterpart of the limiting argument is recorded. Keep the magnetization ratio and boundary remainder as separate obligations before integrating a limiting differential inequality. |
| [p. 15: Claim 1 inside Lemma 2.6](https://arxiv.org/pdf/1502.03050v3#page=15) | No current-factorization and switching proof is recorded for this claim. A link to the Bernoulli boundary factorization would not supply the missing current identity. |
| [p. 17: Claim 2 inside Lemma 2.6](https://arxiv.org/pdf/1502.03050v3#page=17) | The source-current recombination remains a separate coverage obligation, including its ghost-vertex convention. |
| [p. 19: Backbone decomposition for Lemma 2.7](https://arxiv.org/pdf/1502.03050v3#page=19) | No Ising proof is recorded. The percolation first-exit lemma USAC concerns independent bonds and must not be substituted for this input. |
| [p. 20: Volume and field limits; susceptibility iteration](https://arxiv.org/pdf/1502.03050v3#page=20) | No dedicated Ising treatment is recorded. Keep finite-volume correlations, infinite-volume positive-field correlations and the zero-field state distinct. |
| [p. 21: Field inequality and cubic integration](https://arxiv.org/pdf/1502.03050v3#page=21) | The Ising regularity and differential-inequality inputs remain unverified here. A conditional calculus repair alone would not discharge them. |

## Field-range correction to resolve

Propositions 1.3 and 2.3 print lower bounds proportional to h^(1/2) and h^(1/3) for every positive h. The left sides are bounded by one, so no fixed positive constant can make those inequalities hold as h tends to infinity. This is a restriction on the displayed quantifier, not a refutation of a small-field conclusion. The unmerged [moment-interpolation proof 36PN](https://github.com/tomhutchcroft/lrp/blob/a401ebabd0e37411be6a864df733cf8ac2d8a51a/wiki/articles/integrated-lower-tails.md) supplies a saturated percolation bound. The Ising correction and the source-specific proof correspondence remain outstanding. The wiki must not silently promote the printed all-field formulations to reviewed assertions.

## Recorded source corrections

The [source-correction concordance](sources/source-corrections-b20bbd7.md) links this paper’s existing provisional errata, their proposed repairs and the remaining Lean obligations. These records are in the separate unmerged critical-methods bundle. They do not certify this reading map or its article links as reviewed source occurrences.
