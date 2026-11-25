# Source-correction concordance: b20bbd7

This guide connects the reading maps to the 25 existing errata entries across six sources at [b20bbd7](https://github.com/tomhutchcroft/lrp/tree/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata). That critical-methods revision is unmerged. Every entry is provisional: these are recorded discrepancies and proposed fixes or workarounds, not author-confirmed corrections. Repeated issues in different sources retain their separate source locators. The count is not a count of distinct mathematical errors or completed proofs.

The tables below are reading pointers, not another errata registry. The pinned records contain the exact source locator, original claim, explanation, correction, affected assertion tags, issue links and consequences for Lean. The linked reader pages open the separate private critical-methods preview; they can advance after this snapshot. Use the pinned record when reproducing this inventory.

Editorial status, a mathematical replacement proof and formal correspondence are separate. The errata renderer obtains formal evidence from the compiled manifest and fingerprint-bound review records. No proof status is inferred here from a tag, a Lean filename or a proposed repair.

## Preliminary lecture notes

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/notes.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [Literal zero field and the positive-field limit](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#ghost-zero-field) | Separate the value at zero field from the positive-field limit. | The formal statement must allow infinite clusters; the positive-field tree formula is unaffected. |
| [Positive part in the nontransitive boundary bound](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#boundary-positive-part) | Use the squared positive part of the boundary deficit, or the stronger outgoing-mass bound. | Constant susceptibility is needed before dropping the positive part; the transitive application is unchanged. |
| [The stronger quantitative triangle numerator](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#triangle-numerator) | Use the weaker differential inequality 4KBG and its almost-everywhere qualification. | A proof of this replacement does not certify the stronger printed numerator; retain the separate integration argument. |
| [The reverse-BK switching cancellation](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#reverse-bk-cancellation) | Retain the overlap term in the exact interpolation increment. The bubble-only comparison remains open. | FIXER owns issue #242. Independent-copy separation and stronger triangle hypotheses do not close this dependency. |
| [The susceptibility tail sum starts at one](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#susceptibility-tail-index) | Sum non-strict volume tails from threshold one, or strict tails from zero. | Keep extended expectations. The new VolumeTails module is a comparison route, not a reviewed association for this entry. |
| [The exponential cluster tail needs a prefactor](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#sharpness-tail-endpoint) | Keep the exponential-tail prefactor for all thresholds, or state the eventual range without it. | The root counts in cluster volume; no change to the cluster convention is justified. |
| [Critical extinction excludes deterministic one-child offspring](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#deterministic-critical-offspring) | Exclude the deterministic-one law from critical almost-sure extinction. | The least-fixed-point identity alone does not imply extinction when the generating function is the identity. |
| [Local progeny asymptotics must respect lattice support](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#local-progeny-support) | Separate tail asymptotics from local masses and their support restrictions. | The zero-or-two example has only odd total progeny. A tail theorem does not prove a local limit theorem. |
| [OSSS covariance needs an increasing comparator](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#osss-increasing-comparator) | Put monotonicity on the covariance comparator, not on the event computed by the tree. | Retain the finite product and non-repeating tree hypotheses; infinite-product approximation remains separate. |
| [The intensity derivative must specify closed pivotality](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#closed-pivotal-qualifier) | Intensity derivatives use closed pivotality, or state-independent pivotality times the closed-edge probability. | Keep finite-volume differentiation separate from the integrated or almost-everywhere infinite-volume argument. |
| [Ghost-coordinate covariance does not vanish for magnetization](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#ghost-coordinate-covariance) | Ghost-coordinate covariances vanish for a bond-measurable comparator. | The tree computes the ghost event and the comparator is different; direct magnetization variance retains ghost terms. |
| [The four-point bound retains the matching maximum](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/notes/#four-point-prescribed-matching) | Keep the maximum over the three matchings, or its symmetric sum consequence. | A prescribed matching does not bound the whole event. The higher-order probability inequality remains an input. |

## Duminil-Copin–Tassion sharpness paper, arXiv v3

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/dct-sharpness.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The intensity derivative uses closed pivotality](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/dct-sharpness/#closed-pivotal-derivative) | Restore the closed-edge factor when the pivotal event is state independent. | Wire the finite exterior, condition on unexplored bonds and pass to the limit afterwards; do not differentiate an infinite limit formally. |
| [Critical field lower bounds require saturation](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/dct-sharpness/#critical-field-saturation) | Restrict the printed power bound to small fields, or saturate it at one. | 36PN supplies a percolation replacement under its explicit hypotheses. It does not supply the separate Ising small-field proof. |

## Hierarchical critical two-point paper, arXiv v1

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/hutchcroft-hierarchical-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [Finite-volume quantiles need only a one-sided limit](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#quantile-continuity) | Use local constancy from the left at a finite positive endpoint, through continuity of fixed tail probabilities and quantile minimality. | Do not assume global continuity of an integer-valued quantile; the helper alone does not prove the hierarchical estimate. |
| [The quantile estimate at zero intensity](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#zero-intensity-division) | Keep the squared estimate with intensity times quantile squared on the left, so zero intensity is included. | Divide only at positive intensity; the critical passage also needs the finite-threshold proof. |
| [Uniform truncation must retain the intensity scale](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#scaled-truncation) | Retain the intensity-dependent cutoff or a constant multiple of the block-maximum quantile. | The route 12NL to 2XJX to 655W needs rooted tails and the squared quantile estimate; a small discarded probability does not control discarded expectation. |
| [The finite-set criterion requires the root](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#root-containing-criterion) | The finite sets in the critical boundary criterion must contain the root. | Duminil-Copin–Tassion already include this hypothesis; the omission is in the hierarchical quotation. |
| [The critical lower bound retains a coefficient](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#susceptibility-lower-coefficient) | Retain the boundary-flux coefficient and finite positive critical intensity. | An upper kernel envelope alone does not imply finite critical intensity. The comparability statements are unchanged. |
| [The supercritical density comparison uses a minimum](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-hierarchical-2021/#density-saturation) | Saturate the near-critical density scale with the minimum of the intensity increment and one. | The diagram criterion does not itself supply the probabilistic near-critical comparison. |

## Power-law bounds paper, arXiv v2

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/hutchcroft-powerlaw-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The amplification exponent starts at one](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-powerlaw-2021/#amplification-zero-iterate) | Require at least one amplification iteration; the constants 1/9 and 27 are retained. | Use the corrected marked-tree argument for full-cluster intersections. No compiled proof follows from the repair note. |
| [The recursive partition threshold](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-powerlaw-2021/#recursive-retaining-threshold) | Retain small marked pieces at the corrected recursive threshold; keep vertex coverage and disjoint edge sets. | Endpoint sets may overlap. BK applies to disjoint edge witnesses, not a disjoint vertex partition. |

## Triangle-condition paper

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/hutchcroft-triangle-2021.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [Positive part in the nontransitive boundary bound](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-triangle-2021/#boundary-positive-part) | Use the squared positive part of the boundary deficit, or the stronger outgoing-mass bound. | Constant susceptibility is needed before dropping the positive part; the transitive application is unchanged. |
| [The stronger quantitative triangle numerator](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-triangle-2021/#triangle-numerator) | Use the weaker differential inequality 4KBG and its almost-everywhere qualification. | A proof of this replacement does not certify the stronger printed numerator; retain the separate integration argument. |

## L2 and reverse-BK source

[Pinned source records](https://github.com/tomhutchcroft/lrp/blob/b20bbd7db5b5981895d19aab1a516a47f2bbb0a8/wiki/errata/hutchcroft-l2-2020.json).

| Existing erratum | Repair or remaining gap | Consequence for Lean |
| --- | --- | --- |
| [The reverse-BK switching cancellation](https://perclib-private-preview.tomhutchcroft.chatgpt.site/errata/hutchcroft-l2-2020/#reverse-bk-cancellation) | Retain the overlap term in the exact interpolation increment. The bubble-only comparison remains open. | FIXER owns issue #242. Independent-copy separation and stronger triangle hypotheses do not close this dependency. |

## Newly merged comparison routes

The [b086702 library map](sources/perclib-b086702.md) identifies source interfaces relevant to several of these checks. In particular, the positive-index tail sum and finite-coordinate intensity derivatives can now be compared directly with merged source. A file-level match still needs an exact assertion association and review of hypotheses before it changes a displayed correspondence status.

The proposed corrections above do not resolve the bubble-only reverse-BK comparison, the Ising field proof or the probability implication from the hierarchical triangle criterion to its near-critical density conclusion.

## Finite-quantile follow-up on merged main

The [b65a568 library map](sources/perclib-b65a568.md) records the finite-vertex left-stability and positive-endpoint transfer lemmas added by [the merged quantile package](https://github.com/tomhutchcroft/lrp/pull/341). Their source contracts require finite ambient vertices, not merely a finite observation window; the endpoint bound requires a positive endpoint. They supply the helper used by the one-sided quantile workaround, while the hierarchical bound itself and its reviewed correspondence remain separate. This follow-up does not change the historical erratum inventory or its provisional diagnoses.
