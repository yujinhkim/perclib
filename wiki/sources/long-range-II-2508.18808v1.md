# Long-range II: initial reading map

Inspected [versioned HTML](https://arxiv.org/html/2508.18808v1), 15 November 2026.
Selected [PDF text](https://arxiv.org/pdf/2508.18808v1) also inspected, 15 November 2026: pp. 3 and 8–11. Its title date is 27 August 2025; the HTML displays 24 August 2026. Full rendition equivalence and full-paper coverage remain unverified. Locators are not assertion tags.

| Locators | Topic | Wiki disposition |
| --- | --- | --- |
| PDF pp. 3, 8–9; §II.1.1 | Kernel and cutoff conventions | Compare [soft cutoff](../articles/spatial-cutoff-moments.md) |
| PDF pp. 10–11; Definition II.1.3, Theorems II.1.5/II.1.7 | Localization/two-point source candidates | [Quoted scope](../articles/cutoff-localization.md#section-quoted-regimes); correspondence unreviewed |
| §II.4.1; Lemma II.4.4 | Localization | [Conditional criterion](../articles/cutoff-localization.md); model proof outstanding |
| §II.4.2–II.4.3 | Hydrodynamics | [Conditional all-scale argument](../articles/cutoff-hydrodynamics.md#section-all-scales); model inputs outstanding |
| II.5.3–II.5.6 | Mesoscopic mass | [Conditional synthesis](../articles/mesoscopic-tail-transfer.md#section-power-law-criterion); localization and damping remain inputs |
| II.5.8; (II.5.10) | Tail comparison | [Explicit sufficient transfer](../articles/mesoscopic-tail-transfer.md#section-transfer) |
| §II.5.3; Proposition II.5.9, Lemma II.5.11 | Multipoint lower bound | [Cluster extension and local-mass persistence](../articles/multipoint-trees.md#section-cluster-extension), followed by [separated-scale joining](../articles/multipoint-trees.md#section-long-range-gluing); full model-input correspondence remains open |

The introduction to §II.1.2 includes a discontinuous endpoint at alpha=d.
Our fractional-tail transfer instead assumes alpha<d. Do not erase that distinction.
Earlier chapters, the general-kernel application of higher-point geometry, slightly subcritical results, references and
unnumbered arguments still need correspondence work. This map is not a claim of
formalization or a substitute for the paper's hypotheses.

The §II.5.3 HTML proof was read on 15 November 2026. Its displayed tower identity has mismatched intersection ranges in its first equality; [the provisional erratum](../errata/hutchcroft-lrp-2.json) records the correction and its formalization consequence. The corrected recurrence keeps all mass events and adds one joining event at a time. No failure of Proposition II.5.9 is asserted.
