# Session closeout — bounded orchestration, not a completed formalization

## State actually committed

The non-workflow orchestration work is on branch
`work/yujinhkim-critical-lrp-orchestration`, first at commit
`753e9369424b46311bebd730a4dfe21b958d2840`, with this ledger added by its
successor. The current head is the revision named by `git rev-parse HEAD`, not
an assertion that the paper is finished. The supplied source is Hutchcroft
*Critical long-range percolation I*, arXiv:2508.18807v1.

The two literal definitions `SourceNorm` and `SourceModel` remain sealed with
the foundational axioms `[propext, Classical.choice, Quot.sound]`.
The two moment roots remain exactly these registered drafts, not proved theorems:

- `PercLib/CriticalLRP/Orchestration/Frozen/HighDimensionalMoments.lean`
- `PercLib/CriticalLRP/Orchestration/Frozen/CriticalDimensionMoments.lean`

No frozen declaration was weakened or silently replaced, and no `hbc` binder
was inserted to waive positivity/finiteness of `beta_c`.

## Final checks actually run

- `lake build --wfail`: **passed** for the production package at the
  orchestration commit preceding this ledger. The Frozen/Provider quarantine is
  deliberately excluded from this production root; the draft targets were also
  built separately with the two intended registered draft warnings.
- Full production axiom audit, using the existing
  `scripts/ExtractManifest.lean` mechanism with collection enabled for **every**
  declaration in the compiled `PercLib` namespace: **9,753 declarations,
  0 nonstandard axioms, 0 `sorryAx`**. The generated raw audit and verifier live
  at `.scratch/verification/full-axioms.json` and
  `.scratch/verification/ProductionAxiomAudit.lean`, not in the production root.
- Separate checks on the two frozen roots: each reports
  `[propext, sorryAx, Classical.choice, Quot.sound]`. These are intentional
  `DRAFT_SORRY` declarations, **not proof results** and not part of the clean
  production axiom set.
- `scripts/check_semantic_closure.py --root . --manifest docs/orchestration/FROZEN_ANCHOR_MANIFEST.json`:
  passed with 17/19/44/44 pinned semantic source files respectively for
  `source_norm_v1`, `source_model_v1`, and the two theorem roots.
  This verifies source bytes and scope, not source mathematics or proof.
- Source restitution: all 2,838 math annotations and all 287 containing
  inequalities passed, with pinned hashes and locator schema. The HTML hash and
  canonical text hash remain `246ccda2…` and `7658da06…`.
- Production import closure with `--exclude-quarantined`: passed. The excluded
  items are precisely the two frozen roots and their two providers; no draft is
  imported into the production root aggregator.
- Existing manifest and source-packet tests, semantic-closure mutation tests,
  dangling-dependency regression, anchor-scope tests: all passed.

The CI workflow extension itself was validated locally as YAML and by the
corresponding local checks, but was **not executed as a GitHub Actions run**.
GitHub refused the workflow-changing push: the connection lacks `workflows`
permission. `.github/workflows/lean.yml` therefore remains an uncommitted local
modification here. The complete attempt is retained on local branch reference
`blocked-ci-workflow`; it is not a published remote CI configuration. No
force-push, token-sharing workaround, or rewrite of history was used.

Node is unavailable in this VM, so the real wiki renderer/schema tests and the
wiki-dependent manifest-generation command were **not run**. That is distinct
from JSON-only errata validation and from the successful compiled axiom audit.

## Source graph and reviews: what is accepted

Exactly one packet from the latest normalization run was accepted after every
requested correction: `.ultramath/smwobyis9/m2/I23Packet.m2.md`. It has **68
source nodes and 93 edges**. Its parser, node-shape and topology checks report
zero diagnostics; its 205 locators have zero defects. It is a bounded source
packet, **not a reviewed global graph and not a Lean proof**. Its cited
literature leaves remain unverified.

Its useful mathematical findings include:

- `0 < beta_c < infinity` for the paper's kernel class for **every** `d >= 1`
  and `alpha > 0`, via the small-beta open-walk first-moment bound and positive
  line-kernel domination with a finite-range one-dimensional threshold. This
  is an ordinary derived proof obligation, not an asserted hypothesis.
- The negative-index Karamata branch really is consumed at canonical L1094
  (contrary to the earlier no-consumer claim), but Lemma I.4.13's actual proof
  uses Tonelli. The aside's factor is `1/a`, not the printed error's
  corresponding `1/(a+2)`.
- Derived `a >= 1` in Proposition I.3.2, with no new model premise.
- The limit defining `A_3` is still a separate well-definedness/finiteness/
  positivity obligation. At the intended use, `a=2` and `Q_infty=chi^2_1`,
  its exact value `sqrt(2)` is established; it is not an assumption leaf.

Other bounded reviews remain research, not a proof-closure judgment: the
critical-point argument, the I.4.1 rechecking, the two-scale averaged
I.4.18 repair, canonical-text fidelity, and the bounded DOM ownership map.

The following were explicitly checked but are **not accepted as completed
source topology**:

- The truncated I.5.3–I.5.4 rev2 record set (seven empty conclusions plus
  further truncated scope fields), despite its raw node/edge counts.
- I.1's full v3 graph; only its bounded ownership/locator artifact is accepted.
- Existing I.4.1 and I.5 normalization candidates still needing real
  repository-schema, ownership and source-provenance repair.
- Any custom count or cycle check that substitutes for source fidelity,
  independently reviewed local topology, or a global reviewer.

No global root-closure review was accepted. The production `DEPGRAPH.md`
remains a seed with the two roots and two standing-assumption records. Many
inventory dispositions still point to non-existent node IDs; there is no
accepted complete source graph, no `TOPOLOGY_STATUS: REVIEWED` promotion, and
no assignment of Lean proof providers based on module existence.

## Mathematical/source issues that remain open

- **HD3/v2:** the inverse logarithm is singular or negative on short distances.
  The candidate `log(1+rho)` regularization is a versioned source
  interpretation, not equality with the printed form and not an activated
  frozen anchor. A corrected anisotropic witness avoids the earlier mistaken
  isotropic-normalization calculation. The derived critical-point result does
  not require adding an arbitrary positivity binder to either root.
- **Lemma I.4.18:** the printed supremum at `ell=3` is false because
  `T(x,x)=1` gives `T^3(0,0) >= 1`. Retain `ell >= 4` separately from the
  two-scale averaged `ell=3` replacement. Do not identify a diagonal triangle
  value with finite total triangle mass. PSD is needed for diagonal maximality;
  symmetry alone is insufficient.
- **Lemma I.4.12:** a four-vertex witness refutes the printed closing product
  equalities/product step. The five-factor statement is not thereby refuted;
  its proof remains open at that step.
- **Corollary I.4.14:** the printed `r^{-d}` coefficient in the median bound
  is defective; the Lemma I.2.6 reasoning uses `r^{d}`. This does not complete
  the downstream hydrodynamic arguments.
- **Uncut-limit order:** I.5.49 quantifies over fixed `s >= s_0` while its
  proof uses a sequence `s_R -> infinity`; the reconciliation remains open.
- **I.5.52:** the alleged false `asymp` proposed in one worker's report is
  rejected. With `si = min{2/alpha,1}`, the displayed quotient is comparable
  to `R^{-alpha*si} = eta(R)`: gyration contributes `R^2`, the first moment
  contributes `R^{alpha*si}`, and the size-biased moment contributes
  `R^{2 alpha*si}`. A wrong computation must not become a source erratum.
- **Tree bookkeeping:** leaves `0,...,n` and `n-1` trivalent internal vertices
  yield `2n` vertices and `2n-1` edges. The coefficient `2^(2n-2)` is intact.
- **Superprocess roots I.1.9/I.1.17:** the canonical integrated excursion
  object, genuine Green function, moment/mass characterization, and the outer
  and inner carrier topologies remain unsettled. They stay deferred.
- Several cited works have not been read. Bot checks at Springer and Project
  Euclid blocked them; no work-around or title-only theorem premise was
  substituted. Contracts to literature require exact hypotheses, scope and
  discharge. Unread references are not counted as verified external leaves.

## Source status at the closeout

```text
DRAFT_ANCHORS: 2 -- the two moment-root files listed above
UNREGISTERED_SORRIES: 0 in the production orchestration modules
DRAFT_IMPORT_VIOLATIONS: 0 in the full semantic/frozen guard
SEALED_THIS_TURN: 0
```

**No new paper theorem was proved in Lean in this session.** The completed
work is bounded orchestration infrastructure, validated source research, and
checks of the resulting production package. Primary root proof obligations
remain `NOT_STARTED`; no unconditional `PROVED` status is claimed, and
`PROVED_MODULO` is not used to disguise an unproved root or unread citation.

The remaining source-only run was stopped after accepting the bounded
I.2/I.3 packet. Unfinished members' files are preserved as unaccepted research.
No additional proof-provider campaign was launched merely to meet a deadline.
