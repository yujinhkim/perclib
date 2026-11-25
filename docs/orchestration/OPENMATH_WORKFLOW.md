# Openmathmodel autoformalization workflow

Scope: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. This implements the
proof dependency-graph and frozen-anchor part of the author's *Autoformalization is now very easy*
(https://www.scottnarmstrong.com/2026/10/autoformalization-is-now-very-easy/), adapted to
Openmathmodel rather than Claude/ChatGPT role names. It is a working policy, not a claim that the
paper is formalized.

## 1. What already exists and what is added

Keep the existing effective source audits, errata registers, source-specific coverage documents,
independently checked proof packages, cached builds, and external Git history. Do not infer
coverage from module names, file counts or build counts.

Add the missing constitutional layer, in this order:

1. source transcription and semantic definitions checked against the primary PDF;
2. sealed definitions in literal `def` files, one declaration per file, with hashed carriers;
3. exact source-facing theorem statements, each in its own file in `Orchestration/Frozen/`;
4. one independent refute-first source review per accepted statement;
5. a manifest recording approval, identity, definition closure, prefixes, suffixes, deterministic
   hashes, provider module, provider export and draft quarantine;
6. a source-level dependency graph with ordinary step, application, route, external and
   standing-assumption nodes, plus independent slice and global reviews;
7. proof providers below the anchor in the import DAG;
8. seal, rebuild, axiom audit, kernel replay and independent source re-audit before `PROVED`.

A temporary elaboration check is not source approval. A scratch report or declaration containing
an ordinary `sorry` is not evidence at all. `DRAFT_SORRY` is allowed only where the manifest says
that exact text is registered. Frozen and provider imports may not leak unfinished anchors into
production code.

## 2. Openmathmodel adaptations

- **Orchestrator:** this agent maintains shared definitions, the manifest, central database,
  branch coordination and source-fidelity decisions.
- **Openmathmodel subagents:** use distinct source slices or independently argued reviews, not
  different proprietary role labels. Their prose is untrusted input. Their accepted result must be
  checked by the orchestrator before use. A submission from an abandoned direction may be mined but
  must be independently rebuilt before being described as a result.
- **Independent review:** a different worker or an independent refute-first pass is required. A
  self-review is not independent. A fresh reviewer identifies actual passages and binders checked;
  topology and proof completeness are separate questions.
- **Machine policy:** this VM has four cores and about 15 GiB RAM. Research/review agents may work
  concurrently, but package-wide builds are owned by the coordinator and serialized. Focused
  elaboration uses the pinned toolchain and one targeted check per worker. Preserve existing caches
  and do not switch/take over other sessions' build processes.
- **Persistence:** Openmathmodel background jobs and reminders provide the long-running mechanism;
  no tmux setup is required. GitHub writes are made only through the available repository connector,
  with exact commits and post-push fetch checks.
- **Errata:** keep using `wiki/errata/*.json` with provisional status until the author explicitly
  confirms the source interpretation. Local repairs to my statements and abandoned proof attempts
  are not source errata. Real source changes require versioned anchors and corresponding evidence.

## 3. Literature and existing PercLib status

The author now permits cited literature rather than re-proving it. Named results from literature
used by Hutchcroft, already formalized results in PercLib, and canonical objects whose canonical
characterization is supplied by a cited result are explicit graph leaves. Use the existing PercLib
export whenever it really matches that result. Do not reproduce a library proof for ceremony.

An external leaf records source/edition, exact claim, object or normalization data, and status.
It never substitutes a generic `Input` proposition for the theorem being proved. A group,
normalization, construction or uniqueness result must still have the right mathematical definition
and, if source uniqueness is required, its sorry-free characterization or that characterization as
an explicit external input. Empty wrappers, fallback zeros, unused carrier defaults, or invented
hypotheses are not literature.

Overall `PROVED_MODULO` remains visible and separate from unconditional `PROVED`. Conditional
components are internal results only; they cannot close a source-facing node.

## 4. Current initial checkpoint

- Two literal sealed definitions (`SourceNorm`, `SourceModel`) and their supporting structures are
  built with the source normalization, unit-volume ball, homogeneity and kernel error constraints.
- Two theorem anchors, `hutchcroft.i.1.6` and `hutchcroft.i.1.15`, elaborate with only their exact
  registered draft warning. They are not proved and are not imported into production code.
- `python3 scripts/check_semantic_closure.py --root . --manifest \
  docs/orchestration/FROZEN_ANCHOR_MANIFEST.json` pins the source-import closure of the
  four manifest anchors. Scope: 17 files for `SourceNorm`, 19 for `SourceModel`, and 44
  for each theorem root. Every non-proof repository import of the declaration file is
  mechanically covered, not merely an author-selected subset. The wrapper then delegates
  to the original frozen guard after removing the extension metadata. A closure-only
  `--skip-core` run returns status 3, not a combined pass. These remain current-byte
  checks, not proof, elaboration, ABI-generation, approval or source-fidelity judgments.
- The production root imports semantic definitions through
  `PercLib/CriticalLRP/Orchestration.lean`; it does not import Frozen/Provider quarantine.
  CI checks that closure with `--exclude-quarantined`, then builds the two frozen anchors
  and their providers directly with the registered draft warnings.
- The graph's manifest hash and approved anchor bytes are distinct. Changing the manifest
  metadata requires updating the graph's pin, but it does not by itself authorize a change
  to a frozen declaration.
- Source-level critical-parameter positivity/finiteness is in
  [Derived critical point](DERIVED_CRITICAL_POINT.md). These are ordinary mathematical
  proof obligations below both moment roots, not new root premises or completed Lean proofs.
- I.1.9 and I.1.17 are not yet frozen roots. The superprocess carrier, canonical-measure details and
  weak/vague topology still need anchor review.
- The source graph, its coverage manifest and independent global review are not yet published.

Required status fields at this checkpoint:

```text
DRAFT_ANCHORS: 2 -- Frozen/HighDimensionalMoments.lean, Frozen/CriticalDimensionMoments.lean
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN: 0 -- no theorem is marked PROVED
```

## 5. Graph, proving, and closing

Every graph edge cites its consumer use site. Alternatives are separate `route` nodes. Released
graphs are amended, not silently rewritten. A semantic change to an anchor creates a versioned
successor and invalidates dependent evidence.

Before a node becomes `PROVED`, the checker confirms that the exact approved statement is unchanged,
its provider compiles, its axioms are reported, the source audit is repeated, and every module is
kernel-replayed. A source-reviewed `PROVED_MODULO` node displays its external leaves. Afterwards
run dead-code review, measure elaboration on affected targets, make only measured improvements,
rebuild, and compare before/after results. No proving status is inferred from elaboration alone.
