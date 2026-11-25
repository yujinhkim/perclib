# Source-packet review and importer status

This is a campaign checkpoint, not a published dependency graph or a Lean proof.
Nested `.scratch/` adapter inputs and normalized candidate files are not graph
production data. Every imported record remains `PROPOSED`; source location,
statement fidelity, dependency ownership, independent review, and Lean proof
status are separate properties.

## Parser and checker checks

`scripts/import_source_packets.py` now recognizes the three packet formats
currently being reviewed. Its regression tests cover the exact
`EDGE`/`END` fixture, unknown owners, unterminated blocks, missing or truncated
statements, actual HTML span resolution, and packet counts. The packet-reader
counts reproduce the research packets' declared counts:

- I.1: 27 records / 56 structured edges;
- I.2/I.3: 39 records / 37 one-line edges;
- I.5.3-I.5.4 main: 87 records / 134 table edges;
- their deferred I.1.9/I.1.17 package: 3 records / 23 edges.

Those counts do **not** imply a complete or acyclic source topology. The I.5
main packet has blank conclusions and multiple truncated mandatory fields, so
normalization deliberately rejects it. Earlier zero-edge adapter output was
invalid and has not been used as graph evidence.

`proof_depgraph.py` no longer dereferences unknown cross-slice names while
computing a partial packet's closure. It reports their dangling-dependency
diagnostics rather than crashing. This is deliberately not permission to remove
the missing source inputs or manufacture placeholder nodes.

## Native validation of the latest candidate set

The interrupted validation has now been completed with the repository's actual
`_validate_node_shape`, `_apply_amendments`, and `_validate_topology` functions.
The reproducible entry point is `scripts/validate_source_packets.py`; its final
scratch report is `.scratch/packet-native-validation/final/report.json`. The
normalizer preserves canonical-text and HTML line layers separately, resolves
numbered and bare native edges, accepts annotated repeated `DEPS`, flattens
compressed scalar/provenance fields, and resolves display tables plus inline
IDs through their actual enclosing blocks. Its 12 regression tests pass.
Private packet count/cycle checkers were not used as evidence of validity.

The repaired candidate inputs and normalized outputs remain under `.scratch/`,
never in the production seed. Raw `.ultramath/` research was not edited.
`NATIVE_CLEAN` means only zero shape/topology diagnostics in this bounded
candidate. It is not source-fidelity approval, independent review, root-closure
review, or Lean proof status. Every node remains `TOPOLOGY_STATUS: PROPOSED` and
every ordinary Lean field remains `NOT_STARTED`.

| packet | records | native edges | result | remaining declared proof input |
| --- | ---: | ---: | --- | --- |
| reviewed I.1 adapter | 39 | 84 | `NATIVE_CLEAN` after adding real provider links | 14 cross-slice obligations already resolved in `combined.md`; source/gap review and a global closure review remain required |
| accepted I.2/I.3 revision | 68 | 93 | `NATIVE_CLEAN` | its 12 literature leaves remain unverified |
| reviewed I.4.1 | 74 | 118 | `NATIVE_CLEAN` | true statement owners normalized; Proposition I.4.2 split into (a)/(b); citation-only third-paper claims remain unverified |
| reviewed I.4.2/I.4.3 | 47 | 117 | `NATIVE_CLEAN` | eight cross-slice links connect to actual I.4.1/I.2/I.3 providers; source/gap review remains required |
| I.5.1/I.5.2 | 52 | 89 | `NATIVE_CLEAN` | none structural; HD-v2 and deferred superprocess semantics stay unresolved |
| I.5.3/I.5.4 | 59 | 71 | one diagnostic | Remark I.5.25 (`I.5.25`) has only an unlocated citation to [87, Ch. III, Thm 4] |

The normalized review artifacts and their current hashes are preserved in
`docs/orchestration/candidates/`; see
[`VALIDATION.json`](candidates/VALIDATION.json). They are review inputs, not a
production dependency graph or accepted topology. The separate provider review
graph `combined.md` has 228 records and 412 edges and passes native validation;
its provisional root closure has 163 nodes, leaving 65 candidate records
outside. That is not global closure or a licence to add missing nodes. The
duplicate-duty audit is in [`MERGE_MEMO.md`](candidates/MERGE_MEMO.md): exact
identity collisions are zero and eight identity renames are explicitly logged,
while semantic overlaps still require independent adjudication. No frozen
anchor, dependency-graph seed, or Lean module was edited for this conversion.

The bounded I.2/I.3 packet therefore now passes the native 68-record/93-edge
gate, validating the earlier bounded acceptance without promoting its source
leaves. The I.1 repair moved route ownership from the `(HD)` assumption leaf to
its consuming frozen root and added three proof-assembly edges. The I.4.2
repair identified 45 records rather than trusting a narrative count, preserved
99 declared dependency pairs, and made every edge consumer explicit; its private
linter had compared only provider multisets and could not check that ownership.
The I.5.3/I.5.4 repair keeps all 59 records but replaces invalid shared route
owners with ordinary source-hypothesis dependencies and assumption leaves.
Case 4's `(Hydro)` content remains verbatim. No placeholder node, arbitrary
witness, silent second route owner, or completion assumption was created.
Additional nodes added by later source reviews are explicitly identified as
derived obligations, refutations, or conditional computations rather than as
source-proven statements.

I.4.4's actual citation-only remark locator is retained, but I.5.25 remains the
one declared missing proof locator among the six bounded slices; its cited
Le Gall text has not been obtained. Nothing else is hidden by a declared-open
flag, and no canonical appendix with the drifted stride-2 mapping has been used
as physical-line evidence. No candidate has been merged into the production
`DEPGRAPH.md`, and no fresh global reviewer has approved this repaired set.
The bounded first-round reviewers were `smwohv6t4`. A second bounded review of
the corrected artifacts is ongoing in `smwoiwd22`.

## Critical parameter and source errata

The small-parameter walk bound and the repaired large-parameter finite-range
square-lattice coupling establish positivity for every `d >= 1, alpha > 0` and
finiteness for `d >= 2`. The use of two linearly independent displacements
`v=e_1` and `w=2e_2` makes the graph embedding injective and its retained edges
distinct and independent. Fresh review refuted an earlier collinear
`(m+n)v` construction: it repeated physical edges and did not transfer infinite
open components to the long-range model. The valid construction uses i.i.d.
thinning and Theorem 10 of Bollobas--Riordan (arXiv:math/0410359v3), read at the
named source. For `d = 1`, the separately cited long-range threshold remains an
open external-input obligation; along the two root domains it is needed only in
the source's asserted `0 < alpha <= 1` range. No general continuity result is
inferred. The exact derivation and its scope boundary are in
[DERIVED_CRITICAL_POINT.md](DERIVED_CRITICAL_POINT.md). This has not been Lean
proved and the external threshold has not been assigned a Lean provider.

The moment-tree indexing correction now records `E = 2n-1` from the degree
sum. It deliberately does not change the coefficient `2^(2n-2)`. The I.4.18
repair uses `ell >= 4` and the two-scale averaged `ell = 3` estimate; the old
single-scale total-triangle-mass argument is not sound. Proposed source errata
remain provisional. The real errata renderer/schema tests were not run here;
node is unavailable in the VM.

## Frozen and proof status at this checkpoint

```text
DRAFT_ANCHORS: 2 -- Frozen/HighDimensionalMoments.lean, Frozen/CriticalDimensionMoments.lean
UNREGISTERED_SORRIES: 0 in the production orchestration modules; scratch candidates are not promoted
DRAFT_IMPORT_VIOLATIONS: 0 in the full wrapper guard at this checkpoint
SEALED_THIS_TURN: 0
```

The two root theorem statements remain unproved. No `TOPOLOGY_STATUS: REVIEWED`
or `GLOBAL_REVIEWER` is set by this importer/checker work. Proof providers must
wait for independently reviewed topology and frozen-anchor fidelity. Named
cited literature and matching PercLib exports may then be used explicitly;
titles alone do not supply mathematical hypotheses.
