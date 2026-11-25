# Initial work programme and contributor protocol

These are **proposed work-package IDs**, not live GitHub issue numbers or assignments. Only tasks whose prerequisites and statements have been agreed should be marked ready. Subdivide large packages into proof tasks before assigning agents.

## 1. Architecture and source work

| ID | Work package | Depends on | Acceptance criterion | Suggested owner role |
|---|---|---|---|---|
| ORG-01 | Establish human roles, task claims, review responsibilities, and repository enforcement | None | Named maintainers, one authoritative task board, known branch-protection capabilities, documented merge responsibility | Mathematical lead + integration maintainer |
| SRC-01 | Inventory every precise assertion in the uploaded notes | Mechanical inventory supplied | Every source region reviewed; compound statements split; proof claims and quoted inputs included; definitions, conjectures, corrections, and unresolved formulations explicitly classified | Source reviewers |
| SRC-02 | Fix Grimmett edition and produce the complete source inventory | Access to the agreed edition | All chapters, appendices, exercises, examples, and precise prose covered with edition-specific locators | Source reviewers |
| SRC-03 | Fix Heydenreich–van der Hofstad edition and inventory it | Access to the agreed edition | Distinguish published book from March 2017 manuscript; include survey/related-model chapters, exercises, and open problems | Source reviewers |
| SRC-04 | Establish the long-range research corpus | Initial bibliography | Versioned source register with corrections, older foundational results, newer extensions, and a procedure for finding omissions | Area maintainers |
| ARC-01 | Review core mathematical conventions | Representative items from SRC-01–04 | Agreed models, cardinalities, finite/infinite criticality, finite-volume observables, parameterisations, asymptotics, and explicit non-vacuous examples | Mathematical lead + Lean steward |
| DOC-01 | Specify assertion, occurrence, proof-route, and mapping records | ARC-01 | Stable-ID rules; per-mapping review evidence; correction history; separate mathematical and formal statuses; small machine-readable examples | Exposition editor + Lean steward |
| DOC-02 | Build the twelve-page wiki design prototype | DOC-01 | The navigation tasks in WIKI_ARCHITECTURE pass; one source shared across several routes; alternative proofs, a corrected claim, a conditional statement, and an open problem remain distinguishable | Exposition editor |
| ENV-01 | Strengthen verification coverage and contributor build setup | Existing pinned project | Production-module coverage, transitive axiom audit, reproducible local instructions, final CI gate, and truthful revision-linked status | Lean steward |

SRC-01 is a semantic inventory, not rerunning the supplied parser. SRC-02 and SRC-03 are broad source-audit packages that should be divided by section with independent review. The mathematical organisation may evolve as these audits reveal shared interfaces.

## 2. First formal slice

| ID | Work package | Depends on | Acceptance criterion |
|---|---|---|---|
| API-01 | Implement the minimal configuration and edge interface | ARC-01, ENV-01 | Countable/finite independent coordinates; undirected non-loop bonds; explicit graph adapter; no host local-finiteness assumption; site and finite-graph use cases inform the design |
| PRB-01 | Adapt existing product probability APIs | API-01 | Arbitrary edge marginals, finite cylinder formulae, coordinate independence, probability-measure instance, finite restriction compatibility |
| EVT-01 | Connectivity, path witnesses, and measurability | API-01, PRB-01 | Connectivity agrees with graph reachability; finite simple-path witnesses; measurable cluster events; self-connectivity included |
| OBS-01 | Extended cluster volume and susceptibility | EVT-01 | Expected cardinality equals the sum of connection probabilities; infinite values handled honestly; finite and box-restricted variants separated |
| PATH-01 | Weighted path and walk sums | API-01 | Simple-path events have the distinct-edge product formula; walk-weight recurrence and geometric bound are proved with nonnegative sums |
| PILOT-01 | Complete the row-sum susceptibility theorem | PRB-01, EVT-01, OBS-01, PATH-01 | The exact contract in PROJECT_PLAN §7.1 is proved, including almost-sure finiteness of every cluster |
| CRIT-01 | Intensity family and threshold specialisation | PILOT-01 | Explicit root/global extended thresholds; `M=0` handled; lower bound for finite `M>0`; no unsupported criticality conclusion |
| GEO-01 | Instantiate the pilot in different geometries | PILOT-01, CRIT-01 | Finite graph, tree, Euclidean summable kernel, and hierarchical kernel instances compile with common definitions |
| DOC-03 | Complete the pilot's wiki and source correspondence | DOC-02, PILOT-01, GEO-01 | Exact statement, proof idea, assumptions, source mappings, backlinks, Lean declarations, and build evidence agree |

The mathematical hypotheses must be in each task brief, not inferred from this table. The path-sum and observable work can proceed in parallel once the minimal interfaces are stable. Changes to the shared model remain coordinated.

## 3. The next ready-task frontier

These are programme fronts to decompose, not single agent jobs:

- **Finite correlation inequalities:** weighted Harris/FKG, then the exact BK/Reimer forms needed by selected results, with witness conventions and extension to countable events.
- **Exploration and resampling:** revealed-coordinate sigma-algebras, conditional independence, decision trees, ghost coordinates, and carefully scoped finite examples before infinite stopping rules.
- **General critical theory:** finite-size criteria, sharpness, moment/tail bounds, tree-graph estimates, and universal tightness. Keep exponential spatial decay separate from cluster-size conclusions in long-range models.
- **Branching and analytic infrastructure:** concrete tree calculations, generating functions, regular variation, Tauberian conversion, asymptotic inversion, moment determinacy, and ODE comparison. Start with precise lemmas serving actual targets.
- **Geometry:** hierarchy blocks and cardinalities; lattice shells and summability; planar embeddings and duality; finite tori and hypercubes; intrinsic graph distance.
- **First critical flagship:** decompose the hierarchical two-point theorem's complete prerequisite closure and compare it with other ready critical targets. Do not combine its kernel assumptions with those of later volume-tail theorems.
- **Textbook model tracks:** basic sub/supercritical lattice theory, planar arguments, triangle-condition consequences, lace expansion, IIC, random walks, and finite random-graph scaling, according to reviewed dependencies and maintainer capacity.

Generic operator inequalities, invariant traces, and mass-transport arguments appearing in the notes should be located in the shared analytic/probabilistic infrastructure rather than hidden inside a paper-specific file. Related systems from the books get explicit model laws; reuse event-level facts without assuming independence where it does not hold.

## 4. Required task brief

Use this as a compact issue template. It is intentionally a mathematical specification before it is an agent prompt.

```text
Task ID and title:
Human owner and reviewers:
Base commit / Lean / mathlib revision:

Mathematical objective:
Canonical assertion IDs:
Source occurrences, editions, and locators:
Exact hypotheses, conclusion, and conventions:
Definition or source-correction questions already resolved:

Prerequisite assertions and tasks:
Approved interfaces / declaration signatures:
Files owned by this task:
Shared files that require coordination:
Allowed freedom in helper statements and proof strategy:

Deliverables:
- Lean definitions/proofs
- Source-correspondence records
- Relevant wiki explanation and proof route
- Validation evidence for the exact submitted revision

Stopping / escalation conditions:
- Missing mathematical prerequisite
- Proposed change to a shared definition or target hypothesis
- Source ambiguity or suspected counterexample
- Agreed resource/time budget reached

Handoff:
- Commit and changed files
- What is proved and what remains
- Commands run and actual outcomes
- Missing dependencies and useful failed approaches
```

Routine implementation choices and helper lemmas stay within the contributor's authority. A missing source hypothesis, a change of model, or a shared semantic interface requires explicit resolution, not an agent's silent substitution.

## 5. PR completion checklist

A mathematical PR is ready when its statement and relevant definition bodies have been reviewed; its source mappings are precise; it adds no unreported assumptions; its production modules are imported and audited; the full required build succeeds on the final revision; and its natural-language explanation has been updated where affected.

The handoff must say whether the result is an exact source theorem, a justified equivalent formulation, a specialisation, or a partial reduction. A custom hypothesis that simply assumes the missing theorem cannot be used to mark the original source complete.

At merge time, check the combined current-base revision. Review changes to CI, axiom checks, core definitions, and the manifest separately from ordinary proof development. Keep contributor identity and AI assistance visible in the PR, while crediting specification, proof development, review, and exposition as distinct work.

## 6. Decisions that remain to be made

The proposal supplies defaults so that planning can proceed. The first implementation tasks should settle the exact book editions and accessible source copies; the initial Lean steward and integration maintainer; repository protection available under the current GitHub plan; the source-correction approval convention; and the renderer chosen after the wiki prototype.

These decisions do not require changing the source-based mathematical scope. They make the agreed goal executable and reviewable. Repository publication, ownership transfer, invitations, and paid infrastructure are separate actions.
