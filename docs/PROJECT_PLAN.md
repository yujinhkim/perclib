# A shared formal library of percolation

**Draft proposal, 12 November 2026.** The repository is `tomhutchcroft/lrp`. Critical long-range percolation is a central research programme within a broader percolation library. The uploaded notes and the requested books are minimum coverage commitments; their chapter order does not determine the library or the accompanying wiki.

The original proposal was based on repository revision `c0a3cbf307dca1e2f2b0379cf3c6a8e777ffaa27`. This document records the mathematical and organisational plan; implementation and verification evidence belong to the corresponding changes and build records. The wiki navigation direction was refined on 12 November 2026 to use canonical articles, contextual hyperlinks, backlinks, indexes, and local logical dependencies, without a maintained reading-route catalogue.

Companion documents:

- [Wiki architecture](WIKI_ARCHITECTURE.md): the mathematical information structure, contextual links, typed dependencies, page contracts, and a concrete first prototype.
- [Wiki prototype guide](WIKI_PROTOTYPE.md): the current direction and how to add a canonical article.
- [Initial backlog](INITIAL_BACKLOG.md): work packages, dependencies, acceptance criteria, and a contributor task brief.
- [Source audit](SOURCE_AUDIT.md): the notes inventory, preliminary corrections, and the method for establishing complete coverage.

## 1. The objective and the unit of completion

Build a reusable Lean library and a parallel, carefully edited mathematical reference in HTML. A reader should be able to move between an explanation, an exact statement, its assumptions, proof ideas, applications, source occurrences, and a verified Lean declaration. A contributor should be able to identify a bounded missing result and prove it without inventing an incompatible version of the model.

The reference should support entry at any mathematical concept or result. Canonical articles contain useful local explanations and contextual hyperlinks; generated backlinks expose their uses. Subject and notation indexes and the source concordance provide entry points. Each result can show a small logical dependency neighbourhood, with explanatory relationships and authored proof inputs clearly distinguished from dependencies extracted from a compiled Lean declaration.

The intended corpus includes:

1. Every precise mathematical statement in the uploaded **Critical Percolation, Scaling, and Long-Range Models: A Detailed Expository Draft**, including statements in prose, intermediate calculations, examples, and quoted inputs.
2. Everything mathematical in **Grimmett, Percolation**, provisionally the second edition (1999), including exercises and the related-model material.
3. Everything mathematical in **Heydenreich–van der Hofstad, Progress in High-Dimensional Percolation and Random Graphs** (2017), including exercises, later survey chapters, and statements of open problems.
4. The literature on critical long-range percolation, including original results, corrections, subsequent improvements, and the external mathematics needed to close their proofs.

The book identifications are working assumptions until the precise editions are fixed. The publisher identifies Grimmett's second edition; the other book's author-hosted PDF is a March 2017 manuscript, whose numbering must not be silently equated with the published edition. The publisher contents and author manuscript have been inspected for planning, not exhaustively inventoried. [G], [HH]

The notes are a lower bound on coverage, not a ceiling on subject matter or a prescribed exposition. Planar theory, finite random graphs, branching processes, random walks on clusters, the incipient infinite cluster, and scaling limits are therefore first-class areas. Related models occurring in the books remain in scope; they should enter through appropriate interfaces, rather than forcing independent-edge assumptions onto dependent models.

**Completion is tracked by mathematical assertion and source occurrence, not by paper title or lines of Lean.** One theorem may cover several occurrences. Conversely, one paragraph may contain several separate assertions. An original theorem and a stronger later theorem are not automatically the same item: the original statement must be recovered with its exact conventions.

For rigorous assertions, completion means a checked proof of the faithful statement with all necessary external inputs proved or reused from trusted dependencies. Definitions are complete when their mathematical meaning has been reviewed, their Lean implementation checks, and any identification with a source's convention is justified. Open conjectures receive precise formal statements and an explicit open status; they are not added as axioms. A false or ambiguous draft assertion receives a documented correction or unresolved issue, never a silently weakened replacement. Intermediate assertions remain coverage obligations even if the final theorem is proved by a different route. They may be discharged by private checked lemmas or dedicated source-concordance obligations without becoming permanent public API.

## 2. What the existing projects teach us

Armstrong's October workflow separates statement auditing from proof production and gives agents bounded work below a small set of agreed interfaces. His stochastic-homogenisation project also maintains explicit manuscript-to-Lean correspondence, including deviations. We should adopt those practices while preserving this repository's strict production axiom policy. His timings are experience reports, not an estimate for this corpus. [A1], [A2]

The useful lesson from large community projects is that architecture and review are continuing work. Mathlib asks for coherent contributions with maintainer review; the FLT project coordinates work through tasks and branches. A blueprint supplies an explanatory dependency map, but declaration-name checks alone do not establish that a theorem is proved. [M1], [M2], [F], [B]

Our adaptation is a **federated contribution process with one integration authority**. Each person's agent can plan and execute its assigned task. It cannot independently redefine the shared foundations, claim the same task as another worker, or declare the entire project complete. Human mathematical judgement determines fidelity; Lean determines whether the formal proof checks.

Do not install another project's full agent instructions as policy without review. Armstrong's published skills were inspected at commit `1837b95b3d5a9fd8d311367603902ad7fe261adf`; any later adaptation should pin the version and preserve attribution. The plan does not depend on particular model providers, subscription tiers, or permissive execution settings. [A3]

## 3. Organise around objects, observables, and reusable mechanisms

Use a modest dependency-oriented structure. The following are responsibility boundaries, not a demand to create every directory immediately.

| Layer | Mathematical responsibility | Illustrative location |
|---|---|---|
| General foundations | Missing generic graph, measure, series, asymptotic, and analytic lemmas; no percolation dependencies | `Lrp/ForMathlib/` |
| Probability and exploration | Product laws, coupling, independent coordinates, conditional laws, decision trees, entropy, size biasing | `Lrp/Probability/` |
| Deterministic geometry | Paths, cutsets, automorphisms, lattices, planar embeddings, hierarchical balls, finite tori | `Lrp/Geometry/` |
| Configurations and observables | Bond/site events, connectivity, clusters, restricted events, tails, susceptibility, magnetisation, diagrams | `Lrp/Percolation/` |
| General mechanisms | Correlation inequalities, pivotality, Russo formulae, sharpness, mass transport, tree-graph bounds, universal tightness | `Lrp/Inequalities/`, `Lrp/Critical/` |
| Analytic mechanisms | Regular variation, Tauberian arguments, convolutions, Fourier estimates, differential inequalities, moment recursions | `Lrp/Analysis/` |
| Model theories | Trees, planar models, high-dimensional lattices, finite random graphs, Euclidean and hierarchical long-range models, related systems | `Lrp/Models/` |
| Limits and geometry | IIC constructions, cluster metrics, random walks, random measures, superprocess and finite-size limits | `Lrp/ScalingLimits/` |
| Source correspondence | Thin theorem specialisations and source-specific obligations using the shared library | `Lrp/SourceChecks/` |

The wiki is a network of canonical mathematical articles. Readers enter through a concept, model, method, result, index, search query, or source occurrence, then follow contextual hyperlinks and backlinks. This does not require maintained learning sequences. A conceptual link, an input to an authored proof, a compiled declaration dependency, and a Lean module import express different relationships. The [wiki design](WIKI_ARCHITECTURE.md) keeps them separate and exposes a bounded local view around the current assertion.

### 3.1 Shared model contracts

Start from independent coordinates on a finite or countable index set, reusing mathlib's product-measure constructions. Independent bond percolation is an instance on unordered non-loop edges; site percolation uses vertex coordinates. Finite random graphs are finite-host instances. An adapter should connect the chosen bond representation to mathlib's graph paths and connectivity.

For the first bond interface, allow an arbitrary profile `q(e)` in `[0,1]`. The intensity family is then a specialisation:

$$q_\beta(x,y)=1-\exp(-\beta J(x,y)).$$

Use finite nonnegative intensities and finite nonnegative beta at this stage. Keep symmetry, pointwise summability, a uniform row bound, invariance, and geometric decay as distinct hypotheses. Papers using a linear family `p D(x-y)` need their own family or an explicit comparison theorem: a fixed linear family is not generally the same as a fixed-kernel exponential family after renaming the parameter.

Mathlib already supplies `Measure.infinitePi`, homogeneous random subsets, independence, and graph foundations. Initial reconnaissance at the repository's exact mathlib revision found these building blocks; it did not establish the absence of every useful percolation lemma. Audit the actual declarations before implementing replacements. [M3], [M4]

Dependent or directed models in the wider corpus should reuse the configuration, event, and graph interfaces where appropriate, with their own laws and hypotheses. The property of being an independent product measure must remain explicit. Avoid one enormous class that bundles all the estimates a future theorem is supposed to prove.

### 3.2 Conventions that must be settled before many agents contribute

| Question | Proposed policy and reason |
|---|---|
| Infinite potential degree | Permit it. A long-range host can have infinitely many possible neighbours; local finiteness of the sampled open graph is a theorem under summability. |
| Cluster volume | Use extended cardinality and nonnegative extended expectations until finiteness is proved. Ordinary `Nat.card`/`Set.ncard` are unsuitable defaults for possibly infinite clusters. |
| Critical thresholds | Distinguish root and global thresholds, and allow infinity for intensity models. Prove equality under the appropriate support/invariance hypotheses. |
| Finite-size criticality | Give finite graphs their own critical-window and susceptibility-normalisation definitions. An infinite-cluster threshold cannot describe an Erdős–Rényi or torus critical window. |
| Evaluation at criticality | Prove the intensity threshold finite before converting it to a real parameter; do not conceal infinity through a conversion. |
| Finite volume | Distinguish the cluster using only edges within a region from the full cluster intersected with that region. Include restriction and exhaustion theorems. |
| Spatial versus intrinsic geometry | Use separate distances, balls, arm events, and exponents. |
| Truncation and conditioning | Distinguish an edge cutoff, an induced finite box, a conditioned law, a size-biased law, and a full infinite-volume law. |
| Asymptotic statements | Separate logarithmic exponent limits, bounds up to constants, asymptotic equivalence, and exact constants. Specify where constants are uniform. |
| Correlation length | Keep competing definitions separate until their comparison is proved. Do not silently identify second-moment, exponential, and cutoff scales. |
| Parameter names | Distinguish the intensity beta from the order-parameter critical exponent, and record each source's one-arm exponent convention. |

Examples and elementary identities should accompany these definitions: the empty configuration, self-connectivity, finite graphs, a tree, and summable Euclidean and hierarchical kernels. These are useful mathematical checks of meaning, rather than a large collection of implementation-shaped tests.

## 4. A theorem registry and a source concordance

Maintain three separate kinds of record, with permanent IDs independent of filenames and theorem numbering:

- **Mathematical object or assertion:** the reviewed meaning, explicit assumptions, model and regime, canonical notation, and any Lean declarations implementing it.
- **Source occurrence:** exact source edition or snapshot, locator, surrounding assumptions, and a mapping to one or more assertions. Record whether the correspondence is exact, by proved equivalence, a specialisation, a correction, or still unresolved.
- **Mathematical proof:** target assertion, logical prerequisites, proof strategy, provenance, and planned, implemented, or reviewed status. Alternative proofs may use different intermediate results. A proof-route record describes an argument, not an ordered reading itinerary.

A small YAML/JSON schema and repository review are enough initially. Generate indexes, backlinks, source concordances, local dependency panels, and coverage reports from these records and the actual article links; do not maintain a second handwritten spreadsheet with competing statuses. Canonical page links and assertion anchors must survive moves or renames.

Maintain compiled dependency evidence separately: record the exact checked revision, declaration, whether references arise in its type or proof term, and whether the displayed relation is direct or transitive. An authored proof sketch must never be presented as compiler-extracted evidence. If extraction has not run, show that limitation explicitly instead of displaying an empty formal dependency list.

Record source status, semantic-review status, and formal-proof status separately. A theorem can have a perfectly reviewed statement but no Lean proof. An explicitly conditional mathematical theorem can be completely proved. A reduction that assumes an unproved external theorem does not complete the corresponding unconditional source theorem. A conjecture can have a checked statement without being a proved result.

For every item claimed as verified, retain the declaration names, defining modules, exact repository commit, toolchain and dependency lock, successful build, axiom result, and semantic reviewer. Correspondence reviews belong to each source-occurrence–assertion mapping and each assertion–Lean mapping at identified revisions; approving one does not approve all other mappings. Definition changes and changes to assumptions can invalidate downstream correspondence even when theorem text does not change; flag these for re-review. This is a review aid, not a claim that software can decide semantic fidelity.

CI should produce a verification manifest after the build, keyed by the checked commit and dependency lock. Authored registry files contain mappings and review records, not a self-certified `verified: true` flag or the hash of their own future commit. A displayed verification status combines matching build evidence with current correspondence review. A manually reviewed import manifest is enough to establish complete audit coverage for the pilot before this process is fully automated.

The uploaded file is an immutable baseline snapshot with SHA-256 `61c11fcbd2d4ac600e9b96b6b1a81c399b6e049dd208e8790d5f06e1b02b5fd4`. Its mechanical inventory contains **10 numbered chapters, 56 sections, 45 named statements, and 698 outer displayed-math blocks**. These are document counts, not a count of mathematical obligations. Much of the mathematics is in prose and proofs; see [the source audit](SOURCE_AUDIT.md).

For the books, pin editions and create section-by-section inventories, including exercises, appendices, related-model chapters, and precise claims in survey material. For the research literature, follow citations backwards and forwards, reconcile errata and alternative proofs, and publish a versioned corpus register. A seed bibliography is not an exhaustive bibliography. New papers extend the register without redefining the identities of existing results.

## 5. How people and agents work together

### 5.1 Responsibilities

| Role | Responsibility |
|---|---|
| Mathematical lead | Tom initially; scope, important statement decisions, and adjudication of source corrections. |
| Lean/library steward | Shared definitions, reusable APIs, dependency choices, performance, and eventual upstream work. |
| Area maintainers | Review within probability, planar theory, high-dimensional theory, random graphs, long-range theory, or limits as teams form. |
| Integration maintainer | Task ownership, shared-file changes, merge order, conflicts, release evidence, and the current ready-task frontier. |
| Exposition editor | Canonical explanations, contextual links, aliases, coherent local dependency views, and agreement between wiki statements and the formal library. |
| Contributor and supervising human | One accountable owner for each task and PR, including work produced by that person's agents. |

People can hold multiple roles initially. The essential early resource is someone able to review Lean architecture as well as mathematicians able to review statements. Additional proof agents should be added at the rate at which their work can be specified and reviewed.

### 5.2 Task protocol

Use one GitHub issue per coherent work package. The issue's human assignee is the authoritative owner. A contributor requests or accepts a task; the integration maintainer confirms the claim before parallel work starts. Do not rely on several agents simultaneously seeing an unassigned issue and assuming ownership.

Each brief contains the target assertion IDs, source locators, exact base commit, approved interfaces, prerequisite tasks, owned files, permitted shared-file edits, expected deliverables, validation commands, and a stopping condition. If an agent needs a missing lemma or a different interface, it returns a precise dependency request rather than quietly changing the target. Claim check-in intervals are agreed by the team; blocked work is visible and can be reassigned with a handoff.

Suggested lifecycle: **needs specification → ready → claimed → in progress → review → merged**, with an explicit blocked state and reason. Source and proof statuses live in the registry; task status lives on the issue. No duplicate claims ledger is needed.

Give each contributor a separate branch/worktree and build directory, even on a shared server. Avoid several workers editing one checkout or one mutable `.lake` directory. Agents read the common repository instructions, their task brief, and relevant architecture decisions at the start of a session. They finish with a durable handoff: exact commit, changed files, completed results, build evidence, unresolved obligations, and useful failed approaches.

### 5.3 PR size and shared interfaces

Prefer one coherent definition/API change or theorem family per PR. Merge shared infrastructure early, then let dependent tasks build on it. Large dependent developments can use explicit stacked branches, with the integration maintainer controlling the order and checking the final combined revision.

Freeze only important interfaces: configuration laws, core observables, major hypotheses, and the main statements on which other tasks depend. Helpers remain flexible. Changing an approved interface requires a small design note explaining the mathematical reason, downstream impact, migration, and correspondence changes. Do not freeze thousands of local helper statements before trying the first proof.

A PR should state the mathematical result, source mapping, new assumptions or normalisations, reusable contributions, AI assistance, validation revision, and remaining limitations. Automated summaries are helpful internally, but the supervising human must understand and take responsibility for the submitted work.

### 5.4 Reviews

Important definitions and source-facing results need both a mathematical-fidelity review and a Lean/library review, ideally independent of the producing agent. Routine helper lemmas can use lighter review. The semantic check includes quantifier order, non-vacuity, parameter ranges, uniform constants, bundled assumptions, and the bodies of definitions on which the statement relies. Agreement between two agents is useful evidence for review, not a substitute for it.

Source corrections are recorded with the original assertion, the issue, proposed precise replacement, justification, and approval. The uploaded draft already contains elementary cases where literal proof is impossible; the [audit examples](SOURCE_AUDIT.md) show why this process is necessary. Preserve the draft and its provenance rather than silently rewriting it.

## 6. Proof integrity, GitHub, and the build loop

The current repository pins Lean `v4.35.0` and mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its existing workflow runs `lake build --wfail` and an axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`. The successful baseline [run](https://github.com/tomhutchcroft/lrp/actions/runs/43308413050) checked the initial smoke-test theorem, not any percolation theorem.

Keep production free of `sorry`, `admit`, and extra axioms. Work-in-progress proofs may live on clearly marked branches; statement-only specifications can be represented without pretending to have proof terms. A missing dependency is never discharged by adding an axiom or by importing an admitted lemma. All completed source obligations must be in the compiled and audited import closure.

Proposed additions, in a separate implementation PR:

1. Enumerate production Lean modules and check that the public root or another explicitly audited target includes all of them. The existing audit only sees declarations actually imported into its environment.
2. Audit transitive axiom dependencies across all project modules, including source-concordance helpers. A name-existence check or text search for `sorry` is insufficient.
3. Validate registry IDs, canonical anchors and redirects, source links, Lean declarations, and wiki links; generate backlinks and proof badges from their authoritative inputs. Keep authored mathematical links separate from extracted declaration dependencies, and tie formal evidence to the built revision. Leanblueprint's `checkdecls` checks declaration existence, not proof completeness. [B]
4. Review changes to foundational definitions, workflows, audit code, and dependency locks. Keep dependency upgrades separate from mathematical PRs.
5. If checks are split into jobs, use an always-running final gate that requires the necessary jobs to have actually succeeded. A skipped GitHub job can otherwise report success. [GH3]
6. Build the final merge candidate, and periodically run a clean build. Record toolchain and dependency revisions with releases; use caches to accelerate compilation, not as the sole evidence of a clean build.

Each worker needs a warm Lean environment with fast local or server compilation. In this interface, the existing project has been compiled through GitHub Actions. That is a workable integration check, but a slow inner loop for hundreds of tactic attempts. Contributors can use their preferred agent interface provided it can edit a checkout and invoke the pinned compiler. Shared servers need isolated builds and concurrency limits set from measured memory and compilation behaviour.

Propose protected `main`, required verification checks, qualified review, and no direct worker pushes to `main`. Actual enforcement must be checked against the account and repository settings: GitHub's private-repository protection features depend on the plan. A `CODEOWNERS` line with two people requires either person's approval, not both; two-role review needs an explicit process or additional check. Agent instructions are not access controls. [GH1], [GH2]

The repo can remain under its current name and owner initially. If the collaboration becomes a continuing institution, consider an organisation with several maintainers and continuity of access. No repository transfer, visibility change, purchase, or invitation is part of this planning proposal.

## 7. The first complete slice

Before distributing entire chapters, complete a small piece that crosses the whole system: source occurrence → reviewed statement → shared definitions → Lean proof → wiki explanation → cross-links → build evidence.

### 7.1 Recommended probability pilot

On a countable undirected simple host, let `q` map edges to `[0,1]` and use the independent product law with those edge probabilities. Extend the profile to vertex pairs by zero on nonedges, including the diagonal. If

$$0\le m<1,\qquad \sum_w q(v,w)\le m\quad\text{for every }v,$$

prove

$$\chi(v)=\sum_w\mathbb P(v\leftrightarrow w)=\mathbb E|K_v|\le\frac1{1-m},$$

and that almost surely every cluster is finite. The equality and inequality use extended nonnegative quantities. No transitivity or host local finiteness is required.

The proof uses a simple path witnessing each connection, independence of its distinct edges, a union bound, an upper bound by weighted walks, and a geometric series. It must not multiply probabilities along a walk as if repeated edges were independent. Countability upgrades the individual-root conclusion to one probability-one event for all vertices.

For the intensity family, a finite nonnegative real bound `sum_w J(v,w) <= M` at every vertex gives `chi_beta(v) <= 1 / (1 - beta*M)` when `beta*M < 1`, and a lower bound `1/M` for every root threshold and the global threshold when `M > 0`. Handle `M = 0` separately with infinite threshold. This proves neither finiteness of the threshold nor behaviour at criticality. The elementary threshold argument is a standard input in the long-range literature. [P1]

Instantiate the pilot for a finite graph, a tree, a summable Euclidean kernel, and a hierarchical kernel. This checks whether the common interface serves the expanded corpus. In parallel, the wiki prototype should explain susceptibility, the product law, finite-volume distinctions, and the source mappings for this result.

### 7.2 First critical target and independent early tracks

The 2021 hierarchical two-point paper remains an attractive first critical target, subject to the initial dependency audit. Start with Theorem 1.1's averaged estimate, then Corollary 1.2's pointwise version under radial symmetry. Track its BK, sharpness, finite-size, and cluster-tightness inputs explicitly. It is a substantial milestone, not an isolated short proof. [P2]

This target does not organise the whole project. Once the common interfaces work, other teams can pursue finite correlation inequalities, tree/branching calculations, basic lattice phase transition results, planar geometry, and generic analytic lemmas. Select tasks by shared benefit, prerequisite readiness, and available reviewers.

## 8. Programme tracks and dependencies

| Track | Substantive milestones | Shared inputs |
|---|---|---|
| General percolation | Coupling, correlation and disjoint-occurrence inequalities, pivotal formulae, sharpness, uniqueness, subcritical and supercritical theory | Product/event API, graph geometry, finite approximations |
| Branching and analysis | Tree models, generating functions, regular variation, Tauberian conversion, moment/tail inequalities | Probability, series, asymptotics |
| Planar theory | Duality, crossings, RSW, gluing, arm and hyperscaling results, continuum statements under their actual hypotheses | Embeddings, event algebra, correlation inequalities |
| Mean-field mechanisms | Triangle and tree-graph bounds, susceptibility and magnetisation inequalities, entropy/OSSS methods, intrinsic geometry | General inequalities, exploration, diagrams |
| Lace expansion | Expansion identities, remainder control, diagram estimates, Fourier analysis and bootstrap; later nonbacktracking refinements | Random walks, convolution, general percolation |
| Finite random graphs | Critical windows, finite-size scaling, high-dimensional tori, hypercube and Erdős–Rényi comparison | Finite graphs, exploration, moments, finite triangle criteria |
| Hierarchical long range | Two-point estimates, cluster-volume laws, renormalisation, marginal logarithms | Exact ball geometry, tightness, sharpness, moment methods |
| Euclidean long range | Critical bounds, averaged and pointwise estimates, localisation, modern real-space and lace routes | Lattice analysis, common critical theory, relevant model inputs |
| Limits and random walks | IIC, random walks on clusters, cluster metric limits, superprocess and spatial moment limits | Tightness, probability convergence, geometry and model estimates |
| Related models | The rigorous material in the requested books on oriented, dependent, invasion and other systems | Shared objects where valid, separate laws and hypotheses where needed |

Maintain theorem-level dependencies, including alternative proof routes. Paper boundaries can create misleading apparent cycles. For example, a paper can prove a consequence of a hydrodynamic condition while a later paper establishes that condition; generic inequalities from another part of the series may be independent of that part's main hypotheses.

Keep the current long-range regime map exact. The recent trilogy has explicit two-point, localisation, hydrodynamic, and dimension hypotheses; register them rather than replacing them with a conjectural universal regime rule. In particular, the upper-critical regime `d = 3 alpha < 6` and the `alpha = 2` marginal lace-expansion regime are different targets. [P3], [P4], [P5], [P6]

### Seed literature, to be expanded into a complete register

The initial bibliography should include BK/Reimer and correlation inequalities; the Aizenman–Barsky, Menshikov, and Duminil-Copin–Tassion sharpness routes; Aizenman–Newman and subsequent triangle-condition results; Berger's corrected critical long-range argument; Heydenreich–van der Hofstad–Sakai and Chen–Sakai on lace expansion; Hulshof on long-range arms; the hierarchical two-point and cluster-volume papers; isoperimetric, averaged, and pointwise Euclidean estimates; and all three parts of Critical Long-Range Percolation. The books and notes supply further required branches, including decision trees, entropy, universal tightness, IIC, finite-size scaling, and continuum limits. [P7]–[P15]

Each source must be decomposed before it becomes an executable proof task. The seed is not an assertion of exhaustive coverage, and the bibliography process should actively find omissions and corrected versions.

## 9. Milestones, effort, and maintenance

**Gate A — agree the architecture through examples.** Fix source editions, stable-ID and coverage conventions, a minimal model contract, role owners, and an information-design prototype of the wiki. Use representative records with accurate pending statuses; a completed pilot proof is not required yet. Test one result shared across sources, one conditional result, one correction, one finite-graph result, and one long-range result. Check that contextual links, generated backlinks, and typed local dependencies let readers find definitions, logical inputs, and applications from each entry point. Do not allocate the entire corpus before these cases work.

**Gate B — complete the first slice.** Several contributors independently deliver pieces of the pilot using the same interfaces. The proof, source mapping, narrative, and verification evidence agree. Every advertised production module and source obligation is included in an audited target, and a verification manifest identifies the successful checked revision. The prototype now gains its first fully verified proof page. Use this to measure specification effort, review time, merge conflicts, and build latency.

**Gate C — establish the shared toolkit.** Complete high-reuse inequalities, finite/infinite transitions, graph and analytic interfaces. Produce the first substantive critical theorem with its full prerequisite closure. Build the task frontier from that dependency map.

**Gate D — expand the parallel tracks.** Assign area maintainers and run multiple model programmes. Keep library refactoring, source inventories, and exposition as funded work, not cleanup deferred until all proofs are finished.

**Gate E — release by verified coverage.** Tag releases containing an explicit set of covered source assertions, theorem statements, proof evidence, compatible dependencies, and a matching wiki snapshot. A release may offer broad partial coverage; it should not label an entire book or paper formalised while required inputs remain open.

Do not promise a completion date for the full corpus before the pilot and dependency census. A useful initial timebox is a short architecture-and-pilot sprint, with completion judged by these gates rather than by a claim that a large theorem must fit the timebox. Track reviewed assertion coverage, completed high-dependency results, unresolved semantic questions, contributor blocking, reviewer hours, reuse, and clean build performance. Lines of code and number of agents are poor progress measures.

Generic reusable mathematics should eventually move upstream where appropriate. Keep temporary `ForMathlib` material independent of specialised models. Follow mathlib's current AI contribution policy: human understanding, tool disclosure, and human-written upstream discussions; do not send unattended agent contributions into the community. [M1]

Choose contribution and publication licensing before broader distribution, preserve attribution and contributor credit, and retain source links and version metadata. The HTML can be built privately while the source corpus and exposition are being developed. Public hosting is a separate decision.

## References

- **[A1]** Scott Armstrong, [Autoformalization is now very easy](https://www.scottnarmstrong.com/2026/10/autoformalization-is-now-very-easy/), 4 October 2026.
- **[A2]** Armstrong, [Formalizing Stochastic Homogenization in Lean](https://www.scottnarmstrong.com/2026/06/formalizing-stochastic-homogenization-in-lean/), 15 June 2026; [De Giorgi–Nash–Moser project](https://www.scottnarmstrong.com/2026/04/formalizing-de-giorgi-nash-moser-theory-in-lean/), 7 April 2026.
- **[A3]** [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/1837b95b3d5a9fd8d311367603902ad7fe261adf).
- **[M1]** [Mathlib contribution and AI policy](https://leanprover-community.github.io/contribute/index.html).
- **[M2]** [Mathlib contribution workflow](https://leanprover-community.github.io/contribute/how-to-contribute.html).
- **[M3]** [Product measures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProductMeasure.html); [pinned source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/ProductMeasure.lean).
- **[M4]** [SetBernoulli](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/SetBernoulli.html).
- **[F]** [FLT contribution guide](https://github.com/ImperialCollegeLondon/FLT/blob/main/CONTRIBUTING.md).
- **[B]** [Leanblueprint](https://github.com/PatrickMassot/leanblueprint); Tao's [PFR blueprint tour](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/).
- **[GH1]** [GitHub protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches).
- **[GH2]** [GitHub code owners](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-code-owners).
- **[GH3]** [GitHub status checks](https://docs.github.com/en/pull-requests/reference/status-checks).
- **[G]** Grimmett, [Percolation, second edition](https://link.springer.com/book/10.1007/978-3-662-03981-6), 1999; [author publication list](https://www.statslab.cam.ac.uk/~grg1000/preprints.html).
- **[HH]** Heydenreich–van der Hofstad, [Progress in High-Dimensional Percolation and Random Graphs](https://link.springer.com/book/10.1007/978-3-319-62473-0), 2017; [author-hosted manuscript, 17 March 2017](https://www.win.tue.nl/~rhofstad/survey-high-d-percolation.pdf).
- **[P1]** Hutchcroft, [Power-law bounds for critical long-range percolation below the upper-critical dimension](https://doi.org/10.1007/s00440-021-01043-7), 2021.
- **[P2]** Hutchcroft, [The critical two-point function for long-range percolation on the hierarchical lattice](https://arxiv.org/abs/2103.17013), 2021.
- **[P3–P5]** Hutchcroft, Critical Long-Range Percolation [I](https://arxiv.org/abs/2508.18807), [II](https://arxiv.org/abs/2508.18808), [III](https://arxiv.org/abs/2508.18809), 2025.
- **[P6]** Chen–Sakai, [The marginal case](https://arxiv.org/abs/1808.06789v3), 2019 version.
- **[P7]** Duminil-Copin–Tassion, [Sharpness](https://arxiv.org/abs/1502.03050v3), corrected 2018 version.
- **[P8]** Berger, [Transience, Recurrence and Critical Behavior for Long-Range Percolation](https://arxiv.org/abs/math/0110296v3), corrected 2014 version.
- **[P9]** Heydenreich–van der Hofstad–Sakai, [Mean-field behavior for long- and finite range models](https://arxiv.org/abs/0712.0312v2), 2008 version; Chen–Sakai, [Critical two-point functions](https://arxiv.org/abs/1204.1180v4), 2015 version.
- **[P10]** Hulshof, [The one-arm exponent for mean-field long-range percolation](https://arxiv.org/abs/1411.3020), 2014.
- **[P11]** Hutchcroft, [Triangle-condition implications](https://arxiv.org/abs/2106.06400v3), 2022 version.
- **[P12]** Hutchcroft, [Critical cluster volumes in hierarchical percolation](https://arxiv.org/abs/2211.05686), 2022.
- **[P13]** Hutchcroft, [Sharp hierarchical upper bounds on the Euclidean critical two-point function](https://arxiv.org/abs/2202.07634v2), 2022.
- **[P14]** Bäumler–Berger, [Isoperimetric lower bounds for critical exponents](https://arxiv.org/abs/2204.12410v2), 2023 version.
- **[P15]** Hutchcroft, [Pointwise two-point function estimates](https://arxiv.org/abs/2404.07276), 2024.
