# Wiki prototype: canonical articles and mathematical links

This prototype tests the information structure of the percolation reference. Its governing design is in [WIKI_ARCHITECTURE.md](WIKI_ARCHITECTURE.md); the wider programme is in [PROJECT_PLAN.md](PROJECT_PLAN.md).

## Direction

Build a Wikipedia-style network of canonical mathematical articles. A reader can enter at a concept, theorem, model, or source passage and follow links to definitions, hypotheses, proof inputs, related results, and applications. Subject indexes, notation-aware search, and source concordances provide additional entry points. Generated backlinks reveal how the rest of the reference uses the current article.

The core reference has no maintained reading-route catalogue and no prescribed previous/next sequence. Keep each article readable without opening every link, while providing enough precise connections to inspect unfamiliar concepts and the logical structure of an argument.

## What each article should show

| Element | Purpose |
| --- | --- |
| Stable page ID and assertion anchors | Preserve links when names, folders, or presentation change |
| Shared setting and notation | Establish the objects, conventions, and genuine running hypotheses |
| Local theorem statement | Introduce the extra hypotheses and parameters of this result, followed by its conclusion |
| Contextual mathematical links | Connect definitions, notation, hypotheses, proof steps, variants, and applications at their point of use |
| Local dependency panel | Distinguish concepts needed to read the statement, inputs to a selected mathematical proof, and actual compiled Lean dependencies |
| Generated backlinks | Show where the concept or result is mentioned, required, specialised, or applied |
| Source and attribution panel | Identify precise source occurrences, reused libraries, corrected formulations, and relevant versions |
| Formalisation evidence | Link each implemented assertion to its declaration, checked revision, build and axiom evidence, and correspondence review |

A mathematical proof may have several alternative arguments. Keep their inputs separate. These proof records establish logical relationships; they do not prescribe reading order. Source tables of contents remain useful within the concordance, without defining the canonical article hierarchy.

## Editorial judgement about hypotheses

Use the top setting block for background notation and genuinely running assumptions. Put an additional condition that makes a particular theorem true into that theorem. For example, the graph and independent law are the setting of the susceptibility article; the quantified parameter m and uniform row-sum bound below one belong inside its theorem. The same distinction places the power-law comparison and exponent range inside the hierarchical two-point estimate, while leaving hierarchical geometry and notation above it.

This is a judgement call for a mathematician, not a formatting rule that moves every assumption to the same place. The exact Lean statement and any standalone export must retain all relevant context and hypotheses. The page-data key `context` denotes the shared setting only.

## Navigation that grows with the corpus

The global sidebar contains navigation tools and a bounded selection of broad subject hubs. It does not contain a list of all articles. Subject membership can overlap, and adding an article should not require an edit to the application shell.

Full article, subject, source, search, and relation lists use filters, counts, and pagination. Their URL retains the selected query and page. A local dependency graph is bounded and links to its complete relation lists. Backlinks are generated from outgoing links at build time. Article bodies and source-occurrence records are fetched as needed; the catalogue contains only navigation/search metadata.

These choices separate the reader's navigation from the number of articles. Client-side search still has a finite practical limit; a future sharded or server-side index should preserve the same link and filtering contracts. The prototype is not a performance claim about the eventual full corpus.

## Adding or extending a page

1. **Find the existing canonical article.** Search names, notation aliases, source locators, and assertion IDs before creating another formulation of the same object. Extend a coherent article when a separate page adds little value.
2. **Assign stable identity and scope.** Use the repository's ID convention, choose a subject title, and identify separately addressable assertions. Record the exact model, parameter range, boundary convention, and any uniformity of constants.
3. **Write a self-contained explanation with contextual links.** Link technical terms to their definitions and results to the relevant assertion anchors. Link each nontrivial proof input where it is used. Preserve important distinctions such as site versus bond percolation and restricted versus full-space clusters.
4. **Record typed relationships.** Separate `defined_using`, `requires_to_state`, `proof_uses`, specialisation, equivalence, analogy, and ordinary mentions. Mark authored proof inputs as planned or reviewed. Supply the assumptions and bridge behind any claimed equivalence or specialisation.
5. **Attach sources and formal evidence.** Give edition or commit pins and exact locators. Existing-library reuse carries attribution and its own upstream status. A checked upstream theorem, a compiled local adaptation, and a reviewed correspondence to the prose are distinct facts.
6. **Add discovery metadata.** Assign subject/model tags and notation aliases. Forward links and typed relations generate backlinks; do not maintain a second hand-written backlink list. Ensure that at least one relevant existing article or index makes the new page discoverable.
7. **Review the rendered article.** Check mathematics, anchors, source links, contextual navigation, backlink labels, and the local dependency panel. A reader should be able to inspect an input and return to its point of use. Validate that every advertised formal status matches evidence for the exact revision.

## Evidence boundaries

Conceptual links are editorial relationships. Authored proof inputs describe a mathematical argument and carry their review status. Compiled dependencies come from an extractor inspecting the declaration type or proof term in a checked Lean environment. Keep these distinct in the data and in the interface. Record whether a formal dependency view is direct or transitive and which revision it describes; module imports are a separate build relationship.

When no compiled dependency extraction exists, say so. Do not infer theorem dependencies from the fact that a module was imported, and do not present an illustrative mathematical diagram as a compiler-produced proof graph. A page about a large subject can contain both implemented foundations and unformalised target results; assign evidence to individual assertions instead of colouring the whole page as proved.

The prototype is an information-design test. Its page count, illustrations, and explanatory text do not certify coverage of the books or research literature. Build and deployment details, together with exact checked revisions, should be recorded alongside the implementation.

## Implemented sample

The source lives in `wiki/prototype/`. Run `npm ci` followed by `npm run build` in that directory, then serve `dist/` as a static site. The build validates internal page and source references and parses the article mathematics with the pinned KaTeX renderer. Browser assets are served locally, including KaTeX and fonts.

The sample content spans foundational and critical percolation articles, contextual hyperlinks, overlapping subject collections, and source concordances. It includes the complete natural-language row-sum susceptibility argument, filterable and paginated indexes, search by aliases and identifiers, hover previews, generated prose backlinks, bounded local prerequisite maps with access to complete relation lists, source-occurrence tables, and a distinct reuse register. The registry contains an explicit verification snapshot for the foundation port in PR #2, at revision `4b1f7bf859d00d0a5fff781820f1cf7312f2e2bf`. The full research statements remain pending in Lean.

The current UI supports readable text and formulas on desktop and at a 390-pixel mobile width. Browser checks covered search, article links, local dependency graph navigation, source tables, permalink copying, and the mobile navigation drawer. The concept map is editorial; a compiler-produced declaration dependency view has not yet been implemented.


## Project metrics

The Project metrics page has its own permanent navigation entry. Website measurements are regenerated with the content build. Repository measurements are dated snapshots with links to the exact commits and CI runs; the default branch and the separately checked foundation contribution are displayed independently.

This distinction matters for review: article count is not assertion coverage, source-occurrence count is not book coverage, and a count of Lean source declarations is not a count of checked mathematical theorems. Unknown measurements remain unmeasured. Overall coverage percentages and time trends require a complete inventory and comparable retained observations.

The navigation redesign was also checked against an isolated corpus of 1,200 synthetic articles and 2,400 source occurrences. The test verified separation of article text from navigation metadata, complete reverse links, source mappings, and cleanup of removed payloads. It did not measure theorem rendering or mathematical correctness. Browser checks exercised actual search pagination, URL-preserving filters, complete relationship lists, on-demand article loading, and the mobile navigation drawer.
