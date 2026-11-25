# Pinned source corpus and reproducible text preparation

## Inputs

The mathematical source is Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1. The supplied primary PDF is `attachments/i-want-you-to-ljpx/tom1.pdf`
in the enclosing project, not a recreated substitute under `.scratch/`.

| artifact | SHA256 |
|---|---|
| `.scratch/source/paper.html` | `246ccda2bfadabc8f6ce1670f015ddcb58b99f896ea16ff722321532f074d76f` |
| `.scratch/source/paper-tex.txt` | `7658da0615631fa69f53a9a7d7b6de2526e83016ad4ecd5c0159774a8d071755` |
| `.scratch/source/paper-tex-regenerated.txt` | `7658da0615631fa69f53a9a7d7b6de2526e83016ad4ecd5c0159774a8d071755` |

The HTML is the unchanged primary LaTeXML snapshot. `paper-tex.txt` is a convenience
rendition of its `alttext` LaTeX annotations, not a new independent mathematical edition.
Statement/proof locators use stable HTML element IDs and HTML line ranges; the sidecar
`paper-tex.locators.tsv` gives inner IDs for rendered content blocks. Do not cite line numbers
from an agent's separately generated text dump as though they were canonical.

The ignored `.scratch/source/` directory is inside this staging worktree, not at the enclosing project root.
Workers should use absolute repository paths rather than treating a member-specific `.scratch/` directory as the canonical one.

## Preparing and checking

Run from this staging worktree:

```sh
python3 .scratch/source/html2tex.py .scratch/source/paper.html .scratch/source/paper-tex.txt   --locators .scratch/source/paper-tex.locators.tsv --self-check
cp .scratch/source/paper-tex.txt .scratch/source/paper-tex-regenerated.txt
python3 scripts/source_statement_inventory.py   .scratch/source/paper.html .scratch/source/numbered-inventory.tsv
python3 scripts/check_source_restitution.py
python3 -W error scripts/test_source_restitution.py
python3 -W error scripts/test_semantic_closure.py
```

The original converter restored LaTeX before applying a generic HTML-tag strip regex. That incorrectly deleted
text beginning at unescaped `<` in formulas such as `d=3\alpha<6` and `0<\beta_c<\infty`. The current parser
holds mathematical annotations as opaque tokens until tag removal has finished. It also excludes JavaScript, navigation,
and arXiv page chrome. The checked canonical text preserves all 2838 math annotations, including all 287 containing
an inequality. The regression tests include a failing-altered-annotation case and an end-to-end byte-identical regeneration.

`SOURCE-RESTITUTION GUARD OK` is an identity/fidelity check of those artifacts, not a source-fidelity proof of
Hutchcroft's mathematical statements, a topological graph review, or a Lean build. The primary PDF remains authoritative
where HTML cross-references are missing or copied labels are corrupted. In particular, the HTML sometimes prints a
section reference where the PDF prints `(HD)`.

## Graph and anchor status

The numbered-environment inventory contains 98 environments: 75 named statements and 23 numbered remarks. It is
not exhaustive coverage of the 104-page paper's displays, citations, proof paragraphs, or unnumbered definitions.
Every graph and coverage record remains proposed unless its own independent review is recorded. Lemma I.4.18's printed
ell=3 supremum bound has a verified diagonal counterexample. The bounded-reviewed replacement uses ell>=4 and a two-scale averaged ell=3 estimate; it does not summably control total triangle mass. The three consumers have been identified, but their other inputs are not thereby reviewed.

There are no accepted new theorem proofs from this orchestration layer. Both moment roots have versioned source-audit
obligations: the third HD logarithmic factor required regularization, both have the semantic-definition-closure problem,
and the treatment of positive `beta_c` is still being checked against primary literature. `PROVED_MODULO` is not
shorthand for unconditional `PROVED`, and no existing PercLib export is credited without matching its actual statement.

Current planning checkpoint, not a full repository proof scan:

```text
DRAFT_ANCHORS: 2 -- both v1 moment roots are blocked for declaration-fidelity repair; a v2 is only a candidate
UNREGISTERED_SORRIES: 0 in the production orchestration modules; isolated candidate files remain non-production
DRAFT_IMPORT_VIOLATIONS: 0 in the last core run; must be rechecked after every anchor/import change
SEALED_THIS_TURN: 0
```

The semantic-closure guard now mechanically covers every non-proof repository import of each declaration, strips its two
extension keys, and then runs the full frozen-anchor guard. Its hashes certify only the source bytes at the checked
revision. Source fidelity, Lean elaborability, ABI generation, approval provenance and proof status remain separate.
Run it after every semantic-definition change or manifest metadata change; then update `DEPGRAPH.md`'s manifest pin.
No root has been promoted by a build count, a worker's report, or this source-hash guard.
