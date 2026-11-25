# Mechanical inventory of `book_draft.tex`

This is a reproducible **screening inventory, not an exhaustive semantic inventory of mathematical claims**. Neither a display nor a theorem environment is a reliable unit of mathematical coverage. One paragraph can contain many claims; a display can be a definition, a heuristic, a repetition, or part of one assertion.

## Source snapshot

- Source: `sources/notes/book_draft.tex`
- SHA256: `61c11fcbd2d4ac600e9b96b6b1a81c399b6e049dd208e8790d5f06e1b02b5fd4`
- UTF-8 file size: **286,293 bytes**.
- Physical lines (`str.splitlines()`): **6,307**, also 6,307 newline characters.
- Script: `scripts/inventory_source.py`. From the repository root, regenerate with:

```sh
python scripts/inventory_source.py --source sources/notes/book_draft.tex --output-dir docs/sources/notes
```

## Exact mechanical counts

| Item | Count |
|---|---:|
| Numbered chapters | 10 |
| Starred chapters | 2 |
| Parts | 5 |
| Sections | 56 |
| Named statement environments | 45 |
| Theorems | 20 |
| Propositions | 11 |
| Lemmas | 8 |
| Corollaries | 3 |
| Definitions | 3 |
| Explicit proof environments | 22 |
| Outer displayed-math blocks | 698 |
| `\[ ... \]` blocks | 697 |
| `align*` blocks | 1 |
| Nested `aligned` environments, not additional displays | 15 |
| Nested `cases` environments, not additional displays | 3 |
| Labels in the whole file | 7 |
| Named environments carrying labels | 7 |
| Candidate paragraphs from the lexical screen | 363 |
| Candidate paragraphs overlapping a display | 274 |
| Candidate paragraphs without a display | 89 |
| Candidate paragraphs overlapping a named statement | 46 |
| Candidate paragraphs overlapping an explicit proof | 57 |
| Candidate paragraphs overlapping neither | 260 |

The preamble also declares conjecture, example, remark, and warning environments, but there are no instances of them. **Zero conjecture environments does not mean zero conjectural or heuristic mathematical content.** The draft uses prose and approximate displays extensively, particularly in Chapter 3.

| Chapter | First line | Sections | Named statements | Explicit proofs | Display blocks | Candidate paragraphs |
|---|---:|---:|---:|---:|---:|---:|
| Preface | 75 | 0 | 0 | 0 | 0 | 0 |
| A Roadmap for the Reader | 87 | 0 | 0 | 0 | 0 | 4 |
| 1. Critical Phenomena and Percolation | 104 | 5 | 1 | 1 | 23 | 27 |
| 2. The Mean-Field Reference Models | 303 | 6 | 1 | 0 | 52 | 25 |
| 3. Scaling and Hyperscaling | 649 | 5 | 0 | 0 | 45 | 21 |
| 4. Sharpness and Correlation Inequalities | 948 | 5 | 5 | 5 | 62 | 25 |
| 5. The Triangle Condition | 1421 | 7 | 5 | 4 | 78 | 49 |
| 6. Entropy, Decision Trees, and Universal Bounds | 2128 | 8 | 9 | 5 | 135 | 67 |
| 7. Two Dimensions and Continuum k-Point Functions | 3299 | 4 | 3 | 3 | 59 | 35 |
| 8. Long-Range Percolation | 3877 | 6 | 5 | 0 | 52 | 35 |
| 9. Cutoff Renormalization and Effective Long-Range Behaviour | 4448 | 7 | 16 | 4 | 186 | 67 |
| 10. A Roadmap of the Proof Techniques | 6218 | 3 | 0 | 0 | 6 | 8 |

## Method

1. Read the fixed source snapshot as UTF-8. Replace unescaped LaTeX comments by spaces, preserving offsets and newlines. The draft does not require a verbatim-aware parser for the counted constructs.
2. Parse `part`, `chapter`, and `section` commands, reading balanced title arguments and distinguishing starred chapters. Retain source line and enclosing chapter/section.
3. Read the environment names declared by `newtheorem`; use a balanced begin/end stack to extract every instance, its optional title, labels, source interval, and text. Record proof environments separately.
4. Count outer display environments and bracket-delimited displays once. Nested `aligned` and `cases` environments are not new display blocks. The raw bracket counts were independently checked: 697 opening and 697 closing delimiters.
5. Split the document body into blank-line-delimited paragraphs. Select a paragraph if it overlaps a recognized display or matches a liberal assertion/definition keyword expression, including such phrases as “we have,” “for every,” “finite,” “independent,” “convergence,” “we define,” and “let.” Record inline-math presence, overlap with named/proof environments, and lexical tags for heuristic, quoted, conditional, definition, and proof language.

This is not a TeX macro-expansion engine. Lexical tags are suggestions for human/agent review, not reliable classifications. Paragraphs may cross environment boundaries. A paragraph overlapping a named statement is not necessarily wholly within it. References to “proof” identify explicit proof environments only: large amounts of proof reasoning occur outside them. Keyword false positives and false negatives are expected.

## Files

- `summary.json`: compact counts and chapter breakdown.
- `inventory.json`: full machine-readable inventory with headings, source intervals, all named statement text, displays, and screened paragraphs.
- `headings.tsv`: heading and chapter locations.
- `named_statements.tsv`: the 45 named statement instances, with IDs `S001`–`S045`, source intervals, title, labels, and lexical tags.
- `candidate_paragraphs.tsv`: screened paragraphs `P0001`–`P0363`, including text and overlap metadata.

**The Snnn/Pnnnn IDs are provisional mechanical IDs, not canonical assertion IDs.** IDs in these generated files are snapshot-local conveniences. The eventual coverage registry should use stable source IDs plus text fingerprints; it should not use a mutable line number or ordinal as the sole identity.
