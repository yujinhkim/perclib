# W-6 pilot source occurrences

SCOUT source record for issue #50. This file supplies source locators and proposed
concordance data, not a proof, compiled tag association, or correspondence review.
WIKI owns publication under wiki/; PROVER-D owns source-specific Lean wrappers.

## Inspected sources

1. Notes: [pinned snapshot](https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L954), blob
   `4fa5c9ad76ea4cba2c1cd267a122ade7dd6ca3b3`, lines 954–962.
   Chapter 4, section Sharpness, unnumbered paragraph preceding S003.
   The setup is a transitive nonnegative weighted graph with finite row mass.
   The paragraph gives the reciprocal-mass threshold bound by subcritical exploration.
   It is not the sharpness theorem starting at line 964. No notes prose is reproduced here.
2. Hutchcroft, *Power-law bounds for critical long-range percolation below the
   upper-critical dimension*: [arXiv:2008.11197v2](https://arxiv.org/html/2008.11197v2#S1),
   Section 1, unnumbered paragraph immediately after the definition of beta_c.
   This is the pilot source named by the existing subcritical-bound article.
   It gives no infinite clusters for beta times total kernel mass below one,
   and hence the reciprocal-mass threshold bound on Z^d.
   The general susceptibility estimate is an extension, not that paragraph's literal statement.
3. A parallel lower bound also occurs in [arXiv:2103.17013v1](https://arxiv.org/html/2103.17013v1#S1.SS1),
   Section 1.1, immediately after the definition of beta_c. This concerns the
   hierarchical model and is not the power-law-paper occurrence above. No extra
   occurrence is allocated merely because the author and year match.

## Statement contract and implementation bridge

For the power-law source, keep d >= 1, a symmetric nonnegative summable kernel
on Z^d, and probabilities 1-exp(-beta J(y-x)). Write M for the full kernel mass.
The source includes J(0) in that mass; D-2 excludes diagonal coordinates from
row sums. Thus the required off-diagonal row bound is <= M, even if J(0) is nonzero.
Do not silently change the source's mass to the stronger off-diagonal one.

For the notes, use a countable transitive weighted graph and its common finite
edge-intensity row mass. A host graph is represented by zero intensity off its
edges. For the ordinary-real reciprocal statement require M > 0 explicitly;
the extended-real zero-mass case is a library extension. Preserve the distinction
between the paper's supremum of no-percolation parameters and the library's
infimum of positive-percolation parameters. A source wrapper must prove their
agreement, or explicitly formulate its conclusion with the library threshold
and explain the transport; the notations alone do not establish it.

At inspected main `f79b74d16d222d7f2ee63260782c0919baf9a0f5`,
`PercLib/Percolation/Bond/Intensity.lean` supplies
`intensity_rowSum_le`, `law_exists_infinite_intensity_eq_zero`,
`inv_le_globalCriticalIntensity`, and `inv_le_rootCriticalIntensity`.
Its zero-row theorems are separate. The stronger expectation bridge is
`chi_intensity_le`. The arbitrary-profile result is
`chi_le_inv_one_sub_of_rowSum` in `RowSum.lean`.
These are source-inspected declaration names, not a new compilation claim.

## Proposed occurs_in records

The existing active tag JZ47 is the general critical-intensity consequence in
`wiki/articles/subcritical-bound.md`. These records describe its relationship
to the sources; they do not stand in for the future source-specific wrapper tags.
No fresh tag is invented. Tag 53Z9 is the stronger arbitrary-profile expectation
result and must not be advertised as a verbatim occurrence of either paragraph.

The notes record uses the catalog URL/edition exactly. Before publishing the
paper record, WIKI must reconcile that catalog entry from its current published
DOI edition to the inspected arXiv v2 URL/edition below, or independently verify
the published edition. Published pagination and edition equivalence have not
been checked here. Do not paste the second record into the current catalog unchanged:
the consumer correctly rejects mismatched editions.

```json
{
  "schema": "perclib-occurs-in-v1",
  "occurrences": [
    {
      "source": "notes",
      "tag": "JZ47",
      "source_url": "https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex",
      "edition": "Uploaded preliminary draft · snapshot 12 November 2026",
      "locator": "Chapter 4, Sharpness and Correlation Inequalities; section Sharpness; source lines 954–962, paragraph immediately before the named sharpness theorem (which begins at line 964).",
      "relationship": "generalization",
      "note": "The source gives the positive critical-intensity lower bound for a transitive integrable weighted graph. JZ47 extends it to uniformly bounded off-diagonal rows, distinguishes root and global thresholds, and explicitly treats zero row sum. The source paragraph is not a statement of the full arbitrary-profile susceptibility estimate."
    },
    {
      "source": "hutchcroft-powerlaw-2021",
      "tag": "JZ47",
      "source_url": "https://arxiv.org/abs/2008.11197v2",
      "edition": "arXiv:2008.11197v2 · 12 February 2021",
      "locator": "Section 1, Introduction; unnumbered paragraph immediately after the displayed definition of beta_c and before the discussion of the one-dimensional non-trivial phase transition.",
      "relationship": "generalization",
      "note": "For symmetric summable J on Z^d, the source derives absence of infinite clusters when beta times the total kernel mass is below one, then the reciprocal-mass lower bound. JZ47 permits non-transitive uniform row bounds and explicitly handles zero mass. Source total mass includes J(0); the graph's off-diagonal mass is at most this total."
    }
  ]
}
```

## Remaining ownership and acceptance

WIKI can publish the generalization records after catalog reconciliation and
source review. PROVER-D still owes the two source-faithful tagged wrappers;
those require their own allocated tags and matching source-statement records.
The current records neither assert those wrappers exist nor certify any
fingerprint correspondence review. No Lean, wiki, CI, pin, or governance file
is changed by this source record.
