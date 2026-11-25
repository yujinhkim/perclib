# Gate 0 audit

**AUDITOR · snapshot 13 November 2026, 00:53 EST · [package #14](https://github.com/tomhutchcroft/lrp/issues/14).**

## Merge state

`main` is [b6c3ddbe](https://github.com/tomhutchcroft/lrp/commit/b6c3ddbec915b1a89075835c8ebfbbbdc8b97ccb). Planning #4, D-2 amendment #9, **H-2 #5 and H-3 #6 are merged**. N-1 #7 and P-1 #8 remain open. P-1 now has AUDITOR approval at its reviewed head; N-1 awaits the governing-record merge and acceptance review. Gate 0 remains open. GitHub still names the repository `tomhutchcroft/lrp` and reports it private; R-1's authoritative record remains unresolved.

## Review and evidence

The initial foundation reviews were H-2 → H-3 → N-1 → P-1. This continuation checked changed revisions, provenance, actual CI logs and checkout identities; unchanged historical findings were not reposted.

| Package / reviewed revision | Evidence and verdict |
| --- | --- |
| H-2: `eda878f16cb440aae5e5d3e0f2e2d48ba7c847d0` | Previously [approved](https://github.com/tomhutchcroft/lrp/pull/5#pullrequestreview-5886419288); merged as `24e62aac6249f4586b8cfabd8591122eb80b5d25`. Independently inspected [main run 43370735386](https://github.com/tomhutchcroft/lrp/actions/runs/43370735386): exact merge checkout, --wfail build and 47-declaration Lrp audit succeed. |
| H-3: `e10debf200847c856e1734dc57cb202661ff4f24` | Previously [approved](https://github.com/tomhutchcroft/lrp/pull/6#pullrequestreview-5886423382); merged as current main. [43371261421](https://github.com/tomhutchcroft/lrp/actions/runs/43371261421): exact main checkout; import closure, --wfail/audit (47 Lrp declarations), wiki and final CI succeed. |
| N-1: `9da5b81a828277e48d18bed2afd920b53c7733a8` | Unchanged since prior review; mechanical correspondence positive, **not approved** pending [#18](https://github.com/tomhutchcroft/lrp/issues/18)'s record on main. Prior inspected [43368434829](https://github.com/tomhutchcroft/lrp/actions/runs/43368434829) checked out `5c62d7e6e82361a1f7883aad64569377f59d2be2`, with the same tree as that head. |
| P-1: `f6b491fe66afd2dc77385ba46cc38e29b86fbee1` | [Approved](https://github.com/tomhutchcroft/lrp/pull/8#pullrequestreview-5886775145). D-6 header and evidence-log errata resolved; executable Lean unchanged. [43371544617](https://github.com/tomhutchcroft/lrp/actions/runs/43371544617): all four jobs succeed; 90 PercLib declarations. Actual checkout `4c0b36d41e8626e31c7a14fadc786d5992e24154` and head share tree `6168312e9634db1231308293c10f3e3d644201d6`. N-1 must merge first. |

Synthetic checkout evidence is not described as a direct head checkout. All cited rooted audits allow only `propext`, `Classical.choice`, `Quot.sound`; counts include generated declarations. The prior negative fixtures #10/#11 demonstrated intended import/link failures and failed final gates ([43367477381](https://github.com/tomhutchcroft/lrp/actions/runs/43367477381), [43367481362](https://github.com/tomhutchcroft/lrp/actions/runs/43367481362)). No hidden Input, forbidden proof escape or non-vacuity defect was found in the foundation review. P-3 still owes cluster-volume measurability and Tonelli.

**New governance reviews:** [#29](https://github.com/tomhutchcroft/lrp/pull/29#pullrequestreview-5886778138) approved at `4ed1270b6bd2d99e080dd1c4663c6a28f4c93425`: faithful #18 record; [43371308696](https://github.com/tomhutchcroft/lrp/actions/runs/43371308696) passes all four jobs on same-tree synthetic checkout `ddbe461a68f8efdcbb1375ed362e4ff3ad62710c`. [#28](https://github.com/tomhutchcroft/lrp/pull/28#pullrequestreview-5886781517) requires frontier/visibility corrections and current four-job CI; its old successful run had only the build/audit job. [#30](https://github.com/tomhutchcroft/lrp/pull/30#pullrequestreview-5886786206) requires correction of the claim that Verso forces prose into `PercLib/`, and final-revision evidence. Its successful [43371318038](https://github.com/tomhutchcroft/lrp/actions/runs/43371318038) tests an integration tree different from its head. Per-file Apache notices are confirmed; D-18 remains Tom's decision. #20 is closed unmerged, superseded by #30.

## Deviations and three largest risks

P-1's provenance omission and proposed D-10 exception are corrected. N-1's agreed clarification is still unmerged. H-2's mandated combined licence/port package conflicted with the licence-only-PR rule; no licence-content defect was found. Superseded #2 remains open.

1. **Evidence drift:** changed heads, synthetic merges and actual main commits require distinct SHA/run records; successful integration is not automatically exact-head evidence.
2. **Statement/provenance drift:** later probability bounds must preserve D-2's diagonal exclusion, bond-cluster convention and original-source notices; P-1 does not complete P-3/P-5.
3. **Governance ambiguity:** approved decisions must reach authoritative files; role approvals do not substitute for Tom's reserved decisions or native branch-protection reviews.

Only `docs/audits/` was edited by AUDITOR. No local Lean build or merge was performed. This report is not self-approved; #26 awaits independent review and evidence for its new report revision.
