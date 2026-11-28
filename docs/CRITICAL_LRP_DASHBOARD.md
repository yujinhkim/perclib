# Critical long-range percolation I — progress dashboard

> **THE PAPER IS NOT COMPLETELY FORMALIZED.** This dashboard separates proof checks, source coverage, model inputs and publication. Do not infer completion from an import-closure count or a clean axiom report.

Generated: `2026-11-28T03:03:15.950952+00:00`. Schema: `1`. Source digest: `da412f7737e490b4d0f4e441f61ffe3106d1cb0493cda10b7d65047cc1e60ebf`.

## Current snapshot

| Item | Current value |
|---|---|
| Production branch | `work/yujinhkim-critical-lrp-orchestration` |
| Committed production revision | `175f10881a6efbf55f4e6e67ec6c508ba91ef5e0` |
| Local source-only mirror | `62816b7cb8090ba6f46132f2afbc36afc1e4c21e` |
| Fetched GitHub mirror tip | `62816b7cb8090ba6f46132f2afbc36afc1e4c21e` (reflected remote, fetched through the connected repository) |
| Current integration batch | `validated, ready to commit` |
| Current source validation | **passed_for_this_source_snapshot** |
| Current research run | `smwzt36y2`: `running`, 4 working, 2 accepted, 2 awaiting verdict |
| Unowned workflow edit | **Excluded from every staging list and mirror patch.** |

## Source-result ledger

**19 FULL · 42 PARTIAL · 14 NOT FORMALIZED**, of 75 numbered items.
These are deliberately not percentages of completion. FULL entries include printed conditional claims whose intended canonical-model inputs may still be missing.

The item-by-item ledger is [CRITICAL_LRP_COVERAGE.md](CRITICAL_LRP_COVERAGE.md). The independent supporting checks are recorded in [CRITICAL_LRP_FIDELITY_AUDIT.md](CRITICAL_LRP_FIDELITY_AUDIT.md).

## Build and proof checks

* Import closure: exit **0**; ok: all 1491 modules of PercLib are in the import closure of PercLib.lean.
* Latest build log reports success: **True**.
* Latest axiom summary: `Production declarations: 23664 ; Nonstandard axioms: 0 ; sorryAx: 0`.
* Latest Python summary: `Ran 68 tests in 46.593s ; OK`.
* These log lines are historical unless `matches_current_source` is true in the JSON.
* The old source-only cold build timed out after one hour; it is **not** a passing verification and is not being retried unchanged.

## Next genuine inputs

- I.4.16: full tree/BK proof of the generalized mixed moments, notably CaseTwo.SixthMomentMixed; the collapsed two-hub route is refuted.
- Cited critical volume tail: differential/triangle comparison and the two-intensity or uncut comparison, not merely a cutoff equivalence.
- Nontrivial canonical critical two-point estimates, with a large-distance rather than literal unit-distance HD(3) reading.
- Case-1 hHlog, Case-2 positivity and sixth-moment inputs; avoid leaking Case-3 hypotheses.
- Off-diagonal HasCovBound; a uniform covariance bound does not supply the weighted star.
- Actual first-order tail applications through I.3.2 and the superprocess statements; compilation and local ODE wrappers do not close these.

## Research activity

Previous run `smwzqts7r`: 8 accepted reports, solved. Its older delayed wake notices carry no new pending submission.

Current participant directions (not accepted results):

- Marginal two-fold convolution asymptotics
- Conditional Corollary I.2.15 from the two-point estimate
- Cluster lower-tail probability tools
- Case-1 hHlog reduction
- Tree/BK sixth mixed moment
- Off-diagonal covariance
- I.3.2 moment-to-tail applications

Only a reviewed, independently rebuilt and integrated submission counts as a result.
A swarm remaining within its own time/step budget is not a weekly-quota signal.
Quota status: No weekly quota meter is exposed by the available session tools. Do not interpret a swarm's fixed run limits as the weekly quota.

## Delivery and maintenance

The source-only GitHub mirror was fetched successfully and remains at 62816b7cb8090ba6f46132f2afbc36afc1e4c21e until this batch is pushed. The latest connector fetch of the production branch reported branch_not_found; no force-push, history rewrite, or PR is claimed.

The `docs/` and `results/` copies are generated together. The JSON is the machine-readable record; Markdown has no live background service privilege.
Refresh it after each accepted packet, validation, commit/push, stalled run or quota signal:

1. Refresh .scratch/dashboard/activity.json from Ultramath direction/report/verdict records.
1. Run the full validation suite and write current-validated-state.json with its source digest.
1. Refresh the connected GitHub mirror through the authorized connector before reading its tip.
1. From the production worktree, run python3 scripts/update_critical_lrp_dashboard.py.
1. Commit dashboard state with its corresponding proof/integration batch.

```sh
cd .scratch/critical-lrp-orchestration
python3 scripts/update_critical_lrp_dashboard.py
python3 scripts/update_critical_lrp_dashboard.py --check
```

For the project-overview copy see [results/critical-lrp-dashboard.md](../../results/critical-lrp-dashboard.md). The project-root Markdown links have been normalized separately; this note does not override a source-ledger status.

The current full-validation log paths are under `.scratch/verification/` in this production worktree. Use the committed source itself as the reproducible proof artifact.
