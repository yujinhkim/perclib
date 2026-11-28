# Critical long-range percolation I — progress dashboard

> **THE PAPER IS NOT COMPLETELY FORMALIZED.** This dashboard separates proof checks, source coverage, model inputs and publication. Do not infer completion from an import-closure count or a clean axiom report.

Generated: `2026-11-28T03:37:00.906245+00:00`. Schema: `1`. Source digest: `6efe077db4974d73529de88f42a61a0fecd810cd62d91902e1a8d4e11f7280a0`.

## Current snapshot

| Item | Current value |
|---|---|
| Production branch | `work/yujinhkim-critical-lrp-orchestration` |
| Committed production revision | `702a43e792bf5dc3e29f98ed80d172132cae9dfb` |
| Local source-only mirror | `7ded230c8b47b992aa65625c1b50ca7f52db3947` |
| Fetched GitHub mirror tip | `7ded230c8b47b992aa65625c1b50ca7f52db3947` (reflected remote, fetched through the connected repository) |
| Current integration batch | `validated, ready to commit` |
| Current source validation | **passed_for_this_source_snapshot** |
| Current research run | `smwzuf8hm`: `running`, 5 working, 0 accepted, 1 awaiting verdict |
| Unowned workflow edit | **Excluded from every staging list and mirror patch.** |

## Source-result ledger

**20 FULL · 43 PARTIAL · 12 NOT FORMALIZED**, of 75 numbered items.
These are deliberately not percentages of completion. FULL entries include printed conditional claims whose intended canonical-model inputs may still be missing.

The item-by-item ledger is [CRITICAL_LRP_COVERAGE.md](CRITICAL_LRP_COVERAGE.md). The independent supporting checks are recorded in [CRITICAL_LRP_FIDELITY_AUDIT.md](CRITICAL_LRP_FIDELITY_AUDIT.md).

## Build and proof checks

* Import closure: exit **0**; ok: all 1499 modules of PercLib are in the import closure of PercLib.lean.
* Latest build log reports success: **True**.
* Latest axiom summary: `Production declarations: 23850 ; Nonstandard axioms: 0 ; sorryAx: 0`.
* Latest Python summary: `Ran 68 tests in 49.147s ; OK`.
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

Previous run `smwzt36y2`: 8 accepted reports, solved. Its older delayed wake notices carry no new pending submission.

Current participant directions (not accepted results):

- Full labelled-tree/BK sixth mixed moment
- Moment asymptotics to weak convergence
- Case-1 hydrodynamic condition
- Gladkov inequality I.2.7
- Four-point square inequality I.5.10
- Critical-tail differential comparisons

Only a reviewed, independently rebuilt and integrated submission counts as a result.
A swarm remaining within its own time/step budget is not a weekly-quota signal.
Quota status: No weekly quota meter is exposed by the available session tools. Do not interpret a swarm's fixed run limits as the weekly quota.

## Delivery and maintenance

The source-only GitHub branch has been pushed and fetched back at 401dba0907e730ceb009274eb1b48cf8b70848ab. All 36 files match the validated production commit. No workflow edit, force-push, history rewrite or pull request was used.

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
