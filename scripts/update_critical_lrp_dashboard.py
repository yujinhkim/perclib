#!/usr/bin/env python3
"""Generate the Critical LRP progress dashboard from repository evidence.

The coordinator owns the activity snapshot, including Ultramath reports surfaced by
its tools. Compilation, source coverage, revisions and delivery-read comparisons are
computed locally. Never turn ledger counts into a claim that the paper is complete.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT.parent.parent
VERIFY = ROOT / ".scratch" / "verification"
ACTIVITY = ROOT / ".scratch" / "dashboard" / "activity.json"
SOURCE_BRANCH = "work/yujinhkim-critical-lrp-orchestration-source-only"
MIRROR = PROJECT / ".scratch" / "critical-lrp-orchestration-source-only"
SCHEMA = 1

PATHS = (
    ROOT / "docs" / "CRITICAL_LRP_DASHBOARD.md",
    ROOT / "docs" / "CRITICAL_LRP_DASHBOARD.json",
    PROJECT / "results" / "critical-lrp-dashboard.md",
    PROJECT / "results" / "critical-lrp-dashboard.json",
)


def validation_files() -> list[Path]:
    return sorted(
        {ROOT / "PercLib.lean"}
        | {p for p in (ROOT / "PercLib").rglob("*.lean") if not p.is_symlink()}
        | set(ROOT.glob("*.lean"))
    )


def validation_digest() -> str:
    """Digest of exactly the source material used by the Lean package."""
    return hashlib.sha256(
        b"".join(p.relative_to(ROOT).as_posix().encode() + b"\0" + p.read_bytes()
                 for p in validation_files())
    ).hexdigest()


def snapshot_validated(marker: dict, digest: str, build: str, axioms: str,
                       python: str, guards: str) -> bool:
    """Apply historical logs only to their exact recorded source snapshot."""
    return bool(
        marker.get("source_digest") == digest
        and marker.get("status") == "passed"
        and "Build completed successfully" in build
        and re.search(r"^Nonstandard axioms: 0$", axioms, re.M)
        and re.search(r"^sorryAx: 0$", axioms, re.M)
        and re.search(r"^Ran \d+ tests", python, re.M)
        and re.search(r"^OK$", python, re.M)
        and "SEMANTIC-CLOSURE + FROZEN-ANCHOR GUARD OK" in guards
        and "SOURCE-RESTITUTION GUARD OK" in guards
    )


def git(repo: Path, *args: str) -> str | None:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], text=True, capture_output=True, check=False
    )
    return result.stdout.strip() if result.returncode == 0 else None


def evidence() -> dict:
    import os
    activity_path = Path(
        os.environ.get("CRITICAL_LRP_ACTIVITY", str(ACTIVITY))
    )
    activity = json.loads(activity_path.read_text())
    digest = validation_digest()
    rows = [x for x in (ROOT / "docs" / "CRITICAL_LRP_COVERAGE.md").read_text().splitlines()
            if x.startswith("| **I.")]
    counts = Counter(
        status for row in rows for status in ("FULL", "PARTIAL", "NOT FORMALIZED")
        if f"| **{status}** |" in row
    )
    closure = subprocess.run(
        ["python3", "scripts/check_import_closure.py", "PercLib", "--exclude-quarantined"],
        cwd=ROOT, text=True, capture_output=True, check=False
    )
    build_text = (VERIFY / "current-build.log").read_text()
    axiom_text = (VERIFY / "current-production-axiom-summary.log").read_text()
    python_text = (VERIFY / "current-python-tests.log").read_text()
    guards_text = (VERIFY / "current-guards.log").read_text()
    marker_path = VERIFY / "current-validated-state.json"
    marker = json.loads(marker_path.read_text()) if marker_path.exists() else {}
    validation_current = snapshot_validated(
        marker, digest, build_text, axiom_text, python_text, guards_text
    )
    repo = {
        "production_branch": git(ROOT, "branch", "--show-current"),
        "production_head": git(ROOT, "rev-parse", "HEAD"),
        "mirror_branch": git(MIRROR, "branch", "--show-current"),
        "mirror_head": git(MIRROR, "rev-parse", "HEAD"),
        "source_remote_refread_tip": git(ROOT, "rev-parse", f"refs/remotes/omm/{SOURCE_BRANCH}"),
        "production_source": "working tree; may include uncommitted integration work",
        "publication": activity.get(
            "delivery_note",
            "A fetched GitHub tip is reported separately from the local mirror head. "
            "The old production push was rejected for workflow permission; no "
            "force-push, history rewrite, or PR is claimed."
        ),
        "preexisting_workflow_edit_unowned": bool(
            git(ROOT, "diff", "--quiet", "--", ".github/workflows/lean.yml") is None
            or (ROOT / ".github" / "workflows" / "lean.yml").exists()
            and git(ROOT, "diff", "--name-only", "--", ".github/workflows/lean.yml")
        ),
        "source_digest": digest,
        "coverage_digest": hashlib.sha256(
            (ROOT / "docs" / "CRITICAL_LRP_COVERAGE.md").read_bytes()
        ).hexdigest(),
    }
    return {
        "schema": SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "complete": False,
        "completion_note": "The paper is not completely formalized. Neither compilation nor "
            "the source-ledger proportions establishes source fidelity, canonical-model "
            "non-vacuity, or coverage of named external inputs.",
        "repository": repo,
        "source_ledger": {
            "total": len(rows),
            "FULL": counts["FULL"],
            "PARTIAL": counts["PARTIAL"],
            "NOT_FORMALIZED": counts["NOT FORMALIZED"],
            "document": "docs/CRITICAL_LRP_COVERAGE.md",
            "interpretation": "Statement-level ledger, not a completion percentage.",
        },
        "validation": {
            "matches_current_source": bool(validation_current),
            "record": marker or None,
            "state": "passed_for_this_source_snapshot" if validation_current
                     else "pending_or_not_matched_to_current_source",
            "lean_files_in_source_digest": len(validation_files()),
            "import_closure_exit_code": closure.returncode,
            "import_closure_detail": closure.stdout.strip(),
            "latest_recorded_build_succeeded": "Build completed successfully" in build_text,
            "axiom_summary": axiom_text.strip().splitlines(),
            "python_summary": [x for x in python_text.splitlines()
                              if x.startswith("Ran ") or x == "OK"],
            "guards_tail": guards_text.strip().splitlines()[-4:],
            "distinction": "The logs and marker must match the current Lean digest before "
                           "their passing status is applied to this working tree.",
        },
        "activity": activity,
        "maintenance": {
            "activity_snapshot": activity_path.relative_to(ROOT).as_posix(),
            "generated_files": [str(p.relative_to(ROOT).as_posix())
                                if p.is_relative_to(ROOT) else str(p.relative_to(PROJECT))
                                for p in PATHS],
            "update": [
                "Refresh .scratch/dashboard/activity.json from Ultramath direction/report/verdict records.",
                "Run the full validation suite and write current-validated-state.json with its source digest.",
                "Refresh the connected GitHub mirror through the authorized connector before reading its tip.",
                "From the production worktree, run python3 scripts/update_critical_lrp_dashboard.py.",
                "Commit dashboard state with its corresponding proof/integration batch."
            ]
        },
    }


def render(prior: dict | None) -> dict:
    data = evidence()
    if prior and {k: v for k, v in prior.items() if k != "generated_at"} == {
        k: v for k, v in data.items() if k != "generated_at"
    }:
        data["generated_at"] = prior["generated_at"]
    return data


def markdown(data: dict) -> str:
    repo, ledger, val, activity = (
        data[k] for k in ("repository", "source_ledger", "validation", "activity")
    )
    run = activity.get("current_run", {})
    lines = [
        "# Critical long-range percolation I — progress dashboard",
        "",
        "> **THE PAPER IS NOT COMPLETELY FORMALIZED.** This dashboard separates "
        "proof checks, source coverage, model inputs and publication. Do not infer "
        "completion from an import-closure count or a clean axiom report.",
        "",
        f"Generated: `{data['generated_at']}`. Schema: `{data['schema']}`. "
        f"Source digest: `{repo['source_digest']}`.",
        "",
        "## Current snapshot",
        "",
        "| Item | Current value |",
        "|---|---|",
        f"| Production branch | `{repo['production_branch']}` |",
        f"| Committed production revision | `{repo['production_head']}` |",
        f"| Local source-only mirror | `{repo['mirror_head']}` |",
        f"| Fetched GitHub mirror tip | `{repo['source_remote_refread_tip']}` "
        "(reflected remote, fetched through the connected repository) |",
        f"| Current integration batch | `{activity.get('integration', {}).get('state', 'unrecorded')}` |",
        f"| Current source validation | **{val['state']}** |",
        f"| Current research run | `{run.get('id', 'none')}`: "
        f"`{run.get('state', 'unknown')}`, {run.get('working', 0)} working, "
        f"{run.get('accepted', 0)} accepted, {run.get('pending_verdicts', 0)} awaiting verdict |",
        "| Unowned workflow edit | **Excluded from every staging list and mirror patch.** |",
        "",
        "## Source-result ledger",
        "",
        f"**{ledger['FULL']} FULL · {ledger['PARTIAL']} PARTIAL · "
        f"{ledger['NOT_FORMALIZED']} NOT FORMALIZED**, of {ledger['total']} numbered items.",
        "These are deliberately not percentages of completion. FULL entries include printed "
        "conditional claims whose intended canonical-model inputs may still be missing.",
        "",
        "The item-by-item ledger is [CRITICAL_LRP_COVERAGE.md](CRITICAL_LRP_COVERAGE.md). "
        "The independent supporting checks are recorded in "
        "[CRITICAL_LRP_FIDELITY_AUDIT.md](CRITICAL_LRP_FIDELITY_AUDIT.md).",
        "",
        "## Build and proof checks",
        "",
        f"* Import closure: exit **{val['import_closure_exit_code']}**; "
        f"{val['import_closure_detail'] or 'no report yet'}.",
        f"* Latest build log reports success: **{val['latest_recorded_build_succeeded']}**.",
        f"* Latest axiom summary: `{' ; '.join(val['axiom_summary'])}`.",
        f"* Latest Python summary: `{' ; '.join(val['python_summary'])}`.",
        "* These log lines are historical unless `matches_current_source` is true in the JSON.",
        "* The old source-only cold build timed out after one hour; it is **not** a passing "
        "verification and is not being retried unchanged.",
        "",
        "## Next genuine inputs",
        "",
    ]
    lines.extend(f"- {item}" for item in activity.get("next_inputs", []))
    lines += [
        "",
        "## Research activity",
        "",
        f"Previous run `{activity.get('previous_run', {}).get('id')}`: "
        f"{activity.get('previous_run', {}).get('accepted')} accepted reports, solved. "
        "Its older delayed wake notices carry no new pending submission.",
        "",
        "Current participant directions (not accepted results):",
        "",
    ]
    lines.extend(f"- {topic}" for topic in run.get("topics", []))
    lines += [
        "",
        "Only a reviewed, independently rebuilt and integrated submission counts as a result.",
        "A swarm remaining within its own time/step budget is not a weekly-quota signal.",
        f"Quota status: {activity.get('quota', {}).get('meter')}",
        "",
        "## Delivery and maintenance",
        "",
        repo["publication"],
        "",
        "The `docs/` and `results/` copies are generated together. The JSON is the "
        "machine-readable record; Markdown has no live background service privilege.",
        "Refresh it after each accepted packet, validation, commit/push, stalled run or "
        "quota signal:",
        "",
    ]
    lines.extend(f"1. {step}" for step in data["maintenance"]["update"])
    lines += [
        "",
        "```sh",
        "cd .scratch/critical-lrp-orchestration",
        "python3 scripts/update_critical_lrp_dashboard.py",
        "python3 scripts/update_critical_lrp_dashboard.py --check",
        "```",
        "",
        "For the project-overview copy see [results/critical-lrp-dashboard.md]"
        "(../../results/critical-lrp-dashboard.md). The project-root Markdown links have "
        "been normalized separately; this note does not override a source-ledger status.",
        "",
        "The current full-validation log paths are under `.scratch/verification/` in this "
        "production worktree. Use the committed source itself as the reproducible proof artifact.",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if either copy is stale")
    args = parser.parse_args()
    previous_json = PATHS[1].read_text() if PATHS[1].exists() else None
    prior = json.loads(previous_json) if previous_json else None
    data = render(prior)
    doc = markdown(data)
    if data["validation"]["import_closure_exit_code"] != 0:
        raise SystemExit("import closure failed; dashboard not written")
    json_text = json.dumps(data, indent=2) + "\n"
    root_doc = doc.replace(
        "[CRITICAL_LRP_COVERAGE.md](CRITICAL_LRP_COVERAGE.md)",
        "[the production source ledger](../.scratch/critical-lrp-orchestration/docs/CRITICAL_LRP_COVERAGE.md)"
    ).replace(
        "[CRITICAL_LRP_FIDELITY_AUDIT.md](CRITICAL_LRP_FIDELITY_AUDIT.md)",
        "[the source-fidelity review](../.scratch/critical-lrp-orchestration/docs/CRITICAL_LRP_FIDELITY_AUDIT.md)"
    ).replace(
        "[results/critical-lrp-dashboard.md](../../results/critical-lrp-dashboard.md)",
        "[the production dashboard](../.scratch/critical-lrp-orchestration/docs/CRITICAL_LRP_DASHBOARD.md)"
    )
    outputs = ((PATHS[1], json_text), (PATHS[0], doc),
               (PATHS[3], json_text), (PATHS[2], root_doc))
    if args.check:
        stale = [str(p) for p, content in outputs
                 if not p.exists() or p.read_text() != content]
        if stale:
            raise SystemExit("stale or missing dashboard files: " + ", ".join(stale))
        print("All four dashboard files match their evidence snapshot; --check changed nothing.")
    else:
        for path, content in outputs:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        for p in PATHS:
            print(p)


if __name__ == "__main__":
    main()
