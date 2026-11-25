# Coordination

**12 November 2026.** How people and agents work on this repository. What to work on is
in [ROADMAP.md](ROADMAP.md). What has been decided is in [DECISIONS.md](DECISIONS.md).

## 1. Roles

| Role | Holder | Authority |
|---|---|---|
| Mathematical lead | Tom Hutchcroft | Scope, statement fidelity, source corrections, everything marked R-n. |
| ARCHITECT (project lead) | Claude session named ARCHITECT; not continuously present | High-level plan, architecture and the decision record. Audits the plan and its execution at each gate from the AUDITOR's reports. Does no implementation and no line-by-line review. Acts only through PRs to `DECISIONS.md`, `ROADMAP.md` and this file. |
| Lean steward | A dedicated agent session, subordinate to Tom (R-4) | The D-2 interface, shared definitions, dependency pins, CI. |
| Integrator (COORDINATOR) | Claude session named COORDINATOR, subordinate to Tom and ARCHITECT; charter in §1c | Confirms claims, releases stale ones, keeps the frontier in §6 current, triages `needs-decision` issues, writes the daily digest, closes superseded and duplicate pull requests (D-20). Does not merge: STEWARD merges (D-20). |
| Contributor | One accountable human or agent per package | Everything inside the package's owned files. |

### 1a. Lean steward charter

The steward is one dedicated agent session at a time. It reports to Tom, who can overrule
it on anything.

- **Owns:** the D-2 bond interface, everything under `PercLib/Probability/`, `PercLib.lean`,
  the toolchain and dependency pins, and `.github/`.
- **First tasks:** H-2, H-3, then P-1. P-1 is the steward's own package because it
  fixes the interface.
- **Reviews:** every PR that adds or changes a definition or a roadmap target statement.
- **Does not:** change a roadmap target, add an `Input` without an issue for its proof,
  or merge a PR that AUDITOR has not approved.
- **Escalates to Tom:** any amendment to D-2, any dependency upgrade, any statement that
  looks false or vacuous.
- **Standing authority** (granted by Tom on 13 November 2026: "I need STEWARD to run
  more independently from me"). Without asking, STEWARD may: commit; push `work/*` and
  `planning/*` branches; open, update and close pull requests; read CI; rebase its own
  branches; start its next package when the previous one is in review. Confirming
  claims and releasing stale ones moved to COORDINATOR (§1c) on 13 November 2026.
- **Merging** is governed by D-20: "STEWARD merges every pull request, whoever wrote
  it, once CI is green on its final commit and AUDITOR has approved that commit. This
  includes pull requests to this file, to `ROADMAP.md` and to `COORDINATION.md`, and
  AUDITOR's own reports, which STEWARD reviews in AUDITOR's place."
- **Still needs Tom** (D-20, "Still Tom's alone"): "The reserved items R-n; repository
  settings, visibility and the rename; anything irreversible, including force pushes to
  `main`; scope and the fidelity of a target statement to its source; approval of
  `wiki/STYLE.md` (D-19)." Also kept from this charter, because D-20 does not address
  them: deleting others' branches, and dependency or toolchain upgrades.
- **Reporting instead of asking:** STEWARD writes what it did in `docs/STEWARD_LOG.md`
  and stops to ask only for the items in the previous bullet.
- **Continuity:** the steward keeps `docs/STEWARD_LOG.md`, one dated entry per session
  in the §7 handoff format, so a replacement session can take over from the repository
  alone.

### 1b. Agent roster

Set 13 November 2026. All agents are subordinate to Tom. Each works only on its own
packages and files (§3) and ends every session with a §7 handoff note.

| Name | Kind | Packages | Writes to |
|---|---|---|---|
| STEWARD | Claude session | H-2, H-3, N-1, P-1, W-3; reviews every definition and target statement; merges under §1a | Foundations, CI, pins, `PercLib.lean` |
| PROVER-A | Codex | P-2, P-2b, P-3, P-5; then T-3, T-5 | Its package files only |
| PROVER-B | Codex | P-4, P-6, P-7; then T-2, T-4, T-6 | Its package files only |
| WIKI | Codex | W-1, W-2, W-4, W-5, W-6 | `wiki/` only; never `PercLib/` |
| AUDITOR | Codex | Line-by-line review of every PR before merge; audits STEWARD's PRs too; writes a gate report for ARCHITECT | `docs/audits/` only |
| SCOUT | Codex | T-1, F-1, mathlib and upstream search for each package before it starts, source locators and `occurs_in` records | `docs/` inventories and source records only |
| COORDINATOR | Claude session | Integrator (§1c): claims, frontier, `needs-decision` triage, collision flags, daily digest | `docs/digests/`, §6 of this file, and issue and PR comments and labels only |
| MANAGER | Codex | Added by Tom on 13 November 2026 (D-21). Keeps the other Codex agents working whenever they have work to do; does not manage Claude sessions | Issue comments only |

Rules specific to the roster:

- AUDITOR never writes Lean or wiki content and never reviews its own output. Its review
  covers: the statement against the roadmap and the source; the bodies of definitions in
  the statement; non-vacuity (D-5); cited inputs (D-4); and every claim of "passed" or
  "checked" against a CI run on that commit (D-10).
- A prover starts a package only after SCOUT has posted the reuse findings for it and
  STEWARD has confirmed the signatures it depends on.
- Builds: one `lake build` at a time on any one machine (§4). Agents that can build in
  their own cloud sandbox or through CI do so; they do not build on Tom's Mac in parallel.
- Start order: SCOUT, AUDITOR and WIKI now. PROVER-B when P-1's signatures are agreed.
  PROVER-A when P-1 merges.
- A gate report from AUDITOR is one page: what merged, what the evidence is, deviations
  from DECISIONS, and the three biggest risks. ARCHITECT reads only these.

Because ARCHITECT is not present between sessions, a question for ARCHITECT is
raised as an issue labelled `needs-decision` and answered by Tom, or by the next ARCHITECT
session, with an edit to `DECISIONS.md`. COORDINATOR triages each such issue first (§1c);
ARCHITECT reads only those labelled `for-architect`. Work that does not depend on the
answer continues.

### 1c. COORDINATOR charter

Set 13 November 2026 at Tom's request. COORDINATOR is one Claude session at a time. It
reports to Tom and to ARCHITECT, is the integrator of §1, and is the single channel
between Tom, ARCHITECT and the other agents, so that Tom and ARCHITECT do not read
routine notes.

On every run it does one full pass:

1. Reads new issues, pull requests, reviews and §7 handoff notes since its last pass.
2. Triages every `needs-decision` issue. If `DECISIONS.md` already answers it,
   COORDINATOR replies quoting the decision and closes the issue. Otherwise it comments
   a three-line brief for ARCHITECT (the question, the options, links to the evidence)
   and labels the issue `for-architect`.
3. Confirms new claims (§2), releases claims stale for three days, and keeps the
   frontier table in §6 current through docs-only pull requests.
4. Flags collisions: two agents on one file, a package started before its prerequisite
   merged, a pull request waiting on review for more than a day.
5. Writes the daily digest for Tom in `docs/digests/YYYY-MM-DD.md`, in under 200 words:
   what merged, what is blocked and on whom, and "a list of at most five items that need
   him, each as a question he can answer in a line" (D-20). Nothing else is addressed to
   Tom.
6. Closes "superseded and duplicate pull requests and stale issues, and resolves
   collisions between agents, without asking" (D-20).

Limits:

- **Never:** decides policy; changes `DECISIONS.md` or a roadmap target; approves or
  merges a pull request; writes Lean or wiki content.
- Quotes and links decisions; does not restate them in its own words.
- Passes on every required change or risk raised by AUDITOR unedited.
- Signs every comment "COORDINATOR".

Division of work with MANAGER (§1b):

- COORDINATOR says what work exists. It keeps the per-agent work queues on the roll-call
  issue (#34), confirms claims and opens package issues.
- MANAGER makes sure the Codex agents do that work. Its scope and limits are D-21. It
  reports to COORDINATOR on #34 any agent that is stuck, does not respond, or has
  nothing it can start.
- Neither assigns packages outside the roster or decides policy.

## 2. Claiming work

1. One GitHub issue per roadmap package, titled with its ID, for example `P-3`.
2. A package is claimed when the issue has an assignee and the integrator has commented
   `claim confirmed`. Before that, do not start.
3. One owner per package. One branch per package, named `work/<ID>-<short-name>`.
4. A claim with no pushed commit and no comment for three days is released by the
   integrator.
5. The issue is the only record of ownership. There is no second ledger in this file.

## 3. What a contributor may change

- **Freely:** the files the package names, and new helper lemmas inside them.
- **With the Lean steward's review:** anything under `PercLib/Probability/`, any definition
  in `PercLib/Percolation/Bond/Basic.lean`, `PercLib.lean`.
- **Only in a dedicated PR with no mathematics:** `lean-toolchain`, `lakefile.toml`,
  `lake-manifest.json`, `.github/`, licence files.
- **Never:** another package's files; the statement of a roadmap target. If the target
  looks wrong or unprovable, stop and open a `needs-decision` issue with the
  counterexample or the missing hypothesis.

Before creating a file, list the directory and search open PRs for the path. Two
packages creating the same file is the most common collision.

## 4. Building

- Use the pinned toolchain. Run `lake exe cache get` before the first build.
- One `lake build` at a time per machine. Lean builds exhaust memory when run in
  parallel, and the result is slower, not faster.
- Never kill a build or a verification run that another contributor started. Ask in the
  issue.
- Each contributor uses a separate checkout or worktree with its own `.lake`.
- A claim that something compiles refers to a build that ran on the stated commit.

## 5. Pull requests

A PR is ready for review when all of these hold.

- [ ] It implements one roadmap package, named in the title.
- [ ] `lake build --wfail` and the axiom audit pass in CI on the final commit.
- [ ] Every new file under `PercLib/` is imported from `PercLib.lean`.
- [ ] Each target statement matches the roadmap, or the difference is stated at the top
      of the PR description and has a `needs-decision` issue.
- [ ] Non-vacuity witnesses are included where D-5 requires them.
- [ ] Any cited literature result is an `Input` hypothesis listed in
      `docs/CITED_INPUTS.md` (D-4). There is no `axiom`, `sorry` or `native_decide`.
- [ ] Adapted code carries the source, revision and licence in its header (D-6).
- [ ] The description says which model assistance was used and who is accountable.

Review: definitions and target statements need the Lean steward and a mathematical
review of the statement and of the bodies of the definitions it uses. Helper lemmas need
one reviewer. STEWARD merges, under D-20, once AUDITOR has approved the final commit and
CI is green on it; no other author merges their own PR.

## 6. Current frontier

Updated by the integrator when a phase changes. Ownership is on the issues, not here.

As of 13 November 2026, 06:05 UTC. Merged on `main`: H-2 (#5) and H-3 (#6, `b6c3ddb`).
No Phase 1 package has merged. "In review" means an open, unmerged pull request.

| Ready now | Blocked | Blocked by |
|---|---|---|
| R-1 (Tom) | N-1 (#7, in review) | the #18 record (#30, or #29) merging |
| H-4, T-1, F-1 | P-1 (#8, in review) | N-1 merging |
| P-4 (claimed) | P-2, P-3 (#31) | P-1 merging (PROVER-A starts then, §1b) |
| W-1 (claimed) | P-2b | P-2 |
| | P-5 | P-2, P-3, P-4 |
| | W-2 | W-1 |
| | W-3, W-4 | P-1 and W-1; P-5, W-2 and W-3 |

## 7. Handoff note

Posted as the last comment on the issue whenever a session ends, finished or not.

```text
Package and branch:
Commit:
Done (with declaration names):
Not done:
CI run for this commit:
Changes to any shared file:
Open questions or needs-decision issues:
Approaches that failed, and why:
```

## 8. Reporting

Report what the evidence shows. "Proved" means D-4 `proved` on a named commit with a CI
run. "Proved modulo" names the inputs and is never reported as a completed target. A draft that has not compiled is called an
uncompiled draft. Nothing on `main` describes unmerged work as present (D-10).
