# Lean steward log

One dated entry per steward session, newest last, in the handoff format of
[COORDINATION.md](COORDINATION.md) §7. A replacement steward session should be able to
take over from this file and the repository alone.

## 2026-11-12, session 1

```text
Package and branch:
  H-2 on local branch work/H-2-reuse-foundations (worktree .worktrees/H-2 of the
  clone on Tom's Mac). NOT pushed. H-3 and P-1 not started.

Commit:
  3453399 (Lean tree last changed in 85817f4). Base: main at f38c177.
  The commit that adds this log is on top of 3453399 and changes no Lean file.

Done (with declaration names):
  - Claims on H-2, H-3 and P-1 confirmed by Tom in the steward session on
    2026-11-12. This stands in for the "claim confirmed" issue comment of
    COORDINATION §2; the three issues do not exist yet.
  - Planning documents: with Tom's go-ahead, committed as d3f2b80 on
    planning/leadership-reset and pushed to origin. No PR opened (see Not done).
  - Rebased the two commits of PR #2 (da0518b, 4b1f7bf) onto main without
    conflicts; they are now 3b7146d and 3669b3c.
  - D-3: moved Lrp/Percolation/Site/Basic.lean to Lrp/Models/Site/Basic.lean and
    renamed the namespace Lrp.Percolation.Site to Lrp.Models.Site. Deleted the
    wrapper Lrp/Percolation.lean. No definition, statement or proof changed.
    Declarations affected are the whole module, e.g. Lrp.Models.Site.siteConn,
    siteCluster, measurableSet_siteConn, measurableSet_siteInfinite,
    criticalProbSite_mem_Icc. Lrp.Probability.prodBernoulli and its lemmas are
    unchanged and stay canonical.
  - R-2: top-level LICENSE (Apache-2.0 text), top-level NOTICE stating scope,
    and an all-rights-reserved NOTICE in sources/notes/ and docs/sources/notes/.
  - docs/UPSTREAM_REUSE.md and docs/upstream-reuse.json: module paths updated;
    the status now separates the run recorded for the pre-rebase head 4b1f7bf
    from this branch, which has no CI run.
  - Local verification on commit 3453399, macOS arm64, Lean 4.35.0, mathlib
    56a0058: `lake exe cache get` then `lake build --wfail` passed (3149 jobs);
    `lake env lean scripts/AuditImportedPercolation.lean` listed 19 declarations,
    all within propext, Classical.choice, Quot.sound.

Not done:
  - H-2 is not complete: branch not pushed, PR #2 not updated or merged, no CI
    run on the final commit, so the UPSTREAM_REUSE.md status row still says
    "No CI run yet" and must be filled with the run URL before merge.
  - PR for planning/leadership-reset: open it at
    https://github.com/tomhutchcroft/lrp/pull/new/planning/leadership-reset
  - The rooted axiom audit of the CI workflow (lean-action, root Lrp) was not
    run locally; only the 19-name script was.
  - H-3 and P-1.

CI run for this commit:
  None. Local build only.

Changes to any shared file:
  - Lrp.lean: now imports Lrp.Basic, Lrp.Probability.ProdBernoulli and
    Lrp.Models.Site.Basic directly.
  - LICENSE, NOTICE (new, top level).
  - scripts/AuditImportedPercolation.lean: names follow the namespace rename.
    H-3(d) deletes this file.
  - No change to lean-toolchain, lakefile.toml, lake-manifest.json or .github/.

Open questions or needs-decision issues (none filed; no gh CLI on this machine):
  1. How should H-2 reach GitHub: force-push the rebased history to
     reuse/percolation-foundations so PR #2 updates, or push
     work/H-2-reuse-foundations and open a new PR that supersedes PR #2?
  2. COORDINATION §3 says licence files change only in a dedicated PR with no
     mathematics; ROADMAP H-2 puts the LICENSE in the same package as the port.
     The licence files are in their own commit (3453399) so they can be split
     into a separate PR if Tom prefers.
  3. Copyright line. NOTICE names no copyright holder for the Lean code or the
     notes, because R-2 does not. Tom to supply the holder(s).
  4. R-2 does not say how the planning documents under docs/ or the wiki's
     hand-written JS/CSS are licensed. NOTICE covers "the build scripts of the
     wiki prototype" under Apache-2.0 and is silent on the rest.
  5. Wiki data on main (wiki/prototype/content/reuse-audit.json, editorial.json,
     repository-metrics.json) says the port "passed CI at 4b1f7bf" and names
     declarations as Lrp.Percolation.Site.*. After H-2 merges, 4b1f7bf is not an
     ancestor of main and those names no longer exist. Not edited here: wiki
     content belongs to the W packages. It needs a correction before H-2's
     acceptance line ("no document on main calls unmerged work checked") holds.
  6. R-1. On 2026-11-12 the unauthenticated GitHub API returned 404 for
     tomhutchcroft/lrp, which suggests the repository is already private.
     Not confirmed; DECISIONS.md still lists R-1 as open.
  7. D-10 asks UPSTREAM_REUSE.md to cite the CI run on the final commit, but
     recording the URL makes a new commit. Proposed reading: the cited run is the
     one on the last commit that changes any file under Lrp/, and the follow-up
     commit that records the URL is documentation only.
     [WITHDRAWN 2026-11-13. AUDITOR's review of #5: D-10 has no such
     exception. The run cited for a revision is a run on that revision. A
     committed file need not record its own hash; the final SHA and run pair
     go in the PR description or a review comment.]

Approaches that failed, and why:
  - `gh` is not installed and the repository is not readable without
    credentials, so PR #2's CI state and run 43324614451 could not be inspected.
    The run is cited as recorded in the wiki data, not as verified.
  - No elan on this machine. The build used the Lean 4.35.0 toolchain at
    ../near-critical-percolation/.tools/lean-4.35.0-darwin_aarch64/bin (put on
    PATH for the command only) and the existing ~/.cache/mathlib; the worktree
    has its own .lake.
  - The clone has no git user.name/user.email. Commits were made with
    `git -c user.name=… -c user.email=…` using the identity of the existing
    commits; git config was not changed.
```

### Addendum, later in session 1

```text
- With Tom's go-ahead: decisions D-11 to D-17 and the rewritten ROADMAP Phase 2
  committed on planning/leadership-reset on top of d3f2b80 and pushed.
- With Tom's go-ahead: work/H-2-reuse-foundations pushed to origin as a new
  branch. Tom opens a PR that supersedes PR #2 and closes PR #2. Open question 1
  above is answered. CI for this branch runs on push; its run URL still has to be
  recorded in docs/UPSTREAM_REUSE.md.
- New steward duties from those decisions (they are on the planning branch, not
  on this one):
    N-1  rename Lrp -> PercLib, package lrp -> perclib; lakefile.toml, CI audit
         root, every document; no mathematics; after H-2, before P-1. Tom
         renames the GitHub repository himself.
    W-3  the @[tag] attribute and manifest extractor, after P-1.
    D-17 check the current state of Verso once and record it in DECISIONS.md
         before W-3.
    D-16 unproved targets are a tagged `def Name : Prop`, never `sorry`.
- Order of the steward's packages is now H-2, H-3, N-1, P-1, then W-3. The lead's
  message puts N-1 "after H-2 and before P-1"; whether N-1 goes before or after
  H-3 is not stated. H-3 first is assumed, because both edit .github/.
```

## 2026-11-13, session 1 continued: H-3

```text
Package and branch:
  H-3 on local branch work/H-3-ci (worktree .worktrees/H-3), branched from
  work/H-2-reuse-foundations at e5e5521 because (d) deletes a file that H-2
  adds. NOT pushed. Rebase onto main once H-2 has merged.

Commit:
  81c1bfd (the commit that adds this entry is on top and changes only this file).

Done (with declaration names):
  No Lean declaration is added or changed; the Lrp tree and the pins are
  identical to work/H-2-reuse-foundations.
  (a) scripts/check_import_closure.py ROOT. Reads import headers (comments
      stripped), walks the closure from ROOT.lean, and fails on any file under
      ROOT/ that is not reached or any import of a missing project module.
      Takes the root as an argument so that N-1 only changes the argument.
  (b) .github/workflows/lean.yml: triggers are pull_request and push to main.
      workflow_dispatch removed. Runs on main are not cancelled.
  (c) Job "Wiki build": Node 22, npm ci, npm run build in wiki/prototype.
      scripts/build.mjs already throws on an unresolved internal link or an
      unparsable formula, so no new link checker was written.
  (d) scripts/AuditImportedPercolation.lean deleted; docs/UPSTREAM_REUSE.md
      updated to match.
  (e) Job "CI": if: always(), needs the other three, fails unless all three
      results are "success". This is the one check to require in branch
      protection. Tom sets that; the steward does not change settings.

Not done:
  - Nothing in the workflow has run on GitHub. It is an untested draft until a
    PR exists. Only the YAML parse and the Python script were checked locally.
  - The wiki job was not run locally: Node is not installed on this machine.
  - The two acceptance tests on GitHub: a PR adding an unimported file must
    fail, and a PR with a broken wiki link must fail.
  - README.md still says CI "builds pushes and pull requests". Left for H-4.

CI run for this commit:
  None.

Local evidence (not CI), on 81c1bfd:
  check_import_closure.py Lrp        -> ok, 4 modules, exit 0
  with an unimported Lrp/Models/Orphan.lean            -> exit 1
  with the import only inside a comment                -> exit 1
  with the import added to Lrp.lean                    -> exit 0
  with an import of a module that has no file          -> exit 1
  ruby YAML parse of the workflow                      -> four jobs

Changes to any shared file:
  .github/workflows/lean.yml (workflow renamed from "Lean" to "CI"; the file
  name is unchanged), scripts/, docs/UPSTREAM_REUSE.md.

Open questions or needs-decision issues:
  1. After this merges, pushes to branches other than main get no CI run until
     a PR is opened. That is what H-3(b) asks for.
  2. actions/setup-node is pinned to 949feb2 (tag v7.1.0, read with
     git ls-remote on 2026-11-13). It is a new third-party action in CI.
  3. The wiki build writes generated files into the tracked dist/ tree. In CI
     this is harmless. W-2 makes dist/ generated and ignored.

Approaches that failed, and why:
  - Considered checking for a built .olean per source file after lake build.
    Rejected: a restored build cache could hold a stale .olean for a file that
    is no longer imported, and the header check runs without a toolchain.
```

## 2026-11-13, session 1 continued: authority and N-1

```text
Authority:
  Tom confirmed in the steward session on 2026-11-13 the standing authority in
  COORDINATION §1a ("Confirmed as written"). The COORDINATION edit (§1a, §1b
  roster) is committed as dd8b08e on planning/leadership-reset and pushed.
  From here STEWARD reports in this log instead of asking, except for the
  items under "Still needs Tom". Merging stays with Tom until AUDITOR exists.

Package and branch:
  N-1 on work/N-1-rename-perclib (worktree .worktrees/N-1), stacked on
  work/H-3-ci at c33d699. Pushed.

Commit:
  d2dea73 (the commit that adds this entry is on top and changes only this
  file).

Done (with declaration names):
  - Lrp.lean -> PercLib.lean, Lrp/ -> PercLib/, root namespace Lrp -> PercLib.
    Every declaration keeps its name below the root, e.g.
    PercLib.two_mul_le_add_sq, PercLib.Probability.prodBernoulli,
    PercLib.Models.Site.measurableSet_siteConn. No statement or proof changed.
  - lakefile.toml: package perclib, library and default target PercLib.
    lake-manifest.json: the root "name" only. No dependency revision changed.
  - CI: import-closure argument and axiom-audit-root are PercLib.
  - Living documents renamed: README.md, AGENTS.md, NOTICE,
    third_party/percolation/NOTICE (the project's own section),
    docs/UPSTREAM_REUSE.md, docs/upstream-reuse.json, and the functional paths
    in wiki/prototype/scripts/collect-repository-metrics.mjs.
  - Local verification on d2dea73: `lake build --wfail` passed (3149 jobs);
    check_import_closure.py PercLib ok (4 modules); `#print axioms` on the same
    19 declarations as in H-2, under their new names, showed only propext,
    Classical.choice, Quot.sound.

Not done (N-1 acceptance says "no Lrp identifier remains"; these remain, on
purpose, and AUDITOR should rule on each):
  1. GitHub URLs github.com/tomhutchcroft/lrp/... everywhere. They change after
     Tom renames the repository; GitHub redirects the old ones.
  2. docs/DECISIONS.md, ROADMAP.md, COORDINATION.md are on
     planning/leadership-reset, not on this branch. ROADMAP's draft signatures
     say `namespace Lrp.Percolation.Bond` and paths `Lrp/...`. They are
     ARCHITECT's files; after the planning PR merges, the rename there is a
     one-line follow-up PR (Lrp -> PercLib in ROADMAP Phase 0/1 and
     COORDINATION §3 and §5).
  3. docs/PROJECT_PLAN.md and the other three reference documents: frozen by
     D-1.
  4. Records of earlier revisions: the two history rows and three JSON keys in
     the reuse records, and earlier entries of this log.
  5. wiki/prototype/content/*.json, wiki/prototype/README.md and
     dist/assets/app.js. They describe the PR #2 snapshot at 4b1f7bf with the
     names of that revision and are already stale (H-2 open question 5). Left
     to WIKI.
  6. Module doc headers keep one line each recording that the root was renamed
     (Apache-2.0 §4(b) change notice); they no longer contain the old name.

CI run for this commit:
  None. The workflow runs on pull requests only, and no PR is open.

Changes to any shared file:
  PercLib.lean, lakefile.toml, lake-manifest.json (name only),
  .github/workflows/lean.yml, scripts/check_import_closure.py.

PULL REQUESTS TOM NEEDS TO OPEN (no gh on this machine), in merge order:
  a. planning/leadership-reset -> main
     https://github.com/tomhutchcroft/lrp/pull/new/planning/leadership-reset
  b. work/H-2-reuse-foundations -> main; then close PR #2 as superseded
     https://github.com/tomhutchcroft/lrp/pull/new/work/H-2-reuse-foundations
  c. work/H-3-ci -> main (shows only H-3 once b has merged)
     https://github.com/tomhutchcroft/lrp/pull/new/work/H-3-ci
  d. work/N-1-rename-perclib -> main (shows only N-1 once c has merged)
     https://github.com/tomhutchcroft/lrp/pull/new/work/N-1-rename-perclib
  Each later branch contains the earlier ones. If they are merged with merge
  commits in this order, no rebase is needed. If squash-merged, STEWARD rebases
  the next branch before it is merged.

Open questions or needs-decision issues:
  - None new for Tom. Items 1 to 5 above are for AUDITOR.

Approaches that failed, and why:
  - None. The worktree's .lake/packages was made with an APFS copy-on-write
    clone (cp -c -R) of the H-2 worktree's packages, which avoids a second
    mathlib download while keeping a separate .lake.
```

## 2026-11-13, session 1 continued: P-1

```text
Package and branch:
  P-1 on work/P-1-bond-basic (worktree .worktrees/P-1), stacked on
  work/N-1-rename-perclib at 9aa22d1. Pushed.

Commit:
  ab0be77 (the commit that adds this entry is on top and changes only this
  file).

Done (with declaration names), all in namespace PercLib.Percolation.Bond,
file PercLib/Percolation/Bond/Basic.lean:
  Definitions: Config, law, openGraph, conn, cluster, tau, chi;
    instance instIsProbabilityMeasureLaw.
  Conventions: openGraph_adj_iff, openGraph_mono, openGraph_empty,
    mem_conn_iff, mem_cluster_iff.
  Required by the roadmap: conn_self (reflexive), conn_symm (symmetric),
    measurableSet_conn and measurableSet_cluster_infinite (both [Countable V]),
    with conn_eq_iUnion, measurableSet_isChain_openGraph and
    cluster_infinite_eq_iInter behind them.
  Also: conn_trans, conn_mono (connection is increasing), mem_conn_of_mem,
    empty_mem_conn_iff, mem_cluster_self, mem_cluster_comm, cluster_empty,
    one_le_encard_cluster, tau_self, tau_comm, tau_le_one.
  Non-vacuity (D-5): three examples on V = Bool. With every pair open the two
    vertices are connected; with none open they are not; with none open a
    cluster has exactly one vertex.
  PercLib.lean imports the new module.

Local verification on ab0be77 (not CI): `lake build --wfail` passed (3150
  jobs); check_import_closure.py PercLib ok (5 modules); `#print axioms` on
  all 30 theorems, definitions and instances of the module showed nothing
  beyond propext, Classical.choice, Quot.sound; no sorry, admit, axiom or
  native_decide in PercLib/.

D-2: CONFIRMED, with one spelling change and three notes. ARCHITECT expected
P-1 to expose a flaw. At the level of P-1 it did not. What was found:
  1. (change to the draft signature) chi needs the cluster volume coerced from
     ℕ∞ to ℝ≥0∞ inside the integral:
       chi q x = ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q)
     This is the only difference from the ROADMAP draft.
  2. (not a flaw; a duty for P-3) P-1 does not prove that
     ω ↦ (cluster ω x).encard is measurable. chi is well defined without it,
     but the Tonelli step chi = ∑' y, tau needs it. It follows from
     measurableSet_conn and belongs in P-3.
  3. (affects the statements of P-4/P-5) Because q on the diagonal is
     arbitrary, a row-sum hypothesis must exclude w = v explicitly, e.g.
     ∑' w, if w = v then 0 else q s(v, w). "∑' w, q s(v, w) ≤ m" is a stronger
     hypothesis than the target and would make q's diagonal matter.
  4. (not done; needs P-2) D-2 promises "a lemma connecting the two views" for
     a host graph (q = 0 off its edge set). The statement is almost-sure, so
     it needs the cylinder probabilities of P-2. No package owns it yet.
  5. (convention worth knowing) The bond cluster of x always contains x, so
     chi ≥ 1 and tau q x x = 1. The site model differs: a closed vertex has
     an empty cluster. The two are not interchangeable.

PROPOSED EDIT TO DECISIONS D-2, for Tom to approve (not applied):
  - Replace "Cluster volume is ℕ∞-valued and expectations are ℝ≥0∞-valued."
    with "Cluster volume is ℕ∞-valued. Expectations are ℝ≥0∞-valued; the
    susceptibility integrates the volume coerced to ℝ≥0∞. The cluster of x
    contains x."
  - Add "Row sums of q over the neighbours of v exclude w = v explicitly,
    because q on the diagonal is arbitrary."
  - Add "The host-graph lemma is owed after P-2" and name its package.
  ROADMAP: the Phase 1 draft block should show the coercion in chi, and its
  namespace and paths should read PercLib (see N-1, item 2).

Not done:
  - No CI run. No PR. D-12 tags are not attached: the @[tag] attribute is W-3.
  - Mathematical review of the definitions (COORDINATION §5) by Tom or
    AUDITOR.

CI run for this commit:
  None.

Changes to any shared file:
  PercLib.lean (one import added).

PULL REQUESTS TOM NEEDS TO OPEN, added to the list in the N-1 entry:
  e. work/P-1-bond-basic -> main (shows only P-1 once N-1 has merged)
     https://github.com/tomhutchcroft/lrp/pull/new/work/P-1-bond-basic

Signatures for PROVER-B (P-4) and PROVER-A (P-2, P-3, P-5): the declarations
listed above, at ab0be77, are the agreed signatures subject to D-2 review.

Approaches that failed, and why:
  - `Mathlib.Data.Real.ENatENNReal` is a deprecated module at the pinned
    mathlib and fails --wfail; the import is `Mathlib.Basic.Real.ENatENNReal`.
```

## 2026-11-13, session 1 continued: pull requests and CI

```text
gh is installed and signed in as the repository owner (done by Tom). Under
COORDINATION §1a STEWARD opened these pull requests, stacked oldest first:

  #4 planning/leadership-reset -> main          https://github.com/tomhutchcroft/lrp/pull/4
  #5 work/H-2-reuse-foundations -> main         https://github.com/tomhutchcroft/lrp/pull/5  (supersedes #2)
  #6 work/H-3-ci -> work/H-2-reuse-foundations  https://github.com/tomhutchcroft/lrp/pull/6
  #7 work/N-1-rename-perclib -> work/H-3-ci     https://github.com/tomhutchcroft/lrp/pull/7
  #8 work/P-1-bond-basic -> work/N-1-rename-perclib  https://github.com/tomhutchcroft/lrp/pull/8
  #9 planning/d2-amendment -> planning/leadership-reset  https://github.com/tomhutchcroft/lrp/pull/9

CI, read with gh on 2026-11-13. Every run below is on the branch tip at the
time, and every job succeeded.

  #4 dd8b08e  https://github.com/tomhutchcroft/lrp/actions/runs/43366735762
  #5 e5e5521  https://github.com/tomhutchcroft/lrp/actions/runs/43366739795
              (old workflow) axiom-audit: audited 47 declaration(s) under 'Lrp'
  #6 c33d699  https://github.com/tomhutchcroft/lrp/actions/runs/43366741582
              jobs: Import closure, Lean build and axiom audit, Wiki build, CI
  #7 9aa22d1  https://github.com/tomhutchcroft/lrp/actions/runs/43366744370
              axiom-audit: audited 47 declaration(s) under 'PercLib'
  #8 74743dd  https://github.com/tomhutchcroft/lrp/actions/runs/43366748261
              axiom-audit: audited 90 declaration(s) under 'PercLib';
              all within [propext, Classical.choice, Quot.sound]
  #9 2685acc  https://github.com/tomhutchcroft/lrp/actions/runs/43366868682

[Corrected 2026-11-13 after AUDITOR's review of #8.] The local builds in the
earlier entries ran on 3453399 (H-2), d2dea73 (N-1) and ab0be77 (P-1). The
runs above are on the later branch tips e5e5521, 9aa22d1 and 74743dd. They do
not establish CI on the earlier commits, and each is evidence for its own
revision only. Pull-request runs check out GitHub's synthetic merge commit,
not the head commit object. Where the two trees are equal, the run is evidence
for the head's tree, and both SHAs are recorded. This entry adds a commit to
#8; that commit needs its own run.

D-2 amendment:
  ARCHITECT approved the proposed D-2 edit on Tom's behalf. STEWARD applied it,
  with ARCHITECT's decisions on notes 2 to 5 (P-3 owns the measurability of the
  cluster volume; P-4 and P-5 spell the diagonal exclusion; new package P-2b,
  PROVER-A, after P-2; D-3 states the bond/site cluster convention), in #9.

Still owed before merging:
  - H-2: replace "No CI run yet" in docs/UPSTREAM_REUSE.md with run 43366739795.
    [Corrected 2026-11-13: done at eda878f, which has its own run. The
    reading "the last commit that touches Lean" is withdrawn; see open
    question 7 above.]
  - H-3 acceptance tests (an unimported file fails; a broken wiki link fails)
    are not yet run. Plan: two throwaway draft PRs against work/H-3-ci, closed
    after the failure is observed.
  - Merging: nothing merged. Merge order #4, #9 (retargeted), #5, #6, #7, #8,
    by Tom or after AUDITOR approves.
```

## 2026-11-13, session 1 continued: AUDITOR's first reviews, H-3 tests, D-17

```text
Standing instruction from Tom (2026-11-13, in the steward session): work more
autonomously; ask only questions worth interrupting work for hours. Routine
choices are decided by STEWARD and recorded here.

State of main: Tom merged #4 (planning) and #9 (D-2 amendment). D-2 as amended
is on main, along with P-2b, and with P-3 owning the measurability of the
cluster volume.

H-3 acceptance tests: PASSED. Throwaway draft PRs against work/H-3-ci:
  #10 unimported Lrp/Unimported.lean -> Import closure failed (run 43367477381),
      final CI job failed.
  #11 broken link #/no-such-article-h3-test -> Wiki build failed
      (run 43367481362), final CI job failed.
  Both closed, branches deleted.

AUDITOR (Codex) reviewed #5 and #6: required changes, now addressed.
  #5: cite the run on the rebased commit; no "last Lean commit" exception to
      D-10. Accepted; my open question 7 is withdrawn. The reuse records now
      cite runs 43324614451 (4b1f7bf) and 43364411092 (e5e5521), both verified
      with gh, each as evidence for its own revision only.
  #6: all main pushes shared one concurrency group, so a pending run could be
      replaced. The group is now pr-<number> for pull requests and
      run-<run_id> otherwise.
  Method: no rebases. Fixes were carried down the stack by merging
  H-2 -> H-3 -> N-1 -> P-1, so every commit AUDITOR cited stays reachable.
  N-1 merge conflicts in the reuse records were resolved by keeping both
  sides (evidence rows plus the rename note).

CI on the new tips (all jobs passed). Pull-request runs check out a synthetic
merge commit; in each case its tree equals the head's tree.
  #5 eda878f  push 43368358556 (exact checkout), 47 under Lrp;
              pull_request 43368363750
  #6 e10debf  43368382905, merge 389759a, tree eb7499a75fbc, 47 under Lrp
  #7 9da5b81  43368434829, merge 5c62d7e, tree e9aaee7ce4ed, 47 under PercLib
  #8 7e04cfc  43368444781, merge ce649ff, tree a8a1bfdccf50, 90 under PercLib
  #8's head moves with this log commit; its own run is cited in #8.

Claims and issues:
  - "claim confirmed" on #14 (AUDITOR, AUDIT-0) and #17 (PROVER-B, P-4).
    Told PROVER-B: branch from the stack, since PercLib is not on main yet; add
    the PercLib.lean import line in its own PR for STEWARD's review; wait for
    SCOUT's findings.
  - Package issues created after the fact: #21 H-2, #22 H-3, #23 N-1, #24 P-1.
  - #18 (AUDITOR, N-1 scope): proposed acceptance wording for Tom/ARCHITECT.
    Not decided.

D-17 Verso check: done. Finding recorded in DECISIONS by #20 (docs only, open).
  Verso is active and has a v4.35.0 tag. leanprover/verso-blueprint overlaps
  most of D-14 and W-3 to W-5, but it builds the prose with Lean and has no
  licence file. Question raised as needs-decision #19. W-1 and the @[tag]
  attribute are not blocked by it.

Not done / next:
  - Re-review of #5 and #6 by AUDITOR; #7 waits on #18; #8 not yet reviewed.
  - docs/upstream-reuse.json still has per-module "selected-port-pending-ci"
    fields from the original port. They understate rather than overstate,
    so D-10 is not violated. Update them when H-2 is next touched.
  - W-3 can start once P-1 merges and W-1 defines tags. Until then, design
    the @[tag] attribute against D-12 (four-character tags, uniqueness in CI).
```

## 2026-11-13, session 1 end: HANDOFF before the move to a cloud session

```text
Why this entry: Tom asked (via ARCHITECT) for STEWARD to move to a cloud
session so work continues when his laptop is off. Everything below is pushed.
The local worktrees under .worktrees/ on Tom's Mac hold nothing that is not
on origin.

Package and branch / commit (all pushed, all clean):
  H-2  work/H-2-reuse-foundations  eda878f  PR #5  issue #21
  H-3  work/H-3-ci                 e10debf  PR #6  issue #22  (base: H-2)
  N-1  work/N-1-rename-perclib     9da5b81  PR #7  issue #23  (base: H-3)
  P-1  work/P-1-bond-basic         this commit's parent and this commit,
                                   PR #8  issue #24  (base: N-1)
  D-17 planning/d17-verso-finding  67b4579  PR #20 (base: main)
  Stack convention: fixes to a lower branch are MERGED upward (H-2 -> H-3 ->
  N-1 -> P-1), never rebased, so cited commits stay reachable.

Review state (AUDITOR = Codex; it posts COMMENT reviews because the shared
GitHub account cannot approve its own PRs; its Gate 0 report is PR #26):
  #5 H-2  approved by AUDITOR at eda878f (per #26).
  #6 H-3  approved by AUDITOR at e10debf (per #26).
  #7 N-1  mechanically approved; waits on the docs PR below (#18 decided).
  #8 P-1  mathematics approved; two required changes are ADDRESSED in the
          commit before this one (attribution header; log evidence errata).
          Needs: CI on the new head, then AUDITOR re-review.
  #20 D-17  required change NOT yet done (see next item 2).
  Merging: Tom, or STEWARD once AUDITOR has approved and CI is green on the
  final head (COORDINATION §1a). Order #5, #6, #7, #8. When #5 merges, GitHub
  retargets #6 to main, and so on. Nothing has been merged by STEWARD.

NEXT, in order:
  1. N-1 governing record (ARCHITECT's decision in #18, comment 6844522555).
     Docs-only PR against main:
     (a) ROADMAP N-1 acceptance line: replace it with STEWARD's wording quoted
         in #18. No Lrp identifier remains in the Lean library, imports, Lake
         config, CI build/audit roots, or any document describing the
         current API. Historical records keep their names (D-10); the D-1
         documents are unchanged; repository URLs change at Tom's rename.
     (b) ROADMAP W-1 acceptance gains "no Lean declaration name remains in
         article content".
     (c) A dated note under D-11 recording this decision.
     Then link the PR on #7 and ask AUDITOR to re-review #7.
  2. #20: AUDITOR's correction. verso-blueprint has no repository LICENSE
     file, but its source files carry per-file Apache-2.0 notices (Lean FRO
     LLC; e.g. src/VersoBlueprint/DependencyAnalysis.lean:1-5 at 4943d333).
     State both. Remove the sentence "Its code cannot be copied ... until that
     changes"; say instead that any reuse is a decision for Tom/ARCHITECT
     (#19). Push, then ask AUDITOR to re-review.
  3. After #8's new head is green: put the run and the synthetic-merge SHA
     (with tree equality) in #8's description, and ask AUDITOR to re-review.
  4. W-3 (the @[tag] attribute and manifest extractor): starts after P-1
     merges and W-1 (#15) has tags. Read verso-blueprint's
     doc/HELPER_DEPENDENCY_INFERENCE.md for design first (#19 open).
  5. Review PROVER-B's P-4 PR when it appears (#17): branch from the stack,
     one import line in PercLib.lean, SCOUT findings first.
  6. Low priority: docs/upstream-reuse.json per-module "selected-port-
     pending-ci" fields (understated, not overstated).

Who is who now:
  COORDINATOR (cloud, Opus) takes over integrator duties: claims, frontier
  table, digests. Its charter PR says so. STEWARD no longer confirms claims.
  ARCHITECT is in the cloud too. Reach it through issues labelled
  `for-architect`, not session messages. Decisions go to Tom only for the
  "Still needs Tom" list of COORDINATION §1a.

Cloud working notes:
  - In the cloud there is no `gh pr` / `gh issue`. Use the built-in GitHub
    tools or `gh api` (e.g. gh api repos/tomhutchcroft/lrp/pulls/8/reviews).
  - CI is the build. Do not build on Tom's Mac. Only build in the cloud
    sandbox if it has the pinned toolchain (Lean 4.35.0, mathlib 56a00585).
  - Commit identity used so far: the identity of the repository's existing
    commits, passed per command with `git -c user.name=… -c user.email=…`.
    The clone has no configured identity.
  - Pull-request CI runs check out a synthetic merge. Record its SHA and
    check that its tree equals the head's tree (git fetch origin
    refs/pull/N/merge; compare ^{tree}).

CI run for this commit:
  None yet at the time of writing. It is the head of #8; see item 3.

Changes to any shared file in this last step:
  PercLib/Percolation/Bond/Basic.lean (header comment only).

Open questions or needs-decision issues:
  #19 (verso-blueprint adoption, ARCHITECT). Nothing waits on Tom.

Approaches that failed, and why:
  - Rebasing H-2 onto the updated main would have orphaned e5e5521, which the
    evidence rows cite. Undone; merges are used instead.
```

## 2026-11-13, session 2 (cloud): takeover, H-2 and H-3 merged

```text
Takeover:
  This is the cloud STEWARD session that replaces the local one on Tom's Mac.
  Read AGENTS.md, DECISIONS.md, ROADMAP.md, COORDINATION.md on main at b0fdf28,
  then this whole log on work/P-1-bond-basic at 5c773d3 (the handoff above).
  Commit identity in this session: the sandbox's configured git identity.

Erratum to the 2026-11-13 entry "AUDITOR's first reviews, H-3 tests, D-17",
"Not done / next": "#8 not yet reviewed" was wrong when written. AUDITOR had
reviewed #8 at 48ae241 (review 5886331989, required changes) and again at
175e29e (review 5886440415). Its findings: (1) per-file attribution header on
PercLib/Percolation/Bond/Basic.lean, (2) withdraw the last-Lean-commit
reading of D-10, (3) say that the later branch-tip runs are not CI on the
earlier local revisions 3453399, d2dea73, ab0be77, (4) this stale line.
(1) to (3) are addressed at 987ce8f; (4) by this erratum.

Package and branch / commit:
  P-1  work/P-1-bond-basic  this commit (parent 5c773d3)  PR #8, issue #24
  N-1  work/N-1-rename-perclib  9da5b81 (unchanged)       PR #7, issue #23
  N-1 record  planning/n1-acceptance  4ed1270             PR #29

Done:
  - Merged #5 (H-2) into main as 24e62aa, at head eda878f. AUDITOR approved
    that head (review 5886419288); CI on it: push run 43368358556 (exact
    checkout) and pull_request run 43368363750, both success. Main run on
    24e62aa: 43370735386, success (--wfail, 47 declarations under Lrp, within
    propext, Classical.choice, Quot.sound).
  - Retargeted #6 to main and merged it as b6c3ddb, at head e10debf. AUDITOR
    approved that head (review 5886423382); CI run 43368382905, success
    (synthetic merge 389759a, tree eb7499a equal to the head's). The merge
    into main adds only the planning documents already on main
    (DECISIONS, ROADMAP, COORDINATION, AGENTS.md, README.md) to the reviewed
    tree; checked with git merge-tree before merging. Main run on b6c3ddb:
    43371261421, in progress when this entry was written.
  - Retargeted #7 to main.
  - N-1 record (#18): opened #29 (ROADMAP N-1 and W-1 acceptance, dated note
    under D-11). ARCHITECT opened #30 with the same record plus the finding of
    #20 and decision D-18 (verso-blueprint is a reuse source, not the
    platform). #29 is kept only as a fallback if Tom wants the N-1 record
    before deciding D-18; whichever merges first, the other is closed.
  - #20: applied AUDITOR's correction at b1526a9 (checked the licence facts
    from raw files at verso-blueprint 4943d3335ffa: no LICENSE at the root;
    src/VersoBlueprint/DependencyAnalysis.lean, src/VersoBlueprint.lean and
    src/VersoBlueprint/ProvedStatus.lean carry Lean FRO Apache-2.0 notices
    that point to the absent LICENSE). Then closed #20 unmerged, superseded
    by #30 as #30 states.
  - Reviewed #28 (COORDINATOR charter): agree to moving claim duties out of
    §1a; pointed out that its §6 frontier is stale after H-3 merged.
  - Reviewed #30 (record check; no Lean definitions involved).

Not done:
  - PR #2 (superseded by #5) is still open. Closing it was refused by this
    session's permission check; Tom or COORDINATOR should close it. Keep the
    branch: 4b1f7bf is cited as historical evidence.
  - #7: waits for #29 or #30 to merge, then AUDITOR's approval of 9da5b81.
  - #8: needs CI on this commit and AUDITOR's re-review; merges after #7.
    #8's base is work/N-1-rename-perclib; retarget to main after #7 merges.
  - W-3: not started (needs P-1 merged and W-1 tags). D-17 check: done
    (finding in #30).
  - Review of AUDITOR's Gate 0 report #26: it is a draft and its facts
    predate the merges above.

CI run for this commit:
  None yet; cited in #8 when it finishes.

Changes to any shared file:
  None in this commit beyond this log. Main gained H-2 and H-3 by merge.

Open questions or needs-decision issues:
  #19 is answered by D-18 in #30, pending Tom's merge.

Approaches that failed, and why:
  - gh api cannot read leanprover/verso-blueprint in this session (repository
    scope); raw.githubusercontent.com works for public files.
```
