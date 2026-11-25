# Working on this Lean project

**Read first, in this order:** [docs/DECISIONS.md](docs/DECISIONS.md) (what is decided), [docs/ROADMAP.md](docs/ROADMAP.md) (what to work on), [docs/COORDINATION.md](docs/COORDINATION.md) (how to claim, build and hand off). Do not start a package until its claim is confirmed.

- Use the pinned Lean and mathlib versions in this repository.
- Keep mathematical statements faithful to the requested result. Report any changed hypotheses or conclusions explicitly.
- Put definitions and proofs in `PercLib/` and import completed modules from `PercLib.lean`.
- Use Lean's module system: start modules with `module`, export mathematical dependencies with `public import`, and make the intended declarations public.
- Use focused mathlib imports where practical.
- Validate completed work with `lake build --wfail` and the repository's axiom audit.
- Completed proofs must not depend on `sorry`, `admit`, or additional axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
- A compilation claim must refer to a build that actually ran on the reported revision. Clearly distinguish uncompiled drafts from verified proofs.
- Keep dependency upgrades separate from mathematical changes.

## Code Review Rules

These apply to automated review of pull requests. They follow `docs/DECISIONS.md` (D-4,
D-5, D-6, D-23, D-24), which wins if they disagree.

- Begin the review with one line, exactly `CODEX-REVIEW verdict: APPROVED at <full sha>`
  or `CODEX-REVIEW verdict: CHANGES REQUIRED at <full sha>`. Do not write the words
  "AUDITOR verdict"; that line belongs to the AUDITOR agent.
- **Do not review proof bodies or helper lemmas.** The Lean kernel, `lake build --wfail`
  and the axiom audit check them. Do not comment on proof style, naming of local
  hypotheses, or golfing.
- **Review these, and treat a defect in any of them as P1:**
  - every new or changed `def`, `abbrev`, `structure`, `class`, `instance` and notation:
    is it the right mathematical notion, and does it duplicate something already in
    this repository or in mathlib at the pinned revision;
  - every tagged statement and every roadmap target: does it say what the roadmap or
    the cited source says, with the same hypotheses and conclusion, on the bond
    interface of D-2 (`Set (Sym2 V)` under `PercLib.Probability.prodBernoulli`);
  - vacuity: hypotheses that cannot hold, or a missing compiled witness where D-5
    requires one;
  - `sorry`, `admit`, `axiom`, `native_decide`, or a literature result assumed other
    than as an explicit `…Input` hypothesis with an issue for its proof;
  - adapted code without a header naming its source, revision and licence;
  - a definition outside a file named `Basic.lean` or `Defs.lean` (pull requests opened
    after 14 November 2026);
  - a change to `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` or `.github/`
    mixed with mathematics.
- A pull request that adds only theorems and lemmas, with none of the above, is
  approved without further comment.
- For documents and wiki pages: check only that tags, anchors and the mathematical
  content of tagged statements are unchanged, and that a claim of "passes" or "green"
  cites a CI run. Do not review prose style.
- List required changes as numbered, concrete edits. Raise nothing below P1.
