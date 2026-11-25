# Contributing to PercLib

PercLib is a Lean 4 / mathlib library of percolation theory, proved from the axioms,
with a companion wiki. It is led by Tom Hutchcroft. Most of the work is done by AI
agents, and this page is written so that you can hand it to yours. People are equally
welcome and follow the same rules.

The repository is `tomhutchcroft/lrp` and will be renamed `perclib`. It is private:
ask Tom for an invitation first. Never push to `main` or to a branch that is not yours;
everything reaches `main` by pull request.

## The short version

1. Pick an open issue labelled [`open-to-all`](../../issues?q=is%3Aissue+is%3Aopen+label%3Aopen-to-all).
   Comment `claim — <your agent's name>` on it.
2. Branch from `main` and write the Lean. Use a fork, or, if you have been invited to
   the repository, a branch named `work/<your-handle>-<short-name>`.
3. Open a pull request against `main`. CI builds it and audits its axioms.
4. A pull request that adds only theorems and lemmas merges automatically once CI is
   green and an auditor has approved it. You do not need to ask anyone.

## Before you start

- Read [`AGENTS.md`](AGENTS.md), then [`docs/DECISIONS.md`](docs/DECISIONS.md). The
  decisions file is the authority; later decisions override earlier ones.
- Use the pinned toolchain in `lean-toolchain` and the pinned mathlib. Run
  `lake exe cache get` before the first build. Do not upgrade either.
- Give your agent a name that is unique here, built from your GitHub handle, for
  example `jsmith-PROVER-1`. One session per name. Sign comments with it.

## Choosing work

- Issues labelled `open-to-all` are packages whose prerequisites are already merged,
  so they can be done from a fork. Each states the precise statements wanted, the file
  to create, what already exists in mathlib and what to reuse.
- An issue is taken when it has a `claim` comment. Take the lowest-numbered unclaimed
  one unless you have a reason to prefer another. A claim with no pull request after
  three days is released.
- If you want to contribute something that has no issue, open one first, describing the
  statements, and wait for the label. Unrequested work may duplicate work in progress.
- Planar theory, the lace expansion, finite random graphs and scaling limits are not
  scheduled yet. Please do not start them.

## Rules for the Lean

- **No** `sorry`, `admit`, `axiom` or `native_decide`. The only axioms allowed are
  `propext`, `Classical.choice` and `Quot.sound`. CI checks this.
- **The bond interface is fixed** (decision D-2). A bond configuration on `V` is a
  `Set (Sym2 V)`, its law is `PercLib.Probability.prodBernoulli q`, and the open graph
  is `SimpleGraph.fromEdgeSet ω`. The definitions are in
  `PercLib/Percolation/Bond/Basic.lean`. Everything lands on that interface.
- **Do not redefine.** Before adding a definition, search this repository and mathlib.
  A second definition of an existing notion is rejected whatever depends on it.
- **Two kinds of pull request, never mixed** (decision D-24).
  - An *interface* pull request adds definitions, structures, instances, notation or
    tagged statements. It is small, lives in a file named `Basic.lean` or `Defs.lean`,
    and gets a full review. Open it first.
  - A *proof* pull request adds theorems and lemmas only.
- A result from the literature that is used but not proved is an explicit hypothesis,
  bundled as a structure whose name ends in `Input`, with an issue for its proof. It is
  never an axiom (decision D-4).
- A theorem whose hypotheses are not obviously satisfiable comes with a compiled
  example showing that they can hold (decision D-5).
- Code adapted from elsewhere carries a header with its source, revision and licence.
- Every new file is imported from `PercLib.lean`, one import per line, in alphabetical
  order. Modules begin with `module` and use `public import`.
- Do not touch `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` or `.github/`.

## Pull requests

- One file, or one coherent group of results, per pull request. Open it as soon as it
  compiles; small and early is better than large and late.
- Target `main`. In the description give: the issue it addresses; the agent's name and
  the model used; and the person accountable for it.
- Proof bodies are not read by reviewers: the Lean kernel, the build and the axiom
  audit are their check. Statements and definitions are read carefully.
- A review begins with a line `AUDITOR verdict: APPROVED at <commit>` or
  `AUDITOR verdict: CHANGES REQUIRED at <commit>`, followed by numbered changes. Make
  exactly those changes and push; you do not need to reply.
- Only verdicts posted from the repository owner's account count. A workflow merges an
  approved pull request with green CI by itself.
- If a statement you were asked to prove looks false or vacuous, do not weaken it
  silently. Say so on the issue with the counterexample, and prove the corrected
  statement you recommend.

## Licence and credit

Lean code and tooling are under Apache-2.0 (see `LICENSE`). By opening a pull request
you agree that your contribution is licensed on those terms. The lecture notes under
`sources/notes/` and `docs/sources/notes/` are all rights reserved and are not to be
copied. Contributors are credited in the file header of what they write and in the
commit history.

## Questions

Open an issue with the label `question`, or comment on the issue you claimed. Questions
about scope or architecture are answered by the project lead's agent, ARCHITECT, in a
comment that begins "ARCHITECT decision".

## A prompt you can give your agent

```text
You are <NAME>, a prover contributing to PercLib (github.com/tomhutchcroft/lrp), a
Lean 4 / mathlib library of percolation theory proved from the axioms. Read
CONTRIBUTING.md, AGENTS.md and docs/DECISIONS.md in that repository and follow them
exactly. Then: pick the lowest-numbered open issue labelled `open-to-all` that has no
claim comment, comment `claim — <NAME>`, and write the Lean it asks for on a branch
from main named work/<handle>-<short-name> (or in a fork). Never push to main. Build with the pinned toolchain after
`lake exe cache get`. Open a pull request against main as soon as a file compiles, and
make exactly the changes any "AUDITOR verdict: CHANGES REQUIRED" review lists. When the
package is done, take the next one. Never use sorry, admit, axiom or native_decide;
never redefine an existing notion; never mix definitions and proofs in one pull
request; never change the toolchain, the lakefile or .github/.
```
