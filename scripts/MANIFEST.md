# Compiled assertion manifest (W-3)

Run after `lake build --wfail` and the rooted axiom audit:

```
lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json
python3 scripts/build_manifest.py .lake/manifest-raw.json --output .lake/manifest.json
python3 scripts/test_manifest.py
```

The manifest is a CI artifact, never a committed status ledger. `commit` is the actual
checkout (a PR workflow normally checks a synthetic merge); `ci_run` links to that run.
It is not evidence of success until the workflow succeeds. W-4 consumes the artifact
without invoking Lean. No existing theorem is assigned a correspondence tag by W-3.

`@[tag "XXXX"]` persists in compiled module metadata. The extractor loads the whole
root, including private helper bodies and source ranges. It obtains defining modules
from Lean's module index, not declaration namespaces. In the raw snapshot a theorem's
proof is not serialised: its record carries `proof_constants`, the sorted constant and
projection-structure names the proof term references (`null` if it has no body), which is
all the proof frontier uses. Types, statements and definition/opaque bodies are written in
full. Under this repository's standard
Lake layout, module `A.B` maps to `A/B.lean`. Missing source ranges are JSON `null`, never
fabricated. Renaming a namespace does not change that mapping.

Each assertion has its permanent tag, article locator and derived `proof_status`. Formalised
entries also contain declarations (name, displayed type, source file/line), statement,
transitive axioms, named `Input` debts, fingerprint and separate statement/proof tag
frontiers. The entire association map is collected before traversal. Helpers expand
through type and body; tagged declarations stop traversal, self-edges are suppressed,
and visited sets terminate cycles. An external dependency cannot refer back into this
library; its axioms are still included by Lean's transitive `collectAxioms`.

Only tagged definitions, theorems and non-Prop-valued opaque declarations are supported.
Tagged inductives (including empty or inhabited propositions), constructors, recursors
and other declaration kinds fail extraction rather than receiving a default proof status.
Untagged inductives and their constructors still participate in dependency fingerprints
and the public definition index.

A Prop-valued definition is a statement, not a proof. Lean reduces the type telescope
and codomain to recognize Prop aliases; it closes the applied body over the telescope,
including definitions whose values are function aliases rather than literal lambdas. Tagged opaque propositions are
rejected: D-16 uses definitions, and opacity cannot turn a proposition into its proof. Its value, with lambda parameters
turned into universal quantifiers, is the proposition displayed and fingerprinted.
The one allowed shared tag is a statement and a theorem of exactly that statement
applied to its parameter telescope. Incompatible duplicates, unknown/tombstoned tags,
missing bodies and extra axioms fail extraction. All other wiki assertions are
`unformalised`. Named `*Input` parameters (including through definition aliases) yield
`proved-modulo` and a debt list. This follows D-4's Input naming convention; it cannot
infer whether an arbitrarily named hypothesis secretly represents literature debt.
The artifact calls an unproved compiled proposition `statement-only`, not D-4 `stated`:
W-4 must join the fingerprint-matching correspondence review before displaying `stated`.
Correspondence review records, final displayed statuses and staleness belong to W-4.

Fingerprint schema `perclib-statement-v1` is SHA-256 of a structural expression and
its project definition closure. Binder names, declaration names, source locations and
pretty-printer output are excluded. Universe parameters are indexed. Project constants
are numbered by first occurrence in the ordered expression graph; cycles are references
back to those numbers. Definition/opaque bodies, types and inductive constructor data
are included; theorem proofs are excluded from statement fingerprints. External names
and pinned Lean/package revisions are included. Declaration and helper renames preserve
this graph; changing a definition body invalidates it. A schema change requires fresh
reviews. This is a structural fingerprint, not a decision procedure for equivalence.

The Lean API and pinned Verso dependency-traversal source were inspected per SCOUT's
findings on issue #47. The implementation uses Lean directly and introduces no dependency
on Verso or on wiki prose. Integration tests compile separate imported fixture modules;
fixtures are outside `PercLib` and never contribute assertions to the production artifact.


## D-24 definition index and proof-only gate

The same artifact includes `definitions.json`: every exported project non-theorem
constant, with name, kind, type, module-based source location and structural fingerprint.
Visibility comes from each module's exported `.olean` part, not a namespace/name heuristic.
Generated constructors/recursors may have a null source line; private helpers are excluded.
No hand-maintained definition ledger is introduced.

Label a PR `proof` to request the proof-only lane. CI reruns on label changes. Without
that label the PR remains in the interface-review lane. The gate rejects changes to
`Basic.lean`/`Defs.lean`, non-Lean files, interface/metaprogramming command tokens, and any
root change beyond imports. It then builds the event's exact base SHA in an isolated
worktree with its own copied cache and compares **all compiled non-theorem declarations**,
including private helpers, against the head snapshot. It also rejects changed tagged
statements/associations. The head's kernel build and rooted audit remain required.

The token screen is conservative, not a Lean parser or a security boundary; the compiled
comparison is the no-new-definition check. Generated auxiliary definitions can therefore
reject an otherwise mathematical proof: use interface review in that case, rather than
weakening the check or guessing which generated definitions are harmless. This gate
classifies the compiled interface; it is not a mathematical correspondence review and
cannot identify an untagged target by prose intent. User-required reviews still apply.

Local gate regression tests: `python3 scripts/test_proof_pr.py`. CI runs both the gate
regressions and the compiled extraction fixtures before uploading either artifact.
