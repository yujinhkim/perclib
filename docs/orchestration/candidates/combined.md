GRAPH_VERSION: 4
ROOTS: hutchcroft.i.1.6,hutchcroft.i.1.15
CORPUS: .scratch/source/paper.html | arXiv:2508.18807v1
CONVENTIONS: unit-volume unit ball and C=1; imported packet only, not reviewed source topology
STANDING_ASSUMPTIONS: assumption.hd,assumption.weighted_graph,hutchcroft.a.cutoff,hutchcroft.a.norm
EXTERNAL_POLICY: named cited inputs only; packet claims remain unverified
FROZEN_ANCHORS: hutchcroft.i.1.6,hutchcroft.i.1.15
FROZEN_MANIFEST: docs/orchestration/FROZEN_ANCHOR_MANIFEST.json | sha256:bb855df26fab249019a04a395d3e613446796ce0d4d6a648a58e969359011c36
WRITER: openmathmodel-orchestrator
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

## Nodes

NODE: convention.asymptotic_notation
KIND: definition
TITLE: Asymptotic notation `≍`, `⪯`, `⪰`, `O`, `o`, `∼` and the implicit-constant convention (§I.1.1)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS1.p9@L325-L329
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.1.asymptotic_notation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (notation).
SOURCE_QUANTIFIERS: all functions of the displayed variables; `n ≥ 1` where `O(n)` is used.
SOURCE_CONCLUSION: `≍`, `⪯`, `⪰` denote (in)equalities up to positive multiplicative constants depending on `d ≥ 1`, `α > 0` and the kernel `J` but on no other parameter, with subscripts adding dependence; for non-negative `f`, `f(n) = O(n)` and `f(n) ⪯ n` both mean `∃C > 0 ∀n ≥ 1, f(n) ≤ Cn`; `f = o(g)` means `f/g → 0`; `f ∼ g` means `f/g → 1`; `O`/`o` quantities are non-negative; `±O`, `±o` mark uncertain sign.
CONSTANT_SCOPE: only `d`, `α`, `J`, plus declared subscripts. `(2p−3)!!` is outside this scope and is a pure number.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (notation). Consumed by both roots (`∼` in (I.1.6)/(I.1.7), (I.1.16)/(I.1.17)) and by `route.hd.case2/3` (`⪯`). The printed scope "not on any other parameters" is what forbids `⪯`-constants depending on `r`, `p` or `n` un-subscripted. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.2.model
KIND: definition
TITLE: Long-range percolation random graph and its law (unnumbered model paragraph, §I.1.2)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.model
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition of the model); `d ≥ 1`; `β ≥ 0`; `J : Z^d × Z^d → [0,∞)` symmetric and translation-invariant, `J(x,y) = J(y,x) = J(0,y−x)`.
SOURCE_QUANTIFIERS: each unordered pair `{x,y}`, `x ≠ y`, independently; all `β ≥ 0`.
SOURCE_CONCLUSION: the random graph on `Z^d` in which each pair `x ≠ y` carries the edge `{x,y}` with probability `1 − e^{−βJ(x,y)}`, independently over pairs; open/closed edges; clusters = connected components; `P_β`, `E_β` the law and expectation.
CONSTANT_SCOPE: none: the edge probability is exactly as printed.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (definition). The motivating decay (I.1.1) `J(x,y) ∼ const.‖x−y‖^{−d−α}` is printed in the same element as motivation only; the operative class is Definition I.1.3, and no record in this file uses (I.1.1) as a premise. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.2.betac
KIND: definition
TITLE: The critical point `β_c` (unnumbered, §I.1.2)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.betac
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition); the law `P_β` of `hutchcroft.i.1.2.model`.
SOURCE_QUANTIFIERS: infimum over `β ≥ 0`.
SOURCE_CONCLUSION: `β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`; `β_c` is always the critical parameter of the *original* kernel `J`, so it is unchanged by the cut-off of Definition I.1.5.
CONSTANT_SCOPE: none (definition); `β_c` is normalization-dependent through (*) (quoted in `hutchcroft.i.1.3`).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.2.model
ROUTES: -
ROUTE_FOR: -
NOTE: The same element prints the ambient background sentence "which satisfies `0 < β_c < ∞` whenever `d ≥ 2` and `α > 0` or `d = 1` and `0 < α ≤ 1` [90, 97, 45]", and the continuity sentence "there are no infinite clusters at `β_c` whenever `0 < α < d` (Berger [22])" with the conjectured extension and the known discontinuity at `d = α = 1` [5, 41]. This record asserts neither: `β_c ∈ (0,∞)` is discharged by `hutchcroft.i.1.2.betac.pos`/`.fin`, and **no record in this file asserts `θ(β_c) = 0`**, universally or as a hypothesis. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.2.model | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: the probability spaces `P_β` over which the infimum is taken

NODE: hutchcroft.i.1.2.betac.pos
KIND: step
TITLE: `β_c > 0`: first moment of the subcritical branching (walk) comparison
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
CONTRACT_ID: hutchcroft.i.1.2.betac.pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model of `hutchcroft.i.1.2.model` with the kernel class of `hutchcroft.i.1.3`; `m := Σ_{y≠0} J(0,y) < ∞`.
SOURCE_QUANTIFIERS: every `β ≥ 0` with `βm < 1`.
SOURCE_CONCLUSION: `Σ_{x∈Z^d} P_β(0 ↔ x) ≤ Σ_{n≥0} (βm)^n = 1/(1−βm) < ∞`; hence the cluster of the origin is a.s. finite for every `β < 1/m`, so `β_c ≥ 1/m > 0`.
CONSTANT_SCOPE: no implicit constant: the bound is `1/(1−βm)` with `m` the explicit kernel mass.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.2.model,hutchcroft.i.1.3
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm3@L370-L416 Argument (mine, elementary; no literature): `1 − e^{−t} ≤ t` for `t ≥ 0`; a connection `0 ↔ x` implies the existence of a finite (possibly self-intersecting) walk `0 = x_0, …, x_n = x` all of whose edges are open; independence over distinct edges and the union bound over walks give `Σ_x P_β(0↔x) ≤ Σ_n β^n Σ_{x_1..x_{n−1}} Π_i J(x_{i−1},x_i) ≤ Σ_n (βm)^n`; repeated edges and vertices only enlarge the walk set, so the comparison is an upper bound. Translation invariance plus a countable union over origins extends "origin cluster finite a.s." to "no infinite cluster a.s.". Monotonicity of `1−e^{−βJ}` in `β` makes every such `β` subcritical. This is the *small-beta walk first-moment* half of the derived obligation `0 < β_c < ∞`; it is a derived `step`, not a free `hbc` binder and not a citation. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SOURCE_GAP: the paper asserts positivity/finiteness once at canonical paper-tex.txt L49 with citations [90,97,45]; no proof is printed in this slice. The argument in this record is a derived obligation, not a quotation of a printed proof. PROOF_SOURCE is the source assertion's statement locator, not Definition I.1.3 mislabelled as a proof.
EDGE: hutchcroft.i.1.2.model | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: the independent edge law `1 − e^{−βJ(x,y)} ≤ βJ(x,y)`, the only place the law enters
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: gives `J(r) = ∫_r^∞∣J'∣` with `∣J'(r)∣ = C(1+δ_r)r^{−d−α−1}`, so `m ≍ Σ_{y≠0}‖y‖^{−d−α} < ∞` because `α > 0`, and `m > 0` because `C > 0`

NODE: hutchcroft.i.1.2.betac.fin
KIND: step
TITLE: `β_c < ∞`: domination by bond percolation (`d ≥ 2`) and by 1-D long-range percolation (`d = 1`)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
CONTRACT_ID: hutchcroft.i.1.2.betac.fin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model and kernel class of `hutchcroft.i.1.2.model`, `hutchcroft.i.1.3`; `d ≥ 1`; `α > 0`.
SOURCE_QUANTIFIERS: the two cases `d ≥ 2` and `d = 1` separately; `β → ∞`.
SOURCE_CONCLUSION: (i) d >= 2: with c_* := min_{‖v‖_1=1}J(0,v)>0 and p(beta) := 1-exp(-beta*c_*), any p(beta)>p_0(d) for a nearest-neighbour supercritical threshold p_0(d)<1 gives an infinite cluster almost surely, hence beta_c <= -log(1-p_0(d))/c_* < infinity. (ii) d=1, 0<alpha<=1: ext.lr_d1_alpha_le_1 supplies finite beta_1 with a.s. percolation for each beta>beta_1, hence beta_c <= beta_1 < infinity. Both follow from appropriate supercritical thresholds, not the false claim that these models percolate for every beta>0.
CONSTANT_SCOPE: the thresholds `p_0(d)` and the 1-D statement are those of the two external leaves; no other constant is hidden.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.2.model,hutchcroft.i.1.3,ext.zoo_subcritical_pc,ext.lr_d1_alpha_le_1
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm3@L370-L416 Domain restriction is not a narrowing. The roots' domains are (HD) and `{d = 3α}`; (HD)1 with `d = 1` gives `3α < 1`, and `d = 3α` with `d = 1` gives `α = 1/3`; in both `0 < α ≤ 1`, exactly the printed p. 6 range, so case (ii) is only ever used inside the paper's own claim. DEAD END, recorded so it is not re-used: `docs/orchestration/DERIVED_CRITICAL_POINT.md` derives `β_c < ∞` by restricting to the nearest-neighbour chain `{kv,(k+1)v}` and invoking "the standard exact one-dimensional percolation threshold" at `p > 1/2`. Nearest-neighbour bond percolation on `Z` has `p_c = 1` (its cluster is the maximal run of open bonds), so no `p < 1` suffices and that route does not establish finiteness. The repair used here is the dimension split above; the 1-D long-range route (with `p_k ≍ βk^{−1−α}`) is a genuine theorem but is external, and its exact hypotheses are the job of a literature direction, not of this packet. `0 < β_c < ∞` is still a derived obligation, not a binder: this record and `.pos` are its two derivations. LIMIT OF THIS RECORD, stated so it is not over-claimed: the two cases above discharge `β_c ∈ (0,∞)` on the **union of the two roots' domains**, not on the whole printed kernel class. `d = 1` with `α > 1` is outside both domains and is **not** discharged here; a claim of the form "`0 < β_c < ∞` for every `d ≥ 1`, `α > 0`" additionally needs the one-dimensional long-range large-`β` theorem (`p_k ≍ βk^{−1−α'}` percolates for `β` large, `α' = d+α−1 > 0`), which is a genuine theorem of Schulman/Newman–Schulman type — the orchestration doc's nearest-neighbour route does **not** give it (see the DEAD END above). No record in this file asserts the unrestricted claim. COORDINATOR REPAIR: the central critical-point note now uses a finite-range square-lattice embedding with two positive weights and Kesten's Z^2 theorem, not the superseded nearest-neighbour Z argument. This packet's older alternative construction and named external leaves remain unverified research, not the proof of the corrected central derivation. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SOURCE_GAP: the paper asserts positivity/finiteness once at canonical paper-tex.txt L49 with citations [90,97,45]; no proof is printed in this slice. The argument in this record is a derived obligation, not a quotation of a printed proof. PROOF_SOURCE is the source assertion's statement locator, not Definition I.1.3 mislabelled as a proof.
EDGE: hutchcroft.i.1.2.model | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: the edge law on the nearest-neighbour pairs of `Z^d`
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: `J(r) = ∫_r^∞∣J'∣ ≥ c r^{−d−α}` for `r ≥ r_0` and `J(r) > 0` for every `r > 0`; this is what makes `c_* > 0` and what gives the 1-D profile `p_k ≥ 1 − e^{−cβk^{−d−α}}`
EDGE: ext.zoo_subcritical_pc | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: supplies a single number `p_0(d) < 1` so that `p(β) > p_0(d)` forces percolation
EDGE: ext.lr_d1_alpha_le_1 | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: supplies `d = 1, 0 < α ≤ 1` finiteness, the only `d = 1` range occurring on either root's domain

NODE: ext.zoo_subcritical_pc
KIND: external
TITLE: Bond percolation on `Z^d`, `d ≥ 2`, is not percolating at small `p` (i.e. `p_c(Z^d) < 1`)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: -
CONTRACT_ID: ext.zoo_subcritical_pc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: independent bond percolation on the nearest-neighbour lattice `Z^d`, `d ≥ 2`, with parameter `p ∈ [0,1]`.
SOURCE_QUANTIFIERS: `d ≥ 2`; `p ∈ [0,1]`.
SOURCE_CONCLUSION: `∃ p_0 = p_0(d) < 1` such that for every `p > p_0` an infinite cluster exists a.s.
CONSTANT_SCOPE: `p_0` depends on `d` only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (external). Deliberately states `p_0 < 1`, not "`1/2`" and not "the threshold": the quantity the consumer needs is a strict inequality below 1. A citation is not a proof; the record stays `PROPOSED`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: ext.lr_d1_alpha_le_1
KIND: external
TITLE: One-dimensional long-range percolation: finite supercritical threshold for 0<alpha<=1
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: -
CONTRACT_ID: ext.lr_d1_alpha_le_1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: independent nearest-neighbour-excluded edges on Z with open probability bounded below by 1-exp(-c*beta*|i-j|^{-(1+alpha)}) for some c>0; 0<alpha<=1; beta>0
SOURCE_QUANTIFIERS: every `β > 0`; `0 < α ≤ 1`.
SOURCE_CONCLUSION: some beta_1(alpha,c) < infinity exists such that an infinite cluster exists almost surely whenever beta>beta_1; hence beta_c <= beta_1 < infinity. Positivity of beta_c is not part of this external leaf and is discharged separately by the walk bound.
CONSTANT_SCOPE: no constant is extracted; only the qualitative conclusion is used.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (external). Discharges exactly one thing: finiteness of `β_c` for `d = 1, 0 < α ≤ 1`. It does **not** discharge the `d = 1, α > 1` case (outside both roots' domains) and is not a statement about `d ≥ 2`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CORRECTION: an earlier 'percolates for every beta>0' statement implied beta_c=0 and contradicted the elementary positive lower bound in betac.pos. Only finiteness of the supercritical threshold is asserted; [90,97,45] were not opened by this campaign. Use ONLY for beta_c < infinity; beta_c > 0 is not an external premise and must not be bundled here.

NODE: hutchcroft.i.1.3
KIND: definition
TITLE: Definition I.1.3 (Assumptions on the kernel)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm3@L370-L416
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition of the kernel class); `d ≥ 1`; `‖·‖` a norm on `R^d`; `α > 0`; `J` translation-invariant.
SOURCE_QUANTIFIERS: all `x, y ∈ Z^d`; all `r > 0`; all `s` in the integral.
SOURCE_CONCLUSION: `J(x,y)` is a decreasing, differentiable function of `‖x−y‖` when `x ≠ y` and vanishes otherwise, so that (I.1.2) holds; `|J'(r)| = C(1+δ_r)r^{−d−α−1}` with `C > 0` and `δ` measurable and logarithmically integrable (footnote 4: `δ_r → 0`, `δ` locally integrable on some `[r_0,∞)`, `∫_{r_0}^∞|δ_r| dr/r < ∞`); WLOG the `‖·‖`-unit ball has unit Lebesgue measure and `C = 1`, so that (*) holds.
CONSTANT_SCOPE: `C > 0`; after the WLOG `C = 1` and `|unit ball| = 1`. The constants `α/β_c` of (I.1.6)-(I.1.7) and (I.1.16)-(I.1.17) depend on (*); the combinatorial factor `(2p−3)!!` does not.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.2.model,hutchcroft.i.1.3.disp.I.1.2,hutchcroft.i.1.3.disp.star
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_CORRECTION (replaces v3's `SOURCE_GAP`). v3 recorded a gap because "`J(r) → 0` is not stated". It is not a gap: the class **assumes** the identity (I.1.2) ("so that we can write"), and (I.1.2) *is* `J(r) = ∫_r^∞|J'(s)| ds`; with `|J'| = C(1+δ_r)r^{−d−α−1}` the integral converges (`∫|δ_s| s^{−d−α−1}ds ≤ ∫|δ_s| ds/s < ∞` for `s ≥ 1`), so `J(∞) = 0` is a hypothesis of the class, not a missing inference. Consequently the class also excludes `J ≡ 0` (`C > 0` forces `J' ≢ 0`) and forces `J(0,v) > 0` for every `v ≠ 0`; both are used by `hutchcroft.i.1.2.betac.fin`. Remark I.1.4 in the same section relaxes (I.1.2) to `‖x−y‖` large and allows small-scale kernels that are not functions of the norm. That relaxation is **not** used by either root here and is not a record; a reader who needs it must open `#S1.Thmthm4@L417-L422`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.2.model | .scratch/source/paper.html#S1.Thmthm3@L370-L416 | packet relation requires: the translation-invariant kernel `J` of the model is the object restricted here
EDGE: hutchcroft.i.1.3.disp.I.1.2 | .scratch/source/paper.html#S1.Thmthm3@L370-L416 | packet relation requires: the identity (I.1.2) is one of the two things the class asserts
EDGE: hutchcroft.i.1.3.disp.star | .scratch/source/paper.html#S1.Thmthm3@L370-L416 | packet relation requires: the normalization (*) is the other, and it fixes `C = 1`

NODE: hutchcroft.i.1.3.disp.I.1.2
KIND: display
TITLE: Display (I.1.2)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E2@L374-L381
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.3.disp.I.1.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display); it is asserted of the kernel class of `hutchcroft.i.1.3`.
SOURCE_QUANTIFIERS: all `x ≠ y ∈ Z^d`.
SOURCE_CONCLUSION: `J(x,y) = 1(x≠y) J(‖x−y‖) = 1(x≠y) ∫_{‖x−y‖}^∞ |J'(s)| ds`.
CONSTANT_SCOPE: none.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). Carries the content `J(∞) = 0`; see the `SOURCE_CORRECTION` on `hutchcroft.i.1.3`. Its right-hand side is what makes `Σ_y J(0,y) < ∞` and `J(0,v) > 0` available downstream. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.3.disp.star
KIND: display
TITLE: Display (*): unit-ball normalization and the two asymptotic normalizations
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Ex3@L400-L407
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.3.disp.star
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display/WLOG normalization of `hutchcroft.i.1.3`).
SOURCE_QUANTIFIERS: `r → ∞`.
SOURCE_CONCLUSION: `|J'(r)| ∼ r^{−d−α−1}` and `|B_r| := |{x ∈ Z^d : ‖x‖ ≤ r}| ∼ r^d`.
CONSTANT_SCOPE: the `‖·‖`-unit ball has Lebesgue measure 1; `C = 1`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_CORRECTION (replaces v3's `SOURCE_GAP`). v3 recorded the second half `|B_r| ∼ r^d` as a gap "derived in Lemma I.4.6, not an assumption". In the printed text (*) is the *definition* of `|B_r|` together with its asymptotic, asserted under the WLOG `|unit ball| = 1`; it is lattice-point counting, and the WLOG is part of the kernel class. No record in this file uses `|B_r| ∼ r^d` as an independent premise: the normalization has nonlocal normalization-dependence and is not consumed by hutchcroft.i.1.5; the consumers are hutchcroft.i.1.3 and hutchcroft.i.1.2.disp.I.1.3, and `hutchcroft.i.1.2.betac.pos`/`.fin` use only `J`, not `|B_r|`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CORRECTION: consumers are hutchcroft.i.1.3 and hutchcroft.i.1.2.disp.I.1.3; hutchcroft.i.1.5 does not consume the normalization in this candidate.

NODE: hutchcroft.i.1.5
KIND: definition
TITLE: Definition I.1.5 (The cut-off kernel)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a kernel `J` as in `hutchcroft.i.1.3`; a parameter `r > 0`.
SOURCE_QUANTIFIERS: all `x, y ∈ Z^d`; `r > 0`; `β ≥ 0`.
SOURCE_CONCLUSION: `J_r(x,y) = 1(x≠y, ‖x−y‖ ≤ r) ∫_{‖x−y‖}^r |J'(s)| ds`; `P_{β,r}`, `E_{β,r}` are the laws with kernel `J_r` at parameter `β`; `β_c` always denotes the critical parameter of the original `J`, so `P_{β_c,r}` is subcritical at `β_c` for `r < ∞`.
CONSTANT_SCOPE: `β_c` is the *uncut* critical point, never the critical point of `J_r`; `r` is finite throughout.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.3,hutchcroft.i.1.2.betac,hutchcroft.i.1.5.disp.Jr
ROUTES: -
ROUTE_FOR: -
NOTE: The definition's parenthetical ("for every `r<∞` there is `ε = ε(r)>0` with `J_r ≤ (1−ε)J`, so `P_{β_c,r}` is dominated by the subcritical `P_{(1−ε)β_c}`") is a substantive proof remark, not part of the definition; it is recorded as `hutchcroft.i.1.5.step.subcritical` so that the finiteness of the cut-off moments used by both roots has an owner. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: the kernel class whose radial profile `∫∣J'∣` the cut-off truncates
EDGE: hutchcroft.i.1.2.betac | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: `β_c` is attached to the original kernel and kept fixed under the cut-off
EDGE: hutchcroft.i.1.5.disp.Jr | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: the displayed formula for `J_r`

NODE: hutchcroft.i.1.5.disp.Jr
KIND: display
TITLE: The cut-off kernel `J_r` (unnumbered display inside Definition I.1.5)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Ex5@L439-L445
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.5.disp.Jr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display).
SOURCE_QUANTIFIERS: all `x ≠ y`; `r > 0`.
SOURCE_CONCLUSION: `J_r(x,y) = 1(x≠y, ‖x−y‖ ≤ r) ∫_{‖x−y‖}^r |J'(s)| ds`.
CONSTANT_SCOPE: none.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). Note `J_r ↑ J` pointwise as `r ↑ ∞` (`J_r(x,y) = J(x,y) − 1(‖x−y‖>r)J(‖x−y‖)`), which is the monotone coupling behind the cut-off analysis; recorded here because the identity is not printed in this element. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.5.step.subcritical
KIND: step
TITLE: J_r <= (1-epsilon(r))J and cutoff subcriticality (moment finiteness is a separate obligation)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448
PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448
CONTRACT_ID: hutchcroft.i.1.5.step.subcritical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `hutchcroft.i.1.5`; `r < ∞`.
SOURCE_QUANTIFIERS: for each `r < ∞` there is `ε = ε(r) > 0`; all `β ≥ 0`.
SOURCE_CONCLUSION: `J_r(x,y) ≤ (1−ε(r))J(x,y)` for all distinct x,y; hence P_{β_c,r} is stochastically dominated by the subcritical P_{(1−ε(r))β_c}. The printed statement does not itself establish finiteness of every moment.
CONSTANT_SCOPE: `ε(r)` may depend on `r` and on the kernel, not on `x, y, p`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.Orchestration.SourceModelData.exists_epsilon_domination_attained
LEAN_NOTE: Strict arbitrary-normalized-norm domination. An attained positive lattice minimum and K_pos from derivative bounds give ε(r)=min(1/2)(K r/(2K t₀)) in (0,1) for all r>0. The per-edge and reduced-law comparisons are also proved; cutLaw_infiniteClusterProb_eq_zero retains 0<β_c. No higher-moment finiteness is claimed.
DEPS: hutchcroft.i.1.5,hutchcroft.i.1.3,hutchcroft.i.1.2.betac
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448 The earlier J(0+) justification remains WITHDRAWN because it diverges for the normalized power law. VERIFIED STRICT DOMINATION: `MomentMonotonicity.StrictCutoffEpsilon` constructs a positive attained lattice minimum t₀ using finite normalized balls, proves K r>0 from source error/derivative bounds, and sets ε(r)=min(1/2)(K r/(2K t₀)). This lies in (0,1), and gives cutKernel r e≤(1−ε(r))kernel e for every pair, including loops and any admissible norm. `cutLaw_le_reduced` supplies the uncut-law stochastic comparison; `cutLaw_infiniteClusterProb_eq_zero` supplies no infinite cluster when 0<β_c. All-moment finiteness is NOT asserted by this domination; it is the additional open obligation `hutchcroft.i.1.5.step.cutoffmoments`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SCOPE CORRECTION: finite all-moment finiteness is removed from the printed conclusion and exposed at hutchcroft.i.1.5.step.cutoffmoments. It needs a subcritical first-moment estimate plus e.g. the tree-graph moment inequality, not merely a.s. finiteness of the cluster.
EDGE: hutchcroft.i.1.5 | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: the parenthetical is printed there; it is the site that asserts the domination
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: StrictCutoffEpsilon proves strict domination at SourceModelData; its attained-minimum and K-positive premises are proved, not assumed
EDGE: hutchcroft.i.1.2.betac | .scratch/source/paper.html#S1.Thmthm5@L435-L448 | packet relation requires: "subcritical" is with respect to the *uncut* `β_c`, the point of the parenthetical

NODE: hutchcroft.i.1.2.observables
KIND: definition
TITLE: Cluster-volume and spatial observables of the real-space RG analysis (unnumbered, §I.1.2)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p4@L449-L468
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.observables
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition); the cut-off laws `P_{β_c,r}` of `hutchcroft.i.1.5`.
SOURCE_QUANTIFIERS: the analysis is as `r → ∞`; `p ≥ 1` integer where a moment index occurs.
SOURCE_CONCLUSION: the observables are `E_{β_c,r}|K|^p` (cluster volume moments); `M_{β_c,r}`, "the typical size of the largest cluster in the box of radius `r`", defined in detail in §I.2.1; and, say, the spatial moments `E_{β_c,r}Σ_{x∈K}‖x‖_2^p`, `E_{β_c,r}Σ_{x,y∈K}‖x‖_2^p‖y‖_2^q`; `K` always denotes the cluster of the origin.
CONSTANT_SCOPE: `‖·‖_2` is the Euclidean norm on the spatial moments, even when the model norm `‖·‖` is different.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.5,hutchcroft.i.1.2.model
ROUTES: -
ROUTE_FOR: -
NOTE: `M_{β_c,r}` is only *named* here; its definition is the separate display `hutchcroft.i.1.14.disp.Mr` (§I.1.4), which is the carrier of (Hydro). v3 folded that formula into an assumption leaf; this file does not. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.5 | .scratch/source/paper.html#S1.SS2.p4@L449-L468 | packet relation requires: the cut-off law `E_{β_c,r}` under which every observable is taken
EDGE: hutchcroft.i.1.2.model | .scratch/source/paper.html#S1.SS2.p4@L449-L468 | packet relation requires: `K` is the cluster of the origin of that graph

NODE: hutchcroft.i.1.2.disp.I.1.3
KIND: display
TITLE: Display (I.1.3): the asymptotic ODE for the volume moments
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E3@L452-L459
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.disp.I.1.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d_eff > d_c = 6`, or `d_eff = d_c = 6` and `α ≤ 2`
SOURCE_QUANTIFIERS: each integer `p ≥ 1`; `r → ∞`.
SOURCE_CONCLUSION: `(d/dr)E_{β_c,r}|K|^p ∼ β_c r^{−α−1} Σ_{ℓ=0}^{p−1} C(p,ℓ) E_{β_c,r}|K|^{ℓ+1} E_{β_c,r}|K|^{p−ℓ}`.
CONSTANT_SCOPE: leading constant `β_c r^{−α−1}`, determined by the normalization (*); `C(p,ℓ)` is the binomial coefficient.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.3.disp.star
ROUTES: -
ROUTE_FOR: -
NOTE: OUTSIDE both root closures (§3.2). The ODE is *stated* in §I.1.2 but *justified* in §I.4 (cross-slice); the roots' own proof paragraphs (`#S4.SS3.6`, `#S3.SS2.3`) consume Propositions I.4.2/I.4.15/I.4.20 directly, never this display. It is recorded because it is the mathematical engine of the deferred subtree (I.1.9, I.1.17) and of Theorem I.1.15's "analytic consequence" sentence at `#S1.SS4.p6@L939-L941`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.3.disp.star | .scratch/source/paper.html#S1.E3@L452-L459 | packet relation requires: the printed sentence "the leading constants appearing here are determined by our normalization assumptions (*)" makes (*) the source of the constant

NODE: hutchcroft.i.1.2.disp.I.1.4
KIND: display
TITLE: Display (I.1.4): the asymptotic ODE for the second spatial moment
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E4@L471-L478
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.disp.I.1.4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display).
SOURCE_QUANTIFIERS: `r → ∞`.
SOURCE_CONCLUSION: `(d/dr)E_{β_c,r}[Σ_{x∈K}‖x‖_2^2] ∼ (2α/r)E_{β_c,r}[Σ_{x∈K}‖x‖_2^2] + (1/r)((α^2/β_c)∫_B ‖y‖_2^2 dy) r^{2+α}`, with `B = {x ∈ R^d : ‖x‖ ≤ 1}`.
CONSTANT_SCOPE: driving constant `α^2/β_c` times `∫_B‖y‖_2^2 dy`, fixed by (*).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). OUTSIDE both root closures. It is the ODE behind the radius of gyration of Theorem I.1.9, i.e. inside the deferred subtree; the printed text also records that its solution form changes at `α = 2` (power vs. logarithmic), which is why the `α < 2` / `α = 2` / `α > 2` split exists in the I.5 slice. Not used here. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.2.disp.I.1.5
KIND: display
TITLE: Display (I.1.5): the `p = 1` volume-moment ODE
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E5@L492-L499
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.2.disp.I.1.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display).
SOURCE_QUANTIFIERS: `r → ∞`.
SOURCE_CONCLUSION: `(d/dr)E_{β_c,r}|K| ∼ β_c r^{−α−1}(E_{β_c,r}|K|)^2`.
CONSTANT_SCOPE: `β_c` explicit; it is the `p = 1` case of (I.1.3).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.2.disp.I.1.3
ROUTES: -
ROUTE_FOR: -
NOTE: OUTSIDE both root closures. The `p = 1` input reaches the roots through Proposition I.4.2 (cross-slice), not through this display. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.2.disp.I.1.3 | .scratch/source/paper.html#S1.E5@L492-L499 | packet relation requires: (I.1.5) is the `p = 1` specialization of (I.1.3) (the `ℓ = 0` term alone)

NODE: assumption.hd
KIND: assumption
TITLE: (HD) — the three high-dimensional hypotheses, as declared in §I.1.3
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS3.p1@L518-L537
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.hd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (declared assumption). Its content is the disjunction: (1) `d > 3α`; (2) `d > 6` and `P_{β_c}(x ↔ y) ⪯ ‖x−y‖^{−d+2}` for all `x ≠ y`; (3) `d = 6`, `α = 2`, and `P_{β_c}(x ↔ y) ⪯ (log‖x−y‖)^{−1}‖x−y‖^{−d+2}` for all `x ≠ y`.
SOURCE_QUANTIFIERS: the disjunction is over the three alternatives; each is a condition on the whole model `(Z^d, ‖·‖, J, α)`.
SOURCE_CONCLUSION: none (declared assumption; the printed phrase is "under one of the three following hypotheses, which we refer to collectively as (HD)").
CONSTANT_SCOPE: `⪯` up to a positive constant depending on `d`, `α`, `J` (`convention.asymptotic_notation`).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (assumption): `DEPS: none` and no outgoing `EDGE`. It is a **disjunction**: its disjuncts are never conjoined and never edges. A route would be a way for a model to satisfy (HD), not a consequence of it, and `EDGE: route -> assumption.hd` (v3's form) would both reverse the consumer→provider direction and put an outgoing edge on a leaf. Nothing here licenses a header declaration, or a closure, to be read as asserting two alternatives together. SOURCE_CORRECTION (HD-v2, documented campaign ruling; no v1 anchor is edited by this record). Alternative (3) has been PROPOSED for downstream use in the source-interpreting repaired form -- a CANDIDATE only (route.hd.case3, CONTRACT_VERSION 2); the case-3 route of Theorem I.1.6 consumes the printed v1 text and no consumer uses the repair until the coordinator rules -- namely the form `P_{β_c}(x↔y) ⪯ (log(1+‖x−y‖))^{−1}‖x−y‖^{−d+2}` with the constant re-chosen. The repair is class-preserving: on `ρ > 1`, `log(1+ρ)/log ρ → 1` and is ≤ 2 for `ρ ≥ 2`; on the bounded region `ρ ≤ 2` only finitely many lattice displacements occur and the constant absorbs them. It is *strictly weaker* than the printed form on models whose normalized norm puts a non-zero lattice vector at norm ≤ 1, where the printed right-hand side is ≤ 0 while `P_{β_c}(x↔y) > 0`; so the repair adds coverage rather than changing the mathematics. The printed `(log ρ)^{−1}` is quoted, not certified. No `HDplus`, no `d < 6` condition is added to Theorem I.1.15 (which uses `d = 3α` plus (Hydro), not (HD)). COORDINATOR REPAIR: the standing disjunction is now a true leaf. Its three alternatives remain records -- route.hd.case1/2/3, KIND: definition -- but they are not and cannot be this node's ROUTES: `_validate_topology` requires a KIND: assumption node to be a dependency leaf. The case split is recorded at the consuming theorem, whose three routes hutchcroft.i.1.6.hd1/.hd2/.hd3 each consume exactly one alternative. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SCOPE: this is a theorem-local assumption for the (HD) branch, never a global (HD+) assumption. I.1.15 assumes d=3alpha plus (Hydro), not (HD). M1: production STANDING_ASSUMPTIONS may contain assumption.hd alone. CONTRACT-VERSION CONFLICT (recorded, unresolved, no adoption): this node is CONTRACT_VERSION 1 and states the PRINTED alternative 3 as `(log‖x−y‖)^{−1}‖x−y‖^{−d+2}`, while route.hd.case3 carries CONTRACT_VERSION 2 with the repaired `(log(1+‖x−y‖))^{−1}` factor. A v2 disjunct of a v1 assumption is an inconsistent contract pair; either the printed v1 text is kept and the repair recorded as a source defect, or the whole (HD) object is versioned together. Neither v2 adoption nor any edit of the v1 text is proposed: this needs the coordinator's source ruling. The root still consumes this theorem-level (HD) disjunction, but hutchcroft.i.1.6.hd3 now consumes its dedicated printed case hutchcroft.i.1.6.hd3.case, not this whole disjunction. The v2 route.hd.case3 record remains unconsumed.

NODE: route.hd.case1
KIND: definition
TITLE: (HD) alternative 1 — `d > 3α`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.I1.i1.p1@L522-L524
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.hd.case1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d > 3α`.
SOURCE_QUANTIFIERS: none (one alternative of a case split).
SOURCE_CONCLUSION: supplies alternative 1 of (HD).
CONSTANT_SCOPE: none.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE HYPOTHESIS DEFINITION, not an alternative derivation of the theorem. The source assembly site is a consumption site, not a proof of d>3alpha or either two-point bound. HD-v2 (case 3) remains a versioned candidate, not admitted literal source coverage. Leaf (case-hypothesis definition). Non-perturbative alternative: it needs no small parameter and contains the whole effectively-long-range high-dimensional regime; the source at `#S1.SS3.p1.2@L536-L536` says so explicitly. CASE HYPOTHESIS, not a derivation of (HD): consumed only as a source case by the appropriate application of hutchcroft.i.1.6; PROOF_SOURCE and ROUTE_FOR both stay '-'. FIELD/NOTE CONSISTENCY REPAIR: PROOF_SOURCE: - and ROUTE_FOR: - are correct for this record and both stay so. It is KIND: definition because an alternative of a declared disjunction is a definition of a case, not a derivation: `_validate_topology` accepts ROUTE_FOR only on KIND: route, requires a KIND: route node to carry a non-placeholder PROOF_SOURCE, and forbids ROUTES on the KIND: assumption node the disjunction belongs to. The earlier sentences claiming a packet PROOF_SOURCE at the assembly paragraph and a 'route owner' were unsatisfiable and are withdrawn; the assembly paragraph belongs to the root, which reaches the alternatives through its three case routes. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: route.hd.case2
KIND: definition
TITLE: (HD) alternative 2 — `d > 6` with `P_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.I1.i2.p1@L526-L529
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.hd.case2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d > 6`; `P_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}` for all `x ≠ y`.
SOURCE_QUANTIFIERS: all `x ≠ y ∈ Z^d`.
SOURCE_CONCLUSION: supplies alternative 2 of (HD).
CONSTANT_SCOPE: `⪯` up to a `(d, α, J)` constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE HYPOTHESIS DEFINITION, not an alternative derivation of the theorem. The source assembly site is a consumption site, not a proof of d>3alpha or either two-point bound. HD-v2 (case 3) remains a versioned candidate, not admitted literal source coverage. Leaf (case-hypothesis definition). Availability for spread-out models via the lace expansion [35, 36, 67] is an *availability citation*, not a prerequisite of this packet and not a verified leaf: it is not read here and no record depends on it. FIELD/NOTE CONSISTENCY REPAIR: PROOF_SOURCE: - and ROUTE_FOR: - are correct for this record and both stay so. It is KIND: definition because an alternative of a declared disjunction is a definition of a case, not a derivation: `_validate_topology` accepts ROUTE_FOR only on KIND: route, requires a KIND: route node to carry a non-placeholder PROOF_SOURCE, and forbids ROUTES on the KIND: assumption node the disjunction belongs to. The earlier sentences claiming a packet PROOF_SOURCE at the assembly paragraph and a 'route owner' were unsatisfiable and are withdrawn; the assembly paragraph belongs to the root, which reaches the alternatives through its three case routes. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: route.hd.case3
KIND: definition
TITLE: (HD) alternative 3 — `d = 6`, `α = 2`, with the logarithmic two-point bound
STATEMENT_SOURCE: .scratch/source/paper.html#S1.I1.i3.p1@L531-L534
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.hd.case3
CONTRACT_VERSION: 2
SOURCE_HYPOTHESES: `d = 6`; `α = 2`; `P_{β_c}(x↔y) ⪯ (log(1+‖x−y‖))^{−1}‖x−y‖^{−d+2}` for all `x≠y` [SOURCE_CORRECTION: candidate HD-v2 representative; printed form `(log‖x−y‖)^{−1}` is retained in the note but is not a positive bound at every norm value]
SOURCE_QUANTIFIERS: all `x ≠ y ∈ Z^d`.
SOURCE_CONCLUSION: supplies the candidate HD-v2 alternative 3; adoption as a literal replacement for printed (HD) alternative 3 requires independent source review and a versioned successor
CONSTANT_SCOPE: `⪯` up to a `(d, α, J)` constant; the logarithmic factor is exact in the far field and absorbed at short range.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE HYPOTHESIS DEFINITION, not an alternative derivation of the theorem. The source assembly site is a consumption site, not a proof of d>3alpha or either two-point bound. HD-v2 (case 3) remains a versioned candidate, not admitted literal source coverage. SOURCE_CORRECTION, same ruling as `assumption.hd`. The printed `(log ρ)^{−1}` is not a positive bound at `ρ ≤ 1` (it is `≤ 0`, and `0⁻¹` is undefined in ordinary mathematics, `0` in Lean's `ℝ`), so it cannot dominate `P_{β_c}(x↔y) > 0`; the repaired representative `(log(1+ρ))^{−1}` is total and differs by a bounded factor from the printed one on `ρ > 1`. This route is *the reason* the repair matters: it is the only alternative that is unsatisfiable on some admissible models (the paper's own `d = 6` isotropic model is *not* one of them: with unit-ball volume 1 the normalized Euclidean norm puts `‖e_1‖ ≈ 1.315 > 1`). Do not copy a v1 HD frozen state as certified. FIELD/NOTE CONSISTENCY REPAIR: PROOF_SOURCE: - and ROUTE_FOR: - are correct for this record and both stay so. It is KIND: definition because an alternative of a declared disjunction is a definition of a case, not a derivation: `_validate_topology` accepts ROUTE_FOR only on KIND: route, requires a KIND: route node to carry a non-placeholder PROOF_SOURCE, and forbids ROUTES on the KIND: assumption node the disjunction belongs to. The earlier sentences claiming a packet PROOF_SOURCE at the assembly paragraph and a 'route owner' were unsatisfiable and are withdrawn; the assembly paragraph belongs to the root, which reaches the alternatives through its three case routes. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. V2 CONSUMPTION BAR: hutchcroft.i.1.6.hd3 consumes the dedicated printed-v1 case hutchcroft.i.1.6.hd3.case, not assumption.hd or this version-2 record. This interpretation remains unadopted.

NODE: hutchcroft.i.1.14
KIND: definition
TITLE: Definition I.1.14 ((Hydro), the hydrodynamic condition)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm14@L888-L901
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition of a condition on the model); it uses `M_r` of `hutchcroft.i.1.14.disp.Mr` and the cut-off law `P_{β_c,r}`.
SOURCE_QUANTIFIERS: as `r → ∞`.
SOURCE_CONCLUSION: (Hydro) holds iff `M_r = o(r^{(d+α)/2})` as `r → ∞`.
CONSTANT_SCOPE: no constant: the `o(·)` is the whole content.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.14.disp.Mr,hutchcroft.i.1.5
ROUTES: -
ROUTE_FOR: -
NOTE: (Hydro) is a **definition**, not an assumption: the roots *assume* that the condition holds, which is the roots' `ASSUMED` content and their edge to this record. Making the definition an `assumption` leaf (v3's `assumption.hydro`) forced the `M_r` formula into the leaf's `HYPOTHESES` and destroyed its evidence; this file separates them (§0.2 A3). The surrounding text (canonical paper-tex.txt L285-L287) also records `M_r = O(r^{(d+α)/2})` when `0 < α < d` (from [76]) — an *upper* bound, not (Hydro) — and that (Hydro) is a corollary of this paper's results when `d > 3α` (Corollary I.4.14), is proved for `d = 3α` in the third paper, and fails in the effectively-long-range low-dimensional regime. None of those facts is a prerequisite of either root, and none is a record here. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.14.disp.Mr | .scratch/source/paper.html#S1.Thmthm14@L888-L901 | packet relation requires: the quantity `M_r` whose asymptotics is the condition
EDGE: hutchcroft.i.1.5 | .scratch/source/paper.html#S1.Thmthm14@L888-L901 | packet relation requires: `M_r` is defined under the cut-off law `P_{β_c,r}`

NODE: hutchcroft.i.1.14.disp.Mr
KIND: display
TITLE: The `M_r` display preceding Definition I.1.14
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Ex13@L870-L876
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.14.disp.Mr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition, for `r ≥ 1`).
SOURCE_QUANTIFIERS: `r ≥ 1`; the minimum over `n ≥ 0`.
SOURCE_CONCLUSION: `M_r = min{n ≥ 0 : P_{β_c,r}(max_{x∈Z^d}|K_x ∩ B_r| ≥ n) ≤ e^{−1}}`.
CONSTANT_SCOPE: the constant `e^{−1}` is part of the definition; `B_r` is the `‖·‖`-ball of radius `r`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). Read as "the typical size of the largest cluster in the box `B_r` under `P_{β_c,r}`". `K_x` is the cluster of `x`; the maximum is over all of `Z^d`, so `M_r` counts clusters meeting `B_r`. An implementation must not silently replace `max_x |K_x ∩ B_r|` by the largest cluster *contained* in `B_r`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: convention.double_factorial
KIND: definition
TITLE: The combinatorial factor `(2p−3)!!` and its normalization-independence
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS3.p3@L541-L551
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.double_factorial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (notation), for integers `p ≥ 1`.
SOURCE_QUANTIFIERS: each integer `p ≥ 1`.
SOURCE_CONCLUSION: `(2p−3)!!` is "the product of all odd integers between `1` and `2p−3`" — so `(−1)!! = 1` (empty product), `1!! = 1`, `3!! = 3`, `5!! = 15`, and in general `(2p−3)!! = (2p−2)!/(2^{p−1}(p−1)!)`; and it "does not depend on this choice of normalization", unlike the constant `α/β_c`.
CONSTANT_SCOPE: the value is a pure number; it is **not** in the `⪯`/`∼` constant scope.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (definition). Owned in this slice because the roots use it in two places: at `p = 1` it must be `1` (otherwise (I.1.6)/(I.1.16) contradict (I.1.3)'s `p = 1` case and Proposition I.3.2's hypothesis 1), and the `CONSTANT_SCOPE` of both roots separates it from the normalization-dependent `α/β_c` — the printed sentence at this element is the evidence for that separation. M2's `I43Database.md` carries the same id from a different slice: a merge must keep one record, not two. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.6
KIND: theorem
TITLE: Theorem I.1.6 (High-dimensional cluster moments) — EXISTING FROZEN ROOT  metadata copied, not re-declared
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm6@L552-L577
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.6@L3370-L3377
CONTRACT_ID: hutchcroft.i.1.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of the three alternatives of (HD) of §I.1.3 (`.scratch/source/paper.html#S1.SS3.p1@L518-L537`; the printed cross-reference reads `(I.1.3)`)
SOURCE_QUANTIFIERS: one positive constant `A`; for each integer `p ≥ 1` as `r → ∞` (moments) and as `n → ∞` (tail).
SOURCE_CONCLUSION: `E_{β_c,r}|K|^p ∼ (2p−3)!! A^{p−1}(α/β_c) r^{(2p−1)α}` (I.1.6) and `P_{β_c}(|K| ≥ n) ∼ (α/β_c)√(2/(πA)) n^{−1/2}` (I.1.7).
CONSTANT_SCOPE: one positive constant `A` shared by (I.1.6) and (I.1.7); `α/β_c` is normalization-dependent through (*); `(2p−3)!!` is not; the `∼` constants are absolute (1).
FROZEN_FILE: PercLib/CriticalLRP/Orchestration/Frozen/HighDimensionalMoments.lean
FROZEN_DECL: PercLib.CriticalLRP.Orchestration.theorem_I_1_6
FROZEN_ANCHOR_ID: theorem_I_1_6_v1
FROZEN_ABI_SHA256: 1de8ef21dfc1913f0b19b9e87efeacaec3341c1e048943bbe6d868bdf7a14e59
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: assumption.hd,convention.asymptotic_notation,convention.double_factorial,hutchcroft.i.1.2.betac,hutchcroft.i.1.2.betac.fin,hutchcroft.i.1.2.betac.pos,hutchcroft.i.1.2.observables,hutchcroft.i.1.3,hutchcroft.i.1.5,hutchcroft.i.1.5.step.subcritical,hutchcroft.i.1.step.chi2.hd,hutchcroft.i.1.step.constants.hd,hutchcroft.i.1.step.integral.chi2,hutchcroft.i.1.5.step.cutoffmoments,hutchcroft.i.3.2
ROUTES: hutchcroft.i.1.6.hd1,hutchcroft.i.1.6.hd2,hutchcroft.i.1.6.hd3
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.6@L3370-L3377 REFERENCE-TARGET CORRECTION (read off the primary HTML, not inferred): the printed parenthetical in the theorem statement, paper.html L555, is a hyperlink to `#S1.SS3`; it resolves to the SUBSECTION §I.1.3 "Statement of high-dimensional results" (its h3 is at L516), where the itemised (HD) list is printed at L518-L537. The proof paragraph uses the same target: paper.html L3373 links "(I.1.3)" to `#S1.SS3`. So this is not a printed slip, it is a subsection reference, and it is not a reference to display (I.1.3) (`S1.E3@L452`, the volume-moment ODE). No consumer may use display (I.1.3) as a hypothesis. FROZEN METADATA, copied and not re-declared: active manifest `.scratch/critical-lrp-orchestration/docs/orchestration/FROZEN_ANCHOR_MANIFEST.json`, sha256 `bb855df26fab249019a04a395d3e613446796ce0d4d6a648a58e969359011c36`, entry `id = theorem_I_1_6_v1`, `contract.id = hutchcroft.i.1.6`, `contract.version = 1`, `state = DRAFT_SORRY`, `abi_sha256 = 1de8ef21dfc1913f0b19b9e87efeacaec3341c1e048943bbe6d868bdf7a14e59`, `path`/`export` as in `FROZEN_FILE`/`FROZEN_DECL`. This record does not add, split, re-status, re-hash or promote the root, and copies no `prefix_sha256`/`suffix_sha256` (they are not `FROZEN_*` fields). CROSS_SLICE (open, §3.3): the proof paragraph consumes Propositions I.4.2, I.4.15, I.4.20 and Lemma I.4.3 (`#S4.SS3.6@L3370-L3377`), and the tail route consumes Proposition I.3.2. None is a record of this file; their exact obligations are in §1. The root's in-packet closure is therefore *necessary but not sufficient* for the theorem, and no root-closure claim is made. CASE-SPLIT GEOMETRY (printed proof at L3373): Propositions I.4.2, I.4.15 and I.4.20 'apply in cases 2 and 3 of (I.1.3) by Lemma I.4.3'. The root's proof is therefore a case split on (HD), recorded as exactly three ROUTES of this root -- hutchcroft.i.1.6.hd1, .hd2, .hd3 -- one per printed alternative. Each route consumes exactly one case-hypothesis record (hd1: route.hd.case1; hd2: route.hd.case2; hd3: hutchcroft.i.1.6.hd3.case, a KIND: definition of printed alternative 3) and the case DERIVATIONS of the propositions (i.4.2.c1..c5, i.4.15.c1/.c3, i.4.20.c1/.c3), not the packaged propositions: a proposition-level edge would re-import all three alternatives into every branch, which is the scoping defect this shape removes. The packaged propositions remain recorded and are consumed elsewhere (hutchcroft.i.1.15, hutchcroft.i.4.14). (I.1.7) still comes from Proposition I.3.2, which stays a DEPS edge. Open I.3.2/I.4.2/I.4.3/I.4.15/I.4.20 obligations remain open and are not promoted; the (HD)2/3 routes still need the triangle bridge recorded at hutchcroft.i.4.2.ap-hd23. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CONCLUSION-INPUT REPAIR: the root no longer depends on its own two conclusion displays as proof inputs. The moment display remains available to the genuine moment-asymptotic computations through chi2 and constants; the tail display becomes an unconsumed exported conclusion record, not a discharged proof. The case routes must still be proved before any display is asserted.
EDGE: assumption.hd | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: the theorem is asserted under one of the three alternatives; the disjuncts are the three KIND: definition case records consumed one each by this root's three case routes hutchcroft.i.1.6.hd1/.hd2/.hd3; an assumption node owns no routes and a leaf is never a consumer
EDGE: convention.asymptotic_notation | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: the `∼` in (I.1.6) and (I.1.7)
EDGE: convention.double_factorial | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: `(2p−3)!!` at `p = 1` is `1`, and it is the factor that is *not* normalization-dependent
EDGE: hutchcroft.i.1.2.betac | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: `β_c` occurs both as the subcritical cut-off parameter and in the constant `α/β_c`
EDGE: hutchcroft.i.1.2.betac.fin | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: `β_c < ∞`, so `P_{β_c}` is a probability measure and `β_c` is a finite parameter
EDGE: hutchcroft.i.1.2.betac.pos | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: `β_c > 0`, so that `α/β_c ∈ (0,∞)` in both displays
EDGE: hutchcroft.i.1.2.observables | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: `E_{β_c,r}∣K∣^p` and `P_{β_c}(∣K∣ ≥ n)` are the observables defined there, with `K` the cluster of the origin
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: the kernel class and the standing normalization (*) under which the constants of (I.1.6)/(I.1.7) are computed
EDGE: hutchcroft.i.1.5 | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | packet relation requires: the cut-off laws `P_{β_c,r}` carrying the left side of (I.1.6)
EDGE: hutchcroft.i.1.5.step.subcritical | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | the printed cutoff/subcritical domination only; all-moment finiteness is separately exposed as the open `hutchcroft.i.1.5.step.cutoffmoments` obligation
EDGE: hutchcroft.i.1.step.chi2.hd | .scratch/source/paper.html#S4.SS3.6@L3370-L3377 | packet relation requires: the proof's route to (I.1.7): Proposition I.3.2 is applied to the chi-squared limit of the size-biased laws
EDGE: hutchcroft.i.1.step.constants.hd | .scratch/source/paper.html#S4.SS3.6@L3370-L3377 | packet relation requires: the proof's constant computation: Proposition I.3.2 at `a = 2` gives `√(2/(πA))`
EDGE: hutchcroft.i.1.step.integral.chi2 | .scratch/source/paper.html#S4.SS3.6@L3370-L3377 | packet relation requires: the `λ → ∞` limit `√2` of the `Q_∞` integral, needed for `A_3`
EDGE: hutchcroft.i.1.5.step.cutoffmoments | .scratch/source/paper.html#S1.Thmthm6@L552-L577 | SOURCE_GAP: the theorem concerns finite cut-off moments; subcriticality alone does not supply this all-moment condition
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S4.SS3.6@L3370-L3377 | CROSS_SLICE root dependency expressly stated at the theorem proof assembly; supplied by the actual candidate provider packet
EDGE: hutchcroft.i.1.6.hd1 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | one of the three (HD) alternatives: the root's printed proof is a case split over them
EDGE: hutchcroft.i.1.6.hd2 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | one of the three (HD) alternatives: the root's printed proof is a case split over them
EDGE: hutchcroft.i.1.6.hd3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | one of the three (HD) alternatives: the root's printed proof is a case split over them

NODE: hutchcroft.i.1.6.disp.I.1.6
KIND: display
TITLE: Display (I.1.6)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E6@L557-L564
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.6.disp.I.1.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display; inherits `hutchcroft.i.1.6`).
SOURCE_QUANTIFIERS: `r → ∞`; each integer `p ≥ 1`.
SOURCE_CONCLUSION: `E_{β_c,r}|K|^p ∼ (2p−3)!! A^{p−1}(α/β_c) r^{(2p−1)α}`.
CONSTANT_SCOPE: as `hutchcroft.i.1.6`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). Its `p = 2` case, divided by its `p = 1` case, is exactly `A r^{2α}` — the identity that `step.chi2` and `step.constants` use; at `p = 1` it is `E_{β_c,r}|K| ∼ (α/β_c)r^α`, which is Proposition I.3.2's hypothesis 1. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.6.disp.I.1.7
KIND: display
TITLE: Display (I.1.7)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E7@L567-L574
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.6.disp.I.1.7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display; inherits `hutchcroft.i.1.6`).
SOURCE_QUANTIFIERS: `n → ∞` (integers).
SOURCE_CONCLUSION: `P_{β_c}(|K| ≥ n) ∼ (α/β_c)√(2/(πA)) n^{−1/2}`.
CONSTANT_SCOPE: as `hutchcroft.i.1.6`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). The tail is under the **uncut** `P_{β_c}`. A consumer must not replace it by `P_{β_c,r}`: the cut-off tail carries an `r` and is Proposition I.3.2's intermediate object. Note also that the conclusion's decay forces `P_{β_c}(|K| = ∞) = 0`; the volume-tail estimate itself implies P_{β_c}(|K|=infinity)=0; no domain generalization via Berger is required or used — which is *not* used as a premise anywhere in this file. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CORRECTION: no Berger assertion is needed: the tail decay itself implies P(|K|=infinity)=0. Alternatives (HD)2/3 do not imply alpha<d/3.

NODE: hutchcroft.i.1.step.chi2.hd
KIND: step
TITLE: The normalized size-biased volume laws converge to `χ²_1`
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.step.chi2.hd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: moment asymptotics (I.1.6) in the d > 3alpha case; Q_r is the law of |K|/Ê_{β_c,r}|K| under the size-biased measure, with Ê_{β_c,r}|K| = E_{β_c,r}|K|²/E_{β_c,r}|K|.
SOURCE_QUANTIFIERS: each integer `p ≥ 1`; `r → ∞`.
SOURCE_CONCLUSION: `∫_0^∞ x^p dQ_r = Ê_{β_c,r}|K|^p/(Ê_{β_c,r}|K|)^p = E_{β_c,r}|K|^{p+1}/((E_{β_c,r}|K|²/E_{β_c,r}|K|)^p E_{β_c,r}|K|) ∼ (2p−1)!!`; `(Q_r)` is tight; every subsequential limit has moments `(2p−1)!!` and hence equals the law of `χ²_1`; so `Q_r ⇒ χ²_1`, which has no atom at `0`.
CONSTANT_SCOPE: the moments are exactly the double factorials `(2p−1)!!`; `A` (`A_r`) cancels between numerator and denominator. No implicit constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review-smwohv6t4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.carleman_moment_uniqueness,hutchcroft.i.1.6.disp.I.1.6
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: d > 3alpha branch only. The moment quotient's tightness/uniform-integrability bridge must be supplied from the shifted moment bounds; it is not stated in the source. The hd branch does not depend on the other root's moment or tail displays. PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 The printed paragraph asserts the conclusion "by dominated convergence" and "by Carleman's criterion" without the two lines that make the first valid. I supply them, marked as mine, not as printed: (i) *tightness*: the same computation at `p = 1` gives `∫x dQ_r ∼ 1!! = 1`, and Markov gives `P_{Q_r}(x ≥ K) ≤ (1+o(1))/K` uniformly in `r`; (ii) *uniform integrability of `x^p`*: the same computation at `p+1` gives `sup_r ∫x^{p+1}dQ_r < ∞`, hence `(x^p)` is uniformly integrable. Without (ii) a subsequential limit could lose mass at `p`, and Carleman would not apply. Both follow from the *printed* moment computation at shifted index, so the paragraph's conclusion stands; the gap is in the exposition, not in the mathematics. Corroboration, not a premise: Remark I.1.7 (`#S1.Thmthm7@L581-L587`) states independently that the size-biased distribution of `|K|`, normalized to mean 1, converges to `χ²_1`. That remark is OUTSIDE both closures and is not a record here. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SOURCE_GAP: Proposition I.3.2 is a cross-slice application, not a proof of that proposition.
EDGE: ext.carleman_moment_uniqueness | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: "hence by Carleman's criterion that `Q_r` converges to a chi-squared": determinacy of the limit from the moment sequence
EDGE: hutchcroft.i.1.6.disp.I.1.6 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: supplies the four moment asymptotics that the quotient expands into (`p`, `p+1`, `2`, and `1`)

NODE: hutchcroft.i.1.step.integral.chi2
KIND: step
TITLE: The `Q_∞ = χ²_1` integral identity and its `√2` limit
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.step.integral.chi2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the limiting measure Q_infty is exactly chi-square with one degree of freedom; this conditional computation is supplied at either branch consumer by the corresponding chi2 step
SOURCE_QUANTIFIERS: `λ > 0`; `λ → ∞`.
SOURCE_CONCLUSION: `∫_0^∞ (1−e^{−λx})/x dQ_∞(x) = (1/√(2π))∫_0^∞ (1−e^{−λx})e^{−x/2}x^{−3/2}dx = √(2λ+1) − 1`; consequently `lim_{λ→∞} λ^{−1/2}∫_0^∞ (1−e^{−λx})/x dQ_∞(x) = √2`.
CONSTANT_SCOPE: the constants `1/√(2π)` (the `χ²_1` density) and `√2` are explicit.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 Independently checked in this run (`I1Checks.md` §4): the closed form `√(2λ+1)−1` matches high-precision quadrature of `(1/√(2π))∫(1−e^{−λx})e^{−x/2}x^{−3/2}dx` at `λ ∈ {0.01, 0.1, 1, 10, 100}` to better than `1e-9` relative, and `λ^{−1/2}(√(2λ+1)−1) → √2`. The identity is the *only* place a numerical constant enters the tail: everything else is the double factorial. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CONDITIONAL INTEGRAL: this computation has no unconditional chi2 dependency and is shared by both root branches without cross-contaminating them. Its Q_infty premise is discharged branch-locally at chi2.hd or chi2.crit.

NODE: hutchcroft.i.1.step.constants.hd
KIND: step
TITLE: Instantiation of Proposition I.3.2 at `a = 2` and the constants of (I.1.7)/(I.1.17)
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.step.constants.hd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the d > 3alpha case only: A_1 = alpha/beta_c and A appears in the moment scaling; Q_r ⇒ χ²_1; the √2 integral limit is available; f(r)=r^{2alpha} and A_2=A in the d>3alpha branch, whose f^{-1}(n)^alpha = A^{-1/2}n^{1/2}
SOURCE_QUANTIFIERS: `n → ∞`; `h ↓ 0`.
SOURCE_CONCLUSION: Proposition I.3.2 at a=2 gives A_3=(alpha/beta_c)A^{-1/2}sqrt(2) and A_4=(alpha/beta_c)sqrt(2/(pi*A)); multiplying f^{-1}(n)^alpha/n by this factor gives exactly (I.1.7).
CONSTANT_SCOPE: `Γ(1/2) = √π`; `A_3 = (α/β_c)A^{−1/2}√2` resp. `(α/β_c)√2`; `A_4 = A_3/√π`. No other constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review-smwohv6t4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.6.disp.I.1.6,hutchcroft.i.1.step.chi2.hd,hutchcroft.i.1.step.integral.chi2,hutchcroft.i.3.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 CROSS_SLICE (open, §3.3): Proposition I.3.2 (`hutchcroft.i.3.2`) is not a record of this file. The four hypotheses it would have to supply, and the instantiation above, are stated so the I.3 owner can attach a verdict without re-deriving them. **This file does not assert Proposition I.3.2.** Two facts about that slice, reported by its owner (board `smwobyis9` direction d4, findings f1-f2) and consistent with this use site: (i) the printed `a > 0` is not enough — `a ≥ 1` is *derived* from hypothesis (1) via `Ê_r|K| ≥ E|K|` (so it is a step, not a binder); here `a = 2` satisfies it with room to spare. (ii) the `A_3` limit is **not** implied by hypotheses (1)-(4) in general (for `a = 3` and `Q_∞ = χ²_1` the expression tends to `0`, so the printed `∼` degenerates); its well-definedness is a separate obligation of the I.3 slice. This file asserts the limit only at its own instantiation (`a = 2`, `Q_∞ = χ²_1`), where the printed computation gives exactly `√2` (`step.integral`), and it does not generalize that to other `a`. A merge must keep `step.constants` attached to `hutchcroft.i.3.2` as an *application*, not as a proof of the proposition. Constant arithmetic, checked symbolically in this run (`I1Checks.md` §4): with `a = 2`, `λ^{−(a−1)/a} = λ^{−1/2}`; `A_3 = (α/β_c)A^{−1/2}·√2`; `A_4 = A_3/Γ(1/2) = (α/β_c)√2/(A^{1/2}√π) = (α/β_c)√(2/(πA))`; multiplying by `f^{-1}(n)^α/n = n^{1/2}/n = n^{−1/2}` gives (I.1.7) exactly. In the `d = 3α` case `A_3 = (α/β_c)√2`, `A_4 = (α/β_c)√(2/π)`, and `f^{-1}(n)^α/n = (A*_n)^{−1/2}n^{1/2}/n`, giving (I.1.17) exactly. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. TOPOLOGY REPAIR: d > 3alpha branch only. The tail display (I.1.7 if hd, I.1.17 if crit) is this computation's conclusion, not its prerequisite. SOURCE_GAP: Proposition I.3.2 is a cross-slice application, not a proof of that proposition.
EDGE: hutchcroft.i.1.6.disp.I.1.6 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: supplies `A_1` and `f` in the `d > 3α` case (`p = 1` and `p = 2` of (I.1.6))
EDGE: hutchcroft.i.1.step.chi2.hd | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: Proposition I.3.2's hypothesis 3 and 4 (`Q_r ⇒ Q_∞` and no atom at `0`)
EDGE: hutchcroft.i.1.step.integral.chi2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: the `λ → ∞` limit that is the factor `2` inside `√2` in `A_3`
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | CROSS_SLICE: the constants instantiate Proposition I.3.2 at a=2; this is an application, not a proof of the proposition

NODE: ext.carleman_moment_uniqueness
KIND: external
TITLE: Carleman's criterion: a moment sequence with `Σ_k m_{2k}^{−1/(2k)} = ∞` determines its measure
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: -
CONTRACT_ID: ext.carleman_moment_uniqueness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a probability measure `μ` on `[0,∞)` with finite moments `m_p = ∫x^p dμ`, `p ≥ 0`.
SOURCE_QUANTIFIERS: all `p ≥ 0`; the sum over `k ≥ 1`.
SOURCE_CONCLUSION: if `Σ_{k≥1} m_{2k}^{−1/(2k)} = ∞` then `μ` is the unique measure on `[0,∞)` with that moment sequence (the Hamburger/Stieltjes moment problem is determinate).
CONSTANT_SCOPE: none.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (external). Its *only* use is in `step.chi2`, and its hypothesis is checked arithmetically in this run (`I1Checks.md` §4): with `m_{2k} = (4k−1)!!`, `((4k−1)!!)^{1/(4k)} ≍ k^{1/2}` (for `m_{2k}=(4k-1)!!`, Stirling gives `m_{2k} ≈ sqrt(2)(4k/e)^(2k)`), so the terms are `≍ k^{−1/2}` and the series diverges — Carleman applies to `χ²_1`. Do not use this leaf for a measure whose moments are only known up to constants: the criterion is about *exact* moments, which is why `step.chi2` first cancels `A` exactly. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.15
KIND: theorem
TITLE: Theorem I.1.15 (Cluster volumes in the critical dimension) — EXISTING FROZEN ROOT  metadata copied, not re-declared
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm15@L914-L938
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.15
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d = 3α`; the hydrodynamic condition (Hydro) of Definition I.1.14
SOURCE_QUANTIFIERS: there exist bounded slowly varying functions `A_r`, `A*_n` with `r ↦ A_r r^{2α}` and `n ↦ (A*_n)^{−1/2α}n^{1/2α}` mutually inverse; then for each integer `p ≥ 1` as `r → ∞`, and as `n → ∞`.
SOURCE_CONCLUSION: `E_{β_c,r}|K|^p ∼ (2p−3)!! A_r^{p−1}(α/β_c) r^{(2p−1)α}` (I.1.16) and `P_{β_c}(|K| ≥ n) ∼ (α/β_c)√(2/(πA*_n)) n^{−1/2}` (I.1.17).
CONSTANT_SCOPE: the pair `(A_r, A*_n)` is one joint object linked by mutual inversion of the scale maps; `α/β_c` is normalization-dependent through (*); `(2p−3)!!` is not; the `∼` constants are absolute (1).
FROZEN_FILE: PercLib/CriticalLRP/Orchestration/Frozen/CriticalDimensionMoments.lean
FROZEN_DECL: PercLib.CriticalLRP.Orchestration.theorem_I_1_15
FROZEN_ANCHOR_ID: theorem_I_1_15_v1
FROZEN_ABI_SHA256: 567d1220587aa715d9046f1f89f7ef6cf404d04da5e175637b7cb165b774e186
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: convention.asymptotic_notation,convention.double_factorial,hutchcroft.i.1.14,hutchcroft.i.1.15.step.objects,hutchcroft.i.1.2.betac,hutchcroft.i.1.2.betac.fin,hutchcroft.i.1.2.betac.pos,hutchcroft.i.1.2.observables,hutchcroft.i.1.3,hutchcroft.i.1.5,hutchcroft.i.1.5.step.subcritical,hutchcroft.i.1.step.chi2.crit,hutchcroft.i.1.step.constants.crit,hutchcroft.i.1.step.integral.chi2,hutchcroft.i.1.5.step.cutoffmoments,hutchcroft.i.3.2,hutchcroft.i.4.2.c2,hutchcroft.i.4.15.c2,hutchcroft.i.4.20.c2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 No alternative appears in `ROUTES`: this root's hypothesis is `d = 3α` **and** (Hydro), a conjunction, not the (HD) disjunction. In particular (HD) is *not* a hypothesis of this root, and no `HD+`/`d < 6` condition may be added to it (the campaign has ruled on this). `PROOF_SOURCE` is the §I.3 paragraph "Proof of (I.1.7) and (I.1.17) given (I.1.6) and (I.1.16)". It proves (I.1.17) *from* (I.1.16); (I.1.16) itself is justified in §I.4 ("the two estimates (I.1.16) and (I.1.3) are justified in parallel over the course of Section I.4", `#S1.SS4.p6@L939-L941`, the in-slice pointer). The pointer sentence is not a proof and gets no record. FROZEN METADATA, copied and not re-declared: active manifest sha256 `bb855df26fab249019a04a395d3e613446796ce0d4d6a648a58e969359011c36`, entry `id = theorem_I_1_15_v1`, `contract.id = hutchcroft.i.1.15`, `contract.version = 1`, `state = DRAFT_SORRY`, `abi_sha256 = 567d1220587aa715d9046f1f89f7ef6cf404d04da5e175637b7cb165b774e186`. No add, split, re-status, re-hash or promotion. CROSS_SLICE (open, §3.3): (I.1.16) is derived from Propositions I.4.2, I.4.15, I.4.20 (`hutchcroft.i.4.2`, `.4.15`, `.4.20` — none a record here), and (I.1.17) from Proposition I.3.2 (`hutchcroft.i.3.2` — not a record here). The in-packet closure is necessary but not sufficient. SOURCE_QUESTION: the printed Remark I.1.16 gives the `d = 3α < 6` confluence as `A*_n ∼ (2α)^{1/2}A(log n)^{1/2}`; mutual inversion with `A_r ∼ A(log r)^{-1/2}` forces the exponent `−1/2`, not `+1/2` (checked in `hutchcroft.i.1.15.step.objects` and `hutchcroft.i.1.16`). The theorem's own statement is unaffected. Recorded, not silently changed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. CASE-SCOPING REPAIR: all dependencies in this critical application now name the conditional Hydro case derivations, instead of the umbrella Propositions I.4.2, I.4.15, I.4.20 and their other alternatives. CONCLUSION-INPUT REPAIR: neither own conclusion display is a direct root premise. The moment display is retained by chi2 and constants for moment algebra; the tail display is intentionally outside this closure, not silently promoted or discarded. Displays label targets rather than discharged proofs. CRITICAL-PERCOLATION LINKING: I.3.2 now consumes the independently recorded beta_c.fin and beta_c.pos obligations, not the withdrawn finite-range-line reconstruction.
EDGE: convention.asymptotic_notation | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: the `∼` in (I.1.16) and (I.1.17)
EDGE: convention.double_factorial | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: `(2p−3)!!` at `p = 1`, and its normalization-independence
EDGE: hutchcroft.i.1.14 | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: the assumed (Hydro) condition
EDGE: hutchcroft.i.1.15.step.objects | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: discharges the existential "there exist `A_r`, `A*_n` with the mutual-inverse property" by construction
EDGE: hutchcroft.i.1.2.betac | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: `β_c` in the constant `α/β_c` and as the parameter of the cut-off measures
EDGE: hutchcroft.i.1.2.betac.fin | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: `β_c < ∞`
EDGE: hutchcroft.i.1.2.betac.pos | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: `β_c > 0`, so that `α/β_c ∈ (0,∞)`
EDGE: hutchcroft.i.1.2.observables | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: the observables `E_{β_c,r}∣K∣^p`, `P_{β_c}(∣K∣ ≥ n)`
EDGE: hutchcroft.i.1.3 | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: the kernel class and the normalization (*) behind `α/β_c` and `r^{2α}`
EDGE: hutchcroft.i.1.5 | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | packet relation requires: the cut-off laws `P_{β_c,r}`
EDGE: hutchcroft.i.1.5.step.subcritical | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | the printed cutoff/subcritical domination only; all-moment finiteness is separately exposed as the open `hutchcroft.i.1.5.step.cutoffmoments` obligation
EDGE: hutchcroft.i.1.step.chi2.crit | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: the `χ²_1` limit used in the proof of (I.1.17)
EDGE: hutchcroft.i.1.step.constants.crit | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: the `a = 2` instantiation giving `√(2/(πA*_n))`
EDGE: hutchcroft.i.1.step.integral.chi2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | packet relation requires: the `√2` limit entering `A_3`
EDGE: hutchcroft.i.1.5.step.cutoffmoments | .scratch/source/paper.html#S1.Thmthm15@L914-L938 | SOURCE_GAP: the theorem concerns finite cut-off moments; subcriticality alone does not supply this all-moment condition
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | CROSS_SLICE root dependency expressly stated at the theorem proof assembly; supplied by the actual candidate provider packet
EDGE: hutchcroft.i.4.2.c2 | .scratch/source/paper.html#S1.SS4.p6@L939-L941 | Hydro first-moment asymptotic at d=3α plus Hydro, not the d>3α or triangle alternatives
EDGE: hutchcroft.i.4.15.c2 | .scratch/source/paper.html#S1.SS4.p6@L939-L941 | Hydro second-moment regular variation, without pretending the sharp-constant branch applies
EDGE: hutchcroft.i.4.20.c2 | .scratch/source/paper.html#S1.SS4.p6@L939-L941 | Hydro higher-moment asymptotics, not the triangle alternative

NODE: hutchcroft.i.1.15.disp.I.1.16
KIND: display
TITLE: Display (I.1.16)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E16@L918-L925
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.15.disp.I.1.16
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display; inherits `hutchcroft.i.1.15`).
SOURCE_QUANTIFIERS: `r → ∞`; each integer `p ≥ 1`.
SOURCE_CONCLUSION: `E_{β_c,r}|K|^p ∼ (2p−3)!! A_r^{p−1}(α/β_c) r^{(2p−1)α}`.
CONSTANT_SCOPE: as `hutchcroft.i.1.15`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). `p = 2` divided by `p = 1` gives `A_r r^{2α}`, the object that `hutchcroft.i.1.15.step.objects` constructs; `p = 1` gives Proposition I.3.2's hypothesis 1 with `A_1 = α/β_c`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.15.disp.I.1.17
KIND: display
TITLE: Display (I.1.17)
STATEMENT_SOURCE: .scratch/source/paper.html#S1.E17@L928-L935
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.15.disp.I.1.17
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (display; inherits `hutchcroft.i.1.15`).
SOURCE_QUANTIFIERS: `n → ∞` (integers).
SOURCE_CONCLUSION: `P_{β_c}(|K| ≥ n) ∼ (α/β_c)√(2/(πA*_n)) n^{−1/2}`.
CONSTANT_SCOPE: as `hutchcroft.i.1.15`; the `n`-dependence sits in the slowly varying `A*_n`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Leaf (display). `A*_n` is the slowly varying factor of the inverse scale `(A*_n)^{−1/2α}n^{1/2α}`; a consumer must not replace it by a constant (that is the `d = 3α ≥ 6` case of Remark I.1.16, not this one). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.15.step.objects
KIND: step
TITLE: Construction of the pair `(A_r, A*_n)`: definition of `A_r`, its boundedness and slow variation, and the mutual-inverse `A*`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm15@L914-L938
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5@L1917-L1978
CONTRACT_ID: hutchcroft.i.1.15.step.objects
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: printed critical-dimension moment scaling and the existence of the scale transformation required for its inversion; the positivity, boundedness and slow variation of A_r are open cross-slice obligations
SOURCE_QUANTIFIERS: `r → ∞`; `n → ∞`.
SOURCE_CONCLUSION: printed part only: Ê_{β_c,r}|K| ∼ A_r r^{2α}, and the inverse of r↦A_r r^{2α} is written s↦Ã_s^{−1/(2α)}s^{1/(2α)} with Ã_s slowly varying; A*_n:=Ã_n is the notation identification used by this candidate
CONSTANT_SCOPE: mutual inversion is exact by construction; the constant `(2α)^{1/2}` comes from `log σ^{-1}(n) = (1/(2α))log n + o(log n)`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c2,hutchcroft.i.4.15.c2,hutchcroft.i.1.15.step.objects.regularization
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5@L1917-L1978 The paper never writes the definition of `A_r`; it uses `Ê_r|K| ∼ A_r r^{2α}` at the cited site. So the theorem's existential is discharged by *construction plus the moment asymptotics*, not by a missing hypothesis and not by a new definition record. The smooth monotone inverse is the standard regular-variation regularization (a slowly varying function is asymptotically equivalent to a smooth one); it is a proof duty recorded here, not a source object. The exponent check is mine and is arithmetic: put `A_r ∼ A(log r)^{β}`, `A*_n ∼ cA(log n)^{β'}`. Then `σ^{-1}(σ(r)) = c^{-1/(2α)}(log r)^{(β−β')/(2α)}r`, so mutual inversion forces `β' = β`, and normalizing the leading coefficient forces `c = (2α)^{1/2}` when `β = −1/2`. Hence `A*_n ∼ (2α)^{1/2}A(log n)^{-1/2}`. This is the *opposite sign* from the printed Remark I.1.16 clause (ii); see `hutchcroft.i.1.16`. CROSS_SLICE (open, §3.3): the `p = 1` and `p = 2` asymptotics it consumes are Propositions I.4.2 and I.4.15, which are not records here. Merge note: m2's `I43Database.md` splits the same duties into `hutchcroft.i.1.15.step.normalize`, `.posbdd`, `.inverse`; their statements agree with this one on the exponent, and a merge must adjudicate the split rather than concatenate. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SOURCE_GAP: positivity, boundedness and slow variation of A_r are NOT proved at this paragraph and are not inferred from the theorem's own conclusion display. They need the p=1,2 moment propositions I.4.2/I.4.15. The former transitive Hydro and self-conclusion edges were removed; forward construction obligations normalize/.posbdd/.inverse remain subject to merge adjudication. CASE-SCOPING REPAIR: all dependencies in this critical application now name the conditional Hydro case derivations, instead of the umbrella Propositions I.4.2, I.4.15, I.4.20 and their other alternatives.
EDGE: hutchcroft.i.4.2.c2 | .scratch/source/paper.html#S1.SS4.p6@L939-L941 | Hydro first-moment asymptotic at d=3α plus Hydro, not the d>3α or triangle alternatives
EDGE: hutchcroft.i.4.15.c2 | .scratch/source/paper.html#S1.SS4.p6@L939-L941 | Hydro second-moment regular variation, without pretending the sharp-constant branch applies
EDGE: hutchcroft.i.1.15.step.objects.regularization | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | the joint scale and mutual-inverse construction consumes these explicit, still-open obligations

NODE: hutchcroft.i.1.16
KIND: application
TITLE: Remark I.1.16 — the confluence of `A_r` and `A*_n` in the two regimes
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm16@L942-L949
PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm16@L942-L949
CONTRACT_ID: hutchcroft.i.1.16
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: for the first sentence: `d = 3α ≥ 6` **and** a two-point function estimate as verified for spread-out models via the lace expansion [35, 36], together with Theorem I.1.6; for the second: the objects of Theorem I.1.15.
SOURCE_QUANTIFIERS: `r → ∞`, `n → ∞`.
SOURCE_CONCLUSION: (i) when `d = 3α ≥ 6` and the two-point estimate holds, `A_r` and `A*_n` converge to positive constants; (ii) when `d = 3α < 6`, `A_r ∼ A(log r)^{-1/2}` and `A*_n ∼ (2α)^{1/2}A(log n)^{1/2}` for some constant `A > 0`.
CONSTANT_SCOPE: one constant `A > 0` shared by the two displays; the factor `(2α)^{1/2}` is explicit.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.15,hutchcroft.i.1.6
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_CORRECTION (checked in this run, arithmetic only). Clause (ii) cannot hold literally together with Theorem I.1.15's mutual-inverse clause: as computed in `hutchcroft.i.1.15.step.objects`, `σ^{-1}(σ(r)) = c^{-1/(2α)}(log r)^{(β−β')/(2α)}r` for `A_r ∼ A(log r)^β`, `A*_n ∼ cA(log n)^{β'}`, so mutual inversion forces `β' = β = −1/2`. The printed `A*_n ∼ (2α)^{1/2}A(log n)^{+1/2}` therefore has the wrong sign in the exponent (or the `A_r` display does); the constant `(2α)^{1/2}` is right. The theorem's own statement (existence of a mutually inverse pair) is unaffected, and nothing here changes a root. Recorded, not silently corrected. Clause (ii) is attributed by the source to the **third paper in the series**, not proved here; the `[35, 36]` lace-expansion attribution in clause (i) is an availability citation. Neither is a verified leaf in this packet. OUTSIDE both root closures (§3.2). It is a record because the ownership map (`#S1.Thmthm16`) has content that no other record carries, and because it is the only printed statement of the `A`/`A*` confluence that a consumer of (I.1.16)/(I.1.17) will look for. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.1.6 | .scratch/source/paper.html#S1.Thmthm16@L942-L949 | packet relation requires: clause (i): under `d = 3α ≥ 6` plus the two-point estimate, Theorem I.1.6 applies with `A_r → A` a positive constant
EDGE: hutchcroft.i.1.15 | .scratch/source/paper.html#S1.Thmthm16@L942-L949 | packet relation requires: the `A_r`, `A*_n` of clause (ii) are the theorem's objects, constrained by its mutual-inverse clause

NODE: hutchcroft.i.1.step.chi2.crit
KIND: step
TITLE: The normalized size-biased volume laws converge to `χ²_1`
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.step.chi2.crit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: moment asymptotics (I.1.16) in the d = 3alpha case; Q_r is the law of |K|/Ê_{β_c,r}|K| under the size-biased measure, with Ê_{β_c,r}|K| = E_{β_c,r}|K|²/E_{β_c,r}|K|.
SOURCE_QUANTIFIERS: each integer `p ≥ 1`; `r → ∞`.
SOURCE_CONCLUSION: `∫_0^∞ x^p dQ_r = Ê_{β_c,r}|K|^p/(Ê_{β_c,r}|K|)^p = E_{β_c,r}|K|^{p+1}/((E_{β_c,r}|K|²/E_{β_c,r}|K|)^p E_{β_c,r}|K|) ∼ (2p−1)!!`; `(Q_r)` is tight; every subsequential limit has moments `(2p−1)!!` and hence equals the law of `χ²_1`; so `Q_r ⇒ χ²_1`, which has no atom at `0`.
CONSTANT_SCOPE: the moments are exactly the double factorials `(2p−1)!!`; `A` (`A_r`) cancels between numerator and denominator. No implicit constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review-smwohv6t4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.carleman_moment_uniqueness,hutchcroft.i.1.15.disp.I.1.16
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: d = 3alpha branch only. The moment quotient's tightness/uniform-integrability bridge must be supplied from the shifted moment bounds; it is not stated in the source. The crit branch does not depend on the other root's moment or tail displays. PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 The printed paragraph asserts the conclusion "by dominated convergence" and "by Carleman's criterion" without the two lines that make the first valid. I supply them, marked as mine, not as printed: (i) *tightness*: the same computation at `p = 1` gives `∫x dQ_r ∼ 1!! = 1`, and Markov gives `P_{Q_r}(x ≥ K) ≤ (1+o(1))/K` uniformly in `r`; (ii) *uniform integrability of `x^p`*: the same computation at `p+1` gives `sup_r ∫x^{p+1}dQ_r < ∞`, hence `(x^p)` is uniformly integrable. Without (ii) a subsequential limit could lose mass at `p`, and Carleman would not apply. Both follow from the *printed* moment computation at shifted index, so the paragraph's conclusion stands; the gap is in the exposition, not in the mathematics. Corroboration, not a premise: Remark I.1.7 (`#S1.Thmthm7@L581-L587`) states independently that the size-biased distribution of `|K|`, normalized to mean 1, converges to `χ²_1`. That remark is OUTSIDE both closures and is not a record here. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. SOURCE_GAP: Proposition I.3.2 is a cross-slice application, not a proof of that proposition.
EDGE: ext.carleman_moment_uniqueness | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | branch-local proof input for crit; full source attribution retained in PROOF_SOURCE and NOTE
EDGE: hutchcroft.i.1.15.disp.I.1.16 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | branch-local proof input for crit; full source attribution retained in PROOF_SOURCE and NOTE

NODE: hutchcroft.i.1.step.constants.crit
KIND: step
TITLE: Instantiation of Proposition I.3.2 at `a = 2` and the constants of (I.1.7)/(I.1.17)
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.step.constants.crit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the d = 3alpha case only: A_1 = alpha/beta_c and A_r appears in the moment scaling; Q_r ⇒ χ²_1; the √2 integral limit is available; f(r)=A_r r^{2alpha} and A_2=1 in the critical branch, whose f^{-1}(n)^alpha = (A*_n)^{-1/2}n^{1/2}
SOURCE_QUANTIFIERS: `n → ∞`; `h ↓ 0`.
SOURCE_CONCLUSION: Proposition I.3.2 at a=2 gives A_3=(alpha/beta_c)sqrt(2) and A_4=(alpha/beta_c)sqrt(2/pi); multiplying f^{-1}(n)^alpha/n by it gives exactly (I.1.17).
CONSTANT_SCOPE: `Γ(1/2) = √π`; `A_3 = (α/β_c)A^{−1/2}√2` resp. `(α/β_c)√2`; `A_4 = A_3/√π`. No other constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review-smwohv6t4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.1.15.disp.I.1.16,hutchcroft.i.1.step.chi2.crit,hutchcroft.i.1.step.integral.chi2,hutchcroft.i.3.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979 CROSS_SLICE (open, §3.3): Proposition I.3.2 (`hutchcroft.i.3.2`) is not a record of this file. The four hypotheses it would have to supply, and the instantiation above, are stated so the I.3 owner can attach a verdict without re-deriving them. **This file does not assert Proposition I.3.2.** Two facts about that slice, reported by its owner (board `smwobyis9` direction d4, findings f1-f2) and consistent with this use site: (i) the printed `a > 0` is not enough — `a ≥ 1` is *derived* from hypothesis (1) via `Ê_r|K| ≥ E|K|` (so it is a step, not a binder); here `a = 2` satisfies it with room to spare. (ii) the `A_3` limit is **not** implied by hypotheses (1)-(4) in general (for `a = 3` and `Q_∞ = χ²_1` the expression tends to `0`, so the printed `∼` degenerates); its well-definedness is a separate obligation of the I.3 slice. This file asserts the limit only at its own instantiation (`a = 2`, `Q_∞ = χ²_1`), where the printed computation gives exactly `√2` (`step.integral`), and it does not generalize that to other `a`. A merge must keep `step.constants` attached to `hutchcroft.i.3.2` as an *application*, not as a proof of the proposition. Constant arithmetic, checked symbolically in this run (`I1Checks.md` §4): with `a = 2`, `λ^{−(a−1)/a} = λ^{−1/2}`; `A_3 = (α/β_c)A^{−1/2}·√2`; `A_4 = A_3/Γ(1/2) = (α/β_c)√2/(A^{1/2}√π) = (α/β_c)√(2/(πA))`; multiplying by `f^{-1}(n)^α/n = n^{1/2}/n = n^{−1/2}` gives (I.1.7) exactly. In the `d = 3α` case `A_3 = (α/β_c)√2`, `A_4 = (α/β_c)√(2/π)`, and `f^{-1}(n)^α/n = (A*_n)^{−1/2}n^{1/2}/n`, giving (I.1.17) exactly. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I1Adapter.md; all source claims and references remain unreviewed. TOPOLOGY REPAIR: d = 3alpha branch only. The tail display (I.1.7 if hd, I.1.17 if crit) is this computation's conclusion, not its prerequisite. SOURCE_GAP: Proposition I.3.2 is a cross-slice application, not a proof of that proposition.
EDGE: hutchcroft.i.1.15.disp.I.1.16 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | branch-local proof input for crit; full source attribution retained in PROOF_SOURCE and NOTE
EDGE: hutchcroft.i.1.step.chi2.crit | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | branch-local proof input for crit; full source attribution retained in PROOF_SOURCE and NOTE
EDGE: hutchcroft.i.1.step.integral.chi2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | branch-local proof input for crit; full source attribution retained in PROOF_SOURCE and NOTE
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | CROSS_SLICE: the constants instantiate Proposition I.3.2 at a=2; this is an application, not a proof of the proposition

NODE: hutchcroft.i.1.5.step.cutoffmoments
KIND: step
TITLE: OPEN OBLIGATION: every cut-off cluster-volume moment is finite at each finite r
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm6@L552-L577
PROOF_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448
CONTRACT_ID: hutchcroft.i.1.5.step.cutoffmoments
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: cut-off subcriticality at beta_c,r; a subcritical finite-first-moment estimate and a tree-graph moment bound are required
SOURCE_QUANTIFIERS: every finite r>0 and every integer p>=1
SOURCE_CONCLUSION: E_{β_c,r}|K|^p < infinity for every p>=1 at each finite r>0
CONSTANT_SCOPE: `ε(r)` may depend on `r` and on the kernel, not on `x, y, p`.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review-smwohv6t4
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this obligation is not discharged by subcriticality alone. A valid route is subcritical finite first moment + the tree-graph moment inequality; recording the route does not assign it a provider or prove it. All consumer roots must retain this open obligation. This is a consumption site of the open cut-off moment premise, not Definition I.1.5 mislabelled as a proof. CIRCULAR-CITATION CORRECTION: PROOF_SOURCE was `.scratch/source/paper.html#S1.Thmthm15@L914-L938`, i.e. the *statement of* Theorem I.1.15, the other registered DRAFT_SORRY root. Sourcing a premise of Theorem I.1.6 from the statement of Theorem I.1.15 is circular: both roots consume this same obligation. It is replaced by the only printed input, Definition I.1.5 (subcriticality of P_{βc,r} at finite r), which this record's own NOTE already says does not suffice; the obligation therefore stays OPEN for both roots. No frozen declaration is imported, cited as a proof, or re-statused here.

NODE: hutchcroft.i.2.1
KIND: lemma
TITLE: Two-cluster correlation inequalities
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm1@L1139-L1168
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176
CONTRACT_ID: hutchcroft.i.2.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a weighted graph $G=(V,E,J)$ at any $\beta\geq0$; $x,y\in V$; $F,G$ increasing non-negative functions of the cluster considered as a set. The weighted-graph typing is not restated in I.2: see assumption.weighted_graph.
SOURCE_QUANTIFIERS: Every $\beta\geq0$, every $x,y\in V$ and every pair of increasing non-negative $F,G$; clauses (ii) and (iii) additionally require $\mathbb{E}_\beta F(K_x),\mathbb{E}_\beta G(K_y)<\infty$.
SOURCE_CONCLUSION: (i) $\mathbb{E}_\beta[F(K_x)G(K_y)\mathbb{1}(x\nleftrightarrow y)]\leq\mathbb{E}_\beta F(K_x)\,\mathbb{E}_\beta G(K_y)$; (ii) $\mathbb{E}_\beta[F(K_x)G(K_y)\mathbb{1}(x\nleftrightarrow y)]\geq\mathbb{E}_\beta F(K_x)\mathbb{E}_\beta G(K_y)-\mathbb{E}_\beta[F(K_x)G(K_y)\mathbb{1}(x\leftrightarrow y)]$; (iii) $0\leq\mathbb{E}_\beta[F(K_x)G(K_y)]-\mathbb{E}_\beta F(K_x)\mathbb{E}_\beta G(K_y)\leq\mathbb{E}_\beta[F(K_x)G(K_y)\mathbb{1}(x\leftrightarrow y)]$.
CONSTANT_SCOPE: No constant: every inequality holds with factor 1.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: assumption.weighted_graph,ext.grimmett.fkg.bk,ext.bk.extensions
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176 canonical paper-tex.txt L395-L409. SOURCE DEFECT (label, confirmed): the proof paragraph at canonical L411 is headed "Proof of Lemma I.2.2." but proves Lemma I.2.1 (its three sentences match clauses (i)-(iii)); Lemma I.2.2 (canonical L417) has no proof of its own. Interval of the mislabel: html S2.SS1.2 L1169-L1176. SOURCE GAP (proof-level): the printed proof says only "an immediate consequence of the BK inequality", so it does not say (a) that the factor $\mathbb{1}(x\nleftrightarrow y)$ is DECREASING, which makes the increasing-events BK insufficient and forces Reimer / van den Berg-Fiebig, nor (b) how general increasing $F,G$ are reduced to indicators (distribution-function or monotone-class argument). CONSUMERS recorded elsewhere in this packet: canonical L1029, L1194, L1435, L1475, L2197, L2577. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S2.Thmthm1@L1139-L1168 | packet relation requires: model typing "Bernoulli bond percolation on a weighted graph $G=(V,E,J)$" is the object of the statement, not derived here
EDGE: ext.grimmett.fkg.bk | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: Harris-FKG supplies $\mathbb{E}[FG]\geq\mathbb{E}F\,\mathbb{E}G$ in the derivation of clauses (ii) and (iii)
EDGE: ext.bk.extensions | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: clause (i) applies disjoint occurrence to the decreasing factor $\mathbb{1}(x\nleftrightarrow y)$, so the non-monotone (Reimer) or van den Berg-Fiebig form is the one actually used

NODE: hutchcroft.i.2.1:step-bk
KIND: step
TITLE: BK on disjoint witnesses of the two clusters, then integrate over levels
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176
CONTRACT_ID: hutchcroft.i.2.1:step-bk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Lemma I.2.1, restricted to $x\nleftrightarrow y$; for $s,t\geq0$ the events $\{F(K_x)\geq s\}$ and $\{G(K_y)\geq t\}$ have disjoint witnesses because the two clusters are disjoint on $\{x\nleftrightarrow y\}$.
SOURCE_QUANTIFIERS: Every $s,t\geq0$, every $\beta\geq0$, every $x,y\in V$.
SOURCE_CONCLUSION: $\mathbb{P}_\beta(F(K_x)\geq s,\ G(K_y)\geq t,\ x\nleftrightarrow y)\leq\mathbb{P}_\beta(F(K_x)\geq s)\,\mathbb{P}_\beta(G(K_y)\geq t)$, hence clause (i) by integrating over $s$ and $t$.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.bk.extensions,ext.grimmett.fkg.bk
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176 canonical paper-tex.txt L411. Reconstructed step: the source says only "an immediate consequence of the BK inequality". Two ingredients the source leaves implicit: the witness argument for general increasing $F,G$ (via level sets, giving the sup over $s,t$) and the infinite-volume extension of BK by limiting arguments (footnote 11, html S2.SS1.p3 L1133-L1138). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.bk.extensions | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: disjoint-occurrence inequality applied to the decreasing factor $\mathbb{1}(x\nleftrightarrow y)$ together with its infinite-volume form
EDGE: ext.grimmett.fkg.bk | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: the finite-volume increasing-events form is the base case of the limiting argument

NODE: hutchcroft.i.2.1:step-partition
KIND: step
TITLE: Partition $1=\mathbb{1}(x\leftrightarrow y)+\mathbb{1}(x\nleftrightarrow y)$ and apply FKG
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176
CONTRACT_ID: hutchcroft.i.2.1:step-partition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Lemma I.2.1, with $\mathbb{E}_\beta F(K_x),\mathbb{E}_\beta G(K_y)<\infty$.
SOURCE_QUANTIFIERS: Pointwise in the configuration; every $\beta\geq0$ and $x,y\in V$.
SOURCE_CONCLUSION: $\mathbb{E}[FG]=\mathbb{E}[FG\mathbb{1}(x\leftrightarrow y)]+\mathbb{E}[FG\mathbb{1}(x\nleftrightarrow y)]$, so clause (i) and Harris-FKG give (ii), and the same partition re-applied gives (iii).
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.1:step-bk,ext.grimmett.fkg.bk
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.2@L1169-L1176 canonical paper-tex.txt L413. Reconstructed step; the source asserts it in one clause ("further follows by writing ... and using Harris-FKG"). Uses finiteness of the two one-point expectations to subtract. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.1:step-bk | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: clause (i) enters the computation of $\mathbb{E}[FG\mathbb{1}(x\nleftrightarrow y)]$ from above
EDGE: ext.grimmett.fkg.bk | .scratch/source/paper.html#S2.SS1.2@L1169-L1176 | packet relation requires: Harris-FKG bounds the resulting term $\mathbb{E}[F(K_x)G(K_y)]\geq\mathbb{E}F(K_x)\mathbb{E}G(K_y)$

NODE: hutchcroft.eq.i.2.1
KIND: display
TITLE: (I.2.1) the three-point tree-graph inequality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
CONTRACT_ID: hutchcroft.eq.i.2.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on any weighted graph $G=(V,E,J)$; $x,y,z\in V$; $\beta\geq0$.
SOURCE_QUANTIFIERS: Every $x,y,z\in V$ and every $\beta\geq0$.
SOURCE_CONCLUSION: $\mathbb{P}_\beta(x\leftrightarrow y\leftrightarrow z)\leq\sum_{w\in V}\mathbb{P}_\beta(x\leftrightarrow w)\mathbb{P}_\beta(w\leftrightarrow y)\mathbb{P}_\beta(w\leftrightarrow z)$, the sum over the whole vertex set.
CONSTANT_SCOPE: Constant 1.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.aizenman-newman1984
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 Display (I.2.1) is the html equation table id=S2.E1 at paper.html L1205, inside block #S2.SS1.p6; canonical paper-tex.txt L427. Borrowed from the tree-graph inequalities of Aizenman-Newman [4]; no proof in I.2, and no consumer of the label (I.2.1) anywhere in paper I (text search for "(I.2.1)"). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.aizenman-newman1984 | .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 | packet relation requires: the paragraph attributes the tree-graph inequalities and this first instance to [4] without proof

NODE: hutchcroft.eq.i.2.2
KIND: display
TITLE: (I.2.2) the (k+1)-point tree-graph inequality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
CONTRACT_ID: hutchcroft.eq.i.2.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on any weighted graph; $x_0,\ldots,x_k\in V$; the sum runs over representatives of isomorphism classes of trees with leaves labelled $0,\ldots,k$ and unlabelled non-leaf vertices of degree $3$.
SOURCE_QUANTIFIERS: Every integer $k\geq1$ and every $(k+1)$-tuple of vertices.
SOURCE_CONCLUSION: $\mathbb{P}_\beta(x_0,\ldots,x_k\text{ all connected})\leq\sum_{T\in\mathbb{T}_k}\sum_{x_{k+1},\ldots,x_{2k-1}}\prod_{i<j,\ i\sim j}\mathbb{P}_\beta(x_i\leftrightarrow x_j)$.
CONSTANT_SCOPE: Constant 1; the combinatorial bookkeeping is the labelled tree class of (I.1.11).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.aizenman-newman1984
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 Display (I.2.2) is the html equation table id=S2.E2 at paper.html L1215, inside block #S2.SS1.p6; canonical paper-tex.txt L431-L432. Borrowed from [4]. CONSUMER in this paper: canonical L1795 ("Applying the tree-graph inequality (I.2.2)"), Section I.5, outside this slice. Vertex and edge count of the tree class: $k+1$ labelled leaves plus $k-1$ unlabelled internal vertices of degree $3$, hence $2k$ vertices in total (not $2k-1$) and, by the handshake lemma $(k+1+3(k-1))/2=2k-1$ edges. The coefficient $2^{2n-2}$ used elsewhere in the series belongs to a different tree enumeration and is not derived from this count; the tree-indexing question for (I.1.11) is a separate slice. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.aizenman-newman1984 | .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 | packet relation requires: the higher-point tree-graph bound is attributed to [4] with no proof here

NODE: hutchcroft.eq.i.2.3
KIND: display
TITLE: (I.2.3) cluster-moment bound from the tree-graph inequality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
CONTRACT_ID: hutchcroft.eq.i.2.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a transitive weighted graph; integer $p\geq1$; $\beta\geq0$.
SOURCE_QUANTIFIERS: Every integer $p\geq1$.
SOURCE_CONCLUSION: $\mathbb{E}_\beta|K|^p\leq(2p-3)!!\,(\mathbb{E}_\beta|K|)^{2p-1}$, with $(2p-3)!!$ the number of trees with leaves $0,\ldots,p$ and all other vertices unlabelled of degree $3$.
CONSTANT_SCOPE: Combinatorial constant $(2p-3)!!$ only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.aizenman-newman1984,hutchcroft.eq.i.2.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 Display (I.2.3) is the html equation table id=S2.E3 at paper.html L1227, inside block #S2.SS1.p6; canonical paper-tex.txt L436. Derived in one sentence from the tree-graph inequalities; no consumer of the label (I.2.3) in paper I (series-level input). The same combinatorial factor $(2p-3)!!$ is the one asserted in Theorems I.1.6 and I.1.15, so a formalisation must not re-derive it with a different convention. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.aizenman-newman1984 | .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 | packet relation requires: the word "namely" introduces (I.2.3) as a consequence of the tree-graph inequalities of [4]
EDGE: hutchcroft.eq.i.2.2 | .scratch/source/paper.html#S2.SS1.p6@L1194-L1237 | packet relation requires: the moment bound is obtained by specialising the (k+1)-point bound to a single root and summing

NODE: hutchcroft.def.median
KIND: definition
TITLE: $|K_{\max}(\Lambda)|$ and the "edian" $M_\beta(\Lambda)$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p7.2@L1248-L1257
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.median
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Weighted graph $G=(V,E,J)$; finite non-empty $\Lambda\subseteq V$; $\beta\geq0$; clusters computed with respect to the whole graph $G$.
SOURCE_QUANTIFIERS: Every finite non-empty $\Lambda$ and every $\beta\geq0$.
SOURCE_CONCLUSION: $\mathscr{C}(\omega,\Lambda)=\{C\cap\Lambda:C\text{ a cluster of }\omega\}$; $|K_{\max}(\Lambda)|=\max\{|K_x\cap\Lambda|:x\in V\}=\max\{|K_x\cap\Lambda|:x\in\Lambda\}$; $M_\beta(\Lambda):=\min\{n\geq0:\mathbb{P}_\beta(|K_{\max}(\Lambda)|\geq n)\leq e^{-1}\}$.
CONSTANT_SCOPE: No constant; the threshold $e^{-1}$ is part of the definition.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L440-L444. "edian" is deliberate: footnote 13 records the pun on "median". The definition is only usable through its two consequences, both used later: $\mathbb{P}(|K_{\max}(\Lambda)|\geq M_\beta(\Lambda))\leq e^{-1}$ (by definition) and $\mathbb{P}(|K_{\max}(\Lambda)|\geq M_\beta(\Lambda)-1)>e^{-1}$ (by minimality, for $M_\beta(\Lambda)\geq1$). The second is what Lemma I.2.6 needs and it is not stated in the source. Cross-slice: the ambient model is Definition I.1.3, owned by slice A; this record deliberately depends on nothing so that the merge can re-point it. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.2.3
KIND: theorem
TITLE: Universal tightness of the maximum cluster size
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm3@L1259-L1289
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p7.1@L1239-L1240
CONTRACT_ID: hutchcroft.i.2.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $G=(V,E,J)$ a weighted graph; $\Lambda\subseteq V$ finite non-empty; clusters taken in the entire graph; $\beta\geq0$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$, $\lambda\geq1$ and $0<\varepsilon\leq1$ in (I.2.4)-(I.2.5); every $\beta\geq0$, $\lambda\geq1$ and $u\in V$ in (I.2.6).
SOURCE_CONCLUSION: (I.2.4) $\mathbb{P}_\beta(|K_{\max}(\Lambda)|\geq\lambda M_\beta(\Lambda))\leq\exp(-\lambda/9)$; (I.2.5) $\mathbb{P}_\beta(|K_{\max}(\Lambda)|<\varepsilon M_\beta(\Lambda))\leq27\varepsilon$; (I.2.6) $\mathbb{P}_\beta(|K_u\cap\Lambda|\geq\lambda M_\beta(\Lambda))\leq e\,\mathbb{P}_\beta(|K_u\cap\Lambda|\geq M_\beta(\Lambda))\exp(-\lambda/9)$.
CONSTANT_SCOPE: Universal constants $1/9$, $27$, $e$; no model-dependent constant, no $r$-dependent constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.median,ext.hutchcroft2021.thm2.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p7.1@L1239-L1240 canonical paper-tex.txt L446-L458; the three displays (I.2.4), (I.2.5), (I.2.6) are html equation tables inside that block (canonical L450, L452, L456) and are carried by this record rather than by three separate nodes, because an inline equation table has no resolvable html block of its own. PROOF IS BY CITATION ONLY: the attributing sentence is "We now state the universal tightness theorem of [74, Theorem 2.2]" at html #S2.SS1.p7.1 L1239-L1240 (canonical L435), which is what PROOF_SOURCE locates; the paper proves nothing here. Only (I.2.6) is consumed inside this slice (Corollary I.2.5). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.median | .scratch/source/paper.html#S2.Thmthm3@L1259-L1289 | packet relation requires: $M_\beta(\Lambda)$ and $∣K_{\max}(\Lambda)∣$ are used verbatim as defined, including the $\ell^\infty$ maximum over the partition
EDGE: ext.hutchcroft2021.thm2.2 | .scratch/source/paper.html#S2.SS1.p7.1@L1239-L1240 | packet relation requires: every inequality of the theorem is taken from [74, Theorem 2.2] with no argument given in this paper

NODE: hutchcroft.i.2.5
KIND: corollary
TITLE: Moment-ratio bound from universal tightness
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm5@L1300-L1314
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p9@L1317-L1350
CONTRACT_ID: hutchcroft.i.2.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $G=(V,E,J)$ a weighted graph; $q,p\geq0$; $\beta\geq0$; $x\in V$; $W\subseteq V$ finite.
SOURCE_QUANTIFIERS: Every $q,p\geq0$, $\beta\geq0$, $x\in V$ and every finite $W\subseteq V$.
SOURCE_CONCLUSION: $\mathbb{E}_\beta|K_x\cap W|^{p+q}\preceq_{p,q}M_\beta(W)^{q}\,\mathbb{E}_\beta|K_x\cap W|^{p}$.
CONSTANT_SCOPE: $\preceq_{p,q}$ means a constant depending only on $p,q$, never on $G,\beta,x,W$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.3,hutchcroft.def.median
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p9@L1317-L1350 canonical paper-tex.txt L466-L472 (statement), L474-L490 (proof). Proof checked line by line: layer cake, split at $t=M$, the upper branch uses (I.2.6) with $\lambda=t/M\geq1$, Markov gives $\mathbb{P}(X\geq M)\leq\mathbb{E}X^p/M^p$, and $s=t/(9M)$ gives $\int_M^\infty t^{p+q-1}e^{1-t/(9M)}dt\asymp_{p,q}M^{p+q}$. No defect; the only suppressed detail is that the layer-cake constant is two-sided in $p,q$, which the displayed $\asymp_{p,q}$ asserts. $p=q=0$ is trivial and vacuous, so no division by $p$ occurs. CONSUMERS recorded: canonical L1029, L1222, L1493, L1886 (Sections I.4 and I.5). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.3 | .scratch/source/paper.html#S2.SS1.p9@L1317-L1350 | packet relation requires: inequality (I.2.6) of Theorem I.2.3 is applied to the exponential tail of $∣K_x\cap W∣$ above $M_\beta(W)$
EDGE: hutchcroft.def.median | .scratch/source/paper.html#S2.Thmthm5@L1300-L1314 | packet relation requires: $M_\beta(W)$ is the edian of $∣K_{\max}(W)∣$ as defined there, and the split point $t=M$ is that quantity

NODE: hutchcroft.i.2.5:step-ibp
KIND: step
TITLE: Layer cake, split at the edian, Markov and the $s=t/9M$ rescaling
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p9.1@L1318-L1318
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p9@L1317-L1350
CONTRACT_ID: hutchcroft.i.2.5:step-ibp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $X=|K_x\cap W|$ non-negative, $M=M_\beta(W)$; all moments of $X$ allowed to be infinite.
SOURCE_QUANTIFIERS: Every $p,q\geq0$; every $M>0$.
SOURCE_CONCLUSION: $\mathbb{E}X^{p+q}\asymp_{p,q}\int_0^\infty t^{p+q-1}\mathbb{P}(X\geq t)dt\leq M^q\int_0^\infty t^{p-1}\mathbb{P}(X\geq t)dt+\mathbb{P}(X\geq M)\int_M^\infty t^{p+q-1}e^{1-t/(9M)}dt\preceq_{p,q}M^q\mathbb{E}X^p$.
CONSTANT_SCOPE: Only $\preceq_{p,q}$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.3
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p9@L1317-L1350 canonical paper-tex.txt L476-L488. Reconstructed in detail; the source displays the same chain. Substitution $s=t/(9M)$ turns the second integral into $M^{p+q}\int_{1/9}^\infty(9s)^{p+q-1}e^{1-s}9\,ds$, finite and $\asymp_{p,q}M^{p+q}$. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.3 | .scratch/source/paper.html#S2.SS1.p9.2@L1332-L1332 | packet relation requires: only the tail inequality (I.2.6) is used, in the form $\mathbb{P}(X\geq t)\leq e\,\mathbb{P}(X\geq M)e^{-t/(9M)}$ for $t\geq M$

NODE: hutchcroft.i.2.6
KIND: lemma
TITLE: Lower bound on cluster moments by the edian
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm6@L1356-L1369
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.4@L1370-L1385
CONTRACT_ID: hutchcroft.i.2.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $\beta,r\geq0$; $p\geq1$; $M_{\beta,r}=M_\beta(B_r)$ the edian of $|K_{\max}(B_r)|$ under $\mathbb{P}_{\beta,r}$; $B_r=\{y\in\mathbb{Z}^d:\|y\|\leq r\}$.
SOURCE_QUANTIFIERS: Every $\beta,r\geq0$ and every $p\geq1$.
SOURCE_CONCLUSION: $\mathbb{E}_{\beta,r}|K|^p\geq\mathbb{E}_{\beta,r}|K\cap B_{2r}|^p\geq(M_{\beta,r}-1)^p\mathbb{P}_{\beta,r}(|K\cap B_{2r}|\geq M_{\beta,r}-1)\geq\frac{(M_{\beta,r}-1)^{p+1}}{e|B_r|}$.
CONSTANT_SCOPE: Universal $e$ and the scale $|B_r|$; no growth rate of $|B_r|$ is used.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.median,assumption.weighted_graph
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.4@L1370-L1385 canonical paper-tex.txt L494-L500 (statement), L502-L508 (proof). Proof checked: if a cluster meets $B_r$ in at least $M-1$ points then every $x\in B_r$ of that cluster has $|K\cap B_{2r}(x)|\geq M-1$; such a cluster exists with probability at least $1/e$ by MINIMALITY in the definition of the edian (this uses $\mathbb{P}(|K_{\max}(B_r)|\geq M-1)>e^{-1}$, which is not stated in the source and needs $M\geq1$); transitivity then converts the per-vertex event into the average $(1/|B_r|)\sum_{x\in B_r}$. Typographic slip: the last display prints $M_\beta$ where $M_{\beta,r}$ is meant. Transitivity of the cut-off law is a genuine hypothesis (see assumption.weighted_graph). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.median | .scratch/source/paper.html#S2.SS1.4@L1370-L1385 | packet relation requires: $M_{\beta,r}$ and the event $∣K_{\max}(B_r)∣\geq M_{\beta,r}-1$ are the edian definition applied with $\Lambda=B_r$
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S2.Thmthm6@L1356-L1369 | packet relation requires: the cut-off law $\mathbb{P}_{\beta,r}$ and the balls $B_r$ are those of the weighted $\mathbb{Z}^d$ model; translation invariance is what makes the average over $x\in B_r$ legitimate

NODE: hutchcroft.i.2.6:step-transitivity
KIND: step
TITLE: Transitivity converts a per-vertex event into the average over $B_r$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p11.2@L1382-L1383
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p11@L1372-L1384
CONTRACT_ID: hutchcroft.i.2.6:step-transitivity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Lemma I.2.6; the cut-off law $\mathbb{P}_{\beta,r}$ is invariant under the translations of the ambient transitive graph.
SOURCE_QUANTIFIERS: Every $\beta,r\geq0$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta,r}(|K\cap B_{2r}|\geq M-1)=\frac{1}{|B_r|}\mathbb{E}_{\beta,r}\sum_{x\in B_r}\mathbb{1}(|K\cap B_{2r}(x)|\geq M-1)\geq\frac{M-1}{e|B_r|}$.
CONSTANT_SCOPE: Universal $e$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.median
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p11@L1372-L1384 canonical paper-tex.txt L504-L506. Reconstructed; the source displays exactly this identity and inequality. Note $B_{2r}(x)$ is the translate, and $|B_{2r}(x)\cap K|$ equals the size of the cluster of $x$ inside the ball of radius $2r$ around $x$, which is the quantity the edian controls only through the single ball $B_r$. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.median | .scratch/source/paper.html#S2.SS1.p11.2@L1382-L1383 | packet relation requires: the factor $M-1$ on the right is $∣K_{\max}(B_r)∣\geq M-1$ pushed through the averaging

NODE: hutchcroft.i.2.7
KIND: theorem
TITLE: Gladkov three-point inequality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm7@L1391-L1404
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p12.1@L1387-L1389
CONTRACT_ID: hutchcroft.i.2.7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $G=(V,E,J)$ a weighted graph; Bernoulli bond percolation on it; $\beta\geq0$; $x,y,z\in V$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$ and every $x,y,z\in V$.
SOURCE_CONCLUSION: $\mathbb{P}_\beta(x\leftrightarrow y\leftrightarrow z)^2\leq8\,\mathbb{P}_\beta(x\leftrightarrow y)\mathbb{P}_\beta(y\leftrightarrow z)\mathbb{P}_\beta(z\leftrightarrow x)$.
CONSTANT_SCOPE: Universal constant $8=(2^{3/2})^2$; no model constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.gladkov2024,assumption.weighted_graph
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p12.1@L1387-L1389 canonical paper-tex.txt L512-L518; attributing sentence at L510. PROOF IS BY CITATION: "The last correlation inequality we make note of was established in the recent work of [52], and is once again a (non-obvious) consequence of the BK inequality." Nothing is proved here. CONSUMERS in this paper: proof of Corollary I.2.8 (canonical L530-L545) and Section I.5 (canonical L1864, three-point terms). The higher-$k$ extension is deferred to Paper II (footnote 14) and is not in this slice. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.gladkov2024 | .scratch/source/paper.html#S2.SS1.p12.1@L1387-L1389 | packet relation requires: the whole inequality is taken from [52] with no argument in this paper
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S2.Thmthm7@L1391-L1404 | packet relation requires: the statement is made for Bernoulli bond percolation on a weighted graph, i.e. the ambient model typing

NODE: hutchcroft.i.2.8
KIND: corollary
TITLE: Cluster-size weighted second-moment bound from Gladkov
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm8@L1408-L1421
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.5@L1422-L1455
CONTRACT_ID: hutchcroft.i.2.8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $G=(V,E,J)$ a TRANSITIVE weighted graph; Bernoulli bond percolation; $\beta\geq0$; $x\in V$; $W\subseteq V$ finite.
SOURCE_QUANTIFIERS: Every $\beta\geq0$, $x\in V$ and finite $W\subseteq V$.
SOURCE_CONCLUSION: $\mathbb{E}_\beta[|K_x|\,|K_x\cap W|]\leq2^{3/2}\,\mathbb{E}_\beta|K|\sqrt{|W|\,\mathbb{E}_\beta|K_x\cap W|}$.
CONSTANT_SCOPE: Universal $2^{3/2}$; no model constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.7,assumption.weighted_graph
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.5@L1422-L1455 canonical paper-tex.txt L522-L528 (statement), L530-L545 (proof). Proof checked: $\mathbb{E}[|K_x||K_x\cap W|]=\sum_{y\in V,z\in W}\mathbb{P}(x\leftrightarrow y\leftrightarrow z)$; Gladkov bounds each term by $2^{3/2}(\mathbb{P}(x\leftrightarrow y)\mathbb{P}(y\leftrightarrow z)\mathbb{P}(z\leftrightarrow x))^{1/2}$; the sum over $y$ is bounded by $\mathbb{E}_\beta|K|$ via Cauchy-Schwarz and transitivity (so $\mathbb{P}(y\leftrightarrow z)$ may be replaced by $\mathbb{P}(0\leftrightarrow z-y)$); a second Cauchy-Schwarz over $z\in W$ gives $\sum_{z\in W}\mathbb{P}(z\leftrightarrow x)^{1/2}\leq\sqrt{|W|\mathbb{E}|K\cap W|}$. Transitivity is used twice (once per Cauchy-Schwarz) and is genuinely needed, not decorative. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.7 | .scratch/source/paper.html#S2.SS1.5@L1422-L1455 | packet relation requires: the square-rooted Gladkov bound is the first display of the proof
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S2.Thmthm8@L1408-L1421 | packet relation requires: transitivity of the weighted graph is required for the two Cauchy-Schwarz reductions

NODE: hutchcroft.i.2.8:step-cauchy
KIND: step
TITLE: Two Cauchy-Schwarz reductions, one over $V$ and one over $W$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p14.3@L1435-L1435
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p14@L1424-L1454
CONTRACT_ID: hutchcroft.i.2.8:step-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Corollary I.2.8; transitivity so that $\sum_y\mathbb{P}(x\leftrightarrow y)=\sum_y\mathbb{P}(y\leftrightarrow z)=\mathbb{E}_\beta|K|$.
SOURCE_QUANTIFIERS: First over $y\in V$ for each fixed $z\in W$, then over $z\in W$.
SOURCE_CONCLUSION: $\sum_{y\in V}\mathbb{P}(x\leftrightarrow y)^{1/2}\mathbb{P}(y\leftrightarrow z)^{1/2}\leq\sqrt{(\sum_y\mathbb{P}(x\leftrightarrow y))(\sum_y\mathbb{P}(y\leftrightarrow z))}=\mathbb{E}_\beta|K|$ and then $\sum_{z\in W}\mathbb{P}(z\leftrightarrow x)^{1/2}\leq\sqrt{|W|\mathbb{E}_\beta|K\cap W|}$.
CONSTANT_SCOPE: Universal $2^{3/2}$ carried from the parent.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.7
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p14@L1424-L1454 canonical paper-tex.txt L534-L543. Reconstructed; the source displays both Cauchy-Schwarz lines. The second application needs $\mathbb{E}_\beta|K\cap W|=\sum_{z\in W}\mathbb{P}(z\leftrightarrow x)$, which is where finiteness of $W$ is used. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.7 | .scratch/source/paper.html#S2.SS1.p14.3@L1435-L1435 | packet relation requires: the $2^{3/2}$ factor and the product of the three two-point probabilities come from Gladkov

NODE: hutchcroft.def.rv
KIND: definition
TITLE: Regular variation, slow variation and index
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS2.p1@L1482-L1485
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.rv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f:(0,\infty)\to\mathbb{R}$; for the index theorem $f$ is also measurable.
SOURCE_QUANTIFIERS: Every $\lambda>0$; the limit is $x\to\infty$.
SOURCE_CONCLUSION: $f$ is regularly varying iff it is eventually non-vanishing and $\lim_{x\to\infty}f(\lambda x)/f(x)$ exists for every $\lambda>0$; if $f$ is also measurable there is a unique index $\alpha\in\mathbb{R}$ with $\lim f(\lambda x)/f(x)=\lambda^\alpha$ uniformly for $\lambda$ in compact subsets of $(0,\infty)$. Slowly varying means index $0$; every regularly varying $f$ of index $\alpha$ satisfies $f(x)=x^\alpha\ell(x)$ with $\ell$ slowly varying; regular variation is preserved by first-order asymptotic equivalence.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.bgt.thm1.2.1
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L561. The index-existence and uniformity statement is [24, Theorem 1.2.1]; the paper states it rather than proving it. Also recorded here: $f(x)=x^{\alpha\pm o(1)}$ is strictly weaker than regular variation, the paper’s own example being $(2+\sin x)x^\alpha$ (checked: it is not eventually non-vanishing in the ratio sense). Two facts used silently later but NOT part of this record: a regularly varying function of negative index tends to $0$, and a slowly varying function is bounded above and away from $0$ on $[R,\infty)$; both need the uniform convergence theorem and are supplied as a bridge step in this packet (hutchcroft.i.3.2:step-a-at-least-1). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.bgt.thm1.2.1 | .scratch/source/paper.html#S2.SS2.p1@L1482-L1485 | packet relation requires: the existence and compact-uniformity of the index are quoted from [24, Theorem 1.2.1]

NODE: hutchcroft.i.2.10
KIND: lemma
TITLE: Karamata integral asymptotics, both index signs, with the negative branch corrected
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm10@L1489-L1511
PROOF_SOURCE: .scratch/source/paper.html#S2.Thmthm10@L1489-L1511
CONTRACT_ID: hutchcroft.i.2.10
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f:(0,\infty)\to\mathbb{R}$ measurable and regularly varying of index $\alpha$, in the sense of hutchcroft.def.rv.
SOURCE_QUANTIFIERS: First display: $\alpha>-1$, $r\to\infty$. Second display: $\alpha<-1$, every $r>0$, $r\to\infty$.
SOURCE_CONCLUSION: If $\alpha>-1$ then $\int_1^r f(s)ds\sim rf(r)/(\alpha+1)$. If $\alpha<-1$ then $\int_r^\infty f(s)ds<\infty$ for every $r>0$ and $\int_r^\infty f(s)ds\sim rf(r)/(-\alpha-1)$; the printed constant $1/(1-\alpha)$ is FALSE and must not be used.
CONSTANT_SCOPE: Constants $1/(\alpha+1)$ and $1/(-\alpha-1)$; no model constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.rv,ext.feller.8.9.1
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.Thmthm10@L1489-L1511 canonical paper-tex.txt L565-L575. ERATUM CONFIRMED, printed text must be corrected: the negative-index half prints $\int_r^\infty f\sim rf(r)/(1-\alpha)$; the correct constant is $rf(r)/(-\alpha-1)$. Independent check run in this session (sympy, results quoted in I23Validation.md): $\int_r^\infty s^\alpha ds=-r^{\alpha+1}/(\alpha+1)$ for $\alpha<-1$; at $\alpha=-2$ the integral is $1/r$ whereas the printed formula gives $1/(3r)$; at $\alpha=-3/2$ the integral is $2r^{-1/2}$ whereas the printed formula gives $(2/5)r^{-1/2}$. BLAST RADIUS, corrected against the earlier packet: the claim "no consumer of the defective half in paper I" is WRONG. Canonical L1094 (the aside after Lemma I.4.13) says of both $r^a\int_r^\infty s^{-a-1}h(s)ds$ and $r^{-a}\int_1^r s^{a-1}h(s)ds$ that they are "asymptotic to multiples of $h$ by Lemma I.2.10"; the first of the two is the negative-index branch, and with the corrected constant it equals $h(r)/a$ for slowly varying $h$ (e.g. $h\equiv1$ gives $1/a$) whereas the printed constant would give $h(r)/(a+2)$. The aside is NOT used by the proof of Lemma I.4.13: that proof (from canonical L1096 onward) is a Tonelli computation followed by inequality bounds (canonical L1098-L1105), and it is TONELLI, not the aside, that supplies the $1/a$ factor of the theorem’s conclusion. So no theorem of paper I changes value; what changes is the multiple quoted in the aside, which must be $1/a$ and not $1/(a+2)$. Consumer check completed for all three invocations: L1094 (negative branch, aside only), L1373 (positive branch, index $b-a-1>-1$, result $1/(b-a)$, consistent), L593 (backward mention only). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.rv | .scratch/source/paper.html#S2.Thmthm10@L1489-L1511 | packet relation requires: the hypothesis "regularly varying of index $\alpha$" is exactly the notion defined there, including measurability
EDGE: ext.feller.8.9.1 | .scratch/source/paper.html#S2.Thmthm10@L1489-L1511 | packet relation requires: the lemma is quoted from [47, Theorem VIII.9.1]; the paper gives no proof

NODE: hutchcroft.i.2.11
KIND: theorem
TITLE: Karamata’s Tauberian theorem in probabilistic form
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm11@L1515-L1528
PROOF_SOURCE: .scratch/source/paper.html#S2.Thmthm11@L1515-L1528
CONTRACT_ID: hutchcroft.i.2.11
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f$ regularly varying of index $-\alpha$ for some $0\leq\alpha<1$; $X$ a non-negative random variable.
SOURCE_QUANTIFIERS: $h\downarrow0$ and $x\to\infty$; the assertion is an equivalence.
SOURCE_CONCLUSION: $\mathbb{E}[1-e^{-hX}]\sim f(1/h)$ as $h\downarrow0$ if and only if $\mathbb{P}(X\geq x)\sim f(x)/\Gamma(1-\alpha)$ as $x\to\infty$, where $\Gamma(z)=\int_0^\infty t^{z-1}e^{-t}dt$.
CONSTANT_SCOPE: Only the Gamma factor $\Gamma(1-\alpha)$; no model constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.feller.13.5.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.Thmthm11@L1515-L1528 canonical paper-tex.txt L579-L585. Quoted from [47, Theorem XIII.5.2] with no proof. CONSISTENCY CHECK performed here: with $\mathbb{P}(X\geq x)=f(x)/\Gamma(1-\alpha)$ and $f$ of index $-\alpha$, integrating by parts gives $\mathbb{E}[1-e^{-hX}]=\int_0^\infty he^{-hx}\mathbb{P}(X\geq x)dx\sim h\,(1/h)^{-\alpha}\Gamma(1-\alpha)/\Gamma(1-\alpha)=f(1/h)$ for $f(x)=x^{-\alpha}$, so the normalisation is right. DOMAIN CONDITION THAT MATTERS DOWNSTREAM: the hypothesis $0\leq\alpha<1$ is a genuine restriction and is exactly what forces $a\geq1$ in Proposition I.3.2, where the index of $A_3f^{-1}(s)^\alpha/s$ is $-(1-1/a)$. CONSUMERS: Prop I.3.2 proof (canonical L747) and hutchcroft.i.3.2:step-tauberian. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.feller.13.5.2 | .scratch/source/paper.html#S2.Thmthm11@L1515-L1528 | packet relation requires: the theorem is quoted from [47, Theorem XIII.5.2)] with no proof in this paper

NODE: hutchcroft.def.logint
KIND: definition
TITLE: Logarithmic integrability and logarithmically integrable error functions
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS2.p4@L1529-L1541
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.logint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $h:(0,\infty)\to\mathbb{R}$ measurable.
SOURCE_QUANTIFIERS: Some $r_0$; $r\to\infty$.
SOURCE_CONCLUSION: $h$ is logarithmically integrable iff it is locally integrable on some $[r_0,\infty)$ and $\int_{r_0}^\infty|h(r)|\,dr/r=\int_{\log r_0}^\infty|h(e^t)|dt<\infty$; it is a logarithmically integrable error function if moreover $h(r)\to0$; these functions form an algebra; regularly varying functions of negative index are always such, and a regularly varying function is such iff it is logarithmically integrable.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L587-L591. Correct. The algebra claim follows immediately from the $t=\log r$ representation. CONSUMERS: Lemma I.2.12 and, outside this slice, the kernel error $\delta_r$ of Definition I.1.3 and Lemmas I.4.13 and I.4.21. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.2.12
KIND: lemma
TITLE: $f\prime\sim ar^{-1}f$ forces regular variation of index $a$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm12@L1545-L1550
PROOF_SOURCE: .scratch/source/paper.html#S2.SS2.2@L1554-L1584
CONTRACT_ID: hutchcroft.i.2.12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f:(0,\infty)\to(0,\infty)$ differentiable, eventually non-vanishing, with $f\prime(r)\sim ar^{-1}f(r)$ for some $a>0$; in the second part $f\\prime(r)=a(1-h(r))r^{-1}f(r)$ with $h$ a logarithmically integrable error function.
SOURCE_QUANTIFIERS: $r\to\infty$; $a>0$ fixed; $R\geq r\geq1$ in the integrated identity.
SOURCE_CONCLUSION: $f$ is regularly varying of index $a$; in the second case there is $A>0$ with $f(r)\sim Ar^a$.
CONSTANT_SCOPE: $A=r_0^{-a}f(r_0)\exp[-a\int_{r_0}^\infty h(s)\,ds/s]$, which is finite because $h$ is logarithmically integrable.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.logint,hutchcroft.def.rv
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS2.2@L1554-L1584 canonical paper-tex.txt L595-L599 (statement), L601-L615 (proof). Proof checked: $(\log f)\prime=a(1-h(r))/r$, integration from $r$ to $R$ gives $f(R)=\exp[-a\int_r^R h(s)ds/s](R/r)^a f(r)$, which is regular variation of index $a$; in the second case $\int_{r_0}^r h(s)ds/s$ converges by logarithmic integrability, giving the constant $A$. Minor: "eventually non-vanishing" is redundant given the codomain $(0,\infty)$, but it is harmless. Note the differentiated object in the printed proof is written $f^{\\prime}$; the theorem as printed writes $f^{\prime}$, and this packet reproduces the printed symbol rather than silently repointing it. CONSUMERS: Proposition I.4.15 (canonical L1169, L1194). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.logint | .scratch/source/paper.html#S2.SS2.2@L1554-L1584 | packet relation requires: the convergence of $\int_{r_0}^\infty h(s)ds/s$ to a finite value is exactly logarithmic integrability
EDGE: hutchcroft.def.rv | .scratch/source/paper.html#S2.Thmthm12@L1545-L1550 | packet relation requires: the conclusion "regularly varying of index $a$" is stated in the sense of that definition

NODE: hutchcroft.i.2.12:step-integrate
KIND: step
TITLE: Integrate $(\log f)\prime$ and exponentiate
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS2.p7.1@L1557-L1557
PROOF_SOURCE: .scratch/source/paper.html#S2.SS2.p7@L1556-L1583
CONTRACT_ID: hutchcroft.i.2.12:step-integrate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Lemma I.2.12; $|h(r)|\to0$ as $r\to\infty$.
SOURCE_QUANTIFIERS: Every $R\geq r\geq1$.
SOURCE_CONCLUSION: $f(R)=\exp[-a\int_r^R h(s)\,ds/s]\,(R/r)^a f(r)$.
CONSTANT_SCOPE: Only $a$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.logint
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS2.p7@L1556-L1583 canonical paper-tex.txt L603-L611. Reconstructed; the source displays this identity. The passage from $f\prime\sim ar^{-1}f$ to the stated form of $h$ is where the differentiability and the eventual positivity are used. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.logint | .scratch/source/paper.html#S2.SS2.p7.1@L1557-L1557 | packet relation requires: the finite limit of $\int_{r_0}^r h(s)ds/s$ used in the second part is logarithmic integrability of $h$

NODE: hutchcroft.def.doubling
KIND: definition
TITLE: Doubling and reverse doubling
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS2.p8@L1585-L1587
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.doubling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Increasing $f:[1,\infty)\to(0,\infty)$.
SOURCE_QUANTIFIERS: Every $x\geq1$.
SOURCE_CONCLUSION: $f$ is doubling iff there is $C$ with $f(2x)\leq Cf(x)$ for all $x\geq1$; $f$ is reverse doubling iff its inverse is doubling, equivalently there is $C$ with $f(Cx)\geq2f(x)$ for all $x\geq1$; positive increasing regularly varying functions of positive index are both.
CONSTANT_SCOPE: The doubling constant $C$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L617. Correct. The final sentence needs index $\geq0$ for doubling and index $>0$ for reverse doubling; the source states the combined claim only for positive index, which is what Proposition I.3.1 needs. CONSUMER: hypothesis "$f^{-1}$ is doubling" of Proposition I.3.1. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.2.13
KIND: theorem
TITLE: Spatially averaged two-point upper bound at criticality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm13@L1596-L1601
PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p1@L1592-L1595
CONTRACT_ID: hutchcroft.i.2.13
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Long-range percolation on $\mathbb{Z}^d$ with a kernel $J$ as in Definition I.1.3, $\alpha>0$, at the critical parameter $\beta_c$; $B_r=\{x\in\mathbb{Z}^d:\|x\|\leq r\}$.
SOURCE_QUANTIFIERS: Every $r\geq1$.
SOURCE_CONCLUSION: $\sum_{x\in B_r}\mathbb{P}_{\beta_c}(0\leftrightarrow x)\preceq r^{\alpha}$.
CONSTANT_SCOPE: $\preceq$ carries a constant depending on the model data only, never on $r$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.hutchcroft2022,assumption.weighted_graph
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p1@L1592-L1595 canonical paper-tex.txt L623-L625; attributing sentence at L621 ("the most important such result is the following spatially-averaged upper bound on the two-point function, proven in [76] following the hierarchical analysis of [77]"). PROOF IS BY CITATION. The parenthetical "(The theorem holds vacuously when $\alpha\geq d$)" is an expository slip rather than a mathematical one: for $\alpha\geq d$ the bound is trivially true because the left side is at most $|B_r|\preceq r^d\leq r^\alpha$; it is not vacuous. CONSUMERS in this paper: Corollary I.2.15 (canonical L633) and Section I.4 (canonical L1029, L1222). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.hutchcroft2022 | .scratch/source/paper.html#S2.SS3.p1@L1592-L1595 | packet relation requires: the whole estimate is attributed to [76] with no proof in this paper
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S2.Thmthm13@L1596-L1601 | packet relation requires: the model, the ball $B_r$ and the critical measure $\mathbb{P}_{\beta_c}$ are those of the weighted $\mathbb{Z}^d$ model

NODE: hutchcroft.i.2.14
KIND: theorem
TITLE: Pointwise two-point function in the regime $\alpha<1$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm14@L1605-L1612
PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p2@L1602-L1604
CONTRACT_ID: hutchcroft.i.2.14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $\alpha<1$, together with the $\mathbb{Z}^d$ long-range model at $\beta_c$.
SOURCE_QUANTIFIERS: Every $x\neq y$ in $\mathbb{Z}^d$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(x\leftrightarrow y)\asymp\|x-y\|^{-d+\alpha}$.
CONSTANT_SCOPE: Two-sided constants depending on the model data only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.baumler-berger2024,ext.hutchcroft-ptf
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p2@L1602-L1604 canonical paper-tex.txt L629-L631; attributing sentence at L627 (lower bound from [20], pointwise two-sided estimate from [73]). PROOF IS BY CITATION. No consumer of the label "Theorem I.2.14" exists anywhere in paper I (text search), so this is a series-level input; it is retained because it is a printed item of the slice. The two-sided constant is NOT asserted to be 1, and the record must not be merged into an interface that assumes a normalised constant. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: ext.baumler-berger2024 | .scratch/source/paper.html#S2.SS3.p2@L1602-L1604 | packet relation requires: the matching lower bound is attributed to [20]
EDGE: ext.hutchcroft-ptf | .scratch/source/paper.html#S2.SS3.p2@L1602-L1604 | packet relation requires: the pointwise two-sided estimate is attributed to [73]

NODE: hutchcroft.i.2.15
KIND: corollary
TITLE: Edian upper bound $M_r\preceq r^{(d+\alpha)/2}$
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm15@L1616-L1621
PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p3@L1613-L1615
CONTRACT_ID: hutchcroft.i.2.15
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Model of Definition I.1.3 on $\mathbb{Z}^d$ at $\beta_c$; $\alpha>0$; $M_r=M_{\beta_c,r}$ the edian of $|K_{\max}(B_r)|$ under $\mathbb{P}_{\beta_c,r}$.
SOURCE_QUANTIFIERS: Every $r\geq1$; the same bound is asserted for the edian of $|K_{\max}(B_r)|$ under the non-cut-off measure $\mathbb{P}_{\beta_c}$.
SOURCE_CONCLUSION: $M_r\preceq r^{(d+\alpha)/2}$.
CONSTANT_SCOPE: Constant depending on the model data only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.13,hutchcroft.i.2.6,hutchcroft.i.1.beta_c.bilat
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 canonical paper-tex.txt L635-L637; the referring sentence is at L633. The source gives NO proof: it says only that Theorem I.2.13 and Lemma I.2.6 have this consequence. The derivation is therefore carried as hutchcroft.i.2.15:step-drift and is necessary for the record to be honest. The non-cut-off half of the statement is not derived in this packet and is recorded as a residual obligation in the NOTE of the step; it is not used in Sections I.2-I.3. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.13 | .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 | packet relation requires: the averaged two-point bound bounds $\mathbb{E}_{\beta_c,r}∣K∣$ and hence, through Lemma I.2.6, the edian
EDGE: hutchcroft.i.2.6 | .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 | packet relation requires: the lower bound on the first moment in terms of $M_r-1$ is combined with $∣B_r∣\preceq r^d$
EDGE: hutchcroft.i.1.beta_c.bilat | .scratch/source/paper.html#S2.Thmthm15@L1616-L1621 | packet relation requires: the measure $\mathbb{P}_{\beta_c,r}$ needs $0<\beta_c<\infty$, which is a derived result here and not an assumed premise

NODE: hutchcroft.i.2.15:step-drift
KIND: step
TITLE: From the averaged two-point bound and the edian lower bound to the edian upper bound
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS3.p3@L1613-L1615
PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p3@L1613-L1615
CONTRACT_ID: hutchcroft.i.2.15:step-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Corollary I.2.15; the cut-off law is dominated by the full law because the cut-off kernel satisfies $J_r\leq J$.
SOURCE_QUANTIFIERS: Every $r\geq1$.
SOURCE_CONCLUSION: $(M_r-1)^2\leq e|B_r|\,\mathbb{E}_{\beta_c,r}|K|\leq e|B_r|\sum_{x\in B_r}\mathbb{P}_{\beta_c}(0\leftrightarrow x)\preceq r^{d+\alpha}$, hence $M_r\preceq r^{(d+\alpha)/2}$.
CONSTANT_SCOPE: $e$ times the constant of Theorem I.2.13.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.13,hutchcroft.i.2.6
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 canonical paper-tex.txt L633. NOT PRINTED IN THE SOURCE: the source asserts the corollary without proof, so this reconstruction is a proposal. Uses Lemma I.2.6 at $p=1$, monotonicity $\mathbb{P}_{\beta_c,r}\leq_{\mathrm{st}}\mathbb{P}_{\beta_c}$, and $|B_r|\preceq r^d$; the last is a lattice-volume fact that is used silently and is not stated anywhere in the paper. RESIDUAL OBLIGATION, not discharged here: the second sentence of the statement about the edian under $\mathbb{P}_{\beta_c}$ needs the corresponding averaged bound for the non-cut-off law and the same argument with $B_r$ replaced by $B_r\cap K$; it is not used in I.2-I.3 and is left open rather than asserted. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.13 | .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 | packet relation requires: the bound $\sum_{x\in B_r}\mathbb{P}_{\beta_c}(0\leftrightarrow x)\preceq r^{\alpha}$ is the input
EDGE: hutchcroft.i.2.6 | .scratch/source/paper.html#S2.SS3.p3@L1613-L1615 | packet relation requires: the inequality $\mathbb{E}_{\beta_c,r}∣K∣\geq(M_r-1)^2/(e∣B_r∣)$ is Lemma I.2.6 at $p=1$

NODE: hutchcroft.i.2.2
KIND: lemma
TITLE: Four-point two-cluster bound
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm2@L1180-L1193
PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p5@L1177-L1179
CONTRACT_ID: hutchcroft.i.2.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a weighted graph $G=(V,E,J)$ at any $\beta\geq0$; $x,y,z,w\in V$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$ and every $x,y,z,w\in V$.
SOURCE_CONCLUSION: $0\leq\mathbb{P}_\beta(x\leftrightarrow y)\mathbb{P}_\beta(z\leftrightarrow w)-\mathbb{P}_\beta(x\leftrightarrow y\circ z\leftrightarrow w)\leq\mathbb{P}_\beta(x\leftrightarrow y\leftrightarrow z\leftrightarrow w)$, where the middle event is the disjoint occurrence $\{x\leftrightarrow y\}\circ\{z\leftrightarrow w\}$ of BK.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.1
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S2.SS1.p5@L1177-L1179 canonical paper-tex.txt L417-L423. NO PRINTED PROOF: the source only says (canonical L415) that the lemma "is a special case of Lemma I.2.1 and generalizes [3, Lemma 4]", and that sentence is what PROOF_SOURCE locates. REQUIRED READING OF THE PRINTED SYMBOL: the middle factor is the disjoint occurrence of $\{x\leftrightarrow y\}$ and $\{z\leftrightarrow w\}$, which the source writes with a negation-like glyph. Under that reading the left inequality is BK and the right is FKG plus the exact partition $\{x\leftrightarrow y,z\leftrightarrow w\}=(\text{disjoint occurrence})\sqcup(\text{all four connected})$; a formalisation must fix one reading and this is the only reading under which the left inequality holds for all $\beta$. Obtaining the lemma as a special case of Lemma I.2.1 needs $F(K_x)=\mathbb{1}(y\in K_x)$, $G(K_z)=\mathbb{1}(w\in K_z)$ (or the transposed choice) and is a genuine dependency, not a restatement. [3, Lemma 4] is an attribution of generality only and is NOT recorded as a use of a premise. Consumers: canonical L1056 and L2189. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.1 | .scratch/source/paper.html#S2.SS1.p5@L1177-L1179 | packet relation requires: the source states the lemma as a special case of Lemma I.2.1, obtained by taking indicators of the two connections

NODE: hutchcroft.def.sizebiased
KIND: definition
TITLE: Size-biased measure $\hat{\mathbb{P}}_{\beta_c,r}$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p1@L1640-L1642
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.sizebiased
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $r>0$; the cut-off model at $\beta_c$; $K$ the cluster of the origin under $\mathbb{P}_{\beta_c,r}$.
SOURCE_QUANTIFIERS: Every $r>0$.
SOURCE_CONCLUSION: $\hat{\mathbb{P}}_{\beta_c,r}$ has Radon-Nikodym derivative $|K|/\mathbb{E}_{\beta_c,r}|K|$ with respect to $\mathbb{P}_{\beta_c,r}$, and $\hat{\mathbb{E}}_{\beta_c,r}$ is its expectation.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L647. Well defined because under the cut-off law $1\leq\mathbb{E}_{\beta_c,r}|K|\leq|B_r|<\infty$; that finiteness is used silently and is recorded here rather than as an extra hypothesis. Cross-slice: the notation is the one introduced for Definition I.1.5 (slice A); this record owns only the size-biasing, so the merge must reconcile the two. CONSUMERS inside this slice: Proposition I.3.1 (via its hypotheses), Proposition I.3.2 hypothesis (2), and the derivation of (I.3.4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.def.ghost
KIND: definition
TITLE: Independent ghost field of intensity $h$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p4@L1699-L1753
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.ghost
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $h>0$; a percolation configuration on $\mathbb{Z}^d$.
SOURCE_QUANTIFIERS: Every $r,h>0$.
SOURCE_CONCLUSION: $\mathcal{G}$ is a random subset of $\mathbb{Z}^d$ with each vertex included independently with probability $1-e^{-h}$, independent of the percolation configuration; $\mathbb{P}_{\beta_c,r,h}$ and $\mathbb{P}_{\beta_c,\infty,h}$ are the joint laws with and without cut-off; and $\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})=\mathbb{E}_{\beta_c,r}[1-e^{-h|K|}]$.
CONSTANT_SCOPE: No constant; the intensity $h$ is the only parameter.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L679-L683. The definition and the identity are in two consecutive paragraphs of the block (html #S3.SS1.p4.1 L1700 and #S3.SS1.p4.2 L1708). The identity holds because, conditionally on $K$, $K\cap\mathcal{G}=\emptyset$ has probability $(e^{-h})^{|K|}$. DOMAIN CONDITION that a formalisation must keep: the ghost field must be independent of the percolation configuration and defined on the SAME vertex set, otherwise the two-sided comparison (I.3.5) is not meaningful. USED BY: (I.3.1), (I.3.5) and both proofs of this section. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.eq.i.3.1
KIND: display
TITLE: (I.3.1) one-sided cut-off versus full ghost-field comparison
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p4@L1699-L1753
PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4@L1699-L1753
CONTRACT_ID: hutchcroft.eq.i.3.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ghost field of intensity $h>0$; cut-off radius $r>0$; a constant $C$ and the normalisation of the kernel; the monotone coupling of the cut-off and full configurations.
SOURCE_QUANTIFIERS: Every $r,h>0$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})\leq\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})+Cr^{-\alpha}\mathbb{E}_{\beta_c,r}[|K|e^{-h|K|}]\,\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})$.
CONSTANT_SCOPE: $C>0$ is a model constant; the factor $r^{-\alpha}$ is the order of the expected number of edges of the origin that flip from closed to open between $\mathbb{P}_{\beta_c,r}$ and $\mathbb{P}_{\beta_c}$, and is not derived from any earlier display.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.ghost
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4@L1699-L1753 Canonical paper-tex.txt L685; the display is html table id=S3.E1 at paper.html L1709. THIS IS THE WEAKEST LINK OF THE SECTION AND IS A GENUINE SOURCE GAP: the display is derived, never proved. The printed derivation is a union bound over edges of the boundary of the cut-off cluster that flip open, together with the assertion that "exploring the cluster of the origin in the cut-off model reveals only negative information about connectivity to the ghost off of this cluster"; the factor $r^{-\alpha}$ uses the kernel normalisation through $\sum_{y\notin B_r}J(x,y)\asymp r^{-\alpha}$, which the source nowhere derives in this section; and [78, Section 5.2] is cited only for the hierarchical model. Recorded as a derived display with a gap, not as a cited theorem. DO NOT read it as an equality: it is a one-sided bound with a self-referential final factor. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS1.p4@L1699-L1753 | packet relation requires: the ghost field, the two joint laws and the identity $\mathbb{P}_{r,h}(0\leftrightarrow\mathcal{G})=\mathbb{E}_r[1-e^{-h∣K∣}]$ are used verbatim in the comparison

NODE: hutchcroft.i.3.1
KIND: proposition
TITLE: Up-to-constants volume-tail asymptotics from moment asymptotics
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm1@L1643-L1674
PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.2@L1678-L1754
CONTRACT_ID: hutchcroft.i.3.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $\mathbb{E}_{\beta_c,r}|K|\asymp r^{\alpha}$ as $r\to\infty$, and $f:(0,\infty)\to(0,\infty)$ increasing with $f^{-1}$ doubling. Item 1: there are $c,C>0$ with $\hat{\mathbb{P}}_{\beta_c,r}(cf(r)\leq|K|\leq Cf(r))\geq c$ for every $r\geq1$. Item 2: for every $\varepsilon>0$ there is $\delta>0$ with $\hat{\mathbb{P}}_{\beta_c,r}(|K|\leq\delta f(r))\leq\varepsilon$ for every $r\geq1$.
SOURCE_QUANTIFIERS: Every $r\geq1$ and $n\geq1$; the two-sided asymptotics are as $r\to\infty$ and $n\to\infty$.
SOURCE_CONCLUSION: Item 1: $\mathbb{P}_{\beta_c}(|K|\geq n)\succeq f^{-1}(n)^{\alpha}/n$. Item 2: $\mathbb{P}_{\beta_c}(|K|\geq n)\preceq f^{-1}(n)^{\alpha}/n$.
CONSTANT_SCOPE: Constants depend on $c,C,\alpha$ and on the two constants inside $\mathbb{E}_{\beta_c,r}|K|\asymp r^{\alpha}$; uniformly in $r,n$ otherwise.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.sizebiased,hutchcroft.def.ghost,hutchcroft.eq.i.3.1,hutchcroft.i.1.beta_c.bilat
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.2@L1678-L1754 canonical paper-tex.txt L649-L665 (statement), L667-L703 (proof). Proof checked. Two local slips in the printed proof of item 2, neither affecting the conclusion: (a) at canonical L695 the condition reads "when $r\geq f^{-1}(h/\delta)$" but the argument at L693 sets $r=f^{-1}(1/\delta h)$ and the equivalent form of $h\geq1/(\delta f(r))$ is $r\geq f^{-1}(1/(\delta h))$, so the printed argument is inverted; (b) at canonical L701 the left side is printed $\mathbb{P}_{\beta_c}(|K|\geq m)$ while the right side uses $n$, so the two letters disagree. The sufficient condition stated at canonical L665 in the body ("$\hat{\mathbb{E}}_r|K|\asymp f(r)$ and the laws $Q_r$ are tight in $(0,\infty)$") is correct and implies both items: tightness gives item 2 with $\delta$ from the compact set, and combined with $\hat{\mathbb{E}}_r|K|\asymp f(r)$ and $\int x\,dQ_r=1$ it gives item 1. Not merged: item 1 and item 2 are two separate conclusions of one statement and must not be cited as one. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.Thmthm1@L1643-L1674 | packet relation requires: both hypotheses and both conclusions are stated in the size-biased measure $\hat{\mathbb{P}}_{\beta_c,r}$
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS1.p4@L1699-L1753 | packet relation requires: only the proof of item 2 uses the ghost field, and it is the sole route to the upper bound
EDGE: hutchcroft.eq.i.3.1 | .scratch/source/paper.html#S3.SS1.p4@L1699-L1753 | packet relation requires: item 2 is obtained by inserting the ghost-field comparison (I.3.1) and then making its last factor harmless
EDGE: hutchcroft.i.1.beta_c.bilat | .scratch/source/paper.html#S3.Thmthm1@L1643-L1674 | packet relation requires: $\mathbb{P}_{\beta_c}$ and $\mathbb{P}_{\beta_c,r}$ must be non-degenerate; $0<\beta_c<\infty$ is a derived result of this packet, cited here as such

NODE: hutchcroft.i.3.1:step-lower
KIND: step
TITLE: Item 1: monotone cut-off, size biasing and the truncation to $[cf,Cf]$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p3.1@L1681-L1681
PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p3@L1680-L1698
CONTRACT_ID: hutchcroft.i.3.1:step-lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Proposition I.3.1 item 1; the cut-off kernel is dominated by the original kernel, so $\mathbb{P}_{\beta_c}\geq\mathbb{P}_{\beta_c,r}$ on increasing events.
SOURCE_QUANTIFIERS: Every $r\geq1$; then $n$ is recovered as $n=cf(r)$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(|K|\geq n)\geq\mathbb{P}_{\beta_c,r}(|K|\geq n)=\mathbb{E}_{\beta_c,r}|K|\,\hat{\mathbb{E}}_{\beta_c,r}[\mathbb{1}(|K|\geq n)/|K|]$; with $n=cf(r)$ and the truncation to $[cf(r),Cf(r)]$ this is $\asymp r^{\alpha}/f(r)$, and $r=f^{-1}(n/c)\asymp f^{-1}(n)$ is used.
CONSTANT_SCOPE: $\succeq$ constant from $c,C$ and from $\mathbb{E}_{\beta_c,r}|K|\asymp r^{\alpha}$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.sizebiased,hutchcroft.def.doubling
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p3@L1680-L1698 canonical paper-tex.txt L669-L677. Reconstructed from the displayed proof. Uses $\mathbb{1}(|K|\geq cf(r))\geq\mathbb{1}(cf(r)\leq|K|\leq Cf(r))$ and $1/|K|\geq1/(Cf(r))$ on that event; the final "$r=f^{-1}(n/c)$ is of the same order as $f^{-1}(n)$" is exactly where doubling of $f^{-1}$ enters. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.SS1.p3.1@L1681-L1681 | packet relation requires: the identity $\mathbb{P}_{\beta_c,r}(∣K∣\geq n)=\mathbb{E}_{\beta_c,r}∣K∣\,\hat{\mathbb{E}}[\mathbb{1}(∣K∣\geq n)/∣K∣]$ is the Radon-Nikodym derivative written out
EDGE: hutchcroft.def.doubling | .scratch/source/paper.html#S3.SS1.p3.3@L1697-L1697 | packet relation requires: doubling of $f^{-1}$ is what converts $f^{-1}(n/c)$ into a constant multiple of $f^{-1}(n)$

NODE: hutchcroft.i.3.1:step-ghost
KIND: step
TITLE: Item 2: make the ghost-field correction smaller than one half
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p4.3@L1717-L1718
PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4.4@L1726-L1727
CONTRACT_ID: hutchcroft.i.3.1:step-ghost
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in Proposition I.3.1 item 2, with $\delta>0$ supplied by that hypothesis; $r\geq1$ and $h\geq1/(\delta f(r))$.
SOURCE_QUANTIFIERS: Every $r\geq1$ and every $h>0$ satisfying $h\geq1/(\delta f(r))$.
SOURCE_CONCLUSION: $Cr^{-\alpha}\mathbb{E}_{\beta_c,r}[|K|e^{-h|K|}]=Cr^{-\alpha}\mathbb{E}_{\beta_c,r}|K|\,\hat{\mathbb{E}}_{\beta_c,r}[e^{-h|K|}]\leq\frac12$, hence $\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})\leq2\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})$.
CONSTANT_SCOPE: $C$ from (I.3.1); the threshold $\delta$ from item 2; the factor $2$ is $(1-1/2)^{-1}$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.eq.i.3.1,hutchcroft.def.ghost,hutchcroft.def.sizebiased,hutchcroft.def.doubling
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4.4@L1726-L1727 canonical paper-tex.txt L689-L697 and the two-sided consequence at L700. Reconstructed; the source displays the $\leq1/2$ inequality and states the smallness of $\hat{\mathbb{E}}[e^{-h|K|}]$ in words only. The precise split needed is $\hat{\mathbb{E}}[e^{-h|K|}]\leq\varepsilon+e^{-h\delta f(r)}\leq\varepsilon+e^{-1}$ for $h\geq1/(\delta f(r))$ with $\varepsilon$ chosen small, which is where item 2 is used with the SAME $\delta$. The passage from the printed condition "$r\geq f^{-1}(h/\delta)$" to the correct "$r\geq f^{-1}(1/(\delta h))$" is the slip recorded on the parent; the step is stated with the corrected condition. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.eq.i.3.1 | .scratch/source/paper.html#S3.SS1.p4.3@L1717-L1718 | packet relation requires: the correction term $Cr^{-\alpha}\mathbb{E}[∣K∣e^{-h∣K∣}]$ is exactly the final factor of (I.3.1)
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS1.p4.3@L1717-L1718 | packet relation requires: the identity $\mathbb{E}_r[∣K∣e^{-h∣K∣}]=\mathbb{E}_r∣K∣\,\hat{\mathbb{E}}_r[e^{-h∣K∣}]$ and the joint law $\mathbb{P}_{\beta_c,\infty,h}$ are those of the ghost-field definition
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.SS1.p4.3@L1717-L1718 | packet relation requires: the size-biased expectation $\hat{\mathbb{E}}_r[e^{-h∣K∣}]$ is the object that the hypothesis of item 2 controls
EDGE: hutchcroft.def.doubling | .scratch/source/paper.html#S3.SS1.p4.5@L1735-L1735 | packet relation requires: doubling of $f^{-1}$ is used to replace $f^{-1}(1/(\delta h))$ by a constant multiple of $f^{-1}(1/h)$ at fixed $\delta$

NODE: hutchcroft.i.3.1:step-h-n
KIND: step
TITLE: Item 2: take $h=1/n$ and divide by the conditional ghost probability
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS1.p4.6@L1743-L1743
PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4.7@L1751-L1752
CONTRACT_ID: hutchcroft.i.3.1:step-h-n
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ghost field of intensity $h=1/n$; $n\geq1$.
SOURCE_QUANTIFIERS: Every $n\geq1$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(|K|\geq n)=\mathbb{P}_{\beta_c,\infty,1/n}(|K|\geq n\text{ and }K\cap\mathcal{G}\neq\emptyset)/\mathbb{P}_{\beta_c,\infty,1/n}(K\cap\mathcal{G}\neq\emptyset\mid|K|\geq n)\leq\mathbb{P}_{\beta_c,\infty,1/n}(K\cap\mathcal{G}\neq\emptyset)/(1-e^{-1})\preceq f^{-1}(n)^{\alpha}/n$.
CONSTANT_SCOPE: The factor $1/(1-e^{-1})$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.1:step-ghost,hutchcroft.def.ghost
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS1.p4.7@L1751-L1752 canonical paper-tex.txt L699-L703. Reconstructed. The denominator bound is the point: conditionally on $|K|\geq n$ and $h=1/n$, $\mathbb{P}(K\cap\mathcal{G}\neq\emptyset\mid K)\geq1-(e^{-1/n})^{n}=1-e^{-1}$. The identity in the middle is an exact Bayes-type factorisation, so no independence between the two events is being assumed. The printed letter slip "$|K|\geq m$" versus "$|K|\geq n$" is recorded on the parent. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.3.1:step-ghost | .scratch/source/paper.html#S3.SS1.p4.6@L1743-L1743 | packet relation requires: the two-sided comparison is used with $h=1/n$ to bound the full-law probability
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS1.p4.6@L1743-L1743 | packet relation requires: the event $K\cap\mathcal{G}\neq\emptyset$ and its conditional probability are the ghost-field objects

NODE: hutchcroft.eq.i.3.2
KIND: display
TITLE: (I.3.2) Laplace-transform asymptotics of the cluster volume
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm2@L1762-L1813
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.eq.i.3.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1)-(4) of Proposition I.3.2, together with the existence of the limit defining $A_3$ (see hutchcroft.i.3.2:step-a3-limit).
SOURCE_QUANTIFIERS: $h\downarrow0$.
SOURCE_CONCLUSION: $\mathbb{E}_{\beta_c}[1-e^{-h|K|}]\sim A_3f^{-1}(1/h)^{\alpha}h$.
CONSTANT_SCOPE: $A_3=\frac{A_1}{A_2^{1/a}}\lim_{\lambda\to\infty}\lambda^{-(a-1)/a}\int_0^\infty\frac{1-e^{-\lambda x}}{x}\,dQ_\infty(x)$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-mgf
ROUTES: -
ROUTE_FOR: -
NOTE: Canonical paper-tex.txt L723; the display is html tbody id=S3.E2 at paper.html L1787, inside block #S3.Thmthm2. Containment only: this is the first conclusion of Proposition I.3.2, recorded separately because the Tauberian step consumes it as an input. Its proof is the designated producer step inside Proposition I.3.2's actual proof block, not an independent statement/proof pair. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. PRODUCER LINK: this display is produced by hutchcroft.i.3.2:step-mgf (now a DEPS edge) inside the proof block `#S3.SS2.2@L1838-L1911`; it is not a printed assertion with a proof of its own.
EDGE: hutchcroft.i.3.2:step-mgf | .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899 | display (I.3.2) is produced by the matched-scale computation, not asserted independently

NODE: hutchcroft.eq.i.3.3
KIND: display
TITLE: (I.3.3) volume-tail asymptotics of the cluster volume
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm2@L1762-L1813
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.eq.i.3.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1)-(4) of Proposition I.3.2 together with the limit defining $A_3$, or equivalently (I.3.2) plus $0\leq1-1/a<1$.
SOURCE_QUANTIFIERS: $n\to\infty$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(|K|\geq n)\sim A_4f^{-1}(n)^{\alpha}/n$ with $A_4=A_3/\Gamma(1/a)$.
CONSTANT_SCOPE: $A_4=A_3/\Gamma(1/a)$; at $a=2$ this is $A_4=A_3/\sqrt{\pi}$ since $\Gamma(1/2)=\sqrt{\pi}$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-tauberian
ROUTES: -
ROUTE_FOR: -
NOTE: Canonical paper-tex.txt L725; the display is html tbody id=S3.E3 at paper.html L1795, and the constants $A_3,A_4$ are displayed at paper.html L1804 (canonical L729). Containment only. This is the half that the two frozen roots need (see hutchcroft.i.3.tail). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. PRODUCER LINK: this display is produced by hutchcroft.i.3.2:step-tauberian (now a DEPS edge) inside the proof block `#S3.SS2.2@L1838-L1911`; it is not a printed assertion with a proof of its own.
EDGE: hutchcroft.i.3.2:step-tauberian | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | display (I.3.3) is produced by the Tauberian passage, not asserted independently

NODE: hutchcroft.i.3.2:step-a3-limit
KIND: step
TITLE: OPEN OBLIGATION: the limit defining $A_3$ is well defined, finite and positive
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm2@L1762-L1815
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.i.3.2:step-a3-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1)-(4) of Proposition I.3.2: $Q_r\Rightarrow Q_\infty$ and $Q_\infty$ has no atom at $0$; $a\geq1$ as derived in hutchcroft.i.3.2:step-a-at-least-1; $A_1,A_2\in(0,\infty)$.
SOURCE_QUANTIFIERS: $\lambda\to\infty$ along the reals.
SOURCE_CONCLUSION: $\lim_{\lambda\to\infty}\lambda^{-(a-1)/a}\int_0^\infty\frac{1-e^{-\lambda x}}{x}\,dQ_\infty(x)$ exists and lies in $(0,\infty)$.
CONSTANT_SCOPE: The limit is a single finite positive number independent of $\lambda$; it enters only through $A_3$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-a-at-least-1
ROUTES: -
ROUTE_FOR: -
NOTE: PROOF/RECONSTRUCTION OBLIGATION AT: .scratch/source/paper.html#S3.SS2.2@L1838-L1911 SOURCE_GAP, OPEN OBLIGATION, NOT A DISCHARGE AND NOT AN ASSUMPTION. The limit whose value $A_3$ quotes must be established to be well defined, finite and positive; the paper asserts this at canonical L731 ("It is an implicit conclusion of the proposition that the $\lambda\to\infty$ limit taken in the definition of $A_3$ is well-defined") and proves nothing. Hypotheses (1)-(4) do not imply it: at $a=1$ the expression equals $\int_0^\infty x^{-1}dQ_\infty(x)$ for every $\lambda$ and is finite only if $x^{-1}$ is $Q_\infty$-integrable; for $a>1$ the growth rate is not pinned, and $a=3$ with $Q_\infty=\chi^2_1$ gives $\sqrt{2\lambda+1}-1$, hence $\sqrt2\,\lambda^{-1/6}\to0$ and $A_3=0$. DISCHARGED ONLY AT THE TWO INTENDED USES: $a=2$ with $Q_\infty=\chi^2_1$ gives the exact value $\sqrt2$ (canonical L795, computed independently in hutchcroft.i.3.tail:step-integrals), so in the applications of Theorem I.1.6 and Theorem I.1.15 the obligation is met with an explicit constant. This record exists so that a formalisation must PROVE it rather than inherit it; it must not be reclassified as an assumption and it must not be counted as evidence. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. SELF-CITATION CORRECTION: STATEMENT_SOURCE and PROOF_SOURCE were both `#S3.Thmthm2@L1762-L1813`, i.e. this step cited the proposition it decomposes as its own proof. The statement field now names the source region of the object and the proof field names the proof block. The SOURCE_GAP is unchanged and is not repaired by this move: the `A_3` limit is defined in the statement's constants paragraph (L1804-L1813) and called an 'implicit conclusion' at L1815; the proof block is where the lambda -> infinity passage is taken; the obligation stays OPEN.
EDGE: hutchcroft.i.3.2:step-a-at-least-1 | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | packet relation requires: for $a<1$ the expression diverges, so the obligation can only be stated after $a\geq1$ is derived

NODE: hutchcroft.i.3.2
KIND: proposition
TITLE: First-order volume-tail asymptotics from moment asymptotics
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm2@L1762-L1813
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.i.3.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (1) $\mathbb{E}_{\beta_c,r}|K|\sim A_1r^{\alpha}$ with $A_1\in(0,\infty)$; (2) $\hat{\mathbb{E}}_{\beta_c,r}|K|=\mathbb{E}_{\beta_c,r}|K|^{2}/\mathbb{E}_{\beta_c,r}|K|\sim A_2f(r)$ with $f$ regularly varying of index $a\alpha$ for some $a>0$ and $A_2\in(0,\infty)$; (3) $Q_r$, the law of $|K|/\hat{\mathbb{E}}_{\beta_c,r}|K|$ under $\hat{\mathbb{P}}_{\beta_c,r}$, converges weakly to $Q_\infty$; (4) $Q_\infty$ has no atom at $0$.
SOURCE_QUANTIFIERS: $r\to\infty$, then $h\downarrow0$ and $n\to\infty$; $A_1,A_2,a,\alpha$ are fixed.
SOURCE_CONCLUSION: (I.3.2) $\mathbb{E}_{\beta_c}[1-e^{-h|K|}]\sim A_3f^{-1}(1/h)^{\alpha}h$; (I.3.3) $\mathbb{P}_{\beta_c}(|K|\geq n)\sim A_4f^{-1}(n)^{\alpha}/n$; with $A_3,A_4$ as displayed.
CONSTANT_SCOPE: $A_3,A_4$ are functions of $A_1,A_2,a$ and of $Q_\infty$ only; no $r$- or $h$-dependent constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-a3-limit,hutchcroft.i.3.2:step-a-at-least-1,hutchcroft.def.sizebiased,hutchcroft.def.ghost,hutchcroft.eq.i.3.5,hutchcroft.i.3.2:step-mgf,hutchcroft.i.3.2:step-qlimit,hutchcroft.i.3.2:step-two-sided,hutchcroft.i.3.2:step-tauberian,hutchcroft.eq.i.3.2,hutchcroft.eq.i.3.3,hutchcroft.i.1.2.betac.pos,hutchcroft.i.1.2.betac.fin
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911 canonical paper-tex.txt L709-L731 (statement), L745-L776 (proof). THREE DEFECTS, all substantive and none repaired by weakening the statement. (a) HYPOTHESIS (2) PRINTS "$a>0$"; the correct domain is $a\geq1$. It is DERIVED, not assumed: $\hat{\mathbb{E}}_r|K|\geq\mathbb{E}_r|K|$ because $\mathbb{E}X^{2}\geq(\mathbb{E}X)^{2}$, so $A_2f(r)\geq(A_1/2)r^{\alpha}$ eventually, i.e. $f(r)/r^{\alpha}$ is bounded below, and that ratio is regularly varying of index $(a-1)\alpha$, so $(a-1)\alpha\geq0$; see hutchcroft.i.3.2:step-a-at-least-1. The same condition is forced twice more: Theorem I.2.11 needs its index in $(-1,0]$, here $1/a-1$, and the $A_3$ limit is $+\infty$ for $a<1$. (b) The existence and positivity of the $A_3$ limit is ASSERTED at canonical L731 ("an implicit conclusion") and is not implied by (1)-(4); it is recorded as hutchcroft.i.3.2:step-a3-limit and is discharged only in the two applications, where the constant is computed. (c) The passage $Q_r\to Q_\infty$ under the integral $\int(1-e^{-\lambda x})/x\,dQ_r(x)$ is asserted without justification; it needs truncation at $x<\delta$ plus tightness on $(0,\infty)$, which (3)+(4) do give, but the argument is not printed. NO DEFECT in the algebra: with $r=f^{-1}(\lambda/A_2h)$ one has $h\hat{\mathbb{E}}_r|K|\to\lambda$, and $f^{-1}$ being regularly varying of index $1/(a\alpha)$ turns $r^{\alpha}$ into $\lambda^{1/a}A_2^{-1/a}f^{-1}(1/h)^{\alpha}$, reproducing (I.3.7) exactly. Cross-slice: the d=3$\alpha$ application needs $A_r$ slowly varying in $\hat{\mathbb{E}}_r|K|\sim A_rr^{2\alpha}$, which is part of the frozen root hutchcroft.i.1.15 and not of this slice. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. STEP-MAP CORRECTION (measured: all four proof steps and both conclusion displays had zero consumers and were outside every root closure). Printed order: (I.3.5) `hutchcroft.eq.i.3.5` -> choose lambda_0,h_0 giving (I.3.6) `hutchcroft.i.3.2:step-two-sided` -> damped first moment with Q_infinity `hutchcroft.i.3.2:step-qlimit` -> matched-scale computation giving (I.3.7) `hutchcroft.i.3.2:step-mgf` -> (I.3.2) `hutchcroft.eq.i.3.2` -> Tauberian `hutchcroft.i.3.2:step-tauberian` -> (I.3.3) `hutchcroft.eq.i.3.3`. This record now names its own chain; the two open obligations (`step-a3-limit`, `step-a-at-least-1`) stay open and stay on the chain. No step is promoted and no printed hypothesis is added.
EDGE: hutchcroft.i.3.2:step-a3-limit | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | packet relation requires: $A_3$ is a printed constant of the conclusion and the well-definedness, finiteness and positivity of its defining limit is precisely the named obligation
EDGE: hutchcroft.i.3.2:step-a-at-least-1 | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | packet relation requires: hypothesis (2) prints $a>0$, but the statement is false for $a<1$; the bridge step supplies the required $a\geq1$
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | packet relation requires: $\hat{\mathbb{E}}_{\beta_c,r}∣K∣$ and the laws $Q_r$ in hypotheses (2) and (3) are defined through the size-biased measure
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS2.2@L1838-L1911 | packet relation requires: the proof turns both sides into ghost-field connection probabilities
EDGE: hutchcroft.eq.i.3.5 | .scratch/source/paper.html#S3.SS2.p3.2@L1850-L1850 | packet relation requires: the two-sided cut-off comparison is the estimate the proof applies at $r=f^{-1}(\lambda/A_2h)$
EDGE: hutchcroft.i.3.2:step-mgf | .scratch/source/paper.html#S3.SS2.p3.6@L1879-L1880 | (I.3.7) is computed here; without it the proposition's first conclusion has no assembly
EDGE: hutchcroft.i.3.2:step-qlimit | .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870 | the Q_r -> Q_infinity replacement inside the damped first moment
EDGE: hutchcroft.i.3.2:step-two-sided | .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870 | (I.3.6) is produced here and is what lets (I.3.7) be compared with the uncut field
EDGE: hutchcroft.i.3.2:step-tauberian | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | the Tauberian passage (I.3.2) -> (I.3.3) is the second printed conclusion
EDGE: hutchcroft.eq.i.3.2 | .scratch/source/paper.html#S3.Thmthm2@L1784-L1793 | the proposition asserts display (I.3.2) as conclusion 1
EDGE: hutchcroft.eq.i.3.3 | .scratch/source/paper.html#S3.Thmthm2@L1793-L1801 | the proposition asserts display (I.3.3) as conclusion 2
EDGE: hutchcroft.i.1.2.betac.pos | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | positive critical parameter supplied by the small-β first-moment walk bound; supplied at the proposition's hypothesis (1), not via its proof paragraph or the withdrawn nearest-line reconstruction
EDGE: hutchcroft.i.1.2.betac.fin | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | finite critical parameter from the square-lattice route at d≥2 and the separately tracked α≤1 one-dimensional regime; supplied at the proposition's hypothesis (1), not via its proof paragraph or the withdrawn nearest-line reconstruction

NODE: hutchcroft.i.3.2:step-a-at-least-1
KIND: step
TITLE: Bridge condition: hypotheses (1) and (2) force $a\geq1$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.I2.i2@L1771-L1773
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.i.3.2:step-a-at-least-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1) and (2) of Proposition I.3.2: $\mathbb{E}_{\beta_c,r}|K|\sim A_1r^{\alpha}$ and $\hat{\mathbb{E}}_{\beta_c,r}|K|\sim A_2f(r)$ with $f$ regularly varying of index $a\alpha$; $A_1,A_2\in(0,\infty)$; $\alpha>0$.
SOURCE_QUANTIFIERS: All sufficiently large $r$; the conclusion is about the fixed parameter $a$.
SOURCE_CONCLUSION: $a\geq1$.
CONSTANT_SCOPE: No constant; only the sign of $(a-1)\alpha$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.I32Endpoint.one_le_of_normalized_moment_asymptotics
LEAN_NOTE: Moment-asymptotics endpoint only: no A3 convergence/positivity, ghost-restoration comparison, Tauberian argument or root proof is supplied.
DEPS: hutchcroft.def.rv
ROUTES: -
ROUTE_FOR: -
NOTE: PROOF/RECONSTRUCTION OBLIGATION AT: .scratch/source/paper.html#S3.SS2.2@L1838-L1911 NOT PRINTED IN THE SOURCE. This is the missing bridge between hypotheses (1)-(2) and both downstream uses of $a$, and it is a derivation, not a new hypothesis. Proof: since $\mathbb{E}X^{2}\geq(\mathbb{E}X)^{2}$ for $X=|K|\geq0$ one has $\hat{\mathbb{E}}_{\beta_c,r}|K|=\mathbb{E}_r|K|^{2}/\mathbb{E}_r|K|\geq\mathbb{E}_r|K|$; combining (1) and (2) gives $A_2f(r)\geq(1-o(1))A_1r^{\alpha}$, hence $g(r):=f(r)/r^{\alpha}\geq A_1/(2A_2)>0$ for all large $r$. The function $g$ is regularly varying of index $(a-1)\alpha$. If $(a-1)\alpha<0$ then $g(r)=r^{(a-1)\alpha}\ell(r)$ with $\ell$ slowly varying, and $\ell$ is bounded on $[R,\infty)$ by the uniform convergence theorem, so $g(r)\to0$, contradicting the eventual lower bound. Hence $(a-1)\alpha\geq0$ and, since $\alpha>0$, $a\geq1$. TWO CONSUMERS, both of which fail at $a<1$: hutchcroft.i.3.2:step-tauberian, where Theorem I.2.11 requires the exponent $\alpha\prime=1-1/a$ to satisfy $0\leq\alpha\prime<1$; and hutchcroft.i.3.2:step-a3-limit, where the $A_3$ limit is $+\infty$ for $a<1$ because the integral is non-decreasing and positive while $\lambda^{-(a-1)/a}\to\infty$. The two intended applications have $a=2$ exactly, so nothing is lost there; the point is that the printed "$a>0$" invites a formalisation to carry an impossible case. The two regularly varying facts used (negative index tends to $0$; a slowly varying function is eventually bounded) are standard consequences of the uniform convergence theorem quoted in hutchcroft.def.rv, and are NOT separately printed in the paper. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. SELF-CITATION CORRECTION: STATEMENT_SOURCE and PROOF_SOURCE were both `#S3.Thmthm2@L1762-L1813`, i.e. this step cited the proposition it decomposes as its own proof. The statement field now names the source region of the object and the proof field names the proof block. The SOURCE_GAP is unchanged and is not repaired by this move: hypothesis 2 is where the printed `a > 0` lives; the index is used in the proof block; the obligation stays OPEN. VERIFIED ENDPOINT: `NormalizedAEndpoint.one_le_of_normalized_moment_asymptotics` compiles with warnings as errors at `da6ebd79305031f0b78b44cd0140d45970f273c1`, with standard axioms only. The second source asymptotic is normalized by the proved `(φ/f)/A₂ = φ/(A₂·f)` rewriting, and `mean_le_sbMean` supplies Jensenʼs comparison on `[0,∞), giving a ≥ 1 without Tauberian/ghost inputs. The source-domain probability laws, integrable first/second moments and positive means are retained exactly as premises; they are not supplied by the cutoff moment argument.
EDGE: hutchcroft.def.rv | .scratch/source/paper.html#S3.Thmthm2@L1762-L1813 | packet relation requires: the argument uses that $g$ is regularly varying of index $(a-1)\alpha$ and that a regularly varying function of negative index tends to zero

NODE: hutchcroft.eq.i.3.5
KIND: display
TITLE: (I.3.5) two-sided cut-off versus full ghost-field comparison
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910
CONTRACT_ID: hutchcroft.eq.i.3.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ghost field of intensity $h>0$; cut-off radius $r>0$; the constant $C$ of (I.3.1).
SOURCE_QUANTIFIERS: Every $r,h>0$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})\leq\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})\leq\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})+Cr^{-\alpha}\mathbb{E}_{\beta_c,r}[|K|e^{-h|K|}]\,\mathbb{P}_{r,h}(0\leftrightarrow\mathcal{G})$.
CONSTANT_SCOPE: The same $C>0$ as in (I.3.1); no new constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.eq.i.3.1,hutchcroft.def.ghost
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910 Canonical paper-tex.txt L753; the display is html table id=S3.E5 at paper.html L1851. Derived, not proved: the left inequality is monotonicity in the edge set under the monotone coupling, the right one is (I.3.1). NOTATIONAL SLIP, confirmed: the final factor is printed $\mathbb{P}_{r,h}(0\leftrightarrow\mathcal{G})$, whereas (I.3.1) has $\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})$; the proof only needs that factor to be at most $1$ together with $Cr^{-\alpha}\mathbb{E}[|K|e^{-h|K|}]\leq\varepsilon$, so either reading works, but a formalisation must fix one and this packet records the printed form. The whole estimate inherits the gap of (I.3.1). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.eq.i.3.1 | .scratch/source/paper.html#S3.SS2.p3.2@L1850-L1850 | packet relation requires: the right-hand inequality is (I.3.1) verbatim, and the left-hand one is the monotone coupling already used there
EDGE: hutchcroft.def.ghost | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: both sides are ghost-field connection probabilities under the two cut-off laws

NODE: hutchcroft.i.3.2:step-two-sided
KIND: step
TITLE: Choose $\lambda$ and $h_0$ so the correction is at most $\varepsilon$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870
CONTRACT_ID: hutchcroft.i.3.2:step-two-sided
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in the proof of Proposition I.3.2; $r=f^{-1}(\lambda/A_2h)$; hypothesis (4).
SOURCE_QUANTIFIERS: Every $\lambda\geq\lambda_0$ and $h\leq h_0$, with $\lambda_0<\infty$ and $h_0>0$ produced by the argument.
SOURCE_CONCLUSION: For every $\varepsilon>0$ there are $\lambda_0<\infty$ and $h_0>0$ such that $Cr^{-\alpha}\mathbb{E}_{\beta_c,r}[|K|e^{-h|K|}]\leq\varepsilon$, hence $1\leq\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})/\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})\leq(1-\varepsilon)^{-1}$; this is (I.3.6).
CONSTANT_SCOPE: $\varepsilon$, $\lambda_0$, $h_0$, and $C$ from (I.3.5).
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.eq.i.3.5
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870 canonical paper-tex.txt L760-L762. Reconstructed; the source displays (I.3.5) and (I.3.6) and states the existence of $\lambda_0,h_0$ in words. The limit $\int e^{-\lambda x}dQ_\infty(x)\to0$ as $\lambda\to\infty$ is exactly where hypothesis (4) is used: $Q_\infty(\{0\})=0$ gives $e^{-\lambda x}\to0$ $Q_\infty$-almost everywhere and dominated convergence applies. No uniformity in $\lambda$ is claimed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.eq.i.3.5 | .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870 | packet relation requires: the two-sided inequality is instantiated once the correction term is below $\varepsilon$

NODE: hutchcroft.i.3.2:step-qlimit
KIND: step
TITLE: Replace $Q_r$ by $Q_\infty$ in the exponentially damped first moment
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910
CONTRACT_ID: hutchcroft.i.3.2:step-qlimit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1)-(4); $r=f^{-1}(\lambda/A_2h)$ with $\lambda$ fixed and $h\downarrow0$.
SOURCE_QUANTIFIERS: Fixed $\lambda>0$; $h\downarrow0$.
SOURCE_CONCLUSION: $\mathbb{E}_{\beta_c,r}[|K|e^{-h|K|}]=\mathbb{E}_{\beta_c,r}|K|\int_0^\infty e^{-(h\hat{\mathbb{E}}_{\beta_c,r}|K|)x}dQ_r(x)\sim A_1r^{\alpha}\int_0^\infty e^{-\lambda x}dQ_\infty(x)$.
CONSTANT_SCOPE: $A_1$ and $\lambda$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.sizebiased
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910 canonical paper-tex.txt L764-L770. Reconstructed; the source displays the computation and invokes weak convergence with no uniformity discussion. The step is legitimate because $h\hat{\mathbb{E}}_{\beta_c,r}|K|\to\lambda$ exactly by the choice of $r$, and $e^{-\lambda x}$ is bounded and continuous, so weak convergence suffices. SOURCE GAP (minor, recorded on the parent): the passage inside the integral is asserted rather than argued. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.SS2.p3.5@L1870-L1870 | packet relation requires: the identity $\mathbb{E}_r[∣K∣e^{-h∣K∣}]=\mathbb{E}_r∣K∣\hat{\mathbb{E}}_r[e^{-h∣K∣}]$ and the law $Q_r$ are the size-biased objects

NODE: hutchcroft.i.3.2:step-mgf
KIND: step
TITLE: Compute the cut-off ghost probability at $r=f^{-1}(\lambda/A_2h)$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3.6@L1879-L1880
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899
CONTRACT_ID: hutchcroft.i.3.2:step-mgf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hypotheses (1)-(4); $f$ regularly varying of index $a\alpha$, so $f^{-1}$ is regularly varying of index $1/(a\alpha)$; $r=f^{-1}(\lambda/A_2h)$.
SOURCE_QUANTIFIERS: Fixed $\lambda>0$; $h\downarrow0$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})=\frac{\mathbb{E}_{\beta_c,r}|K|}{\hat{\mathbb{E}}_{\beta_c,r}|K|}\int_0^\infty\frac{1-\exp[-(h\hat{\mathbb{E}}_{\beta_c,r}|K|)x]}{x}dQ_r(x)\sim\frac{A_1}{A_2^{1/a}\lambda^{1-1/a}}\left[\int_0^\infty\frac{1-e^{-\lambda x}}{x}dQ_\infty(x)\right]f^{-1}(1/h)^{\alpha}h$, which is (I.3.7).
CONSTANT_SCOPE: $A_1,A_2,a$; the bracket is the $Q_\infty$-integral.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.sizebiased,ext.bgt.thm1.5.12,hutchcroft.i.3.2:step-qlimit
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899 canonical paper-tex.txt L772-L774. Reconstructed; the source displays the same chain and (I.3.7). The algebra was re-derived here and is correct: $r^{\alpha}=\lambda^{1/a}A_2^{-1/a}f^{-1}(1/h)^{\alpha}(1+o(1))$, and $\mathbb{E}_r|K|/\hat{\mathbb{E}}_r|K|=A_1r^{\alpha}h/\lambda$. The only external input is regular variation of the inverse, [24, Theorem 1.5.12]. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. CHAIN REPAIR: the record previously depended only on the size-biased definition and on [24, Thm 1.5.12], so the Q_r -> Q_infinity step it uses was invisible to the graph. It is now a DEP. The `A_3` limit is NOT a dependency of this step: the bracketed factor of (I.3.7) is written in terms of the limit, but the open well-definedness/finiteness/positivity obligation for that limit is a separate record (`hutchcroft.i.3.2:step-a3-limit`) consumed where the constant is actually asserted, not here.
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.SS2.p3.6@L1879-L1880 | packet relation requires: the factor $\mathbb{E}_r∣K∣/\hat{\mathbb{E}}_r∣K∣$ times the $Q_r$-integral is the size-biased representation of the same probability
EDGE: ext.bgt.thm1.5.12 | .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899 | packet relation requires: the step uses "$f^{-1}$ is regularly varying of index $1/(a\alpha)$", quoted from [24, Theorem 1.5.12]
EDGE: hutchcroft.i.3.2:step-qlimit | .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899 | the matched-scale computation uses the Q_r replacement of the previous step; it is not an independent derivation of the same limit

NODE: hutchcroft.eq.i.3.6
KIND: display
TITLE: (I.3.6) two-sided ratio bound for the ghost probabilities
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.eq.i.3.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in the proof of Proposition I.3.2: $r=f^{-1}(\lambda/A_2h)$, $\lambda\geq\lambda_0$, $h\leq h_0$.
SOURCE_QUANTIFIERS: $\lambda\geq\lambda_0$, $h\leq h_0$.
SOURCE_CONCLUSION: $1\leq\mathbb{P}_{\beta_c,\infty,h}(0\leftrightarrow\mathcal{G})/\mathbb{P}_{\beta_c,r,h}(0\leftrightarrow\mathcal{G})\leq(1-\varepsilon)^{-1}$.
CONSTANT_SCOPE: $\varepsilon$ from the smallness of $Cr^{-\alpha}\mathbb{E}[|K|e^{-h|K|}]$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Canonical paper-tex.txt L762; the display is html table id=S3.E6 at paper.html L1871. Produced inside the proof, not an input. Containment of the proof of Proposition I.3.2; it is a separate node because (I.3.7) alone does not give the full-law statement. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.eq.i.3.7
KIND: display
TITLE: (I.3.7) cut-off ghost probability at the matched scale
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3@L1840-L1910
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.2@L1838-L1911
CONTRACT_ID: hutchcroft.eq.i.3.7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: As in hutchcroft.i.3.2:step-mgf.
SOURCE_QUANTIFIERS: $h\downarrow0$ with $\lambda>0$ fixed and $r=f^{-1}(\lambda/A_2h)$.
SOURCE_CONCLUSION: $\mathbb{P}_{r,h}(0\leftrightarrow\mathcal{G})\sim\left[\frac{A_1}{A_2^{1/a}\lambda^{1-1/a}}\int_0^\infty\frac{1-e^{-\lambda x}}{x}dQ_\infty(x)\right]f^{-1}(1/h)^{\alpha}h$.
CONSTANT_SCOPE: $A_1,A_2,a$; the bracket is independent of $h$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-mgf
ROUTES: -
ROUTE_FOR: -
NOTE: Canonical paper-tex.txt L774; the display is html tbody id=S3.E7 at paper.html L1902. Produced inside the proof. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed. PRODUCER LINK: this display is produced by hutchcroft.i.3.2:step-mgf (now a DEPS edge) inside the proof block `#S3.SS2.2@L1838-L1911`; it is not a printed assertion with a proof of its own.
EDGE: hutchcroft.i.3.2:step-mgf | .scratch/source/paper.html#S3.SS2.p3.7@L1899-L1899 | display (I.3.7) is the matched-scale identity the step proves

NODE: hutchcroft.i.3.2:step-tauberian
KIND: step
TITLE: Tauberian passage from (I.3.2) to (I.3.3) at index $1-1/a$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842
CONTRACT_ID: hutchcroft.i.3.2:step-tauberian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I.3.2) holds with $A_3\in(0,\infty)$; $g(s):=A_3f^{-1}(s)^{\alpha}/s$ is regularly varying of index $-(1-1/a)$; $0\leq1-1/a<1$.
SOURCE_QUANTIFIERS: $s\to\infty$ with $h=1/s\downarrow0$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(|K|\geq n)\sim g(n)/\Gamma(1/a)=A_3f^{-1}(n)^{\alpha}/(n\Gamma(1/a))$, which is (I.3.3) with $A_4=A_3/\Gamma(1/a)$.
CONSTANT_SCOPE: The Gamma factor is $\Gamma(1-\alpha\prime)=\Gamma(1/a)$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.2.11,hutchcroft.eq.i.3.2,hutchcroft.def.rv,hutchcroft.i.3.2:step-a-at-least-1,hutchcroft.i.3.2:step-a3-limit
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 canonical paper-tex.txt L747. This is the step where $a\geq1$ is required, and the source says only "together with Karamata’s Tauberian theorem [47, Theorem XIII.5.2] as stated in Theorem I.2.11". The index bookkeeping, re-derived here: $f^{-1}$ has index $1/(a\alpha)$, so $f^{-1}(s)^{\alpha}$ has index $1/a$ and $g$ has index $1/a-1=-(1-1/a)$; Theorem I.2.11 requires the exponent $\alpha\prime=1-1/a$ to satisfy $0\leq\alpha\prime<1$, i.e. $a\geq1$, and then $\Gamma(1-\alpha\prime)=\Gamma(1/a)$. At $a=2$ this is $\Gamma(1/2)=\sqrt{\pi}$, matching the printed remark. The step inherits BOTH the $a\geq1$ condition (supplied by hutchcroft.i.3.2:step-a-at-least-1) and the finiteness of $A_3$ (supplied by hutchcroft.i.3.2:step-a3-limit). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.2.11 | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: the equivalence between the Laplace asymptotics and the tail asymptotics is exactly Karamatas Tauberian theorem as stated there
EDGE: hutchcroft.eq.i.3.2 | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: the Laplace-transform asymptotic with constant $A_3$ is the hypothesis fed into the Tauberian theorem
EDGE: hutchcroft.def.rv | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: the index computation $1/a-1$ uses regular variation of $f^{-1}$ and of $g$ in the sense defined there
EDGE: hutchcroft.i.3.2:step-a-at-least-1 | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: the Tauberian theorem only applies when $0\leq1-1/a<1$, which is precisely $a\geq1$
EDGE: hutchcroft.i.3.2:step-a3-limit | .scratch/source/paper.html#S3.SS2.p3.1@L1841-L1842 | packet relation requires: Karamata’s Tauberian theorem is applied to the asymptotic with the finite non-zero constant $A_3$, which is exactly the content of the open obligation

NODE: hutchcroft.i.3.4
KIND: claim
TITLE: Remark I.3.4: the volume tail at the size-biased mean scale
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm4@L1823-L1837
PROOF_SOURCE: .scratch/source/paper.html#S3.Thmthm4@L1823-L1837
CONTRACT_ID: hutchcroft.i.3.4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition I.3.2 and its proof, in particular the limit $Q_\infty$ and hypotheses (1)-(4); every $r\geq1$.
SOURCE_QUANTIFIERS: Every $r\geq1$; constants uniform in $r$.
SOURCE_CONCLUSION: (I.3.4) $\mathbb{P}_{\beta_c}(|K|\geq\hat{\mathbb{E}}_{\beta_c,r}|K|)\asymp\mathbb{P}_{\beta_c,r}(|K|\geq\hat{\mathbb{E}}_{\beta_c,r}|K|)\asymp r^{\alpha}/\hat{\mathbb{E}}_{\beta_c,r}|K|\asymp\mathbb{E}_{\beta_c,r}|K|/\hat{\mathbb{E}}_{\beta_c,r}|K|$.
CONSTANT_SCOPE: Two-sided constants uniform in $r\geq1$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.Thmthm4@L1823-L1837 canonical paper-tex.txt L737-L743; the display (I.3.4) is html table id=S3.E4 at paper.html L1827 and is carried by this record rather than by a separate display node. No proof is printed; the derivation is by reference to Proposition I.3.2 and its proof, so PROOF_SOURCE locates the remark itself. CHECKED: the middle comparison is the non-obvious one. Under $\mathbb{P}_{\beta_c,r}$ the law of $|K|/\hat{\mathbb{E}}_r|K|$ has density $(\mathbb{E}_r|K|/\hat{\mathbb{E}}_r|K|)x^{-1}dQ_r(x)$, so $\mathbb{P}_{\beta_c,r}(|K|\geq\hat{\mathbb{E}}_r|K|)=(\mathbb{E}_r|K|/\hat{\mathbb{E}}_r|K|)\int_{x\geq1}x^{-1}dQ_r(x)$; the integral is $\asymp1$ only because $Q_\infty$ puts mass on $[1,\infty)$ with $\int_{x\geq1}x^{-1}dQ_\infty<\infty$, which holds for $Q_\infty=\chi^2_1$ but is NOT implied by hypotheses (1)-(4) alone. The remark is therefore correct in its stated scope (the assumptions of Theorem I.1.6 or I.1.15) and must not be generalised. CROSS-SLICE CONSUMER: Section I.5 at canonical L2858 ("the final estimate follows from (I.3.4)"); the consumer node belongs to another slice and is recorded here as text, not as an edge. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.Thmthm4@L1823-L1837 | packet relation requires: the remark is derived from Proposition I.3.2 and its proof, as the sentence at canonical L739 says

NODE: hutchcroft.i.3.tail
KIND: application
TITLE: Deduction of (I.1.7) and (I.1.17) from the moment asymptotics, via the chi-squared limit
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p5@L1917-L1978
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5@L1917-L1978
CONTRACT_ID: hutchcroft.i.3.tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The moment asymptotics (I.1.6) (respectively (I.1.16)); hence hypothesis (1) of Proposition I.3.2 with $A_1=\alpha/\beta_c$ and hypothesis (2) with $a=2$ and $A_2=A$ (respectively $A_2f(r)=A_rr^{2\alpha}$ with $A_r$ slowly varying).
SOURCE_QUANTIFIERS: $r\to\infty$, $h\downarrow0$, $n\to\infty$; each of the two moment roots separately.
SOURCE_CONCLUSION: (I.1.7) $\mathbb{P}_{\beta_c}(|K|\geq n)\sim\frac{\alpha}{\beta_c}\sqrt{\frac{2}{\pi A}}\,n^{-1/2}$ when $d>3\alpha$; (I.1.17) $\mathbb{P}_{\beta_c}(|K|\geq n)\sim\frac{\alpha}{\beta_c}\sqrt{\frac{2}{\pi}}\,\tilde{A}_n^{-1/2}n^{-1/2}$ when $d=3\alpha$.
CONSTANT_SCOPE: $A$ (high-dimensional root) or the slowly varying pair $A_r,\tilde{A}_n$ with $(A_rr^{2\alpha})^{-1}=\tilde{A}_s^{-1/(2\alpha)}s^{1/(2\alpha)}$ at $s=A_rr^{2\alpha}$; both scaled by $\alpha/\beta_c$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2,hutchcroft.i.3.tail:step-chi2,hutchcroft.i.3.tail:step-integrals,hutchcroft.i.3.tail:step-constants,hutchcroft.i.1.beta_c.bilat
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5@L1917-L1978 canonical paper-tex.txt L778-L809; this region is the html block #S3.SS2.p5 L1917-L1978, inside #S3.SS2.3 L1915-L1979, which is the region the coordinator names as the real Section I.3 proof location for Theorem I.1.15. RECORDED AS KIND: application, NOT KIND: route, deliberately: the owner of the route is the frozen root (hutchcroft.i.1.6 / hutchcroft.i.1.15), which is outside this slice, and a route node without an in-slice owner cannot be listed in any ROUTES field. Route ownership therefore stays with the root slice; see the NOTE on the three steps. The derivation proves only the TAIL halves of the two roots and leaves their moment halves to the moment statements. Cross-slice obligations, recorded as text rather than as edges: (i.1.6)/(i.1.16) supply hypothesis (1) with $A_1=\alpha/\beta_c$ and hypothesis (2) with $a=2$; the $d=3\alpha$ root additionally requires $A_r$ slowly varying. The fixed $\kappa$ in $A_3=A_1A_2^{-1/2}\sqrt2$ is CHECKED: $\lim_{\lambda}\lambda^{-1/2}\int(1-e^{-\lambda x})/x\,dQ_\infty=\sqrt2$ and $\Gamma(1/2)=\sqrt\pi$, so $A_4=A_1A_2^{-1/2}\sqrt{2/\pi}$, matching (I.1.7). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: the final asymptotics are obtained by applying Proposition I.3.2 with $a=2$ and the two moment roots
EDGE: hutchcroft.i.3.tail:step-chi2 | .scratch/source/paper.html#S3.SS2.p5.3@L1936-L1937 | packet relation requires: hypothesis (3)+(4) of Proposition I.3.2 is verified by identifying $Q_\infty$ as the chi-squared law
EDGE: hutchcroft.i.3.tail:step-integrals | .scratch/source/paper.html#S3.SS2.p5.4@L1945-L1945 | packet relation requires: the two exact integrals supply the limit $\sqrt2$ that fixes $A_3$
EDGE: hutchcroft.i.3.tail:step-constants | .scratch/source/paper.html#S3.SS2.p5.6@L1963-L1964 | packet relation requires: the printed displays (I.1.7) and (I.1.17) are the constant bookkeeping of that step
EDGE: hutchcroft.i.1.beta_c.bilat | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: $A_1=\alpha/\beta_c\in(0,\infty)$ and the printed constants need $0<\beta_c<\infty$, supplied by the derived result

NODE: hutchcroft.i.3.tail:step-chi2
KIND: step
TITLE: Moment convergence identifies $Q_\infty$ as the chi-squared law with one degree of freedom
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p5.2@L1928-L1928
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.3@L1936-L1937
CONTRACT_ID: hutchcroft.i.3.tail:step-chi2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I.1.6) or (I.1.16) for every integer $p\geq1$.
SOURCE_QUANTIFIERS: $r\to\infty$; every integer $p\geq1$.
SOURCE_CONCLUSION: $\int_0^\infty x^p\,dQ_r=\hat{\mathbb{E}}_{\beta_c,r}|K|^{p}/(\hat{\mathbb{E}}_{\beta_c,r}|K|)^p=\mathbb{E}_r|K|^{p+1}/((\mathbb{E}_r|K|^{2}/\mathbb{E}_r|K|)^p\mathbb{E}_r|K|)\sim(2p-1)!!$; every subsequential limit of $(Q_r)$ has $p$-th moment $(2p-1)!!$ for all $p$, hence by Carleman’s criterion $Q_r\Rightarrow\chi^2_1$.
CONSTANT_SCOPE: The double factorial $(2p-3)!!$ combinatorics, giving moment $(2p-1)!!$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.sizebiased
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.3@L1936-L1937 canonical paper-tex.txt L782-L791. Reconstructed, and the algebra is checked: substituting the moment asymptotics $\mathbb{E}_r|K|^{p}\sim(2p-3)!!A^{p-1}(\alpha/\beta_c)r^{(2p-1)\alpha}$ gives $\int x^p\,dQ_r\sim(2p+1-2)!!=(2p-1)!!$, which are the moments of $\chi^2_1$. SOURCE GAP (technical): the source says "by dominated convergence", which needs uniform integrability of $x^p$ under $Q_r$; that follows from the NEXT moment asymptotic by Markov, i.e. from the case $p+1$, but the argument is not written. Carleman’s criterion applies because $\sum_k m_k^{-1/(2k)}=\infty$ for $m_k=(2k-1)!!$. CROSS-SLICE OBLIGATION: the moment asymptotics are the frozen roots hutchcroft.i.1.6 and hutchcroft.i.1.15, which are NOT nodes of this slice; no edge is drawn to them and the dependency is carried here as text. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.sizebiased | .scratch/source/paper.html#S3.SS2.p5.2@L1928-L1928 | packet relation requires: the identities expressing $\int x^p\,dQ_r$ through $\hat{\mathbb{E}}_r∣K∣^p$ are the size-biased definitions

NODE: hutchcroft.i.3.tail:step-integrals
KIND: step
TITLE: The two chi-squared integrals: $\sqrt{2\lambda+1}-1$ and the limit $\sqrt2$
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p5.4@L1945-L1945
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.4@L1945-L1945
CONTRACT_ID: hutchcroft.i.3.tail:step-integrals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $Q_\infty$ is the chi-squared law with one degree of freedom, density $x^{-1/2}e^{-x/2}/\sqrt{2\pi}$ on $(0,\infty)$.
SOURCE_QUANTIFIERS: Every $\lambda>0$; then $\lambda\to\infty$.
SOURCE_CONCLUSION: $\int_0^\infty\frac{1-e^{-\lambda x}}{x}\,dQ_\infty(x)=\frac{1}{\sqrt{2\pi}}\int_0^\infty(1-e^{-\lambda x})e^{-x/2}x^{-3/2}dx=\sqrt{2\lambda+1}-1$, hence $\lim_{\lambda\to\infty}\lambda^{-1/2}\int\ldots=\sqrt2$.
CONSTANT_SCOPE: $\sqrt{2\pi}$ and $\sqrt2$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2:step-a3-limit
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.4@L1945-L1945 canonical paper-tex.txt L793-L797. INDEPENDENTLY VERIFIED in this session with sympy: $\int_0^\infty(1-e^{-\lambda x})x^{-3/2}e^{-x/2}dx=\sqrt2\sqrt\pi(\sqrt{2\lambda+1}-1)$, so after division by $\sqrt{2\pi}$ the printed identity is exact (residual $0$), and $\lim_{\lambda\to\infty}\lambda^{-1/2}(\sqrt{2\lambda+1}-1)=\sqrt2$. Outputs quoted in I23Validation.md. This step is also where the open obligation hutchcroft.i.3.2:step-a3-limit is DISCHARGED for the two intended uses: it supplies the exact value of the defining limit at $a=2$ and $Q_\infty=\chi^2_1$. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.3.2:step-a3-limit | .scratch/source/paper.html#S3.SS2.p5.4@L1945-L1945 | packet relation requires: this is the computation that discharges the open obligation at $a=2$ with $Q_\infty=\chi^2_1$, giving the value $\sqrt2$ of the defining limit

NODE: hutchcroft.i.3.tail:step-constants
KIND: step
TITLE: Specialise $A_3,A_4$ at $a=2$, $A_1=\alpha/\beta_c$ and the chi-squared law
STATEMENT_SOURCE: .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.6@L1963-L1964
CONTRACT_ID: hutchcroft.i.3.tail:step-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $A_1=\alpha/\beta_c$; $A_2=A$ with $f(r)=r^{2\alpha}$ (high-dimensional root) or $A_2f(r)=A_rr^{2\alpha}$ with $A_r$ slowly varying (critical-dimension root); $a=2$; $\Gamma(1/2)=\sqrt\pi$; $\lim_\lambda\lambda^{-1/2}\int\ldots=\sqrt2$.
SOURCE_QUANTIFIERS: $h\downarrow0$; $n\to\infty$.
SOURCE_CONCLUSION: $A_3=\frac{\alpha}{\beta_c}A^{-1/2}\sqrt2$ and $A_4=A_3/\sqrt\pi=\frac{\alpha}{\beta_c}\sqrt{2/\pi}A^{-1/2}$, giving (I.1.7); in the critical-dimension root $A^{-1/2}$ is replaced by $\tilde{A}_n^{-1/2}$, giving (I.1.17).
CONSTANT_SCOPE: $A$ or the slowly varying pair $A_r,\tilde{A}_n$; the factor $\alpha/\beta_c$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.3.2,hutchcroft.i.3.tail:step-integrals,hutchcroft.i.3.tail:step-chi2,hutchcroft.i.1.beta_c.bilat
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.p5.6@L1963-L1964 canonical paper-tex.txt L799-L809. Reconstructed and checked against the printed displays. The critical-dimension substitution is checked: writing $s=A_rr^{2\alpha}$ gives $f^{-1}(n)^{\alpha}/n=\tilde{A}_n^{-1/2}n^{-1/2}$, which is the printed form. $\beta_c$ must be finite and positive here, because at $\beta_c=0$ one has $\mathbb{E}_{0,r}|K|=1$ for every $r$ and hypothesis (1) fails while $\alpha/\beta_c=+\infty$. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.3.2 | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: the constants $A_3,A_4$ are those of Proposition I.3.2 evaluated at $a=2$
EDGE: hutchcroft.i.3.tail:step-integrals | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: the limit $\sqrt2$ in $A_3$ is exactly the value produced by the chi-squared integral step
EDGE: hutchcroft.i.3.tail:step-chi2 | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: identifying $Q_\infty$ with $\chi^2_1$ is what makes the integral in $A_3$ computable at all
EDGE: hutchcroft.i.1.beta_c.bilat | .scratch/source/paper.html#S3.SS2.p5.5@L1953-L1953 | packet relation requires: $\alpha/\beta_c$ must lie in $(0,\infty)$ for $A_3,A_4$ to be finite and positive, which is the derived bound on $\beta_c$

NODE: hutchcroft.def.beta_c
KIND: definition
TITLE: The critical parameter $\beta_c$
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1@L334-L354
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.def.beta_c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Kernel class of Definition I.1.3: $d\geq1$, a norm on $\mathbb{R}^d$, $\alpha>0$, $J(x,y)=\mathbb{1}(x\neq y)J(\|x-y\|)$ with $J$ a decreasing differentiable function of $\|x-y\|$, $|J^{\prime}(r)|=C(1+\delta_r)r^{-d-\alpha-1}$ with $\delta$ a logarithmically integrable error function, normalised so that $|J^{\prime}(r)|\sim r^{-d-\alpha-1}$ and $|B_r|\sim r^d$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$.
SOURCE_CONCLUSION: $\beta_c:=\inf\{\beta\geq0:\text{an infinite cluster exists }\mathbb{P}_\beta\text{-a.s.}\}$, with $\mathbb{P}_\beta$ the independent bond percolation of the same definition.
CONSTANT_SCOPE: No constant; $\beta_c$ is a function of $(d,\alpha,\text{norm},J)$ only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: canonical paper-tex.txt L46-L48; the display is html table id=S1.Ex1 inside this block. Purely a definition: NOTHING is asserted here about the range of $\beta_c$, and in particular this record is not the statement $0<\beta_c<\infty$. CROSS-SLICE: Definition I.1.3 and $\beta_c$ are Section I.1 objects owned by slice A; this record owns only what the two derived bounds below consume and must be reconciled, not duplicated, at merge. CONSUMERS: hutchcroft.i.1.beta_c.bilat and, through it, hutchcroft.i.2.15, hutchcroft.i.3.1, hutchcroft.i.3.2 and hutchcroft.i.3.tail. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.1.beta_c.bilat
KIND: lemma
TITLE: $0<\beta_c<\infty$ in the dimension regimes stated in Section I.1.2
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353
PROOF_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353
CONTRACT_ID: hutchcroft.i.1.beta_c.bilat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The kernel class of Definition I.1.3, with either d≥2 and α>0, or d=1 and 0<α≤1. The separate d=1, α>1 problem is not discharged here.
SOURCE_QUANTIFIERS: Every kernel in the stated regime, separated as d≥2, α>0 on one branch and d=1, 0<α≤1 on the other. These are disjunctive regimes, not simultaneous conditions.
SOURCE_CONCLUSION: $0<\beta_c<\infty$ in the stated dimension regimes. No d=1, α>1 finiteness assertion is made or silently inherited.
CONSTANT_SCOPE: The lower bound comes from the first-moment walk comparison (betac.pos) and the upper bound from the dimension-split coupling/external inputs (betac.fin). The former all-dimension K≥2 line threshold is withdrawn and no longer supplies any constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.beta_c,hutchcroft.i.1.beta_c.bilat:step-positive,hutchcroft.i.1.2.betac.fin
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE-REGIME CORRECTION. The source at #S1.SS2.p1.3@L353-L353 gives d≥2, α>0 or d=1, 0<α≤1. The earlier candidate's claim that the elementary line construction covered every d≥1, α>0 was unsupported: nearest-neighbour Z has p_c=1 and a collinear embedding can repeat physical edges. The withdrawn reconstruction remains separately DISPUTED, with no incoming edge. This record keeps only the actual source regimes. Positivity is supplied by the first-moment walk bound; finiteness now consumes hutchcroft.i.1.2.betac.fin, including for the other four existing consumers. No new finiteness claim is made for d=1, α>1, and nothing here says that the moment root is proved. The proof source cites the printed assertion; the derived proof obligation remains NOT_STARTED.
EDGE: hutchcroft.def.beta_c | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: the object whose range is bounded is the critical parameter defined there, not a free parameter
EDGE: hutchcroft.i.1.beta_c.bilat:step-positive | .scratch/source/paper.html#S1.SS2.p1.3@L353-L353 | packet relation requires: the lower bound $\beta_c>0$ is supplied by the first-moment walk bound
EDGE: hutchcroft.i.1.2.betac.fin | .scratch/source/paper.html#S1.SS2.p1.3@L353-L353 | finite critical parameter supplied by the corrected dimension-split I.1.2 derivation, rather than the withdrawn nearest-line reconstruction; this same provider remains available to every existing bilat consumer

NODE: hutchcroft.i.1.beta_c.bilat:step-positive
KIND: step
TITLE: $\beta_c>0$ from the first-moment bound on open paths
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353
PROOF_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353
CONTRACT_ID: hutchcroft.i.1.beta_c.bilat:step-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Kernel class of Definition I.1.3 with $\alpha>0$; $m:=\sum_{y\in\mathbb{Z}^d}J(0,y)$.
SOURCE_QUANTIFIERS: Every $\beta\in[0,1/m)$, where $0<m<\infty$.
SOURCE_CONCLUSION: $\mathbb{E}_\beta|K_0|\leq\sum_{n\geq0}(\beta m)^n<\infty$, hence $\mathbb{P}_\beta(|K_0|=\infty)=0$ and $\beta_c\geq1/m>0$.
CONSTANT_SCOPE: The threshold $1/m$ with $m=\sum_y J(0,y)$; finite and positive because $\alpha>0$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.def.logint,hutchcroft.def.beta_c,assumption.weighted_graph
ROUTES: -
ROUTE_FOR: -
NOTE: PACKET PROOF_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353 NOT PRINTED IN THE SOURCE. Elementary and self-contained. Three ingredients, each recorded as an edge. (i) $m<\infty$: from $|J^{\prime}(r)|=(1+\delta_r)r^{-d-\alpha-1}$ with $\delta$ logarithmically integrable one gets $J(r)=\int_r^\infty(1+\delta_s)s^{-d-\alpha-1}ds=r^{-d-\alpha}/(d+\alpha)(1+o(1))$, the error term being bounded by $r^{-d-\alpha}\int_r^\infty|\delta_s|\,ds/s=o(r^{-d-\alpha})$; hence $\sum_{y\neq0}J(\|y\|)\asymp\sum_{y\neq0}\|y\|^{-d-\alpha}<\infty$ for $\alpha>0$ and every $d\geq1$. (ii) The expected number of open self-avoiding paths of length $n$ from $0$ is at most $\beta^n m^n$ by translation invariance and independence, and every connection contains such a path, giving the displayed bound. (iii) $|K_0|=\infty$ with positive probability would force $\mathbb{E}_\beta|K_0|=\infty$. No monotonicity in $\beta$ is needed for the inequality, only for the phrase "for every $\beta\in[0,1/m)$". Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.def.logint | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: logarithmic integrability of $\delta$ is what makes $J(r)\sim r^{-d-\alpha}/(d+\alpha)$ two-sided, hence $m<\infty$
EDGE: hutchcroft.def.beta_c | .scratch/source/paper.html#S1.SS2.p1.3@L353-L353 | packet relation requires: the conclusion is a lower bound on the infimum that defines $\beta_c$
EDGE: assumption.weighted_graph | .scratch/source/paper.html#S1.SS2.p1@L334-L354 | packet relation requires: the path-expansion uses independence of edges and translation invariance of the kernel

NODE: hutchcroft.i.1.beta_c.bilat:step-finite
KIND: claim
TITLE: Critical-point finiteness: corrected square-lattice route for d≥2; old line reconstruction WITHDRAWN
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS2.p1.3@L353-L353
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.beta_c.bilat:step-finite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: For the corrected route only: d≥2, α>0, Definition I.1.3 normalized kernel J with J(0,e₁)>0 and J(0,2e₂)>0, β>0. The previous all-dimension finite-range-line hypothesis K≥2 is not retained. For d=1, α>1 no finiteness claim is made
SOURCE_QUANTIFIERS: Only under d≥2, choose β satisfying β·min{J(0,e₁),J(0,2e₂)}>log 4. Minimal couplings strengthen the edge parameters past 3/4. For d=1, α>1 there is no constructed witness in this campaign; the independently quoted Dyson regime 0<α≤1 is a separate external input, not a consequence here
SOURCE_CONCLUSION: For d≥2, βc ≤ log 4 / min{J(0,e₁),J(0,2e₂)} < ∞, using the injective φ(m,n)=m e₁+n(2e₂) embedding into the stretched nearest-neighbour square lattice and independent thinning to p>3/4 on distinct coefficients of the two square-lattice edge families, followed by Bollobás–Riordan Theorem 10 at p>1/2. The previous nearest-line candidate is withdrawn: nearest-neighbour Z has p_c=1 and a collinear map repeats physical edges, so neither proof establishes supercritical percolation or independence along it. For d=1, α>1 no assertion is made
CONSTANT_SCOPE: The finite upper bound is log 4/min{J(0,e₁),J(0,2e₂)}. Both edge families of the stretched Z² lattice remain distinct under the embedding, so their thinning preserves independence. The all-dimension K≥2 line threshold is not retained. No external one-dimensional positivity or external supercritical witness is secretly added
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: DISPUTED
EXTRACTOR: bounded-source-correction-current-coordinator
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: WITHDRAWN RECONSTRUCTION (DISPUTED), not a proof provider. The nearest-neighbour-line version claimed finiteness for every d≥1 using K≥2, but nearest-neighbour Z has p_c=1, and collinear maps do not preserve independence or ensure infinite-cluster transfer. The surviving d≥2 statement is the established written reconstruction in docs/orchestration/DERIVED_CRITICAL_POINT.md: φ(m,n)=m e₁+n(2e₂), pairwise distinct nearest-neighbour square-lattice edges, independent thinning with p>3/4, and Bollobás–Riordan Theorem 10 at p>1/2. The supplied literature PDF is .scratch/literature/harris-kesten-math-0410359v3.pdf (SHA256 b171039a2d77dece89a6760749fa31d49843028614c4adf92b6fad21da90d8e8). No Lean proof of the supercritical square-lattice theorem or of the required criticalBetaSet nonemptiness is supplied here. For d=1, α>1, no all-dimensional finiteness statement is claimed. Along the roots, the 1-D cases use α≤1/3 and rely on a separately unverified 0<α≤1 external range, not this rejected line argument.

NODE: assumption.weighted_graph
KIND: assumption
TITLE: Typing convention: Bernoulli bond percolation on a weighted graph
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm3@L370-L416
PROOF_SOURCE: -
CONTRACT_ID: assumption.weighted_graph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A countable graph $G=(V,E)$ with symmetric edge weights $J:E\to[0,\infty)$, written $J(x,y)$ for $\{x,y\}\in E$, and a parameter $\beta\geq0$.
SOURCE_QUANTIFIERS: Every such weighted graph and every $\beta\geq0$.
SOURCE_CONCLUSION: Edges are open independently with $\mathbb{P}_\beta(e\text{ open})=1-e^{-\beta J(e)}$; $K_x$ is the open cluster of $x$; "transitive" means vertex-transitive with a $J$-preserving action.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: The phrase is used in every statement of Section I.2 but is never defined there. The only kernel definition in the paper is Definition I.1.3 at html #S1.Thmthm3 L370-L416 (the $\mathbb{Z}^d$ long-range model with $J(x,y)\sim\mathrm{const}\cdot\|x-y\|^{-d-\alpha}$ and the cut-off $J_r$); the general weighted-graph typing is left to the literature. This leaf records exactly the typing the slice uses and nothing more. CROSS-SLICE: Definition I.1.3 is owned by slice A, so at merge this leaf must either be re-pointed to the I.1.3 node or kept as the thin typing leaf, and in either case the two must not both claim the same CONTRACT_ID. SOURCE GAP (typing): no printed statement fixes the general weighted-graph model, so a formalisation must not silently substitute a different one. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.grimmett.fkg.bk
KIND: external
TITLE: Harris-FKG and BK inequalities
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p2@L1088-L1132
PROOF_SOURCE: -
CONTRACT_ID: ext.grimmett.fkg.bk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $F,G$ increasing functions of a percolation configuration (FKG); $A,B$ increasing events depending on finitely many edges (BK), with witness sets $W$ and disjoint occurrence $A\circ B$.
SOURCE_QUANTIFIERS: All such functions and events; infinite-volume events only after the limiting argument of footnote 11.
SOURCE_CONCLUSION: $\mathbb{E}FG\geq\mathbb{E}F\,\mathbb{E}G$ and $\mathbb{P}(A\cap B)\geq\mathbb{P}(A)\mathbb{P}(B)$; and $\mathbb{P}(A\circ B)\leq\mathbb{P}(A)\mathbb{P}(B)$.
CONSTANT_SCOPE: Factor $1$ in both inequalities; no constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [55, Sections 2.2 and 2.3]. The paper restates both inequalities at the locator, so the as-used hypothesis and conclusion are exact; the cited book was NOT opened and the leaf is NOT independently verified. Standard textbook statements; no defect expected. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.bk.extensions
KIND: external
TITLE: BK without monotonicity, and on infinite edge sets
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p3@L1133-L1138
PROOF_SOURCE: -
CONTRACT_ID: ext.bk.extensions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Reimer [94]: arbitrary events $A,B$ on a finite product space. van den Berg-Fiebig [105]: $A,B$ each an intersection of an increasing and a decreasing set. Arratia-Garibaldi-Hales [10, Section 7]: the set $A\odot B$ of configurations with finite disjoint witnesses, on infinite spaces.
SOURCE_QUANTIFIERS: All such events; the infinite-volume case only for $A\odot B$.
SOURCE_CONCLUSION: $\mathbb{P}(A\circ B)\leq\mathbb{P}(A)\mathbb{P}(B)$ under each of the three hypothesis sets; on infinite spaces the inequality holds for $A\odot B$, which coincides with $A\circ B$ in most use cases.
CONSTANT_SCOPE: Factor $1$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: The citation bundle [94], [105], [10, Section 7] is restated by the paper at the locator; none of the three works was opened, so this leaf is NOT independently verified. WHY IT MATTERS HERE: clause (i) of Lemma I.2.1 involves the DECREASING factor $\mathbb{1}(x\nleftrightarrow y)$, for which the increasing-events form of BK does not apply; the paper relies on this leaf silently. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.aizenman-newman1984
KIND: external
TITLE: Tree-graph inequalities
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p6@L1194-L1237
PROOF_SOURCE: -
CONTRACT_ID: ext.aizenman-newman1984
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a weighted graph; $k\geq1$; $x_0,\ldots,x_k\in V$; trees with leaves labelled $0,\ldots,k$ and unlabelled degree-3 non-leaf vertices.
SOURCE_QUANTIFIERS: Every $k\geq1$ and every $(k+1)$-tuple of vertices.
SOURCE_CONCLUSION: The $k$-point connectivity function is bounded by the sum over labelled-tree shapes of products of two-point functions, i.e. displays (I.2.1), (I.2.2) and (I.2.3) of the paper.
CONSTANT_SCOPE: Factor $1$; the combinatorial factor $(2p-3)!!$ in (I.2.3) counts trees with $p+1$ labelled leaves and unlabelled degree-3 non-leaf vertices.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [4]. The paper restates the three displays, so the as-used data are exact; [4] was NOT opened and the leaf is NOT independently verified. The theorem is itself proved from BK in the cited work, but that is second-hand and is NOT recorded as an edge. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.hutchcroft2021.thm2.2
KIND: external
TITLE: Universal tightness of the maximum cluster size
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p7.1@L1239-L1240
PROOF_SOURCE: -
CONTRACT_ID: ext.hutchcroft2021.thm2.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $G=(V,E,J)$ a weighted graph; $\Lambda\subseteq V$ finite non-empty; clusters computed in the entire graph; $\beta\geq0$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$, $\lambda\geq1$, $0<\varepsilon\leq1$ and $u\in V$.
SOURCE_CONCLUSION: The three inequalities (I.2.4), (I.2.5) and (I.2.6) with the constants $1/9$, $27$ and $e$.
CONSTANT_SCOPE: Universal constants $1/9$, $27$, $e$, independent of $G,\Lambda,\beta$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [74, Theorem 2.2]. [74] was NOT opened; the leaf is NOT independently verified. The paper states the constants explicitly, which is why the as-used data can be transcribed, but the transcription is not a check of the cited theorem. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.hutchcroft2022
KIND: external
TITLE: Spatially averaged two-point upper bound at criticality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS3.p1@L1592-L1595
PROOF_SOURCE: -
CONTRACT_ID: ext.hutchcroft2022
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Long-range percolation on $\mathbb{Z}^d$ with a kernel as in Definition I.1.3, $\alpha>0$, at $\beta_c$.
SOURCE_QUANTIFIERS: Every $r\geq1$.
SOURCE_CONCLUSION: $\sum_{x\in B_r}\mathbb{P}_{\beta_c}(0\leftrightarrow x)\preceq r^{\alpha}$.
CONSTANT_SCOPE: One model-dependent constant, independent of $r$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [76] (following the hierarchical analysis of [77]). NOT opened, NOT independently verified. Note the paper’s own gloss that the bound is "vacuous" for $\alpha\geq d$ is wrong as stated: for $\alpha\geq d$ the bound is trivial, not vacuous. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.baumler-berger2024
KIND: external
TITLE: Matching lower bound on the averaged two-point function for alpha < 1
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS3.p2@L1602-L1604
PROOF_SOURCE: -
CONTRACT_ID: ext.baumler-berger2024
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The $\mathbb{Z}^d$ long-range model at $\beta_c$ with $\alpha<1$.
SOURCE_QUANTIFIERS: All $x\neq y$ in $\mathbb{Z}^d$ or all $r\geq1$, as used for the lower half of Theorem I.2.14.
SOURCE_CONCLUSION: A matching lower bound for the spatially averaged (and, in [73], pointwise) two-point function at criticality when $\alpha<1$.
CONSTANT_SCOPE: One model-dependent constant, two-sided together with [76].
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [20]. NOT opened, NOT independently verified. The exact scope (average versus pointwise) is not separated in the paper’s sentence, so this leaf records only what the sentence asserts and no more. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.hutchcroft-ptf
KIND: external
TITLE: Pointwise two-point function for alpha < 1
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS3.p2@L1602-L1604
PROOF_SOURCE: -
CONTRACT_ID: ext.hutchcroft-ptf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The $\mathbb{Z}^d$ long-range model at $\beta_c$ with $\alpha<1$.
SOURCE_QUANTIFIERS: Every $x\neq y$ in $\mathbb{Z}^d$.
SOURCE_CONCLUSION: $\mathbb{P}_{\beta_c}(x\leftrightarrow y)\asymp\|x-y\|^{-d+\alpha}$.
CONSTANT_SCOPE: Two-sided, model-dependent constants; not normalised to $1$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [73]. NOT opened, NOT independently verified. The constant is NOT asserted to be $1$, and the record must not be merged into any interface that assumes a normalised two-point function. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.gladkov2024
KIND: external
TITLE: Gladkov three-point inequality
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS1.p12.1@L1387-L1389
PROOF_SOURCE: -
CONTRACT_ID: ext.gladkov2024
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a weighted graph $G=(V,E,J)$; $\beta\geq0$; $x,y,z\in V$.
SOURCE_QUANTIFIERS: Every $\beta\geq0$ and every $x,y,z\in V$.
SOURCE_CONCLUSION: $\mathbb{P}_\beta(x\leftrightarrow y\leftrightarrow z)^{2}\leq8\,\mathbb{P}_\beta(x\leftrightarrow y)\mathbb{P}_\beta(y\leftrightarrow z)\mathbb{P}_\beta(z\leftrightarrow x)$.
CONSTANT_SCOPE: Universal constant $8$; no model constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [52]; the paper calls it "a (non-obvious) consequence of the BK inequality" and proves nothing. NOT opened, NOT independently verified. Its higher-$k$ extension is deferred to Paper II and is out of this slice. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.feller.8.9.1
KIND: external
TITLE: Karamata integral asymptotics, both index signs
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm10@L1489-L1511
PROOF_SOURCE: -
CONTRACT_ID: ext.feller.8.9.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f$ regularly varying of index $\alpha$, measurable.
SOURCE_QUANTIFIERS: $\alpha>-1$ and $r\to\infty$ for the first display; $\alpha<-1$ and every $r>0$ for the second.
SOURCE_CONCLUSION: $\int_1^r f\sim rf(r)/(\alpha+1)$ for $\alpha>-1$; $\int_r^\infty f\sim rf(r)/(-\alpha-1)$ for $\alpha<-1$.
CONSTANT_SCOPE: The constants $1/(\alpha+1)$ and $1/(-\alpha-1)$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [47, Theorem VIII.9.1] (Feller volume II). NOT opened, NOT independently verified. IMPORTANT: the printed negative-index constant in the paper is $1/(1-\alpha)$, which is wrong; the value recorded here is the corrected one, established by an independent symbolic check in this session, NOT by the citation. The correction is therefore evidence about the paper, not about the cited book. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.feller.13.5.2
KIND: external
TITLE: Karamata Tauberian theorem, probabilistic form
STATEMENT_SOURCE: .scratch/source/paper.html#S2.Thmthm11@L1515-L1528
PROOF_SOURCE: -
CONTRACT_ID: ext.feller.13.5.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f$ regularly varying of index $-\alpha$ for some $0\leq\alpha<1$; $X$ a non-negative random variable.
SOURCE_QUANTIFIERS: $h\downarrow0$; $x\to\infty$; the assertion is an equivalence.
SOURCE_CONCLUSION: $\mathbb{E}[1-e^{-hX}]\sim f(1/h)$ if and only if $\mathbb{P}(X\geq x)\sim f(x)/\Gamma(1-\alpha)$.
CONSTANT_SCOPE: The Gamma factor $\Gamma(1-\alpha)$ only.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [47, Theorem XIII.5.2]. NOT opened, NOT independently verified. THE DOMAIN RESTRICTION $0\leq\alpha<1$ IS LOAD-BEARING for Proposition I.3.2 and is the reason that statement needs $a\geq1$; it is preserved verbatim here rather than relaxed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.bgt.thm1.2.1
KIND: external
TITLE: Index and compact-uniformity for regularly varying functions
STATEMENT_SOURCE: .scratch/source/paper.html#S2.SS2.p1@L1482-L1485
PROOF_SOURCE: -
CONTRACT_ID: ext.bgt.thm1.2.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f$ regularly varying and measurable.
SOURCE_QUANTIFIERS: Every $\lambda>0$, uniformly for $\lambda$ in compact subsets of $(0,\infty)$.
SOURCE_CONCLUSION: There is a unique $\alpha\in\mathbb{R}$ with $\lim_{x\to\infty}f(\lambda x)/f(x)=\lambda^{\alpha}$, and the convergence is compact-uniform.
CONSTANT_SCOPE: No constant.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [24, Theorem 1.2.1]. NOT opened, NOT independently verified. The compact uniformity is what makes "regularly varying of negative index tends to $0$" available, which the $a\geq1$ bridge step uses. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: ext.bgt.thm1.5.12
KIND: external
TITLE: Regular variation of the inverse function
STATEMENT_SOURCE: .scratch/source/paper.html#S3.Thmthm2@L1762-L1813
PROOF_SOURCE: -
CONTRACT_ID: ext.bgt.thm1.5.12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: $f$ regularly varying of positive index, strictly monotone, with inverse $f^{-1}$.
SOURCE_QUANTIFIERS: As $s\to\infty$.
SOURCE_CONCLUSION: $f^{-1}$ is regularly varying of index $1/\mathrm{ind}(f)$; in particular $f^{-1}$ has index $1/(a\alpha)$ in Proposition I.3.2 and the substitution $r=f^{-1}(\lambda/A_2h)$ produces the factor $\lambda^{1/a}A_2^{-1/a}$.
CONSTANT_SCOPE: No constant; only the index $1/\mathrm{ind}(f)$.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: Cited as [24, Theorem 1.5.12], in the sentence after Proposition I.3.2 and again implicitly in its proof. NOT opened, NOT independently verified. Sharper than the doubling hypothesis of Proposition I.3.1, so the two must not be conflated. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.ultramath/smwobyis9/m2/I23Packet.m2.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.1
KIND: lemma
TITLE: Lemma I.4.1 — exact derivative formula for cut-off cluster-volume moments (carries display (I.4.1) as its own content  no second node)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm1@L1989-L2004
PROOF_SOURCE: .scratch/source/paper.html#S4.2@L2030-L2059
CONTRACT_ID: I.4.1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kernel J and cut-off J_r as in Definition I.1.3/I.1.5 (so the law moves with r); B_r = {x∈Z^d : ‖x‖ ≤ r} lattice points in the closed ‖·‖-ball at the *same* r as the cut-off; K the 0-cluster, K_y the y-cluster in one configuration
SOURCE_QUANTIFIERS: every integer p ≥ 1; every 0 ≤ β ≤ β_c; every r > 0
SOURCE_CONCLUSION: (∂/∂r)𝔼_{β,r}|K|^p = β|J′(r)| Σ_{ℓ=0}^{p−1} C(p,ℓ) 𝔼_{β,r}[ |K|^{ℓ+1} Σ_{y∈B_r} 1(y∉K) |K_y|^{p−ℓ} ]
CONSTANT_SCOPE: only β, |J′(r)| and binomial coefficients; no implicit constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.1.s1,hutchcroft.i.4.1.s2,hutchcroft.i.4.1.s3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.3 [needed: Definition I.1.3: kernel J, |J'(r)| = C(1+δ_r)r^{−d−α−1}, normalization (∗)] ; XSLICE:I.1.5 [needed: Definition I.1.5: cut-off kernel J_r, laws P_{β,r}, β_c of the uncut kernel, P_{β_c,r} subcritical for r<∞, J_r ↑ J] PACKET PROOF_SOURCE: P#S4.SS1@L834-L846 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.3`, `XSLICE:I.1.5` (statements and use sites in §4). The identity is exact; the factor (1−p_r({x,y})) that a naive Russo application would demand is supplied by 1(y∉K) inside the same expectation (§5.4) — do not "repair" it. The RHS sum range and the kernel's support are the same ball B_r; that alignment is what makes the mass-transport rewrite exact (§5.4, §7). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.1.s1 | .scratch/source/paper.html#S4.p3.1@L2033-L2033 | packet relation requires: the displayed right-hand side is produced by the Russo step  [was E003]
EDGE: hutchcroft.i.4.1.s2 | .scratch/source/paper.html#S4.p3.2@L2042-L2042 | packet relation requires: the sum over x ∈ K is replaced by ∣K∣ times the anchored sum  [was E004]
EDGE: hutchcroft.i.4.1.s3 | .scratch/source/paper.html#S4.p3.3@L2056-L2057 | packet relation requires: the ℓ-sum and the binomial coefficient are produced by the expansion  [was E005]

NODE: hutchcroft.i.4.2
KIND: proposition
TITLE: Proposition I.4.2 — first-moment asymptotics and logarithmic integrability of the error H_r
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm2@L2079-L2115
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of (1) d>3alpha; (2) d=3alpha and (Hydro); (3) the triangle condition; conclusion (b) additionally requires d>3alpha or (triangle and nabla_r logarithmically integrable)
SOURCE_QUANTIFIERS: r → ∞; H_r defined for every r > 0
SOURCE_CONCLUSION: (a) 𝔼_{β_c,r}|K| ∼ (α/β_c) r^α; (b) if d>3α **or** (triangle condition **and** ∇_r logarithmically integrable) then H_r := (β_c/α) r^{−α} 𝔼_{β_c,r}|K| − 1 is a logarithmically integrable error function
CONSTANT_SCOPE: leading constant α/β_c explicit and normalization-dependent; "∼" constant 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.a,hutchcroft.i.4.2.b
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.4.1@L1108-L1110 (assembly) with cases at L969-L1039 and L1075-L1085 [F2] ROUTES extended to r1-r5: r1-r3 select conclusion (a); r1 and r4 select conclusion (b) first alternative (`d>3α`); r5 selects (b) second alternative (triangle + log-integrable `∇_r`). r1 and r4 have the same hypothesis by the source's design and are kept distinct because they qualify different conclusions; merging them into one route would leave the second conclusion under-described. The three hypotheses are *alternatives*; the paper's phrase "at least one of the three hypotheses of (I.1.3)" points at the (HD) list, but case 2 of this proposition (d=3α + Hydro) is **not** an (HD) case — see §5.7. Case 2 carries no log-integrability of H_r (Remark I.4.4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.2.a | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | conclusion (a) is assembled from alternatives 1-3, not conjointly with conclusion (b)
EDGE: hutchcroft.i.4.2.b | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | conclusion (b) has a separate hypothesis set from conclusion (a)

NODE: hutchcroft.i.4.2.r1
KIND: route
TITLE: Prop I.4.2 alternative 1 — d > 3α
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i1@L2084-L2087
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.2.r1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d>3alpha
SOURCE_QUANTIFIERS: the fixed model satisfying this alternative; the parent proposition's moment limit is as r tends to infinity
SOURCE_CONCLUSION: one admissible hypothesis under which the asymptotic of I.4.2 holds
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c1
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.2.a
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex14@L971-L1017 (Lemma I.4.9) Alternative, never conjoined with r2 or r3. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SCOPING REPAIR: this alternative consumes only case c1 and neutral glue, not the all-cases assembly s1.
EDGE: hutchcroft.i.4.2.c1 | .scratch/source/paper.html#S4.SS1.5@L2312-L2386 | the route is the packaging of this one case derivation plus the assembly step; it does not restate the case's own lemma dependencies

NODE: hutchcroft.i.4.2.r2
KIND: route
TITLE: Prop I.4.2 alternative 2 — d = 3α and the hydrodynamic condition (Hydro)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i2@L2088-L2091
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.6@L2396-L2428
CONTRACT_ID: I.4.2.r2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α and (Hydro)
SOURCE_QUANTIFIERS: the fixed model satisfying this alternative; the parent proposition's moment limit is as r tends to infinity
SOURCE_CONCLUSION: one admissible hypothesis under which the asymptotic of I.4.2 holds, without any log-integrability conclusion
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c2,hutchcroft.a.hydro
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.2.a
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.14 [needed: Definition I.1.14 (Hydro): M_r is the edian of |K_max(B_r)| under P_{β_c,r}, and (Hydro) is M_r = o(r^{(d+α)/2})] PACKET PROOF_SOURCE: P#S4.Thmthm11.2@L1019-L1039 (Lemma I.4.10) Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.14` (statements and use sites in §4). The canonical text prints "(I.1.14)" here; the PDF p.35 prints "(Hydro)" (§5.7). Display (I.1.14) is the ξ₂ asymptotic, not the hydrodynamic condition — the HTML reference is wrong even though the intended object is unambiguous. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. HYPOTHESIS OWNERSHIP: the condition(s) named in SOURCE_HYPOTHESES are now DEPS (hutchcroft.a.hydro). Previously they were reachable only through the merged file-level STANDING_ASSUMPTIONS declaration, which turned a hypothesis of this one route into a premise of the whole packet. No (HD) case route reaches this record, so these conditions are not imported into the (HD) branches. SCOPING REPAIR: this alternative consumes only case c2 and neutral glue, not the all-cases assembly s1.
EDGE: hutchcroft.i.4.2.c2 | .scratch/source/paper.html#S4.SS1.6@L2396-L2428 | the route is the packaging of this one case derivation plus the assembly step; it does not restate the case's own lemma dependencies
EDGE: hutchcroft.a.hydro | .scratch/source/paper.html#S4.I1.i2@L2088-L2091 | the alternative this route selects IS this condition record: the hypothesis belongs to the route that assumes it, not to the file-level standing assumptions

NODE: hutchcroft.i.4.2.r3
KIND: route
TITLE: Prop I.4.2 alternative 3 — the triangle condition ∇_{β_c} < ∞
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i3@L2092-L2095
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.8@L2496-L2520
CONTRACT_ID: I.4.2.r3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ∇_{β_c} := Σ_{x,y}ℙ_{β_c}(0↔x)ℙ_{β_c}(x↔y)ℙ_{β_c}(y↔0) < ∞
SOURCE_QUANTIFIERS: the fixed model satisfying this alternative; the parent proposition's moment limit is as r tends to infinity
SOURCE_CONCLUSION: one admissible hypothesis under which the asymptotic of I.4.2 holds
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c3,hutchcroft.a.triangle
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.2.a
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex24@L1075-L1085 (Lemma I.4.11) with Lemma I.4.12 Discharged by the averaged triangle bound ℰ_{1,r} ≤ |B_r|^{−1}Σ_{x∈B_r}∇(0,x) plus ∇_r → 0. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. HYPOTHESIS OWNERSHIP: the condition(s) named in SOURCE_HYPOTHESES are now DEPS (hutchcroft.a.triangle). Previously they were reachable only through the merged file-level STANDING_ASSUMPTIONS declaration, which turned a hypothesis of this one route into a premise of the whole packet. No (HD) case route reaches this record, so these conditions are not imported into the (HD) branches. SCOPING REPAIR: this alternative consumes only case c3 and neutral glue, not the all-cases assembly s1.
EDGE: hutchcroft.i.4.2.c3 | .scratch/source/paper.html#S4.SS1.8@L2496-L2520 | the route is the packaging of this one case derivation plus the assembly step; it does not restate the case's own lemma dependencies
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.I1.i3@L2092-L2095 | the alternative this route selects IS this condition record: the hypothesis belongs to the route that assumes it, not to the file-level standing assumptions

NODE: hutchcroft.i.4.2.r4
KIND: route
TITLE: Prop I.4.2 second conclusion, alternative A — d > 3α gives log-integrability of H_r
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex5@L2106-L2112
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.r4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d > 3α
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: H_r is a logarithmically integrable error function
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c4
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.2.b
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.4.1@L1108-L1110 Kept separate from r1 because it qualifies a different conclusion. Case 2 (d=3α+Hydro) is deliberately absent: the paper claims no log-integrability there (Remark I.4.4). COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SCOPING REPAIR: this alternative consumes only case c4 and neutral glue, not the all-cases assembly s1.
EDGE: hutchcroft.i.4.2.c4 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the route is the packaging of this one case derivation plus the assembly step; it does not restate the case's own lemma dependencies

NODE: hutchcroft.i.4.2.r5
KIND: route
TITLE: Prop I.4.2 second conclusion, alternative B — triangle condition + ∇_r log-integrable
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex5@L2106-L2112
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.r5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition holds **and** r ↦ ∇_r := sup_{‖x‖≥r}∇_{β_c}(0,x) is logarithmically integrable
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: H_r is a logarithmically integrable error function
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c5,hutchcroft.a.triangle,hutchcroft.a.logint
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.2.b
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.4.1@L1108-L1110 A genuine conjunction *inside one source item*; recorded as one route because the source states it as one, not because conjunction has been licensed. r5 is what Lemma I.4.3 verifies under (HD) 2/3. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. DIRECTION CORRECTION: Lemma I.4.3 is not a prerequisite of this conditional route. An application below records where the lemma verifies its hypothesis under (HD)2/3. HYPOTHESIS OWNERSHIP: the condition(s) named in SOURCE_HYPOTHESES are now DEPS (hutchcroft.a.triangle, hutchcroft.a.logint). Previously they were reachable only through the merged file-level STANDING_ASSUMPTIONS declaration, which turned a hypothesis of this one route into a premise of the whole packet. No (HD) case route reaches this record, so these conditions are not imported into the (HD) branches. SCOPING REPAIR: this alternative consumes only case c5 and neutral glue, not the all-cases assembly s1.
EDGE: hutchcroft.i.4.2.c5 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the route is the packaging of this one case derivation plus the assembly step; it does not restate the case's own lemma dependencies
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.Thmthm2.p1.3@L2105-L2105 | the alternative this route selects IS this condition record: the hypothesis belongs to the route that assumes it, not to the file-level standing assumptions
EDGE: hutchcroft.a.logint | .scratch/source/paper.html#S4.Thmthm2.p1.3@L2105-L2105 | the alternative this route selects IS this condition record: the hypothesis belongs to the route that assumes it, not to the file-level standing assumptions

NODE: hutchcroft.i.4.3
KIND: lemma
TITLE: Lemma I.4.3 — (HD) cases 2 and 3 imply logarithmic integrability of ∇_r
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm3@L2119-L2124
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.11@L2566-L2621
CONTRACT_ID: I.4.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Case 2 or Case 3 of the (HD) list holds (XSLICE:HD-r2, XSLICE:HD-r3)
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: r ↦ ∇_r is logarithmically integrable
CONSTANT_SCOPE: implicit constants depend on d, α, J and on the exponents a,b,â,b̂ of the convolution bound
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.3.s1,hutchcroft.i.4.3.s2,hutchcroft.i.4.3.s3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Thmthm14.2@L1115-L1137 "Case 2/3" here means the (HD) cases 2/3, not Prop I.4.2's cases 2/3 — the same numerals label two different enumerations in adjacent paragraphs (§5.7). Case 3's hypothesis is the registered `hd-log-singularity` item; this lemma's own displays use log(1+‖x‖)/log(2+‖x‖), so the defect does not propagate into the conclusion (§5.6). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.3.s1 | .scratch/source/paper.html#S4.SS1.p26.1@L2569-L2569 | packet relation requires: Case 2 of the proof  [was E109]
EDGE: hutchcroft.i.4.3.s2 | .scratch/source/paper.html#S4.E12@L2580-L2589 | packet relation requires: the convolution lemma proved in Case 3  [was E110]
EDGE: hutchcroft.i.4.3.s3 | .scratch/source/paper.html#S4.E13@L2610-L2617 | packet relation requires: Case 3 conclusion  [was E111]

NODE: hutchcroft.i.4.4
KIND: claim
TITLE: Remark I.4.4 (source calls it a Remark) — H_r is not logarithmically integrable when d = 3α < 6
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm4@L2125-L2130
PROOF_SOURCE: .scratch/source/paper.html#S4.Thmthm4@L2125-L2130
CONTRACT_ID: I.4.4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α < 6
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: H_r fails to be a logarithmically integrable error function
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:PAPER-III [needed: third paper of the series (Remark I.4.4 and the logarithmic corrections)] PACKET PROOF_SOURCE: none in this paper (forward pointer) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:PAPER-III` (statements and use sites in §4). Delimits Prop I.4.2: it is not a defect of I.4.2 and it is not used by any node of this slice. Proof is deferred outside this paper (a second/third-paper statement); recorded as an unresolved external input, not proved here. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. CITATION-ONLY: the actual remark asserts the fact with a forward reference to LRP III; this locator is not a proof in Paper I and does not make the third-party result verified or proved.

NODE: hutchcroft.i.4.5
KIND: lemma
TITLE: Lemma I.4.5 — the asymptotic ODE f′ ≈ A r^{−α−1} f² (three items, including the exact solution)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm5@L2174-L2201
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.2@L2202-L2217
CONTRACT_ID: I.4.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f : (0,∞) → (0,∞) differentiable; A, α, r_0 > 0; item 3: h : (0,∞) → ℝ bounded measurable
SOURCE_QUANTIFIERS: item 1: every r ≥ r_0; items 2,3: every r ≥ r_0 resp. every r > 0, plus f(r) → ∞
SOURCE_CONCLUSION: 1. f′ ≥ A r^{−α−1}f² on [r_0,∞) ⇒ f(r) ≤ A^{−1}α r^α there; 2. f → ∞ and f′ ≤ A r^{−α−1}f² ⇒ f(r) ≥ A^{−1}α r^α; 3. f → ∞ and f′ = A(1−h) r^{−α−1} f² ⇒ f(r) = (α/A) r^α (1 − α r^α ∫_r^∞ h(s)s^{−α−1}ds)^{−1} for every r > 0
CONSTANT_SCOPE: only A, α; no implicit constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.g4
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p8.1@L923-L929 Checked by hand (both directions of the 1/f identity and the two limit alternatives); item 3 needs boundedness of h for the integral to converge and needs f>0 on all of (0,∞), which is the source's own "no blow-up" caution (recorded as g4). Item 3 also gives uniqueness, which is what makes (I.4.7) an identity rather than a bound. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.g4 | .scratch/source/paper.html#S4.SS1.p4.1@L2171-L2172 | packet relation requires: the paper's own caution: the lemma implicitly assumes f does not blow up  [was E018]

NODE: hutchcroft.i.4.6
KIND: lemma
TITLE: Lemma I.4.6 — |B_r| = r^d ± O(r^{d−1})
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm6@L2236-L2241
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.3@L2242-L2250
CONTRACT_ID: I.4.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: unit-Lebesgue-volume normalization of the ‖·‖-unit ball from (∗)
SOURCE_QUANTIFIERS: r → ∞ (proof: r ≥ 1)
SOURCE_CONCLUSION: |B_r| = r^d ± O(r^{d−1})
CONSTANT_SCOPE: the O(·) constant is the ‖·‖-diameter C of [0,1]^d, hence depends only on d and the norm
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.3 [needed: Definition I.1.3: kernel J, |J'(r)| = C(1+δ_r)r^{−d−α−1}, normalization (∗)] PACKET PROOF_SOURCE: P#S4.SS1.p10.1@L941-L943 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.3` (statements and use sites in §4). The proof's box partition gives (r−C)^d ≤ |B_r| ≤ (r+C)^d for r ≥ 1; the printed last line writes "B_r" for "|B_r|" (harmless). This is the only place where the unit-volume normalization is consumed quantitatively, via 1−ℰ_{0,r} = |J′(r)||B_r|/r^{−α−1}. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.7
KIND: lemma
TITLE: Lemma I.4.7 — two-sided bound on the first-moment error ℰ_{1,r}
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm7@L2254-L2267
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.4@L2268-L2282
CONTRACT_ID: I.4.7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: β = β_c, r > 0; ℰ_{1,r} as defined in display (I.4.5)
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: 0 ≤ ℰ_{1,r} ≤ 𝔼_{β_c,r}[|K|²|K∩B_r|] / (|B_r|(𝔼_{β_c,r}|K|)²)
CONSTANT_SCOPE: no constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp5,hutchcroft.i.4.7.s1
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.1 [needed: Lemma I.2.1: two-cluster correlation inequality, display 0 ≤ P(x↔y)P(z↔w) − P(x↔y↮z↔w) ≤ P(x↔y↔z↔w) (L421)] PACKET PROOF_SOURCE: P#S4.Thmthm9.p1.2.1@L955-L961 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.1` (statements and use sites in §4). Both halves re-derived: the lower half is Lemma I.2.1(c)(lower) applied to F=|K|, G=|K_y| summed over y∈B_r; the upper half additionally uses |K_y| = |K| on {0↔y}. Corollary I.4.8's `E_{1,r} ≤ 1` comes from the *lower* half (see i.4.2.s2). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp5 | .scratch/source/paper.html#S4.Thmthm7@L2254-L2267 | packet relation requires: Lemma I.4.7 is stated in terms of the ℰ_{1,r} defined in (I.4.5)  [was E020]
EDGE: hutchcroft.i.4.7.s1 | .scratch/source/paper.html#S4.SS1.4@L2268-L2282 | Lemma I.4.7 owns the covariance-sandwich proof; edge is not a proof dependency on the completed lemma by its own step

NODE: hutchcroft.i.4.8
KIND: corollary
TITLE: Corollary I.4.8 — unconditional lower bound lim inf r^{−α}𝔼_{β_c,r}|K| ≥ α/β_c
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm8@L2286-L2291
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p10@L2283-L2285
CONTRACT_ID: I.4.8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none beyond Definition I.1.3/I.1.5 (no condition on d, α)
SOURCE_QUANTIFIERS: r → ∞ (lim inf)
SOURCE_CONCLUSION: liminf_{r→∞} r^{−α}𝔼_{β_c,r}|K| ≥ α/β_c
CONSTANT_SCOPE: α/β_c explicit
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.7,hutchcroft.i.4.2.s2,hutchcroft.i.4.5,hutchcroft.i.4.g3,hutchcroft.i.4.dsp6,hutchcroft.i.4.8.s1
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex12@L963-L967 The one-line source justification ("ℰ_{1,r} ≥ 0 and ℰ_{0,r} → 0") omits that the ODE comparison needs 1−Ē_{1,r} ≤ 1, hence ℰ_{1,r} ≤ 1 and (eventually) ℰ_{0,r} ∈ [0,1]; and needs 𝔼_{β_c,r}|K| → ∞ for item 2 of Lemma I.4.5. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. The lower-bound proof is reconstructed from the ODE ingredients rather than claimed as printed; no unconditional proof status follows.
EDGE: hutchcroft.i.4.2.s2 | .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284 | packet relation requires: the ODE comparison needs 1−Ē_{1,r} ≤ 1, i.e. ℰ_{1,r} ≤ 1, which is not stated here  [was E024]
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.Thmthm8.p1.1@L2289-L2289 | RECONSTRUCTED SOURCE-GAP application: Corollary I.4.8 does not print this use of the named ODE hypothesis; proof must supply it
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284 | packet relation requires: "the fact that ℰ_{1,r} is non-negative"  [was E023]
EDGE: hutchcroft.i.4.dsp6 | .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284 | packet relation requires: the ODE being compared is (I.4.6)  [was E131]
EDGE: hutchcroft.i.4.g3 | .scratch/source/paper.html#S4.Thmthm8@L2286-L2291 | RECONSTRUCTED SOURCE-GAP application: Corollary I.4.8 does not print this use of the named ODE hypothesis; proof must supply it
EDGE: hutchcroft.i.4.8.s1 | .scratch/source/paper.html#S4.SS1.p10@L2283-L2285 | RECONSTRUCTED proof assembly for the corollary, whose print contains no full proof. Step is conditional on the explicit ODE ingredients, not a free assumption

NODE: hutchcroft.i.4.9
KIND: lemma
TITLE: Lemma I.4.9 — d > 3α: β-uniform first-moment and error bounds by bootstrap
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm9@L2295-L2308
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.9
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d > 3α
SOURCE_QUANTIFIERS: ∃ r_0 < ∞ such that for every r ≥ r_0 (β-uniformity over β ∈ [β_c/2, β_c) is produced by the proof, not stated)
SOURCE_CONCLUSION: 𝔼_{β_c,r}|K| ≤ (2α/β_c) r^α and ℰ_{1,r} ≤ (16α³/β_c³) r^{3α−d} for every r ≥ r_0; in particular Ē_{1,r} is logarithmically integrable
CONSTANT_SCOPE: 2α/β_c and 16α³/β_c³ explicit; r_0 = (32C)^{1/(d−3α)} is not explicit and depends on the tree-graph constant C
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.1,hutchcroft.i.4.7,hutchcroft.i.4.dsp8,hutchcroft.i.4.9.s1,hutchcroft.i.4.9.s4
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p13.6.1@L981-L1017 Checked: the self-referential threshold closes. If r_0(β) > (32C)^{1/(d−3α)} then the admissible set is [s,∞) with s = (32C)^{1/d}r_0^{3α/d} < r_0, contradicting minimality of r_0; hence r_0(β) ≤ (32C)^{1/(d−3α)}, uniformly in β. One printed intermediate ("r_0 ≥ (32C)^{1/d}r_0^{3α/d}") is a reversed inequality (§5.8), not an equality case or the step carrying the conclusion. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SOURCE_CORRECTION: the printed '(I.4.15)' cross-reference at tex L983 is dangling/misnumbered: display I.4.15 is defined later for second moments. The first-moment replay is a reconstructed source interpretation, not literal fidelity by relabelling. General-beta covariance replay is likewise labelled, not silently donated as a printed use.
EDGE: hutchcroft.i.4.1 | .scratch/source/paper.html#S4.Ex12@L2317-L2323 | RECONSTRUCTION / PRINTED CROSS-REFERENCE: tex L983 says (I.4.15), later used for the second moment; the replay required here is the p=1 identity (I.4.1). This is a source gap, not a verified link to display I.4.15
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.Ex12@L2317-L2323 | RECONSTRUCTION / SOURCE-GAP: covariance sandwich replay at general beta; not a printed application of Lemma I.4.7, whose statement is at beta_c
EDGE: hutchcroft.i.4.9.s1 | .scratch/source/paper.html#S4.SS1.p13.1@L2315-L2316 | packet relation requires: replay of the identity at general β  [was E112]
EDGE: hutchcroft.i.4.9.s4 | .scratch/source/paper.html#S4.SS1.p14.1@L2388-L2388 | packet relation requires: bootstrap conclusion  [was E113]
EDGE: hutchcroft.i.4.dsp8 | .scratch/source/paper.html#S4.E8@L2341-L2348 | packet relation requires: (I.4.8) is the tree-graph error bound used by the bootstrap  [was E029]

NODE: hutchcroft.i.4.10
KIND: lemma
TITLE: Lemma I.4.10 — d = 3α and (Hydro) ⇒ ℰ_{1,r} → 0
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm10@L2390-L2395
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.6@L2396-L2428
CONTRACT_ID: I.4.10
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α and (Hydro)
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: ℰ_{1,r} → 0
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.10.s1,hutchcroft.i.4.10.s2
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.14 [needed: Definition I.1.14 (Hydro): M_r is the edian of |K_max(B_r)| under P_{β_c,r}, and (Hydro) is M_r = o(r^{(d+α)/2})] PACKET PROOF_SOURCE: P#S4.SS1.p17.1@L1023-L1039 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.14` (statements and use sites in §4). The only consumer of M_r in this slice, and the only place where the exponent (d+α)/2 is matched against the Cauchy–Schwarz exponent. No rate is claimed, only convergence. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.10.s1 | .scratch/source/paper.html#S4.SS1.p15.1@L2399-L2399 | packet relation requires: Cauchy–Schwarz step  [was E114]
EDGE: hutchcroft.i.4.10.s2 | .scratch/source/paper.html#S4.Ex19@L2418-L2424 | packet relation requires: ψ-iteration step  [was E115]

NODE: hutchcroft.i.4.11
KIND: lemma
TITLE: Lemma I.4.11 — triangle-diagram bound on the first-moment error
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm11@L2432-L2437
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.8@L2496-L2520
CONTRACT_ID: I.4.11
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none beyond Definition I.1.3/I.1.5
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: ℰ_{1,r} ≤ |B_r|^{−1} Σ_{x∈B_r} ∇(0,x), with ∇ = ∇_{β_c} the open triangle
CONSTANT_SCOPE: no constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.12,hutchcroft.i.4.11.s1,hutchcroft.i.4.11.s2
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex24@L1075-L1085 Its proof is placed after Lemma I.4.12 in the source (statement first, auxiliary lemma, then proof); the dependency is on I.4.12, not the reverse. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.11.s1 | .scratch/source/paper.html#S4.SS1.p20.1@L2499-L2499 | packet relation requires: rewriting step  [was E116]
EDGE: hutchcroft.i.4.11.s2 | .scratch/source/paper.html#S4.Ex23@L2510-L2516 | packet relation requires: final step  [was E117]
EDGE: hutchcroft.i.4.12 | .scratch/source/paper.html#S4.SS1.p20.3@L2509-L2509 | packet relation requires: "applying Lemma I.4.12 we obtain that"  [was E047]

NODE: hutchcroft.i.4.12
KIND: lemma
TITLE: Lemma I.4.12 — five-point insertion inequality with the doorway/exclusion event
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm12@L2441-L2456
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.7@L2460-L2495
CONTRACT_ID: I.4.12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as printed: "every x,y,z ∈ Z^d and every β, r ≥ 0", while the display carries ℙ_{β_c,r} throughout (§5.3)
SOURCE_QUANTIFIERS: every x,y,z ∈ Z^d; every β, r ≥ 0 as printed
SOURCE_CONCLUSION: ℙ_{β_c,r}(0↔x)ℙ_{β_c,r}(y↔z) − ℙ_{β_c,r}(0↔x↮y↔z) ≤ Σ_{a,b}ℙ_{β_c,r}(0↔a)ℙ_{β_c,r}(a↔x)ℙ_{β_c,r}(a↔b)ℙ_{β_c,r}(y↔b)ℙ_{β_c,r}(b↔z)
CONSTANT_SCOPE: no constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.12.s1,hutchcroft.i.4.12.s2,hutchcroft.i.4.12.s3,hutchcroft.i.4.12.s4
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.BK [needed: BK inequality as stated in Subsection I.2.1, including its infinite-edge footnote] ; XSLICE:I.2.1 [needed: Lemma I.2.1: two-cluster correlation inequality, display 0 ≤ P(x↔y)P(z↔w) − P(x↔y↮z↔w) ≤ P(x↔y↔z↔w) (L421)] PACKET PROOF_SOURCE: P#S4.Thmthm13.2@L1065-L1073 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.BK`, `XSLICE:I.2.1` (statements and use sites in §4). Registered errata item `two-cluster-fresh-copy-exclusion` (proof, not statement): the printed closing identity omits the case y ∈ K_0, whose exact missing contribution is computed in §5.1 and is dominated by the same five-factor sum. Do not cite the printed factorization; do not re-assert the withdrawn y=0,z=x "witness". Status of the statement: **open at proof level**, not refuted. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SCOPE WATCH: the print quantifies generally over beta while the display is evaluated at P_{beta_c,r}; keep that binder mismatch explicit instead of silently repairing it.
EDGE: hutchcroft.i.4.12.s1 | .scratch/source/paper.html#S4.SS1.p19.1@L2463-L2463 | packet relation requires: the coupling  [was E118]
EDGE: hutchcroft.i.4.12.s2 | .scratch/source/paper.html#S4.Ex20@L2466-L2470 | packet relation requires: union bound and BK  [was E119]
EDGE: hutchcroft.i.4.12.s3 | .scratch/source/paper.html#S4.Ex22@L2476-L2480 | packet relation requires: tree-graph insertion  [was E120]
EDGE: hutchcroft.i.4.12.s4 | .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491 | packet relation requires: the closing identity (§5.1: invalid as printed)  [was E121]

NODE: hutchcroft.i.4.13
KIND: lemma
TITLE: Lemma I.4.13 — logarithmic integrability preserved by two integral transforms
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm13@L2524-L2529
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.9@L2533-L2555
CONTRACT_ID: I.4.13
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h : (0,∞) → ℝ a logarithmically integrable error function; a > 0
SOURCE_QUANTIFIERS: every a > 0; r → ∞
SOURCE_CONCLUSION: r ↦ r^a∫_r^∞ s^{−a−1}h(s)ds and r ↦ r^{−a}∫_1^r s^{a−1}h(s)ds are logarithmically integrable error functions
CONSTANT_SCOPE: the Tonelli bounds are (1/a)∫|h(s)|ds/s; no other constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.13.s1,hutchcroft.i.4.13.s2
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.10 [needed: Lemma I.2.10: regularly varying integral asymptotics (negative-index half carries the registered constant error)] PACKET PROOF_SOURCE: P#S4.SS1.p26.1.1@L1096-L1110 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.10` (statements and use sites in §4). Both Tonelli computations re-derived and agree with the printed constants. The trailing parenthetical invokes Lemma I.2.10 on the *negative*-index half (s ↦ s^{−a−1}h(s) has index −a−1 < −1); the registered `karamata-negative-index-tail` constant error changes the multiple there, not the conclusion (§5.9). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.13.s1 | .scratch/source/paper.html#S4.SS1.9@L2533-L2555 | packet relation requires: first half of the proof  [was E132]
EDGE: hutchcroft.i.4.13.s2 | .scratch/source/paper.html#S4.Ex25@L2545-L2551 | packet relation requires: second half of the proof  [was E133]

NODE: hutchcroft.i.4.14
KIND: corollary
TITLE: Corollary I.4.14 — (HD) implies the hydrodynamic condition
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm14@L2625-L2630
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.12@L2631-L2663
CONTRACT_ID: I.4.14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of the three (HD) hypotheses holds
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: (Hydro) holds, i.e. M_r = o(r^{(d+α)/2})
CONSTANT_SCOPE: implicit constants only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2,hutchcroft.i.4.14.s1,hutchcroft.i.4.14.s2,ext.grimmett699
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.6 [needed: Lemma I.2.6: E_{β,r}|K|^p ≥ (M_{β,r}−1)^{p+1}/(e|B_r|)] ; XSLICE:I.2.13 [needed: Theorem I.2.13: spatially averaged two-point bound Σ_{x∈B_r}P_{β_c}(0↔x) ⪯ r^α] ; XSLICE:I.1.14 [needed: Definition I.1.14 (Hydro): M_r is the edian of |K_max(B_r)| under P_{β_c,r}, and (Hydro) is M_r = o(r^{(d+α)/2})] PACKET PROOF_SOURCE: P#S4.SS2.2@L1145-L1159 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.6`, `XSLICE:I.2.13`, `XSLICE:I.1.14` (statements and use sites in §4). Carries source defect §5.2 (printed exponent r^{−d} must be r^{+d}); if the coordinator rejects the boundary extension, delete exactly this node plus i.4.14.s1, i.4.14.s2, ext.grimmett699 and edges E140-E142, E146: nothing in I.4.1–I.4.13 depends on it. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. REFERENCE-TARGET CORRECTION (read off the primary HTML): the parenthetical (I.1.3) is the hyperlink `#S1.SS3` at paper.html L555, L2117, L2128 and L3373, i.e. the SUBSECTION §I.1.3, not display (I.1.3) = `S1.E3@L452`. There is no printed slip to correct here; the expansion is §I.1.3. The printed '(I.1.14)' is not the Definition (Hydro); the intended condition is Definition I.1.14 at S1.Thmthm14, distinct from display S1.E14. These interpretations are recorded explicitly, not silently treated as literal source-variable substitutions or new source errata.
EDGE: ext.grimmett699 | .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634 | packet relation requires: tail bound cited as [55, Eq. 6.99]  [was E136]
EDGE: hutchcroft.i.4.14.s1 | .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634 | packet relation requires: tail bound and union bound  [was E122]
EDGE: hutchcroft.i.4.14.s2 | .scratch/source/paper.html#S4.Ex31@L2653-L2659 | packet relation requires: Lemma I.2.6 route  [was E123]
EDGE: hutchcroft.i.4.2 | .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634 | packet relation requires: "It follows from Proposition I.4.2 and the tree-graph inequality"  [was E084]

NODE: hutchcroft.i.4.msm
KIND: display
TITLE: displays (I.4.2)–(I.4.3) — mass-transport principle on Z^d
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p2@L2005-L2029
PROOF_SOURCE: -
CONTRACT_ID: I.4.2-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F : (Z^d)² → [0,∞] with F(x+z,y+z) = F(x,y) for all x,y,z; (k-fold version) F : (Z^d)^k → [0,∞] translation invariant
SOURCE_QUANTIFIERS: all x,y,z ∈ Z^d, all k; sums over Z^d, allowed to be +∞
SOURCE_CONCLUSION: Σ_x F(0,x) = Σ_x F(0,−x) = Σ_x F(x,0); and the k coincident sums
CONSTANT_SCOPE: no constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - Non-negativity is what makes the (possibly infinite) sums Tonelli-legal; a consumer that drops F ≥ 0 or translation invariance is unjustified. Applied at i.4.1.s2. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.dsp4
KIND: display
TITLE: display (I.4.4) — the mean-field approximation to the p-th moment ODE (a *target*, not a result)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E4@L2064-L2068
PROOF_SOURCE: -
CONTRACT_ID: I.4.4d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p ≥ 1; evaluated at β = β_c; validity requires asymptotic independence of the two endpoint clusters, which the paper asserts above the critical dimension
SOURCE_QUANTIFIERS: r → ∞ for each integer p ≥ 1
SOURCE_CONCLUSION: (d/dr)𝔼_{β_c,r}|K|^p ∼ β_c r^{−α−1}Σ_{ℓ=0}^{p−1}C(p,ℓ)𝔼_{β_c,r}|K|^{ℓ+1}𝔼_{β_c,r}|K|^{p−ℓ}
CONSTANT_SCOPE: leading constant β_c explicit; "∼" constant 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: none in I.4.1 UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Target display. This slice supplies the p = 1 instance (Prop I.4.2) and the log-integrability machinery; the p ≥ 2 instances belong to the second-moment slice (XSLICE:I.4.15, XSLICE:I.4.20) and are not extracted here. The paper's own validity restriction (valid above d_c; valid but with slowly decaying errors when d_eff = d_c = 6 and d < 6) belongs to the display and must travel with it. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.dsp5
KIND: display
TITLE: display (I.4.5) and the definition of the first-moment error ℰ_{1,r}
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E5@L2133-L2140
PROOF_SOURCE: -
CONTRACT_ID: I.4.5d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p = 1 instance of (I.4.1) at β = β_c
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: (d/dr)𝔼_{β_c,r}|K| = β_c|J′(r)|𝔼_{β_c,r}[Σ_{y∈B_r}1(y∉K)|K||K_y|] = (1−ℰ_{1,r})β_c|J′(r)||B_r|(𝔼_{β_c,r}|K|)², with ℰ_{1,r} := [|B_r|(𝔼|K|)² − 𝔼[|K|Σ_{y∈B_r}1(y∉K)|K_y|]]/(|B_r|(𝔼|K|)²) = [|B_r|(𝔼|K|)² − 𝔼[|K|Σ_{y∈B_r}|K_y|] + 𝔼[|K|²|K∩B_r|]]/(|B_r|(𝔼|K|)²)
CONSTANT_SCOPE: no constant beyond β_c, |J′(r)|, |B_r|
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.1
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: instance of I.4.1 at p=1 UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied The second form of ℰ_{1,r} is an exact rewriting, not an assumption: on {y ∈ K}, K_y = K so |K_y| = |K|, hence 𝔼[|K|Σ_{y∈B_r}1(y∈K)|K_y|] = 𝔼[|K|²|K∩B_r|]. Verified. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.1 | .scratch/source/paper.html#S4.E5@L2133-L2140 | packet relation requires: "we first rewrite the p = 1 case of the equality (I.4.1)"  [was E011]

NODE: hutchcroft.i.4.dsp6
KIND: display
TITLE: definitions of ℰ_{0,r}, Ē_{1,r} and display (I.4.6)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E6@L2160-L2167
PROOF_SOURCE: -
CONTRACT_ID: I.4.6d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ℰ_{0,r} measures the deviation of |J′(r)||B_r| from r^{−α−1} under (∗)
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: (1−ℰ_{0,r}) := |J′(r)||B_r|/r^{−α−1}; (1−Ē_{1,r}) := (1−ℰ_{1,r})(1−ℰ_{0,r}); hence (d/dr)𝔼_{β_c,r}|K| = (1−Ē_{1,r})β_c r^{−α−1}(𝔼_{β_c,r}|K|)²
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp5,hutchcroft.i.4.6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: definitions UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied ℰ_{0,r} carries the whole normalization (∗). From (∗)+I.4.6 one gets 1−ℰ_{0,r} = 1+δ_r+O(1/r), and δ_r + O(1/r) is a log-integrable error function, so ℰ_{0,r} → 0 and ℰ_{0,r} is log-integrable. That computation is *not* in the source at this site (recorded as g3 below, with the check supplied). COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. LOCATOR OWNERSHIP: S4.E6@L2160-L2167 is display (I.4.6), not (I.4.7). The definitions of the two errors are the separate unnumbered display S4.Ex6@L2152-L2158. There is no conflation of these two objects or with the following S4.E7.
EDGE: hutchcroft.i.4.6 | .scratch/source/paper.html#S4.SS1.p6.2@L2228-L2234 | packet relation requires: log-integrability of ℰ_{0,r} is asserted from (∗) together with Lemma I.4.6  [was E014]
EDGE: hutchcroft.i.4.dsp5 | .scratch/source/paper.html#S4.Ex6@L2152-L2158 | packet relation requires: (1−Ē_{1,r}) := (1−ℰ_{1,r})(1−ℰ_{0,r})  [was E013]

NODE: hutchcroft.i.4.dsp7
KIND: display
TITLE: display (I.4.7) — the exact integral identity for the first moment
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E7@L2220-L2227
PROOF_SOURCE: -
CONTRACT_ID: I.4.7d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 𝔼_{β_c}|K| = ∞ (so f(r) → ∞) and (I.4.6) with bounded measurable error Ē_{1,r}
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: 𝔼_{β_c,r}|K| = (α/β_c) r^α (1 − α r^α ∫_r^∞ Ē_{1,s}s^{−α−1}ds)^{−1}; in particular 𝔼_{β_c,r}|K| ∼ (α/β_c)r^α iff Ē_{1,r} → 0
CONSTANT_SCOPE: α/β_c explicit
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.5,hutchcroft.i.4.dsp6,hutchcroft.i.4.g3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: from I.4.6 + Lemma I.4.5 item 3 UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied The pivot of the slice: every case of Prop I.4.2 is reduced to a statement about Ē_{1,r}. The "if and only if" needs uniqueness of the exact solution (I.4.5 item 3), not just the two-sided bounds. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219 | packet relation requires: "it follows from Lemma I.4.5 and (I.4.6) that the identity … holds"  [was E015]
EDGE: hutchcroft.i.4.dsp6 | .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219 | packet relation requires: (I.4.6) is the ODE to which item 3 of Lemma I.4.5 is applied  [was E016]
EDGE: hutchcroft.i.4.g3 | .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219 | packet relation requires: "Since 𝔼_{β_c}∣K∣ = ∞" is the hypothesis f(r) → ∞ of item 3  [was E017]

NODE: hutchcroft.i.4.dsp8
KIND: display
TITLE: display (I.4.8) — tree-graph bound on the β-dependent error ℰ_{1,r,β}
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E8@L2341-L2348
PROOF_SOURCE: -
CONTRACT_ID: I.4.8d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: β ∈ [β_c/2, β_c]; (I.2.3) at p = 3; |B_r| ⪰ r^d
SOURCE_QUANTIFIERS: all β_c/2 ≤ β ≤ β_c and all r ≥ 1
SOURCE_CONCLUSION: ℰ_{1,r,β} ≤ 𝔼_{β,r}[|K|³]/(|B_r|(𝔼_{β,r}|K|)²) ≤ 3(𝔼_{β,r}|K|)³/|B_r| ⪯ r^{3α−d}(𝔼_{β,r}|K|/((α/β)r^α))³
CONSTANT_SCOPE: 3 = (2·3−3)!!; the ⪯ constant depends only on d, α, J and is uniform in β
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.7,hutchcroft.i.4.6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.3 [needed: display (I.2.3): E|K|^p ≤ (2p−3)!!(E|K|)^{2p−1}] PACKET PROOF_SOURCE: tree-graph (I.2.3) at p = 3 UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.3` (statements and use sites in §4). Checked, no erratum: (I.2.3) at p = 3 gives 𝔼|K|³ ≤ 3(𝔼|K|)^5, and dividing by (𝔼|K|)² produces exactly the printed 3(𝔼|K|)³. The β-uniformity of the ⪯ constant is the whole point of the display. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.6 | .scratch/source/paper.html#S4.E8@L2341-L2348 | packet relation requires: ∣B_r∣ ⪰ r^d converts the middle term into r^{3α−d}  [was E097]
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.E8@L2341-L2348 | RECONSTRUCTION: replaying the covariance bound at general beta together with tree-graph gives (I.4.8), not the verbatim beta_c statement of Lemma I.4.7

NODE: hutchcroft.i.4.dsp9
KIND: display
TITLE: display (I.4.9) — Cauchy–Schwarz bound on 𝔼[|K|²|K∩B_r|]
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E9@L2400-L2407
PROOF_SOURCE: -
CONTRACT_ID: I.4.9d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α; r > 0
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: 𝔼_{β_c,r}[|K|²|K∩B_r|] ≤ (𝔼_{β,r}[|K|⁴]·𝔼_{β_c,r}[|K∩B_r|²])^{1/2} ⪯ ((𝔼_{β,r}|K|)^7 r^α M_r)^{1/2}
CONSTANT_SCOPE: implicit constant only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.5 [needed: Corollary I.2.5: E|K∩W|^{p+q} ⪯ M(W)^q E|K∩W|^p] ; XSLICE:I.2.13 [needed: Theorem I.2.13: spatially averaged two-point bound Σ_{x∈B_r}P_{β_c}(0↔x) ⪯ r^α] ; XSLICE:I.2.3 [needed: display (I.2.3): E|K|^p ≤ (2p−3)!!(E|K|)^{2p−1}] PACKET PROOF_SOURCE: C–S + Cor. I.2.5 + Thm I.2.13 + tree-graph UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.5`, `XSLICE:I.2.13`, `XSLICE:I.2.3` (statements and use sites in §4). Mixed β/β_c inside the first factor is harmless: ℙ_{β,r} ≤ ℙ_{β_c,r} monotonically (β ≤ β_c), so 𝔼_{β,r}[|K|⁴] ≤ 𝔼_{β_c,r}[|K|⁴]. Silent monotone-comparison steps of this kind are listed as g7. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.6 | .scratch/source/paper.html#S4.E9@L2400-L2407 | packet relation requires: ∣B_r∣ ≍ r^d is used to pass to r^α M_r  [was E101]

NODE: hutchcroft.i.4.dsp10
KIND: display
TITLE: display (I.4.10) and the ψ-iteration
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E10@L2409-L2416
PROOF_SOURCE: -
CONTRACT_ID: I.4.10d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α; (Hydro); η : (0,∞) → (0,∞) continuous, decreasing, η(r) → 0
SOURCE_QUANTIFIERS: every 0 ≤ β ≤ β_c and r > 0
SOURCE_CONCLUSION: Ē_{1,r,β} ≤ η(r) r^{α/2} r^{(d+α)/4}(𝔼_{β,r}|K|)^{7/2}/(r^d(𝔼_{β,r}|K|)²) = η(r) r^{−3α/2}(𝔼_{β,r}|K|)^{3/2}; then ψ(r) := (cη(r))^{−2/3α}r and r_0(β) ≤ ψ^{−1}(r_0(β)) with ψ^{−1}(r)/r continuous, decreasing and → 0, so r_0(β) is bounded by the supremal solution of ψ^{−1}(r) = r, independently of β
CONSTANT_SCOPE: all implicit constants absorbed into η; the bound is uniform in β
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp9,hutchcroft.i.4.5
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.14 [needed: Definition I.1.14 (Hydro): M_r is the edian of |K_max(B_r)| under P_{β_c,r}, and (Hydro) is M_r = o(r^{(d+α)/2})] PACKET PROOF_SOURCE: from I.4.9 with M_r = o(r^{(d+α)/2}) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.14` (statements and use sites in §4). The three implications of the ψ display are asserted, not derived ("by the same ODE analysis carried out in the proof of that lemma") — recorded as g8. The uniform-endpoint closure β ↑ β_c is by monotone convergence. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.E10@L2409-L2416 | packet relation requires: the implication chain is an ODE comparison  [was E104]
EDGE: hutchcroft.i.4.dsp9 | .scratch/source/paper.html#S4.E10@L2409-L2416 | packet relation requires: (I.4.10) is (I.4.9) combined with M_r = o(r^{(d+α)/2})  [was E102]

NODE: hutchcroft.i.4.dsp11
KIND: display
TITLE: display (I.4.11) — ∇(0,x) ⪯ ‖x‖^{−d+6} under (HD) 2
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E11@L2570-L2577
PROOF_SOURCE: -
CONTRACT_ID: I.4.11d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) case 2 (d > 6 and ℙ_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}); τ(x) = ℙ_{β_c}(0↔x); ∇(0,x) = τ*τ*τ(x)
SOURCE_QUANTIFIERS: all x ∈ Z^d \ {0}
SOURCE_CONCLUSION: ∇(0,x) ⪯ ‖x‖^{−d+6}
CONSTANT_SCOPE: implicit constant depends on d, α, J
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.hara.prop1.7
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:HD-r2 [needed: (HD) 2: d > 6 and P_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}] PACKET PROOF_SOURCE: [63, Prop. 1.7] twice UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:HD-r2` (statements and use sites in §4). Summability is *not* needed and does not follow: what gives log-integrability of ∇_r ⪯ r^{−d+6} is ∫_1^∞ r^{−d+6}dr/r < ∞ ⟺ d > 6, not Σ_x‖x‖^{−d+6} < ∞ (the latter is false). This distinction is the step's content. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: ext.hara.prop1.7 | .scratch/source/paper.html#S4.E11@L2570-L2577 | packet relation requires: applied twice with a = b = 2  [was E106]

NODE: hutchcroft.i.4.dsp12
KIND: display
TITLE: display (I.4.12) — convolution bound with logarithmic corrections, two regimes
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E12@L2580-L2589
PROOF_SOURCE: -
CONTRACT_ID: I.4.12d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |f(x)| ⪯ (1+‖x‖)^{−d+a}(log(2+‖x‖))^{−â}, |g(x)| ⪯ (1+‖x‖)^{−d+b}(log(2+‖x‖))^{−b̂} with a,b > 0, â,b̂ ≥ 0, and (a+b < d) or (a+b = d and â+b̂ > 1)
SOURCE_QUANTIFIERS: all x ∈ Z^d
SOURCE_CONCLUSION: |f*g(x)| ⪯_{a,b,â,b̂} (1+‖x‖)^{−d+a+b}(log(2+‖x‖))^{−â−b̂} if a+b < d; and ⪯ (log(2+‖x‖))^{−â−b̂+1} if a+b = d
CONSTANT_SCOPE: constant may depend on a,b,â,b̂,d
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: three-region decomposition A_1,A_2,A_3 with box-boundary summation UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied No named external source is cited for this bound; the proof is given in the paper (A_1,A_2,A_3 regions). Its short-range input is the pointwise two-point bound, i.e. exactly the hypothesis the registered `hd-log-singularity` item repairs. Verified consistency: at a+b = d the polynomial factor is absent, which is why (I.4.13)'s ∇ bound has numerator 1. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.dsp13
KIND: display
TITLE: display (I.4.13) — the Case 3 (d = 6, α = 2) conclusions
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E13@L2610-L2617
PROOF_SOURCE: -
CONTRACT_ID: I.4.13d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) case 3; display (I.4.12) applied twice with a=b=2, â=b̂=1 (a+b = d = 6, â+b̂ = 2 > 1)
SOURCE_QUANTIFIERS: every x ∈ Z^d \ {0}
SOURCE_CONCLUSION: τ*τ(x) ⪯ ‖x‖^{−d+4}/(log(1+‖x‖))² and ∇(0,x) ⪯ 1/(log(1+‖x‖))²
CONSTANT_SCOPE: implicit constants only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp12
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:HD-r3 [needed: (HD) 3: d = 6, α = 2 and the logarithmic two-point bound; must be read in the repaired log(1+‖·‖) form (hd-log-singularity)] PACKET PROOF_SOURCE: i.4.3.s3 (I.4.12 applied twice) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:HD-r3` (statements and use sites in §4). Both text layers lose a closing parenthesis in the second inequality (PDF p.41 prints "1/(log(1+∥x∥)2"); the content is determined by the a+b = d branch of (I.4.12). Text-layer defect, not a mathematical erratum (§5.5). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp12 | .scratch/source/paper.html#S4.E13@L2610-L2617 | packet relation requires: (I.4.12) applied twice  [was E107]

NODE: hutchcroft.i.4.1.s1
KIND: step
TITLE: Russo's formula applied to the cut-off moment, with the derivative taken inside the expectation
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p3.1@L2033-L2033
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex1@L2036-L2040
CONTRACT_ID: I.4.1.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.1; plus the two recorded inputs g1, g2
SOURCE_QUANTIFIERS: inherits hutchcroft.i.4.1
SOURCE_CONCLUSION: (∂/∂r)𝔼_{β,r}|K|^p = β|J′(r)|𝔼_{β,r}[Σ_{x∈K}Σ_{y∈B_r(x)}1(y∉K)((|K|+|K_y|)^p − |K|^p)]
CONSTANT_SCOPE: inherits
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.russo,hutchcroft.i.4.g1,hutchcroft.i.4.g2
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1@L834-L846 The contribution of the edge {x,y} to the r-derivative is β|J′(r)|1(‖x−y‖≤r) times the *probability that it is closed*, and that factor is supplied inside the expectation by 1(y∉K) together with x∈K. Verified exactly in a two-vertex instance and numerically on C_8 (§5.4, §7): no missing (1−p) factor. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: ext.russo | .scratch/source/paper.html#S4.p3.1@L2033-L2033 | packet relation requires: "We have by Russo's formula [55, Section 2.4]"  [was E006]
EDGE: hutchcroft.i.4.g1 | .scratch/source/paper.html#S4.Ex1@L2036-L2040 | packet relation requires: the derivative is taken inside an expectation over a measure that itself depends on r  [was E007]
EDGE: hutchcroft.i.4.g2 | .scratch/source/paper.html#S4.p3.2@L2042-L2042 | packet relation requires: "a standard consequence of the sharpness of the phase transition" (infinite volume, β ≤ β_c)  [was E008]

NODE: hutchcroft.i.4.1.s2
KIND: step
TITLE: mass-transport rewrite: Σ_{x∈K}Σ_{y∈B_r(x)} ↦ |K|Σ_{y∈B_r}
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p3.2@L2042-L2042
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex2@L2045-L2049
CONTRACT_ID: I.4.1.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.1; translation invariance of the joint law; non-negativity (for Tonelli)
SOURCE_QUANTIFIERS: inherits
SOURCE_CONCLUSION: Σ_{x∈K}Σ_{y∈B_r(x)}1(y∉K)((|K|+|K_y|)^p−|K|^p) = |K|Σ_{y∈B_r}1(y∉K)((|K|+|K_y|)^p−|K|^p)
CONSTANT_SCOPE: inherits
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.msm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1@L834-L846 Checked exactly, on the nose, in four independent instances: C_8 with r = 1 (ratio 1.0000000000), C_9 with r = 2 at two values of p (1.0000000000, 1.0000000000), C_8 with r = 2 (1.0000000000), and the complete graph C_6 with summing ball r = 1 (1.000000, twice). So the identity is true in every case I could enumerate. What I could *not* do is derive it from the displayed mass-transport statements (I.4.2)–(I.4.3): those are two-point swap identities (Σ_x F(0,x) = Σ_x F(x,0)), whereas this step needs the "sum over the cluster = |K| times the anchored sum" form, which is stated nowhere. Classified as an unproved step with numerical support — not as a defect (§5.4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.msm | .scratch/source/paper.html#S4.p3.2@L2042-L2042 | packet relation requires: "We can use the mass-transport principle to rewrite this as"  [was E009]

NODE: hutchcroft.i.4.1.s3
KIND: step
TITLE: binomial expansion producing the ℓ-sum
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p3.3@L2056-L2057
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex3@L2050-L2054
CONTRACT_ID: I.4.1.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.1
SOURCE_QUANTIFIERS: inherits
SOURCE_CONCLUSION: (|K|+|K_y|)^p − |K|^p = Σ_{ℓ=0}^{p−1}C(p,ℓ)|K|^{ℓ+1}|K_y|^{p−ℓ}, and summing/expectation gives (I.4.1)
CONSTANT_SCOPE: binomial coefficients only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1@L834-L846 Purely algebraic; no independence of K and K_y is asserted or needed here (m7's note on measurability is correct but over-cautious: both are functions of the same configuration). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.7.s1
KIND: step
TITLE: covariance sandwich giving Lemma I.4.7
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex10@L2272-L2278
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.4@L2268-L2282
CONTRACT_ID: I.4.7.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.7; Lemma I.2.1 with F = |K|, G = |K_y|, then sum over y ∈ B_r
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: 0 ≤ 𝔼_{β_c,r}[|K|Σ_{y∈B_r}|K_y|] − |B_r|(𝔼|K|)² ≤ 𝔼_{β_c,r}[|K|²|K∩B_r|]
CONSTANT_SCOPE: inherits
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp5
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.1 [needed: Lemma I.2.1: two-cluster correlation inequality, display 0 ≤ P(x↔y)P(z↔w) − P(x↔y↮z↔w) ≤ P(x↔y↔z↔w) (L421)] PACKET PROOF_SOURCE: P#S4.Thmthm9.p1.2.1@L955-L961 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.1` (statements and use sites in §4). Two compressions the source hides in "a special case of Lemma I.2.1": (i) 𝔼|K_y| = 𝔼|K| by translation invariance; (ii) on {0↔y}, |K_y| = |K|, which turns Σ_{y∈B_r}𝔼[|K||K_y|1(0↔y)] into 𝔼[|K|²|K∩B_r|]. Both verified. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp5 | .scratch/source/paper.html#S4.E5@L2133-L2140 | packet relation requires: the ℰ_{1,r} whose sandwich is proved is (I.4.5)'s  [was E124]

NODE: hutchcroft.i.4.8.s1
KIND: step
TITLE: liminf lower bound from the one-sided ODE comparison
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284
CONTRACT_ID: I.4.8.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.8; ℰ_{1,r} ≥ 0 and ℰ_{1,r} ≤ 1 (from I.4.7), ℰ_{0,r} → 0 (I.4.6+(∗)), 𝔼_{β_c,r}|K| → ∞
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: 0 ≤ 1−Ē_{1,r} ≤ 1 eventually, so f′ ≤ β_c r^{−α−1}f² and Lemma I.4.5 item 2 gives liminf r^{−α}𝔼_{β_c,r}|K| ≥ α/β_c
CONSTANT_SCOPE: α/β_c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.7,hutchcroft.i.4.2.s2,hutchcroft.i.4.5,hutchcroft.i.4.g3,hutchcroft.i.4.dsp6
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP/RECONSTRUCTION: Corollary I.4.8 has only a one-sentence motivation, not a proof from which a locator could be copied. The helper assembles the lower bound using Lemma I.4.5 item 2, E_{1,r}≤1 and E|K|→∞. It is an ordinary proof obligation and must not be cited as a printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex12@L963-L967 The missing ingredient in the printed one-liner is ℰ_{1,r} ≤ 1 (see i.4.2.s2) and 𝔼_{β_c,r}|K| → ∞ (g3); both are available, so this is a SOURCE_GAP/reconstructed proof, not a printed proof. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. The lower-bound proof is reconstructed from the ODE ingredients rather than claimed as printed; no unconditional proof status follows.
EDGE: hutchcroft.i.4.2.s2 | .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284 | packet relation requires: ℰ_{1,r} ≤ 1 for the ODE comparison  [was E126]
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.Thmthm8.p1.1@L2289-L2289 | packet relation requires: item 2 of the ODE lemma  [was E127]
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284 | packet relation requires: non-negativity of ℰ_{1,r}  [was E125]
EDGE: hutchcroft.i.4.dsp6 | .scratch/source/paper.html#S4.Thmthm8@L2286-L2291 | packet relation requires: (I.4.6) is the ODE compared  [was E129]
EDGE: hutchcroft.i.4.g3 | .scratch/source/paper.html#S4.Thmthm8@L2286-L2291 | packet relation requires: f(r) → ∞ for item 2  [was E128]

NODE: hutchcroft.i.4.9.s1
KIND: step
TITLE: replay of the p = 1 identity at general β ≤ β_c
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex12@L2317-L2323
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.9.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 ≤ β ≤ β_c, r > 0
SOURCE_QUANTIFIERS: every 0 ≤ β ≤ β_c and r > 0
SOURCE_CONCLUSION: (∂/∂r)𝔼_{β,r}|K| = (1−Ē_{1,r,β})β r^{−α−1}(𝔼_{β,r}|K|)² with (1−Ē_{1,r,β}) = (1−ℰ_{0,r})(1−ℰ_{1,r,β}) and ℰ_{1,r,β} := [|B_r|(𝔼_{β,r}|K|)² − 𝔼_{β,r}[|K|Σ_{y∈B_r}|K_y|] + 𝔼_{β,r}[|K|²|K∩B_r|]]/(|B_r|(𝔼_{β,r}|K|)²) ≤ 𝔼_{β,r}[|K|²|K∩B_r|]/(|B_r|(𝔼_{β,r}|K|)²)
CONSTANT_SCOPE: inherits
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.1,hutchcroft.i.4.7
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p13.6.1@L981-L1017 The source says "the derivation of (I.4.15) above"; (I.4.15) is a *later* display in Subsection I.4.2 and is not the object being reused. The intended object is (I.4.6)/(I.4.5) (source cross-reference slip, §5.8). Note ℰ_{0,r} is the same for all β (it only involves J and B_r). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SOURCE_CORRECTION: the printed '(I.4.15)' cross-reference at tex L983 is dangling/misnumbered: display I.4.15 is defined later for second moments. The first-moment replay is a reconstructed source interpretation, not literal fidelity by relabelling. General-beta covariance replay is likewise labelled, not silently donated as a printed use.
EDGE: hutchcroft.i.4.1 | .scratch/source/paper.html#S4.Ex12@L2317-L2323 | RECONSTRUCTION / PRINTED CROSS-REFERENCE: tex L983 says (I.4.15), later used for the second moment; the replay required here is the p=1 identity (I.4.1). This is a source gap, not a verified link to display I.4.15
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.Ex12@L2317-L2323 | RECONSTRUCTION / SOURCE-GAP: covariance sandwich replay at general beta; not a printed application of Lemma I.4.7, whose statement is at beta_c

NODE: hutchcroft.i.4.9.s2
KIND: step
TITLE: finiteness of r_0(β) for β < β_c
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex17@L2368-L2374
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.9.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: β_c/2 ≤ β < β_c; subcritical moment bound (g6)
SOURCE_QUANTIFIERS: every β_c/2 ≤ β < β_c
SOURCE_CONCLUSION: r_0(β) := min{r : 𝔼_{β,s}|K| ≤ (2α/β)s^α for every s ≥ r} is finite
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.g6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p13.6.1@L981-L1017 The open endpoint β < β_c is essential; the endpoint is closed only at the end by monotone convergence. This is the "uniform error endpoint" discipline of the slice. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.g6 | .scratch/source/paper.html#S4.Ex17@L2368-L2374 | packet relation requires: "noting that r_0(β) is finite … by sharpness of the phase transition"  [was E032]

NODE: hutchcroft.i.4.9.s3
KIND: step
TITLE: monotonicity in r: 𝔼_{β,r}|K| ≤ 𝔼_{β,max{r,r_0}}|K|
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex18@L2376-L2382
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.9.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J_r ≤ J_{r′} pointwise for r ≤ r′ (XSLICE:I.1.5); monotone coupling (g5)
SOURCE_QUANTIFIERS: all r, r_0
SOURCE_CONCLUSION: r ↦ 𝔼_{β,r}|K| is non-decreasing
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.g5
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.5 [needed: Definition I.1.5: cut-off kernel J_r, laws P_{β,r}, β_c of the uncut kernel, P_{β_c,r} subcritical for r<∞, J_r ↑ J] PACKET PROOF_SOURCE: P#S4.SS1.p13.6.1@L981-L1017 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.5` (statements and use sites in §4). Asserted in one clause; no coupling constructed in the source. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.g5 | .scratch/source/paper.html#S4.SS1.p13.8@L2375-L2375 | packet relation requires: "Since 𝔼_{β,r}∣K∣ is monotone in r" — coupling not constructed  [was E034]

NODE: hutchcroft.i.4.9.s4
KIND: step
TITLE: bootstrap closure: r_0(β) ≤ (32C)^{1/(d−3α)} and the β ↑ β_c limit
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p14.1@L2388-L2388
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.9.s4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.9; d > 3α; Lemma I.4.5 item 1
SOURCE_QUANTIFIERS: every β_c/2 ≤ β < β_c, then β ↑ β_c
SOURCE_CONCLUSION: Ē_{1,r,β} ≤ 8C r^{3α−d}(max{r,r_0}/r)^{3α} ≤ 1/4 whenever r^d ≥ 32C max{r,r_0}^{3α}; then 𝔼_{β,r}|K| ≤ (4α/3β)r^α ≤ (2α/β)r^α; minimality of r_0 forces r_0(β) ≤ (32C)^{1/(d−3α)}, uniformly in β; monotone convergence closes β = β_c
CONSTANT_SCOPE: (32C)^{1/(d−3α)} with C from the tree-graph bound
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.5,hutchcroft.i.4.9.s2,hutchcroft.i.4.9.s3,hutchcroft.i.4.dsp8
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p13.6.1@L981-L1017 Closure verified in full: the admissible set is [min{s,R},∞) with s = (32C)^{1/d}r_0^{3α/d}; if r_0 > R = (32C)^{1/(d−3α)} then s < r_0 and minimality of r_0 is contradicted, so r_0 ≤ R. The printed intermediate "r_0 ≥ (32C)^{1/d}r_0^{3α/d}" is a reversed inequality, not an equality case, and is not what carries the conclusion (§5.8). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. SOURCE_CORRECTION: the source prints r_0(β) ≥ (32C)^{1/d}r_0(β)^{3α/d} immediately before deducing the upper bound from minimality. Minimality forces the reverse ≤ relation, not the printed ≥. The earlier 'equality case' description is withdrawn; the conclusion is retained only using the corrected inequality and full minimality implication.
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.SS1.p13.8@L2375-L2375 | packet relation requires: "Applying Lemma I.4.5 yields 𝔼_{β,r}∣K∣ ≤ (4α/3β)r^α"  [was E035]
EDGE: hutchcroft.i.4.9.s2 | .scratch/source/paper.html#S4.SS1.p13.8@L2375-L2375 | packet relation requires: minimality of r_0(β) is what converts the bootstrap into a bound on r_0  [was E036]
EDGE: hutchcroft.i.4.9.s3 | .scratch/source/paper.html#S4.Ex18@L2376-L2382 | packet relation requires: monotonicity replaces 𝔼_{β,r}∣K∣ by 𝔼_{β,max{r,r_0}}∣K∣  [was E037]
EDGE: hutchcroft.i.4.dsp8 | .scratch/source/paper.html#S4.E8@L2341-L2348 | packet relation requires: (I.4.8) is the error bound fed into the bootstrap  [was E139]

NODE: hutchcroft.i.4.10.s1
KIND: step
TITLE: Cauchy–Schwarz, tightness and the two-point bound produce η
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E9@L2400-L2407
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.6@L2396-L2428
CONTRACT_ID: I.4.10.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3α; Cor. I.2.5 with W = B_r, p = q = 1; Thm I.2.13; tree-graph at p = 4; (Hydro)
SOURCE_QUANTIFIERS: every 0 ≤ β ≤ β_c, r > 0
SOURCE_CONCLUSION: 𝔼[|K|²|K∩B_r|] ⪯ (𝔼|K|)^{7/2}r^{α/2}M_r^{1/2}; with M_r = o(r^{(d+α)/2}) this gives (I.4.10) with a continuous decreasing η → 0
CONSTANT_SCOPE: implicit constants absorbed into η; η independent of β
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp9,hutchcroft.i.4.g7
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.14 [needed: Definition I.1.14 (Hydro): M_r is the edian of |K_max(B_r)| under P_{β_c,r}, and (Hydro) is M_r = o(r^{(d+α)/2})] ; XSLICE:I.2.5 [needed: Corollary I.2.5: E|K∩W|^{p+q} ⪯ M(W)^q E|K∩W|^p] ; XSLICE:I.2.13 [needed: Theorem I.2.13: spatially averaged two-point bound Σ_{x∈B_r}P_{β_c}(0↔x) ⪯ r^α] ; XSLICE:I.2.3 [needed: display (I.2.3): E|K|^p ≤ (2p−3)!!(E|K|)^{2p−1}] PACKET PROOF_SOURCE: P#S4.SS1.p17.1@L1023-L1039 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.14`, `XSLICE:I.2.5`, `XSLICE:I.2.13`, `XSLICE:I.2.3` (statements and use sites in §4). Uses ℙ_{β_c,r} ≤ ℙ_{β_c} silently (g7) to invoke the two-point bound for the original kernel. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp9 | .scratch/source/paper.html#S4.E9@L2400-L2407 | packet relation requires: (I.4.9) is the Cauchy–Schwarz display  [was E039]
EDGE: hutchcroft.i.4.g7 | .scratch/source/paper.html#S4.E9@L2400-L2407 | packet relation requires: the display mixes ℙ_{β,r} and ℙ_{β_c,r}; the comparison is used silently  [was E043]

NODE: hutchcroft.i.4.10.s2
KIND: step
TITLE: the ψ fixed-point iteration and the β-uniform bound on r_0(β)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p16.1@L2430-L2430
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.6@L2396-L2428
CONTRACT_ID: I.4.10.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.10; η continuous, decreasing, → 0; c the universal ODE constant
SOURCE_QUANTIFIERS: every β < β_c
SOURCE_CONCLUSION: [η(r)(r_0/r)^{3α/2} ≤ c] ⇒ [Ē_{1,s,β} ≤ 2^{3/2}c ∀s ≥ r] ⇒ [r_0(β) ≤ r]; hence r_0(β) ≤ ψ^{−1}(r_0(β)) and r_0(β) is bounded by the supremal solution of ψ^{−1}(r) = r, uniformly in β
CONSTANT_SCOPE: universal in β
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.g8,hutchcroft.i.4.5,hutchcroft.i.4.dsp10
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p17.1@L1023-L1039 The three implications are asserted, not proved ("by the same ODE analysis carried out in the proof of that lemma") — g8. The reduction of a pointwise-in-r bound to all s ≥ r is exactly where an ODE comparison is needed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.5 | .scratch/source/paper.html#S4.SS1.p15.3@L2417-L2417 | packet relation requires: the universal constant c and the comparison are Lemma I.4.5's  [was E046]
EDGE: hutchcroft.i.4.dsp10 | .scratch/source/paper.html#S4.Ex19@L2418-L2424 | packet relation requires: the implication chain and ψ(r) are display (I.4.10)'s content, iterated  [was E044]
EDGE: hutchcroft.i.4.g8 | .scratch/source/paper.html#S4.Ex19@L2418-L2424 | packet relation requires: "by the same ODE analysis carried out in the proof of that lemma" — not reproduced  [was E045]

NODE: hutchcroft.i.4.11.s1
KIND: step
TITLE: rewriting the numerator of ℰ_{1,r} as a sum of two-point/doorway differences
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p20.2@L2500-L2508
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.8@L2496-L2520
CONTRACT_ID: I.4.11.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.11; translation invariance; independence of K and K_y on {0 ↮ y}
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: |B_r|(𝔼|K|)² − 𝔼[|K|Σ_{y∈B_r}1(y∉K)|K_y|] = Σ_{y∈B_r}Σ_{x,z∈Z^d}[ℙ(0↔x)ℙ(y↔z) − ℙ(0↔x ↮ y↔z)]
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.1 [needed: Lemma I.2.1: two-cluster correlation inequality, display 0 ≤ P(x↔y)P(z↔w) − P(x↔y↮z↔w) ≤ P(x↔y↔z↔w) (L421)] PACKET PROOF_SOURCE: P#S4.Ex24@L1075-L1085 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.1` (statements and use sites in §4). Uses 𝔼|K| = Σ_xℙ(0↔x) and 𝔼[1(y∉K)|K||K_y|] = Σ_{x,z}ℙ(0↔x, y↔z, 0↮y). The product ℙ(0↔x)ℙ(y↔z) is the product of *marginals* of two correlated events — legitimate only because |B_r|(𝔼|K|)² is by definition Σ_y𝔼|K|𝔼|K_y|; it is not an independence assertion about one configuration. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.11.s2
KIND: step
TITLE: applying Lemma I.4.12 and collapsing the five-factor sum to ∇(0,y)(𝔼|K|)²
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex23@L2510-L2516
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.8@L2496-L2520
CONTRACT_ID: I.4.11.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.11; Lemma I.4.12
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: the difference is ≤ Σ_{y∈B_r}∇(0,y)(𝔼_{β_c,r}|K|)², giving ℰ_{1,r} ≤ |B_r|^{−1}Σ_{x∈B_r}∇(0,x)
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.12
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Ex24@L1075-L1085 The collapse is Σ_xℙ(a↔x) = 𝔼|K| and Σ_zℙ(b↔z) = 𝔼|K|, leaving Σ_{a,b}ℙ(0↔a)ℙ(a↔b)ℙ(y↔b) = ∇(0,y) by symmetry ℙ(y↔b) = ℙ(b↔y). Verified. Because this step consumes I.4.12 at β = β_c only, the β/β_c binder mismatch of I.4.12 (§5.3) has no effect here. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.12 | .scratch/source/paper.html#S4.SS1.p20.3@L2509-L2509 | packet relation requires: five-factor bound applied termwise, then the sums in x and z collapse  [was E049]

NODE: hutchcroft.i.4.12.s1
KIND: step
TITLE: the three-configuration coupling (ω, ω′, ω̃) and the doorway geometry
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p19.1@L2463-L2463
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.7@L2460-L2495
CONTRACT_ID: I.4.12.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ω, ω′ i.i.d. with kernel J_r at β; K_0 the 0-cluster of ω
SOURCE_QUANTIFIERS: all x,y,z
SOURCE_CONCLUSION: PRINTED, REFUTED/OPEN: ω̃ := ω on edges touching K_0 and ω′ elsewhere; ω̃ has the same law as ω; on {y ∉ K_0}, K_y ⊆ K̃_y and z ∈ K_y iff there is an ω̃-open y–z path avoiding K_0; hence z ∈ K̃_y \ K_y forces b ∈ K_0 joined to y and z by disjoint ω′-paths
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this argument is not accepted as a proof. It is preserved precisely because it has a counterexample; no five-factor statement refutation follows, and no repaired proof is claimed. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Thmthm13.2@L1065-L1073 As literally defined, ω̃ agrees with ω on *every* edge with an endpoint in K_0, so K̃_0 = K_0 exactly (not "⊇"). Two consequences recorded in §5.1: the substitution "re-draw the explored cluster" is not what the text says, and the case y ∈ K_0 is not covered by the doorway argument. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.12.s2
KIND: step
TITLE: union bound and BK for infinite-edge events
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex20@L2466-L2470
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491
CONTRACT_ID: I.4.12.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.12.s1; BK inequality
SOURCE_QUANTIFIERS: all b ∈ Z^d
SOURCE_CONCLUSION: PRINTED, REFUTED/OPEN: ℙ(x∈K_0, z∈K̃_y\K_y) ≤ Σ_bℙ(x,b∈K_0 and b on a simple 0–z path in K̃_y) ≤ Σ_bℙ_{β,r}(0↔x,0↔b)ℙ_{β,r}(y↔b)ℙ_{β,r}(b↔z)
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.12.counterexample
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this argument is not accepted as a proof. It is preserved precisely because it has a counterexample; no five-factor statement refutation follows, and no repaired proof is claimed. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.BK [needed: BK inequality as stated in Subsection I.2.1, including its infinite-edge footnote] PACKET PROOF_SOURCE: P#S4.Thmthm13.2@L1065-L1073 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.BK` (statements and use sites in §4). The events depend on infinitely many edges; the source's own footnote (BK by limiting arguments, [10, §7]) is the licence invoked without further comment. Recorded as a hypothesis of this step, not as a new external node. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.12.counterexample | .scratch/source/paper.html#S4.SS1.7@L2460-L2495 | REFUTATION of the printed doorways/fresh-cluster inference, not a proof of that inference. The five-factor statement itself remains open

NODE: hutchcroft.i.4.12.s3
KIND: step
TITLE: tree-graph insertion splitting ℙ(0↔x, 0↔b)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex22@L2476-L2480
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491
CONTRACT_ID: I.4.12.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits; tree-graph inequality (I.2.1)/(I.2.2)
SOURCE_QUANTIFIERS: all a ∈ Z^d
SOURCE_CONCLUSION: ℙ_{β,r}(0↔x,0↔b) ≤ Σ_aℙ_{β,r}(0↔a)ℙ_{β,r}(a↔x)ℙ_{β,r}(a↔b), giving the five-factor display
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.1 [needed: Lemma I.2.1: two-cluster correlation inequality, display 0 ≤ P(x↔y)P(z↔w) − P(x↔y↮z↔w) ≤ P(x↔y↔z↔w) (L421)] PACKET PROOF_SOURCE: P#S4.Thmthm13.2@L1065-L1073 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.1` (statements and use sites in §4). This insertion is what makes I.4.12 stronger than the naive tree-graph bound on ℙ(0↔x↮y↔z); keep it as its own record. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.12.s4
KIND: step
TITLE: the closing "coupling identity" (source-defective  see §5.1)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491
CONTRACT_ID: I.4.12.s4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: inherits hutchcroft.i.4.12.s1
SOURCE_QUANTIFIERS: all x,y,z
SOURCE_CONCLUSION: PRINTED, REFUTED/OPEN: as printed: ℙ_{β_c,r}(0↔x)ℙ_{β_c,r}(y↔z) − ℙ_{β_c,r}(0↔x↮y↔z) = ℙ(x∈K_0,z∈K̃_y) − ℙ(x∈K_0,y∉K_0,z∈K_y) = ℙ(x∈K_0, z∈K̃_y\K_y)
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.12.s1,hutchcroft.i.4.12.counterexample
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this argument is not accepted as a proof. It is preserved precisely because it has a counterexample; no five-factor statement refutation follows, and no repaired proof is claimed. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Thmthm13.2@L1065-L1073 NOT VALID as printed. The identity fails by the term ℙ(x∈K_0, y∈K_0, z∈K_0); §5.1 computes it and shows it is dominated by the same five-factor sum, so the lemma's *statement* survives while this step does not. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.12.s1 | .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491 | packet relation requires: the closing identity is asserted "by construction of the coupling" — and fails on y ∈ K_0 (§5.1)  [was E052]
EDGE: hutchcroft.i.4.12.counterexample | .scratch/source/paper.html#S4.SS1.7@L2460-L2495 | REFUTATION of the printed doorways/fresh-cluster inference, not a proof of that inference. The five-factor statement itself remains open

NODE: hutchcroft.i.4.13.s1
KIND: step
TITLE: both Tonelli computations (preservation of log-integrability)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p22.1@L2531-L2531
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.9@L2533-L2555
CONTRACT_ID: I.4.13.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h log-integrable; a > 0
SOURCE_QUANTIFIERS: a > 0
SOURCE_CONCLUSION: ∫_1^∞[r^a∫_r^∞|h(s)|s^{−a−1}ds]dr/r ≤ (1/a)∫_1^∞|h(s)|ds/s and ∫_1^∞[r^{−a}∫_1^r|h(s)|s^{a−1}ds]dr/r = (1/a)∫_1^∞|h(s)|ds/s
CONSTANT_SCOPE: 1/a
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.1.1@L1096-L1110 Both computations re-derived independently and agree with the printed constants (∫_1^s r^{a−1}dr = (s^a−1)/a; ∫_s^∞ r^{−a−1}dr = s^{−a}/a). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.13.s2
KIND: step
TITLE: both transforms tend to zero
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex25@L2545-L2551
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.9@L2533-L2555
CONTRACT_ID: I.4.13.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h(r) → 0 and h log-integrable
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: both transforms are error functions
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.13.s1
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.1.1@L1096-L1110 "Follows easily" in the source; for the second transform one splits ∫_1^r at r/2 and uses the log-integrability tail. Not written out in the source; the argument is standard and I did not find a gap. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.13.s1 | .scratch/source/paper.html#S4.SS1.p23.3@L2552-L2553 | packet relation requires: "tends to zero" uses the finiteness just proved  [was E145]

NODE: hutchcroft.i.4.2.s1
KIND: step
TITLE: assembly of Proposition I.4.2 from the three cases
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p24.1@L2559-L2560
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one of the three first-moment cases plus its applicable error condition, assembled by cases; the neutral ODE ingredients and explicitly identified logarithmic/averaged bridges
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: first-moment asymptotics and, only on the stated error-integrable routes, the H_r logarithmic-integrability conclusion
CONSTANT_SCOPE: inherits hutchcroft.i.4.2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.odeglue,hutchcroft.i.4.2.c2,hutchcroft.i.4.2.c3,hutchcroft.i.4.2.c4,hutchcroft.i.4.2.c5,hutchcroft.i.4.2.c1,hutchcroft.i.4.2.s3
ROUTES: -
ROUTE_FOR: -
NOTE: FULL CASE ANALYSIS, intentionally retaining every alternative for the proposition-level statement. Single-case consumers must use r1 through r5 and their case records rather than this umbrella assembly. The neutral ODE glue is separated so that a case does not inherit the other alternatives' first-moment proofs. The averaged/triangle and Hydro assumptions remain conditions of the actual cases; no source proof or provider is claimed. PROPOSED, not independently reviewed.
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the full case analysis includes this neutral assembly or case branch
EDGE: hutchcroft.i.4.2.c2 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the full case analysis includes this neutral assembly or case branch
EDGE: hutchcroft.i.4.2.c3 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the full case analysis includes this neutral assembly or case branch
EDGE: hutchcroft.i.4.2.c4 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the full case analysis includes this neutral assembly or case branch
EDGE: hutchcroft.i.4.2.c5 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the full case analysis includes this neutral assembly or case branch
EDGE: hutchcroft.i.4.2.c1 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the general assembly also records the high-dimensional discharge and the averaged-triangle bridge
EDGE: hutchcroft.i.4.2.s3 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the general assembly also records the high-dimensional discharge and the averaged-triangle bridge

NODE: hutchcroft.i.4.2.s2
KIND: step
TITLE: the ℰ_{1,r} ≤ 1 half of the sandwich (used by Corollary I.4.8 but not stated there)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p10.1@L2284-L2284
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.4@L2268-L2282
CONTRACT_ID: I.4.2.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma I.4.7's lower covariance bound 0 ≤ 𝔼[|K|Σ_{y∈B_r}|K_y|] − |B_r|(𝔼|K|)²
SOURCE_QUANTIFIERS: every r > 0
SOURCE_CONCLUSION: 0 ≤ ℰ_{1,r} ≤ min{1, T/𝔹} where 𝔹 = |B_r|(𝔼|K|)² and T = 𝔼[|K|²|K∩B_r|]; in particular ℰ_{1,r} ≤ 1
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.7
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.Thmthm9.p1.2.1@L955-L961 PACKET COMPOUND STATEMENT_SOURCE: P#S4.Ex12@L963-L967 (use), P#S4.Thmthm9.p1.1.1@L949-L953 (source) Corrects m7's `i.4.2.s3`, which asserted ℰ ≤ 1 − T/𝔹. The sandwich gives ℰ ≥ 1 − T/𝔹 and ℰ ≤ T/𝔹; the bound ℰ ≤ 1 comes from 𝔼[|K|Σ_y1(y∉K)|K_y|] ≥ 0, i.e. from the *lower* half. This is exactly the kind of direction slip that would break Corollary I.4.8 if copied. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.7 | .scratch/source/paper.html#S4.Ex9@L2258-L2264 | packet relation requires: ℰ_{1,r} ≤ 1 comes from the lower half of Lemma I.4.7's sandwich  [was E146]

NODE: hutchcroft.i.4.2.s3
KIND: step
TITLE: from ∇_r to the averaged triangle sum and back ("a simple variation on Lemma I.4.13")
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p25.1@L2564-L2564
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p25.1@L2564-L2564
CONTRACT_ID: I.4.2.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition; ∇_R → 0
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: if r ↦ ∇_r is log-integrable then so is r ↦ r^{−d}Σ_{x∈B_r}∇(0,x)
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.BallAverage.logIntegrable_openTriangle
LEAN_NOTE: Configured SourceModelData and arbitrary normalized source norm. The R=√r split gives logarithmic integrability of the normalized ball average from finite nablaSup at zero and log-integrability of nablaSup; measurability is derived from finite monotonic ball sums. This does not prove tail convergence, the triangle condition itself, or any root.
DEPS: ext.triangle-open,hutchcroft.i.4.6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.5.1@L1110-L1113 Verified: for any R, split B_r into B_R and B_r\B_R; the inner part contributes at most |B_R|∇(0,0)/|B_r| = o(1) (using ∇(0,0) = ∇_{β_c} < ∞) and the outer part at most ∇_R. Choose R = sqrt(r), not r/2. The inner term is bounded by |B_sqrt(r)|∇(0,0)/|B_r| ≍ r^{-d/2}∇(0,0), which is both o(1) and logarithmically integrable (since d ≥ 1), and the outer term is bounded by ∇_sqrt(r), whose logarithmic integral follows by u = sqrt(r), dr/r = 2du/u. Setting R = r/2 would leave the nonzero limit 2^{-d}∇(0,0), which is NOT a logarithmically integrable residual. SOURCE_GAP/RECONSTRUCTION: the paper supplies only 'a simple variation on Lemma I.4.13'; this two-scale computation is an explicit proof obligation, not a verified printed derivation. The reverse comparison is elementary: the normalized ball average dominates the tail supremum, so the two statements can be related without pretending the mean value must vanish. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. The reconstructive split uses |B_R| ≍ R^d from Lemma I.4.6 and ∇(0,0)<∞ from the triangle condition; no uniform generic replacement R is hidden in the paper's hypotheses. VERIFIED AVERAGED OPEN TRIANGLE: `Analysis.BallAverage` implements the R=√r split, with no artifactual r/2 residual, and obtains r^{-d}Σ_{B_r}f ≤ 2^d((sup f)r^{-d/2}+∇_{√r}). The log-l integral of the r^{-d/2} part is finite for d≥1 and the √r substitution gives the other factor 2. `measurable_normalized_ballSum_toReal` discharges measurability using finite monotone ball sums, so the configured `logIntegrable_openTriangle` has no hidden extra measurability premise. The finite-tail/log-integrability hypotheses remain explicit; this closes i.4.2.s3 only, not triangle condition itself, a.tri.tail, or a paper root.
EDGE: ext.triangle-open | .scratch/source/paper.html#S4.SS1.p24.1@L2559-L2560 | packet relation requires: ∇_R → 0 for the outer part of the split  [was E147]
EDGE: hutchcroft.i.4.6 | .scratch/source/paper.html#S4.SS1.p24.1@L2559-L2560 | packet relation requires: ∣B_R∣/∣B_r∣ → 0 uses ∣B_r∣ ≍ r^d  [was E148]

NODE: ext.russo
KIND: external
TITLE: [55] G. Grimmett, Percolation, 2nd ed., Springer 1999, Section 2.4 — Russo's formula
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p3.1@L2033-L2033
PROOF_SOURCE: -
CONTRACT_ID: EXT.RUSSO
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Bernoulli bond percolation on a countable graph with edge probabilities p_e; an increasing event A depending on finitely many edges
SOURCE_QUANTIFIERS: per cited work
SOURCE_CONCLUSION: d/dp_e ℙ(A) = ℙ(e is pivotal for A); equivalently the derivative of an expectation of an increasing functional is the expected number of pivotal edges
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - Semantic mismatch to check before any reuse: the cited form is for a finite-edge increasing event with a *single* parameter p_e; here the parameter r moves *all* edges at once and the functional |K|^p is unbounded and infinite-volume. Both mismatches are carried as g1/g2, not absorbed into the citation. CITED-WORK (bibliographic only; not consulted, no Lean, no external verification): [55] §2.4 (not consulted) COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: ext.hara.prop1.7
KIND: external
TITLE: [63] Hara–van der Hofstad–Slade, Ann. Probab. 31 (2003), Proposition 1.7 — convolution decay
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p26.1@L2569-L2569
PROOF_SOURCE: -
CONTRACT_ID: EXT.HARA17
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |f(x)| ⪯ (1+‖x‖)^{−d+a}, |g(x)| ⪯ (1+‖x‖)^{−d+b} with a,b > 0 and a+b < d
SOURCE_QUANTIFIERS: all x ∈ Z^d
SOURCE_CONCLUSION: |f*g(x)| ⪯ (1+‖x‖)^{−d+a+b}
CONSTANT_SCOPE: depends on a,b,d and on the two implied constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - Used twice with a = b = 2 under (HD) 2, where a+b = 4 < d because d > 6. Note the hypothesis a+b < d is *not* what the paper needs in Case 3, where a+b = d; that case is handled by the paper's own (I.4.12), not by [63]. Do not cite [63] for the logarithmic case. CITED-WORK (bibliographic only; not consulted, no Lean, no external verification): [63] Prop. 1.7 (not consulted) Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: ext.triangle-open
KIND: external
TITLE: [12] Barsky–Aizenman, [83] Kozma — the triangle and the open triangle
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p1.1@L2077-L2077
PROOF_SOURCE: -
CONTRACT_ID: EXT.TRIOPEN
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition ∇_{β_c} < ∞
SOURCE_QUANTIFIERS: ‖x‖ → ∞ (hence r → ∞)
SOURCE_CONCLUSION: ∇_{β_c}(0,x) → 0, so ∇_r := sup_{‖x‖≥r}∇_{β_c}(0,x) → 0
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET COMPOUND STATEMENT_SOURCE: P#S4.Thmthm2.p1.4.1@L855-L856 (citation) with use at P#S4.SS1.p26.5.1@L1110-L1113 The exact claim the paper needs is only ∇_r → 0 (not a rate). I did not verify which of [12]/[83] states it in this form; recorded as unverified against the cited works. CITED-WORK (bibliographic only; not consulted, no Lean, no external verification): [12],[83] (not consulted) COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: ext.grimmett699
KIND: external
TITLE: [55, Eq. 6.99] — subcritical cluster-volume tail bound
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634
PROOF_SOURCE: -
CONTRACT_ID: EXT.G699
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: subcritical percolation measure with finite 𝔼|K|; n ≥ 1
SOURCE_QUANTIFIERS: every n ≥ 1
SOURCE_CONCLUSION: ℙ(|K| ≥ n) ≤ (√2 𝔼|K|/n) exp[−n/(4(𝔼|K|)²)]
CONSTANT_SCOPE: absolute √2 and 4
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - Only used in the boundary node I.4.14. The paper writes "the tree-graph inequality applied as in [55, Eq. 6.99]" without reproducing the derivation; the long-range adaptation of a nearest-neighbour-type Chernoff bound is asserted, not proved. Mismatch flagged, not hidden. CITED-WORK (bibliographic only; not consulted, no Lean, no external verification): [55] Eq. 6.99 (not consulted) Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. USE-SITE CORRECTION: the citation is the sentence at `S4.SS1.p28.1@L2634` -- "It follows from Proposition I.4.2 and the tree-graph inequality applied as in [55, Eq. 6.99] that" -- inside the proof of Corollary I.4.14. The former STATEMENT_SOURCE `S4.Ex29@L2635-L2641` is the display the citation is used to obtain, not the site where the external result is invoked. Both consumers already name the sentence in their EDGE, so this only aligns the record with them and with ext.russo / ext.hara.prop1.7 / ext.triangle-open.

NODE: hutchcroft.i.4.g1
KIND: step
TITLE: SOURCE_GAP: differentiability of r ↦ 𝔼_{β,r}|K|^p and the derivative-under-expectation interchange
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex1@L2036-L2040
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex1@L2036-L2040
CONTRACT_ID: I.4.g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model and finite-cutoff moment data are in force; differentiability and the interchange are exactly the unproved source gap
SOURCE_QUANTIFIERS: every p ≥ 1, β ≤ β_c, r > 0
SOURCE_CONCLUSION: r ↦ 𝔼_{β,r}|K|^p is differentiable with locally integrable derivative and the derivative may be taken inside the expectation, including the moving window B_r
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - Not stated anywhere in the paper. Tractable route (not a proof here): the sum over pairs at distance ≤ r is countable and the expectation is finite for r < ∞ because ℙ_{β_c,r} is dominated by a subcritical measure; a finite-volume/monotone truncation plus dominated convergence gives the interchange. The truncated-at-R version of the identity holds exactly (§7). COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.g2
KIND: step
TITLE: SOURCE_GAP: Russo applied directly in infinite volume at β ≤ β_c, r < ∞ ("a standard consequence of the sharpness of the phase transition")
STATEMENT_SOURCE: .scratch/source/paper.html#S4.p3.2@L2042-L2042
PROOF_SOURCE: .scratch/source/paper.html#S4.p3.2@L2042-L2042
CONTRACT_ID: I.4.g2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sharpness/continuity of the phase transition for long-range percolation
SOURCE_QUANTIFIERS: β ≤ β_c, r < ∞
SOURCE_CONCLUSION: the derivative formula applies to the infinite-volume moment without a finite-volume limit
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - No citation at the use site. Classified as gap-with-lead, not as an external leaf: the paper's own attribution of continuity elsewhere is [22] (Berger). The subcritical domination argument in XSLICE:I.1.5's parenthetical is the likely route; not proved here. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.g3
KIND: step
TITLE: SOURCE_GAP: 𝔼_{β_c}|K| = ∞ and 𝔼_{β,r}|K| < ∞ for β < β_c
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219
CONTRACT_ID: I.4.g3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the ambient long-range model and critical parameter are in force; this finite/infinite first-moment dichotomy is an unproved source gap
SOURCE_QUANTIFIERS: beta = beta_c in the first clause and every 0 <= beta < beta_c in the second; no cutoff index is introduced
SOURCE_CONCLUSION: 𝔼_{β_c}|K| = ∞; 𝔼_{β,r}|K| < ∞ for β < β_c
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET COMPOUND STATEMENT_SOURCE: use sites P#S4.SS1.p9.1.1@L931-L935 ("Since 𝔼_{β_c}|K| = ∞") and P#S4.Ex12@L963-L967 Used without proof or citation. The first half is what lets item 3 of Lemma I.4.5 fire (f(r) → ∞) and therefore what makes (I.4.7) an identity rather than a bound; it is therefore load-bearing for the whole slice. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.g4
KIND: step
TITLE: SOURCE_GAP: the implicit no-blow-up hypothesis of Lemma I.4.5
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p4.1@L2171-L2172
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p4.1@L2171-L2172
CONTRACT_ID: I.4.g4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f is positive and differentiable on (0,infinity), as required by Lemma I.4.5; finiteness on the whole domain is an unproved source gap
SOURCE_QUANTIFIERS: f is quantified over the whole interval (0,infinity), in items 1 and 3 of Lemma I.4.5
SOURCE_CONCLUSION: f is finite on all of (0,∞) (does not blow up in finite time) — an implicit hypothesis of items 1 and 3
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET COMPOUND STATEMENT_SOURCE: P#S4.SS1.p5.2.1@L907-L907 (the paper's own caution) with use in P#S4.E8@L971-L1017 The source flags this itself. For this slice's applications f = 𝔼_{β,r}|K|, whose finiteness is g3. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.g5
KIND: step
TITLE: SOURCE_GAP: monotone coupling making r ↦ 𝔼_{β,r}|K| non-decreasing
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p13.8@L2375-L2375
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p13.8@L2375-L2375
CONTRACT_ID: I.4.g5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J_r ≤ J_{r′} pointwise for r ≤ r′
SOURCE_QUANTIFIERS: r ≤ r′
SOURCE_CONCLUSION: 𝔼_{β,r}|K| ≤ 𝔼_{β,r′}|K|
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.CutoffLimit.monotone_lintegral_clusterVol_cutoff
LEAN_NOTE: Exact term-level application for the first-moment monotone-radius obligation; no higher-moment, uniform-first-moment or root claim.
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.5 [needed: Definition I.1.5: cut-off kernel J_r, laws P_{β,r}, β_c of the uncut kernel, P_{β_c,r} subcritical for r<∞, J_r ↑ J] Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.5` (statements and use sites in §4). Asserted in one clause; no coupling is constructed. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. PROVIDER-MAPPING CHECK: `CutoffLimit.monotone_lintegral_clusterVol_cutoff` was applied term-by-term with the same antitone-profile, radius, root and positive-parameter-free hypotheses and elaborated under -DwarningAsError=true in .scratch/verified-gaps/MonotoneCutoffMean.lean. Its axiom report is propext, Classical.choice, Quot.sound. This closes this specific first-moment monotone-radius obligation only, not g7 (stochastic comparison of all higher cluster moments), any finite-critical-moment premise, or a root.

NODE: hutchcroft.i.4.g6
KIND: step
TITLE: SOURCE_GAP: finiteness of r_0(β) from "sharpness of the phase transition"
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex17@L2368-L2374
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex17@L2368-L2374
CONTRACT_ID: I.4.g6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: for β < β_c, 𝔼_{β,r}|K| = o(r^α) (exponential tail / sharpness)
SOURCE_QUANTIFIERS: every β < β_c
SOURCE_CONCLUSION: r_0(β) < ∞
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.Analysis.exists_radius_of_isLittleO_rpow
LEAN_NOTE: Exact little-o-to-threshold step: E=o(r^α), α>0 and β>0 give a finite real r₀ with E(r)≤(2α/β)r^α above r₀. The sharpness asymptotic remains an explicit input; no finite-moment or uniform-in-β radius inference is made.
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - A strictly stronger input than g3: finiteness alone does not give the sublinear growth. No reference given at the use site. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. VERIFIED RADIUS THRESHOLD: `Analysis.SubcriticalRadius.exists_radius_of_isLittleO_rpow` applies the little-o convergence test and chooses a finite positive radius at which E(r)/r^α has absolute value below 2α/β. This is the exact existence step behind r0(β), with the sharpness asymptotic left as an explicit premise. It does not establish sharpness from finite moments, prove a radius uniform in β, or close either paper root.

NODE: hutchcroft.i.4.g7
KIND: step
TITLE: SOURCE_GAP: silent monotone comparisons between ℙ_{β,r}, ℙ_{β_c,r} and ℙ_{β_c}
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E9@L2400-L2407
PROOF_SOURCE: .scratch/source/paper.html#S4.E9@L2400-L2407
CONTRACT_ID: I.4.g7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: β ≤ β_c; J_r ≤ J (XSLICE:I.1.5)
SOURCE_QUANTIFIERS: β ≤ β_c, r ≥ 0
SOURCE_CONCLUSION: ℙ_{β,r} ≤ ℙ_{β_c,r} ≤ ℙ_{β_c} stochastically, hence e.g. 𝔼_{β,r}[|K|⁴] ≤ 𝔼_{β_c,r}[|K|⁴] and Theorem I.2.13 (a statement about ℙ_{β_c}) may be applied inside a display written with ℙ_{β_c,r}
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.Orchestration.SourceModelData.cutoff_mono_beta_and_le_uncut
LEAN_NOTE: Exact general-SourceModelData increasing-event, all-natural-moment, and two-point cutoff comparison at β≤γ; no sup-norm distance minimum or reduced parameter is used. The raw sup-norm companion module checks a power-law/cardFun fourth-moment application. This discharges the comparison step only, not uncut Theorem I.2.13, critical-moment finiteness, sharpness, or either root.
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: originally misclassified as an assumption, but this is a derived fact or unproved proof step, not a frozen standing assumption. PROOF_SOURCE points to the actual gap/use statement, not to a supplied printed proof. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.5 [needed: Definition I.1.5: cut-off kernel J_r, laws P_{β,r}, β_c of the uncut kernel, P_{β_c,r} subcritical for r<∞, J_r ↑ J] PACKET COMPOUND STATEMENT_SOURCE: use sites P#S4.Thmthm12.p1.1.1@L1027-L1029 and P#S4.Thmthm12.p1.2@L1029-L1029 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.5` (statements and use sites in §4). Recorded once and referenced where it is used, instead of scattering "harmless" remarks. The second inclusion is the one that matters: the two-point upper bound of Theorem I.2.13 is for the *uncut* kernel. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. VERIFIED SOURCE COMPARISON: `MomentMonotonicity.SourceModelMoments.SourceModelData.cutoff_mono_beta_and_le_uncut` proves, for β≤γ, the increasing-measurable-event comparisons P_{β,r}≤P_{γ,r} and P_{γ,r}≤P_γ, all-natural-moment comparisons, and both corresponding two-point comparisons. `cutoff_fourthMoment_mono_beta_and_le_uncut` gives the q=4 form; the raw sup-norm companion module contains a power-law/cardFun fourth-moment application. This discharges the general-normalized-source comparison obligation i.4.g7 only; an arbitrary admissible norm is allowed, and a concrete source-model inhabitant is supplied. It does not prove Theorem I.2.13 itself, finiteness of the uncut/critical moments, r0(β)<∞, sharpness, or either paper root.

NODE: hutchcroft.i.4.g8
KIND: step
TITLE: SOURCE_GAP: the "same ODE analysis" behind the ψ-iteration of Lemma I.4.10
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p16.1@L2430-L2430
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p16.1@L2430-L2430
CONTRACT_ID: I.4.g8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: display (I.4.10)
SOURCE_QUANTIFIERS: every β < β_c
SOURCE_CONCLUSION: the three implications of the ψ display, hence the β-uniform bound on r_0(β)
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp10
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - [F1] RECLASSIFIED assumption -> step: the record has a node prerequisite, which the assumption-leaf rule forbids. Content unchanged; it remains a SOURCE_GAP. The source states the implications but does not prove them; the passage from a pointwise η(r) bound to a bound for all s ≥ r is where an ODE comparison is needed. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp10 | .scratch/source/paper.html#S4.SS1.p15.3@L2417-L2417 | packet relation requires: the implications being asserted are those of display (I.4.10)  [was E151]

NODE: hutchcroft.i.4.g9
KIND: step
TITLE: SOURCE_GAP: logarithmic integrability of ℰ_{0,r} from (∗) and Lemma I.4.6
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p6.1@L2219-L2219
CONTRACT_ID: I.4.g9
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |J′(r)| = r^{−d−α−1}(1+δ_r) with δ log-integrable (XSLICE:I.1.3); |B_r| = r^d(1+O(1/r)) (I.4.6)
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: 1−ℰ_{0,r} = 1+δ_r+O(1/r), so ℰ_{0,r} is a log-integrable error function
CONSTANT_SCOPE: no additional implicit multiplicative constant is introduced here; the source conclusion uses only its explicit constants, coefficients and bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio
LEAN_NOTE: Exact normalized-ball/kernel-error product at SourceModelData. Finite-ball measurability, Lemma I.4.6’s relative O(1/r) bound, and product error closure are proved. No sign hypothesis, finite cluster moment, or sharpness input is added.
DEPS: hutchcroft.i.4.6
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.1.3 [needed: Definition I.1.3: kernel J, |J'(r)| = C(1+δ_r)r^{−d−α−1}, normalization (∗)] PACKET COMPOUND STATEMENT_SOURCE: use sites P#S4.SS1.p9.1.1@L931-L935 and P#S4.SS1.p26.5.1@L1110-L1113 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.1.3` (statements and use sites in §4). [F1] RECLASSIFIED assumption -> step: the record has a node prerequisite, which the assumption-leaf rule forbids. Content unchanged; it remains a SOURCE_GAP. Verified: δ_r is log-integrable by hypothesis and O(1/r) is, since ∫_1^∞ dr/r² < ∞; ℰ_{0,r} = 1−(1+δ_r+O(1/r)) = −δ_r+O(1/r) is then a log-integrable error function. The source asserts this with the phrase "by our standing assumptions" and does not display the computation. COORDINATOR SCOPE RESTITUTION: an emdash was expanded from the statement's own hypotheses, quantifiers and conclusion. No mathematical premise, comparison constant or proof status was added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. VERIFIED LOGARITHMIC ERROR: `Analysis.BallRatioLogError` first proves `isLogErrorFunction_mul_of_denominator_bound` and the exact complementary product error for arbitrary-sign δ and an eventual O(1/r) term. `SourceModelData.finite_ball` establishes finite normalized balls and gives a measurable cardinality ratio; `ball_ratio_error_bound` applies Lemma I.4.6 directly to obtain |B_r|/r^d=1+O(1/r). The provider is `SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio`, for the complementary error of (1+δ_r)|B_r|/r^d. A concrete source-model witness with δ≡0 is checked in the same module. This discharges i.4.g9 only; it does not supply the probabilistic E1,r estimates, finite critical moments, or either root.
EDGE: hutchcroft.i.4.6 | .scratch/source/paper.html#S4.SS1.p6.2@L2228-L2234 | packet relation requires: ∣B_r∣ = r^d(1+O(1/r)) supplies the O(1/r) term  [was E153]

NODE: hutchcroft.i.4.14.s1
KIND: step
TITLE: tail bound from Prop I.4.2 + "tree-graph as in [55, Eq. 6.99]", then the union bound
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex29@L2635-L2641
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.12@L2631-L2663
CONTRACT_ID: I.4.14.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Prop I.4.2; tree-graph inequality; [55, Eq. 6.99]; |B_r| ⪯ r^d
SOURCE_QUANTIFIERS: every n ≥ 1; every r ≥ 2
SOURCE_CONCLUSION: ℙ_{β_c,r}(|K| ≥ n) ≤ (√2𝔼|K|/n)exp[−n/(4(𝔼|K|)²)]; hence M_r ⪯ (𝔼_{β_c,r}|K|)² log r
CONSTANT_SCOPE: √2, 4, and a union-bound constant depending only on d
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2,ext.grimmett699
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.3 [needed: display (I.2.3): E|K|^p ≤ (2p−3)!!(E|K|)^{2p−1}] PACKET PROOF_SOURCE: P#S4.SS2.2@L1145-L1159 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.3` (statements and use sites in §4). Neither the Chernoff computation nor the long-range adaptation of [55, Eq. 6.99] is reproduced; the union bound's explicit choice n = C(𝔼|K|)²log r with C > 4d is not written either (reconstructed: it makes |B_r|·e^{−n/(4(𝔼|K|)²)} ≤ e^{−1}). Weakest link of the boundary node. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: ext.grimmett699 | .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634 | packet relation requires: "the tree-graph inequality applied as in [55, Eq. 6.99]"  [was E086]
EDGE: hutchcroft.i.4.2 | .scratch/source/paper.html#S4.SS1.p28.1@L2634-L2634 | packet relation requires: Prop I.4.2 supplies 𝔼_{β_c,r}∣K∣ ⪯ r^α, giving M_r ⪯ r^{2α}log r  [was E087]

NODE: hutchcroft.i.4.14.s2
KIND: step
TITLE: (Hydro) in cases 2 and 3 via Lemma I.2.6 — carries source defect §5.2
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex31@L2653-L2659
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.12@L2631-L2663
CONTRACT_ID: I.4.14.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma I.2.6 at p = 1; two-point bounds of (HD) 2 and 3
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: as printed: M_r² ⪯ r^{−d}𝔼_{β_c,r}|K∩B_{2r}| ≤ r^{−d}Σ_{x∈B_{2r}}ℙ_{β_c}(0↔x); correctly: M_r² ⪯ r^{+d}𝔼_{β_c,r}|K∩B_{2r}|, giving M_r ⪯ r^{(d+2)/2} in case 2 (hence o(r^{(d+α)/2}) because case 1 failing forces α > 2) and M_r ⪯ r^4/(log r)^{1/2} in case 3
CONSTANT_SCOPE: implicit constants only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_CORRECTION: explicit r^{-d} -> r^d source correction. UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:I.2.6 [needed: Lemma I.2.6: E_{β,r}|K|^p ≥ (M_{β,r}−1)^{p+1}/(e|B_r|)] ; XSLICE:I.2.13 [needed: Theorem I.2.13: spatially averaged two-point bound Σ_{x∈B_r}P_{β_c}(0↔x) ⪯ r^α] ; XSLICE:HD-r2 [needed: (HD) 2: d > 6 and P_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}] ; XSLICE:HD-r3 [needed: (HD) 3: d = 6, α = 2 and the logarithmic two-point bound; must be read in the repaired log(1+‖·‖) form (hd-log-singularity)] PACKET PROOF_SOURCE: P#S4.SS2.2@L1145-L1159 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:I.2.6`, `XSLICE:I.2.13`, `XSLICE:HD-r2`, `XSLICE:HD-r3` (statements and use sites in §4). The printed exponent is inverted in the primary PDF (p.42) as well as the HTML, so it is a source defect, not a text-layer artefact. The conclusion of Corollary I.4.14 survives in both cases; the *displayed* inequality does not. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed. RESIDUAL OPEN CASE: r>0 at (HD)2 with d>6 and alpha=2 gives only an O(r^alpha) averaged two-point sum, not the required little-o; this residual is not derived by correcting r^{-d} to r^d. Do not delete the statement or assert Hydro from the wrong exponent.

NODE: hutchcroft.i.4.3.s1
KIND: step
TITLE: Case 2: apply [63, Prop. 1.7] twice
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p26.1@L2569-L2569
PROOF_SOURCE: .scratch/source/paper.html#S4.E11@L2570-L2577
CONTRACT_ID: I.4.3.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) case 2: τ(x) ⪯ ‖x‖^{−d+2}; [63, Prop. 1.7] with a = b = 2 and a+b = 4 < d since d > 6
SOURCE_QUANTIFIERS: all x ≠ 0
SOURCE_CONCLUSION: τ*τ(x) ⪯ ‖x‖^{−d+4} and ∇(0,x) ⪯ ‖x‖^{−d+6}; hence ∇_r ⪯ r^{−d+6} and ∫_1^∞ r^{−d+6}dr/r < ∞ because d > 6
CONSTANT_SCOPE: depends on d, α, J
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.hara.prop1.7,hutchcroft.i.4.dsp11
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:HD-r2 [needed: (HD) 2: d > 6 and P_{β_c}(x↔y) ⪯ ‖x−y‖^{−d+2}] PACKET PROOF_SOURCE: P#S4.Thmthm14.2@L1115-L1137 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:HD-r2` (statements and use sites in §4). The extra observation "Σ over ‖x‖ ≥ r of ‖x‖^{−d+6} ⪯ r^{6−d}" is what turns the pointwise bound into ∇_r ⪯ r^{−d+6}; the summability of ‖x‖^{−d+6} over Z^d is false and is not needed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: ext.hara.prop1.7 | .scratch/source/paper.html#S4.SS1.p26.1@L2569-L2569 | packet relation requires: "a standard fact (see [63, Proposition 1.7])", applied twice with a=b=2  [was E077]
EDGE: hutchcroft.i.4.dsp11 | .scratch/source/paper.html#S4.E11@L2570-L2577 | packet relation requires: (I.4.11) is the resulting pointwise bound  [was E078]

NODE: hutchcroft.i.4.3.s2
KIND: step
TITLE: the two-regime convolution bound with logarithmic corrections, and its three-region proof
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E12@L2580-L2589
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p26.3@L2590-L2590
CONTRACT_ID: I.4.3.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: display (I.4.12)'s hypotheses
SOURCE_QUANTIFIERS: all x ∈ Z^d
SOURCE_CONCLUSION: (I.4.12), proved by decomposing Z^d into A_1 = {‖y‖ ≤ ‖x−y‖, ‖y‖ ≤ 2‖x‖}, A_2 = {‖x−y‖ < ‖x‖, ‖y‖ ≤ 2‖x‖}, A_3 = {‖y‖ ≥ 2‖x‖} and summing over box boundaries with ⟨x⟩ = 2+⌈‖x‖⌉
CONSTANT_SCOPE: depends on a,b,â,b̂
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp12
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p28.2.1@L1125-L1133 The final display is an ≍ (both ⪯ and ⪰); only ⪯ is used. The A_2 definition is complete in the pinned corpus: canonical L1125 and HTML L2590 both contain ‖y−x‖<‖x‖ with ‖y‖≤2‖x‖. The claimed truncation belongs to an older, different extraction and must not be attributed to the pinned source. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp12 | .scratch/source/paper.html#S4.SS1.11@L2566-L2621 | the three-region argument proving the (I.4.12) convolution bound is in this proof, not only the display

NODE: hutchcroft.i.4.3.s3
KIND: step
TITLE: Case 3: apply the convolution bound twice and read off log-integrability
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E13@L2610-L2617
PROOF_SOURCE: .scratch/source/paper.html#S4.E11@L2570-L2577
CONTRACT_ID: I.4.3.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) case 3; a = b = 2, â = b̂ = 1, so a+b = d = 6 and â+b̂ = 2 > 1
SOURCE_QUANTIFIERS: all x ≠ 0
SOURCE_CONCLUSION: τ*τ(x) ⪯ ‖x‖^{−d+4}(log(1+‖x‖))^{−2} and ∇(0,x) ⪯ (log(1+‖x‖))^{−2}, hence ∇_r ⪯ (log(1+r))^{−2} which is logarithmically integrable
CONSTANT_SCOPE: implicit constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.dsp12,hutchcroft.i.4.dsp13
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - UNSCHEMAED INPUT CROSS_SLICE: XSLICE:HD-r3 [needed: (HD) 3: d = 6, α = 2 and the logarithmic two-point bound; must be read in the repaired log(1+‖·‖) form (hd-log-singularity)] PACKET PROOF_SOURCE: P#S4.Thmthm14.2@L1115-L1137 Cross-slice obligations, carried as NOTEs and not as edges: `XSLICE:HD-r3` (statements and use sites in §4). At d = 6 the a+b = d branch leaves no power of ‖x‖, which is why the printed numerator 1 is correct and only the parenthesis is lost (§5.5). ∫_1^∞ (log(1+r))^{−2} dr/r < ∞. Consistent with ∫ (log r)^{−2}dlog r. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.dsp12 | .scratch/source/paper.html#S4.E13@L2610-L2617 | packet relation requires: a=b=2, â=b̂=1 with a+b=d and â+b̂>1  [was E081]
EDGE: hutchcroft.i.4.dsp13 | .scratch/source/paper.html#S4.E13@L2610-L2617 | packet relation requires: (I.4.13) is the result, hence log-integrable ∇_r  [was E082]

NODE: hutchcroft.i.4.2.a
KIND: proposition
TITLE: Proposition I.4.2(a): first-moment asymptotics under one of three alternatives
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm2@L2079-L2115
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of (1) d>3alpha; (2) d=3alpha and (Hydro); (3) the triangle condition
SOURCE_QUANTIFIERS: r → ∞; H_r defined for every r > 0
SOURCE_CONCLUSION: E_{β_c,r}|K| ∼ (α/β_c)r^α
CONSTANT_SCOPE: leading constant α/β_c explicit and normalization-dependent; "∼" constant 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.s1
ROUTES: hutchcroft.i.4.2.r1,hutchcroft.i.4.2.r2,hutchcroft.i.4.2.r3
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.4.1@L1108-L1110 (assembly) with cases at L969-L1039 and L1075-L1085 [F2] ROUTES extended to r1-r5: r1-r3 select conclusion (a); r1 and r4 select conclusion (b) first alternative (`d>3α`); r5 selects (b) second alternative (triangle + log-integrable `∇_r`). r1 and r4 have the same hypothesis by the source's design and are kept distinct because they qualify different conclusions; merging them into one route would leave the second conclusion under-described. The three hypotheses are *alternatives*; the paper's phrase "at least one of the three hypotheses of (I.1.3)" points at the (HD) list, but case 2 of this proposition (d=3α + Hydro) is **not** an (HD) case — see §5.7. Case 2 carries no log-integrability of H_r (Remark I.4.4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.2.r1 | .scratch/source/paper.html#S4.I1.i1@L2084-L2087 | packet relation requires: "1. d > 3α" is alternative 1 of the hypothesis list  [was E090]
EDGE: hutchcroft.i.4.2.r2 | .scratch/source/paper.html#S4.I1.i2@L2088-L2091 | packet relation requires: alternative 2  [was E091]
EDGE: hutchcroft.i.4.2.r3 | .scratch/source/paper.html#S4.I1.i3@L2092-L2095 | packet relation requires: alternative 3  [was E092]
EDGE: hutchcroft.i.4.2.s1 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the printed assembly converts the case error bounds via (I.4.7) into the claimed asymptotic; routes alone do not supply this conclusion

NODE: hutchcroft.i.4.2.b
KIND: proposition
TITLE: Proposition I.4.2(b): logarithmic integrability of H_r under the specified alternatives
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm2@L2079-L2115
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: either d>3alpha, or the triangle condition and logarithmic integrability of nabla_r
SOURCE_QUANTIFIERS: r → ∞; H_r defined for every r > 0
SOURCE_CONCLUSION: if d>3alpha or (triangle condition and nabla_r is logarithmically integrable), then H_r is a logarithmically integrable error function
CONSTANT_SCOPE: no asymptotic-equivalence coefficient is claimed here; the conclusion is the stated logarithmic-integrability condition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.s1
ROUTES: hutchcroft.i.4.2.r4,hutchcroft.i.4.2.r5
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROVENANCE: extractor=m6@smwoa6sry (record content) | normalizer=m1@smwobyis9 | reviewer: - PACKET PROOF_SOURCE: P#S4.SS1.p26.4.1@L1108-L1110 (assembly) with cases at L969-L1039 and L1075-L1085 [F2] ROUTES extended to r1-r5: r1-r3 select conclusion (a); r1 and r4 select conclusion (b) first alternative (`d>3α`); r5 selects (b) second alternative (triangle + log-integrable `∇_r`). r1 and r4 have the same hypothesis by the source's design and are kept distinct because they qualify different conclusions; merging them into one route would leave the second conclusion under-described. The three hypotheses are *alternatives*; the paper's phrase "at least one of the three hypotheses of (I.1.3)" points at the (HD) list, but case 2 of this proposition (d=3α + Hydro) is **not** an (HD) case — see §5.7. Case 2 carries no log-integrability of H_r (Remark I.4.4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I41Normalized.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.2.r4 | .scratch/source/paper.html#S4.Thmthm2.p1.3@L2105-L2105 | packet relation requires: first alternative for the second conclusion  [was E093]
EDGE: hutchcroft.i.4.2.r5 | .scratch/source/paper.html#S4.Thmthm2.p1.3@L2105-L2105 | packet relation requires: second alternative for the second conclusion  [was E094]
EDGE: hutchcroft.i.4.2.s1 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | packet relation requires: the proof assembles the three cases  [was E095]

NODE: hutchcroft.i.4.2.ap-hd23
KIND: step
TITLE: SOURCE_GAP: (HD)2/(HD)3 averaged-triangle bridge, not a completed Proposition I.4.2(b) application
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p2@L2116-L2118
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.ap-hd23
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD)2 or (HD)3 in the paper's enumeration only. The triangle condition and Prop I.4.2(b)'s first conjunct are NOT inserted as standing hypotheses. Any remaining discharge is a proof obligation
SOURCE_QUANTIFIERS: r→∞
SOURCE_CONCLUSION: Lemma I.4.3 gives ∇_r logarithmic integrability, and s3 transfers it to r^{-d}Σ_{x∈B_r}∇(0,x). This supplies only the averaged-sum prerequisite of the assembly. It does NOT establish the triangle condition required for a direct application of Proposition I.4.2(b), so it cannot certify that proposition's triangle route by itself
CONSTANT_SCOPE: leading constant α/β_c explicit and normalization-dependent; "∼" constant 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.3,hutchcroft.i.4.2.s3
ROUTES: -
ROUTE_FOR: -
NOTE: CROSS_SLICE/OUTGOING conditional step. The use-site mentions Proposition I.4.2 applying under the (HD) alternatives (canonical text L1112; HTML S4.SS1.p2). The stale L879-L882 citation is withdrawn. Lemma I.4.3 supplies ∇_r via its source bounds, and i.4.2.s3 supplies the averaged-sum bridge. SOURCE_GAP: the direct Prop I.4.2(b) triangle route also needs its first conjunct (triangle condition), which is not an (HD) list premise. A proof from the two-point bounds and norm/volume normalization remains to be recorded and checked; it cannot be replaced by a hidden standing triangle assumption. Any later full application must restore only that discharged dependency and not rewrite this node into a completed proposition
EDGE: hutchcroft.i.4.3 | .scratch/source/paper.html#S4.SS1.p2@L2116-L2118 | Lemma I.4.3 verifies a premise used by the log-integrability branch
EDGE: hutchcroft.i.4.2.s3 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the averaged-sum bridge is what actually follows from ∇_r via a simple variation; this is not a proof of the broader Proposition I.4.2(b) route

NODE: hutchcroft.i.4.12.counterexample
KIND: step
TITLE: Counterexamples to the printed coupling and doorway union bound (not a proof of the five-factor bound)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex20@L2466-L2470
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p19.3@L2483-L2491
CONTRACT_ID: I.4.12.counterexample
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the exact printed coupling assignment and doorway union-bound formulations, on small finite independent-edge graphs
SOURCE_QUANTIFIERS: independent edges with 0<p<1
SOURCE_CONCLUSION: fresh edges can avoid K_0 and disconnect K_y from K̃_y, so K_y⊆K̃_y can fail; the union bound can be exceeded by direct fresh connections outside K_0; the closing identity also omits an event with positive probability
CONSTANT_SCOPE: exact finite counterexamples; no asymptotic constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: counterexamples reconstructed with the independent reviews smwohv6t4/m1 and m3. Direct fresh edges outside K_0 refute both the printed inclusion and union bound; this is additional to the closing-identity error. Nothing here proves the five-factor statement or labels it false.

NODE: hutchcroft.a.norm
KIND: assumption
TITLE: standing normalization (∗) of Definition I.1.3 — `|J'(r)| ~ r^{-d-alpha-1}` and `|B_r| := |{x : ||x|| <= r}| ~ r^d`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm3@L370-L416
PROOF_SOURCE: -
CONTRACT_ID: I.1.3.norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: translation-invariant decreasing differentiable kernel `J(x,y)=1(x!=y)J(||x-y||)`, `|J'(r)|=C(1+delta_r)r^{-d-alpha-1}` with `delta` logarithmically integrable, normalized so that `||.||`'s unit ball has unit Lebesgue measure and `C=1`
SOURCE_QUANTIFIERS: `r -> infinity` (both asymptotic relations)
SOURCE_CONCLUSION: `|J'(r)| ~ r^{-d-alpha-1}`, `|B_r| ~ r^d`, hence `|J'(r)||B_r| ~ r^{-alpha-1}` and `|B_R|/|B_r| ~ (R/r)^d` for `R = R(r) -> infinity`, `R = o(r)`
CONSTANT_SCOPE: only the comparison constants implicit in `~`; `(∗)` is a normalization, not a rate
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: - (definition, no proof obligation) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Leaf by design: a standing hypothesis of the whole paper, not proved in this slice. Consumed by `hutchcroft.i.4.15.s1` (via `(1-E_{0,r}) := |J'(r)||B_r|/r^{-alpha-1}`, XSLICE), by `hutchcroft.i.4.18.pf` (`|B_R|` step) and by `hutchcroft.i.4.18.ell3.s2` (the ratio `|B_{r^theta}|/|B_r|`). No consumer here needs anything beyond these two asymptotics. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.

NODE: hutchcroft.a.cutoff
KIND: assumption
TITLE: Definition I.1.5 — the cut-off kernel `J_r`, the law `P_{beta,r}`, and subcriticality of `P_{beta_c,r}` at finite `r`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm5@L435-L448
PROOF_SOURCE: -
CONTRACT_ID: I.1.5.cutoff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `J_r(x,y) = 1(x!=y, ||x-y||<=r) int_{||x-y||}^{r}|J'(s)|ds`; `beta_c` is critical for the *original* kernel `J`
SOURCE_QUANTIFIERS: every `r<infinity`, every `beta`
SOURCE_CONCLUSION: `J_r(x,y) ≤ (1−ε(r))J(x,y)` for all x≠y, with ε(r)>0, so P_{β_c,r} is stochastically dominated by P_{(1−ε(r))β_c} and is subcritical.
CONSTANT_SCOPE: `eps=eps(r)>0` finite-`r` only; no uniform-in-`r` constant is asserted or used
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: - (definition + quoted monotone-domination remark, no proof obligation) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Leaf. *Only* used to make denominators legal: `|B_r| E_{beta_c,r}|K| E_{beta_c,r}|K|^2 > 0` and finite in `(I.4.14)`, `(I.4.15)`, `(I.4.16)` (see §7 C21). Also gives `tau_r(x) <= tau_{beta_c}(x)` used for (a) `nabla_{beta_c,r}(0,x) <= nabla_{beta_c}(0,x)` inside `hutchcroft.i.4.18.ell3` and (b) the replacement `P_{beta_c,r} -> P_{beta_c}` in `hutchcroft.i.4.15.s3`. Both monotonicity readings are consequences of `J_r <= J` pointwise plus the standard monotone coupling; they are *uses*, not restatements, of this leaf. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. T3 CORRECTION: finite all-moment finiteness and E|K|>=1 are derived obligations, not printed conclusions. The canonical candidate owning that gap is hutchcroft.i.1.5.step.cutoffmoments in I.1; a merge must not infer it from subcriticality alone.

NODE: hutchcroft.a.hydro
KIND: definition
TITLE: Definition I.1.14 (Hydro) — the hydrodynamic condition `M_r = o(r^{(d+alpha)/2})`
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm14@L888-L901
PROOF_SOURCE: -
CONTRACT_ID: I.1.14.hydro
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: — (a definition of a property of the model)
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `M_r = o(r^{(d+alpha)/2})`, where `M_r := M_{beta_c,r}` is the typical largest cluster volume in the box of radius `r` as defined in Section I.2.1 (XSLICE)
CONSTANT_SCOPE: the `o(1)` is a rate, not a constant; no comparison constant is asserted
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - Leaf. **Not** the display `(I.1.14)` (= ξ₂ asymptotics, `S1.E14@L825-L838`): see defect D1. Wire this to Definition I.1.14 only. Consumed by `hutchcroft.i.4.15.c2` and `hutchcroft.i.4.20.c2`, in both cases *only* through `M_r^{1/2} = o(r^{(d+alpha)/4})`. `M_r` itself is defined in Section I.2.1 (XSLICE(I.2)); the definition is not re-established here. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. SCOPING CORRECTION: reclassified from KIND: assumption to KIND: definition with LEAN_STATUS: NOT_STARTED, so that KIND and status agree. `_validate_topology` requires every KIND: assumption node to be declared in STANDING_ASSUMPTIONS and every declared standing assumption to be KIND: assumption, so recording this condition as an assumption promoted it to a premise of the whole packet -- in the merged file all three mutually alternative conditions (d = 3α plus Hydro, the triangle condition, and log-integrability of ∇_r) were declared together. It is a definition of a condition, quoted from the source, consumed only at hutchcroft.i.4.15.c2, hutchcroft.i.4.20.c2 and hutchcroft.i.4.2.r2. A header declaration is not permission to use two alternatives conjunctively, and no closure may be read as asserting them together. The duplicate duty is flagged, not resolved: see hutchcroft.i.1.14 for (Hydro).

NODE: hutchcroft.a.triangle
KIND: definition
TITLE: the triangle condition at `beta_c` — `nabla := nabla_{beta_c}(0,0) = sum_{x,y} P(0<->x)P(x<->y)P(y<->0) < infinity`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p1.1@L2077-L2077
PROOF_SOURCE: -
CONTRACT_ID: I.4.triangle
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model and cut-off definitions are in force; the triangle condition is an additional source hypothesis
SOURCE_QUANTIFIERS: the condition at beta_c; nontrivial sums range over ordered pairs of lattice vertices
SOURCE_CONCLUSION: `nabla_{beta_c} < infinity` (the *diagonal* value of the open triangle), with `nabla_{beta_c}(0,x) := sum_{y,z} tau(0,y)tau(y,z)tau(z,x)` and `nabla_{beta_c,r}(0,x) <= nabla_{beta_c}(0,x)` for the cut-off law
CONSTANT_SCOPE: the finite value `nabla_{beta_c}` itself is the only constant; it is used as a bound for the *near part only* (see `hutchcroft.i.4.18.ell3` NOTE — it is **never** used as a bound for `sum_{y in B_r} nabla(0,y)`, which diverges at criticality)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - Leaf, third alternative of Prop I.4.2 / Prop I.4.15 / Prop I.4.20. Consumed by `i.4.18.pf`, `i.4.18.ell3.s2`, `i.4.15.c3`, `i.4.20.c3`. This is the hypothesis under which `nabla_{r^c}` and `nabla_{r^theta}` are finite for all `r`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. SCOPING CORRECTION: reclassified from KIND: assumption to KIND: definition with LEAN_STATUS: NOT_STARTED, so that KIND and status agree. `_validate_topology` requires every KIND: assumption node to be declared in STANDING_ASSUMPTIONS and every declared standing assumption to be KIND: assumption, so recording this condition as an assumption promoted it to a premise of the whole packet -- in the merged file all three mutually alternative conditions (d = 3α plus Hydro, the triangle condition, and log-integrability of ∇_r) were declared together. It is a definition of a condition, quoted from the source, consumed only at hutchcroft.i.4.18.pf, hutchcroft.i.4.18.ell3(.s1/.s2), hutchcroft.i.4.15.c3, hutchcroft.i.4.20.c3 and hutchcroft.i.4.2.r3/r5. A header declaration is not permission to use two alternatives conjunctively, and no closure may be read as asserting them together. The duplicate duty is flagged, not resolved: see hutchcroft.i.1.14 for (Hydro).

NODE: hutchcroft.a.tri.tail
KIND: step
TITLE: open-triangle tail decay `nabla_r := sup_{||x||>=r} nabla_{beta_c}(0,x) -> 0`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.p1.1@L2077-L2077
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.p1.1@L2077-L2077
CONTRACT_ID: I.4.triangle.tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition (`hutchcroft.a.triangle`)
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `nabla_r -> 0`
CONSTANT_SCOPE: no rate is asserted; only convergence
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.triangle
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: asserted with a two-item citation whose exact statement was not opened. Finite ∇(0,0) alone does not yield ∇_r→0: the ball total triangle mass can diverge at criticality. This remains an open obligation, not an external-leaf discharge.UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: - (source attributes it to `[83,12]`; **not verified here — title-only reference, therefore not an external leaf**) UNLOCATED PROOF DESCRIPTION: no explicit proof locator was supplied Leaf **carried as an explicit hypothesis, not discharged**. The source states it ("which goes to zero as `r->infinity` whenever the triangle condition holds `[83,12]`") with a two-item citation that I did not open, so it is *not* a verified external leaf and I did not create an `external` node for it. Merge obligation: discharge from `nabla_{beta_c}<infinity` + a continuity/monotonicity argument, or attach a checked literature leaf. Without it, `c3`-type bounds give only boundedness, not `o(1)`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.SS1.p1.1@L2077-L2077 | SOURCE_GAP: source citation [83,12] supplies open-triangle decay at the consumer site; not derived from the finite diagonal value in this slice

NODE: hutchcroft.a.logint
KIND: definition
TITLE: logarithmic integrability of `nabla_r` — `int_{r_0}^{infinity} |nabla_r| dr/r < infinity`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm15@L2671-L2676
PROOF_SOURCE: -
CONTRACT_ID: I.4.triangle.logint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition and the additional logarithmic-integrability hypothesis
SOURCE_QUANTIFIERS: r increases to infinity; some finite lower integration limit r_0 is chosen
SOURCE_CONCLUSION: `r |-> nabla_r` is logarithmically integrable in the paper's sense (locally integrable on some `[r_0,infinity)` and `int_{r_0}^{infinity}|nabla_r| dr/r < infinity`)
CONSTANT_SCOPE: no implicit multiplicative constant; finiteness of the logarithmic integral is the content
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.Thmthm15@L2671-L2676 and #S4.Thmthm18@L2930-L2943 (both state it as an additional hypothesis) ; Leaf. Needed **only** for the *second* conclusion of Prop I.4.15 (`E|K|^2 ~ A r^{3alpha}`) in the triangle branch, and nowhere in Prop I.4.20 (which only needs `o(1)`). Under (HD) cases 2,3 it is supplied elsewhere: Lemma I.4.3 (XSLICE I.4.1) derives it from the two-point upper bound; that derivation is *not* re-proved here and is itemised in §6. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. SCOPING CORRECTION: reclassified from KIND: assumption to KIND: definition with LEAN_STATUS: NOT_STARTED, so that KIND and status agree. `_validate_topology` requires every KIND: assumption node to be declared in STANDING_ASSUMPTIONS and every declared standing assumption to be KIND: assumption, so recording this condition as an assumption promoted it to a premise of the whole packet -- in the merged file all three mutually alternative conditions (d = 3α plus Hydro, the triangle condition, and log-integrability of ∇_r) were declared together. It is a definition of a condition, quoted from the source, consumed only at hutchcroft.i.4.15.s2, hutchcroft.i.4.18.ell3(.s2), hutchcroft.i.4.19 and hutchcroft.i.4.2.r5. A header declaration is not permission to use two alternatives conjunctively, and no closure may be read as asserting them together. The duplicate duty is flagged, not resolved: see hutchcroft.i.1.14 for (Hydro).

NODE: hutchcroft.i.4.15
KIND: proposition
TITLE: Proposition I.4.15 — second-moment asymptotics: `r |-> E_{beta_c,r}|K|^2` is regularly varying of index `3alpha`, and `~ A r^{3alpha}` in the regimes with a logarithmically integrable error
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm15@L2671-L2676
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.2@L2680-L2798
CONTRACT_ID: I.4.15
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of routes `r1` (`d>3alpha`), `r2` (`d=3alpha` and (Hydro)), `r3` (triangle condition); the *second* conclusion additionally needs `d>3alpha` **or** (`r3` and `nabla_r` logarithmically integrable)
SOURCE_QUANTIFIERS: `r -> infinity`; `A` is a single constant (not a function of `r`)
SOURCE_CONCLUSION: (a) `r |-> E_{beta_c,r}|K|^2` is regularly varying of index `3alpha`; (b) if `d>3alpha` or (`r3` and `nabla_r` log-integrable) then `E_{beta_c,r}|K|^2 ~ A r^{3alpha}` for some constant `A`
CONSTANT_SCOPE: `A` unspecified but `A > 0` (follows: `E|K|^2 >= c (E|K|)^3` in the two regimes, §7 C18); "`~`" constant `1`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: hutchcroft.i.4.15.r1,hutchcroft.i.4.15.r2,hutchcroft.i.4.15.r3
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.2@L2680-L2798 (Cases 1 and 2) with paper.html#S4.SS2.7@L3001-L3030 (Case 3) The three alternatives are **alternatives**, never conjoined. The printed statement does not say `A>0`; positivity is derivable (C18) and is recorded in `CONSTANT_SCOPE` as a derived, not printed, strengthening. Statement PASS; proofs open (§4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.r1 | .scratch/source/paper.html#S4.Thmthm15@L2671-L2676 | packet relation requires: first alternative of the statement ("If any of the three conditions ... hold") realised as d>3alpha [ATTRIBUTION unique exact use-site match; line 661]
EDGE: hutchcroft.i.4.15.r2 | .scratch/source/paper.html#S4.Thmthm15@L2671-L2676 | packet relation requires: second alternative realised as d=3alpha + (Hydro) [ATTRIBUTION unique exact use-site match; line 662]
EDGE: hutchcroft.i.4.15.r3 | .scratch/source/paper.html#S4.Thmthm15@L2671-L2676 | packet relation requires: third alternative realised as the triangle condition [ATTRIBUTION unique exact use-site match; line 663]

NODE: hutchcroft.i.4.15.r1
KIND: route
TITLE: Prop I.4.15, route 1 — `d > 3alpha`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p4.1@L2758-L2758
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p4@L2757-L2775
CONTRACT_ID: I.4.15.r1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `alpha>0`, `d>3alpha`
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: both conclusions (a) and (b)
CONSTANT_SCOPE: as the proposition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s1,hutchcroft.i.4.15.s2,hutchcroft.i.4.15.c1,hutchcroft.i.4.15.s4
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.15
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.p4@L2757-L2775 Carries the *stronger* conclusion (b) without any log-integrability hypothesis, because `E_{2,r} <= C r^{3alpha-d}` is itself log-integrable when `d>3alpha` (§7 C11) and `H_r` is log-integrable in this case by Prop I.4.2 route 1 (XSLICE). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s1 | .scratch/source/paper.html#S4.SS2.p4.1@L2758-L2758 | packet relation requires: Case 1 starts from the rewritten identity (I.4.14)/(I.4.15) produced by s1 [ATTRIBUTION unique exact use-site match; line 664]
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.SS2.p4.1@L2758-L2758 | packet relation requires: Case 1 bounds the E_{2,r} of s2 by (I.4.16) [ATTRIBUTION unique exact use-site match; line 665]
EDGE: hutchcroft.i.4.15.c1 | .scratch/source/paper.html#S4.SS2.p4.1@L2758-L2758 | packet relation requires: Case 1's estimate E_{2,r} <= (E∣K∣)^3/∣B_r∣ <= r^{3alpha-d} [ATTRIBUTION unique exact use-site match; line 666]
EDGE: hutchcroft.i.4.15.s4 | .scratch/source/paper.html#S4.SS2.p4.3@L2774-L2774 | packet relation requires: "is logarithmically integrable as required" is the ODE conclusion s4 draws [ATTRIBUTION coordinator attribution: case-1 proof block in declared route-1 source; line 667]

NODE: hutchcroft.i.4.15.r2
KIND: route
TITLE: Prop I.4.15, route 2 — `d = 3alpha` and (Hydro)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p5.1@L2777-L2777
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p5@L2776-L2797
CONTRACT_ID: I.4.15.r2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d = 3alpha`; `M_r = o(r^{(d+alpha)/2})`
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: conclusion (a) **only**; (b) is not claimed in this case
CONSTANT_SCOPE: as the proposition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s1,hutchcroft.i.4.15.s2,hutchcroft.i.4.15.c2,hutchcroft.i.4.15.s4
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.15
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.p5@L2776-L2797 The exclusion of (b) here is deliberate and is the whole point of the section: at `d=3alpha<6` the error `H_r` is *not* logarithmically integrable (tex L886, `paper-tex.txt L886`, in the I.4.1 slice) and the second moment acquires a logarithmic correction, so no constant `A` exists. Do not add (b) to this route. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s1 | .scratch/source/paper.html#S4.SS2.p5.1@L2777-L2777 | packet relation requires: Case 2 starts from the same (I.4.14)/(I.4.15) [ATTRIBUTION unique exact use-site match; line 668]
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.SS2.p5.1@L2777-L2777 | packet relation requires: Case 2 bounds (I.4.16)'s right side by Cauchy-Schwarz [ATTRIBUTION unique exact use-site match; line 669]
EDGE: hutchcroft.i.4.15.c2 | .scratch/source/paper.html#S4.SS2.p5.1@L2777-L2777 | packet relation requires: Case 2's (I.4.17) and (I.4.18) are c2's content [ATTRIBUTION unique exact use-site match; line 670]
EDGE: hutchcroft.i.4.15.s4 | .scratch/source/paper.html#S4.SS2.p5.3@L2795-L2796 | packet relation requires: "the final equality holds since d=3alpha" is the ODE conclusion s4 draws [ATTRIBUTION coordinator attribution: case-2 proof block in declared route-2 source; line 671]

NODE: hutchcroft.i.4.15.r3
KIND: route
TITLE: Prop I.4.15, route 3 — the triangle condition
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p14.1@L2999-L2999
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.7@L3001-L3030
CONTRACT_ID: I.4.15.r3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `nabla < infinity` (triangle condition)
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: (a); and (b) whenever in addition `nabla_r` is logarithmically integrable
CONSTANT_SCOPE: as the proposition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s1,hutchcroft.i.4.15.s2,hutchcroft.i.4.15.c3,hutchcroft.i.4.15.s3,hutchcroft.i.4.15.s4
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.15
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.7@L3001-L3030 This is the only route that consumes the repaired `ell=3` polygon bound (`hutchcroft.i.4.18.ell3`). Its `(E|K|)^2 >> (E|K|)^3` lower bound (`s3`) is *inside* the same proof and is not available from route 1 or 2. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s1 | .scratch/source/paper.html#S4.SS2.p14.1@L2999-L2999 | packet relation requires: Case 3 also starts from (I.4.14)/(I.4.15) [ATTRIBUTION unique exact use-site match; line 672]
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.SS2.p14.1@L2999-L2999 | packet relation requires: "suffices to show E_{2,r} -> 0" uses the (I.4.16) bound [ATTRIBUTION unique exact use-site match; line 673]
EDGE: hutchcroft.i.4.15.c3 | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: the displayed bound E_{2,r} <= C(nabla_{r^c}+r^{-c})(E∣K∣)^4/(E∣K∣E∣K∣^2) [ATTRIBUTION coordinator attribution: only declared consumer of c3; case-3 display; line 674]
EDGE: hutchcroft.i.4.15.s3 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: "it suffices to prove E∣K∣^2 >> (E∣K∣)^3 >> r^{3alpha}" is s3 [ATTRIBUTION coordinator attribution: only declared consumer of s3; case-3 proof; line 675]
EDGE: hutchcroft.i.4.15.s4 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: the case-3 conclusion is again drawn through the ODE (s4) [ATTRIBUTION coordinator attribution: case-3 ODE conclusion in route-3 proof; line 676]

NODE: hutchcroft.i.4.15.s1
KIND: step
TITLE: the `p=2` expansion of `(I.4.1)`, its mass-transport collapse, the error `E_{2,r}`, and the exact ODE `(I.4.15)`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p3.1@L2683-L2683
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p3.1@L2683-L2683
CONTRACT_ID: I.4.15.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: cut-off law at `beta_c` (so all moments finite)
SOURCE_QUANTIFIERS: every `r>0`
SOURCE_CONCLUSION: (i) `d/dr E|K|^2 = beta_c|J'|E[sum_{y in B_r}1(y notin K)|K||K_y|^2] + 2 beta_c|J'|E[sum_{y in B_r}1(y notin K)|K|^2|K_y|] = 3 beta_c|J'|E[sum_{y in B_r}1(y notin K)|K||K_y|^2] = 3(1-E_{2,r}) beta_c|J'||B_r|E|K|E|K|^2` (this is `(I.4.14)`); (ii) `E_{2,r} := (|B_r|E|K|E|K|^2 - E[|K|sum_{y in B_r}1(y notin K)|K_y|^2])/(|B_r|E|K|E|K|^2) = (|B_r|E|K|E|K|^2 - E[|K|sum_{y in B_r}|K_y|^2] + E[|K|^3|K cap B_r|])/(|B_r|E|K|E|K|^2)`; (iii) `(1-\overline{E}_{2,r}) := (1-E_{2,r})(|J'(r)||B_r|/r^{-alpha-1})(E|K|/((alpha/beta_c)r^alpha)) = (1-E_{2,r})(1+H_r)(1-E_{0,r})`, hence `d/dr E|K|^2 = 3alpha(1-\overline{E}_{2,r})r^{-1}E|K|^2`
CONSTANT_SCOPE: exact identity: only `beta_c`, `|J'(r)|`, `|B_r|`, binomial coefficients `C(2,0)=1, C(2,1)=2`; no implicit constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.norm,hutchcroft.a.cutoff
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same block (it *is* the derivation) PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p3.1@L2683-L2683, #S4.EGx12@L2684-L2702, #S4.SS2.p3.2@L2703-L2703, #S4.SS2.p3.3@L2704-L2712, #S4.Ex34@L2714-L2720, #S4.E15@L2722-L2729 ; XSLICE(I.4.1): `(I.4.1)` = Lemma I.4.1 (`hutchcroft.i.4.1`), and the definitions `(1-E_{0,r}) := |J'(r)||B_r|/r^{-alpha-1}`, `H_r := (beta_c/alpha)r^{-alpha}E|K|-1` (tex L899, L874; I.4.1 slice). The ℓ=0 and ℓ=1 terms of `(I.4.1)` are equal by mass transport (`y<->x` swap of `|K|` and `|K_y|`), giving the coefficient `1+2 = 3`: index shift checked, §7 C22. The second display of (ii) is the exact decomposition `1(y notin K) = 1 - 1(y in K)` **with** `K_y = K` on `{y in K}` — that is where `|K|^3 |K cap B_r|` comes from; no inequality is used here. Defect warning: the sign in `(1-E_{0,r})` is *fixed by this definition*, so `(I.4.15)` is an identity, not an estimate. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex34@L2714-L2720 | packet relation requires: (1-\bar E_{2,r}) is rewritten with ∣J'(r)‖B_r∣/r^{-alpha-1}, i.e. with (∗) [ATTRIBUTION unique exact use-site match; line 677]
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.SS2.p3.3@L2704-L2712 | packet relation requires: the decomposition 1(y notin K)=1-1(y in K) and K_y=K on {y in K} are exact pointwise identities (no expectation needed) [ATTRIBUTION unique exact use-site match; line 678]

NODE: hutchcroft.i.4.15.s2
KIND: step
TITLE: the two-sided bound `(I.4.16)`: `0 <= E_{2,r} <= E[|K|^3|K cap B_r|]/(|B_r| E|K| E|K|^2)`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.E16@L2732-L2739
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p3.6@L2730-L2731
CONTRACT_ID: I.4.15.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as `s1`
SOURCE_QUANTIFIERS: every `r>0`
SOURCE_CONCLUSION: `0 <= E_{2,r} <= E[|K|^3|K cap B_r|]/(|B_r|E|K|E|K|^2)`
CONSTANT_SCOPE: exact (`<=`, no constant)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s1,hutchcroft.a.cutoff,ext.bk.extensions
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS2.p3.6@L2730-L2731 PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.E16@L2732-L2739 with #S4.SS2.p3.6@L2730-L2731 ; XSLICE(I.2): Lemma I.2.1 supplies `E[|K| sum_{y in B_r}|K_y|^2] <= |B_r| E|K| E|K|^2` (two-cluster / BK factorization), which gives the lower bound `0 <= E_{2,r}`; the upper bound is the numerator identity of `s1` discarding the non-negative term `|B_r|E|K|E|K|^2 - E[|K|sum_y|K_y|^2]`. The lower bound is *not* from the displayed fraction but from that BK inequality — recorded because an earlier packet got the sandwich direction wrong by attributing `0 <=` to the fraction. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s1 | .scratch/source/paper.html#S4.E16@L2732-L2739 | packet relation requires: (I.4.16)'s numerator is s1's numerator identity, and its lower bound 0 is the BK input [ATTRIBUTION unique exact use-site match; line 679]
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.E16@L2732-L2739 | packet relation requires: makes ∣B_r∣E∣K∣E∣K∣^2 finite and strictly positive so (I.4.16) is a genuine two-sided bound [ATTRIBUTION unique exact use-site match; line 680]
EDGE: ext.bk.extensions | .scratch/source/paper.html#S4.SS2.p3.6@L2730-L2731 | CROSS_SLICE: the non-negative cluster-gap decomposition uses the disjoint-occurrence/BK input retained in the I.2/I.3 candidate

NODE: hutchcroft.i.4.15.c1
KIND: step
TITLE: Case 1 (`d>3alpha`): `0 <= E_{2,r} <= (E|K|)^3/|B_r| <= C r^{3alpha-d}`, which is logarithmically integrable
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p4@L2757-L2775
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p4@L2757-L2775
CONTRACT_ID: I.4.15.c1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d>3alpha`; `E|K| ~ (alpha/beta_c)r^alpha` (route-1 half of Prop I.4.2, XSLICE)
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `E[|K|^3|K cap B_r|] <= E|K|^4 <= 15 E|K|^2 (E|K|)^4`, hence `0 <= E_{2,r} <= (E|K|)^3/|B_r| <= C r^{3alpha-d}`, and `r |-> E_{2,r}` is logarithmically integrable
CONSTANT_SCOPE: `15 = (2*4-3)!!` from Lemma I.4.16 at `p=4, k=1`; the final `C` is a product of the `~`-constants of `(∗)` and Prop I.4.2; no other constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s2,hutchcroft.i.4.16,hutchcroft.a.norm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p4@L2757-L2775, #S4.Ex36@L2759-L2765, #S4.Ex37@L2767-L2773 ; `(E|K|)^3/|B_r| ~ r^{3alpha-d}` uses `|B_r| ~ r^d`; the middle term of `(I.4.8)`-type bounds `3(E|K|)^3/|B_r|` would also be legal but is not needed. Log-integrability: `3alpha-d-1 < -1` iff `d>3alpha` (§7 C11) — strictly, so `d = 3alpha` is *not* covered by Case 1 (there `r^0` is not integrable). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.Ex36@L2759-L2765 | packet relation requires: Case 1 inserts (I.4.16) and then bounds E[∣K∣^3∣K cap B_r∣] by tree-graph [ATTRIBUTION unique exact use-site match; line 681]
EDGE: hutchcroft.i.4.16 | .scratch/source/paper.html#S4.Ex36@L2759-L2765 | packet relation requires: Case 1 uses Lemma I.4.16 with p=4, k=1 (15 (E∣K∣^2)(E∣K∣)^4) [ATTRIBUTION unique exact use-site match; line 682]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex37@L2767-L2773 | packet relation requires: (E∣K∣)^3/∣B_r∣ <= C r^{3alpha-d} uses ∣B_r∣ ~ r^d [ATTRIBUTION unique exact use-site match; line 683]

NODE: hutchcroft.i.4.15.c2
KIND: step
TITLE: Case 2 (`d=3alpha` + (Hydro)): Cauchy–Schwarz plus the generalized tree-graph inequality at `p=6, k=2` give `(I.4.17)` and then `(I.4.18)`, `E_{2,r} = o(1)`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p5@L2776-L2797
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p5@L2776-L2797
CONTRACT_ID: I.4.15.c2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d = 3alpha`; `M_r = o(r^{(d+alpha)/2})`; `E|K| ~ (alpha/beta_c)r^alpha`; `E|K cap B_r|^2 <= M_r E|K cap B_r| <= M_r E|K|`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `E[|K|^3|K cap B_r|] <= sqrt(E|K|^6 E|K cap B_r|^2) <= C sqrt((E|K|^2)^2 (E|K|)^5 r^alpha M_r)`, hence `E_{2,r} = o(r^{2alpha-d+(d+alpha)/4}) = o(1)` at `d=3alpha`
CONSTANT_SCOPE: `C = (9!!)^{1/2} = 945^{1/2}` from Lemma I.4.16 at `p=6, k=2`; then `(∗)` and (Hydro) rates
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s2,hutchcroft.i.4.16,hutchcroft.a.hydro,hutchcroft.a.norm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p5@L2776-L2797, #S4.E17@L2778-L2785, #S4.E18@L2787-L2794 ; Index check (§7 C10/C10b): `2alpha-d+(d+alpha)/4 = 3(3alpha-d)/4`, so it is `0` exactly at `d=3alpha` and the `o(1)` comes *only* from (Hydro) through `M_r^{1/2} = o(r^{(d+alpha)/4})`; if (Hydro) were weakened to `M_r <= C r^{(d+alpha)/2}` this step would give only `O(1)`. XSLICE(I.2): Corollary I.2.5 (universal tightness) and Theorem I.2.13 (two-point upper bound). No log-integrability is claimed in this case (correctly: `H_r` is not log-integrable at `d=3alpha<6`). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.E17@L2778-L2785 | packet relation requires: Case 2 starts from (I.4.16) and applies Cauchy-Schwarz to its right side [ATTRIBUTION unique exact use-site match; line 684]
EDGE: hutchcroft.i.4.16 | .scratch/source/paper.html#S4.E17@L2778-L2785 | packet relation requires: Case 2 uses Lemma I.4.16 with p=6, k=2: E∣K∣^6 <= 945 (E∣K∣^2)^2(E∣K∣)^5 [ATTRIBUTION unique exact use-site match; line 685]
EDGE: hutchcroft.a.hydro | .scratch/source/paper.html#S4.E18@L2787-L2794 | packet relation requires: E_{2,r} = o(r^{2alpha-d+(d+alpha)/4}) needs M_r^{1/2} = o(r^{(d+alpha)/4}), i.e. exactly (Hydro) [ATTRIBUTION unique exact use-site match; line 686]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.E18@L2787-L2794 | packet relation requires: the exponents 2alpha-d+(d+alpha)/4 and r^{alpha}=E∣K∣ comparison use ∣B_r∣ ~ r^d [ATTRIBUTION unique exact use-site match; line 687]

NODE: hutchcroft.i.4.15.c3
KIND: step
TITLE: Case 3 (triangle condition): `E_{2,r} <= C (nabla_{r^c}+r^{-c}) (E|K|)^4/(E|K| E|K|^2)`, hence `E_{2,r} -> 0`, log-integrable when `nabla_r` is logarithmically integrable
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p15.1@L3004-L3005
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.7@L3001-L3030
CONTRACT_ID: I.4.15.c3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition; `nabla_r` log-integrable *(only for the log-integrability clause)*; `E|K| ~ (alpha/beta_c)r^alpha`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `E_{2,r} <= C(nabla_{r^c}+r^{-c})(E|K|)^4/(E|K|E|K|^2)`; `E_{2,r} -> 0`; `r |-> E_{2,r}` logarithmically integrable whenever `nabla_r` is logarithmically integrable
CONSTANT_SCOPE: `C = C_{2,1,3}+C_{2,1,4}` (universal integers of Lemma I.4.17) times the constant of Lemma I.4.18; `c>0` free and re-chosen; **plus** the repaired `ell=3` constant `C_0` of `hutchcroft.i.4.18.ell3`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s2,hutchcroft.i.4.17,hutchcroft.i.4.18,hutchcroft.i.4.18.ell3,hutchcroft.i.4.19,hutchcroft.a.triangle,hutchcroft.a.tri.tail,hutchcroft.a.logint,hutchcroft.a.norm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same, together with #S4.SS2.7@L3001-L3030 PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p15.1@L3004-L3005, #S4.Ex56@L3006-L3012, #S4.SS2.p15.2@L3013-L3013 ; Derivation I checked symbol by symbol (§7 C7): Lemma I.4.17 with `(p,q) = (2,1)` runs `ell = 3,4` only; the `ell=4` term is `<= C(nabla_{r^c}+r^{-c})(E|K|)^{4-3}(E|K|)^{7-4} = C(nabla_{r^c}+r^{-c})(E|K|)^4`, and the `ell=3` term is `<= C G_r(theta)(E|K|)^4` with `G_r(theta) := nabla_{r^theta} + C_0 r^{-d(1-theta)}nabla_{beta_c}` from the **repair** (the printed `ell=3` bound is false). So the honest bound is `E_{2,r} <= C(nabla_{r^c}+r^{-c}+G_r(theta))(E|K|)^4/(E|K|E|K|^2)`; since the three terms each `-> 0` and each is separately log-integrable, splitting into them needs **no comparison** between them and the printed expression (this is the "re-chosen constants" point). Then `(E|K|)^4/(E|K|E|K|^2) ~ 1` by `s3` (`E|K|^2 ≍ (E|K|)^3`). Do **not** replace `G_r` by `nabla_{beta_c}` (see `i.4.18.ell3` NOTE). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s2 | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: the Case 3 right side is (I.4.16)'s numerator divided by ∣B_r∣E∣K∣E∣K∣^2 [ATTRIBUTION unique exact use-site match; line 688]
EDGE: hutchcroft.i.4.17 | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: Case 3 applies Lemma I.4.17 with (p,q)=(2,1) to the numerator, ell=3,4 [ATTRIBUTION unique exact use-site match; line 689]
EDGE: hutchcroft.i.4.18 | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: the ell=4 term is bounded with the (restricted) polygon bound at ell=4 [ATTRIBUTION unique exact use-site match; line 690]
EDGE: hutchcroft.i.4.18.ell3 | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: the ell=3 term has no printed bound (refuted); this node supplies the averaged replacement [ATTRIBUTION unique exact use-site match; line 691]
EDGE: hutchcroft.i.4.19 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: "(nabla_{r^c}+r^{-c}) ... is logarithmically integrable whenever nabla_r is by Lemma I.4.19" [ATTRIBUTION unique exact use-site match; line 692]
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: "If the triangle condition holds then (nabla_{r^c}+r^{-c}) converges to zero" [ATTRIBUTION unique exact use-site match; line 693]
EDGE: hutchcroft.a.tri.tail | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: the r^{-c} and nabla_{r^c} terms are small only through the triangle tail [ATTRIBUTION unique exact use-site match; line 694]
EDGE: hutchcroft.a.logint | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: the log-integrability clause of c3 is conditional on nabla_r being log-integrable [ATTRIBUTION unique exact use-site match; line 695]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex56@L3006-L3012 | packet relation requires: E∣K∣ ~ r^alpha and (E∣K∣^2)^(-1) ~ r^{-3alpha} are used to reduce the ratio to O(1) [ATTRIBUTION unique exact use-site match; line 696]

NODE: hutchcroft.i.4.15.s3
KIND: step
TITLE: Case 3 lower bound: `E|K|^2 >> (E|K|)^3 >> r^{3alpha}` from the volume-tail upper bound `P(|K|>=n) <= C n^{-1/2}` and the optimizing choice `N = ceil((E|K|^2)^{2/3})`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013
CONTRACT_ID: I.4.15.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition; the volume-tail upper bound `P_{beta_c}(|K|>=n) <= C n^{-1/2}` at `d>6` (cited `[12,75]`, and the triangle condition is what makes it available)
SOURCE_QUANTIFIERS: every `r>0`, every integer `N>=1`, then `r -> infinity`
SOURCE_CONCLUSION: `E|K| <= C(N^{1/2}+N^{-1}E|K|^2)`; optimizing `N = ceil((E|K|^2)^{2/3})` gives `E|K| <= C (E|K|^2)^{1/3}`, i.e. `E|K|^2 >> (E|K|)^3`
CONSTANT_SCOPE: `C` absorbs the tail constant and `sqrt(2)`-type factors only; the exponent `1/3` is exact (§7 C17)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.cutoff,hutchcroft.eq.i.2.3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p15.2@L3013-L3013, #S4.EGx17@L3014-L3026, #S4.SS2.p15.3@L3027-L3028 ; Two substantive uses, both recorded because they are easy to drop: (i) `sum_{n=1}^{N}P_{beta_c}(|K|>=n)` is bounded with the **unrestricted** measure while the left side is under `P_{beta_c,r}`; the replacement is legal by `tau_r <= tau_{beta_c}` from `hutchcroft.a.cutoff`; (ii) `E|K| ~ (alpha/beta_c)r^alpha` (Prop I.4.2, XSLICE) turns `(E|K|^2)^{1/3} >= c r^alpha` into `E|K|^2 >> r^{3alpha}`. XSLICE(I.3): the volume tail is Proposition I.3.2 / §I.3.2; XSLICE external literature `[12,75]` is **title-only here and is not an external leaf**. The complementary upper bound `E|K|^2 <= (E|K|)^3` used in `c3` is *not* from here — it is Lemma I.4.16 at `k=0` (`(2p-3)!! = 1` at `p=2`). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.EGx17@L3014-L3026 | packet relation requires: the first tail sum is over P_{beta_c}(∣K∣>=n) while the left side is under P_{beta_c,r}; the replacement is legal by tau_r <= tau_{beta_c} [ATTRIBUTION unique exact use-site match; line 697]
EDGE: hutchcroft.eq.i.2.3 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | CROSS_SLICE: the paper invokes the tree-graph inequality displayed at (I.2.3), not generalized Lemma I.4.16 at k=0

NODE: hutchcroft.i.4.15.s4
KIND: step
TITLE: conclusion: apply the regular-variation ODE lemma to `(I.4.15)` — index `3alpha` always, constant `A` exactly when the multiplicative error is logarithmically integrable
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p2.1@L2678-L2678
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p2.1@L2678-L2678
CONTRACT_ID: I.4.15.s4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `f' = a(1-delta_r)r^{-1}f` with `f = E|K|^2`, `a = 3alpha`, `delta_r = \overline{E}_{2,r}`; `f>0`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: if `delta_r -> 0` then `f` is regularly varying of index `3alpha`; if moreover `int|delta_r|dr/r < infinity` then `f ~ A r^{3alpha}`
CONSTANT_SCOPE: `a = 3alpha` exact; `A>0` (C18)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.15.s1
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS2.p2.1@L2678-L2678 (statement of what will be used), #S4.SS2.p3.6@L2730-L2731 ; XSLICE(I.2): Lemma I.2.12 (`f' ~ a r^{-1}f` gives regular variation of index `a`; log-integrable multiplicative error gives `f ~ A r^a`). `delta_r = \overline{E}_{2,r}` is a *product* `1-(1-E_{2,r})(1+H_r)(1-E_{0,r})`, so `|\overline{E}_{2,r}| <= |E_{2,r}|+|H_r|+|E_{0,r}|+o(...)`; log-integrability of the product therefore needs all three factors, which is exactly why the printed proposition asks for `H_r` and `E_{2,r}` and relies on `E_{0,r}` from the I.4.1 slice. No new hypothesis. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.15.s1 | .scratch/source/paper.html#S4.SS2.p3.6@L2730-L2731 | packet relation requires: the ODE-to-regular-variation step consumes the exact identity (I.4.15) of s1 [ATTRIBUTION coordinator attribution: the stated ODE-to-regular-variation conclusion; line 698]

NODE: hutchcroft.i.4.16
KIND: lemma
TITLE: Lemma I.4.16 — generalized tree-graph inequality `E_beta|K|^p <= (2p-3)!! (E_beta|K|^2)^k (E_beta|K|)^{2p-1-3k}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm16@L2743-L2756
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.3@L2802-L2848
CONTRACT_ID: I.4.16
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: percolation on **any transitive weighted graph**, at any `beta>0` (so it applies verbatim to the cut-off law `P_{beta_c,r}` on `Z^d` with weights `beta_c J_r`)
SOURCE_QUANTIFIERS: every integer `p>=2`, every integer `0 <= k <= ceil((p-1)/2)`, every `beta>0`
SOURCE_CONCLUSION: `E_beta|K|^p <= (2p-3)!! (E_beta|K|^2)^k (E_beta|K|)^{2p-1-3k}`
CONSTANT_SCOPE: `(2p-3)!!` explicit and sharp in the tree count; nothing else
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.16.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.3@L2802-L2848 PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.Thmthm16@L2743-L2756 (statement display `#S4.Ex35@L2747-L2753`) ; Verified instances: `(p,k)=(3,1)` gives `3(E|K|^2)(E|K|)^2`, `(4,1)` gives `15(E|K|^2)(E|K|)^4`, `(4,2)` gives `15(E|K|^2)^2E|K|` — exactly the three displayed instances at `#S4.Ex38@L2813`, `#S4.Ex40@L2830`, `#S4.Ex41@L2838` (§7 C5). `k=0` gives `E|K|^p <= (2p-3)!!(E|K|)^{2p-1}`; at `p=2` the coefficient is `(-1)!! = 1`, i.e. `E|K|^2 <= (E|K|)^3`, which is the upper half of `E|K|^2 ≍ (E|K|)^3` used by `c3` and by `i.4.20.c3`. Admissibility `2p-1-3k >= 0` verified for all admissible `k`, `p<=79` (§7 C4) — the exponent is never negative, so no negative power of `E|K|` is ever formed. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.16.pf | .scratch/source/paper.html#S4.Thmthm16@L2743-L2756 | packet relation requires: the statement is established by the proof node; the proof does not consume the statement (no wrapper cycle) [ATTRIBUTION unique exact use-site match; line 704]

NODE: hutchcroft.i.4.16.pf
KIND: step
TITLE: proof of Lemma I.4.16 — union bound over tree structures plus BK factorization, with the `k` two-point factors chosen by which edges are "doubled"
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p7@L2804-L2847
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p7.1@L2805-L2812
CONTRACT_ID: I.4.16.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `E = E_beta`, BK inequality for the product events
SOURCE_QUANTIFIERS: as the lemma
SOURCE_CONCLUSION: `E|K|^3 <= 3 sum_{x,y,z,w}P(0<->x,w)P(w<->y)P(w<->z) = 3E|K|^2(E|K|)^2` (illustration), and analogously the two `p=4` bounds; general `p` by the same diagram expansion
CONSTANT_SCOPE: combinatorial coefficients `3, 12, 3, 15` as printed; these are the `(2p-3)!!`-family specialisations
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.bk.extensions
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.p7.1@L2805-L2812, #S4.Ex38@L2813-L2819, #S4.Ex39@L2821-L2827, #S4.Ex40@L2830-L2836, #S4.Ex41@L2838-L2844, #S4.SS2.p7.5@L2845-L2846 Leaf-with-external-inputs: the only inputs are the BK inequality and the existence of the tree-graph union bound, neither of which is a node of this slice. The printed proof is explicitly a sketch ("Similarly, we have both that...") for general `p`; I record it as a sketch, not as a complete argument, and I do not claim the general-`p` combinatorial count is verified beyond the three displayed instances plus the exponent admissibility (§7 C4/C5). That gap is a proof obligation of the whole slice (§4), not a statement defect. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: ext.bk.extensions | .scratch/source/paper.html#S4.SS2.p7.1@L2805-L2812 | CROSS_SLICE: the non-negative cluster-gap decomposition uses the disjoint-occurrence/BK input retained in the I.2/I.3 candidate

NODE: hutchcroft.i.4.17
KIND: lemma
TITLE: Lemma I.4.17 — the cluster-gap of order `(p,q)` is bounded by polygon diagrams of orders `ell = 3,...,p+q+1`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm17@L2852-L2865
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.4@L2866-L2926
CONTRACT_ID: I.4.17
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: percolation on a transitive weighted graph at some `beta>0`; `T(x,y) := P(x<->y)`; `T^ell` the `ell`-fold matrix power
SOURCE_QUANTIFIERS: `p,q` integers `>= 1` as used (the printed statement does not state a range for `p,q`; it asserts existence of the "universal integer constants `C_{p,q,ell}`" for every pair of vertices `x,y`, which presupposes at least that the exponents `2p+2q+1-ell` be meaningful); the applications use only `p,q >= 1`
SOURCE_CONCLUSION: `0 <= E|K|^p E|K|^q - E[|K_x|^p|K_y|^q 1(x not<-> y)] <= sum_{ell=3}^{p+q+1} C_{p,q,ell} T^ell(x,y)(E|K|)^{2p+2q+1-ell}`
CONSTANT_SCOPE: `C_{p,q,ell}` universal integers, non-explicit beyond the instance `C_{2,1,3}=1, C_{2,1,4}=2` printed at `#S4.EGx15@L2910`; no other constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.17.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.4@L2866-L2926 PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.Thmthm17@L2852-L2865 (statement display `#S4.Ex42@L2856-L2862`) ; Exponents: `2p+2q+1-ell` is non-negative on `3 <= ell <= p+q+1` for all `p,q>=1` (§7 C6), with the top index leaving exponent `p+q` (§7 C9) — so no negative power of `E|K|` ever appears, in contrast to the printed `ell=3` case of Lemma I.4.18. The printed instance `p=2,q=1` is `<= T^3(x,y)(E|K|)^4 + 2T^4(x,y)(E|K|)^3`; summed over `y in B_r` with the *repaired* `ell=3` bound this is exactly what consumer 1 needs (§7 C7). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.17.pf | .scratch/source/paper.html#S4.Thmthm17@L2852-L2865 | packet relation requires: same relation for Lemma I.4.17 [ATTRIBUTION unique exact use-site match; line 705]

NODE: hutchcroft.i.4.17.pf
KIND: step
TITLE: proof of Lemma I.4.17 — two independent copies `omega, omega'`, the "restored" cluster `tilde K_y`, the case split `y in K_x` / some `y_i notin K_y`, and a tree expansion with `2p+2q+1` edges of which `ell` lie on the `x`–`y` path
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p9@L2868-L2925
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p9.1@L2869-L2870
CONTRACT_ID: I.4.17.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as the lemma; independence of the two copies on the relevant events
SOURCE_QUANTIFIERS: as the lemma
SOURCE_CONCLUSION: the displayed decomposition of the gap as `sum_{x_1..x_p}sum_{y_1..y_q}P(...)` and then the two independent factorisations; "in each case `C_{p,q,ell}` counts the number of diagrams in which the path from `x` to `y` has length `ell`"
CONSTANT_SCOPE: combinatorial counts only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: ext.bk.extensions
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS2.p9.1@L2869-L2870, #S4.EGx13@L2871-L2893, #S4.SS2.p9.2@L2894-L2894, #S4.EGx14@L2895-L2907, #S4.SS2.p9.3@L2908-L2909, #S4.EGx15@L2910-L2922, #S4.SS2.p9.4@L2923-L2924 Leaf-with-external-inputs. XSLICE(I.4.1): the construction of `omega,omega',tilde K_y` and of the "fresh copy" event is Lemma I.4.12's proof (`hutchcroft.i.4.12`), and the two-cluster exclusion `y notin K_0` used there is flagged in the campaign errata (`two-cluster-fresh-copy-exclusion`) as needing its own case in I.4.12 — that concern belongs to the I.4.1 slice and I neither import it nor repair it here. The non-negativity `0 <=` of the gap *is* from BK and is used by consumers, so it is part of this node's content. The general-`p,q` combinatorial count is asserted, not derived; recorded as a proof obligation (§4). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: ext.bk.extensions | .scratch/source/paper.html#S4.SS2.p9.1@L2869-L2870 | CROSS_SLICE: the non-negative cluster-gap decomposition uses the disjoint-occurrence/BK input retained in the I.2/I.3 candidate

NODE: hutchcroft.i.4.18
KIND: lemma
TITLE: Lemma I.4.18 **restricted to `ell >= 4`** — polygon-diagonal bound `sup_x T^ell_{beta_c,r}(0,x) = T^ell_{beta_c,r}(0,0) <= C(nabla_{r^c}+r^{-c})(E_{beta_c,r}|K|)^{ell-3}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm18@L2930-L2943
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.5@L2944-L2973
CONTRACT_ID: I.4.18
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `nabla<infinity` (triangle condition); `T:=T_{β_c,r}` is the cut-off two-point matrix
SOURCE_QUANTIFIERS: each integer `ell >= 4`; every `r>0`
SOURCE_CONCLUSION: `sup_x T^ell_{beta_c,r}(0,x) = T^ell_{beta_c,r}(0,0) <= C(nabla_{r^c}+r^{-c})(E_{beta_c,r}|K|)^{ell-3}`
CONSTANT_SCOPE: C depends only on the source normalization (*) and the first-moment comparison; the free scale c>0 is realised as alpha/(2d) in the proof
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.18.pf,hutchcroft.a.triangle,hutchcroft.a.norm,hutchcroft.i.4.18.psd,hutchcroft.i.4.18.mom
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.5@L2944-L2973 **Restriction is forced, not cosmetic**: the printed `ell=3` instance is false (`hutchcroft.i.4.18.ell3.refute`), and the printed proof's line `sum_{||y||<R}nabla(0,y)T^{ell-3}(y,0) <= nabla|B_R|(E|K|)^{ell-4}` contains the power `(E|K|)^{ell-4}`, which is `(E|K|)^{-1}` at `ell=3` and is undefined (it also needs `T^{-1}`). The printed proof therefore establishes the lemma **only for `ell>=4`**, and that is what this node states. Consumers must supply the `ell=3` term from `hutchcroft.i.4.18.ell3`; **all three** consumers that reach `ell=3` do so at `ell=3` and at `ell>=4` *separately* (checked in §7 C7, C8, C27-C29), so no consumer needs the printed quantifier `ell>=3`. `E|K| >> r^alpha` in `CONSTANT_SCOPE` is not a new hypothesis: it is Prop I.4.2 route 3 (XSLICE), and it is also what makes the `R^d/r^alpha` step small. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.18.pf | .scratch/source/paper.html#S4.Thmthm18@L2930-L2943 | packet relation requires: same relation for the restricted Lemma I.4.18 [ATTRIBUTION unique exact use-site match; line 706]
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.Thmthm18.p1.1@L2933-L2933 | packet relation requires: the printed hypothesis "Suppose that nabla < infinity" [ATTRIBUTION coordinator attribution: hypothesis line inside Lemma I.4.18 statement; line 707]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.SS2.p11.2@L2962-L2962 | packet relation requires: the step ∣B_R∣(E∣K∣)^{ell-4} <= C R^d r^{-alpha}(E∣K∣)^{ell-3} uses ∣B_R∣ ~ R^d and E∣K∣ >> r^alpha [ATTRIBUTION coordinator attribution: scale-choice justification belongs to restricted statement; line 708]
EDGE: hutchcroft.i.4.18.psd | .scratch/source/paper.html#S4.SS2.5@L2944-L2973 | diagonal maximality and the diagonal moment bound are proof inputs, not premises or constant scope
EDGE: hutchcroft.i.4.18.mom | .scratch/source/paper.html#S4.SS2.5@L2944-L2973 | diagonal maximality and the diagonal moment bound are proof inputs, not premises or constant scope

NODE: hutchcroft.i.4.18.pf
KIND: step
TITLE: proof of the `ell>=4` lemma — diagonal maximality, the `nabla * T^{ell-3}` identity, the two-region split at `R`, and `R = r^{alpha/(2d)}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p11@L2946-L2972
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948
CONTRACT_ID: I.4.18.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `nabla<infinity`; each integer ell>=4
SOURCE_QUANTIFIERS: `ell>=4`, every `r>0`, every `R>0`
SOURCE_CONCLUSION: `T^ell(0,0) = sum_y nabla(0,y)T^{ell-3}(y,0) <= nabla_R(E|K|)^{ell-3} + nabla|B_R|(E|K|)^{ell-4} <= (nabla_R + C R^d/r^alpha)(E|K|)^{ell-3}`, and `sum_{||y||<R}T^{ell-3}(y,0) = sum_{x_1..x_{ell-4}}T(0,x_1)prod T(x_i,x_{i+1})sum_{||y||<R}T(x_{ell-4},y) <= |B_R|(E|K|)^{ell-4}`
CONSTANT_SCOPE: `C` as in the lemma; `|B_R|` enters only through `(∗)`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.triangle,hutchcroft.a.norm,hutchcroft.i.4.18.psd,hutchcroft.i.4.18.mom
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS2.p11.1@L2947-L2948, #S4.EGx16@L2949-L2961, #S4.SS2.p11.2@L2962-L2962, #S4.Ex54@L2963-L2969, #S4.SS2.p11.3@L2970-L2971 The diagonal-maximality step `sup_x T^ell(0,x) = T^ell(0,0)` is *used again* by the repair (`i.4.18.ell3.s1`) and is the reason `nabla_{beta_c}` may bound the **near** summand pointwise; it follows from `T` being the Fourier transform of a non-negative function (positive definite) and does **not** bound `sum_y nabla(0,y)`. XSLICE(I.4.1): `E|K| >> r^alpha` is Prop I.4.2 route 3. The identity `T^ell(0,0) = sum_y nabla(0,y)T^{ell-3}(y,0)` requires `nabla = T^3` (matrix cube), which is `nabla_{beta_c,r}(0,y) = sum_{u,v}tau_r(0,u)tau_r(u,v)tau_r(v,y)`; it is exact. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948 | packet relation requires: nabla_{R} must be finite, so the diagonal value nabla = nabla(0,0) < infinity is used [ATTRIBUTION coordinator attribution: near-ball summation estimate belongs to proof step; line 709]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex54@L2963-L2969 | packet relation requires: sum_{‖y‖<R}T^{ell-3}(y,0) <= ∣B_R∣(E∣K∣)^{ell-4} uses ∣B_R∣ << R^d [ATTRIBUTION unique exact use-site match; line 710]
EDGE: hutchcroft.i.4.18.psd | .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948 | the two-region estimate uses diagonal maximality and the diagonal moment bound
EDGE: hutchcroft.i.4.18.mom | .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948 | the two-region estimate uses diagonal maximality and the diagonal moment bound

NODE: hutchcroft.i.4.18.ell3.refute
KIND: step
TITLE: **REFUTATION** of the printed `ell=3` instance of Lemma I.4.18 (derived here  the printed statement is false under its own hypotheses)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm18@L2930-L2943
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex51@L2934-L2940
CONTRACT_ID: I.4.18.ell3.refute
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the printed lemma's hypotheses (`nabla<infinity`, cut-off law at `beta_c`) together with `nabla_r -> 0` (which is what the printed statement's own consumers use)
SOURCE_QUANTIFIERS: all sufficiently large `r`
SOURCE_CONCLUSION: the printed `ell=3` inequality `sup_x T^3_{beta_c,r}(0,x) = T^3_{beta_c,r}(0,0) <= C(nabla_{r^c}+r^{-c})` is **false**
CONSTANT_SCOPE: no implicit constant in the counterexample; printed C belongs to the refuted display
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.cutoff
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this is a coordinator/refutation reconstruction, not a printed lemma or its proof. It is retained only to expose the defective ell=3 instance and the averaged replacement; no topology/proof promotion. UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.Ex51@L2934-L2940 SOURCE-GAP ANCHOR: normalized by the coordinator; this record is explicitly a reconstruction/counterexample, not a printed source statement or proof. Original descriptor: the refuted statement is paper.html#S4.Thmthm18@L2930-L2943 with `ell=3` (`#S4.Ex51@L2934-L2940` at `ell=3`); the refutation itself is not in the source ; original proof descriptor: the three-line argument below (not in the source) Proof: `T(x,x) = P_{beta_c,r}(x<->x) = 1`, so the single summand `y = z = 0` of `T^3(0,0) = sum_{y,z}T(0,y)T(y,z)T(z,0)` contributes `1`, giving `T^3(0,0) >= 1` for **every** `r`. The printed right side is `C(nabla_{r^c}+r^{-c})(E|K|)^{3-3} = C(nabla_{r^c}+r^{-c})`, which tends to `0` as `r->infinity` whenever `nabla_r -> 0`. Hence for all large `r`, `1 <= T^3(0,0) > C(nabla_{r^c}+r^{-c})`. Nothing here depends on `d`, `alpha`, or on the shape of `T` beyond `T(x,x)=1`; the printed bound would be false for the degenerate transitive weighted graph with `T(x,y)=1(x=y)` as well (§7 C16). **No consumer may use the printed `ell=3` estimate.** This refutation is *my* derivation, not a source statement; the corresponding campaign errata entry (`lemma-i418-ell3-diagonal`) was read only after I had the same conclusion from the diagonal computation, and I do not treat it as evidence. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | T(x,x)=P_{β_c,r}(x↔x)=1 makes the diagonal summand of T³(0,0) at least 1

NODE: hutchcroft.i.4.18.ell3
KIND: step
TITLE: **two-scale averaged replacement for the `ell=3` instance of Lemma I.4.18** (not printed): `|B_r|^{-1}sum_{y in B_r}T^3_{beta_c,r}(0,y) <= G_r(theta) := nabla_{r^theta} + C_0 r^{-d(1-theta)}nabla_{beta_c}`, which `-> 0` and is logarithmically integrable under the hypotheses already in force
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm18@L2930-L2943
PROOF_SOURCE: .scratch/source/paper.html#S4.EGx16@L2949-L2961
CONTRACT_ID: I.4.18.ell3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition; `nabla_r -> 0` (for convergence); `nabla_r` log-integrable (for the log-integrability clause only); `J_r <= J` monotonicity (`hutchcroft.a.cutoff`); normalization `(∗)`
SOURCE_QUANTIFIERS: every `theta` with `0<theta<1`; every `r>0`
SOURCE_CONCLUSION: (a) `sum_{y in B_r}T^3_{beta_c,r}(0,y) <= |B_r|nabla_{r^theta} + |B_{r^theta}|nabla_{beta_c}`; (b) `|B_r|^{-1}sum_{y in B_r}T^3_{beta_c,r}(0,y) <= G_r(theta) := nabla_{r^theta} + C_0 r^{-d(1-theta)}nabla_{beta_c}`; (c) `G_r(theta) -> 0`; (d) `r |-> G_r(theta)` is logarithmically integrable whenever `nabla_r` is logarithmically integrable
CONSTANT_SCOPE: `C_0` is the *only* constant and it comes from `(∗)` alone (`|B_{r^theta}|/|B_r| <= C_0 r^{-d(1-theta)}`, §7 C15); `theta` is free in `(0,1)` and consumed as an existential; `nabla_{beta_c}` is finite by `hutchcroft.a.triangle`; **no comparison between `G_r` and the printed `nabla_{r^c}+r^{-c}` is asserted**
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.18.ell3.s1,hutchcroft.i.4.18.ell3.s2,hutchcroft.i.4.19,hutchcroft.a.triangle,hutchcroft.a.tri.tail,hutchcroft.a.logint,hutchcroft.i.4.18.psd,hutchcroft.i.4.18.mom
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: this is a coordinator/refutation reconstruction, not a printed lemma or its proof. It is retained only to expose the defective ell=3 instance and the averaged replacement; no topology/proof promotion. UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.EGx16@L2949-L2961 SOURCE-GAP ANCHOR: normalized by the coordinator; this record is explicitly a reconstruction/counterexample, not a printed source statement or proof. Original descriptor: **not in the source** — reconstruction required because the printed `ell=3` instance is false (`hutchcroft.i.4.18.ell3.refute`). The *shape* of the bound is the one recorded in the campaign errata file quoted in §0; I re-derived it from `hutchcroft.i.4.18.pf`'s diagonal maximality and `hutchcroft.a.tri.tail`, and I do not rely on the errata file as evidence ; original proof descriptor: `hutchcroft.i.4.18.ell3.s1` + `hutchcroft.i.4.18.ell3.s2` **Why averaging and not a supremum.** A supremum bound `T^3(0,0) <= o(1)` is impossible (`>=1`, above); what the three consumers actually need is the *average* `|B_r|^{-1}sum_{y in B_r}T^3(0,y)` (consumer 1 and consumer 2 divide by `|B_r|`; consumer 3 needs `sum_{y in B_r}T^3(0,y) = o(|B_r|)` after multiplying by `|J'(r)| ~ r^{-d-alpha-1}`), and the average is small: the mass sits near `y=0` and the far part decays. **The rejected variant.** One is tempted to bound `sum_{y in B_r}nabla(0,y) <= nabla_{beta_c}` ("total finite triangle mass"). That is **invalid**: `nabla_{beta_c} = nabla(0,0) = sum_{y,z}tau(0,y)tau(y,z)tau(z,0)` is the *diagonal* value, whereas `sum_{y in B_r}nabla(0,y) = sum_{y in B_r}sum_{u,v}tau(0,u)tau(u,v)tau(v,y)` grows like `|B_r|` (at criticality `sum_y tau(v,y) = infinity`); even for the cut-off law the only trivial bound is `sum_{y in B_r}T^3_r(0,y) <= |B_r| nabla_{beta_c}`, which is `O(|B_r|)` and gives **no** `o(1)` after division. The near/far split is what makes the `ell=3` contribution `o(1)`; the finite diagonal value alone does not. Three consumers were checked (§6, §7 C7, C8, C27-C29): consumer 1 (`i.4.15.c3`) and consumer 2 (`i.4.20.c3`) divide by `|B_r|`, consumer 3 (`S5.SS3.p18`) does not; all three are satisfied by (a)+(b), and each re-chooses its own small constants `c`, `theta` — no superiority of `G_r` over the printed expression is claimed or needed, because the three terms are simply added. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.18.ell3.s1 | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: the refuted ell=3 instance of this display is replaced by the two-scale split of s1 [ATTRIBUTION explicit bracketed consumer in packet; line 717]
EDGE: hutchcroft.i.4.18.ell3.s2 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: smallness and log-integrability of G_r are the content of s2 (the analogue of this sentence for the replacement) [ATTRIBUTION explicit bracketed consumer in packet; line 718]
EDGE: hutchcroft.i.4.19 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: clause (d) of the replacement uses Lemma I.4.19 [ATTRIBUTION explicit bracketed consumer in packet; line 719]
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: the bound needs nabla_{beta_c} finite (triangle condition) [ATTRIBUTION explicit bracketed consumer in packet; line 720]
EDGE: hutchcroft.a.tri.tail | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: clause (c) needs nabla_r -> 0 [ATTRIBUTION explicit bracketed consumer in packet; line 721]
EDGE: hutchcroft.a.logint | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: clause (d) is conditional on nabla_r being log-integrable [ATTRIBUTION explicit bracketed consumer in packet; line 722]
EDGE: hutchcroft.i.4.18.psd | .scratch/source/paper.html#S4.EGx16@L2949-L2961 | the averaged ell=3 replacement inherits diagonal maximality and moment control
EDGE: hutchcroft.i.4.18.mom | .scratch/source/paper.html#S4.EGx16@L2949-L2961 | the averaged ell=3 replacement inherits diagonal maximality and moment control

NODE: hutchcroft.i.4.18.ell3.s1
KIND: step
TITLE: the two-scale split of `sum_{y in B_r}nabla(0,y)`: near `||y|| <= r^theta` bounded by the diagonal value, far `r^theta < ||y|| <= r` bounded by the tail `nabla_{r^theta}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.EGx16@L2949-L2961
PROOF_SOURCE: .scratch/source/paper.html#S4.EGx16@L2949-L2961
CONTRACT_ID: I.4.18.ell3.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `0<theta<1`; `nabla_{beta_c,r}(0,y) <= nabla_{beta_c}(0,y)` (monotonicity in the kernel); `sup_y nabla_{beta_c}(0,y) = nabla_{beta_c}(0,0) = nabla_{beta_c}` (diagonal maximality, from `hutchcroft.i.4.18.pf`); `nabla_{beta_c}(0,y) <= nabla_{r^theta}` for `||y|| >= r^theta` (definition of `nabla_{r^theta}`)
SOURCE_QUANTIFIERS: every `r>0`
SOURCE_CONCLUSION: `sum_{y in B_r}nabla(0,y) = sum_{||y||<=r^theta} + sum_{r^theta<||y||<=r} <= |B_{r^theta}|nabla_{beta_c} + |B_r|nabla_{r^theta}`
CONSTANT_SCOPE: exact `<=`; only cardinalities `|B_{r^theta}|`, `|B_r|`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.18.pf,hutchcroft.a.triangle,hutchcroft.a.cutoff
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.EGx16@L2949-L2961 SOURCE-GAP ANCHOR: normalized by the coordinator; this record is explicitly a reconstruction/counterexample, not a printed source statement or proof. Original descriptor: **derived here** (not printed); it is the repair of the printed step `#S4.EGx16@L2949-L2961` at `ell=3` ; original proof descriptor: the two-region computation below Both halves are load-bearing. The **far** half needs the tail decay `nabla_{r^theta} -> 0`, which the triangle condition alone does not supply. The **near** half needs a bound on each `nabla(0,y)` with `||y|| <= r^theta`; the only uniform bound available is the *diagonal* value `nabla(0,0) = nabla_{beta_c}` (diagonal maximality), and applying it to the **whole** ball would give `sum_{y in B_r} <= |B_r|nabla_{beta_c}` — no decay at all after dividing by `|B_r|`. The split is exactly what converts "one finite diagonal value" into "a decaying average": the near mass is at most `|B_{r^theta}|nabla_{beta_c}`, which is `o(|B_r|)` because `theta<1`, while the far mass decays. Positive definiteness of `T` is therefore load-bearing (it is what makes the near bound pointwise), and so is `theta<1`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.18.pf | .scratch/source/paper.html#S4.EGx16@L2949-L2961 | packet relation requires: the split needs the diagonal-maximality/identity machinery of the printed proof at ell=3 (T^3(0,0) = sum_y nabla(0,y)T^0(y,0) = nabla(0,0)) [ATTRIBUTION explicit bracketed consumer in packet; line 711]
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: the near part is bounded by the finite diagonal value nabla_{beta_c} [ATTRIBUTION explicit bracketed consumer in packet; line 712]
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.Ex51@L2934-L2940 | packet relation requires: nabla_{beta_c,r}(0,y) <= nabla_{beta_c}(0,y) transfers the diagonal bound to the cut-off law [ATTRIBUTION explicit bracketed consumer in packet; line 713]

NODE: hutchcroft.i.4.18.ell3.s2
KIND: step
TITLE: smallness and logarithmic integrability of `G_r(theta) = nabla_{r^theta} + C_0 r^{-d(1-theta)}nabla_{beta_c}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013
PROOF_SOURCE: .scratch/source/paper.html#S4.EGx16@L2949-L2961
CONTRACT_ID: I.4.18.ell3.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `nabla_r -> 0`; `d(1-theta) > 0`; `nabla_r` log-integrable (second clause only)
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: (i) `nabla_{r^theta} -> 0` because `r^theta -> infinity`; (ii) `r^{-d(1-theta)} -> 0`; hence `G_r(theta) -> 0`; (iii) `r |-> nabla_{r^theta}` is log-integrable when `nabla_r` is (Lemma I.4.19 with `C=1`, `c=theta`); (iv) `r |-> r^{-d(1-theta)}` is log-integrable because `int^{infinity} r^{-d(1-theta)}dr/r = int r^{-d(1-theta)-1}dr < infinity`; hence `r |-> G_r(theta)` is log-integrable
CONSTANT_SCOPE: the `1/theta` factor from Lemma I.4.19 (corrected, defect D3) and `C_0` from `(∗)`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.19,hutchcroft.a.tri.tail,hutchcroft.a.logint
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PROOF/RECONSTRUCTION OBLIGATION AT: paper.html#S4.EGx16@L2949-L2961 SOURCE-GAP ANCHOR: normalized by the coordinator; this record is explicitly a reconstruction/counterexample, not a printed source statement or proof. Original descriptor: **derived here** (not printed) ; original proof descriptor: the computation below This is where the free parameter `theta` matters: `theta` must be `>0` (so `r^theta -> infinity` and the tail decay applies) and `<1` (so the near-ball ratio decays); any such `theta` works, so no optimization is asserted. Note that `G_r` is *not* claimed to be `o(nabla_{r^c}+r^{-c})`; the consumers add the three small terms. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. SELF-PROOF CORRECTION: STATEMENT_SOURCE and PROOF_SOURCE were the same locator, `#S4.Thmthm19@L2977-L2982`, i.e. the *statement of* Lemma I.4.19 -- a lemma that does not mention G_r at all. A record whose statement and proof are the same lemma statement proves nothing, and here the locator does not even state the claim. The STEP is located at I.4.18's own proof/reconstruction site `#S4.EGx16@L2949-L2961` (the printed ell=3 bound, L2953-L2959, which `hutchcroft.i.4.18.ell3` also uses as its PROOF_SOURCE), and the printed analogue of clauses (i)-(iv) is the sentence at `#S4.SS2.p15.2@L3013`; Lemma I.4.19 remains the only input for clause (iii). The record is a reconstruction and is not promoted.
EDGE: hutchcroft.i.4.19 | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: log-integrability of r ∣-> nabla_{r^theta} comes from I.4.19 applied with C=1, c=theta [ATTRIBUTION explicit bracketed consumer in packet; line 714]
EDGE: hutchcroft.a.tri.tail | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: nabla_{r^theta} -> 0 is what makes the replacement small [ATTRIBUTION explicit bracketed consumer in packet; line 715]
EDGE: hutchcroft.a.logint | .scratch/source/paper.html#S4.SS2.p15.2@L3013-L3013 | packet relation requires: the log-integrability clause is conditional on nabla_r being log-integrable [ATTRIBUTION explicit bracketed consumer in packet; line 716]

NODE: hutchcroft.i.4.19
KIND: lemma
TITLE: Lemma I.4.19 — if `h` is logarithmically integrable then so is `r |-> h(C r^c)`, for every `c,C>0`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm19@L2977-L2982
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.6@L2983-L2997
CONTRACT_ID: I.4.19
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `h` logarithmically integrable in the paper's sense
SOURCE_QUANTIFIERS: every `c>0`, every `C>0`
SOURCE_CONCLUSION: `h(C r^c)` is logarithmically integrable
CONSTANT_SCOPE: the conclusion is a finiteness statement; the *value* of the integral is `(1/c) int_C^{infinity}|h(s)|ds/s` (defect D3)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.19.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS2.6@L2983-L2997 Statement PASS and consumed by `i.4.18.ell3.s2` (with `c = theta`, `C = 1`) and by `i.4.15.c3`. The printed proof's prefactor is wrong (D3) but the lemma does not depend on it. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.19.pf | .scratch/source/paper.html#S4.Thmthm19@L2977-L2982 | packet relation requires: statement established by proof node (no wrapper cycle) [ATTRIBUTION unique exact use-site match; line 723]

NODE: hutchcroft.i.4.19.pf
KIND: step
TITLE: proof of Lemma I.4.19 by the change of variables `s = C r^c` — with the substitution constant **`1/c`**, not the printed `1/(c C^{1-c})`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p13@L2985-L2996
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p13.1@L2986-L2986
CONTRACT_ID: I.4.19.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as the lemma
SOURCE_QUANTIFIERS: as the lemma
SOURCE_CONCLUSION: `int_1^{infinity}|h(Cr^c)|dr/r = (1/c)int_C^{infinity}|h(s)|ds/s < infinity`
CONSTANT_SCOPE: `1/c` only — **independent of `C`**
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS2.p13.1@L2986-L2986, #S4.Ex55@L2987-L2993 Defect **D3**: `s = Cr^c` gives `ds/s = c dr/r`, hence `dr/r = (1/c) ds/s`; the printed `dr/r = (1/(cC^{1-c}))ds/s` is wrong whenever `C != 1` (§7 C14, sympy: `d/dr log(Cr^c) = c/r`). The printed display `#S4.Ex55@L2987-L2993` consequently carries a wrong constant; the lemma's *conclusion* (finiteness) is unaffected, so I keep the lemma node and record the correction in this proof node only. No consumer in this slice uses the constant. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.20
KIND: proposition
TITLE: Proposition I.4.20 — higher-moment asymptotics `E_{beta_c,r}|K|^p ~ (2p-3)!! ((E|K|^2)/(E|K|))^{p-1}E|K|`, hence regular variation of index `(2p-1)alpha`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm20@L3038-L3051
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.5@L3188-L3366
CONTRACT_ID: I.4.20
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of routes `r1` (`d>3alpha`), `r2` (`d=3alpha` and (Hydro)), `r3` (triangle condition)
SOURCE_QUANTIFIERS: every integer `p>=1`; `r -> infinity`
SOURCE_CONCLUSION: `E_{beta_c,r}|K|^p ~ (2p-3)!! ((E_{beta_c,r}|K|^2)/(E_{beta_c,r}|K|))^{p-1}E_{beta_c,r}|K|`; in particular `E|K|^p` is regularly varying of index `(2p-1)alpha`
CONSTANT_SCOPE: `(2p-3)!!` explicit with the convention `(-1)!!=1` (so `p=1` is the identity `E|K| ~ E|K|`); the ratio `E|K|^2/E|K|` is a constant at fixed `r`; `~` constant `1`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: hutchcroft.i.4.20.r1,hutchcroft.i.4.20.r2,hutchcroft.i.4.20.r3
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.5@L3188-L3366 PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.Thmthm20@L3038-L3051, with its display `#S4.Ex59@L3042-L3048` (the numbered display `#S4.E19@L3194-L3201` is the *upper bound* `(I.4.19)`, **not** the statement) ; Statement PASS. `p=1,2` are the base cases (`I.4.2`, `I.4.15`) and the printed statement correctly calls them "vacuous" only for the asymptotic formula, not for the regular-variation claim. The *second* induction is the one that needs the decorrelation estimates; the *first* (upper bound `(I.4.19)`) does not. Consumers: Theorem I.1.6 (XSLICE), Lemma I.5.29 (downstream, §6). I create no node for `(I.4.19)`/`(I.4.20)`/`(I.4.21)`/`(I.4.22)` as statements: they are proof devices, and their content is carried by `s2`/`s3` as steps, not as facts of the slice. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.r1 | .scratch/source/paper.html#S4.Thmthm20@L3038-L3051 | packet relation requires: first alternative of the statement realised as d>3alpha [ATTRIBUTION unique exact use-site match; line 729]
EDGE: hutchcroft.i.4.20.r2 | .scratch/source/paper.html#S4.Thmthm20@L3038-L3051 | packet relation requires: second alternative realised as d=3alpha + (Hydro) [ATTRIBUTION unique exact use-site match; line 730]
EDGE: hutchcroft.i.4.20.r3 | .scratch/source/paper.html#S4.Thmthm20@L3038-L3051 | packet relation requires: third alternative realised as the triangle condition [ATTRIBUTION unique exact use-site match; line 731]

NODE: hutchcroft.i.4.20.r1
KIND: route
TITLE: Prop I.4.20, route 1 — `d > 3alpha`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p11.1@L3295-L3297
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p11@L3294-L3322
CONTRACT_ID: I.4.20.r1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d>3alpha`
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: the asymptotic plus regular variation
CONSTANT_SCOPE: as the proposition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.20.s2,hutchcroft.i.4.20.s3,hutchcroft.i.4.20.c1
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.20
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.p11@L3294-L3322 In this case the printed proof notes that the first-order asymptotic can be obtained *directly* (tree-graph gives the correct order), i.e. `(I.4.19)` and `s3` are not needed; the route keeps them for uniformity, but `c1` alone suffices. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.SS3.p8.3@L3205-L3213 | packet relation requires: route 1 uses the derivative decomposition and Lemma I.2.1 bounds of s1 [ATTRIBUTION coordinator attribution: rationale explicitly names route 1; line 732]
EDGE: hutchcroft.i.4.20.s2 | .scratch/source/paper.html#S4.SS3.p8.3@L3205-L3213 | packet relation requires: route 1's upper bound (I.4.19) is deduced from s1 [ATTRIBUTION coordinator attribution: rationale explicitly names route 1; line 733]
EDGE: hutchcroft.i.4.20.s3 | .scratch/source/paper.html#S4.SS3.p8.3@L3205-L3213 | packet relation requires: route 1's second induction re-uses the derivative decomposition [ATTRIBUTION coordinator attribution: rationale explicitly names route 1; line 734]
EDGE: hutchcroft.i.4.20.c1 | .scratch/source/paper.html#S4.SS3.p11.1@L3295-L3297 | packet relation requires: route 1's decorrelation estimate (I.4.20) is c1 [ATTRIBUTION unique exact use-site match; line 735]

NODE: hutchcroft.i.4.20.r2
KIND: route
TITLE: Prop I.4.20, route 2 — `d = 3alpha` and (Hydro)
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p12.1@L3324-L3325
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p12@L3323-L3351
CONTRACT_ID: I.4.20.r2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d=3alpha`; `M_r = o(r^{(d+alpha)/2})`
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: the asymptotic plus regular variation
CONSTANT_SCOPE: as the proposition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.20.s2,hutchcroft.i.4.20.s3,hutchcroft.i.4.20.c2
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.20
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.p12@L3323-L3351 This is the case where the *first* induction's upper bound `(I.4.19)` is essential ("The case `d=3alpha` is more delicate and will make use of the upper bound", `#S4.SS3.p9.1@L3259-L3260`). Dropping `s2` from this route would make `c2` circular, because `c2` bounds `E|K|^{2p+2}` using `(I.4.19)`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.SS3.p12.1@L3324-L3325 | packet relation requires: route 2 uses s1 [ATTRIBUTION unique exact use-site match; line 736]
EDGE: hutchcroft.i.4.20.s2 | .scratch/source/paper.html#S4.SS3.p12.1@L3324-L3325 | packet relation requires: route 2 needs (I.4.19) for the 2p+2 moment [ATTRIBUTION unique exact use-site match; line 737]
EDGE: hutchcroft.i.4.20.s3 | .scratch/source/paper.html#S4.SS3.p12.1@L3324-L3325 | packet relation requires: route 2 uses the second induction [ATTRIBUTION unique exact use-site match; line 738]
EDGE: hutchcroft.i.4.20.c2 | .scratch/source/paper.html#S4.SS3.p12.1@L3324-L3325 | packet relation requires: route 2's decorrelation estimate is c2 [ATTRIBUTION unique exact use-site match; line 739]

NODE: hutchcroft.i.4.20.r3
KIND: route
TITLE: Prop I.4.20, route 3 — the triangle condition
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p13.1@L3353-L3353
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p13@L3352-L3365
CONTRACT_ID: I.4.20.r3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition
SOURCE_QUANTIFIERS: as the proposition
SOURCE_CONCLUSION: the asymptotic plus regular variation
CONSTANT_SCOPE: as the proposition, plus the repaired `ell=3` constant in `c3`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.20.s2,hutchcroft.i.4.20.s3,hutchcroft.i.4.20.c3
ROUTES: -
ROUTE_FOR: hutchcroft.i.4.20
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.p13@L3352-L3365 Only needs `E|K|^2 ≍ (E|K|)^3` *as an input* from Prop I.4.15 route 3 (XSLICE), unlike Prop I.4.15 itself which proves one half of it internally. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.SS3.p13.1@L3353-L3353 | packet relation requires: route 3 uses s1 [ATTRIBUTION unique exact use-site match; line 740]
EDGE: hutchcroft.i.4.20.s2 | .scratch/source/paper.html#S4.SS3.p13.1@L3353-L3353 | packet relation requires: route 3 uses (I.4.19) only through the general plan [ATTRIBUTION unique exact use-site match; line 741]
EDGE: hutchcroft.i.4.20.s3 | .scratch/source/paper.html#S4.SS3.p13.1@L3353-L3353 | packet relation requires: route 3 uses the second induction [ATTRIBUTION unique exact use-site match; line 742]
EDGE: hutchcroft.i.4.20.c3 | .scratch/source/paper.html#S4.SS3.p13.2@L3354-L3362 | packet relation requires: route 3's decorrelation estimate (I.4.21) is c3 [ATTRIBUTION coordinator attribution: only declared consumer of c3; case-3 display; line 743]

NODE: hutchcroft.i.4.20.s1
KIND: step
TITLE: derivative decomposition: the `p`-th moment derivative with the `ell=0` and `ell=p-1` terms merged by mass transport, then bounded termwise by Lemma I.2.1
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p8.2@L3202-L3204
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p8.2@L3202-L3204
CONTRACT_ID: I.4.20.s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `(I.4.1)` at parameter `beta = beta_c` (so `beta = beta_c` in the first display and `beta_c` thereafter); mass-transport principle
SOURCE_QUANTIFIERS: every integer `p>=3`; every `r>0`
SOURCE_CONCLUSION: `d/dr E_r|K|^p = (p+1)beta_c|J'|E_r[|K|^p sum_{y in B_r}1(y notin K)|K_y|] + beta_c|J'|sum_{ell=1}^{p-2}C(p,ell)E_r[|K|^{ell+1}sum_{y in B_r}1(y notin K)|K_y|^{p-ell}] <= (p+1)beta_c|J'||B_r|E_r|K|E_r|K|^p + beta_c|J'||B_r|sum_{ell=1}^{p-2}C(p,ell)E_r|K|^{ell+1}E_r|K|^{p-ell}`
CONSTANT_SCOPE: coefficient `p+1` exact (`C(p,0)=1` merged with `C(p,p-1)=p` by mass transport, §7 C22); binomial coefficients `C(p,ell)`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.norm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p8.2@L3202-L3204, #S4.SS3.p8.3@L3205-L3213, #S4.SS3.p8.4@L3214-L3214, #S4.Ex68@L3215-L3221 ; XSLICE(I.4.1): `(I.4.1)` = Lemma I.4.1; XSLICE(I.2): Lemma I.2.1 gives each `E_r[|K|^{ell+1}sum_{y in B_r}1(y notin K)|K_y|^{p-ell}] <= |B_r|E_r|K|^{ell+1}E_r|K|^{p-ell}` (and the `ell=0`/`ell=p-1` merged term `<= |B_r|E_r|K|E_r|K|^p`). Both are inputs, not results. Index check: the merged term is the `ell = p-1` term (`|K|^p`), not `ell = p`: §7 C22. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex68@L3215-L3221 | packet relation requires: beta_c∣J'(r)‖B_r∣ ~ alpha r^{-1} converts the derivative bound into the r^{-1} form [ATTRIBUTION unique exact use-site match; line 744]

NODE: hutchcroft.i.4.20.s2
KIND: step
TITLE: first induction — the upper bound `(I.4.19)` follows from `s1` + Prop I.4.2 + the induction hypothesis + Lemma I.4.23 + Lemma I.4.22
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p8@L3190-L3257
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p8@L3190-L3257
CONTRACT_ID: I.4.20.s2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `s1`; `beta_c|J'(r)||B_r| ~ alpha r^{-1}` (from `(∗)`); `E_r|K| ~ (alpha/beta_c)r^alpha` (Prop I.4.2, XSLICE); `(I.4.19)` for all `p' < p` (induction hypothesis); `p>=3`
SOURCE_QUANTIFIERS: every integer `p>=3`, inductively on `p`; `r -> infinity`
SOURCE_CONCLUSION: (a) `d/dr E_r|K|^p <= (1+o(1))(p+1)alpha r^{-1}E_r|K|^p + (1+o(1))alpha [sum_{ell=1}^{p-2}C(p,ell)(2ell-1)!!(2p-2ell-3)!!] r^{-1}(E|K|^2/E|K|)^{p-1}E|K|`; (b) the bracket equals `(p-2)(2p-3)!!`; (c) hence `d/dr E_r|K|^p <= (1+o(1))r^{-1}[(p+1)alpha E_r|K|^p + alpha(p-2)(2p-3)!!(E|K|^2/E|K|)^{p-1}E|K|]`; (d) by Lemma I.4.22, `(I.4.19)`: `E_r|K|^p <= (1+o(1))(2p-3)!!(E|K|^2/E|K|)^{p-1}E|K|`
CONSTANT_SCOPE: `(2p-3)!!` and `alpha(p-2)(2p-3)!!`; the two `alpha(p-2)` factors cancel **only because `b-a = alpha(p-2) > 0`** (needs `p>=3`, §7 C12)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.23,hutchcroft.i.4.22,hutchcroft.a.norm
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p8@L3190-L3257, #S4.E19@L3194-L3201, #S4.SS3.p8.5@L3222-L3222, #S4.SS3.p8.6@L3223-L3231, #S4.SS3.p8.7@L3232-L3232, #S4.Ex69@L3233-L3239, #S4.SS3.p8.8@L3240-L3240, #S4.Ex70@L3241-L3247, #S4.SS3.p8.9@L3248-L3248, #S4.Ex71@L3249-L3255, #S4.SS3.p8.10@L3256-L3256 ; Every index checked symbol by symbol (§7 C2, C3, C12): the induction hypothesis is applied at `ell+1` and `p-ell` (both `<= p-1` because `1 <= ell <= p-2`), giving exponent `(ell-1)+(p-ell-1) = p-2` on the ratio plus `(E|K|)^2`; Lemma I.4.22 is applied with `a=(p+1)alpha`, `b=(2p-1)alpha` (the driving term's index, since `(E|K|^2/E|K|)^{p-1}E|K|` has index `2alpha(p-1)+alpha`), and `b-a = alpha(p-2) > 0`. Defect note: the printed step "Since the driving term is regularly varying of index `(2p-1)alpha > (p+1)alpha`" *is* correct, but only for `p>2`; at `p=2` the two indices coincide and I.4.22 is inapplicable — the source handles `p=2` by I.4.15. Also needed explicitly: `(E|K|^2/E|K|)^{p-1}E|K|` is regularly varying (product of RV functions), which is not stated in the printed line but is what I.4.22's hypothesis requires. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.Ex69@L3233-L3239 | packet relation requires: the bracket sum is evaluated by Lemma I.4.23 applied to the s1 decomposition [ATTRIBUTION unique exact use-site match; line 745]
EDGE: hutchcroft.i.4.23 | .scratch/source/paper.html#S4.Ex69@L3233-L3239 | packet relation requires: "Using Lemma I.4.23 to simplify the constant": sum_{ell=1}^{p-2}C(p,ell)(2ell-1)!!(2p-2ell-3)!! = (p-2)(2p-3)!! [ATTRIBUTION unique exact use-site match; line 746]
EDGE: hutchcroft.i.4.22 | .scratch/source/paper.html#S4.Ex71@L3249-L3255 | packet relation requires: "we may apply Lemma I.4.22" with a=(p+1)alpha, b=(2p-1)alpha, driving term alpha(p-2)(2p-3)!!(...) [ATTRIBUTION unique exact use-site match; line 747]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.SS3.p8.6@L3223-L3231 | packet relation requires: the induction step rewrites beta_c∣J'‖B_r∣ as (1+o(1))alpha r^{-1} using (∗) [ATTRIBUTION unique exact use-site match; line 748]

NODE: hutchcroft.i.4.20.s3
KIND: step
TITLE: second induction — `(I.4.20)`/`(I.4.21)` (decorrelation) give `(I.4.22)`, and Lemma I.4.21 upgrades the upper bound to the first-order asymptotic
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p9@L3258-L3290
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p9@L3258-L3290
CONTRACT_ID: I.4.20.s3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `s1`; the decorrelation alternative `(I.4.20)` **or** `(I.4.21)` for every `0 <= ell <= p-1` in the relevant route; `(I.4.19)` (for the route-2 reduction)
SOURCE_QUANTIFIERS: every `p>=3` (second induction); `r -> infinity`
SOURCE_CONCLUSION: if either `(I.4.20)` `E_r[|K|^{ell+1}sum_{y in B_r}1(y notin K)|K_y|^{p-ell}] ~ |B_r|E_r|K|^{ell+1}E_r|K|^{p-ell}` or `(I.4.21)` the difference is `o((E|K|^2/E|K|)^{p-1}(E|K|)^2)` for every `0<=ell<=p-1`, then `(I.4.22)` holds and Lemma I.4.21 yields `E_r|K|^p ~ (2p-3)!!(E|K|^2/E|K|)^{p-1}E|K|`
CONSTANT_SCOPE: `(p+1)alpha` (self term) and `alpha(p-2)(2p-3)!!` (driving term) as in `s2`; `b-a = alpha(p-2)`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.20.s2,hutchcroft.i.4.21,hutchcroft.i.4.23
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p9@L3258-L3290, #S4.E20@L3261-L3268, #S4.E21@L3270-L3277, #S4.E22@L3279-L3288, #S4.SS3.p9.4@L3289-L3289 ; Note the logical shape: `(I.4.20)` *or* `(I.4.21)` suffices, not both; and `(I.4.20)` is the stronger-looking statement but the source says "either ... since we can absorb the errors ... into either the first or second term". The `s3` conclusion is used by no other node: it *is* the final step for each route (routes `r1`/`r2`/`r3` reach it through their case nodes). `p=2` is excluded here and handled by I.4.15; `p=1` by I.4.2. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.SS3.p9.1@L3259-L3260 | packet relation requires: the second induction starts from the same decomposition [ATTRIBUTION coordinator attribution: second-induction proof block; line 749]
EDGE: hutchcroft.i.4.20.s2 | .scratch/source/paper.html#S4.E20@L3261-L3268 | packet relation requires: "(I.4.19)" is the upper bound produced by s2 and used to close the second induction [ATTRIBUTION unique exact use-site match; line 750]
EDGE: hutchcroft.i.4.21 | .scratch/source/paper.html#S4.E22@L3279-L3288 | packet relation requires: the asymptotic ODE (I.4.22) is upgraded to a first-order asymptotic by Lemma I.4.21 [ATTRIBUTION unique exact use-site match; line 751]
EDGE: hutchcroft.i.4.23 | .scratch/source/paper.html#S4.E22@L3279-L3288 | packet relation requires: the same bracket identity enters (I.4.22) [ATTRIBUTION unique exact use-site match; line 752]

NODE: hutchcroft.i.4.20.c1
KIND: step
TITLE: Case 1 (`d>3alpha`) decorrelation: `E_r[|K|^{p+1}|K cap B_r|] <= E_r|K|^{p+2} <= (E|K|)^{2p+3}` is of smaller order than `|B_r|E|K|^{ell+1}E|K|^{p-ell} ~ r^{d+2p alpha}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p11@L3294-L3322
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p11@L3294-L3322
CONTRACT_ID: I.4.20.c1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d>3alpha`; `E_r|K| ≍ r^alpha`, `E_r|K|^2 ≍ r^{3alpha}`, and (by tree-graph + Hölder) `E_r|K|^p ≍_p r^{(2p-1)alpha}`
SOURCE_QUANTIFIERS: every `p>=3`, every `0<=ell<=p-1`; `r -> infinity`
SOURCE_CONCLUSION: `0 <= |B_r|E|K|^{ell+1}E|K|^{p-ell} - E_r[|K|^{ell+1}sum_{y in B_r}1(y notin K)|K_y|^{p-ell}] <= E_r|K|^{p+2} <= (E|K|)^{2p+3} = o(|B_r|E|K|^{ell+1}E|K|^{p-ell})` because `d+2p alpha > (2p+3)alpha`
CONSTANT_SCOPE: `(2p+3)!!`-type constants from the tree-graph bound, all absorbed in `<=_p`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.a.norm,hutchcroft.eq.i.2.3,ext.bk.extensions
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p11@L3294-L3322, #S4.Ex72@L3298-L3304, #S4.Ex73@L3306-L3312, #S4.Ex74@L3314-L3320, #S4.SS3.p11.4@L3321-L3321 ; The middle estimate uses `1(y notin K) <= 1` and `K cap B_r <= B_r` to replace the expectation by `E_r|K|^{p+1}|K cap B_r|`, then `|K cap B_r| <= |K|`; both are the printed moves. The lower bound `0 <=` is BK (via `s1`). Index check (§7 C7-style): `d+(2ell+1)alpha+(2p-2ell-1)alpha = d+2p alpha` (the printed intermediate writes `2ell+2-1` and `2p-2ell-1`; sum `= 2p`) — verified. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.Ex72@L3298-L3304 | packet relation requires: Case 1's difference is bounded by the s1 decomposition with 1(y notin K) <= 1 [ATTRIBUTION unique exact use-site match; line 753]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex74@L3314-L3320 | packet relation requires: d+2p alpha > (2p+3)alpha is decided with d>3alpha and ∣B_r∣ ~ r^d [ATTRIBUTION unique exact use-site match; line 755]
EDGE: hutchcroft.eq.i.2.3 | .scratch/source/paper.html#S4.SS3.p11@L3294-L3322 | CROSS_SLICE: the paper invokes the tree-graph inequality displayed at (I.2.3), not generalized Lemma I.4.16 at k=0
EDGE: ext.bk.extensions | .scratch/source/paper.html#S4.SS3.p11@L3294-L3322 | CROSS_SLICE: the non-negative cluster-gap decomposition uses the disjoint-occurrence/BK input retained in the I.2/I.3 candidate

NODE: hutchcroft.i.4.20.c2
KIND: step
TITLE: Case 2 (`d=3alpha`+(Hydro)) decorrelation: Cauchy–Schwarz, `(I.4.19)` at `2p+2`, and universal tightness give the required `o(|B_r|(...))`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p12@L3323-L3351
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p12@L3323-L3351
CONTRACT_ID: I.4.20.c2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d=3alpha`; `M_r=o(r^{(d+alpha)/2})`; `(I.4.19)`; `E_r|K cap B_r|^2 <= M_r E_r|K|`; `E_r|K|^2/E_r|K| <= (E_r|K|)^2 <= C r^{2alpha}` (tree-graph at `k=0`)
SOURCE_QUANTIFIERS: every `p>=3`, every `0<=ell<=p-1`; `r -> infinity`
SOURCE_CONCLUSION: `E_r[|K|^{p+1}|K cap B_r|] <= sqrt(E_r|K|^{2p+2}E_r|K cap B_r|^2) <= [(E|K|^2/E|K|)^{2p+1}(E|K|)^2 M_r]^{1/2} = o(r^{3alpha}r^{(d+alpha)/4}(E|K|^2/E|K|)^{p-1}E|K|) = o(r^d (E|K|^2/E|K|)^{p-1}(E|K|)^2)`
CONSTANT_SCOPE: `(4p+1)!!^{1/2}` from `(I.4.19)`; `M_r^{1/2}` rate `(Hydro)`; all absorbed in `<=`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.20.s1,hutchcroft.i.4.20.s2,hutchcroft.a.hydro,hutchcroft.a.norm,hutchcroft.eq.i.2.3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p12@L3323-L3351, #S4.Ex75@L3326-L3332, #S4.SS3.p12.2@L3333-L3333, #S4.Ex76@L3334-L3340, #S4.SS3.p12.3@L3341-L3342, #S4.Ex77@L3343-L3349, #S4.SS3.p12.4@L3350-L3350 ; Index check (§7 C23): reducing `(E|K|^2/E|K|)^{(2p+1)/2}` to `(E|K|^2/E|K|)^{p-1}` costs exactly `(E|K|^2/E|K|)^{3/2} <= C r^{3alpha}` (printed: "we used the tree-graph bound `E_r|K|^2/E_r|K| <= (E_r|K|)^2 <= r^{2alpha}`"), and the final conversion `r^{3alpha}r^{(d+alpha)/4} -> r^d` at `d=3alpha` balances against the extra factor `E|K| ~ r^alpha` on the right: `3alpha+(d+alpha)/4 = 4alpha` and `d+alpha = 4alpha`, **equal** — so the printed chain is consistent (this is *not* an error, and I checked it twice because an arithmetic slip here is easy). XSLICE(I.2): Corollary I.2.5. XSLICE(I.4.1): Prop I.4.2 for `E|K| ≍ r^alpha`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.20.s1 | .scratch/source/paper.html#S4.Ex75@L3326-L3332 | packet relation requires: Case 2 bounds the same difference by Cauchy-Schwarz on the s1 form [ATTRIBUTION unique exact use-site match; line 756]
EDGE: hutchcroft.i.4.20.s2 | .scratch/source/paper.html#S4.SS3.p12.2@L3333-L3333 | packet relation requires: "Using (I.4.19) to bound E_r∣K∣^{2p+2}" is exactly s2's output [ATTRIBUTION unique exact use-site match; line 758]
EDGE: hutchcroft.a.hydro | .scratch/source/paper.html#S4.SS3.p12.2@L3333-L3333 | packet relation requires: M_r = o(r^{(d+alpha)/2}) is what turns the bound into a little-o [ATTRIBUTION unique exact use-site match; line 759]
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex77@L3343-L3349 | packet relation requires: the conversion r^{3alpha}r^{(d+alpha)/4} -> r^d at d=3alpha balances the E∣K∣ ~ r^alpha factor [ATTRIBUTION unique exact use-site match; line 760]
EDGE: hutchcroft.eq.i.2.3 | .scratch/source/paper.html#S4.SS3.p12@L3323-L3351 | CROSS_SLICE: the paper invokes the tree-graph inequality displayed at (I.2.3), not generalized Lemma I.4.16 at k=0

NODE: hutchcroft.i.4.20.c3
KIND: step
TITLE: Case 3 (triangle condition) decorrelation: Lemma I.4.17 with `(p,q) = (ell+1,p-ell)` plus Lemma I.4.18 for `j>=4` and the repaired `ell=3` bound gives `(I.4.21)` with the bound `(nabla_{r^c}+r^{-c}+G_r(theta))(E|K|)^{2p}`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p13@L3352-L3365
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p13@L3352-L3365
CONTRACT_ID: I.4.20.c3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangle condition; `nabla_r -> 0`; `E_r|K|^2 ≍ (E_r|K|)^3` (from `hutchcroft.i.4.15` route 3)
SOURCE_QUANTIFIERS: every `p>=3`, every `0<=ell<=p-1`; `r -> infinity`
SOURCE_CONCLUSION: `E_r|K|^{ell+1}E_r|K|^{p-ell} - |B_r|^{-1}E_r[|K|^{ell+1}sum_{y in B_r}1(y notin K)|K_y|^{p-ell}] <=_p (nabla_{r^c}+r^{-c}+G_r(theta))(E_r|K|)^{2p} = o((E|K|^2/E|K|)^{p-1}(E|K|)^2)`
CONSTANT_SCOPE: `C_{ell+1,p-ell,j}` (universal integers) summed over `j=3,...,p+2`, times the constant of `i.4.18` and `i.4.18.ell3`; `<=_p` hides a `p`-dependent sum of those; `c`, `theta` free and re-chosen
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.17,hutchcroft.i.4.18,hutchcroft.i.4.18.ell3,hutchcroft.a.triangle,hutchcroft.a.tri.tail,hutchcroft.i.4.15.c3
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: same PACKET COMPOUND STATEMENT_SOURCE: paper.html#S4.SS3.p13@L3352-L3365, #S4.SS3.p13.2@L3354-L3362, #S4.SS3.p13.3@L3363-L3364 ; This is **consumer 2** of Lemma I.4.18 (§7 C8): with `(p',q') = (ell+1,p-ell)` the Lemma I.4.17 sum runs `j = 3,...,p+2` and each term is `T^j(x,y)(E|K|)^{2p+3-j}`; averaging `y` over `B_r` and using the polygon bound at `j>=4` gives `(nabla_{r^c}+r^{-c})(E|K|)^{(j-3)+(2p+3-j)} = (nabla_{r^c}+r^{-c})(E|K|)^{2p}`, while `j=3` needs the repair and gives `G_r(theta)(E|K|)^{2p}`. Since `(E|K|^2/E|K|)^{p-1}(E|K|)^2 ≍ (E|K|)^{2p}` by `E|K|^2 ≍ (E|K|)^3`, the `o(1)` from `nabla_{r^c}+r^{-c}+G_r -> 0` suffices. Only `o(1)` is needed here — no log-integrability. **Do not** try to prove the printed estimate verbatim: at `j=3` the printed hypothesis gives no decay (see refutation). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed. SCOPING REPAIR: this case previously consumed Proposition I.4.15 whole, which imported I.4.15's routes 1 and 2 into the triangle branch. It now consumes only hutchcroft.i.4.15.c3, the route-3 case computation; no d>3α or (Hydro) record is reached.
EDGE: hutchcroft.i.4.17 | .scratch/source/paper.html#S4.SS3.p13.2@L3354-L3362 | packet relation requires: "by Lemma I.4.17 and Lemma I.4.18": the polygon sum over ell=3,...,p+2 [ATTRIBUTION unique exact use-site match; line 761]
EDGE: hutchcroft.i.4.18 | .scratch/source/paper.html#S4.SS3.p13.2@L3354-L3362 | packet relation requires: the terms ell>=4 use the restricted polygon bound [ATTRIBUTION unique exact use-site match; line 762]
EDGE: hutchcroft.i.4.18.ell3 | .scratch/source/paper.html#S4.SS3.p13.2@L3354-L3362 | packet relation requires: the ell=3 term uses the averaged replacement (the printed bound would give no decay) [ATTRIBUTION unique exact use-site match; line 763]
EDGE: hutchcroft.a.triangle | .scratch/source/paper.html#S4.SS3.p13.1@L3353-L3353 | packet relation requires: "Case 3: The triangle condition" is the hypothesis under which nabla is finite [ATTRIBUTION coordinator attribution: case-3 proof block; a.triangle is not a direct dep of r3; line 765]
EDGE: hutchcroft.a.tri.tail | .scratch/source/paper.html#S4.SS3.p13.2@L3354-L3362 | packet relation requires: (nabla_{r^c}+r^{-c}) -> 0 is used to conclude the little-o [ATTRIBUTION unique exact use-site match; line 766]
EDGE: hutchcroft.i.4.15.c3 | .scratch/source/paper.html#S4.SS2.p15.1@L3004-L3004 | the needed input is I.4.15 route 3's case computation (E∣K∣^2 compared with (E∣K∣)^3 under the triangle condition), not the packaged proposition with its d>3α and Hydro branches; the route record itself cannot appear in DEPS, so its case carrier is consumed

NODE: hutchcroft.i.4.21
KIND: lemma
TITLE: Lemma I.4.21 — if `f' ~ (af+h)/r` with `h` regularly varying of index `b>a>0` and positive, then `f ~ h/(b-a)` and `f` is regularly varying of index `b`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm21@L3055-L3077
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.2@L3078-L3101
CONTRACT_ID: I.4.21
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `a>0`; `h : (0,infinity) -> (0,infinity)` measurable, **regularly varying of index `b>0`**; `f` differentiable with `f'(r) ~ (a f(r)+h(r))/r`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: if `b>a` then `f(r) ~ h(r)/(b-a)`; in particular `f` is regularly varying of index `b`
CONSTANT_SCOPE: `1/(b-a)` exact; requires `b>a` strictly (denominator positive)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.21.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.2@L3078-L3101 `f` is allowed to be **signed** (only differentiability is assumed) — that is why the signed ODE lemma I.5.26 is a *different* statement (downstream, I.5 slice) and cannot be substituted here. Applied in `i.4.20.s3` with `a=(p+1)alpha`, `b=(2p-1)alpha`. The constant is *correct*: `1/(b-a)`, not the reciprocal of anything else (§7 C13: for `h(s)=s^b`, `int^r s^{b-a-1}ds = r^{b-a}/(b-a)`). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.21.pf | .scratch/source/paper.html#S4.Thmthm21@L3055-L3077 | packet relation requires: statement established by proof node (no wrapper cycle) [ATTRIBUTION unique exact use-site match; line 772]

NODE: hutchcroft.i.4.21.pf
KIND: step
TITLE: proof of Lemma I.4.21 — solve the linear ODE with the multiplicative error `1-delta_r`, then Karamata on a regularly varying integrand of index `b-a-1 > -1`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p3@L3080-L3100
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p3@L3080-L3100
CONTRACT_ID: I.4.21.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as the lemma; `h` locally integrable on some `[r_0,infinity)`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: (i) there are `r_0` and `delta : [r_0,infinity)->R` with `|delta_r| -> 0` and `f' - (1-delta_r)ar^{-1}f = (1-delta_r)r^{-1}h`; (ii) the explicit solution `f(r) = exp[int_{r_0}^r (1-delta_s)as^{-1}ds] f(r_0) + exp[...]int_{r_0}^r (h(s)/s)exp[-int_{r_0}^s (1-delta_t)at^{-1}dt]ds`; (iii) the integrand `s^{-1}h(s)exp[-int...]` is regularly varying of index `b-a-1 > -1`, so `int_{r_0}^r ~ (1/(b-a))h(r)exp[-int_{r_0}^r ...]`; (iv) the homogeneous term is of lower order and the claim follows
CONSTANT_SCOPE: `1/(b-a)`; the `1-delta` factors contribute `r^{o(1)}` only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS3.p3@L3080-L3100 (single paragraph, three displays) XSLICE(I.2): Lemma I.2.10 (Karamata) is invoked with index `b-a-1 > -1`, i.e. the **cumulative-integral** branch whose constant `1/(b-a)` is the correct one. This slice does **not** use the ∞-tail branch, so the campaign's known wrong denominator there (`1/(1-alpha)` vs `1/(-alpha-1)`, errata `karamata-negative-index-tail`) is **not** imported and cannot infect this proof (§7 C13). A proof obligation remains: the step "the other term is of lower order" requires `exp[int (1-delta) a ds/s] = r^{a+o(1)} = o(r^b)` for `b>a`, which is true for any `delta_r -> 0`; recorded as an obligation of the pf node, not a defect. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.22
KIND: lemma
TITLE: Lemma I.4.22 — inequality version: `f' <= (1+o(1))(af+h)/r` with `f>0`, `h` positive regularly varying of index `b>a`, gives `f <= (1+o(1))h/(b-a)`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm22@L3105-L3127
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.3@L3128-L3150
CONTRACT_ID: I.4.22
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `a,b>0`; `h:(0,infinity)->(0,infinity)` measurable, regularly varying of index `b`; `f` **positive** with `f'(r) <= (1+o(1))(af(r)+h(r))/r`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: if `b>a` then `f(r) <= (1+o(1))h(r)/(b-a)`
CONSTANT_SCOPE: `1/(b-a)`; the `(1+o(1))` is *outside*, on `h/(b-a)`
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.22.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.3@L3128-L3150 Positivity of `f` is genuinely needed (Grönwall multiplies by a positive integrating factor); in the application `f = E_r|K|^p > 0` and `h = alpha(p-2)(2p-3)!!(...)^{p-1}E|K| > 0` because `p>=3` — the same positivity as the denominator. Applied in `i.4.20.s2`. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.22.pf | .scratch/source/paper.html#S4.Thmthm22@L3105-L3127 | packet relation requires: statement established by proof node (no wrapper cycle) [ATTRIBUTION unique exact use-site match; line 773]

NODE: hutchcroft.i.4.22.pf
KIND: step
TITLE: proof of Lemma I.4.22 — Grönwall's inequality `[108, 1.III]` then the same computation as I.4.21
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p5@L3130-L3149
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p5@L3130-L3149
CONTRACT_ID: I.4.22.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as the lemma; Grönwall with locally integrable `g,h`
SOURCE_QUANTIFIERS: `r -> infinity`
SOURCE_CONCLUSION: `f(r) <= exp[int_{r_0}^r g](f(r_0) + int_{r_0}^r exp[-int_{r_0}^s g]h(s)ds)` for all `r>=r_0`; the lemma follows by the same calculation as in I.4.21
CONSTANT_SCOPE: as the lemma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS3.p5@L3130-L3149 External input: Grönwall's inequality, cited `[108, 1.III]` — **title-only here, not a verified external leaf** (I did not open it). It is a standard textbook statement and its exact form needed is the one displayed at `#S4.SS3.p5`. Recorded as an external obligation of this proof node (§6, §4); I do not create an `external` node for it because I cannot verify the cited source's exact hypotheses. Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.23
KIND: lemma
TITLE: Lemma I.4.23 — `sum_{k=0}^{n-1} C(n,k)(2k-1)!!(2n-2k-3)!! = (2n-1)!!` for every `n>=2`
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm23@L3154-L3162
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.4@L3163-L3187
CONTRACT_ID: I.4.23
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the double-factorial convention with (-1)!!=1; no analytic hypothesis
SOURCE_QUANTIFIERS: every integer `n>=2`
SOURCE_CONCLUSION: the identity, with the convention `(-1)!!=1` (needed at `k=0` and `k=n-1`)
CONSTANT_SCOPE: no implicit constant; every coefficient is the displayed integer or binomial coefficient
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.23.pf
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: paper.html#S4.SS3.4@L3163-L3187 Verified exactly for `n=2..40` (§7 C1) and the derived constant identity `sum_{ell=1}^{p-2}... = (p-2)(2p-3)!!` verified for `p=3..39` (§7 C3). The convention `(-1)!!=1` is *not* stated in the printed lemma; without it the identity is ill-posed at both ends. Recorded as a minor source omission (**D4**). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.
EDGE: hutchcroft.i.4.23.pf | .scratch/source/paper.html#S4.Thmthm23@L3154-L3162 | packet relation requires: statement established by proof node (no wrapper cycle) [ATTRIBUTION unique exact use-site match; line 774]

NODE: hutchcroft.i.4.23.pf
KIND: step
TITLE: proof of Lemma I.4.23 — exponential generating functions `sum (2n-1)!!x^n/n! = (1-2x)^{-1/2}` and `sum_{n>=1}(2n-3)!!x^n/n! = 1-(1-2x)^{1/2}`, multiplied
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p7@L3165-L3186
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p7@L3165-L3186
CONTRACT_ID: I.4.23.pf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: generalized binomial theorem
SOURCE_QUANTIFIERS: formal power series (`n>=1`)
SOURCE_CONCLUSION: `sum_{n>=1}(x^n/n!)sum_{k=0}^{n-1}C(n,k)(2k-1)!!(2n-2k-3)!! = ((1-(1-2x)^{1/2})/(1-2x)^{1/2}) = sum_{n>=0}(2n-1)!!x^n/n! - 1`; comparing coefficients gives the identity for `n>=1`
CONSTANT_SCOPE: no implicit constant; coefficient comparison has coefficient 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: repaired
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: UNSCHEMAED INPUT PROPOSED: extractor=m6@smwobyis9 | reviewer - PACKET PROOF_SOURCE: #S4.SS3.p7@L3165-L3186 (through `#S4.Ex?` displays at L3165–L3186) The printed proof compares coefficients at `n` and gets the identity for `n>=2` (at `n=1` both sides are `1` under `(-1)!!=1`, so `n>=1` also holds). External input: the EGF expansions, cited to the generalized binomial theorem and to `[110]` "Rule 3′" — title-only, not a verified external leaf. Coefficient comparison re-checked exactly (§7 C1). Imported from /workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration/.scratch/packet-native-validation/repaired/I423_NODES.md; all source claims and references remain unreviewed.

NODE: hutchcroft.i.4.18.psd
KIND: step
TITLE: SOURCE_GAP: positive-definiteness and diagonal maximality of every two-point matrix power
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948
PROOF_SOURCE: .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948
CONTRACT_ID: hutchcroft.i.4.18.psd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T(x,y)=P_{β_c,r}(x↔y) is translation-invariant; positivity of its defining cluster mixture must be used, not symmetry alone
SOURCE_QUANTIFIERS: every integer ell>=1 and every r>0, all lattice vectors x
SOURCE_CONCLUSION: sup_x T^ell_{β_c,r}(0,x)=T^ell_{β_c,r}(0,0), and T^ell is positive definite for every ell>=1
CONSTANT_SCOPE: no multiplicative constant; diagonal maximality has coefficient 1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.a.cutoff
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: the source asserts translation-invariance and positive-definiteness but does not prove it here. Derivation to review: T=sum_C P(C is a cluster) 1_C1_C^T is a mixture of rank-one projections, hence PSD; T^ell is PSD, and |K_{0x}|²<=K_{00}K_{xx} with K_{00}=K_{xx} by translation. Symmetry alone can fail at odd ell; even powers need no PSD. This proof-oriented record is not a topology promotion.
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.SS2.p11.1@L2947-L2948 | the cut-off two-point matrix is the object whose cluster mixture must establish positive-definiteness

NODE: hutchcroft.i.4.18.mom
KIND: step
TITLE: Diagonal moment bound T^n(0,0) <= (E|K|)^{n-1} and the derived E|K| ⪰ r^alpha input
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS2.p11.2@L2962-L2962
PROOF_SOURCE: .scratch/source/paper.html#S4.Ex54@L2963-L2969
CONTRACT_ID: hutchcroft.i.4.18.mom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: cut-off law at beta_c; diagonal maximality from i.4.18.psd
SOURCE_QUANTIFIERS: every integer n>=1; every r>0; r->infinity for the lower moment-rate comparison
SOURCE_CONCLUSION: T^n_{β_c,r}(0,0) <= (E_{β_c,r}|K|)^{n-1}; and the triangle-route first-moment asymptotic supplies E|K| ⪰ r^alpha
CONSTANT_SCOPE: only the source normalization (*) and the Prop I.4.2 comparison; no extra exponent or constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.18.psd,hutchcroft.a.cutoff,hutchcroft.a.norm,hutchcroft.i.4.2.c3
ROUTES: -
ROUTE_FOR: -
NOTE: SOURCE_GAP: induction T^n(0,0)=sum_xT^{n-1}(0,x)tau_r(x) <= (sup_xT^{n-1}(0,x))sum_xtau_r(x)=T^{n-1}(0,0)E|K| reuses diagonal maximality. E|K| ⪰ r^alpha is supplied by the actual I.4.1 route, not by a scope note or a formal T^{-1} at ell=3. INPUT SCOPING: this step previously consumed Proposition I.4.2 whole in order to use the first-moment asymptotic. It now consumes hutchcroft.i.4.2.c3, the triangle-case derivation of that asymptotic, matching Lemma I.4.18's own hypothesis (the triangle condition). No d>3alpha or (Hydro) record is reached from here, and no conclusion of I.4.2 other than (a) is used.
EDGE: hutchcroft.i.4.18.psd | .scratch/source/paper.html#S4.Ex54@L2963-L2969 | diagonal maximality powers the induction
EDGE: hutchcroft.a.cutoff | .scratch/source/paper.html#S4.Ex54@L2963-L2969 | the cut-off two-point function and E∣K∣ enter the moment bound
EDGE: hutchcroft.a.norm | .scratch/source/paper.html#S4.Ex54@L2963-L2969 | normalization (*) identifies the radius asymptotics
EDGE: hutchcroft.i.4.2.c3 | .scratch/source/paper.html#S4.SS2.p11.2@L2962-L2962 | the only input taken from Proposition I.4.2 here is `E∣K∣ ~ (alpha/beta_c) r^alpha`, and Lemma I.4.18's own hypothesis is the triangle condition; consuming the umbrella proposition imported its d>3alpha and (Hydro) alternatives into every triangle-branch consumer

NODE: hutchcroft.i.1.6.hd1
KIND: route
TITLE: (HD) alternative 1 (`d > 3α`): case-1 route of Theorem I.1.6
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
CONTRACT_ID: hutchcroft.i.1.6.hd1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) alternative 1 of §I.1.3, `d > 3α` (`.scratch/source/paper.html#S1.SS3.p1@L518-L537`, item 1 at L522-L524). Printed case hypothesis, consumed as the single branch of this route.
SOURCE_QUANTIFIERS: each integer p ≥ 1, r → ∞ for (I.1.6), n → ∞ for (I.1.7)
SOURCE_CONCLUSION: under `d > 3α` the case-1 derivations of Propositions I.4.2 (both conclusions), I.4.15 and I.4.20 give (I.1.6), with no use of Lemma I.4.3 and no triangle condition
CONSTANT_SCOPE: this record introduces no constant; the shared constant A of (I.1.6)/(I.1.7) is that of the case derivations it consumes
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: route.hd.case1,hutchcroft.i.4.2.c1,hutchcroft.i.4.2.c4,hutchcroft.i.4.15.c1,hutchcroft.i.4.20.c1
ROUTES: -
ROUTE_FOR: hutchcroft.i.1.6
NOTE: ONE of exactly three routes of the root; never conjoined with hd2/hd3, and no record may assume two (HD) alternatives at once. Consumes the case records c1/c4/c1/c1 rather than the packaged propositions, so alternatives 2 and 3 of I.4.2 (and with them (Hydro) and the triangle condition) do not enter this route. Absence of Lemma I.4.3 is the printed clause read contrapositively ('apply in cases 2 and 3 ... by Lemma I.4.3'). Nothing here re-derives, re-statuses or promotes I.4.2/I.4.15/I.4.20.
EDGE: route.hd.case1 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the one printed alternative this route consumes
EDGE: hutchcroft.i.4.2.c1 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | case-1 derivation of Proposition I.4.2, conclusion (a)
EDGE: hutchcroft.i.4.2.c4 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | case-1 derivation of Proposition I.4.2, conclusion (b)
EDGE: hutchcroft.i.4.15.c1 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the `d > 3α` case of Proposition I.4.15
EDGE: hutchcroft.i.4.20.c1 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the `d > 3α` case of Proposition I.4.20

NODE: hutchcroft.i.1.6.hd2
KIND: route
TITLE: (HD) alternative 2 (`d > 6` with the `‖x−y‖^{−d+2}` bound): case-2 route of Theorem I.1.6
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
CONTRACT_ID: hutchcroft.i.1.6.hd2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) alternative 2 of §I.1.3, `d > 6` and `P_{βc}(x↔y) ⪯ ‖x−y‖^{−d+2}` (`.scratch/source/paper.html#S1.SS3.p1@L518-L537`, item 2 at L526-L529); Lemma I.4.3 then supplies `∇_r` log-integrable.
SOURCE_QUANTIFIERS: each integer p ≥ 1, r → ∞ for (I.1.6), n → ∞ for (I.1.7)
SOURCE_CONCLUSION: the triangle case derivations of the three propositions give (I.1.6) provided `∇_{βc} < ∞`; that first conjunct is not an (HD) premise and is not discharged here
CONSTANT_SCOPE: this record introduces no constant; the shared constant A of (I.1.6)/(I.1.7) is that of the case derivations it consumes
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: route.hd.case2,hutchcroft.i.4.3,hutchcroft.i.4.2.ap-hd23,hutchcroft.i.4.2.c3,hutchcroft.i.4.2.c5,hutchcroft.i.4.15.c3,hutchcroft.i.4.20.c3
ROUTES: -
ROUTE_FOR: hutchcroft.i.1.6
NOTE: ONE of exactly three routes of the root, never conjoined. CONSUMES ONLY ONE CASE RECORD: route.hd.case2. The route is CONDITIONAL and does not close (I.1.6): hutchcroft.i.4.2.ap-hd23 records that neither Lemma I.4.3 nor any other record derives `∇_{βc} < ∞` from the two-point bound. No (Hydro) record is consumed, because alternative 2 is not the `d = 3α` branch.
EDGE: route.hd.case2 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the one printed alternative this route consumes
EDGE: hutchcroft.i.4.3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the printed proof applies the propositions in case 2 *by* Lemma I.4.3
EDGE: hutchcroft.i.4.2.ap-hd23 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the only record of the missing triangle bridge; consumed, not discharged
EDGE: hutchcroft.i.4.2.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | triangle-case derivation of Proposition I.4.2, conclusion (a)
EDGE: hutchcroft.i.4.2.c5 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | triangle-case derivation of Proposition I.4.2, conclusion (b)
EDGE: hutchcroft.i.4.15.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the triangle case of Proposition I.4.15
EDGE: hutchcroft.i.4.20.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the triangle case of Proposition I.4.20

NODE: hutchcroft.i.1.6.hd3
KIND: route
TITLE: (HD) alternative 3 (`d = 6`, `α = 2`, logarithmic bound): case-3 route of Theorem I.1.6
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373
CONTRACT_ID: hutchcroft.i.1.6.hd3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (HD) alternative 3 of §I.1.3 **as printed** (`d = 6`, `α = 2`, `P_{βc}(x↔y) ⪯ (log‖x−y‖)^{−1}‖x−y‖^{−d+2}`), carried by the CONTRACT_VERSION 1 text of `.scratch/source/paper.html#S1.SS3.p1@L518-L537` item 3 (L531-L534) restated by the dedicated printed case record hutchcroft.i.1.6.hd3.case. The candidate v2 repair of route.hd.case3 is deliberately NOT consumed.
SOURCE_QUANTIFIERS: each integer p ≥ 1, r → ∞ for (I.1.6), n → ∞ for (I.1.7)
SOURCE_CONCLUSION: as route hd2, in the `d = 6`, `α = 2` case: the triangle case derivations give (I.1.6) provided `∇_{βc} < ∞`, which is still undischarged
CONSTANT_SCOPE: this record introduces no constant; the shared constant A of (I.1.6)/(I.1.7) is that of the case derivations it consumes
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.3,hutchcroft.i.4.2.ap-hd23,hutchcroft.i.4.2.c3,hutchcroft.i.4.2.c5,hutchcroft.i.4.15.c3,hutchcroft.i.4.20.c3,hutchcroft.i.1.6.hd3.case
ROUTES: -
ROUTE_FOR: hutchcroft.i.1.6
NOTE: ONE of exactly three routes of the root, never conjoined. CONTRACT-VERSION DISCIPLINE: this route consumes hutchcroft.i.1.6.hd3.case, a KIND: definition with CONTRACT_VERSION 1 containing only printed alternative 3. It does NOT consume route.hd.case3, whose CONTRACT_VERSION 2 candidate repair is still awaiting the coordinator's source ruling -- so the printed v1 obligation is preserved and no consumer uses the v2 form. For `d = 3α` Corollary I.4.14 also gives (Hydro) and hence Proposition I.4.2's second alternative; that supplies (I.1.6) at `p = 1` and I.4.15's regular-variation clause but NOT the sharp constant A, so it cannot replace the triangle bridge. Recorded, not used. CASE-IDENTITY REPAIR: the single case record is now a printed v1 case-3 definition, rather than the disjunction-valued assumption.hd. This does not repair the problematic logarithm at small normalized distances, which remains an anchor/source question.
EDGE: hutchcroft.i.4.3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the printed proof applies the propositions in case 3 *by* Lemma I.4.3
EDGE: hutchcroft.i.4.2.ap-hd23 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the only record of the missing triangle bridge; consumed, not discharged
EDGE: hutchcroft.i.4.2.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | triangle-case derivation of Proposition I.4.2, conclusion (a)
EDGE: hutchcroft.i.4.2.c5 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | triangle-case derivation of Proposition I.4.2, conclusion (b)
EDGE: hutchcroft.i.4.15.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the triangle case of Proposition I.4.15
EDGE: hutchcroft.i.4.20.c3 | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | the triangle case of Proposition I.4.20
EDGE: hutchcroft.i.1.6.hd3.case | .scratch/source/paper.html#S4.SS3.p15.1@L3373-L3373 | hd3 consumes its own printed (HD) alternative 3, not the whole disjunction and not candidate HD-v2

NODE: hutchcroft.i.4.2.c1
KIND: step
TITLE: Lemma I.4.9 discharges the `d > 3α` case of Proposition I.4.2 (conclusion (a))
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i1@L2084-L2087
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.5@L2312-L2386
CONTRACT_ID: I.4.2.c1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d > 3α`
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: E_{beta_c,r}|K| ~ (alpha/beta_c) r^alpha under alternative 1
CONSTANT_SCOPE: as Proposition I.4.2; no constant introduced by this record
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.9,hutchcroft.i.4.2.odeglue,hutchcroft.i.4.dsp7
ROUTES: -
ROUTE_FOR: -
NOTE: CASE DERIVATION of Proposition I.4.2, one per alternative, mirroring the packet's own hutchcroft.i.4.15.c1..c3 / hutchcroft.i.4.20.c1..c3 pattern so that a consumer can select ONE alternative instead of importing all of them. The alternative-level route record keeps its own packaging (`hutchcroft.i.4.2.r1..r5` now depend on this record) and is not re-derived here. the alternative is one case of the proposition, not a standing assumption. The proposition's open obligations are untouched; no source hypothesis is added.
EDGE: hutchcroft.i.4.9 | .scratch/source/paper.html#S4.SS1.5@L2312-L2386 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the case derivation uses only the neutral ODE assembly and its own case premise/path
EDGE: hutchcroft.i.4.dsp7 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | this case's actual settlement/bridge obligation is retained explicitly

NODE: hutchcroft.i.4.2.c2
KIND: step
TITLE: Lemma I.4.10 discharges the `d = 3α` plus (Hydro) case of Proposition I.4.2 (conclusion (a))
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i2@L2088-L2091
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.6@L2396-L2428
CONTRACT_ID: I.4.2.c2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d = 3α` and the hydrodynamic condition (Hydro)
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: E_{beta_c,r}|K| ~ (alpha/beta_c) r^alpha under alternative 2
CONSTANT_SCOPE: as Proposition I.4.2; no constant introduced by this record
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.10,hutchcroft.i.4.2.odeglue,hutchcroft.i.4.dsp7
ROUTES: -
ROUTE_FOR: -
NOTE: CASE DERIVATION of Proposition I.4.2, one per alternative, mirroring the packet's own hutchcroft.i.4.15.c1..c3 / hutchcroft.i.4.20.c1..c3 pattern so that a consumer can select ONE alternative instead of importing all of them. The alternative-level route record keeps its own packaging (`hutchcroft.i.4.2.r1..r5` now depend on this record) and is not re-derived here. this case is NOT consumed by any (HD) route: no (HD) alternative is `d = 3α` plus (Hydro). The proposition's open obligations are untouched; no source hypothesis is added.
EDGE: hutchcroft.i.4.10 | .scratch/source/paper.html#S4.SS1.6@L2396-L2428 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the case derivation uses only the neutral ODE assembly and its own case premise/path
EDGE: hutchcroft.i.4.dsp7 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | this case's actual settlement/bridge obligation is retained explicitly

NODE: hutchcroft.i.4.2.c3
KIND: step
TITLE: Lemmas I.4.11 and I.4.12 discharge the triangle case of Proposition I.4.2 (conclusion (a))
STATEMENT_SOURCE: .scratch/source/paper.html#S4.I1.i3@L2092-L2095
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.8@L2496-L2520
CONTRACT_ID: I.4.2.c3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition `∇_{beta_c} < infinity`
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: E_{beta_c,r}|K| ~ (alpha/beta_c) r^alpha under alternative 3
CONSTANT_SCOPE: as Proposition I.4.2; no constant introduced by this record
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.11,hutchcroft.i.4.12,ext.triangle-open,hutchcroft.i.4.2.odeglue,hutchcroft.i.4.dsp7
ROUTES: -
ROUTE_FOR: -
NOTE: CASE DERIVATION of Proposition I.4.2, one per alternative, mirroring the packet's own hutchcroft.i.4.15.c1..c3 / hutchcroft.i.4.20.c1..c3 pattern so that a consumer can select ONE alternative instead of importing all of them. The alternative-level route record keeps its own packaging (`hutchcroft.i.4.2.r1..r5` now depend on this record) and is not re-derived here. the case uses the averaged triangle bound; the global-to-averaged bridge is hutchcroft.i.4.2.s3. The proposition's open obligations are untouched; no source hypothesis is added.
EDGE: hutchcroft.i.4.11 | .scratch/source/paper.html#S4.SS1.8@L2496-L2520 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.12 | .scratch/source/paper.html#S4.SS1.8@L2496-L2520 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: ext.triangle-open | .scratch/source/paper.html#S4.SS1.8@L2496-L2520 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the case derivation uses only the neutral ODE assembly and its own case premise/path
EDGE: hutchcroft.i.4.dsp7 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | this case's actual settlement/bridge obligation is retained explicitly

NODE: hutchcroft.i.4.2.c4
KIND: step
TITLE: Case 1 (`d > 3α`) logarithmic integrability of the error `H_r` (Proposition I.4.2, conclusion (b))
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Ex5@L2106-L2112
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.c4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: `d > 3α`
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: H_r is a logarithmically integrable error function under the first alternative of (b)
CONSTANT_SCOPE: as Proposition I.4.2; no constant introduced by this record
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.13,hutchcroft.i.4.dsp7,hutchcroft.i.4.2.odeglue
ROUTES: -
ROUTE_FOR: -
NOTE: CASE DERIVATION of Proposition I.4.2, one per alternative, mirroring the packet's own hutchcroft.i.4.15.c1..c3 / hutchcroft.i.4.20.c1..c3 pattern so that a consumer can select ONE alternative instead of importing all of them. The alternative-level route record keeps its own packaging (`hutchcroft.i.4.2.r1..r5` now depend on this record) and is not re-derived here. the second alternative of (b), the triangle plus log-integrable one, is c5. The proposition's open obligations are untouched; no source hypothesis is added.
EDGE: hutchcroft.i.4.13 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.dsp7 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the case derivation uses only the neutral ODE assembly and its own case premise/path

NODE: hutchcroft.i.4.2.c5
KIND: step
TITLE: Triangle plus `∇_r` log-integrable case of the error `H_r` (Proposition I.4.2, conclusion (b))
STATEMENT_SOURCE: .scratch/source/paper.html#S4.Thmthm2.p1.3@L2105-L2105
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.c5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the triangle condition and logarithmic integrability of `∇_r`
SOURCE_QUANTIFIERS: r → ∞
SOURCE_CONCLUSION: H_r is a logarithmically integrable error function under the second alternative of (b)
CONSTANT_SCOPE: as Proposition I.4.2; no constant introduced by this record
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3-smwolzzaf-proposal
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.13,hutchcroft.i.4.2.s3,hutchcroft.i.4.2.odeglue
ROUTES: -
ROUTE_FOR: -
NOTE: CASE DERIVATION of Proposition I.4.2, one per alternative, mirroring the packet's own hutchcroft.i.4.15.c1..c3 / hutchcroft.i.4.20.c1..c3 pattern so that a consumer can select ONE alternative instead of importing all of them. The alternative-level route record keeps its own packaging (`hutchcroft.i.4.2.r1..r5` now depend on this record) and is not re-derived here. a genuine conjunction inside one source alternative, recorded as one case; hutchcroft.i.4.3 supplies the log-integrability under (HD)2/3. The proposition's open obligations are untouched; no source hypothesis is added.
EDGE: hutchcroft.i.4.13 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.s3 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | case discharge cited by Proposition I.4.2 for this alternative
EDGE: hutchcroft.i.4.2.odeglue | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | the case derivation uses only the neutral ODE assembly and its own case premise/path

NODE: hutchcroft.i.4.2.odeglue
KIND: step
TITLE: Neutral first-moment ODE/error assembly shared by the individual I.4.2 cases
STATEMENT_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
PROOF_SOURCE: .scratch/source/paper.html#S4.SS1.10@L2556-L2562
CONTRACT_ID: I.4.2.odeglue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the exact first-moment derivative/error identity, the H_r-normalization, and the unconditional logarithmic transport lemma I.4.13; no HD, Hydro, triangle or triangle-logarithm alternative is bundled here
SOURCE_QUANTIFIERS: only as invoked by a selected I.4.2 case; no alternatives are supplied by this record
SOURCE_CONCLUSION: the neutral assembly is available to the selected case derivation; it does not itself discharge any case's first-moment or triangle premise
CONSTANT_SCOPE: only the already-fixed kernel/normalization constants; no threshold, Triangle or Hydro witness is introduced
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.13,hutchcroft.i.4.dsp7,hutchcroft.i.4.g9
ROUTES: -
ROUTE_FOR: -
NOTE: SCOPING REPAIR: this retains only the neutral ODE/normalization assembly auxiliaries dsp7 and g9 and the logarithmic transport lemma I.4.13. Each case record supplies its own first-moment derivation alongside this glue. The general assembly s1 retains the full case analysis for the proposition itself; this neutral record is not a proof provider or a review verdict.
EDGE: hutchcroft.i.4.13 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | condition-free ODE/normalization/logarithmic assembly only; no alternative case hypothesis is supplied here
EDGE: hutchcroft.i.4.dsp7 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | condition-free ODE/normalization/logarithmic assembly only; no alternative case hypothesis is supplied here
EDGE: hutchcroft.i.4.g9 | .scratch/source/paper.html#S4.SS1.10@L2556-L2562 | condition-free ODE/normalization/logarithmic assembly only; no alternative case hypothesis is supplied here

NODE: hutchcroft.i.1.6.hd3.case
KIND: definition
TITLE: (HD) alternative 3 (printed v1): d=6, α=2 with the logarithmic two-point bound
STATEMENT_SOURCE: .scratch/source/paper.html#S1.I1.i3.p1@L531-L534
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.i.1.sec3.hd.case3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d=6; α=2; P_{β_c}(x↔y) ⪯ (log‖x−y‖)^{-1}‖x−y‖^{-d+2} for all x≠y, exactly as printed in §I.1.3 alternative 3
SOURCE_QUANTIFIERS: all x≠y in Z^d; this is the one selected case, not the disjunction of cases 1,2,3
SOURCE_CONCLUSION: the printed third alternative, consumed only in the HD3 application of Theorem I.1.6; no repaired HD-v2 form is substituted, and the frozen root is unchanged
CONSTANT_SCOPE: the printed implicit constant ⪯ is allowed to depend only on d, α, J. SOURCE/ANCHOR COMPATIBILITY FINDING, not an adopted correction: at ρ<1 the printed right side is negative, and at ρ=1 its (log ρ)⁻¹ factor is undefined in ordinary mathematics and 0 in Lean's ℝ. Thus this alternative can be unsatisfiable on admissible normalizations. This empties the corresponding case-3 instantiation, not the other alternatives or the theorem universally; no repair is made here
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
NOTE: CASE-SPECIFIC PRINTED-V1 OBLIGATION. Formerly hd3 consumed assumption.hd, whose own content is the disjunction of all three alternatives, while its NOTE falsely cast that as only alternative 3. This record has the exact case-3 v1 content under the existing hutchcroft.i.1.sec3.hd.case3 source-contract family, and does not consume any HD-v2 corrective definition. The frozen HD3 wording still needs an author/source ruling if a successor is wanted; no anchor or manifest is edited by this candidate change. The small-norm defect is recorded as the printed hypothesis's limitation, not presented as a theorem-wide refutation.

NODE: hutchcroft.i.1.15.step.objects.regularization
KIND: step
TITLE: SOURCE_GAP: positivity, boundedness, slow variation and choice of the normalized inverse pair
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm15@L914-L938
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.15.step.objects.regularization
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the Hydro p=1 and p=2 moment asymptotics and their positive, nonzero cluster-volume scale, plus the standard regular-variation regularization obligations already recorded in the consumer record
SOURCE_QUANTIFIERS: choose the pair jointly; no separate choices may silently change A_r. The construct must work at arbitrarily large radius, with positive bounded measurable slowly varying A_r and a normalized inverse A* of the correct slow variation class
SOURCE_CONCLUSION: construct A_r > 0 with Ê_{β_c,r}|K| ∼ A_r r^{2α}, establish boundedness, measurability and slow variation, and construct the normalized A* satisfying the printed mutual-inversion convention. This is a proof obligation, not permission to select an arbitrary witness
CONSTANT_SCOPE: A_r and A*_n are one jointly linked pair with the exact r ↦ A_r r^{2α} scale and n ↦ (A*_n)^{-1/(2α)}n^{1/(2α)} inverse; no arbitrary class invariance or extra logarithmic correction is declared proved
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator-review
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
DEPS: hutchcroft.i.4.2.c2,hutchcroft.i.4.15.c2,hutchcroft.def.rv,ext.bgt.thm1.5.12
ROUTES: -
ROUTE_FOR: -
NOTE: EXPLICIT OPEN OBLIGATION / SOURCE_GAP. The statement asserts the joint properties but does not print the reconstruction; the later tail-proof paragraph only introduces inverse notation. The original objects record placed positivity, boundedness, slow variation and normalized mutual inversion only in SOURCE_HYPOTHESES and prose, so these obligations could disappear from a coverage count. This record makes them an actual dependency of step.objects and preserves the formerly discussed normalization/positivity-boundedness/inverse duties as one JOINT source obligation. No literal ε joint-inverse lemma is asserted by the source. A later ε/smoothing reconstruction would require a separately identified external lemma, not an invented premise. The printed mutual-inversion and regular-variation inverse theorem inputs are explicit edges. The mathematical content is not released: existence of a normalized smooth inverse is permitted only via a proved regular-variation regularization, not an arbitrary choice or a canonical carrier invented later. The printed Remark I.1.16 sign inconsistency remains separately recorded and is not silently repaired.
EDGE: hutchcroft.i.4.2.c2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | the Hydro first-moment asymptotic supplies one factor of the scale object
EDGE: hutchcroft.i.4.15.c2 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | the Hydro second-moment regime supplies Ø∣K∣^{2α} and its regular variation
EDGE: hutchcroft.def.rv | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | the normalized smooth inverse must satisfy regular-variation regularization, not merely an arbitrary choice
EDGE: ext.bgt.thm1.5.12 | .scratch/source/paper.html#S3.SS2.3@L1915-L1979 | regular variation of the actual inverse scale, not just the definition of regular variation, is required to discharge the printed A*-inverse construction
<!-- Add verified fixed-cutoff intensity monotonicity; no full i.4.g7 promotion. -->
