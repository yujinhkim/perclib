# Proof dependency database — Critical LRP I

GRAPH_VERSION: 4
ROOTS: hutchcroft.i.1.6,hutchcroft.i.1.15
CORPUS: .scratch/source/paper.html | arXiv:2508.18807v1
CONVENTIONS: normalized volume-one unit ball, C=1; named node IDs i.<number>; proof-step IDs <parent>:<semantic-slug>; append-only amendments after publication
STANDING_ASSUMPTIONS: assumption.hd,assumption.hydro
EXTERNAL_POLICY: named literature and matching PercLib results are explicit authorized external leaves; source hypotheses are never enlarged by proof steps
FROZEN_ANCHORS: hutchcroft.i.1.6,hutchcroft.i.1.15
FROZEN_MANIFEST: docs/orchestration/FROZEN_ANCHOR_MANIFEST.json | sha256:bb855df26fab249019a04a395d3e613446796ce0d4d6a648a58e969359011c36
WRITER: openmathmodel-orchestrator
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

Dependency direction is NODE -> prerequisite. This is the identity/template layer before slice merge;
not a completed graph or proof-status statement. Ordinary LEAN_STATUS is NOT_STARTED.

## Nodes

NODE: hutchcroft.i.1.6
KIND: theorem
TITLE: High-dimensional cluster moments
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm6@L552-L577
PROOF_SOURCE: .scratch/source/paper.html#S4.SS3.6@L3370-L3377
CONTRACT_ID: hutchcroft.i.1.6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: at least one of (HD)
SOURCE_QUANTIFIERS: normalized model data; every integer p≥1 in the moment statement; integer n→∞ in the tail; shared positive constant/family
SOURCE_CONCLUSION: (I.1.6) E_beta_c,r |K|^p ~ (2p-3)!! A^(p-1) (alpha/beta_c) r^((2p-1)alpha) for every p≥1; (I.1.7) P_beta_c(|K|≥n) ~ (alpha/beta_c) sqrt(2/(pi A))/sqrt(n) as n→∞
CONSTANT_SCOPE: one positive A shared by moment and tail; outer normalized model data only
FROZEN_FILE: PercLib/CriticalLRP/Orchestration/Frozen/HighDimensionalMoments.lean
FROZEN_DECL: PercLib.CriticalLRP.Orchestration.theorem_I_1_6
FROZEN_ANCHOR_ID: theorem_I_1_6_v1
FROZEN_ABI_SHA256: 1de8ef21dfc1913f0b19b9e87efeacaec3341c1e048943bbe6d868bdf7a14e59
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: exact frozen declaration; this record is not itself a proof result

NODE: hutchcroft.i.1.15
KIND: theorem
TITLE: Cluster volumes in the critical dimension
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm15@L914-L938
PROOF_SOURCE: .scratch/source/paper.html#S3.SS2.3@L1915-L1979
CONTRACT_ID: hutchcroft.i.1.15
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d=3 alpha and Hydro
SOURCE_QUANTIFIERS: normalized model data; every integer p≥1 in the moment statement; integer n→∞ in the tail; shared positive constant/family
SOURCE_CONCLUSION: (I.1.16) E_beta_c,r |K|^p ~ (2p-3)!! A_r^(p-1) (alpha/beta_c) r^((2p-1)alpha) for every p≥1; (I.1.17) P_beta_c(|K|≥n) ~ (alpha/beta_c) sqrt(2/(pi Astar_n))/sqrt(n) as n→∞
CONSTANT_SCOPE: one bounded slowly varying pair (A_r, Astar_n) with mutually inverse scale mappings and shared source-scoped constants
FROZEN_FILE: PercLib/CriticalLRP/Orchestration/Frozen/CriticalDimensionMoments.lean
FROZEN_DECL: PercLib.CriticalLRP.Orchestration.theorem_I_1_15
FROZEN_ANCHOR_ID: theorem_I_1_15_v1
FROZEN_ABI_SHA256: 567d1220587aa715d9046f1f89f7ef6cf404d04da5e175637b7cb165b774e186
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: exact frozen declaration; this record is not itself a proof result

NODE: assumption.hd
KIND: assumption
TITLE: HD standing model hypothesis
STATEMENT_SOURCE: .scratch/source/paper.html#S1.SS3.p1@L518-L537
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.hd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: source-normalized model data
SOURCE_QUANTIFIERS: whichever alternative(s) the consuming theorem states
SOURCE_CONCLUSION: HD holds
CONSTANT_SCOPE: source model constants only; no arbitrary local indices
DEPS: -
ROUTES: -
ROUTE_FOR: -
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: source standing hypothesis
LEAN_NOTE: discharge at the consuming result, not inferred from a module name or proof wrapper
NOTE: assumption at consumption sites

NODE: assumption.hydro
KIND: assumption
TITLE: Hydro standing model hypothesis
STATEMENT_SOURCE: .scratch/source/paper.html#S1.Thmthm14@L888-L901
PROOF_SOURCE: -
CONTRACT_ID: hutchcroft.hydro
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: source-normalized model data
SOURCE_QUANTIFIERS: whichever alternative(s) the consuming theorem states
SOURCE_CONCLUSION: M_r = o(r^((d+alpha)/2))
CONSTANT_SCOPE: source model constants only; no arbitrary local indices
DEPS: -
ROUTES: -
ROUTE_FOR: -
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: openmathmodel-orchestrator
REVIEWER: -
LEAN_STATUS: ASSUMED
LEAN_REF: source standing hypothesis
LEAN_NOTE: discharge at the consuming result, not inferred from a module name or proof wrapper
NOTE: assumption at consumption sites
