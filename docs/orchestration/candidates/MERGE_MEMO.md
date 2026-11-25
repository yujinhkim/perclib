# Candidate merge and rename memo

Status: **PROPOSED, review required**. This is not a reviewed topology, an
accepted `RENAMES` table, a root-closure review, or a proof-provider assignment.
The production `DEPGRAPH.md` is deliberately unchanged.

## Exact identity scan

The repository parser, candidate validator and a separately implemented read-only differ have been run on the proposed merged candidate graph `combined.md` (four packets, 239 records), its four in-scope slices, and the exact changed nodes and edges. The latest scoped scan found:

```text
combined records:                    239
combined edges:                      453
duplicate NODE IDs:                  0
duplicate (CONTRACT_ID,VERSION):     0
I.1.6 closure / I.1.15 closure:    130 / 91
HD route closures:                  47 / 65 / 65
union root-closure nodes:            154
records outside root closure:        85
shared slice/merged field or edge differences: 0
```

The new HD3 case record uses the **printed version-1** form under the existing
`hutchcroft.i.1.sec3.hd.case3` contract family; the distinct version-2 interpretation
remains unconsumed. HD3 consumes that one case, not the complete `(HD)` disjunction.
The root retains its theorem-level disjunction. Neither small-norm behavior nor the
(HD)2/(HD)3 triangle bridge is repaired. Four root-to-own-conclusion-display edges
were removed; the actual moment-computation consumers remain. The new regularization
record is still a `SOURCE_GAP`, with the two Hydro cases, regular variation and the
inverse-function leaf as dependencies. It is not an invented smoothness or epsilon
construction. The finite-threshold consumer `bilat` retains an explicit dependency on
`betac.fin` and is limited to the regimes printed at source line 353, rather than the
withdrawn all-dimension reconstruction. No other record or root was promoted: every
record except the expressly withdrawn critical-point record remains `PROPOSED`.

Those outside nodes include intentionally exported, refutation, and
not-yet-consumed records; they are not silently filled. One additional record,
`hutchcroft.i.1.beta_c.bilat:step-finite`, keeps the withdrawn finite-range
line reconstruction with `TOPOLOGY_STATUS: DISPUTED` and no proof source or
dependencies. Its valid surviving content is the separate $d\ge2$ square-lattice
bound; no one-dimensional finiteness is asserted for $\alpha>1$.
There is still no global root-closure review or global reviewer.

This is an identity measurement, not a proof that the semantic duties are
disjoint. In particular, a different local contract name does not license a
second copy of the same source obligation during a later merge.

## Applied I.1 identity renames

The following contract identities were changed in the reviewed I.1 candidate,
following bounded review `smwohv6t4/m7` (finding B8, section-I.1.3 versus
Definition I.1.3 ownership). The stable `NODE` IDs for these five records are
preserved; these are contract-family identity changes, not `REVIEWED` or proof
promotions. A versioned HD-v2 correction to `route.hd.case3` is separately
`CONTRACT_VERSION: 2` and remains subject to independent source review.

| old contract ID | replacement contract ID |
| --- | --- |
| `hutchcroft.i.1.3.hd` | `hutchcroft.i.1.sec3.hd` |
| `hutchcroft.i.1.3.hd.case1` | `hutchcroft.i.1.sec3.hd.case1` |
| `hutchcroft.i.1.3.hd.case2` | `hutchcroft.i.1.sec3.hd.case2` |
| `hutchcroft.i.1.3.hd.case3` | `hutchcroft.i.1.sec3.hd.case3` (version 2) |
| `hutchcroft.i.1.3.double_factorial` | `hutchcroft.i.1.sec3.double_factorial` |

The tail proof was also split and renamed explicitly:
`hutchcroft.i.1.6.step.chi2` and `.step.constants` became branch-specific
`hutchcroft.i.1.step.chi2.hd` and `.constants.hd`, with new critical-dimension
branch records `.chi2.crit` and `.constants.crit`. The integral computation is
`hutchcroft.i.1.step.integral.chi2`, a conditional computation shared by both
branches instead of a dependency on either root's tail conclusion. These are
semantic decompositions, not reassignments of one proof to two roots.
The I.4.2 source proposition is assembled through the two ordinary obligations
`i.4.2.a` and `i.4.2.b`; the five routes no longer conflate both conclusions.

Except for these explicitly recorded changes, semantic overlaps still require
independent adjudication. No arbitrary contract reuse or additional rename is
approved.

## Semantic overlaps that still must be adjudicated before root-level merging

| duty | current candidate records | status and required review |
| --- | --- | --- |
| Double-factorial convention | `i1:convention.double_factorial` | Sole matching record in the present candidate set. Check `hutchcroft.i.4.23` in `i423` separately: it proves an identity using the convention; it is not obviously a second definition of the convention. Do not conflate the two duties. |
| Joined I.1.15 construction | `i1:hutchcroft.i.1.15.step.objects` plus its `.regularization` dependency | The new `SOURCE_GAP` makes positivity, boundedness, measurability, slow variation, and the joint normalized mutual-inverse obligation reachable, and makes the inverse-function theorem a direct input. No construction is printed at the referenced tail-proof paragraph. Earlier research named `.normalize`, `.posbdd`, and `.inverse`; the joined record does not assert that those proof duties are discharged, and no epsilon/smoothing lemma is invented. Count comparisons alone do not certify the construction. |
| `(HD+)` alternatives | `i5152:hutchcroft.i.5.1.r1`–`.r4`; `i5354:R.HD.1`–`R.HD.4` | The first packet now records source-hypothesis definitions, not derivation routes; the second keeps case-scoped assumption leaves. Neither definition is a proof. The I.5 case steps identify the cases they jointly discharge. Review any later consolidation role by role rather than concatenating these records. |
| `(HD+)` disjunction | `i5152:hutchcroft.i.5.1`; `i5354:S54.STANDING` | One is the source hypothesis-list definition, the other the standing disjunction for §I.5.4. The statement-level disjunction contrasts with case-scoped proof prerequisites and with case-partition steps jointly needed for the full statement. Preserve those roles explicitly if a later consolidation is approved. |
| Hydrodynamic condition | `i1:hutchcroft.i.1.14`; `i5152:hutchcroft.i.5.1.r4`; `i5354:AS.HYDRO` and `R.HD.4`; the `DEPGRAPH.md` seed's `assumption.hydro` | Definition, source assumption, and case packaging are not interchangeable. The exact Hydro source is `S1.Thmthm14`, not the similarly numbered display `S1.E14`. A merge must discharge every consumer at Definition I.1.14 without duplicating or discarding that condition. |
| Critical-point positivity/finiteness | `i1:hutchcroft.i.1.2.betac.fin`; `i5152:hutchcroft.i.5.beta.c.pos` | The same derived obligation has different candidate formulations and external boundaries. Use the corrected ordinary derivations, including the finite-range `Z^2` coupling; do not merge in the superseded nearest-neighbour-`Z` argument or any free `hbc` premise. |
| Mass transport | `i41:hutchcroft.i.4.msm`; `i5152:hutchcroft.i.5.mtp` | Check whether these consume the same general principle or different finite/multivariate forms and whether either is a source-proven step rather than an assumption leaf. Do not infer duplication from a shared name. |

## Required follow-up before any root-level merge operation

1. The bounded source reviewers supply an identity and exact span for each
   ordinary record repair. The applied renames above are only an identity
   rewrite, not an independent source-topology PASS.
2. The second-round reviewers must resolve each remaining semantic role
   difference and any proposed consolidation.
3. If a duty is joined into one node, show that every former substantive
   construction or case obligation remains reachable; count comparisons cannot
   establish that property.
4. Re-run duplicate-contract, node-shape, topology, coverage, and fresh global
   root-closure checks on the merged graph. Until then, keep the candidates
   separate and `PROPOSED`, and assign no Lean providers.
