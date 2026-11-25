# Baseline source audit and coverage method

**Initial planning audit, 12 November 2026.** This is a first-pass review and a reproducible mechanical inventory, not a completed assertion census or a verification of the mathematics. The notes are a coverage baseline; the library and wiki will be organised independently of their chapters.

## 1. The immutable notes snapshot

The [source snapshot](../sources/notes/book_draft.tex) is byte-identical to the uploaded `book_draft.tex`.

| Property | Value |
|---|---|
| Title | Critical Percolation, Scaling, and Long-Range Models: A Detailed Expository Draft |
| Author in source | Tom Hutchcroft |
| Bytes / physical lines | 286,293 / 6,307 |
| SHA-256 | `61c11fcbd2d4ac600e9b96b6b1a81c399b6e049dd208e8790d5f06e1b02b5fd4` |
| Numbered chapters / sections | 10 / 56 |
| Named statement environments | 45: 20 theorems, 11 propositions, 8 lemmas, 3 corollaries, 3 definitions |
| Explicit proof environments | 22 |
| Outer displayed-math blocks | 698 |
| Explicit labels | 7 |
| Paragraphs selected by a liberal mechanical screen | 363, of which 260 overlap neither a named statement nor an explicit proof environment |

The [inventory documentation](sources/notes/README.md) explains the method and limitations. The [summary](sources/notes/summary.json), [heading index](sources/notes/headings.tsv), [named-statement index](sources/notes/named_statements.tsv), [candidate paragraphs](sources/notes/candidate_paragraphs.tsv), and [full mechanical inventory](sources/notes/inventory.json) preserve source positions for review.

Reproduce the scan from the repository root:

```sh
python3 scripts/inventory_source.py \
  --source sources/notes/book_draft.tex \
  --output-dir docs/sources/notes
```

The provisional `S...` and `P...` labels in these outputs identify mechanical records in this snapshot. They are not permanent mathematical assertion IDs. The parser does not expand arbitrary TeX, infer all standing hypotheses, or decide whether a sentence asserts a theorem.

## 2. Why the named-statement count is inadequate

Chapter 3 has no named statement environments but 45 displayed-math blocks and substantial precise content. Chapter 10 has no named statements but several implication diagrams. Elsewhere, tree calculations, transform identities, definitions, conditional limits, and proof-local inequalities occur in prose or displays.

An equation is not automatically a separate theorem, and a paragraph may contain several assertions. A complete inventory needs semantic reading of all source regions, including regions missed by a keyword screen. The first-pass reading across the draft has identified useful claim families and issues, but it has not yet classified every assertion and its complete quantified context.

## 3. Concrete correction cases

The following examples illustrate what the project must track. They are mathematical observations from the draft, not compiled Lean counterexamples. They do not authorise silent edits to the source.

### N-ERR-01: the susceptibility tail-sum index

In Chapter 3, Scaling relations, the displayed equality sums `P(|K| >= n)` starting at `n = 0`. For a nonnegative integer-valued variable `X`, the tail identity starts at one:

$$\mathbb E X=\sum_{n\ge1}\mathbb P(X\ge n).$$

Starting at zero adds one in the finite-expectation case. The singleton cluster gives the immediate check: its expectation is one, while the displayed zero-based sum is two. The scaling heuristic can survive this correction, but the exact equality is a separate assertion and must be repaired explicitly.

### N-ERR-02: the endpoint of the exponential cluster-tail bound

Chapter 4's sharpness theorem states `P_beta(|K| >= n) <= exp(-c_beta*n)` for every `n >= 1`, with `c_beta > 0`. At `n = 1`, the left side is one because the cluster contains its root, while the right side is strictly less than one.

The source contract needs a prefactor, a shifted threshold, or an eventual range. The actual corrected form must be chosen against the proof and the intended source theorem, then reviewed. This is not evidence against sharpness itself.

### N-ERR-03: the deterministic critical branching process

Chapter 2 says a Galton–Watson process with mean at most one dies out almost surely. The deterministic offspring law `xi = 1` has mean one and survives forever. The usual extinction conclusion requires excluding this degenerate case at criticality. The later finite, nonzero variance assumption in the discussion of critical asymptotics should not be silently imported into every preceding sentence.

### N-ERR-04: local total-progeny asymptotics need support conditions

Chapter 2 moves from a critical generating-function singularity to both a tail estimate and `P(T = n)` of order `n^(-3/2)`. For critical offspring taking values zero and two with equal probabilities, total progeny is odd, so the point probability vanishes at every even integer.

The local asymptotic needs the appropriate lattice/support qualification and hypotheses; it does not follow in the stated all-integer form merely from the tail asymptotic. Separate the tail theorem, transform theorem, and local limit theorem in the registry.

### N-ERR-05: monotonicity in the OSSS covariance statement

The Chapter 6 covariance proposition uses a right side containing coordinate covariances with an event `A`, without stating that `A` is increasing. For one fair bit and `A = B = {bit = 0}`, the absolute covariance of the two indicators is `1/4`, while the covariance of `A` with the bit is `-1/4` and the revealment is one.

Thus the proposition as printed cannot hold without a correction. Match the intended covariance theorem and its exact assumptions before choosing the formal statement; a later discussion of increasing events does not repair the missing hypothesis in the displayed contract automatically.

### N-ERR-06: zero ghost field is not its positive-field limit

Source: [pinned notes, Chapter 2, Ghost fields, lines 532–570](https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L532).
Tracked in [issue #238](https://github.com/tomhutchcroft/lrp/issues/238).
SCOUT independently read this passage following WIKI's report.

The source defines the observable by independently marking each vertex with
probability `1-exp(-h)` and asking whether the root cluster hits a mark. At
literal `h=0`, on this countable tree every vertex is unmarked almost surely,
so the observable is zero for every bond parameter. At `p=1`, the source's
later displayed zero-field formula instead returns one. This is a mathematical
counterexample, not a compiled Lean counterexample.

Recommended reading: retain the literal marking observable `M_p(0)=0` and
write `M_p(0+)` for its positive-field limit. For `h>0`, condition on the
cluster size `T`: the conditional hit probability is `1-exp(-h*T)` for
finite `T`, and one for infinite `T`. Countable independence gives the latter
by taking larger finite subsets of the cluster. As `h` decreases to zero,
these probabilities converge to the indicator of `T=infinity`; bounded
convergence gives `M_p(0+)=P_p(T=infinity)`. No finite susceptibility assumption
is needed. The expression at `h=0,T=infinity` must not be assigned by silently
extending the positive-field exponential convention.

For the rooted binary tree, setting `h=0` in the recursion gives
`theta = 2*p*theta - p^2*theta^2`. When `p>1/2`, both zero and
`(2*p-1)/p^2` solve it. The recursion alone does not select the positive root:
literal ghost connection selects zero, whereas the right-hand limit selects
the survival probability. At `p=0`, avoid the quotient entirely and use the
zero value. An alternative is to define a right-continuous extension at zero,
but that value is then not the literal marking event.

Disposition: correction needed in the source notation; recommended interpretation
recorded, with the original snapshot unchanged. This record does not approve a
source amendment or assert a formal proof. WIKI's tag `8B62` in PR #252
distinguishes the positive-field limit from literal zero; its separate
susceptibility-ratio claim and any compiled correspondence require their own
verification.

### N-ERR-07: the boundary numerator needs a positive part

SCOUT independently checked WIKI's [report on issue 34](https://github.com/tomhutchcroft/lrp/issues/34#issuecomment-6891883565)
against the pinned notes S011 (lines 1712–1734) and
[arXiv:2106.06400v3, Lemma 2.1, (2.2)](https://arxiv.org/html/2106.06400v3#S2).
Both display the unsigned square. Keep this distinct from the transitive specialization.

A connected three-vertex path suffices: beta=1, edge weights 0.99 and 0.01,
and S the first two vertices. Put p=1-exp(-0.99), t=1-exp(-0.01).
Then chi_min=1+t+pt, chi_max=1+p+t, Q(S)=2(1+p)^2, and Phi(S)=0.01.
The proposed right side equals
2[p-t(1+p)]^2/[(1+p+t)(1+p)^2], approximately 0.172543.
For a non-numerical contradiction, p>3/5 and 0<t<1/100 imply that
this right side exceeds 841/10050, which exceeds 1/100.

The proof only bounds the signed expression
a=chi_min*|S|-sum_{u,v in S}T(u,v) by the nonnegative outgoing mass L.
One may conclude a_+^2 <= L^2, not a^2 <= L^2.
Recommended contract: nonempty finite S, beta>0, finite chi_max, and the
positive-part square; alternatively use L^2 directly. For constant susceptibility,
a=L>=0, so this defect disappears. No source text or formal theorem is amended.

### N-ERR-08: the stronger triangle derivative numerator fails near zero

The pinned notes S010 (lines 1690–1698) state the lower bound
chi*(chi-Delta)/(3*beta^2*Delta^2). SCOUT independently checked WIKI's
normalized-line counterexample.

On Z with nearest-neighbour intensity 1/2, the row sum is one.
For p=1-exp(-beta/2), unique paths give T(x,y)=p^|x-y|,
chi=2 exp(beta/2)-1, chi'=exp(beta/2), and
Delta=1+6p^2/(1-p^2)^2. The triangle formula follows by counting
6n ordered pairs with range n and summing 6 sum_{n>=1} n p^(2n).
Thus chi=1+beta+O(beta^2), Delta=1+O(beta^2):
the proposed lower bound diverges as 1/(3 beta), while chi' tends to one.
Every finite beta is subcritical in this example. At beta=0.01 the two sides
are about 1.005013 and 33.239367; these numerical checks are illustrative,
not the proof.

Independently inspected [the paper's (2.4)–(2.5)](https://arxiv.org/html/2106.06400v3#S2).
Writing X=chi*|K|-U and V for its weighted triple sum, the stated inputs
E[U]<=chi*Delta and E[V]<=chi*(2A+B), together with X>=0, yield
(chi-Delta)_+^2/[beta^2*(2A+B)] after cancellation in
(E[X])^2/[beta^2*chi*E[V]]. They do not yield the stronger numerator.
With the separate diagram bound 2A+B<=3 Delta^2 this gives the weaker
squared-positive-part formula. This arithmetic check does not certify the
entire infinite-volume derivative argument or its endpoint consequences.

Disposition for both records: counterexamples confirmed mathematically;
recommended replacements await source acceptance and independent formalization.
WIKI's 67GX/JTBG and MTYL/1EWX/4KBG are separate article assertions. No
compiled proofs, accepted source amendments, or reviews of the entire article
are claimed here. Checks used the pinned notes and versioned HTML; published
pagination and other editions were not verified.

### N-ERR-09: a switching cancellation leaves an overlap term

Source: [arXiv:1904.05804v2, Section 5, proof of Lemma 5.3](https://arxiv.org/html/1904.05804v2#S5),
the equality of the 01 gain and 10 loss immediately before the both-open bound.
SCOUT read the product-coordinate definitions and that step directly, following
WIKI's updated [report](https://github.com/tomhutchcroft/lrp/issues/34#issuecomment-6891883565).
The notes' related discussion is lines 2965–3133; S019 itself is the named
backbone-scaling proposition at lines 3003–3016, not a named switching lemma.

Take a star with centre o, leaves a,b, and bonds e=oa, f=ob. The first bond
configuration is (X,F); the second is (Y,F), with X,Y,F independent fair bits.
Each of two ghost fields has three independent fair marks, independent of bonds.
Both roots are o. Let H0 be disjoint ghost connections in (X,F), and H1 the
connections in the two configurations with disjoint product-coordinate witnesses.
The two copies of e can serve different witnesses in H1; f cannot.
Marks from different fields are distinct coordinates; zero-edge paths are allowed.

Independent enumeration of all nine bits gives H0 in 254 assignments and H1
in 260. There are 16 gains with (X,Y)=(0,1), 15 losses with (1,0), and 5 gains
with (1,1), out of 512. No other transitions occur. Thus the total increase
is 6/512, not the both-open gain 5/512. This confirms failure of the stated
cancellation under the source's product-coordinate interpretation.

There is a general finite algebraic replacement. For increasing events A,B and
one distinguished Bernoulli-p coordinate, let Cij be the disjoint occurrence
of their forced sections Ai and Bj on the remaining coordinates. Write
U=C10 union C01 and V=C10 intersection C01. Open-witness reduction gives
shared probability (1-p)mu(C00)+p mu(U). The split probability is
(1-p)^2 mu(C00)+p(1-p)[mu(C10)+mu(C01)]+p^2 mu(C11).
Subtracting, and using C00 subset V and U subset C11, yields

`split - shared = p^2 mu(C11 minus U) + p(1-p) mu(V minus C00).`

The extra overlap term is nonnegative and need not vanish. In the star its
contribution is 1/512, with 5/512 from the first term. This also explains
the enumeration without relying on an asserted cancellation bijection.

Disposition: intermediate proof step invalid as written; no refutation of a
reverse-BK conclusion is claimed. A repaired diagram bound must control both
terms, or justify another argument. The finite identity is not itself such a
bound. WIKI's X4OE/XWH4 remain separate assertions, not accepted amendments to
the source. The independent Python enumeration is a finite check, not Lean
compilation or a kernel proof. No source or Lean file is changed.

### N-ERR-10: critical-field powers require a bounded range or saturation

Source: Duminil-Copin–Tassion, [arXiv:1502.03050v3](https://arxiv.org/pdf/1502.03050v3),
Proposition 1.3 (printed p. 5), Proposition 2.3 (p. 11), and the final
differential inequalities in Sections 1.5 (p. 9) and 2.6 (p. 21).
SCOUT inspected this version directly following WIKI's
[report](https://github.com/tomhutchcroft/lrp/issues/34#issuecomment-6891883565).

The propositions quantify over every positive field h with a fixed positive
constant c, giving lower bounds c*h^(1/2) for a probability and c*h^(1/3)
for an Ising spin expectation. Both observables are at most one.
Choosing h>c^(-2), respectively h>c^(-3), contradicts the printed statements.
This does not refute their small-field conclusions.

Here is an independent, conditional calculus repair, rather than a certification
of the paper's probabilistic inputs. Fix A=beta_c*sum_y J(0,y) with 0<A<infinity.
Assume M:(0,infinity)->[0,1] is nondecreasing and locally absolutely continuous.
For percolation assume A*M*M' >= 1-M almost everywhere; for Ising assume
A*M^2*M' >= 2*(1-M^2) almost everywhere. These are the respective displayed
inequalities after fixing beta=beta_c and combining their inputs.

For any h with M(h)<1/2, monotonicity keeps M(t)<1/2 on 0<t<=h.
In the first case (M^2)'=2*M*M' >= 1/A; integrating from delta to h and
discarding M(delta)^2>=0 gives M(h)^2 >= (h-delta)/A.
Let delta decrease to zero. In the second case
(M^3)'=3*M^2*M' >= 9/(2*A), and the same argument applies.
Consequently the conditional all-field bounds are

- percolation: M(h) >= min(1/2, sqrt(h/A));
- Ising: M(h) >= min(1/2, (9*h/(2*A))^(1/3)).

The alternative case M(h)>=1/2 is immediate. Neither argument assumes a
vanishing right limit at zero, so a possible positive critical order parameter
does not invalidate this calculus step. Both bounds imply a constant times
min(h^r,1), with r=1/2 or 1/3. The constants can be chosen as
min(1/2,A^(-1/2)) and min(1/2,(9/(2*A))^(1/3)), respectively.

Recommended reuse contract: explicitly saturated positive-field bounds, with
finite positive A and the requisite probabilistic and regularity hypotheses
proved separately. This is not a proof of those hypotheses or of the source's
infinite-volume differentiation steps. WIKI's separate percolation argument
36PN is not reviewed by this record. Source acceptance, a full Ising proof,
and Lean correspondence remain open. No source snapshot is edited.

## 4. Other high-priority formulation reviews

These are review items, not a claim that every corresponding published theorem is false.

| Area | Issue to resolve |
|---|---|
| Sharpness and boundary susceptibility | Root/graph assumptions; finite critical parameter; positive-part versus signed expressions; an intermediate Cauchy–Schwarz calculation and its stated conclusion |
| Ghosts and decision trees | A cluster-volume event is independent of ghost coordinates, whereas the ghost-connection event is not; keep their covariance formulae separate |
| Universal tightness | Nonempty finite regions, quantile conventions, and allowed ranges of scale parameters |
| Hierarchical benchmark | The two-point source separates an averaged theorem from a radial pointwise corollary; the cluster-volume paper works with a more specific kernel family |
| Cutoff renormalisation | The integral cutoff differs from hard deletion of long edges; its derivative, omitted intensity, and regularity convention need exact definitions |
| Exact constants | Norm-ball volume, kernel normalisation, and distinct moment/size-bias constants must not be suppressed before exact asymptotics |
| Multipoint geometry | Separate a deterministic Möbius-covariance identity, a discrete comparison estimate, and a continuum limit; generic transformed lattice points need not lie on the lattice |
| Localisation | CL, wCL, and Hydro require separate quantified definitions and theorem-backed implications; endpoint cases need explicit treatment |
| Spatial limits | Cutoff motion versus full stable motion; size bias versus conditioning; moment convergence versus random-measure convergence and moment determinacy |

For the hierarchical issue, the primary references are [the 2021 two-point paper](https://arxiv.org/pdf/2103.17013) and [the 2022 cluster-volume paper](https://arxiv.org/pdf/2211.05686). The mathematical hypotheses should be reconciled before the notes' combined benchmark is assigned as a single proof task. The long-range trilogy supplies the detailed cutoff and localisation contracts; the [project bibliography](PROJECT_PLAN.md#references) links its parts.

## 5. Complete-coverage protocol

1. **Pin the source.** Record edition, revision, content fingerprint, and reliable locators. Keep an original snapshot of the notes and an edition-specific register for each book.
2. **Partition every source region.** Assign chapters or sections for audit, including prose, exercises, appendices, proofs, tables, captions, and mathematical roadmap arrows. A complete partition prevents unlabelled material from disappearing.
3. **Run independent extraction passes.** Mechanical scans locate candidates. Semantic readers identify precise assertions and local standing assumptions. A second review checks omissions and compound statements.
4. **Split claims at meaningful boundaries.** Separate definitions, implications, equivalences, estimates, exact constants, limit claims, and proof steps when their assumptions or status differ.
5. **Give each occurrence a disposition.** Established assertion, quoted input, definition, conditional theorem, conjecture, heuristic without a precise assertion, duplicate, correction needed, or clarification needed. A non-mathematical passage can be marked reviewed without inventing a theorem.
6. **Map to canonical mathematics.** Use many-to-many mappings. A notation change, specialisation, or equivalence needs an explicit justification; different meanings of a shared symbol remain separate.
7. **Review exact contracts.** Specify all quantifiers, constants, parameter ranges, ambient hypotheses, and infinite-value conventions. Record review on each source-to-assertion and assertion-to-Lean mapping, with the relevant versions.
8. **Choose proof routes.** Alternative proofs can complete a theorem, but precise intermediate assertions in the original source remain covered by checked auxiliary obligations where necessary. Quoted inputs remain proof obligations.
9. **Check the formal closure.** A result counts as proved only with its exact statement, full dependency closure, required build, and allowed axioms. The source's status and the project's proof status remain separate.
10. **Audit both directions at release.** From a source passage, locate its disposition and verified counterpart. From a claimed formal result, locate its reviewed meaning, sources, and evidence. Unresolved corrections and unproved inputs remain visible.

The coverage denominator is unknown until a source census is complete. Report "census in progress" rather than a misleading percentage over the named theorems. A correction is not counted as a literal proof of the original sentence: show the original, the reviewed replacement, and the relationship.

## 6. How the books enter the same system

Provisionally use Grimmett's **Percolation**, second edition (1999), and Heydenreich–van der Hofstad's **Progress in High-Dimensional Percolation and Random Graphs** (2017). Their full statement inventories are future work in this proposal. In particular, the accessible author manuscript of the latter is dated 17 March 2017 and has different pagination from the publisher's edition.

The source concordances should preserve each book's complete order, including exercises and survey chapters. The mathematical pages should instead join common material: configurations and observables, graph and planar geometry, branching and exploration, correlation/differential inequalities, mean-field mechanisms, finite-size scaling, IIC, random walks, limits, and related models. Source completeness and subject organisation are complementary requirements.
