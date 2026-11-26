# Lemma I.4.17: nonnegativity, marked expansion and the `p = 2, q = 1` display

The modules under `Correlation/I417` and `Correlation/I417Example` formalize three
parts of Lemma I.4.17 (supplied PDF p. 45). The upper diagram bound for general
`p, q` remains open; no coverage beyond the statements below is implied.

## General nonnegativity

`I417A.momentDiff_nonneg` proves, for every `p q : ℕ`, that

```text
E[1(x ↮ y) |Kx|^p |Ky|^q] ≤ E|Kx|^p · E|Ky|^q
```

for the canonical independent bond law and the native extended-natural cluster
cardinality. It uses the increasing labelled-cluster events and BK directly;
`I417A.momentDiff_nonneg'` independently obtains the same inequality from the
general two-cluster correlation inequality. No moment-finiteness or transitivity
assumption is needed for the `ℝ≥0∞` statement.
`I417A.momentDiff_nonneg_basepoint` supplies the source's common-basepoint moment
product from invariance under vertex permutations, while
`I417A.momentDiff_nonneg_real` gives the real-valued subtractive nonnegativity
with explicit finiteness hypotheses on the two moments.
`I417A.longRange_momentDiff_nonneg` specializes the general result to the
long-range Bernoulli law.

## The printed second-moment-by-first-moment display

For a countable vertex type `V`, an opening profile `π` with `π e < 1`, and roots
`x y`, `I417Example.printed_le` assumes only
`hχ : ∀ v, meanVol π v = meanVol π x` and proves

```text
volSq π x * meanVol π y - exclMomentSq π x y
  ≤ T3 π x y * (meanVol π x)^4 + 2 * T4 π x y * (meanVol π x)^3.
```

Here `volSq` is the native expected squared cluster volume, `meanVol` is the
expected cluster volume, `exclMomentSq` is the actual excluded second-by-first
moment with the indicator `x ↮ y`, and `T3`, `T4` are the third and fourth powers
of the two-point matrix. Subtraction is the stated `ℝ≥0∞` operation; the proof
adds no finite-moment assumption. `I417Example.printed_le_of_transitive` derives
`hχ` from `π`-preserving vertex permutations acting transitively at `x`.
`I417Example.latticeLongRange_I417_p21_printed` discharges that hypothesis for
the canonical power-law law on `ℤ^d` using translation invariance of `lrKernel`.

## The proof and its constant bookkeeping

* `I417Example.twoCopy_moment_le_tight` replaces the naive base-cluster reading of
  the printed two-copy argument by the actual restored configuration. The diagonal
  alternative evaluates to `exclMomentSq`. The `y ∈ Kx` alternative is redundant:
  `I417Example.yInSet_subset_markSet` includes it in the marked family at `w = y`,
  using the empty certificate for the certain event `y ↔ y`.
* `I417Example.exists_two_level_branch` performs a two-level first-hit
  decomposition of `x₁,x₂,w ∈ Kx` into the three labelled five-edge tree shapes.
  Pairwise disjointness of the finite path witnesses is proved from their vertex
  regions. `I417Example.tree5_le` applies fivefold BK in `ℝ≥0∞`.
* Tonelli and transitivity evaluate the three shapes, yielding
  `I417Example.jointSq_le`:
  `jointSq π x w ≤ χ^3 T2 π x w + 2 χ^2 T3 π x w`, where `χ = meanVol π x`.
* Summing over the marked vertex with the two fresh arms gives
  `I417Example.markSet_le`, whose right side is exactly
  `T3 χ^4 + 2 T4 χ^3`. These are the printed coefficients `1` and `2`.

The earlier auxiliary `I417.excess` retains the redundant `y ∈ Kx` family as a
separate summand in addition to the whole marked family. Consequently
`I417Example.excess_le_two_four` proves only the uniform bound
`2 T3 χ^4 + 4 T4 χ^3` for that larger auxiliary quantity. The printed `(1,2)`
statement is for the true moment difference and for the marked family, not a
claim that the same coefficients have been proved for `I417.excess` itself.

`I417.diagSet_not_base` records the concrete four-vertex obstruction to replacing
the restored cluster by the base cluster inside the diagonal event. This is why
the formal proof keeps the restored configuration rather than silently patching
that event identity.

## General marked two-copy expansion

`I417/General` extends the event expansion from `p = 2, q = 1` to arbitrary finite
`p` and every `1 ≤ q`. With `f : Fin p → V` and `g : Fin q → V`, the product event
is covered by the restored-cluster diagonal together with the marked family over
`j : Fin q` and `w : V` (`I417Gen.prodSet_subset`). The paper's `y ∈ Kx`
alternative is the mark `w = y`, with an empty witness for `y ↔ y`. When
`y ∉ Kx`, failure of one arm to lie in the restored cluster supplies the first-hit
split into two disjoint fresh connections. The fresh arms are retained in the
fresh cluster; no false inclusion `Ky ⊆ K̃y` is used.

The labelled sums give the exact two-copy moment product and excluded moment.
Consequently `I417Gen.twoCopy_moment_le_marked` and
`I417Gen.moment_gap_tsub_le_marked` are unconditional inequalities in `ℝ≥0∞`, with
the general base factor `I417Gen.jointPow π x p w = E[|Kx|^p 1(w ∈ Kx)]` and the
explicit fresh marked factors. `tsum_diagSet` identifies the diagonal term through
law preservation of `restoreMap`, rather than replacing the restored cluster.
`moment_gap_tsub_le_marked_basepoint` supplies the common-basepoint form under
the stated profile-preserving permutations. `prodSet_not_subset_q_zero` records
why the positive-`q` hypothesis is necessary.

For `q = 1`, `twoCopy_moment_le_marked_q_one` and
`moment_gap_tsub_le_marked_q_one` additionally apply BK to bound the fresh factor
by `τ(y,w) ∑_z τ(w,z)` for every `p`. This is a general-`p` event/two-point
reduction, not yet the polygon-diagram estimate in the statement of I.4.17.

## Marked-tree evaluation and the arbitrary-`p`, `q = 1` composition

`I417/Base` supplies the analytic diagram layer needed on the base side. For a
kernel with constant row sum `χ`, `I417Base.tsum_wtE` evaluates every rooted
binary tree diagram, and `I417Base.tsum_wtE_marked` evaluates one with a marked
leaf pinned at `w`. Its value depends only on marked depth:

```text
χ^(2p+1-depth) * pathW k depth x w.
```

`pathW_eq_iterPow` identifies that path with the matrix power `iterPow`, and
`marked_diagram_by_depth` groups a finite diagram family by depth with explicit
natural-number coefficients computed by `Finset.card`. These are analytic
identities, not a construction of the required event-cover family.

`I417Base.q_one_polygon` then composes the marked bound with the fresh factor
`τ(y,w) χ`, raising every matrix power by one. It yields a finite sum over
`2 ≤ ℓ ≤ p+1` for arbitrary `p`. Its remaining `hjoint` is exactly the marked
tree-graph inequality for `I417Gen.jointPow`, with that depth range and with
constant root mean. It is an explicit input, not a new axiom and not derived
from the ordinary full tree expansion. In particular, plain rooted trees can
also produce depth-one marks; this module does not silently prove away that
structural issue.

## Finite-ambient arbitrary-`p` marked atlas and diagram evaluation

`TreeExpansion/AtlasRealization/MarkedAtlas` instantiates the actual atlas realization
and BK union bound with ordinary arms `Fin p` and one distinguished mark. The labels
are distinct, but terminal vertices may coincide. The marked leaf position comes from
that label, not from an arbitrary child. `prob_markedBase_le_shapeSum` bounds the finite
Bernoulli event by labelled shapes and internal-position diagrams, and the finite
coefficient `markCoeff` groups the diagrams by marked depth. `Example` and `TwoLeaf`
classify the small shapes: `prob_markedBase_p0` is an exact two-point identity, and the
`p = 1` evaluations handle the two orderings and their common depth `2`.

Independently, `Correlation/I417/Marked` supplies the label/leaf-position bijection and
`labelledMarkedDiagram_eq_polygon`. This sums ordinary terminal values, pins the marked
terminal at `w`, and evaluates the result by the marked depth. Its coefficients are the
actual finite family cardinalities `markedCount p ℓ`, not an assumed `(2p-1)!!` claim.

`Marked/Numerics` additionally proves the depth coefficients partition the family,
with vanishing coefficients outside the legal depth range. `markedCount_one_two =
2`, `markedCount_one`, and `markedCount_zero` are computed explicitly.
`MarkedJoint/Relabel/Total` uses the new finite label equivalence and exact enumeration to
prove `sum_markedCount_eq_two_pow_mul_dfactorial`: the total is `2^p * (2p-1)!!`,
including its `p = 0` convention. This is a count of the actual labelled plane shapes,
not a coefficient guessed from the finished bound.
`markedPolygonBound_zero` and `labelledMarkedDiagram_zero` are both
`I417Base.iterPow k 1 x w`, with no constant row-sum hypothesis. At `p = 1`,
`labelledMarkedDiagram_one = 2 * (χ ^ 1 * iterPow k 2 x w)`. The small shapes in
`ExampleDefs` reuse the independently checked `MarkedAtlas` orderings and their
distinctness proof rather than introducing another shape-classification shortcut.

`Marked/FiniteSum` supplies the corresponding literal finite sum over shapes,
label assignments with the mark pinned, and internal positions. It does not
assert an `ℝ → ℝ≥0∞` transfer without its valuation, nor a canonical countable
moment bound.

`FiniteMarkedJoin` joins these two presentations for finite edge and vertex types.
`finite_marked_moment_le_polygon_toReal` is its generic finite-kernel formulation;
`finite_marked_moment_le_polygon_of_real` specializes it to finite Bernoulli connection
probabilities cast into `ℝ≥0∞`. It uses bounded weights, `BKIncreasing`, and the explicit
constant row-sum hypothesis expected from transitivity. The proof does not replace
`ENNReal.toReal` of an infinite quantity with a finite moment, nor introduce a finite-box
moment as the canonical cluster moment.

The finite package is unconditionally a finite-model result. The next section records
its genuinely countable canonical counterpart; polygon evaluation and the other open
steps are not inferred from finite-volume results.

## Canonical arbitrary-`p` marked atlas and polygon bounds

`I417/MarkedJoint` now bounds `I417Gen.jointPow π x p w` for **arbitrary countable** `V`,
every `p`, and every opening profile with `π e < 1`. The bound is the sum over fully
labelled `(p+1)`-leaf shapes, internal positions, and terminal tuples whose last physical
value is the mark `w`, of the product of connection probabilities along the atlas edges.
There is no finite vertex or edge assumption, no extra BK premise, and no finite-cluster
or finite-moment substitution.

The label map is `markedExtend w f = Fin.snoc f w`. Its image equivalence
`markedSubtypeEquiv` is exactly the terminal tuples with last value `w`, and
`labelEvent_markedExtend` identifies the arm-plus-mark event without replacing the mark by
an arbitrary terminal. `jointPow_le_markedAtlasBound` applies the canonical covering and
finite-index BK bound, then reindexes the shape, position, and terminal sums.
`jointPow_le_tsum_marked_atlas` gives that same bound in its literal nested-`tsum` form;
`jointPow_zero_eq` checks the no-arm boundary exactly.

`I417/MarkedJoint/Relabel` then identifies the atlas sum exactly with
`labelledMarkedDiagram`. It uses the explicit label equivalence between `Fin (p+1)`
and `Label p = Fin p ⊕ PUnit`, transports internal positions and atlas products along
`RTree.mapLabel`, and reindexes the fully labelled shape family. The last label is sent
to the mark, so the physical pin is unchanged. No `Fintype V` instance or finiteness
of a sum is needed.

Under a constant two-point row sum `χ`, `jointPow_le_markedPolygonBound` consequently
bounds `jointPow π x p w` by `markedPolygonBound χ`, namely the finite depth sum
`markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)`. The exported
`jointPow_le_markedPolygonBound_via_pending` gives the corresponding assembly directly
from `jointPow_le_markedAtlasBound`. Relabelling was recovered from the unsubmitted
`smwwxbtza` candidate and independently rebuilt after reusing the integrated carrier.
This closes the countable marked polygon evaluation, not the full general-`p,q` upper
bound of Lemma I.4.17.

## The positive-`p`, `q = 1` moment-gap bound

`MarkedJoint/Relabel/QOne` proves that a leaf of any tree with at least two leaves has
depth at least two. Consequently `markedCount p 1 = 0` for `1 ≤ p`, and the polygon sum
at positive `p` has the reduced range `Icc 2 (p+1)`. This does not discard the `p = 0`
case: there `markedCount 0 1 = 1`, and no zero-arm extension is inferred here.

For countable `V`, `π e < 1`, and `∀ v, meanVol π v = meanVol π x`,
`moment_gap_q_one_le_of_pos` proves for every `1 ≤ p` that

```text
momentProd π x y p 1 - rawDiff π x y p 1 ≤
  ∑ ℓ ∈ Icc 2 (p+1),
    markedCount p ℓ · (meanVol π x)^(2p+2-ℓ) · T^(ℓ+1)(x,y).
```

The proof supplies the new polygon bound as the `hjoint` input to the existing
`I417Base.q_one_polygon`. After writing `ℓ+1` as the polygon path length, this is the
source's `q = 1` range `3 ≤ pathLength ≤ p+2`, with actual diagram-count coefficients.
These are the canonical plane-labelled counts, not the sharper one-arm branch coefficient:
at `p = 1` this route gives `2 χ² T³`, while `moment_gap_one_one_le` still gives `χ² T³`.
`moment_gap_q_one_le_of_transitive_pos` instead supplies vertex-transitivity through
profile-preserving permutations. `latticeLongRange_moment_gap_q_one_le_of_pos` specializes
it to the canonical power-law law on `ℤ^d`, with no subcriticality or finite-moment premise.
It is a fully assembled positive-`p`, `q = 1` case, not a proof for `q ≥ 2`.

The general mixed-`k` evaluation of I.4.16, fresh factors for `q ≥ 3`, and a uniform
general-`p,q` upper diagram bound remain open.

## Marked depth on a child-swap transversal

`I417/MarkedJoint/Transversal` strengthens the canonical marked bound to one plane
representative per child-swap orbit. `jointPow_le_markedTransversalBound` derives the
inequality directly from the canonical transversal cover, for every `p`, not by dividing
the earlier `ENNReal` bound by a multiplicity. The pin is still the physical value of the
actual terminal `Fin.last p`, and every physical collision and empty diagonal witness is
preserved. The old shape sum is compared exactly by
`markedAtlasBound_eq_two_pow_mul_markedTransversalBound`:
`markedAtlasBound = 2^p * markedTransversalBound`.

`Depth.lean` then proves that every transversal element is fully labelled and reindexes its
terminal labels by the genuine leaf-position bijection. `posSum_pin_eq_leafPos` carries
the *same* marked label to its leaf; `transversal_term_eq` evaluates each diagram by the
marked depth. Therefore `markedTransversalBound_eq_sum_depth` produces finite coefficients
`nonplaneMarkedCount p ℓ`, counted directly on the filtered transversal with no choice of a
child or arbitrary relabelling. At positive `p`, depth one is excluded. At `p = 1`, the
coefficient at depth two is `nonplaneMarkedCount_one_two = 1`, not its plane analogue `2`.

The resulting `jointPow_le_nonplane_markedDepth`, `moment_gap_q_one_le_nonplane`,
`moment_gap_q_one_le_nonplane_of_transitive`, and
`latticeLongRange_moment_gap_q_one_le_nonplane` assemble the positive-`p`, `q = 1` bound
with these non-plane coefficients. They use the same hypotheses as the earlier positive-`p`
assembly, and the power-law specialization has no extra subcriticality or moment-finiteness
premise.

Count normalization is proved directly at **each** depth:
`PerDepth.markedCount_eq_two_pow_mul_nonplaneMarkedCount p ℓ` holds for every `p, ℓ`.
`leafPosMapLabel`, `markPos_mapLabel`, and `depth_markPos_mapLabel` transport the actual
marking leaf and depth under the label equivalence. `exists_leafPosSwap` supplies the same
depth invariance across child swaps, so the native-ℕ decomposition of the depth-filtered
plane family yields exactly `2^p` representatives per filtered orbit. `nonplaneMarkedCount_zero_one`
and the two off-range vanishing lemmas cover the zero-arm and depth boundaries. This is not
inferred from the total identities quoted below.:
`sum_nonplaneMarkedCount = M p`, and
`sum_markedCount = 2^p * sum_nonplaneMarkedCount`.
The older total identities are compatible consequences of this sharper equality.
The full fresh-side general-`q` bound remains open.

## The one-arm marked factor, completed
`I417/Base/MarkedOne` proves `branch_three`, a deterministic decomposition of
any two connections `x ↔ u` and `x ↔ w` at a common branch point into pairwise
edge-disjoint open witnesses. Geodesic splitting and maximally overlapping
supports handle both degenerate and non-degenerate branches. Iterated BK then
proves `jointPow π x 1 w ≤ χ · T²(x,w)` for a constant two-point row sum. This
is the marked base input at `p = 1`, not a false replacement by a single
two-point factor.

`I417/Base/One.moment_gap_one_one_le` inserts it into the general polygon
composition and proves, with the same constant mean assumption and BK alone,
`momentProd − rawDiff ≤ χ² · T³(x,y)`. The one-by-one case of Lemma I.4.17 is
therefore closed in the canonical model. The general positive-`p` case is discharged
separately by `MarkedJoint/Relabel/QOne` above.
The unused draft `twoLeafMarked` index family was deliberately not integrated:
the underlying `RTree.depth` increment convention gives a two-leaf marked path
depth `2`, matching the above bound.

## Fresh-side spine and one-hub reductions

`I417/Fresh` retains the mark and all labelled arms in `freshMark_subset_hubStar`.
The monotone finitely-witnessed hub event is available for later BK expansions.
`freshMark_measure_le_twoArm` keeps the disjoint path halves and proves
`τ(y,w) τ(w,g j)`. `freshMark_measure_le_oneHub` gives a three-arm diagram
`∑_a τ(w,a) τ(a,y) τ(a,g j)` by the existing two-leaf tree-graph inequality.
`fresh_factor_one_le` sums this at `q = 1`, retaining the expected arm inside
`hubArmSum`; `freshCombBound_holds_one` proves the corresponding instance of the
named aggregated diagram condition.

The single-hub shortcut does not generalize to four arms. On the explicit finite
tree with seven edges, the joint event costs `p^7` while the candidate one-hub
diagram is strictly smaller at `p = 1/4` and `p = 1/2` (exact-rational check).
This is a checked counterexample to that shortcut, not a new Lean counterexample
or a refutation of I.4.17. The remaining `FreshCombBound π q` names the explicit
chain/comb inequality still to prove; it is not hidden as an axiom in a complete
fresh-side theorem.

## The two-arm chain bound

`I417/Fresh/Two` proves `freshCombBound_two` and `hubStarChain_two` with only BK.
The hub event is bounded by the existing three-terminal expansion. Summing the
two arms out gives three diagram families `sTerm1`, `sTerm2`, and `sTerm3`.
The second and third coincide after swapping the two summation indices, and at
the single chain point `![u,v,v]` the chain monomial absorbs `sTerm1` and two
copies of the common term. Two copies come from different summands in the
binomial expansion, not from a duplicated union bound. The map from `(u,v)` to
that chain point is injective, so no extra multiplicity is invented.

`twoCopy_moment_le_marked_two`, `moment_gap_tsub_le_marked_two`, and the
real-valued form insert that evaluation into arbitrary-`p` two-copy statements.
Only the base marked moment remains unevaluated there. For `q ≥ 3`, a
`q+1`-terminal tree-graph decomposition is needed; the three-terminal expansion
does not extend merely by repetition. No general-`q` proof is claimed.

## The two-arm fresh polynomial and its exponent gap

`I417FreshTwo.tsum_leafShape_eq_poly` in `Fresh/Two/Poly` evaluates the summed
fresh labelled diagrams exactly as
`χ³ T²(w,y) + 2 χ² T³(w,y)`.
The first term comes from the branch point carrying the y-leg at its first internal
vertex; the second comes from the two swapped placements of the third diagram point.
This is an equality of **diagram sums**, not an assertion that the fresh probability
itself has this exact value. By BK and the existing event bounds,
`tsum_freshMark_le_poly` gives the corresponding inequality for the actual fresh
factor, using only `π e < 1` and a constant two-point row sum.

`moment_gap_two_le_poly` composes the non-plane marked coefficients with that
fresh polynomial, and `moment_gap_two_le_poly_transitive` supplies the transitivity
input through profile-preserving vertex permutations. The resulting bound has the
two families
`2 C(p,ℓ) χ^(2p+4-ℓ) T^(ℓ+2)(x,y)` and
`4 C(p,ℓ) χ^(2p+3-ℓ) T^(ℓ+3)(x,y)`
under `2 ≤ ℓ ≤ p+1`. Its T-powers therefore run from `4` to `p+4`, and every
monomial has `2p+6` factors. This is a genuine unconditional polygon/mean bound
at arbitrary positive `p`, not the paper's exact exponent.

The remaining normalization gap is explicit. The source exponent after q = 2 is
`2p+5-ℓ`, whereas the proved first-family exponent is one larger. Moreover, the
available second family gains one additional path edge. No reduction of the exponent
by cancelling large powers against zero-incidence terms is valid here.

`moment_gap_two_le_poly_fourArm` does give the right source exponent,
`2p+5-(ℓm+2)`, with `2 ≤ ℓm ≤ p+1`. It gives the corresponding range
`4 ≤ ℓm+2 ≤ p+3`, inside the paper's `3 ≤ ℓ ≤ p+3`. **However**, its consistency
check requires the additional fresh hypothesis `hfresh`: the fresh factor must be
bounded by the four-factor single-hub quantity
`fourArmFresh π y w = ∑_a τ(w,a)τ(a,y)χ(a)²`.
This additional hypothesis is not merely unproved:
`Poly/Counterexample.not_fourArmFresh_bound` refutes it on `Fin 3` with two positive
star edges of weight `1/5`. At `y = w = 0`, `freshMark_self_eq_labelEvent` reduces the left
side to `E|K_0|² = 57/25`, whereas the four-arm quantity is
`32547/15625`, strictly smaller. The exact rational calculations and cylinder-measure proofs
are integrated and audited. This is an **inhomogeneous** counterexample to the extra general
hypothesis, not a counterexample to the theorem on transitive weighted graphs, nor a refutation
of I.4.17. The conditional interface remains correct where a source of the additional input
exists, but that interface cannot be discharged generically. A source-faithful fresh expansion
must avoid this exact auxiliary single-hub form. The proved five-factor alternative majorant is
unaffected, and the `q = 2` source exponent remains an open part of I.4.17. `fourArmFresh_eq` merely evaluates that quantity; it does not provide a fresh event bound.

## The fresh hub star is a canonical marked terminal event

`I417/Fresh/HubStar.hubStar_eq_labelEvent_markedExtend` proves the exact set identity
between `hubStar y w g` and the canonical terminal event rooted at `w`, with arms `g` and
marked terminal `y`. In particular the fresh root and mark are kept in the right roles, and
no finite approximation to the restored cluster is involved.
`tsum_hubStar_eq_jointPow` then gives the exact identification
`∑'_g P(hubStar y w g) = I417Gen.jointPow π w q y`.

Consequently the non-plane marked-depth evaluation applies to the hub star.
`tsum_hubStar_le_nonplane_markedDepth` and
`tsum_freshMark_le_nonplane_markedDepth` bound their respective sums by the finite
non-plane polynomial with root `w` and distinguished endpoint `y`, for `q ≥ 1` and a
constant two-point row sum. The second statement uses the existing *containment*
`freshMark ⊆ hubStar`; it does not equate the fresh event with the hub star or with the old
base cluster. It provides a larger-event upper bound, not the explicit chain-cover or
full polygon assembly required for the final general-`p,q` theorem. Those remaining
composition and coefficient steps are not hidden in this identity.

## The fixed chain-witness cover fails at `q = 3`

`I417/Fresh/Obstruction` proves `ds_no_chainSpider`: on the six-edge double star
`0–1–{3,4}` and `0–2–{5,6}`, for every spine vector `u : Fin 4 → Fin 7` and
every injective terminal assignment into `{3,4,5,6}`, the four spine connections
and four leg connections have no pairwise edge-disjoint witnesses. Here `3,4,5`
are the three labelled arms and `6` is the mark-connected terminal. The companion
`ds_hubEvent` proves that all four arms are connected in that same configuration.

Each separated double-star cut forces its unique edge into a connection witness.
Pairwise disjointness therefore makes each of the six cuts serve at most one of
the eight requirements. The finite proof `chainSepX_ge_seven` checks all
`7^4 · 4!` spine/terminal assignments and gives a separation count at least seven.
This contradiction rules out the fixed configurationwise cover that would
justify a chain monomial directly by BK. It does **not** prove or refute
`FreshCombBound π 3`, exclude other upper-bound arguments, or change the status
of Lemma I.4.17. The finite case analysis uses ordinary `decide`, not
`native_decide`; `ds_no_chainSpider` has only the standard axioms.

## Fork witnesses and the chain slack

`I417/Fresh/Fork` supplies a genuine two-hub alternative to the failed
configurationwise chain cover. `Q3.forkEvent` asks for six pairwise
edge-disjoint connection witnesses: one spine from the mark `w` to each of two
hubs, and two arms from each hub. `forkEvent_measure_le` bounds its probability
by the corresponding six two-point factors. `fresh_fork_three_le` sums the three
arm labels explicitly and retains the fourth connection to `y`; it gives
`τ(w,a) χ(a)² τ(w,b) χ(b) τ(b,y)`. `fresh_fork_le_forkBound` absorbs this term in
the explicit sum over both hub positions.

This family is non-vacuous exactly where the proposed chain cover fails:
`ds_forkEvent` constructs six distinct single-edge witnesses on the production
double-star configuration. `q3_doubleStar_fork_not_chain` combines this with
`ds_hubEvent` and `ds_no_chainSpider`. This does **not** show that fork events,
or fork plus chain events, cover all fresh configurations. It does not complete
the `q = 3` theorem.

`Fork/Slack` also proves the constant-spine evaluation
`chainTerm_const`, hence
`tau π w a * (hubArmSum π a + tau π a y)^(q+1)`, and embeds its average over
`a` into `freshChainBound` by injectivity of the constant-spine map. Thus
`freshCombBound_of_hubMoment` and its `q = 3` specialization reduce the full
fresh bound to the remaining hub-moment inequality. That hub-moment inequality
is still an explicit, unproved hypothesis. No counterexample to the source's
full upper bound is asserted from the fixed-chain obstruction.

## The fork obstruction and the spine–hub event

`I417/Fresh/Q3Cover` adds the independently rebuilt `smwx5p94b/m3` component.
It does not settle the proposed chain-plus-fork cover or the `q = 3` fresh
bound.

* The five-edge **fan** has mark `0`, hub `1`, fresh arms `2,3,4`, and marked
  arm `5`, with edges `0–1`, `0–5`, `1–2`, `1–3`, and `1–4`.
  `fan_hubEvent` proves its `hubStar` condition; this is the hub-star
  qualification, not a separately checked `freshMark` statement.
  `fan_not_forkEvent` proves that for every pair of hubs the production fork
  event with fixed ordering `![2,3]` and `![4,5]` has no pairwise-disjoint
  witnesses there. The proof uses five cuts: at most one requirement can use
  each cut under disjointness, while `fanSep_ge_six` computes total separation
  at least six. This is the precise fixed-order obstruction, not a theorem
  about every possible permutation of the four terminals.
* `spineHubEvent` is a new five-requirement disjoint-occurrence event for
  `w ↔ a`, `w ↔ y`, and `a ↔ g i` for all three fresh arms.
  `spineHubEvent_measure_le` is its five-fold BK bound and
  `fresh_spineHub_le` sums the three arms to
  `τ(w,a) τ(w,y) χ(a)³`. `fresh_spineHub_le_bound` absorbs this into the
  hub-summed diagram. These bounds concern the newly defined event; no general
  inclusion of `freshMark` or `hubStar` in a spine–hub event is asserted.
* `fan_spineHubEvent` gives explicit five-edge witnesses on the fan and
  `fan_spineHub_vs_fork` packages that concrete comparison. Fork and spine–hub
  therefore add genuinely different finite examples, but neither supplies the
  missing general fresh cover or its evaluation.

A bounded Python experiment accompanying the submission explored this class of
finite trees; it is not a Lean coverage proof and has not been incorporated into
any theorem or assumed in a production declaration.

## Audits and remaining work

`I417/Nonnegative/Audit.lean`, `I417/Audit.lean`, and `I417Example/Audit.lean`
contain the older focused `#print axioms` declarations. The canonical lattice
theorem is included in the last audit. The new general modules were also rebuilt
with the strict warning settings and all exported declarations passed the global
axiom audit.

`I417/MarkedJoint` supplies the arbitrary-`p` canonical marked atlas/BK bound.
Still open are the fresh tree expansion for `q ≥ 3` and the evaluation as a finite sum of
`C_{p,q,ℓ} T^ℓ(x,y)(E|K|)^(2p+2q+1−ℓ)` with universal integer constants. The full
upper diagram bound in Lemma I.4.17 is not proved.
