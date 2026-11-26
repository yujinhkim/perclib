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
exists, but that interface cannot be discharged generically. The proved five-factor alternative
majorant remains valid, but is not the source-normalized refinement. `fourArmFresh_eq` merely
evaluates that quantity; it does not provide a fresh event bound. The following independently
rebuilt refinement now supplies the missing source argument instead.

## The refined two-arm mark-on-path expansion

`I417FreshTwo.Refined` closes the `q = 2` normalization gap in the transitive setting.
Unlike the hub-star proxy, it uses the actual disjoint occurrence inside `freshMark` of
`y ↔ w` and `w ↔ g j`.

`exists_refined_branch` reduces the path witnesses to paths and first-hits the walk
from the other labelled arm against the union of the two disjoint halves. If the
first hit is in the `y → w` half, splitting there gives `ShapeA`

  `{y↔p} ∘ {p↔w} ∘ {w↔g j} ∘ {p↔g j'}`.

If it is in the `w → g j` half, splitting there gives `ShapeB`

  `{y↔w} ∘ {w↔p} ∘ {p↔g j} ∘ {p↔g j'}`.

Every witness is retained and all four pairs of witnesses are proved
edge-disjoint. The proof handles both values of `j : Fin 2` and does not require
distinct physical positions.

The fourfold BK bound and the two arm sums yield
`χ² T²(w,y)` from shape A and `χ³ T(w,y)` from shape B, with four two-point
factors in each term. In particular the `w = y` diagonal is not hidden by the
refuted single-hub shortcut. `tsum_freshMark_le_refined` needs only BK and a
constant mean-volume row sum; no finite moment or subcriticality is assumed.

`moment_gap_two_le_refined` composes this with the non-plane marked-depth bound.
For every `p ≥ 1`, the two coefficient families have
`2 * nonplaneMarkedCount(p,ℓ)`, `2 ≤ ℓ ≤ p+1`, and respective monomials
`χ^(2p+3-ℓ) T^(ℓ+2)(x,y)` and `χ^(2p+4-ℓ) T^(ℓ+1)(x,y)`.
Every monomial has `2p+5` two-point factors and its path power lies in
`[3,p+3]`, as required by Lemma I.4.17 at `q = 2`. The result is the usual
`ℝ≥0∞` subtractive moment-gap form. `moment_gap_two_le_refined_transitive`
discharges the row-sum hypothesis for a vertex-transitive profile, and
`latticeLongRange_moment_gap_two_le_refined` specializes it to the canonical
power-law law on `ℤ^d`.

This closes the abstract transitive and canonical-law `q = 2` form. It does not
solve fresh factors for `q ≥ 3`, general mixed-`k` moments, or a further
real-valued conversion not stated by this module. The older two-copy upper
majorants and the inhomogeneous counterexample are retained for provenance and
must not be confused with these proved normalized bounds.

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

## The three-arm mark-on-path expansion

`I417FreshThree.Refined`, from the independently reviewed completed
`smwx6p0op/m1` artifact, closes the **normalized `q = 3` case**. Its cover does
not use the incomplete fixed chain-spider, fork, or single-hub families.

`freshMark_subset_shapeQ3` retains the two edge-disjoint halves of the selected
`y → w → g j` path. It first-hits one other arm against their union, splits the
hit segment, then first-hits the third arm against the augmented union and
splits whichever of the four resulting segments it meets. The generic
`shapeOf_split` lemma preserves every edge-disjointness premise. This gives
exactly eight six-leg subdivided binary-tree families, including hits on the
auxiliary arm and all coincident positions and label choices. No branch point
or arm is discarded by a non-degeneracy assumption.

With `j` the selected arm and the other two labels summed independently,
sixfold BK and the three-arm row-sum evaluation give

  `∑_g P(freshMark y g j w) ≤
    2 χ³ T³(w,y) + 3 χ⁴ T²(w,y) + 3 χ⁵ T(w,y)`.

Two depth-three shapes, three depth-two shapes and three depth-one shapes
explain the coefficients; all three arms are retained and every monomial has
six fresh two-point factors. `moment_gap_three_le_refined` composes this with
the non-plane marked-depth bound and the three selected-arm labels. For every
`p ≥ 1`, its three coefficient families (inside the outer factor `3`) have
factors `2, 3, 3` times `nonplaneMarkedCount(p,ℓ)` and respective monomials
`χ^(2p+4-ℓ) T^(ℓ+3)`, `χ^(2p+5-ℓ) T^(ℓ+2)`, and
`χ^(2p+6-ℓ) T^(ℓ+1)`. Their factor count is exactly `2p+7` and their path
powers lie inside the printed range `[3,p+4]`.

Only BK and a constant mean-volume row sum are required, not moment finiteness.
`moment_gap_three_le_refined_transitive` supplies the usual vertex-transitivity
input, and `latticeLongRange_moment_gap_three_le_refined` instantiates the
canonical power-law law on `ℤ^d`. These are the same `ℝ≥0∞` subtractive
moment-gap bounds as the rest of the development; a separate real-valued
conversion is not restated, and **general `q ≥ 4` is still open**.

## The four-arm first-hit cover and BK bound

`I417FreshFour.Refined` proves the next **event-level** step, not yet the full
`q = 4` moment inequality. Its bounded `Diag` structure records any finite
index family of legs with open path witnesses that are pairwise edge-disjoint.

The reusable `Diag`/`step` attachment theorem splits a leg at a point of its
support, keeps both path halves, and attaches the new first-hit arm. It shows
that all pairwise disjointness constraints are preserved and takes indices
from `ι` to `ι ⊕ Bool`, hence from `2q` to `2q+2` legs. `splitAt_left` retains
the pin `y`, allowing the next first hit.

`freshMark_subset_q4Shape` starts from the actual disjoint halves of the
selected fresh path and applies this step three times. It gives
`freshMark ⊆ q4Shape` for every selected arm `j : Fin 4` and every ordering of
the other three labels. There are no distinctness assumptions, and every
coinciding attachment or arm is retained. The 48 choices of splits and the
three summed attachment positions yield eight legs on each diagram.
`freshMark_measure_le_q4` combines that cover with finite-type BK, reindexed by
`Fintype.equivFin`, to bound every fresh probability by the sum of the eight
two-point factors over those 48 diagram families.

The remaining `FreshFourEval` proposition is the weighted evaluation: sum the
arms and attachment positions to the source Fresh polynomial with eight
factors, then compose it with the marked depth bound. The independent family
checker predicts `6χ⁴T⁴+12χ⁵T³+15χ⁶T²+15χ⁷T`, with total count 2q=8 and
upper endpoint `T⁴`; this separates the verified event cover from the still
missing sum. The factor-count computation alone did not prove the required sum, but the
subsequent 48 branch evaluations complete it. Each `ev_i` proves the exact
weighted value of one branch. The completed aggregation uses every `ev_i`
fully instantiated by `π`, `y`, `w`, `χ`, and the constant-row-sum hypothesis
`hχ`, so no unification shortcut changes the data. The resulting
`tsum_q4_le_profile` and `tsum_freshMark_le_profile` prove
`6χ⁴T⁴+12χ⁵T³+15χ⁶T²+15χ⁷T` for the actual four-arm fresh factor.
`freshFourEval_holds` closes the old named `FreshFourEval` premise.

`moment_gap_four_le_eval` then composes this with the non-plane marked-depth
bound. Every positive `p` has total factor count `2p+9`, with the expected
$T$-powers in `[3,p+5]`. `moment_gap_four_le_eval_transitive` supplies the
vertex-transitive case, and `latticeLongRange_moment_gap_four_le_eval`
specializes the result to the canonical power-law law. The local audit
prints every `ev_i` as well as these moment bounds, all with the standard three
axioms. This closes the normalized `q = 4` cases; the general-`q` weighted
expansion and the remaining cases `q ≥ 5` were still open at that stage.

## The finite `q = 5` fresh evaluation

`Fresh/Five`, from independently rebuilt `smwxb4a1l/m1`, now proves four
first-hit attachment rounds directly: `round_q5` retains the selected-arm
path halves and `exists_diag_q5` gives a genuine ten-leg witnessed diagram.
It gives the resulting 384-branch cover and finite BK bound, together with
`tsum_freshMark_le_profile_five` and `freshFiveEval_holds` for
`24χ⁵T⁵ + 60χ⁶T⁴ + 90χ⁷T³ + 105χ⁸T² + 105χ⁹T`.
All five labelled arms are retained. The summation sends the arm endpoints
inside the attachment-vertex sum before peeling off-path vertices; each
remaining path contributes `T^ℓ` for `ℓ ∈ {1,2,3,4,5}`. A separate
increasing-tree check independently confirms the coefficient row
`105,105,90,60,24` by depth. Every branch lemma is explicitly applied in the
aggregation. `Fresh/Five/Moment` now gives the normalized positive-`p`
bound `moment_gap_five_le_eval`, with total factor count `2p+11` and path
powers in `[3,p+6]`, plus the transitive and canonical-law specializations
`moment_gap_five_le_eval_transitive` and
`latticeLongRange_moment_gap_five_le_eval`. The coefficient is kept as the
sum of the five fibre contributions `5 * nonplaneMarkedCount p ℓ` times
`(24,60,90,105,105)`, rather than reindexed into one closed-form per-depth
constant. This closes the normalized `q = 5` specialization, not
`GenFreshEval` in general.

## Analytic spine evaluation, and the remaining geometric bridge

`Fresh/Spine`, independently rebuilt from `smwxcafk7/m1`, provides the
order-free analytic core. `Hang.val_eq_pow` proves that a rooted hanging
forest with `m` vertices contributes `χ^m` for every base vertex.
`spineVal_eq_normal` evaluates a chain with hanging-forest total size
`2q-ℓ` as `χ^(2q-ℓ) T^ℓ`; `spineVal_eq_kernel` gives the symmetric-kernel
normalization, and `spine_aggregate_genFreshProfile` applies the accepted
`genCoeff` coefficients. `genFreshProfile_four` and `genFreshProfile_five`
identify the generic profile with the accepted finite fresh profiles.

This is **not** an identification of `I417GenIter.Hist.legs` with these spine
diagrams. An explicit transport of actual `Hist.legs` and its attachment and
arm sums to `spineVal` is still required. A fixed attachment-time ordering
is not a legal peel order in every case, and `subW` alone does not describe
all split-below-`w` histories. This generic infrastructure does not solve the
general weighted `GenFreshEval` but reduces the missing work to honest
combinatorial reindexing and a geometric bridge.

## The general-`q` iterated first-hit cover

`I417GenIter`, from the accepted `smwx9itnu/m2` development, constructs the
fresh diagram family for arbitrary `q ≥ 2`, reusing the $q=4$ `Diag`/`splitAt`
interface rather than defining a second incompatible model.

* `Idx 0 = Fin 2` (the two actual selected-path halves), and each attachment
  changes `Idx n` to `Idx n ⊕ Bool`. `card_Idx` gives cardinality $2(n+1)$;
  consequently `card_genLegs` at `q-1` attachments gives exactly $2q$ legs.
* `Hist V n` stores a split index, a first-hit vertex and an attached arm for
  each attachment, so no label/order data is made up. `Hist.legs` evaluates the
  history to a diagram and `Hist.arm` records the attached arms explicitly;
  `genShape` unions those diagrams subject to a chosen enumeration `e` of the
  non-selected labels. `exists_armEnum` supplies this enumeration by a cardinal
  argument.
* `exists_iter_diag` is the induction. From the actual disjoint halves, it does
  one first hit against the *whole current diagram* at each stage, splits the
  contained path, attaches precisely the next non-selected arm, and preserves
  all pairwise edge-disjoint path witnesses. `Hist.first_leg_start` keeps the
  pin `y` available for each later first hit, including all degenerate choices.
* `freshMark_subset_genShape` consequently proves the genuine arbitrary-$q$
  cover at the actual `freshMark` event. `shapeOfI_measure_le` provides
  finite-type BK after `Fintype.equivFin`, and `freshMark_measure_le_genShape`
  bounds the actual fresh probability by the sum of the `2q`-leg products.
  `tsum_freshMark_le_genShape` sums over all arm tuples under a fixed honest
  enumeration, instead of inventing a permutation factor.
* `card_histChoices` gives the finite product of split-index cardinalities,
  with checks $48$ at $q=4$ and $384$ at $q=5$.
  `card_histChoices` corresponds to $2^n n!$ for $n=q-1$ attachments, not to a
  hidden empty coefficient assignment. The independent family script confirms
  every member through $q=5$ has $2q$ legs, tree structure and all arm leaves.

The remaining `GenFreshEval` is the attachment/arm-sum substitution: evaluating
these products as finite coefficient-weighted
$C_\ell \chi^{2q-\ell} T^\ell$ with $1\leq\ell\leq q$.
`freshMark_measure_le_poly` and `freshMark_measure_le_freshPoly` are explicitly
conditional on that named input; they do not prove general weighted moments.
The separate generalized subdivision package supplies finite diagram consumers,
but the general-`q` mark-on-path moment theorem still needs this evaluation
and its outer marked-$p$ composition.

## Verified branch cardinalities at arbitrary `q`

`I417FreshDepth` defines `splitChoices`, `pathLegsK`, and `markDepthK` for the
actual first-hit histories. The depth successor adds one precisely when a path
leg is split. At `q-1` attachments this yields the source monomial range
`χ^(2q-ℓ) T^ℓ` with `1 ≤ ℓ ≤ q` and total count `2q`.

`genCoeff q ℓ` is an explicit finite cardinality of split branches of depth
`ℓ`, not an abstract coefficient without a family. Ordinary `decide`
computations give `(1)`, `(1,1)`, `(3,3,2)`, `(15,15,12,6)`, and
`(105,105,90,60,24)` at `q = 1, ..., 5`, with totals `1, 2, 8, 48, 384`.
The `q = 4` row matches `I417FreshFour.Eval`, and
`genFreshProfile_eq_freshPoly` is the exact `Subdivision.freshPoly` definition
with these coefficients.

This is only combinatorial support for weighted evaluation. Finer endpoint
statements (`legs_wSlot` and the path geometry) are not supplied by these
modules. Hanging subtrees must also be summed before the constant row sum can
collapse to powers of `χ`, including splits below `w`, so the plain `subW`
family cannot simply replace the whole leg-history family. `GenFreshEval` and
its full moment composition remain open despite the verified coefficient
counts.


`I417FreshDepth` adds the finite combinatorial counterpart of `I417GenIter`'s
attachment histories. `splitChoices` forgets attachment vertices and arms but
keeps the actual leg indices, and `pathLegsK`/`markDepthK` propagate the
pin--mark path count. `markDepthK_succ` proves that it increases by exactly one
when a path leg is split, and bounds its value by the attachment count plus
one. At `q-1` attachments this yields the monomial range
`χ^(2q-ℓ) T^ℓ` with `1 ≤ ℓ ≤ q` and exponents summing to `2q`.

`genCoeff q ℓ = depthCount (q-1) ℓ` is an explicit `Fintype.card` of the split
branches of length `ℓ`, not a raw global coefficient chosen in the abstract.
The ordinary-kernel-`decide` computations give rows `(1)`, `(1,1)`,
`(3,3,2)`, `(15,15,12,6)`, `(105,105,90,60,24)` at `q = 1, ..., 5`, with
coefficient totals `1, 2, 8, 48, 384`. The `q = 4` row is the verified
coefficient profile of `I417FreshFour.Eval`, and the `q = 5` row matches the
branch-evaluation program. `genFreshProfile_eq_freshPoly` identifies this
definition exactly with `Subdivision.freshPoly` using those coefficients.

This is still **not** a proof of `GenFreshEval`. The artifact's narrative gaps
remain: finer endpoint/linking statements (`legs_wSlot` and related path
geometry) must be proved, and pendent subtrees must be summed before the
constant row sum reduces them to powers of `χ`. Splits below `w` mean the plain
`subW` family cannot be applied directly to the unrestricted leg histories.
Both are prerequisites for a general weighted branch evaluation, which is an
independent remaining obligation, not inferred from coefficient counts alone.


`I417/Fresh/Subdivision` (the independently rebuilt accepted `smwx6p0op/m2`
package) supplies the general-`q` diagram and depth machinery that an actual
fresh-tree cover must feed. It is not a fresh-event cover theorem.

* `subW k t q ℓ v w` is the weight after subdividing the edge above the chosen
  arm leaf `q` and pinning its subdivision point at `w`. The mark is therefore
  a vertex on the fresh selected-arm path rather than a new labelled leaf.
  `subW_eq` proves the shape-independent value
  `χ^(2*numLeaves t - ℓ) * iterPow k ℓ v w` for every admissible depth, using
  only a constant row sum.
* `fresh_family_by_depth` groups a finite family exactly into
  `C_ℓ χ^(2q-ℓ) T^ℓ`, with `C_ℓ` a cardinality and `1 ≤ ℓ ≤ q`.
  `comb_subW_max` attains `χ^q T^q` for every positive arm count, so this upper
  depth endpoint is present. Two- and three-leaf instances are checked,
  including the same two monomials as the accepted `q = 2` path cover.
* `base_marked_depth_range` uses the proved non-plane coefficient vanishings
  to derive nonzero marked depths in `[2,p+1]`. `source_path_range` and
  `source_edge_count` derive the composed bounds `3 ≤ ℓ ≤ p+q+1` and total
  `2p+2q+1` edges. `composed_family_le` groups the corresponding finite
  composed diagram family with explicit cardinal coefficients.
* `tsum_marked_fresh_eq` sums a marked base diagram and a subdivided fresh
  diagram over the mark **using the polygon identity**. It is an equality
  yielding exactly `χ^(2p+2q+1-ℓ) T^ℓ(x,y)`, not a per-position upper bound
  that cannot be summed. `tsum_marked_fresh_eq_two` reproduces the two
  accepted `q = 2` monomials after the same mark summation.

What remains is the configuration-level cover of `freshMark` by a finite
family of such diagrams, followed by its union/BK estimate and interchange of
summation over mark positions and family members. The finite diagram
identities above supply the evaluation only after those inputs; they must not
be read as a proof of Lemma I.4.17 at general `q` or of mixed-moment bounds.

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
