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

`FiniteMarkedJoin` joins these two presentations for finite edge and vertex types.
`finite_marked_moment_le_polygon_toReal` is its generic finite-kernel formulation;
`finite_marked_moment_le_polygon_of_real` specializes it to finite Bernoulli connection
probabilities cast into `ℝ≥0∞`. It uses bounded weights, `BKIncreasing`, and the explicit
constant row-sum hypothesis expected from transitivity. The proof does not replace
`ENNReal.toReal` of an infinite quantity with a finite moment, nor introduce a finite-box
moment as the canonical cluster moment.

The countable canonical instantiation of `I417Gen.jointPow`, the general mixed-`k`
evaluation of I.4.16, fresh factors for `q ≥ 3`, and a uniform general-`p,q` upper diagram
bound remain open. The finite package is not a replacement for those steps.

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
therefore closed in the canonical model; the general-`p` `hjoint` remains open.
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

## Audits and remaining work

`I417/Nonnegative/Audit.lean`, `I417/Audit.lean`, and `I417Example/Audit.lean`
contain the older focused `#print axioms` declarations. The canonical lattice
theorem is included in the last audit. The new general modules were also rebuilt
with the strict warning settings and all exported declarations passed the global
axiom audit.

Still open are the rooted-tree bound on `I417Gen.jointPow`, the fresh tree
expansion for `q ≥ 3`, and the evaluation as a finite sum of
`C_{p,q,ℓ} T^ℓ(x,y)(E|K|)^(2p+2q+1−ℓ)` with universal integer constants. The full
upper diagram bound in Lemma I.4.17 is not proved.
