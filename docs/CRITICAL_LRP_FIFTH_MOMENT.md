# Fifth-moment interface

`Correlation/SixPoint/FullMoment.lean` proves the exact native expansion

```text
∫⁻ ω, cardFun(cluster ω x)^5 ∂law π
  = ∑' y z w q r, law π (conn x y ∩ conn x z ∩ conn x w ∩ conn x q ∩ conn x r).
```

This is proved by expanding |Kᵥ| as a sum of connection indicators, applying
Tonelli, and multiplying five indicator functions. It requires only a
countable carrier; the reused fourfold sum algebra carries the same abelian
group instances as the other native moment packages. All values remain in
`ℝ≥0∞`, so no moment-finiteness or local-finiteness premise is introduced.

The companion `tsum_five_mul_with` factors a product of five extended sums
with a constant final factor. These are the exact left-hand-side and summation
interfaces needed for a higher mixed tree-moment proof.

Before the attachment package described below, this file established only the
moment-expansion and diagram-evaluation interfaces, not the `p=5,k=1` source inequality.

`MomentAssembly.lean` makes the older abstract analytic consumer precise: if `D`
supplies a valid bound for each five-point event and each of its 105 diagrams has
the full terminal sum `secondMoment π 0 * (firstMoment π 0)^6`, then
`fifth_moment_le_of_105diagrams` derives the desired bound. These remain explicit
hypotheses of that helper. The concrete proof is in the attachment package below.

## Completed `p = 5`, `k = 1` attachment package

`Attachment/Assembly.lean` proves `SixPoint.fifth_moment_le`:

```text
∫⁻ ω, cardFun(cluster ω 0)^5 ∂law π
  ≤ 105 * (∫⁻ ω, cardFun(cluster ω 0)^2 ∂law π) *
      (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^6
```

on a countable abelian group with full profile invariance `hq`, without any
finite-moment or additional event-cover premise.
`PowerLawTreeMoments.latticeLongRange_fifth_moment_mixed_le` is the corresponding
unconditional theorem for the canonical `latticeLongRangeMeasure`.

The proof has these concrete parts:
* `Attachment/Cover.lean` supplies the deterministic `Fin 15 × Fin 7` cover by
  adding a sixth terminal to one of seven arms of each five-terminal pattern.
* `Attachment/Split.lean` produces nine edge-disjoint walks by splitting the arm
  at the attachment point. `Attachment/Main.lean` bounds the corresponding
  fourteen slot families by one joint pair and six singleton two-point factors.
* `Attachment/Final.lean` evaluates each remaining diagram to the native second
  moment times `(∑' x, tau π 0 x)^6`. Adjacent `ENNReal.tsum_comm` exchanges avoid
  the earlier expensive concrete-permutation unification, with no change to the
  statements or heartbeat budget.
* `Attachment/Assembly.lean` keeps internal vertices inside the union bounds,
  reindexes the pair `k,j` productwise, and uses the exact
  `tsum_fin15_fin7_const` count only at the coefficient step.

No ordinary `χ^9` replacement of the retained **mixed** joint pair, finite-window
substitute, or general-`p` claim is involved.

## Completed ordinary `p = 5`, `k = 0` bound

`Correlation/SixPoint/Ordinary/Assembly.lean` also proves
`SixPoint.fifth_moment_ordinary_le`:

```text
∫⁻ ω, cardFun(cluster ω 0)^5 ∂law π
  ≤ 105 * (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^9.
```

It is not deduced from the mixed bound. The nine split walks supply nine
independent finite certificates for `countable_profile_bk`; `Ordinary/NineFold`
makes that BK step explicit. `Ordinary/NineShape` proves every per-shape event
bound while retaining all four internal sums, and `NineBridge` identifies that
event diagram with `ordD`. `Ordinary/Eval` and `Main` evaluate all fourteen slot
families and all fifteen leaf patterns to `χ^9`, with no finiteness assumption.
Finally `NineIntegration` and `Consumer` assemble the native fifth-moment and
canonical results, using `tsum_fin15_fin7_const` for the exact 105 coefficient.
The canonical theorem is `latticeLongRange_fifth_moment_ordinary_le_uncond`.
`SixPoint/Cases.lean` packages both cases as `fifth_moment_all_k_le`, for every
natural `k ≤ 1`, and as `latticeLongRange_fifth_moment_all_k_le` at the canonical
law. These two cases cover `k = 0,1`; the `k = 2` case is discussed separately
below, and general `p` remains an independent open problem.

## Conditional two-hub evaluation for `p = 5`, `k = 2`

`Correlation/SixPoint/MixedK2` supplies the analytic fan and chain diagrams for
the remaining admissible case at `p = 5`. Under full profile translation
invariance, `HubK2.tsum_hubStar` and `HubK2.tsum_hubChain` evaluate the five free
leaf sums and both hub sums exactly to

```text
(secondMoment π o)^2 * (∑' x, tau π o x)^3.
```

`HubK2.tsum_slotK2_five` and `HubK2.tsum_slotChain_five` prove the corresponding
identities for every leaf permutation. `HubK2.fifth_moment_mixed_k2_le_of_hubBound`
and `HubK2.fifth_moment_mixed_k2_le_of_chainBound` therefore derive the native
inequality

```text
∫⁻ ω, cardFun(cluster ω 0)^5 ∂law π
  ≤ 105 * (∫⁻ ω, cardFun(cluster ω 0)^2 ∂law π)^2 *
      (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^3
```

from their explicitly displayed pointwise bound by 105 fan or chain diagrams.
That event-cover premise `hpoint` is **not discharged**. The fan/chain evaluation
is exact and does not use moment finiteness, but these theorems must not be cited
as unconditional proofs of the `p = 5,k = 2` case.

Moreover, the fan/chain pointwise-cover route has now been refuted. On
nearest-neighbour percolation on `ℤ`, at root `0` and leaves `1,2,3,4,5`, the
left side is exactly `p^5`. Every chain summand has exponent at least `6`
(every fan summand at least `7` in the exhaustive exact-integer check), while
hub-distance bounds give only polynomially many hub pairs at each excess degree.
The complete chain RHS is therefore `O(p^6)`, even if all 120 rather than 105
leaf permutations are included, and is smaller than `p^5` for sufficiently small
`p`. The analytic route was translated into five-group certificates in
`.ultramath/smwvlmbqa/m5/ChainGroup`; this counterexample was checked separately
by exact computation and the path-connectedness argument, not formalized as a
new Lean counterexample. It rules out **these particular diagrams**, not the
lemma or every alternative event cover. Future work must use the genuine
same-parity three-star regrouping/summed argument, not another labelling search
over the same fan or chain family.

### Root-in-pair evaluation and its remaining cover

`Correlation/SixPoint/RootPair` implements the repaired shape suggested by the
paper's `p = 3` example: the root is included in the first joint pair. Its
integrand is `(jointP o a c1 * tau b c1) * (jointP d e c2 * tau c1 c2) * tau f c2`.
`HubRoot.tsum_slotChainRoot_five` proves the exact evaluation
`(secondMoment π o)^2 * (∑' x, tau π o x)^3` under full profile invariance.
The root-carrying pair is evaluated by summing its centre and applying
`SixPoint.tsum_jointP_centre'`; it is not treated as locally constant.

`HubRoot.fifth_moment_mixed_k2_le_of_chainRootBound` derives the desired fifth
moment inequality from the corrected pointwise-cover premise. **That premise is
still entirely open.** The `Obstruction` inequalities and the exact cost-five
example show that the new shape removes the local arm-cost mismatch, not that a
deterministic event/BK cover exists. This module makes no unconditional
`p = 5,k = 2` or general-`p` claim.

There is also a finite, nontransitive counterexample to relabelling this one chain
shape as a universal combinatorial cover. `RootPairObstruction.chainCost_ge_six`
proves that on the five-edge tree with centre `0` and legs `0-1-2`, `0-3-4`, `0-5`,
every one of the `120` labellings and every one of the `36` hub pairs has total
connector cost at least `6`. The explicit evaluation with both hubs at the centre
attains `6`. This does **not** prove that `HubRoot.hpoint` fails for the transitive
lattice law and formalizes no percolation law or BK identity. It demonstrates only
that a fixed permutation family of this single shape is not a universal cover.
The genuine next target is the shape-indexed Atlas realization, not another
labelling search.

## A verified fork shape and BK kit

`Correlation/SixPoint/Fork` also supplies a native sevenfold BK kit and one
non-vacuous fork-shape theorem. The nine-arm realization covers the root and a
cherry partner at one branch, a lower chain of hubs, four other leaves, and an
additional leaf attached at the pair centre. Seven pairwise-disjoint open
certificates are regrouped into one joint pair and six two-point arms. The pair
is retained through BK and evaluated by `tsum_jointP_centre` rather than split
into two `tau` terms. Hence its diagram sum is `secondMoment π 0 * χ^6` with
`χ = ∑' x, tau π 0 x` under full profile invariance, exactly as needed by
`p=5,k=1`. The `ForkEvent` and its diagram are definitionally compatible, and
`fork_shape_bound` proves their full-leaf-sum inequality with standard axioms.

The fork alone does not supply the remaining 104 shape instantiations or the
uniform deterministic 105-cover; the attachment package above supplies those
separately. `fifth_moment_of_cover` and `fifth_moment_le_of_105diagrams` retain
their abstraction hypotheses and are not rebranded as unconditional theorems.
The completed concrete result is `SixPoint.fifth_moment_le`, in
`Correlation/SixPoint/Attachment/Assembly.lean`.
