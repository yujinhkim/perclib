# Supporting atlas, recursion and covariance results

These are independently rebuilt and independently accepted supporting lemmas from
`smwziumdb`. They do not supply the q-zero printed two-term estimate, the
canonical-model requirements of Proposition I.4.20, or a general completion of
I.4.15. For Case 3 use the proved direct consumer in
[CRITICAL_LRP_PRODUCT_GAP.md](CRITICAL_LRP_PRODUCT_GAP.md).

## Shape evaluations and kernel-power identification

`QZeroAtlas/Main.lean` now proves the four previously hypothesized shape
bounds. `atlas_le_nohyp` and `starMoment_le_three_term_nohyp` discharge those
evaluations, while **retaining the actual `hatlas` tree-realization premise**.
`QZeroAtlas.kpow_eq_Kpow` identifies the atlas's left-nested power with
`KernelPower.Kpow`, by induction on the number of steps without a kernel
symmetry assumption. Equality forms under constant row mass show the generic
shape estimates are sharp.

The $\ell=2$ class remains. No two-term star estimate follows by deleting it
or by a coincident-vertex substitution. The direct Case-3 numerator does not
need this star route.

## Exact branch-and-root count: `QZeroCount`

`TS_eq_sum_reps` evaluates the recursive tree sum over the canonical
representatives of the non-plane rooted binary trees on every finite nonempty
label set. At four labels, `card_reps_four` proves 15, the path distribution is
$(3,6,6)$, and the four shapes have multiplicities $(3,3,3,6)$. The
isomorphism-closure checks show the hand-written atlas is complete and
duplicate-free. `sum_LT_fin_four` proves the exact factor 8 between the plane
weight sum and the non-plane sum.

These cardinality/structure results concern the explicit representative
recursion. They do not by themselves prove a numerical evaluation of the
(separate) `nonplaneMarkedCount` function, and do not give a percolation moment
bound.

## Canonical event realization: `QZeroStarAtlas4`

`starLabels` extends three cluster labels by the marked vertex $y$.
`labelEvent_starLabels` identifies the resulting four-label event, and
`starMoment_le_starAtlasSum` applies production's finite-witness BK chain to
obtain the actual infinite-product event realization. `tsum_arms_wtE` proves
the exact value $\chi^{7-\ell}T^\ell(x,y)$ for a shape of marked depth $\ell$.
A further bound in terms of `nonplaneMarkedCount` keeps the coefficients
symbolic and retains $\ell\in\{2,3,4\}$.

The plane-labelled sum carries the larger multiplicities noted in the m7
packet; it is not silently equated to the non-plane atlas. This remains an
atlas/shape result, not a proof of the two-term star estimate.

## Exponent and covariance corrections

`QZeroAtlasWitness` proves attainment of the generic atlas estimates on the
constant kernel and a kernel-level upper bound on its full window sum. This
does not establish a small model residual or a finite/tower replacement for
the source law.

`QZeroRepairAudit` proves the additive split
$$\text{star}=\text{productGap}+\operatorname{Cov}(\lvert K_x\rvert^a,\lvert K_y\rvert^b),$$
the diagonal distinctions, the covariance reduction behind an additive repair,
and conditional correction lower bounds. `additive_of_gap_of_cov` shows that a
product-gap bound together with `HasCovBound` suffices. **The covariance bound
itself is not proved.** Conditional $\chi^5$ and fixed-radius no-gos retain the
`QZeroDiagInputs` assumptions and do not refute the paper.

The corresponding exported results and key consumers are imported in the global
axiom audit and the focused Case-3 audit. No `sorry`, `admit`, `native_decide` or
custom axiom is used.
