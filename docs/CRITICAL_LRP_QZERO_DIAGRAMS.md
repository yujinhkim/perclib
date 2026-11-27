# Conditional restoration, diagram and consumer packets

These independently rebuilt packets were accepted in `smwzg77c3` with explicit
scope limits. Their full capstone is **not** the old all-vertex $(3,0)$
estimate, and none of them completes Proposition I.4.15 or I.4.20.

## Restoration: `QZeroRestoration`

The definition layer introduces `restoredConn`, `restoredDiag`, and
`restoredTotal`. The principal exact identities are:

* on $y\in K_x$ in the restoration coupling, the restored cluster at $y$ is
  the cluster at $x$; consequently `restoredConn_eq_starMoment` holds for
  every $p,q$;
* `restoredTotal_eq_jointMoment` makes the restored total the **one-copy
  joint** moment, not a product moment;
* `restoredDiag_eq_rawDiff` identifies its excluded part, so
  `starMoment_three_add_rawDiff_two_one` splits the joint moment into the
  star and the excluded moment;
* at the cutoff law, `connCubeVertexMass_eq_restoredConn` and its window sum
  specialize this at degree three.

`connCubeVertexMass_le_twoTerm_of_source_two_one` transports a **restored**
$(2,1)$ two-term estimate with printed constants $1,2$. It is conditional,
not an application of the product-minus-excluded gap to the star. Positive
association makes the latter a lower bound for the star, the wrong direction.

## Vertex obstruction: `QZeroRepair`

`harris_starMoment` proves termwise positive association:
$$T(x,y)\,\mathbb E|K_x|^p\le
  \mathbb E[|K_x|^p\mathbf1(x\leftrightarrow y)].$$
The cutoff instance is `harris_cutMoment`. Under finite moments, finite
triangle, and a lower third-moment estimate $E|K|^3\ge K\chi^5$,
`T_mul_chi_le_of_twoTerm'` and `T_le_of_twoTerm'` turn an instance of the
old two-term estimate at $y$ into
$$K\,T(0,y)\,\chi\le(C_3+C_4)\nabla.$$
`not_twoTerm_of_T_ge` therefore applies at near nonzero vertices too, not
only at the basepoint. A sole $y\ne0$ restriction is not a valid universal
repair. The alternative interfaces `StarTwoTermBoundFar` and
`StarTwoTermBoundAdd`, and the exact window arithmetic `sum_le_twoTerm_far`
and `sum_le_twoTerm_add`, remain conditional: no far or additive estimate is
proved. Growth, triangle and unbounded-susceptibility premises in the other
no-go statements stay explicit.

## Marked and explicit atlas reductions

`QZeroMarked.markedCoeff_one_eq_zero` proves that the $p=3$ marked bound has
no $\ell=1$ class, giving the three-class formula $m_2T^2\chi^5+m_3T^3\chi^4+
m_4T^4\chi^3$. `markedCoeff_sum_four` proves the total $120$. The split
$(m_2,m_3,m_4)=(24,48,48)$ remains hand computation and is not baked into
these declarations.

The reductions `twoTermBound_of_chi_mul_square_le` and
`twoTermBound_of_chi_sq_mul_square_le` require the stated two-point residual;
they do not establish it. `QZeroGapNoGo` proves only that symmetry and
stochasticity of an abstract two-point swap kernel do not imply such a
comparison. Aperiodicity by itself is not asserted to be sufficient either.

`QZeroAtlas` names fifteen explicit seven-edge diagrams. Their formal
$\ell=2,3,4$ multiplicities are $(3,6,6)$, and the shape summands use the
actual iterated kernel-power definitions. `atlas_le` and
`starMoment_le_three_term` are conditional on the four shape evaluations and
an event-atlas realization, respectively. Thus the displayed three-term
weight is not yet a proved source-moment inequality. Moving internal
vertices to $0$ without preserving the edge-disjoint events is not accepted
as an $\ell=2$ cancellation.

## Consumer bookkeeping: `QZeroConsumer`

This packet proves `tsum_starRHS`,
$$\sum_y\big(C_3T^3(0,y)\chi^4+C_4T^4(0,y)\chi^3\big)
 =(C_3+C_4)\chi^7,$$
under finite $\chi$ and the corresponding summability, plus its extended-real
conversion bridges and abstract non-absorption examples. It also instantiates
the native third-moment tree bound at the root,`connCubeVertexMass_zero_le`,
and supplies off-diagonal summation wrappers. Those wrappers retain their
premises and do not resolve the Harris/near-vertex obstruction.

The old pointwise $\ell=3$ driver appearing in some conditional statements is
already known to be unusable with a vanishing driver. New work must use the
proved windowed polygon inputs instead. The remaining mathematical questions
are the actual certificate-level realization, source diagram evaluations,
and a valid small-two-point or additive completion of any q-zero route.
