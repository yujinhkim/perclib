# Cubic ratio induction and explicit triangle normalization

Production base: `46283a4a578de6882474c649d656555db9a7dcb2`.

## Case-3 ratios instead of pointwise decorrelation bounds

`VolumeMoments/HigherMoments/I420Case3/RatioInduction` turns the Case-3 limits
into the induction step used for the cubic moment. This is not a substitution
of the old pointwise `hA0`/`hAmid` bounds: ratio convergence gives only
eventual $(1+\delta)$ comparisons. These feed the existing finite binomial
sum, with slack absorbed using $(1+\delta)^4\le 1+\epsilon$.

`HigherMoments.derivative_bound_ratio` performs that analytic comparison.
`moment_upper_bound_three_ratio` then uses the vacuous lower-order induction
at $p=3$. `padMom` gives positivity only at orders $1,2,3$ without changing
anything in the cubic moment ratios; it is a bookkeeping device, not a claim
about arbitrary higher moments.

At the actual cutoff family, `mixedExclR_cutProb_swap` supplies endpoint mass
transport, `ballCard_pos` supplies ball nondegeneracy, and
`momOf_cutProb_pos_three` supplies the first three moments' positivity at
positive radius. `case3_moment_three_bound_of_HD_case3` yields the eventual
cubic upper bound and `case3_moment_three_asymptotic_of_HD_case3` the ratio
one asymptotic and regular-variation conclusion. The source's actual higher
order derivative identity, first/second-moment regular variation, cutoff
normalization and triangle condition are **not supplied by these wrappers**.
The global `hderivId` required by the old higher-moment interface remains a
material input. The subsequent off-corner/AE package is a separate reduction;
it does not by itself prove that higher-moment identity.

## Finite triangles from an explicit autocorrelation profile

`Analysis.TriTailNormalization` defines
$$\Gamma_f(u,v)=\sum_z f(z)f(z+v-u).$$
Tonelli gives row mass at most $(\sum_z |f(z)|)^2$, and mass $(\sum_z f(z))^2$ for nonnegative $f$; its diagonal is $\sum_z f(z)^2$. For nonnegative summable $f$, the general row-sum estimate
$\nabla(0,0)\le R^3$ therefore gives $\nabla(0,0)\le(\sum_z f(z))^6<\infty$.
If the configured two-point function equals, or is dominated pointwise by,
$\Gamma_f$, `openTriangleSelf_lt_top_of_gramProfile` and
`openTriangleSelf_lt_top_of_gramDomination` give the corresponding finite
open triangles. `SourceModelData` wrappers specialize this to the source
model, without requiring the empty assertion that every critical two-point
function has such a profile.

The identity profile makes this condition inhabited: it has unit diagonal,
translation invariance, symmetry and finite triangle. Conversely,
`openTriangleKernel_one_eq_top` and
`diagonal_one_translationInvariant_not_sufficient` show that unit diagonal,
pointwise bound one, symmetry and translation invariance **cannot by
themselves** imply finite triangle mass, even though one also checks PSD for
the constant-one kernel elsewhere in the library. The infinite diagonal sum
is the obstruction. This is a counterexample to an insufficient hypothesis
set, not to the paper.

The source uses the triangle condition as Case 3 of Proposition I.4.2
(`paper.txt` lines 1820–1837), so retaining it as a source input is faithful.
The profile hypothesis here is separate from `(HD)(3)` and is not obtained
from that disjunct. The $\ell^1$-row estimate is not the critical model's
claimed $\ell^2$ operator bound; it cannot be inferred from the critical
power-law decay.

## Remaining tail work

`conv_comm` and `conv_assoc` are proved for extended-nonnegative lattice
convolution. They do **not** establish the triple-convolution/autocorrelation
identity or its finite-real conversion needed to derive tail vanishing under
the Gram profile. Those steps remain open. The delta computation is a
non-vacuity example only, not a model identifier for critical percolation.
