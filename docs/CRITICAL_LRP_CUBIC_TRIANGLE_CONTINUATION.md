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

## Almost-everywhere higher-moment induction

`Analysis.AEHigherMoments` defines the corner-safe analytic interface:
absolute continuity on every compact interval of a radius tail, a derivative
almost everywhere on that tail, and a.e. one-sided differential comparisons.
The integration core uses absolute continuity and an a.e. fundamental theorem;
it never invents derivatives on the null set of attained radii. The normalized
increment and defect forms of Lemma I.4.22 permit a sign-changing measurable
defect tending to zero.

`moment_upper_bound_of_percolation_ae` and its ratio form carry the same interface
through the general higher-moment induction step. The cubic wrappers and
`I420Case3.case3_moment_three_bound_of_HD_case3_ae` use the accepted off-corner
first-moment package instead of a global pointwise first-moment ODE.

The third-moment absolute continuity, its a.e. Lemma-I.4.1 identity, and
measurability of that moment and derivative expression remain explicit
hypotheses. The available first-moment absolute continuity is not silently
promoted to order three, and second-moment regular variation is still a
separate input. These are corner-safe conditional induction results, not a
proof of general Proposition I.4.15 or I.4.20.

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

## Triple convolution and tail decay

`Analysis.TriTailConvolution` now supplies the exact identity
$$\nabla_{\Gamma_f}(0,x)
 =\sum_y(f*f*f)(y)(f*f*f)(y-x)$$
after the required `ℝ≥0∞`-to-real conversion. For nonnegative summable $f$,
it proves that $f*f*f$ is summable with mass $(\sum f)^3$, belongs to $\ell^2$,
and therefore has vanishing far-translation autocorrelation. This gives
`openTriangleTail_tendsto_of_gramProfile` and its domination version.
`SourceModelData.nablaTail_le_openTriangleTail` explicitly carries the radius
normalization $r/\mathrm{srcUpperConst}(M.S)$, and the model tail also tends
to zero.

`Analysis.TriTailRadial` supplies an independent route that does not need the
convolution identity. Two row-mass bounds and Tonelli give
$$\sum_x\nabla_{\Gamma_f}(0,x)\le(\sum_z f(z))^6,$$
and a general finite-mass lemma makes the radial supremum tend to zero for any
real-valued radius function, including the actual normalized source norm. The
strict and closed tails are both covered. The delta profile attains the mass
bound; the constant-one example proves that finite total mass is indispensable.

These results remain conditional on the Gram-profile identification or
domination hypothesis. Such a summable profile has finite $\ell^1$ row mass and
is not a derivation of the critical long-range two-point profile from HD(3).
No general Case-3 or Proposition I.4.20 conclusion is claimed.
