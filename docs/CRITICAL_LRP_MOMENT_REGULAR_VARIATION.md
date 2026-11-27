# Regular variation of cutoff moments

Production base: `d2b527c1acf9fb8db8ca24854405020a6b3de061`.

## What is now supplied

`Analysis.MomentRegularVariation` proves a normalized-asymptotic to
regular-variation transfer. If $f(r)/(c r^a)\to1$ with $c\ne0$, then
$F(r)=f(r)$ is regularly varying of index $a$:
$F(lr)/F(r)\to l^a$ for every fixed $l>0$. Eventual non-vanishing follows from
the ratio being eventually positive, not from an added smoothness hypothesis.

For the actual cutoff profile, the usual cutoff-mass asymptotic `hP` supplies:

* first-moment regular variation `momOf_one_regularlyVarying` (index $\alpha$);
* global measurability `momOf_measurable_one_two` of the first two cutoff
  moments, once that asymptotic supplies finite first moments at every radius;
* positivity `momOf_pos_of_hP` at every positive radius, using root
  membership and the existing ordinary atlas finite-moment bound.

The composition
`momOf_one_regularlyVarying_of_critical_divergence` uses the already proved AE
first-moment asymptotic under critical mean divergence. The asymptotic is an
input chain, not a proof of sharpness or critical divergence.

## The remaining second-moment input

Second-moment regular variation of index $3\alpha$ remains independent. The
interface now states the exact equivalence, given first-moment regular
variation and eventual positivity:

$$\mathrm{RV}[M_2](3\alpha)
\iff \mathrm{RV}[M_2/M_1^3](0).$$

`momTwo_regularlyVarying_of_tendsto_ratio` supplies a sufficient version: a
nonzero limit of this quotient yields the required regular variation. This is
stronger than the bounded two-sided comparison supplied by the critical tail
comparison plus the ordinary atlas bound. `momOf_two_squeeze` records that
bounded comparison without calling it an asymptotic.

`Analysis.RegularVariationCounterexample` proves that bounded comparison is
not enough. The scalar function $x(2+(-1)^{\lfloor x\rfloor})$ lies between
$x$ and $3x$, but its $2$-scaling ratio is $6$ along $x=2n+1$, so the required
limit for index $1$ does not exist. This is a counterexample to the inference
from bounded comparison to regular variation, not to the paper's actual
second-moment theorem.

The source's second-moment excluded quadratic mass is supplied independently of
regular variation: `SecondMoment.ExclusionSwap` uses midpoint reflection of the
actual radial cutoff law to prove `exclMassQuad = exclMassSqLin`, hence
`p2RHS = 3 * exclMassQuad`. This closes the exact coefficient-three identity of
(I.4.14), not the derivative handoff or the vanishing of the second-moment
error. See [the second-moment note](CRITICAL_LRP_SECOND_MOMENT.md).

## Corner-safe linear-ODE route

`Analysis.SecondMomentRV` supplies the other analytic input separately: for a
positive function $f$, interval absolute continuity and an almost-everywhere
identity $f'=3\alpha(1-E)f/r$, with measurable $E\to0$, imply
`RegularlyVaryingAtTop f (3 * α)`. If $E$ is logarithmically integrable, it
also gives a positive limit of $f(r)/r^{3\alpha}$. The proof uses the exact
integrating factor and the existing a.e. normalized-increment theorem, with no
driving term and no assertion of differentiability at attained radii.

`ModelSecondMomentRV` specializes this to the actual cutoff second moment and
to the `rhsScalarTwo` error ratio. Its hypotheses include $h_P$, second-moment
absolute continuity, the a.e. ODE, measurability and the error limit; the
logarithmic-integrability refinement is a separate input.
`momOf_packet_of_ae_linear_ode` composes this with `momOf_packet`, so $h_2$ is
derived only once those extra model data are supplied. It does not construct
them and does not prove general Proposition I.4.15 or I.4.20.

`momOf_packet` and `drivingTerm_RVPosData_of_hP` expose the first-moment,
positivity, measurability and RV data to the higher-moment machinery while
keeping $h2$ explicit in the absence of those additional data. They do not
claim the Lemma I.4.1 derivative, critical second-moment asymptotic, general
I.4.15, or general I.4.20.
