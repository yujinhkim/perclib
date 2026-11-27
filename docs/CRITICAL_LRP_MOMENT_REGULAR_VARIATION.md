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

`momOf_packet` and `drivingTerm_RVPosData_of_hP` expose the first-moment,
positivity, measurability and RV data to the higher-moment machinery while
keeping $h2$ explicit. They do not claim the Lemma I.4.1 derivative, critical
second-moment asymptotic, general I.4.15, or general I.4.20.
