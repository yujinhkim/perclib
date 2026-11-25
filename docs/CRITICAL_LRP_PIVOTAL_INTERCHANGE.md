# Per-edge integration and two-point increments

`Analysis/Cutoff/OffCorner/PivotalWeight/{Defs,Interchange,TwoPointIncrement}.lean`
proves a separate interchange from the outer radius/vertex exchange.

`pivotalTerm m r e` isolates the nonnegative per-edge summand in the pivotal weight series.
It scales by `max m 0`, is measurable in radius, and decomposes finite observations by the
same arithmetic that handles `max (∑_x |q x|)`.

With the interior-scale derivative envelope and finite first cutoff moment at its
comparison radius, the model-level Tonelli theorem exchanges interval integration with
the genuine edge series:

$$
\int_a^b \sum_e \text{pivotalTerm} = \sum_e \int_a^b \text{pivotalTerm}.
$$

It also proves interval integrability for a finite observation and for the signed
per-edge Russo flux series. The finite-observation identity separates the finite integral
of a weighted sum into the sum of the singles, without conflating this with a constant
unweighted singleton weight.

For one vertex, the signed per-edge infinite flux is integrated termwise and then valued
via the cutoff two-point fundamental theorem:

$$
\sum_e \int_a^b c_r(e)\,\operatorname{pivotalFlux}_r(e)\,dr
 = \operatorname{cutTwoPoint}_b(0,y)-\operatorname{cutTwoPoint}_a(0,y).
$$

The remaining window hypotheses are explicit: off-corner radii, local differentiability
and regularity of the kernel, edge summability and per-vertex flux continuity. There is
no claim of new uniform differentiability at attained radii.

The unit-weighted singleton bound being constant in `y` is only a limitation of that
bounding route. The true outer vertex interchange is the independently proved
`RadiusVertexInterchange` theorem and is not contradicted or assumed here.
