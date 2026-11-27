# Case 3 from the proved `(2,1)` product gap

`Analysis/SecondMomentCase3/ProductGap` supplies the source-side consumer that
does not use the old q-zero star hypothesis `hgap`. It was independently
rebuilt and axiom audited from `smwziumdb/m5`. Audit records 39 declarations
with only `propext`, `Classical.choice`, and `Quot.sound` for each.

## Exact numerator identification

Printed page 43, displays (I.4.14) and the alternative expression following
them, distinguishes two things:

* the numerator of $E_{2,r}$, namely
  $|B_r|E|K|E|K|^2-E[|K|\sum_{y\in B_r}1(y\notin K_0)|K_y|^2]$; and
* its separate upper bound by the q-zero star, used in Case 1 and Case 2.

At $(p,q)=(2,1)$ Lemma I.4.17, printed p. 45, bounds the first object. With the
root-independence of the cutoff moments and plain connectivity symmetry, this
is the window sum of `I417.volSq (cutProb r) y * I417.meanVol (cutProb r) 0 -
I417.exclMomentSq (cutProb r) y 0`. The squared exponent belongs on the window
vertex $y$; the swapped-pair assignment is essential.

`perVertex_case3_eq_p21` proves the per-vertex identity, and
`case3Numerator_eq_sum_sub_sum` gives the normalization in $\mathbb R_{\ge0}\infty$.
`case3Numerator_le_case3DiffWindow` handles the direction from a difference of
sums to sums of differences without silently distributing real subtraction.
`case3Numerator_le_polygonWindow` then specializes the **proved**
`I417Example.printed_le`:
$$N_r\le\sum_{y\in B_r}\left(T^3(0,y)\chi^4+2T^4(0,y)\chi^3\right).$$
That displayed $(2,1)$ product-gap bound is unconditional as given over the
independent edge profile, subject to its usual all-open-probabilities-less-than-one
and root-independence hypotheses. It is not a restored-moment or star bound.

## Case-3 assembly

`polygonWindow_toReal_eq` identifies the two matrix powers with actual cutoff
`I418C.polyK` values. `polygonWindow_toReal_le_of_inputs` applies the proved
windowed $\ell=3$ and per-vertex $\ell=4$ polygon inputs, giving
$$(N_r).\mathrm{toReal}\le 3C_p|B_r|\operatorname{drv}(r)\chi^4$$
in real form, without the impossible pointwise $\ell=3$ input.
`p2ExclError_le_case3Driver_of_polygonWindow` then retains the lower
second-moment comparison and proves the expected driver bound, with its
vanishing and logarithmic-integrability consequences.

`secondMoment_asymptotic_case3_p21` and
`secondMoment_asymptotic_case3_of_source_p21` assemble the conclusion
$E_{\beta_c,r}|K|^2/r^{3\alpha}\to A>0$. The old third-star term and `hgap` are
absent. `regularlyVarying_two_of_source_p21` supplies the other second-moment
regular-variation form.

This closes the Case-3 **numerator/consumer gap**. It does not prove
Proposition I.4.15 or I.4.20 as unconditional model theorems. The retained
hypotheses are the same ODE absolute continuity, almost-everywhere derivative,
finite first/second cutoff moment, first-moment asymptotic, triangle condition,
open-triangle logarithmic radial bound, second-moment lower comparison,
measurability and logarithmic-integrability inputs as in the earlier
source-like wrapper. No q-zero star estimate is inferred, no other case of
I.4.15 is completed, and no higher-moment I.4.20 statement is proved by this
packet.

## Relation to the obsolete target

The q-zero star inequality targeted by the preceding campaign was a stronger,
optional way of upper-bounding the same error via the covariance correction.
`star = productGap + covariance` makes clear why a product-gap bound alone
cannot prove it. The newly integrated consumer targets the product object the
source's Case 3 actually consumes, so the earlier root/near-vertex star
obstructions are not missing completion conditions for this route.
