# The summation step of Lemma I.4.11

`Correlation/I411/RowSumCore` and `Correlation/I411/RowSum` prove the
row-sum/factorisation stage of Lemma I.4.11. They do not identify the actual
excluded-mass numerator with the five-factor gap diagram, so Lemma I.4.11
remains PARTIAL.

Let the five-factor leaf be
$$\tau_{oa}\tau_{ax}\tau_{ab}\tau_{by}\tau_{bz},$$
summed over $a,b$, and sum the result over $y\in B$ and all $x,z$. Exchanging
sums and factoring the separate $x,z$ variations produces
$$\sum_{a,b}\tau_{oa}\tau_{ab}\tau_{by}
 (\sum_x\tau_{ax})(\sum_z\tau_{bz}).$$
Two row bounds $\sum_\bullet\tau_{a\bullet}\le\chi$ therefore give
$$\operatorname{gapMass}\le\chi^2\sum_{y\in B}\nabla(0,y).$$
`lemma_I_4_11_step` then divides by $|B|\chi^2$, with the necessary hypotheses
that `B` is nonempty and `χ > 0`. When every row sum equals `χ`, the
factorisation is an equality. The `Unit` example with $\tau=1$, $B=\{()\}$, and
`χ=1` attains the bound and supplies a nonvacuity witness.

The finite version uses a finite vertex type and real nonnegative weights. The
countable companion uses `Countable V` and `ℝ≥0∞` weights with `tsum`, avoiding
a summability hypothesis while making no conversion to finite real moments.

Still outside these modules are the two-copy rewriting of the cluster/excluded
mass numerator, the pointwise I.4.12 gap input at that identified numerator,
and the model row-sum identity. They are retained explicitly rather than being
replaced by the factorisation. The source normalization and the existing
conditional cutoff theorem are unchanged.

Both integrated modules were elaborated with all three strict flags; their
audited declarations have only `propext`, `Classical.choice`, and `Quot.sound`
as axioms.
