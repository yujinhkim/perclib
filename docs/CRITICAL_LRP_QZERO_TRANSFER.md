# Conditional reductions around the `q = 0` star

## Scope

`QZeroReduction` and `QZeroTransfer` are independently rebuilt, accepted
supporting packets from `smwzg77c3`. They reduce some arithmetic and
measure-theoretic work around the connected third star moment. They do **not**
prove its two-term bound, the seven-edge event realization, or Proposition
I.4.15/I.4.20.

## Conversion, invariance and absorption limits

`Correlation/I417/General/QZeroReduction` names the real two-term target and
its `ℝ≥0∞` parents. It proves:

* `hgap_of_KpowTwoTerm` and `hgap_of_cutPolyTwoTerm`, with finite cutoff
  susceptibility and nonnegative coefficients; every `toReal` conversion is
  applied to a finite quantity.
* `starMoment_shift`, `starMoment_root_indep`, `polyK_shift`,
  `polyK_root_indep`, and `chi_root_indep`: translation does not change the
  root-normalized star, kernel power, or susceptibility.
* `hgap_of_treeFour`, `hgap_of_treeClasses`, and `hgap_of_tauChi`: conditional
  absorption of explicitly named residual bounds. Their bound hypotheses are
  not supplied by this packet.
* `degree_five_class_not_absorbable` and `deep_class_not_absorbable`: abstract
  real-valued counterfamilies showing that certain deep tree classes cannot
  be absorbed using only nonnegativity, exponent monotonicity, and `χ ≥ 1`.
  These are not counterexamples to the cutoff percolation model.

## Finite-restriction suprema

`Correlation/I417/General/QZeroTransfer` defines `Exhaustion.labSum`,
`Exhaustion.truncMass`, and `Exhaustion.truncStar` in its `Defs.lean`. It
proves that the original star is the supremum of its finite label-family
partial sums and, independently, of the moments with cluster volume
restricted to finite vertex sets. Uniform bounds against a fixed RHS pass in
both directions. Strict violations occur already at some finite restriction
in either family.

The principal statements are `starMoment_eq_iSup_labSum`,
`starMoment_le_iff_forall_labSum`, `starMoment_eq_iSup_truncStar`,
`starMoment_le_iff_forall_truncStar`, `lintegral_cardFun_eq_iSup_truncMass`,
and the `SourceModelData.connCubeVertexMass_*` specializations.
`connCubeVertexMass_toReal_le_of_labSum_le` converts to a fixed nonnegative
real RHS with `ENNReal.toReal_ofReal`.

`truncStar` restricts the cluster volume inside the **same infinite product
law**. It is not a finite-torus model or proof of a finite-volume analogue of
the source theorem, and its RHS is not thereby truncated. The missing
uniform seven-edge/tree cover is unchanged.

## Target scope

Under the explicit root growth package, the established diagonal obstruction
rules out the old all-vertex target. The later Harris/FKG constraint also
rules out treating mere exclusion of `y = 0` as a universal repair: on a
region where the two-point function is bounded below, an unbounded third
moment defeats the same estimate. Valid alternatives must restrict to a
small-two-point region or carry an additional term. No such far or additive
estimate is proved here.

The standalone audits of both packets compile under the strict warning,
auto-implicit, and mathlib-lint settings and use only `propext`,
`Classical.choice`, and `Quot.sound` for their recorded declarations.
