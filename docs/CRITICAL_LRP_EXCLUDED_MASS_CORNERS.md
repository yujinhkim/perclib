# Excluded mass and one-sided cutoff derivatives at attained radii

This note covers the packages
`Analysis/Cutoff/OffCorner/LeftExcludedMass` and
`Analysis/Cutoff/OffCorner/RightExcludedMass`.
They concern the $p=1$ cutoff first moment under the existing normalized-source model.
They do not assert the general-$p$ formula of Lemma I.4.1, subcritical sharpness,
positivity of `betaCrit`, or the large-radius asymptotic ODE.

## Exact strict-window and shell decompositions

`LeftExcludedMass/Defs.lean` uses the common uniform-mark representation to define
`exclMassLt` over the strict ball $B_{<r}$.  `LeftExcludedMass/Main.lean` proves the
left limit
$$
  \lim_{s\uparrow r}\operatorname{exclScalar}(s)=\operatorname{exclScalarLt}(r)
$$
at every positive radius from finite second and third cutoff moments at a strictly larger
radius.  It also proves the exact jump identity
$$
  \operatorname{exclScalar}(r)
  =\operatorname{exclScalarLt}(r)
   +\operatorname{pairSphereMass}(r).toReal
   -\operatorname{sphereMass}(r).toReal
$$
and shows that the last two terms have nonnegative difference.  The connected and pair
sphere layers are different objects and are not silently identified.

`RightExcludedMass/Defs.lean` defines `exclMassStrict` directly under the cutoff law,
again with the strict ball, and separately defines the shell contribution `exclMassShell`.
`RightExcludedMass/Main.lean` proves the closed-strict-shell decomposition
$$
  \operatorname{exclMass}(r)
  =\operatorname{exclMassStrict}(r)+\operatorname{exclMassShell}(r)
$$
and right continuity of the closed-window excluded mass at every positive radius, from
finite second and third cutoff moments at a strictly larger radius.

`RightExcludedMass/Bridge.lean` proves
`exclMassLt = exclMassStrict` by transporting the uniform marks with
`markMeasure_map_atParameter`.  Thus the two strict-window definitions denote the same
mathematical quantity, with no off-sphere premise.  The corresponding scalar identity is
`exclScalarLt_eq_exclScalarStrict`.

## One-sided derivative values

`LeftExcludedMass/Scalar.lean` proves that, given an off-corner derivative family on an
adjacent open left interval, the cutoff first moment has left derivative
`rhsScalarLt r = coeffRHS r * exclScalarLt r`.

`RightExcludedMass/Main.lean` proves the corresponding right derivative with the
closed-window value `rhsScalar r = coeffRHS r * exclScalar r`, from an off-corner
family on an adjacent open right interval.  `RightExcludedMass/Corner.lean` supplies a
version beyond the existing tail threshold and proves the exact discrepancy
$$
  \operatorname{rhsScalar}(r)
  -\operatorname{coeffRHS}(r)\operatorname{exclScalarStrict}(r)
  =\operatorname{coeffRHS}(r)\operatorname{exclMassShell}(r).toReal.
$$
The adjacent derivative families, local moment bounds, and kernel-derivative continuity
remain explicit hypotheses; they are not inferred from zero percolation probability.

`RightExcludedMass/Tail.lean` constructs a corner-free left window and produces the left
off-corner derivative family from the landed tail theorem.
`exists_left_hasDerivWithinAt_cutMassReal_rhsScalarLt_Iic` therefore gives the left
corner derivative without a supplied family, while `exists_not_hasDerivAt_of_shell` and
`exists_not_hasDerivAt_of_attained` assemble both sides without either derivative family.
These versions ask for continuity of the kernel derivative and per-vertex singleton flux
on the fixed window used by the two tail constructions.  The larger-radius second moment
also supplies the second moment needed at the corner; no separate endpoint second-moment
premise is required.  The family-based bridge theorem is retained because it asks only
for kernel-derivative continuity at the corner and is useful when the families are
already available.

## Shell positivity and two-sided differentiability

`RightExcludedMass/ShellPositive.lean` computes finite closed-cylinder probabilities and
proves that an edge longer than the cutoff is closed almost surely.
`RightExcludedMass/Positive.lean` uses these facts at a nonempty shell and positive
radius.  On a positive-probability event, close the loop at the origin and every edge of
the finite short incident support; intersect this with the almost-sure event closing all
longer edges.  On the intersection, the origin cluster is the singleton and each shell
vertex contributes at least one to the shell expectation.  Consequently
`exclMassShell r ≠ 0`.

The same file proves the reverse boundary conditions: an empty shell has zero mass and
so does the origin shell at radius zero.  Consequently
`M.exclMassShell r ≠ 0 ↔ 0 < r ∧ (M.shellF r).Nonempty`.
`RightExcludedMass/Bridge.lean` uses an attained radius to construct a positive-radius
witness in every normalized source model, so this positivity is non-vacuous within the
model class.

`RightExcludedMass/Bridge.lean` specializes this to every attained radius and
assembles the two derivative values.  Under the two adjacent off-corner derivative
families, the local moments and kernel continuity, and `0 < coeffRHS r`, it proves that
the cutoff first moment is **not two-sided differentiable** at an attained radius:
its left derivative uses the strict window and its right derivative uses the closed
window, with a positive shell discrepancy.

Accordingly, these results must not be read as a two-sided version of the printed
closed-ball derivative formula at an attained radius.  They support the separate
one-sided statements and make the derivative-jump obstruction explicit.  A complete
source treatment of Lemma I.4.1 remains open, including general $p$, its regularity
inputs, and its intended convention at corners.
