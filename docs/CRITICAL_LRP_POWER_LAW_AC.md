# Local absolute continuity for the power-law cutoff mass

`Analysis/Cutoff/OffCorner/PowerLawAC.lean` combines the finite-moment off-corner
derivative with the established local derivative majorant. The central analytic target
is local radius absolute continuity of `M.cutMassReal`, not the large-radius asymptotic
ODE.

## What is proved

The module constructs monotone finite vertex/edge exhaustions from `Encodable.decode`
and products through `Sym2.mk`; it does not assume a separate enumeration of `Sym2` in
this construction. For the literal `sourceModelWitness`, it also proves the exact
`hboundint` input of the radius derivative-exchange wrapper, using the interior-scale
envelope. The per-vertex continuity helper is imported from
`OffCorner/PowerLawContinuity`, not duplicated.

At an off-corner radius the derivative and its coarse window majorant are explicit.
For `0 < a < b` with the interior of `[a,b]` off the corner set:

- `sourceModelWitness_continuousOn_cutMassReal` proves continuity on the closed
  interval. Interior points use the finite-mean continuity theorem at a larger radius.
  At `b`, only the left approach within the interval is required, so left continuity
  from `cutMassAt b 0 ≠ ⊤` suffices. No moment at a radius above `b` is needed.
- `sourceModelWitness_cutMassReal_absolutelyContinuousOn_Icc` proves absolute
  continuity in radius.
- `sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc` proves
  $∫_a^b χ'(r)\,\mathrm{d}r = χ(b)-χ(a)$.
- The same finite second/third endpoint-moment hypotheses give the increment bound by
  a constant majorant and almost-everywhere `DifferentiableAt` on the interval.
- `sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc_of_firstMoment` supplies
  the same fundamental-theorem identity from the single assumption
  `cutMoment 1 b ≠ ⊤`, because `SourceCutoffMoments` derives the required higher
  moments from that first moment.

The derivative majorant used is the existing coarse constant
$β_c a^{-d-α-1}|B_b|(\mathbb E_{β_c,b}|K|^2)^2$, not a new asymptotic estimate and not
a radius-uniform bound on `stdDegree`.

## Scope

These results are conditional on the finite endpoint moment and off-corner window.
They do not construct finite first moments for arbitrary large radii, prove
$β_c>0$, prove a derivative at an attained radius, or prove the paper's asymptotic ODE.

Integration repaired the scratch packet's missing module docstring, an unused
`DecidableEq` binder, and the placement of its heartbeat options. Its duplicate
per-vertex continuity helper was removed. Strict focused compilation and the module
build pass, with only the standard axioms in every audited theorem.
