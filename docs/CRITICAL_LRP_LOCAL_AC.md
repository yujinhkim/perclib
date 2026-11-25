# Interval majorants and absolute continuity

`Analysis/Cutoff/LocalAC/Defs.lean` introduces primitive-derivative-majorant
and off-finite-set predicates. `Analysis/Cutoff/LocalAC.lean` weakens the
continuous-majorant criterion behind `IntervalAC` to interval-integrable
majorants with primitive derivative or point-continuity assumptions.
`LocalAC/Interface.lean` exposes the conditional model-level instances.

Endpoint singularities are allowed under interior continuity and closed-window
`L¹` integrability. Once absolute continuity of the function is established,
only an almost-everywhere derivative bound against an arbitrary
interval-integrable majorant is needed. A step-function counterexample checks
that discontinuity of the function cannot be dropped.

The model continuity and corner-set premises are explicitly supplied by
`Cutoff/Continuity` and `CornerRadii`; the actual off-corner derivative is still
an input in the interface. These lemmas do not claim AC from an arbitrary
measurable derivative bound alone, from finite boxes, or from monotone
regularity alone.
