# Sixth mixed moment: the exact cover residual and a false shortcut

`Correlation/SixPoint/MixedK2/SixthMoment` independently checks computations
for Lemma I.4.16 at `p = 6`, `k = 2`, at the actual normalized cutoff law.

## Proved reductions

* `lintegral_cardFun_six_eq` expresses the sixth cluster moment as the exact
  sixfold sum of joint connection probabilities, using Tonelli alone.
* `tsum_slotK2Six_six` evaluates every two-hub slot at exactly
  `(E|K|²)² (E|K|)⁴`, using full translation invariance and root independence
  of the second moment. Since `E|K| ≥ 1`, each has bound
  `(E|K|²)² (E|K|)⁵`.
* `sixth_moment_of_sixCover` shows that a cover of the sixfold joint event by
  the `945` two-hub diagrams implies `E|K|⁶ ≤ 945 (E|K|²)²(E|K|)⁵`.
* `sixthMomentMixed_of_sixCover` instantiates this literally as
  `CaseTwo.SixthMomentMixed M`.
* `sixth_moment_of_eventCover` replaces the diagram-specific condition by an
  arbitrary `945`-event cover with the same bound on each shape, without
  assuming that the two-hub diagrams are the correct ones.

The Case-2 excluded-error consumer `p2ExclError_tendsto_zero_of_sixCover`
preserves `hP`, `Hydro`, `d = 3α` and eventual finiteness of the second moment.

## Refutation of the two-hub cover

`HubK2SixCounterexample.sixCover_false256` disproves `SixCover` on the
vertex-transitive six-cycle at opening probability `1/256`. At the collapsed
tuple `(0,3,3,3,3,3)`, the three-edge connection cylinder forces a lower bound
of `θ³`, while all hub pairs and all 945 labellings together have a smaller
upper bound of order `θ⁶`. Hence that collapsed two-hub cover cannot be used
for the proof of Lemma I.4.16 at `p = 6`.

This is a counterexample to a proof route, **not** to the generalized tree-graph
inequality. The latter stays true, with printed coefficient `945`. A source
proof needs the full tree/BK decomposition with degenerate configurations
handled per tree rather than after reducing them to two hubs.

The related source erratum from the audit is only about the printed
proof-sketch's `(2p−1)!!` terminology versus the statement's `(2p−3)!!`; this
package follows the statement and does not change its constant.

## Scope

`SixCover` is not unconditionally proved. The generalized event-cover residual
is also retained, not discharged, so this is **not** a completed proof of
`CaseTwo.SixthMomentMixed`. All seven modules rebuild with strict flags and all
reported proof axioms are standard. Their integration target passes
`lake build --wfail PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Axioms`.
