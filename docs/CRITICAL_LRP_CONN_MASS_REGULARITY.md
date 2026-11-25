# Connected window-mass radius regularity

Accepted from `smwu10gjo/m2` and integrated in `Analysis/Cutoff/ConnMassRegularity/{Defs,Main}.lean`.  This is the moving-window `connMass` theorem; it does not claim continuity for `pairMass`, `exclMass` or `cutE1`.

`connMass_le_cutMoment_three` and its strict-window analogue bound the connected window mass by the third root-cluster moment, because the window indicator count is at most the cluster volume.  This is a pointwise mark-space bound and requires no moment-existence theorem.

`tendsto_connMassReal_nhdsGT` proves right continuity at `r0>0` from `cutMoment 3 r1 ≠ ⊤` at one larger radius `r1`.  Off the box-change and escape events, the connected clusters at `r` and `r0` are proved equal.  The remaining contributions are the spatial annulus and the two bad-mark cube terms.  The finite-window annulus vanishes by antitone `lintegral` convergence, while the latter use the established third-power box and escape regulations.

From the left, `iSup_connMass_nat` and `tendsto_connMassReal_nhdsLT` give the limit **`connMassLt`**, computed with the strict window `ρ<r0`, not unconditionally the closed-window `connMass M r0`.  `connMass_eq_connMassLt_add_sphereMass` is the exact decomposition.  Left and two-sided continuity use `sphereMass=0`, supplied by the explicit condition `∀y, S.ρ (toVec y)≠r0`; `continuousAt_connMassReal` retains that condition and the finite larger third moment.

The proof statements were unchanged during integration.  Duplicate module documentation was removed, and a prose-only overstatement was corrected to match the actual sufficient no-sphere condition.  Fresh strict `Main` and production `Defs`/`Main` builds reported only the standard three axioms.  No third-moment existence at large cutoff, unconditional left continuity, derivative, or `cutE1` continuity result is established.