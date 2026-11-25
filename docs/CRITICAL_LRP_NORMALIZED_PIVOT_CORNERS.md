# Normalized pivotal mass at attained radii

`Analysis/Cutoff/OffCorner/NormalizedAggregate/Corner/{Defs,Main}.lean` extends the
normalized-pivot capstone to attained radii. The finite first cutoff moment at a strictly
larger radius remains an explicit hypothesis throughout.

`cutPivotFactorLT r` uses the same `exp (-β_c K s)` normalization as `cutPivotFactor r`
but only for `s < r`. It removes the shell of length exactly `r` while retaining the
theory's closed `s ≤ r` convention at `r` itself. The new definition is isolated in its
own `Defs.lean` and built before the proof module.

The proof gives:

- `tendsto_normalizedPivotMass_nhdsGT`: right continuity at every positive radius, with
  **no off-corner hypothesis**;
- `tendsto_normalizedPivotMass_nhdsLT_trimmed`: the left limit is the genuine infinite
  edge series formed with `cutPivotFactorLT`, not merely a finite-window approximation;
- `normalizedPivotMass_eq_leftLimit_add_shell`: the value at the attained radius is the
  trimmed sum plus the summable activation shell;
- `continuousAt_iff_activationShell_eq_zero`: continuity at the radius is equivalent to
  vanishing of that shell. The name of the trimmed left-limit result is deliberately
  different from the earlier off-corner `tendsto_normalizedPivotMass_nhdsLT`.

The proof uses the existing finite first-moment edge majorant and genuine Tanner
convergence for the entire edge series. It does not use finite-volume replacement of
infinite-volume events. The activation-shell analysis also makes the right one-sided
property independent of the off-corner restriction used by the capstone.

This package does not construct the finite first moment or show that the shell vanishes
at an attained radius. It is a statement about normalized pivotal mass, not a cutoff
mass derivative at an attained radius, a claimed optimum/error in Lemma I.4.1, or a
completion of the paper.

Integration repaired three gaps in the unfinished audit packet: positivity of the
larger comparison radius, the left-limit-target equality, and the joining of one-sided
limits into `ContinuousAt`. The complete corrected modules passed strict focused checks
with only the standard axioms.
