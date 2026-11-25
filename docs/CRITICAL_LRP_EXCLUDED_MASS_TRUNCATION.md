# Expectation-level finite-truncation assembly of the excluded mass

Accepted from `smwu10gjo/m3` and integrated in `Analysis/Cutoff/Fibre/Expectation/{Defs,Main}.lean`.  This completes the expectation-level input that the pointwise fibre packet deliberately did not provide.

`exclMass_eq_iSup_lintegral_pairIncr` and `exclMass_eq_iSup_lintegral_edgeIncr` identify `E1Sign.exclMass` with the supremum, over finite vertex sets, of the cutoff-law integral of the summed excluded increments.  Measurability of each pair or edge integrand is proved.  The truncation is monotone under finite-set inclusion and directed by union, so `MeasureTheory.lintegral_iSup_directed` genuinely interchanges the finite-truncation supremum with the `lintegral`.  This uses `paperSum_eq_iSup_tsum_pairIncr`/`_edgeIncr` and `PivotFlux.lintegral_paperSum_eq_exclMass`, all unconditionally in `ENNReal`.

`exclMass_eq_iSup_tsum_lintegral_pairIncr` and its edge and iterated forms use nonnegative-series Tonelli to put the expectation inside the sums.  `codeWindow` in the definition layer is an explicit monotone cofinal family of finite vertex windows for any countable vertex type.  It yields the sequential supreme and the honest limits `tendsto_lintegral_codeWindow` and its edge counterpart, plus pointwise convergence to `paperSum`.

Every truncation is bounded by `exclMass`.  `toReal_exclMass_eq_iSup_toReal_codeWindow` is the real version and assumes `exclMass≠⊤`; that finiteness is not derived.  All 43 separate axiom reports used only the standard three axioms in an independently rebuilt snapshot.

This is not a Russo identity, a derivative interchange, a finite large-radius moment, a proof of absolute continuity, or an ODE.  The excluded-mass supremum need not be attained at any finite window.

The subsequent `Fibre/RussoAssembly` package now carries the closed-event real increments into the
same untruncated edge objects. It proves an `ℝ≥0∞` per-edge decomposition of `exclMass`, the
truncated-to-full closed-event limit, and cofinal-window standardized Russo limits with
`exclMass ≠ ⊤` (and the slope sign in the domination statement). See
`CRITICAL_LRP_RUSSO_EXCLUDED_ASSEMBLY.md`. It still does not prove a complete derivative or an
uncapped real full-cluster moment.
