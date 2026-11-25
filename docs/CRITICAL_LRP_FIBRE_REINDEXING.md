# Finite-fibre reindexing of the excluded increment

Accepted from swarm `smwtzmkep`, member `m4`, and integrated at this branch's current production revision.  The modules `Analysis/Cutoff/Fibre/{Defs,Reindex,Full,Truncation,Limit,PaperSum,PaperSumLimit}.lean` relate the model's standardized excluded increments on ordered pairs to those on unordered edges.

For every finite window, `sum_pairIncr_eq_sum_edgeIncr` and its untruncated analogue sum explicitly over the one-element diagonal and two-element non-diagonal fibres of `s(x,y) : Sym2 V`.  The cofinality results `tsum_pairIncr_eq_tsum_edgeIncr` and `tsum_pairIncrFull_eq_tsum_edgeIncrFull` lift these finite identities to `tsum`, including infinite sums without finite-moment hypotheses.  A filtered version removes the zero loop terms.

`pairIncrFull_cutDist_eq_pivotWeight` identifies the untruncated ordered-pair increment with the paper's pivotal weight at the source model's cutoff distance.  Consequently, `paperSum_eq_tsum_pairIncrFull` and `paperSum_eq_tsum_edgeIncrFull` identify `PivotFlux.paperSum` with the corresponding untruncated sums.  `sum_pivotWeight_eq_sum_edgeIncrFull` is the finite-window version.

The truncation results are exactly integrand-level: `iSup_pairIncr_eq_pairIncrFull`, `iSup_tsum_pairIncr_eq_tsum_pairIncrFull`, and their edge analogues write the untruncated increments as suprema over finite vertex truncations.  Hence `paperSum_eq_iSup_tsum_pairIncr` and `paperSum_eq_iSup_tsum_edgeIncr` express the paper's double sum as a supremum of the model's summed excluded increments.

These are pointwise `ENNReal` computations.  They do **not** prove monotone convergence under `M.cutLaw`, a Russo or derivative interchange, a finite large-radius moment, or an ODE.  Expectation-level assembly must still use `lintegral_paperSum_eq_exclMass`; no such assembly is claimed in these pointwise modules.

The separate `Fibre.Expectation.Main` module subsequently proves the unconditional `ENNReal` expectation/truncation identities and sequential limit using `lintegral_paperSum_eq_exclMass`, measurability, directed monotonicity and Tonelli (see `CRITICAL_LRP_EXCLUDED_MASS_TRUNCATION.md`).  It still supplies no derivative, moment existence, or ODE.  The integrated edge increment is standardized (`p = 1`), not the raw Russo coefficient without its support and resampling treatment.
