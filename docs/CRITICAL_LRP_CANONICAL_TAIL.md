# Canonical cluster tails and susceptibility

`Analysis/SecondMomentCase3/CriticalVolumeTail/CanonicalTail` proves the
integer-valued layer-cake identities at the canonical model law `M.law β`. It
uses `clusterVol`, not a finite graph surrogate, and does not assume a triangle
condition or a finite critical mean.

For `lawTailAt β k = P_β(|K_0| ≥ k)` in `ℝ≥0∞`, the main identities are

$$χ_β = ∑_{k≥1} P_β(|K_0|\ge k),$$

and

$$E_β[|K_0|\wedge n] = \sum_{k=1}^{n}P_β(|K_0|\ge k).$$

The module also proves `χ_β = sup_n E_β[|K_0| ∧ n]`, the finite-tail bound
`∑_{k≤n} P_β(|K_0| ≥ k) ≤ χ_β`, and Markov's inequality
`n P_β(|K_0| ≥ n) ≤ χ_β`, all without a finiteness hypothesis in `ℝ≥0∞`.
The corresponding real-valued forms explicitly assume `χ_β ≠ ⊤`; this premise
cannot be dropped because `(⊤ : ℝ≥0∞).toReal = 0`. Finite susceptibility gives
summability of the real tail series and its exact sum.

Integer-valuedness is necessary for the general counting identity. For
example, on a probability space with `f ≡ 1/2`, its integral is `1/2`, whereas
`∑'_{k : ℕ} P(k < f) = 1` because only the `k = 0` term is nonzero. The
definition `LayerCake.IntValued` therefore retains the exact `ℕ∞`-image
hypothesis rather than asserting a formula for arbitrary nonnegative reals.

## Cutoff and finite-window forms

The cutoff statements identify `M.cutMoment 1 r` with the tail series at
`M.cutLaw r`, prove its truncation, and derive the real finite-tail bound under
`M.cutMoment 1 r ≠ ⊤`. These match the layer-cake step in Proposition I.4.15,
Case 3 of arXiv:2508.18807v1, without proving its volume-tail envelope.

For a monotone exhaustion `F n` in which every finite vertex set is eventually
contained, the module proves

$$P_β(|K_0|\ge k) = \sup_n P_β(|K_0\cap F_n|\ge k)$$

and `χ_β = sup_n E_β|K_0 ∩ F_n|`. It furthermore identifies susceptibility
with the two-point row sum `χ_β = ∑_y τ_β(0,y)` and checks the exact value
`χ_0 = 1` as a nonvacuity test.

## What remains open

This closes the infinite-susceptibility layer-cake input isolated in
`Entropy/TailAssembly`. It does **not** prove the transcript entropy limit,
the canonical cluster-event/revealment compatibility,
`TwoIntensityTailComparison`, `SusceptibilityBound`, the `n^{-1/2}` critical
tail, or the paper's higher-moment estimates. It also does not bridge the
separate finite-edge-set `TreeGraph.clusterF` formalism to `clusterVol`.
