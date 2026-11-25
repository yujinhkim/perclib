# Cutoff first moment as a monotone limit

Source: Definition I.1.5 and the comparison of the cutoff and uncut laws.

`CriticalLRP/CutoffLimit.lean` proves the monotone limit in `ℝ≥0∞`:

```text
sup_{r : ℝ} E_{β,r}|K_o| = E_β|K_o|
lim_{r→∞} E_{β,r}|K_o| = E_β|K_o|.
```

The right-hand side may be `⊤`. In that case these results give divergence to
`⊤`; no unqualified claim about a real-valued derivative or finite real limit is
made. The uncut infinite-mean premise itself is explicitly required for the
divergence corollary and is not manufactured from criticality.

## Proof method

`CountableProduct.Marks` provides a common law on uniform edge marks. Every
connection is witnessed by a finite path. If edge probabilities increase
pointwise to a limit, finitely many strict mark inequalities therefore hold
simultaneously at some finite index. This proves saturation of the mark
preimage of the connection event, hence continuity from below of connection
probabilities.

The final moment identity follows by Tonelli through the cluster-volume sum of
connection probabilities and commutation of the monotone supremum with `tsum`.
The helpers include `iSup_measure_iUnion`, `iSup_finset_sum_of_mono`,
`iSup_tsum_of_monotone`, and `iSup_lintegral_clusterVol_real`.

`lintegral_clusterVol_cutoff_le` proves domination by the uncut law for every
radius. Conversely, `le_of_forall_lintegral_clusterVol_cutoff_le` transfers a
uniform-in-radius bound back to the uncut mean. This does not produce such a
uniform bound, but identifies exactly how it would give finiteness.

## Source-model fidelity and non-vacuity

The cutoff is the loop-safe `CutoffKernel.cutoffSymKernel`; diagonal pairs are
zero. The uncut profile kernel uses the same factor `K 0 = 0` on the diagonal.
The proof does not use `cutoffPiFamily` or its false hypothesis on loop-carrying
`Sym2` edges, documented separately in `CRITICAL_LRP_MONOTONE.md`.

The hypotheses are antitonicity on `(0,∞)`, pointwise nonnegativity, `K → 0` at
infinity, and `K 0 = 0`. They require no derivative or moment estimate.
`modelProfile_hypotheses` discharges them for `r^{-(d+α)}` when `d+α > 0`, and
`iSup_lintegral_clusterVol_cutoff_modelProfile` gives the corresponding source
power-law identity. This is not an empty profile proposition.

The moment divergence does not prove sharpness, a radius bound, a finite
critical-mean input, or a derivative in the radius. Instructions converting to
`toReal` must still establish finiteness at each relevant radius and any
uncapping needed for differentiation.

## Arbitrary source norms and the genuine `M.cutMoment`

`MomentMonotonicity/SourceModelCutoffLimit.lean`, from independent audit
`smwp7ai5u` and recompiled during integration, derives the tail hypothesis
inside `SourceModelData` rather than leaving it as an input.  The normalization
error is eventually at most `2 r^{-d-α-1}` in absolute derivative form.  This
first proves integrability of `|deriv K|` on a tail; then `K_eq_integral` bounds
`K(r)` by `2 r^{-(d+α)}/(d+α)`, giving `SourceModelData.tendsto_K_atTop_zero`.

The `cutRadialSym` engine proves convergence of cutoff connection
probabilities, every natural cluster moment, and the positive/negative cutoff
monotonicity cases at arbitrary admissible norms.  In particular,
`SourceModelData.iSup_cutMoment_eq`,
`SourceModelData.cutMoment_monotone`, and
`SourceModelData.tendsto_cutMoment` hold at `M.betaCrit` with allowed value
`⊤`.  Fixed-cutoff moments dominate neither their own finiteness nor a uniform
bound; `uncutMoment_ne_top_of_forall_cutMoment_le` still takes that uniform
bound as an explicit premise.  A concrete model witness and a normalized flat
norm witness are checked.

The separate `MomentMonotonicity/StrictCutoffEpsilon.lean` now proves the strict
positive epsilon coefficient.  The historical `J(0⁺)` rationale has been
replaced by an attained positive lattice-distance lower bound and a proof that
the profile is positive at every positive argument.  This gives stochastic
domination at the reduced parameter, including no infinite cluster when
`β_c > 0`.  It still produces no finite-moment or uniform-moment bound.
See `docs/CRITICAL_LRP_STRICT_CUTOFF_EPSILON.md`.

## Natural powers and the I.4.g7 comparison

`MomentMonotonicity/CutoffMomentConvergence.lean` extends the method from the
first moment to every natural power.  It first proves the cluster-volume
supremum identity directly on the common mark space, then integrates powers by
monotone convergence.  Thus the supremum and extended-real limiting identities
above hold with `|K_o|` replaced by `|K_o|^q` for every natural `q`, including
the case `⊤`.  Monotonicity in the cutoff radius and the one-sided uncut bound
hold at the same orders.  A finite bound uniform in `r` would transfer to the
uncut moment, but no such bound is proved here.

The raw sup-norm module's `cutoff_mono_beta_and_le_uncut` assembles the two
stochastic comparisons `P_{β,r} ≤ P_{γ,r} ≤ P_γ` for `β ≤ γ`, their all-natural-
moment consequences, and the corresponding two-point comparisons.
`MomentMonotonicity/SourceModelMoments.lean` proves the corresponding statement
for `SourceModelData` at an arbitrary admissible norm, and is the provider for
`hutchcroft.i.4.g7`.  This discharges that specific comparison gap, not the
uncut two-point estimate of Theorem I.2.13, finite critical moments, or the
separate `i.4.g6` sharpness/radius step.

## Verification

The integrated module passes focused compilation with warnings treated as
errors. All 40 audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Local validation, not upstream CI.
