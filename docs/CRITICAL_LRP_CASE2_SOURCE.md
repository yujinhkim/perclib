# Case 2 of I.4.15: the error bound and its sixth-moment input

`Analysis/SecondMomentCase2/Source/Defs.lean` proves the Case-2 error estimate
of Proposition I.4.15, not the full second-moment asymptotic proposition. The
condition is the source's `d = 3α` with `(Hydro)` and first-moment asymptotic.

## Checked estimate

The package identifies the source numerator with the actual cutoff-window
third-moment integral and applies Cauchy–Schwarz, yielding

```text
E_{2,r} ≤ √(945 C₁) · (E|K|)² · √M_r / |B_r|.
```

The cancellation of `(E|K|)²` is exact. At `d = 3α`, the source's tightness and
hydrodynamic terms yield `E_{2,r} → 0`. The proof establishes the explicit
prefactor `√(945 C₁) (2α/β_c)² 2^d` in the `(9α−3d)/4` estimate.

Universal tightness is implemented with its actual constant
`Tightness.momentConst 1 1`, via `interSecond_le_edian` and the equality
`Mr_eq_edianMaxVol`. The landed older constant-free tightness premise is a
stronger assumption than what Corollary I.2.5 directly supplies; it is not used
as if it were free.

## Exact remaining input

The capstone `p2ExclError_tendsto_zero_of_caseTwo'` keeps:

* `d = 3α`, positive normalizing constant, the first-moment asymptotic `hP`,
  and `Hydro M`;
* eventual finiteness of the second cutoff moment; and
* the mixed sixth-moment inequality eventually:
  `E|K|⁶ ≤ 945 (E|K|²)² (E|K|)⁵`.

`SixthMomentMixed` names the stronger all-nonnegative-radii form, at `p=6,k=2`
of Lemma I.4.16. This mixed generalized tree-graph input is **not proved**.
The ordinary sixth-moment bound with the eleventh power of the first moment is
not sufficient for this Case-2 exponent. Tightness is discharged, not replaced
by that missing moment estimate.

The immediately preceding "only remaining input" statement concerns the
original error-bound package, not subsequent composition into the radius ODE.
Nothing here proves I.4.20, HD(3), an uncut tail or a critical first-few
moments theorem. This package is a public Lean module, so its capstone and
named residual can be consumed downstream. Its focused build and axiom audit
use only the standard three Lean axioms for proof-producing theorems.

## Subsequent regular-variation assembly

`Analysis/SecondMomentCase2/RegularVariation.lean` now composes the error bound
with the existing ODE machinery. Under the first-moment asymptotic `hP`,
`Hydro`, the Case-2 dimension identity, and the same mixed sixth-moment input,
`regularlyVarying_two_of_caseTwo` proves regular variation of index `3α` for
the second cutoff moment. Its `of_hP` / `of_sixthMomentMixed` forms delete
separate first- and second-moment finiteness hypotheses using the generic
first-moment transfer. Versions in the higher-moment `momOf` spelling, a
slowly varying ratio `mom₂/(mom₁)³`, and the corresponding moment packet are
also proved.

The remaining radial obligation is made exact by `forall_identity_of_hac_hae`:
absolute continuity plus the a.e. identity is equivalent to the integrated
primitive identity whose interval-integrability side condition is provided by
`regularlyVarying_two_of_caseTwo_of_integrated_identity`'s `hint`. This is a
reduction in stated form, not a proof of the open interchange.

A positive power-law limit is **not** claimed from Case 2 alone.
`tendsto_div_two_of_caseTwo_of_hP` additionally assumes
`LogarithmicallyIntegrable M.p2Ebar`. The abstract counterexample
`exists_ode_regularlyVarying_not_sharp` uses `f(t)=t/log t` and `E(t)=1/log t`
to show exactly why vanishing ODE error gives regular variation but not a
positive limiting constant. This example concerns the ODE, not a claim about
the percolation model. The integrated target passes
`lake build --wfail PercLib.CriticalLRP.Analysis.SecondMomentCase2.RegularVariation`;
all 14 of its axiom reports are standard.
