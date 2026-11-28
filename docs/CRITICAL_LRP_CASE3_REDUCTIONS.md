# Case-3 source-input reductions

This note records the `smwzlje3f` integration at production base
`a59bc6c22aba42e69160666c17feac870d4cb887` and its independent review. The
paper is **not** completely formalized. Compilation and an axiom audit do not
supply the remaining model hypotheses, nor do they establish source fidelity by
themselves.

## HD(3) gives the finite triangle and logarithmic tail

`Analysis/SecondMomentCase3/TriangleFromHD` supplies a model-side proof of the
two convolution stages in the proof of Lemma I.4.3. From the literal third
alternative of (HD), namely `d = 6`, `α = 2` and the stated log-corrected
critical two-point upper bound, it proves:

* a real majorant for the origin two-point profile, using `τ ≤ 1` near the
  origin rather than applying the printed logarithmic bound where its
  totalized logarithm is nonpositive;
* `exists_tauConv_bound`, the strict convolution case `2 + 2 < 6`, and
  `exists_tauConvConv_bound`, the marginal case `2 + 4 = 6` with logarithmic
  exponents `1 + 2 > 1`;
* `openTriangleSelf_lt_top_of_case3`, the finite triangle at the origin;
* `logRadialBound_openTriangle_of_case3`, the (I.4.13) logarithmic decay with
  exponent two at the model's own normalized source norm; and
* `isLogErrorFunction_nablaTail_of_case3`.

The conversion to `ℝ≥0∞` is summability-gated: no unproved interchange of sums
or identification of a non-summable `tsum` with the open triangle is used.
`secondMoment_asymptotic_case3_of_case3HD` and its three companion wrappers
therefore remove `hTri` and the pointwise `hF` from the earlier interface, but
retain `Case3HD` and all the other moment and analytic inputs. `Case3HD` is not
instantiated here. This does not prove the lace-expansion estimates or any
unconditional statement about the canonical critical law.

## Tail-only second-moment route and the cubic connector

`RadialRegularity/TailRoute` separates the two uses of the pointwise bound. Only
vanishing of `∇_r` is needed to construct the repaired polygon bundle. Lemma
I.4.19 and integrability of the negative power penalty then give the driver's
logarithmic integrability from that of `∇_r`. Consequently
`secondMoment_asymptotic_case3_of_source_of_logTail` removes the pointwise `hF`
as well as the wrapper's radius AC/AE, first-moment finiteness and error
measurability bookkeeping inputs. It still requires tail second-moment
finiteness, the first-moment limit, finite triangle, `IsLogErrorFunction ∇_r`,
the first-moment error data and the moment gap.

`case3_moment_three_asymptotic_of_HD_case3_no_hRV2` uses the regular-variation
conclusion of that Case-3 chain at the `p = 3` second-induction interface of
I.4.20. This is an assembly of conditional results, not a proof of I.4.20. Its
original higher-moment derivative, normalization and other model inputs remain
explicit.

## Finite-moment and ambient bookkeeping

`FiniteMoments` proves that the first-moment limit `hP` yields a uniform lower
comparison and finiteness of the cutoff first moment at every positive radius.
The already-proved all-order ordinary moment bound then gives every finite
order; radius monotonicity and the same bound convert the existing `h2`/`hfin`
interfaces to the root-moment range used by I.4.20. These are not uniform upper
bounds on the critical first moment and do not prove subcritical sharpness.

`AmbientParameters` derives the positivity/nonvanishing parameters from the
existing normalization or two-point lower bound, proves global measurability of
the real shadow of each monotone cutoff moment without a finiteness premise,
and turns a positive power-law limit into regular variation. Its consumer
wrappers preserve the remaining hypotheses and conclusions. The separately
submitted explicit-witness convenience wrapper was not integrated because it
adds no substance beyond these general reductions.

## The exact role of the uncut critical tail

`CriticalVolumeTail/Defs` names the uncut, infinite-lattice hypothesis

```text
∀ n ≥ 1, P_{β_c}(|K_0| ≥ n) ≤ C / sqrt n.
```

It derives the same pointwise envelope from the summatory form used in the
paper's optimization, and obtains the moment gap with explicit constant
`(4C+1)⁻³` when the relevant cutoff second moment is finite. `Main` adjusts the
old finite-moment threshold and replaces `hgm` by this cited tail input in four
conditional consumers.

The tail theorem itself is **not proved**. The implication from a tail
asymptotic is conditional on that asymptotic and imports none of the
quarantined `DRAFT_SORRY` anchors. The summatory-to-pointwise implication is not
an exact necessity/minimality theorem. No bound on a cutoff tail is promoted to
the uncut tail. The supplied paper cites this bound at p. 47 to its references
[12] and [75], rather than proving it there; see `docs/CITED_INPUTS.md`.

`MomentGapAudit` records the distinction between the one-sided moment gap and
regular variation, the exact normalization of its constants, and the circularity
of trying to derive it from a positive-limit version of the desired conclusion.
Its seven-input wrapper is an audit of that earlier signature, not a proof that
those seven inputs are independent, jointly satisfiable, or a minimal current
frontier after the other reductions above.

## Product gap and covariance are separate

`QZeroRepairAudit/ProductGap` proves `HasProductGap M 1 2` from the established
`(2,1)` display at the swapped pair, with finite first cutoff moment, and from
`hP` after deriving that finiteness. The additive repair therefore retains only
its genuine covariance input `HasCovBound` (alongside the second/third-moment
finiteness in that wrapper). It does **not** prove `HasCovBound`, revive the old
all-vertex two-term star or complete another Case-3 numerator proof.

`QZeroRepairAudit/I420Consumer` also preserves checked variants of the cubic
and asymptotic consumers with `hRV2` derived from the product-gap chain. These
are conditional interface reductions, with all other original inputs retained.

## Validation and remaining scope

Every submitted module was rebuilt independently against the production base
with `-DwarningAsError=true`, `-DautoImplicit=false` and the Mathlib standard
linter set. All reported exported axioms were restricted to `propext`,
`Classical.choice` and `Quot.sound`. The integrated target was then checked with

```sh
lake build --wfail PercLib.CriticalLRP.Analysis.SecondMomentCase3.Audit
```

On the integrated working tree at base `a59bc6c`, the full `lake build --wfail`
and whole-production axiom audit passed with no nonstandard axiom and no
`sorryAx`. The foreground wrapper then reached its time limit, so the remaining
checks were rerun separately and passed: the Python test suite,
`check_semantic_closure.py`, `check_source_restitution.py`, and
`check_import_closure.py PercLib --exclude-quarantined`. Python's deliberate
open-input I.4.1 fixture prints `FAILED` before testing the expected
`OPEN_DECLARED_PROOF_INPUT` verdict; the test suite itself ends in `OK`.

The remaining work includes instantiating HD/other source hypotheses, the uncut
critical tail, the covariance input where that optional repair is wanted, the
remaining first-moment/continuity data, the other cases of I.4.15/I.4.20, and
large parts of the rest of the paper. No finite-torus result is used as an
infinite-lattice theorem, and no `sorry`, custom axiom or hidden premise is
introduced by these reductions.
