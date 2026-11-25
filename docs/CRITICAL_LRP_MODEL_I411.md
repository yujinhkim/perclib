# Normalized model defect and triangle comparison

`Analysis/Cutoff/Defect/Triangle/Defs.lean` introduces the actual cutoff
two-point function and its open threefold triangle convolution at arbitrary
`SourceNormData`. `Analysis/Cutoff/Defect/Triangle.lean` proves comparisons and
finite-moment reductions; it does not specialize to `linfNorm`.

## First-moment consequences

`E1Sign.cutMoment_two_ne_top_of_one` obtains finite second cutoff moment from
finite first cutoff moment using shift-invariance and the existing
second-moment theorem. Joint window moment and connected moment finiteness
also follow. As a result, the defect sign and excluded-rate estimates from
`Analysis/Cutoff/Defect` have first-moment-only versions.

## Triangle comparison

`E1Sign.cE1_le_windowTriangle` states Lemma I.4.11's upper comparison with the
actual cutoff triangle diagram. `E1Sign.cE1_le_windowOpenTriangle` and
`E1Sign.cE1_le_ballSum_openTriangle` bound the actual defect by the normalized
window sum of the **uncut** critical open triangle, using pointwise domination by
the uncut two-point function. The sign half is included in the corresponding
`cE1_mem_Icc_*` theorems. The underlying abstract comparison is
`I411.lemma_I_4_11_of_finite`; its triangle and excluded-event semantics,
including `apartSet`, are unchanged.

These results require finite first cutoff moment and finiteness of the explicit
windowed triangle diagram. Neither is asserted for every large radius here:
small-radius finiteness is proved separately, while large-radius subcritical
upper bounds and the HD/convolution estimate remain open. The package does not
prove tail decay, a limit for the averaged defect, Cesàro cancellation,
differentiability, an ODE, or Case 3.
