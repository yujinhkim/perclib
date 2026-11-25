# Interval absolute continuity for cutoff mass

`Analysis/Cutoff/IntervalAC/Defs.lean` defines the real cutoff mass and its
normalized-norm corner radii. `Analysis/Cutoff/IntervalAC.lean` proves ordinary
analysis in `IntervalAC` before applying it to the actual source mass.

## What is proved

For a continuous function on a closed radius interval, differentiability and a
bounded derivative off an arbitrary finite exceptional set, with a **continuous**
majorant `g`, the file proves
`|f(y)-f(x)| ≤ ∫[x,y] g`. It then derives absolute continuity, a full
fundamental-theorem identity for the derivative, and almost-everywhere
differentiability. The finite set is split explicitly; there is no derivative
claim at a corner and no AC hypothesis smuggled into the premises.

The monotone layer only assumes finiteness at the right endpoint. It gives a.e.
differentiability within the interval, interval integrability of `deriv`, and
`0 ≤ ∫ deriv ≤ χ(b)-χ(a)`. The elegant one-sided integral inequality is not
turned into an equality and monotonicity is not confused with AC.

## Inputs still needed for the source model

The AC layer retains continuity of the real cut mass, finiteness of the corner
set on the interval, the actual off-corner derivative bound, and a continuous
majorant. It does not derive any of these from finite-box results. A measurable
but non-continuous log-error factor or ordinary normalized-norm support does
not satisfy that majorant premise by assertion. Arbitrary normalized norm corner
finiteness remains separate from the sup-norm `edgeLen` example.

The artifact was recovered from the closed, unfinished Ultramath `smwtqkdul` d4
and independently compiled and axiom-audited: 18 theorem reports use only
`propext`, `Classical.choice`, and `Quot.sound`.
