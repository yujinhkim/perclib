# Exact FTC / Cantor defect of the cutoff increment

`Analysis/MonotoneStieltjes.lean` proves the general Lebesgue decomposition of a
monotone right-continuous Stieltjes increment. `Cutoff/CantorPart/Defs.lean`
clamps the real cutoff mass to a compact radius window and defines its actual
Stieltjes function, measure, and singular (Cantor) part. The companions
reexport those definitions and prove the clamp's monotonicity, continuity,
agreement, and derivative agreement.

The main identity on every window with finite cut mass at a larger radius is
`χ(b)-χ(a) = (CantorPart (Ioc a b)).toReal + ∫_[a,b] χ'`.
The iff version says that the FTC holds exactly when this singular part
vanishes. Absolute continuity forces that part to vanish, and atoms have zero
mass because continuity of the clamp is proved. Arbitrary representatives of
χ' may be inserted in the same decomposition.

This is not an assertion that the Cantor part vanishes at criticality, nor that
zero singular part alone gives a stronger differentiability theorem. When a
flux identity is known only almost everywhere, increment preservation requires
precisely the singular part to vanish. The remaining standardized Russo
interchange and the absolute-continuity work therefore still have distinct
model obligations.
