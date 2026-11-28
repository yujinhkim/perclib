# Proposition I.4.15, Case 1, from Proposition I.4.2

`Analysis/SecondMomentCase1/Source` integrates `smwznoz6j` member m4 at
production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`. This is a
source-facing **conditional** assembly, not a proof of Proposition I.4.2 or of
the whole of Proposition I.4.15.

## Exact main statements

For `0 < α` and `3α < d`, assume the literal cutoff first-moment limit

```text
hP : E_{β_c,r}|K| / ((α/β_c) r^α) → 1.
```

Then `regularlyVarying_two_of_caseOne_source` proves that the second cutoff
moment is regularly varying of index `3α`. This first clause requires no
log-integrability hypothesis.

With `hHlog : LogarithmicallyIntegrable M.p2H` as well,
`tendsto_div_two_of_caseOne_source` produces a positive `A` and proves
`(E_{β_c,r}|K|²) / r^(3α) → A`. The two results are paired by
`propositionI415_caseOne_source`. Here `p2H` is the actual normalized
first-moment error `(E|K| / ((α/β_c) r^α)) − 1`, not a renamed target.

The prior Case-1 radius-AC/AE, first/second-moment finiteness, error
measurability, `β_c`, normalizing-constant and `E₀` hypotheses are discharged by
the already-proved generic radial and moment modules. No triangle condition,
HD(3), Case-3 polygon hypothesis or Case-3 moment gap is assumed. The similarly
named `SecondMomentCase3` libraries are used only for their generic radius and
moment facts.

## One-sided rate and two-sided comparison

`FirstMomentUpperAt C` names the eventual bound `E_{β_c,r}|K| ≤ C r^α`. The
Case-1 error rate is proved from this one-sided input as
`15 C³ 2^d r^(3α−d)`, together with its vanishing and logarithmic integrability.
At the constant produced by `hP`, this recovers exactly the earlier
`15 · 8 · (α/β_c)³ · 2^d` constant.

`exists_cube_comparable_of_caseOne_source` proves positive eventual upper and
lower comparisons between `E|K|²` and `(E|K|)³`. It uses the first-moment limit
and the already-proved positive power-law limit of the second moment, not bare
regular variation and not Jensen alone. Correspondingly,
`momentGap_of_caseOne_source` derives the Case-3-style one-sided moment gap in
Case 1; it does not derive that gap in Cases 2 or 3, nor avoid the uncut critical
tail needed in Case 3.

## Residual scope and validation

The open model inputs remain `hP` and, for the sharp-limit clause and cube
comparison, `hHlog`: the two relevant assertions of Proposition I.4.2 in Case 1.
No proof of those assertions, Cases 2/3 of I.4.15, I.4.20, `HasCovBound` or the
uncut critical volume tail is claimed.

The candidate was independently elaborated with strict flags at the base above;
all 18 axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.
The integrated target passes

```sh
lake build --wfail PercLib.CriticalLRP.Analysis.SecondMomentCase1.Source.Audit
```
