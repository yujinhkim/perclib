# Lemma I.5.6: why the second-driver comparison matters

The existing `lemma_I_5_6_of_errors` and `lemma_I_5_6_log_of_errors`
explicitly use a measurable second error tending to zero. The source proof's
`δ₂ ≡ 0` step must not be encoded as an unsupported proposition that an
arbitrary regularly varying replacement driver may be discarded without
comparing its divergent integral against the original driver's integral.

`Lemma_I_5_6_Driver` supplies the corresponding positive interface.
`lemma_I_5_6_of_driver` and its logarithmic corollary absorb a replacement
driver H when H/h tends to one; its ratio of divergent interval integrals
therefore tends to one as well. The earlier two-error theorems are recovered
as consequences (`lemma_I_5_6_of_errors_of_driver` and its log form), with a
standalone audit certifying the same conclusions. This is a second-driver
replacement, not an assertion that the second error is absent.

`Analysis/Lemma_I_5_6_Obstruction` proves the following negative statement in
Lean. Take `a=1`, zero homogeneous error, `h(r)=r`, `H(r)=2r−3`, and
`f(r)=2r log r + 3`. Then

- `HasDerivAt f f'` holds with `f'r = 2 log r + 2`;
- `f'r = (f(r) + H(r))/r`;
- `f`, and eventually `h` and `H`, are positive; `h` and `H` are regularly
  varying of index one;
- `h/r` and `H/r` are both not logarithmically integrable.

Even though the logarithmic-integrability classes agree, the normalised
solution `f(r) / (r * ∫ s / s²)` tends to `2`, not `1`. The same comparison
fails for every positive starting point. Regular variation of index `a` plus
coincidence of logarithmic-integrability classes is insufficient to force the
expected limiting ratio. The divergent-integral comparison — or a driver
ratio tending to one — is a real requirement.

This is a precise obstruction to an over-broad weakening of the
second-driver interface, not a blanket refutation of Hutchcroft's Lemma I.5.6
or of its intended vanishing-second-error argument. Independently rebuilt
under the strict settings with only standard axioms.
