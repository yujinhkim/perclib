# Local regularity of the open-triangle tail

`Analysis/LogTailLocal/Defs.lean` introduces source-style bounds on positive
compact intervals and explicit local source-log predicates.
`LogTailLocal/Core.lean` proves integrability of antitone real functions and of
finite extended-real-valued antitone tails.
`LogTailLocal/Source.lean` applies these to the source `nablaTail`;
`Assembly.lean` joins it with the existing global logarithmic-tail results.

The local statements cover integrability of the tail and of its logarithmic
density on each compact positive interval, local boundedness, and the improper
integral as a limit of interval integrals. They follow from finiteness at the
left endpoint, not from global tail decay. The pointwise logarithmic and
polynomial decay inputs remain explicit.

The `invSpike` counterexample vanishes in the far tail while having a genuine
polar singularity at `1`. It satisfies the repository's old global predicate
but fails local integrability and boundedness, showing why the added local
clauses matter.

This does not prove the HD/convolution estimate, the model Gram factor, or tail
control at criticality. It supplies the separate local clause omitted by the
repository's original `LogarithmicallyIntegrable` definition.
