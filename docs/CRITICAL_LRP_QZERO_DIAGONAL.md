# The root obstruction to the full `p = 3, q = 0` two-term gap

## Exact result

`Correlation.I417.General.QZeroDiagonal` proves two distinct things:

1. under the explicit `QZeroDiagInputs` hypotheses, the full per-vertex
   two-term `hgap` has no constants `C₃,C₄ ≥ 0` for which it can hold at
   every radius and vertex; and
2. the root-stripped per-vertex form `HasRepairedPerVertexHgap` has the
   actual off-diagonal numerators, and `windowSum_le_of_repaired` isolates
   the exact diagonal contribution and puts the remaining vertices in the
   standard diagonal-dominant form.

The first is a conditional source contradiction, not a refutation of
Proposition I.4.15 or I.4.20. The second is only a consumer theorem: it does
not supply the off-diagonal estimate itself.

## Why the root defeats the full target

Unconditionally, `connCubeVertexMass r 0 = cutMoment 3 r`: the cluster always
contains its basepoint. The window includes that point whenever `r ≥ 0`
(`zero_mem_ballF`). The target left-hand side at the root is therefore a third
cutoff moment, not merely another generic polygon entry.

With the cutoff `PowerInputs`, the triangle/diagonal controls say

```
T³(0,0) ≤ ∇,    T⁴(0,0) ≤ ∇ χ.
```

So the target's right side at the origin is at most `(C₃+C₄)∇χ⁴`. In contrast,
`QZeroDiagInputs.third_lower` requires `cutMoment 3 ≥ c χ⁵` eventually, and
`chi_unbounded` requires arbitrarily large χ. Consequently the target would
force the impossible fixed-constant relation `c χ ≤ (C₃+C₄)∇` along an
unbounded sequence.

`fourDiag_le_triSelf_mul_chi` proves the second control directly by
composition and the triangle bound. `diag_inequality`,
`diag_contradiction`, `not_hasPerVertexTwoTermHgap`,
`no_perVertex_twoTerm_constants`, `not_windowGap`, and
`no_windowGap_constants` turn it into the exact negation of the full target
and of the older window hypothesis used by the original consumer.

The structure `QZeroDiagInputs` makes its further premises explicit:
`PowerInputs`, `chi_one_le`, `chi_unbounded`, and `third_lower`. The latter two
are the relevant Case-3 growth statements, including the source's intended
third-moment comparison via Proposition I.4.20 and the second-moment lower
comparison. **No non-vacuity derivation of that entire input package is
claimed by this packet.** It must not be used as an unconditional model
counterexample, and it does not license inventing those bounds.

## The allowed repair

`HasRepairedPerVertexHgap C₃ C₄` is the two-term estimate restricted to
`y ≠ 0`. Given that off-diagonal estimate, `windowSum_le_of_repaired` proves,

```
(connCubeMass r).toReal
  ≤ (cutMoment 3 r).toReal
    + |B_r| * (C₃ T³(0,0) χ⁴ + C₄ T⁴(0,0) χ³),
```

for `r ≥ 1` with finite first cutoff and connected third-window moment.
The proof removes and reinserts the root summand explicitly; the hypotheses on the remaining
vertices preserve their actual source shape. All required cutoff/window finiteness assumptions
stay visible rather than being inferred from `⊤`-to-real conventions.

In the Case-3 growth regime the isolated third moment has the expected
`χ⁵` comparison rather than being thrown into the `ell = 1,2` tree classes.
The source's normalization comparisons are intended to absorb this isolated
quantity via `χ ≤ |B_r| ∇`, giving `χ⁵ ⪯ |B_r|∇χ⁴`. That absorption is a
separate model/scale argument; it is not a proof of an off-diagonal tree
bound, nor an assertion of a finished normalized Case-3 asymptotic.

Thus the correct remaining per-vertex question is the **off-diagonal**
`HasRepairedPerVertexHgap`, not the old full-`y` hypothesis. The repair
requires root-split assembly together with the already proved windowed
polygon drivers. The accepted old conditional wrappers remain in the
historical record with their old assumptions; none of them establishes the
full proposition under the source's current open inputs.

## Relationship to the tree-atlas findings

An independent atlas check found an `ell = 2` class in the one-copy
seven-edge expansion. That makes an `ell ≥ 3`-only truncation invalid as
a generic unconditional argument from tree enumeration alone. A two-copy
`q ≥ 1` marked vertex provides the extra source-level mechanism that removes
the small path classes; there is no corresponding arm at `q = 0`. This does
not prove that every off-diagonal statement fails, but it means the old claim
cannot be repaired by deleting those diagram classes without an exact event
cancellation.

The root obstruction is stronger and more model-specific: under the explicit
Case-3 third-moment/growth inputs it rules out even a claimed solution of the
two-term bound via a source-wide arithmetic comparison. It therefore changes
the mathematical target rather than being only a choice of proof technology.

## Verification

The definitions, negative proof and repaired window inequality were
independently rebuilt under strict Lean warnings, no auto-implicit declarations
and the mathlib lint set. The twelve audited exports depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Production integration adds
the modules and their key capstones to the Case-3 axiom wrapper. No new axiom
or hidden assumption is used to manufacture the missing off-diagonal estimate.
