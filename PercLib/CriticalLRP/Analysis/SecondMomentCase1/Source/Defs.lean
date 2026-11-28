/-
Ultramath swarm `smwznoz6j`, member `m4`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m4.
Production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`; reviewed scratch source `.scratch/review-smwznoz6j/m4/Defs.lean`.

# Case-1 first-moment inputs of Proposition I.4.15: named one-sided bound

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 1 (`d > 3α`), p. 44:

```
  E_{β_c,r}[|K|³ |K ∩ B_r|] ≤ E_{β_c,r}[|K|⁴] ⪯ E_{β_c,r}|K|² (E_{β_c,r}|K|)⁴,
  so that   0 ≤ E_{2,r} ⪯ (E_{β_c,r}|K|)³ / |B_r| ⪯ r^{3α-d}
```

Every `⪯` in that display is an *upper* bound: the Case-1 chain uses only
`E_{β_c,r}|K| ≤ C r^α` for some constant `C`, not the two-sided first-moment
asymptotic `E_{β_c,r}|K| ~ (α/β_c) r^α` of Proposition I.4.2.  This file names that
weaker input, so that the Case-1 decay and logarithmic integrability of `E_{2,r}` can be
stated from it, with the constant `C` explicit and no reference to `β_c`.

Definitions only; no theorem is stated here.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1

/-! # The one-sided first-moment upper bound `E_{β_c,r}|K| ⪯ r^α` -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The one-sided Case-1 first-moment input**: `E_{β_c,r}|K| ≤ C r^α` at large `r`, at the
explicit constant `C`.  This is the only first-moment information the paper's Case 1 uses; it is
strictly weaker than the two-sided asymptotic `E_{β_c,r}|K| ~ (α/β_c) r^α`, which additionally
pins down the constant `α/β_c` and gives a matching lower bound.

The moment is written `M.cutMoment 1 r` (equal to `M.cutMassAt r 0`, production
`SourceModelData.cutMassAt_zero_eq_cutMoment`). -/
def FirstMomentUpperAt (C : ℝ) : Prop :=
  ∀ᶠ r : ℝ in atTop, (M.cutMoment 1 r).toReal ≤ C * r ^ M.α

end SourceModelData

end PercLib.CriticalLRP.Orchestration
