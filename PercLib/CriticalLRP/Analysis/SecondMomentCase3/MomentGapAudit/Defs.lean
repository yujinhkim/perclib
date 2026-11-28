/-
Ultramath swarm `smwzlje3f`, member `m1`, direction `d7`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m1/Defs.lean`.

# Named forms of the Case-3 moment-gap input `hgm`

`secondMoment_asymptotic_case3_of_source_p21` (production HEAD `5d2d681`) retains the explicit
input

```
{c3 : ℝ} (hc3 : 0 < c3)
  (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
```

Hutchcroft, *Critical long-range percolation I*, proof of Proposition I.4.15, Case 3 (p. 47),
writes the same requirement as

> "it suffices to prove that if the triangle condition holds then
>  `E_{β_c,r}|K|² ⪰ (E_{β_c,r}|K|)³ ⪰ r^{3α}` as `r → ∞`"

i.e. the source itself uses the two equivalent forms `⪰ (E|K|)³` and `⪰ r^{3α}`. This file
names both forms so that the equivalence (`momentGap_iff_secondMomentLower` in `Audit.lean`)
can be stated and audited. Definitions only.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer

/-! # Named Case-3 moment-gap predicates -/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The retained Case-3 moment-gap input at an explicit constant**, verbatim the hypothesis
`hgm` of `secondMoment_asymptotic_case3_of_source_p21`. -/
def MomentGapAt (c : ℝ) : Prop :=
  ∀ᶠ r : ℝ in atTop, c * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal

/-- **The constant-free moment gap**: some positive constant works at all large radii.  This is
the form produced by `exists_momentGap_of_volumeTail`. -/
def MomentGap : Prop :=
  ∃ c : ℝ, 0 < c ∧ M.MomentGapAt c

/-- **The second form of the source's Case-3 lower bound**: a genuine power lower bound of index
`3α` on the second cutoff moment. -/
def SecondMomentLowerAt (c : ℝ) : Prop :=
  ∀ᶠ r : ℝ in atTop, c * r ^ (3 * M.α) ≤ (M.cutMoment 2 r).toReal

/-- The constant-free power lower bound of index `3α`. -/
def SecondMomentLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ M.SecondMomentLowerAt c

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
