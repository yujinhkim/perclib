/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definitions for radius regularity of the higher cutoff moments

The landed `Analysis/Cutoff/Continuity` file proves that
`r ↦ χ(r) = (M.cutMoment 1 r).toReal` is left- and right-continuous at every `r₀ > 0`
(left unconditionally, right under finiteness of the mass at a strictly larger radius), and
`MomentMonotonicity/CutoffMomentConvergence` proves monotone convergence of every natural
cluster moment along an increasing family of edge laws.  This file adds only the two pieces of
vocabulary needed to state the same regularity for all orders `p : ℕ`:

* `markVolPow M p r` — the `p`-th power of the cluster volume read on the common mark space;
* `cutMomentReal M p r` — the `p`-th cutoff moment as a real number.

No mathematical statement is asserted here.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.MomentMonotonicity.CutoffMomentConvergence
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect

/-! # Mark-space powers of the cluster volume -/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The `p`-th power of the cut-off cluster volume of the origin, as a function on the common
mark space carrying every cut-off law.  This is the integrand of `M.cutMoment p r`. -/
abbrev markVolPow (p : ℕ) (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => (M.markVol r u) ^ p

/-- The `p`-th cut-off cluster moment as a real number. -/
abbrev cutMomentReal (p : ℕ) (r : ℝ) : ℝ :=
  (M.cutMoment p r).toReal

end SourceModelData

end PercLib.CriticalLRP.Orchestration
