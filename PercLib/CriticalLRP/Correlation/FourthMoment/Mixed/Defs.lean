/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Definitions for the mixed fourth cluster-moment tree-graph bound, supplied by
Ultramath `smwpmcy6r` member m1 and reviewed before integration.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Bridge
public import PercLib.CriticalLRP.Correlation.CubicMixed.Moments

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- Five increasing events with five pairwise disjoint finite certificates in `ω`. -/
def FiveGroupEvent (A₀ A₁ A₂ A₃ A₄ : Set (Config V)) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ : Set (Sym2 V),
        W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧
        W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧
        W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧
        Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
        Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧
        Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₃ W₄}

/-- The per-shape slot diagram: the right-hand side of the fivefold BK bound, in slot form,
with the union-bounded branch vertex already summed out. -/
noncomputable def slotDiagram (π : Sym2 V → unitInterval) (k : Fin 15) (w : V)
    (T : Fin 5 → V) : ℝ≥0∞ :=
  if pat k 0 = 0 then
    ∑' c : V, law π (conn (T 0) c ∩ conn (T (pat k 1)) c) *
      (tau π (T (pat k 2)) c * (tau π c w * (tau π (T (pat k 3)) w *
        tau π (T (pat k 4)) w)))
  else
    ∑' c : V, law π (conn (T 0) w ∩ conn c w) *
      (tau π (T (pat k 0)) c * (tau π (T (pat k 1)) c * (tau π (T (pat k 3)) w *
        tau π (T (pat k 4)) w)))

/-- `Fin 4 → V` as a product of four copies of `V`. -/
def fin4Prod : (Fin 4 → V) ≃ V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by obtain ⟨a, b, c, d⟩ := p; rfl

/-- The root-at-`u` diagram, with both branch vertices summed. -/
noncomputable def canonU (π : Sym2 V → unitInterval) (o : V) (a b c d : V) : ℝ≥0∞ :=
  ∑' w : V, ∑' x : V,
    law π (conn o x ∩ conn a x) * (tau π b x * (tau π x w * (tau π c w * tau π d w)))

/-- The root-at-`v` (balanced) diagram, with both branch vertices summed. -/
noncomputable def canonV (π : Sym2 V → unitInterval) (o : V) (a b c d : V) : ℝ≥0∞ :=
  ∑' w : V, ∑' x : V,
    law π (conn o w ∩ conn x w) * (tau π a x * (tau π b x * (tau π c w * tau π d w)))

end PercLib.CriticalLRP.TreeExpansion.FivePoint
