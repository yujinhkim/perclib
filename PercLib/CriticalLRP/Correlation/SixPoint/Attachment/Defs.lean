/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Six-terminal deterministic tree-arm decomposition for the `p = 5`, `k = 1` mixed moment.
Supplied by Ultramath `smwprafq1` member `m1` (direction d1).

Definitions only.  The nine-arm cover is proved in `Cover.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Attach

/-!
# The six-terminal nine-arm system

The five-terminal `CombSlots` system has seven arm slots in a fixed order:
`b₀—u, b₁—u, b₂—v, b₃—w, b₄—w, u—v, v—w`.
Attaching a sixth terminal `t` at a point `c` of arm `j` splits that arm into
`armSrc j — c` and `c — armTgt j` and adds the new arm `t — c`, so the tree on
six leaves has `2 * 6 - 3 = 9` edges.

`CombSystem` records the eight pairwise edge-disjoint walks (the seven arms plus the
new arm `t — c`) together with the information that the landing point `c` lies on
arm `j`.  The split of arm `j` at `c` is then a purely formal operation on edge
lists, so it is not built into the definition.
-/

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- The seven arm sources of the five-terminal comb, in slot order. -/
def armSrc (b0 b1 b2 b3 b4 u v : V) : Fin 7 → V := ![b0, b1, b2, b3, b4, u, v]

/-- The seven arm targets of the five-terminal comb, in slot order. -/
def armTgt (u v w : V) : Fin 7 → V := ![u, u, v, w, w, v, w]

/-- The seven comb arms as a `Fin 7`-indexed family of walks. -/
def combFam {G : SimpleGraph V} {b0 b1 b2 b3 b4 u v w : V}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) :
    (i : Fin 7) → G.Walk (armSrc b0 b1 b2 b3 b4 u v i) (armTgt u v w i) :=
  fun i => match i with
  | ⟨0, _⟩ => p0
  | ⟨1, _⟩ => p1
  | ⟨2, _⟩ => p2
  | ⟨3, _⟩ => p3
  | ⟨4, _⟩ => p4
  | ⟨5, _⟩ => s1
  | ⟨6, _⟩ => s2

@[simp] theorem combFam_zero {G : SimpleGraph V} {b0 b1 b2 b3 b4 u v w : V}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) :
    (combFam p0 p1 p2 p3 p4 s1 s2 0).edges = p0.edges := rfl

/-- **Six-terminal arm system.**  Seven pairwise edge-disjoint comb arms together with a
sixth arm `Q : t — c` edge-disjoint from all of them, the landing point `c` lying on arm `j`.
This is the deterministic input of the `p = 5`, `k = 1` BK regrouping: splitting arm `j` at
`c` produces the nine pairwise edge-disjoint walks of the six-leaf binary tree. -/
def CombSystem (G : SimpleGraph V) (b0 b1 b2 b3 b4 t u v w c : V) (j : Fin 7) : Prop :=
  ∃ (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c),
    (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges ++
      Q.edges).Nodup ∧
    c ∈ (combFam p0 p1 p2 p3 p4 s1 s2 j).support

/-- `Fin 5` embedded in `Fin 6` (the six terminals are the five comb terminals and the new one). -/
def lift5 (i : Fin 5) : Fin 6 := ⟨(i : ℕ), Nat.lt_trans i.2 (by decide)⟩

@[simp] theorem lift5_val (i : Fin 5) : (lift5 i : ℕ) = (i : ℕ) := rfl

/-- The five-terminal pattern applied to six terminals: the `k`-th labelled comb on the
first five terminals, plus the sixth terminal `T 5`. -/
def SixShape (G : SimpleGraph V) (k : Fin 15) (j : Fin 7) (c u v w : V)
    (T : Fin 6 → V) : Prop :=
  CombSystem G (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
    (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
    (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
    (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
    (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) u v w c j

/-! ## The exact coefficient `105 = 15 * 7` -/

theorem card_fin15_mul_fin7 : Fintype.card (Fin 15 × Fin 7) = 105 := by
  simp [Fintype.card_prod]

theorem card_fin15_mul_fin7_eq_sevenDoubleFactorial :
    Fintype.card (Fin 15 × Fin 7) = Nat.doubleFactorial 7 := by
  simp [Fintype.card_prod, Nat.doubleFactorial]

/-- A constant sum over the `105` six-terminal shape indices. -/
theorem tsum_fin15_fin7_const (c : ℝ≥0∞) :
    (∑' _ : Fin 15 × Fin 7, c) = 105 * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, card_fin15_mul_fin7]
  simp [nsmul_eq_mul]

end PercLib.CriticalLRP.TreeExpansion.SixPoint

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **Seven-group certificate event**: one joint group (a single finite open set carrying a joint
connection event) and six single two-point groups with pairwise disjoint certificates.  This is the
certificate object of the `p = 5`, `k = 1` regrouping: one shared-spine joint pair plus six
two-point functions. -/
def SevenGroupEvent (A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Config V)) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set (Sym2 V),
        W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧
          W₆.Finite ∧
        W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
        W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧ W₅ ∈ A₅ ∧ W₆ ∈ A₆ ∧
        Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
          Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
        Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧
          Disjoint W₁ W₆ ∧
        Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
        Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
        Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}

/-- **Seven-fold BK for one joint event and six singleton events.**  The joint event `A₀` is not
split: its certificate is a single finite open set. -/
theorem sevenGroup_le [Countable V] (π : Sym2 V → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Config V)} (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁)
    (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃) (h₄ : IsUpperSet A₄) (h₅ : IsUpperSet A₅)
    (h₆ : IsUpperSet A₆) :
    law π (SevenGroupEvent A₀ A₁ A₂ A₃ A₄ A₅ A₆) ≤
      law π A₀ * (law π A₁ * (law π A₂ * (law π A₃ * (law π A₄ * (law π A₅ * law π A₆))))) := by
  simpa only [SevenGroupEvent, PercLib.Percolation.Bond.law] using
    PercLib.CriticalLRP.TreeExpansion.FivePoint.prodBernoulli_seven_wit_le (p := π)
      (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (A₃ := A₃) (A₄ := A₄) (A₅ := A₅) (A₆ := A₆)
      h₀ h₁ h₂ h₃ h₄ h₅ h₆

end PercLib.CriticalLRP.TreeExpansion.SixPoint

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- The fifteen slot patterns as a pattern-matching function (definitionally reducing on
numerals, unlike the vector literal `pat`). -/
def patF : Fin 15 → (Fin 5 → Fin 5)
  | 0 => ![1, 2, 0, 3, 4]
  | 1 => ![1, 3, 0, 2, 4]
  | 2 => ![1, 4, 0, 2, 3]
  | 3 => ![0, 2, 1, 3, 4]
  | 4 => ![0, 3, 1, 2, 4]
  | 5 => ![0, 4, 1, 2, 3]
  | 6 => ![0, 1, 2, 3, 4]
  | 7 => ![0, 3, 2, 1, 4]
  | 8 => ![0, 4, 2, 1, 3]
  | 9 => ![0, 1, 3, 2, 4]
  | 10 => ![0, 2, 3, 1, 4]
  | 11 => ![0, 4, 3, 1, 2]
  | 12 => ![0, 1, 4, 2, 3]
  | 13 => ![0, 2, 4, 1, 3]
  | 14 => ![0, 3, 4, 1, 2]

theorem patF_eq (k : Fin 15) : patF k = PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k := by
  fin_cases k <;> rfl

end PercLib.CriticalLRP.TreeExpansion.SixPoint
