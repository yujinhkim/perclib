/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Exact free-terminal evaluation of the fourteen six-terminal slot diagrams.
The original proofs and public statements came from Ultramath `smwprafq1`
member `m1`.  Their concrete `Fin 4` permutation applications exceeded the
heartbeat budget during definitional unification at revision
`5c25062c071ed99bd44904ceb185d8dba8f9093f`.  Here the same fifteen
permutations are performed by explicit adjacent exchanges of extended sums
after simplifying the finite-index vectors.  No budget or premise changes.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Main

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Pointwise bounds through the five-terminal patterns -/

/-- The pointwise bound for the `k`-th pattern when the root sits in slot `0`. -/
theorem pointwiseU [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0) (T : Fin 6 → V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      slotU π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) :=
by
  have _ := hk
  exact slotU_le π j _ _ _ _ _ _

/-- The pointwise bound for the `k`-th pattern when the root sits in slot `2`. -/
theorem pointwiseV [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0) (T : Fin 6 → V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      slotV π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
        (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5) :=
by
  have _ := hk
  exact slotV_le π j _ _ _ _ _ _

theorem evalFslotU [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : patF k 0 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotU π j (![0, y, z, w, q, r] (lift5 (patF k 0)))
          (![0, y, z, w, q, r] (lift5 (patF k 1)))
          (![0, y, z, w, q, r] (lift5 (patF k 2)))
          (![0, y, z, w, q, r] (lift5 (patF k 3)))
          (![0, y, z, w, q, r] (lift5 (patF k 4)))
          (![0, y, z, w, q, r] 5)) =
      secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, slotU π j 0 z y w q r := ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, slotU π j 0 w y z q r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, slotU π j 0 w y z q r := ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, slotU π j 0 q y z w r := tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, slotU π j 0 q y z w r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, slotU π j 0 q y z w r := ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    exact slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, slotU π j 0 w z y q r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, slotU π j 0 w z y q r := ENNReal.tsum_comm
      _ = ∑' w, ∑' z, ∑' y, ∑' q, ∑' r, slotU π j 0 w z y q r := tsum_congr fun w => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, slotU π j 0 q z y w r := tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, slotU π j 0 q z y w r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, slotU π j 0 q z y w r := ENNReal.tsum_comm
      _ = ∑' q, ∑' z, ∑' y, ∑' w, ∑' r, slotU π j 0 q z y w r := tsum_congr fun q => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, slotU π j 0 y w z q r := tsum_congr fun y => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, slotU π j 0 z w y q r := ENNReal.tsum_comm
      _ = ∑' z, ∑' w, ∑' y, ∑' q, ∑' r, slotU π j 0 z w y q r := tsum_congr fun z => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, slotU π j 0 q w y z r := tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, slotU π j 0 q w y z r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, slotU π j 0 q w y z r := ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' w, ∑' z, ∑' r, slotU π j 0 q w y z r := tsum_congr fun q => tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' q, ∑' w, ∑' y, ∑' z, ∑' r, slotU π j 0 q w y z r := tsum_congr fun q => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, slotU π j 0 y q z w r := tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, slotU π j 0 y q z w r := tsum_congr fun y => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, slotU π j 0 z q y w r := ENNReal.tsum_comm
      _ = ∑' z, ∑' y, ∑' q, ∑' w, ∑' r, slotU π j 0 z q y w r := tsum_congr fun z => tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' z, ∑' q, ∑' y, ∑' w, ∑' r, slotU π j 0 z q y w r := tsum_congr fun z => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, slotU π j 0 w q y z r := tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, slotU π j 0 w q y z r := ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' q, ∑' z, ∑' r, slotU π j 0 w q y z r := tsum_congr fun w => tsum_congr fun y => ENNReal.tsum_comm
      _ = ∑' w, ∑' q, ∑' y, ∑' z, ∑' r, slotU π j 0 w q y z r := tsum_congr fun w => ENNReal.tsum_comm
      _ = _ := slotU_tsum π j hq

theorem evalFslotV [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : patF k 2 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotV π j (![0, y, z, w, q, r] (lift5 (patF k 0)))
          (![0, y, z, w, q, r] (lift5 (patF k 1)))
          (![0, y, z, w, q, r] (lift5 (patF k 2)))
          (![0, y, z, w, q, r] (lift5 (patF k 3)))
          (![0, y, z, w, q, r] (lift5 (patF k 4)))
          (![0, y, z, w, q, r] 5)) =
      secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  fin_cases k
  · simp [patF, lift5]
    exact slotV_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, slotV π j y w 0 z q r := tsum_congr fun y => ENNReal.tsum_comm
      _ = _ := slotV_tsum π j hq
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, slotV π j y q 0 z w r := tsum_congr fun y => tsum_congr fun z => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, slotV π j y q 0 z w r := tsum_congr fun y => ENNReal.tsum_comm
      _ = _ := slotV_tsum π j hq
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem evalslotU [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotU π j (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
      secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  rw [← patF_eq] at hk ⊢
  exact evalFslotU π hq k j hk

theorem evalslotV [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        slotV π j (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
      secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  rw [← patF_eq] at hk ⊢
  exact evalFslotV π hq k j hk

end PercLib.CriticalLRP.TreeExpansion.SixPoint
