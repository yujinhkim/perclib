/-
Ordinary `p = 5`, `k = 0`: the per-`(k,j)` nine-tau diagram evaluation.

Supplied by Ultramath `smwpv4yqm` member `m2` (direction `d1`, task B).

**Main result.**  For the terminal vector `T = ![0, y, z, w, q, r]` and every one of the `15 * 7`
shape indices, the ordinary per-shape diagram `ordD` sums to exactly the ninth power of the
susceptibility:

  `∑' y z w q r, ordD π k j ![0, y, z, w, q, r] = (∑' x, tau π 0 x) ^ 9`.

No finiteness hypothesis of any kind is used: the four internal sums `c, u, v, w` are retained,
all permutation steps are unconditional identities of extended sums in `ℝ≥0∞`, and profile
invariance enters only through the row/column-sum identities `tau_row`/`tau_col`.  By
`Defs.ordD` this is exactly the quantity bounded below by the nine-walk event bound
`law π (⋃ c u v w, {ω | SixShape (openGraph ω) k j c u v w T})`, so the coefficient computation
`105 * (∑' x, tau π 0 x) ^ 9` is a `Fin 15 × Fin 7` constant sum.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Eval

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

set_option linter.unusedSimpArgs false

/-! ## Where the root sits in each of the fifteen patterns -/

/-- In every one of the fifteen normalised patterns the root `0` occupies comb slot `0` or comb
slot `2`.  (Local restatement of `Attachment.Assembly.pat_root_slot`, so that this module does not
import the mixed `k = 1` development.) -/
theorem ord_pat_root_slot (k : Fin 15) :
    PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 ∨
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 := by
  rw [← patF_eq]
  fin_cases k <;> decide

/-! ## Free-terminal evaluation through the fifteen patterns -/

/-- **The twelve patterns with the root in comb slot `0`.**  The pattern only permutes which free
coordinate sits in which leaf slot, so the five extended sums are exchanged (at most four adjacent
exchanges) into the canonical leaf order and `ordSlotU_tsum` applies. -/
theorem evalFordU [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        ordSlotU π j 0 (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
      (∑' x, tau π 0 x) ^ 9 := by
  rw [← patF_eq] at hk ⊢
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, ordSlotU π j 0 z y w q r :=
        ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w y z q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w y z q r :=
        ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, ordSlotU π j 0 q y z w r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q y z w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q y z w r :=
        ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    exact ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w z y q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w z y q r :=
        ENNReal.tsum_comm
      _ = ∑' w, ∑' z, ∑' y, ∑' q, ∑' r, ordSlotU π j 0 w z y q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, ordSlotU π j 0 q z y w r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q z y w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q z y w r :=
        ENNReal.tsum_comm
      _ = ∑' q, ∑' z, ∑' y, ∑' w, ∑' r, ordSlotU π j 0 q z y w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 y w z q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, ordSlotU π j 0 z w y q r :=
        ENNReal.tsum_comm
      _ = ∑' z, ∑' w, ∑' y, ∑' q, ∑' r, ordSlotU π j 0 z w y q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, ordSlotU π j 0 q w y z r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q w y z r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 q w y z r :=
        ENNReal.tsum_comm
      _ = ∑' q, ∑' y, ∑' w, ∑' z, ∑' r, ordSlotU π j 0 q w y z r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' q, ∑' w, ∑' y, ∑' z, ∑' r, ordSlotU π j 0 q w y z r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, ordSlotU π j 0 y q z w r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, ordSlotU π j 0 y q z w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' z, ∑' y, ∑' w, ∑' q, ∑' r, ordSlotU π j 0 z q y w r :=
        ENNReal.tsum_comm
      _ = ∑' z, ∑' y, ∑' q, ∑' w, ∑' r, ordSlotU π j 0 z q y w r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' z, ∑' q, ∑' y, ∑' w, ∑' r, ordSlotU π j 0 z q y w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w q y z r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' z, ∑' q, ∑' r, ordSlotU π j 0 w q y z r :=
        ENNReal.tsum_comm
      _ = ∑' w, ∑' y, ∑' q, ∑' z, ∑' r, ordSlotU π j 0 w q y z r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' w, ∑' q, ∑' y, ∑' z, ∑' r, ordSlotU π j 0 w q y z r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotU_tsum π hq j 0

/-- **The three patterns with the root in comb slot `2`** (`pat k 2 = 0`). -/
theorem evalFordV [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7)
    (hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        ordSlotV π j 0 (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
          (![0, y, z, w, q, r] (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))
          (![0, y, z, w, q, r] 5)) =
      (∑' x, tau π 0 x) ^ 9 := by
  rw [← patF_eq] at hk ⊢
  fin_cases k
  · simp [patF, lift5]
    exact ordSlotV_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' w, ∑' z, ∑' q, ∑' r, ordSlotV π j 0 y w z q r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotV_tsum π hq j 0
  · simp [patF, lift5]
    calc
      _ = ∑' y, ∑' z, ∑' q, ∑' w, ∑' r, ordSlotV π j 0 y q z w r :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
      _ = ∑' y, ∑' q, ∑' z, ∑' w, ∑' r, ordSlotV π j 0 y q z w r :=
        tsum_congr fun _ => ENNReal.tsum_comm
      _ = _ := ordSlotV_tsum π hq j 0
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

/-! ## The per-`(k, j)` diagram -/

/-- **The ordinary nine-tau diagram evaluation.**  For every shape index `(k, j)` and the root
terminal vector `![0, y, z, w, q, r]`, the per-shape diagram `ordD` sums to `(∑' x, tau π 0 x)^9`.
No finiteness, no second moment and no joint pair occur. -/
theorem ordD_eval [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (k : Fin 15) (j : Fin 7) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ordD π k j ![0, y, z, w, q, r]) =
      (∑' x, tau π 0 x) ^ 9 := by
  by_cases hk : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0
  · simp only [ordD, ite_eq_left hk]
    exact evalFordU π hq k j hk
  · have hk2 : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 :=
      (ord_pat_root_slot k).resolve_left hk
    simp only [ordD, ite_eq_right hk]
    exact evalFordV π hq k j hk2

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.ordSlotU_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.ordSlotV_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.evalFordU
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.evalFordV
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.ordD_eval

end PercLib.CriticalLRP.TreeExpansion.SixPoint
