/-
Swarm `smwxk27m7`, member `m3`, direction `d3` (`SOCKET-MIRROR`).

# Mirror-pair reduction of the `p = 5`, `k = 2` root-socket shape masses

The twelve off-middle `k = 2` root-class bounds of Lemma I.4.16 (`p = 5`, `k = 2`) are indexed by
`j : Fin 7`, `j ≠ 2`, and two canonical root sockets (`patSlot0 = pat 6`, root in comb slot `0`;
`patSlot2 = pat 0`, root in comb slot `2`).  This file supplies the definitions with which the
`j = 4` column is identified with the `j = 3` column (and, for `patSlot2`, the `j = 1` column with
`j = 0`): the leaf permutations of the comb system that carry one split tree onto the other, and
the mass of an arbitrary slot pattern.

Nothing here is a new mathematical hypothesis.  `patTotal` is `K2Mass.shapeTotal5` with `pat k`
replaced by an arbitrary `p : Fin 5 → Fin 5`, so that the split-position transport of
`leafMass` can be composed with a reindexing of the five free terminal sums; `swap34` and
`swap01` are the two leaf permutations that act on the nine edges of the split tree.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.RootCollapse.Main

/-! Leaf permutations and pattern masses used to transport split events. -/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

@[expose] public section

namespace SocketMirror

variable {V : Type*}

/-- The comb-leaf permutation `3 ↔ 4`.  The two leaves `b₃` and `b₄` are both attached to the
internal vertex `w`; interchanging them carries the split tree at position `3` (the sixth arm
landing on `b₃ — w`) onto the split tree at position `4` (landing on `b₄ — w`), fixing the root
leaf, all other leaves and all internal vertices. -/
def swap34 : Fin 5 → Fin 5 := ![0, 1, 2, 4, 3]

/-- The comb-leaf permutation `0 ↔ 1`, the mirror of `swap34` at the two leaves attached to `u`. -/
def swap01 : Fin 5 → Fin 5 := ![1, 0, 2, 3, 4]

@[simp] theorem swap34_zero : swap34 0 = 0 := rfl

@[simp] theorem swap34_one : swap34 1 = 1 := rfl

@[simp] theorem swap34_two : swap34 2 = 2 := rfl

@[simp] theorem swap34_three : swap34 3 = 4 := rfl

@[simp] theorem swap34_four : swap34 4 = 3 := rfl

@[simp] theorem swap01_zero : swap01 0 = 1 := rfl

@[simp] theorem swap01_one : swap01 1 = 0 := rfl

@[simp] theorem swap01_two : swap01 2 = 2 := rfl

@[simp] theorem swap01_three : swap01 3 = 3 := rfl

@[simp] theorem swap01_four : swap01 4 = 4 := rfl


/-- **The mass of a slot pattern at one split position.**  This is `K2Mass.shapeTotal5` with the
labelled pattern `pat k` replaced by an arbitrary `p : Fin 5 → Fin 5`: the five comb leaves are
`fun i => slotVec x u (p i)` and the five non-root terminals are summed over all of `V`. -/
noncomputable def patTotal (π : Sym2 V → unitInterval) (x : V) (p : Fin 5 → Fin 5) (j : Fin 7) :
    ℝ≥0∞ :=
  ∑' u : Fin 5 → V, leafMass π j (fun i => slotVec x u (p i)) (u 4)

/-- For a labelled pattern, `patTotal` is `K2Mass.shapeTotal5`. -/
theorem patTotal_pat (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    patTotal π x (pat k) j = shapeTotal5 π x k j := rfl


end SocketMirror
