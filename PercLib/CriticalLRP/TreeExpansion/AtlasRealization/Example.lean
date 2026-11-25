/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m4/.
-/

/-
A non-vacuous instance of the atlas realization, and the `2p - 1` edge count.

The configuration is the path `0 — 1 — 2` with both edges open and the root at the middle
vertex `1`; the two terminals sit at the ends.  The shape is the two-leaf tree, its single
internal vertex sits at `1`, and the three atlas edges are witnessed by `∅`, `{0}` and `{1}`:

* the root edge is trivial (the root leaf and the internal root coincide at `1`), which is the
  factor `P(w ↔ w) = 1` of the source;
* the two child edges are the two distinct open path edges,

so the witnesses are pairwise disjoint and together account for *every* open edge exactly once.
This shows that the realization is not vacuous: the atlas is realized by genuine open edges,
with a repeated vertex image (the terminal leaf `0` sits at the same vertex as the internal
root) and without any edge being charged twice.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExampleDefs

/-! Atlas realization, covering and example lemmas. -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The atlas of a shape with leaf set `Z` has exactly `2 #Z - 1` edges.** -/
theorem card_aedge_of_isLabelledShape {t : RTree α} {Z : Finset α}
    (h : IsLabelledShape t Z) : Fintype.card (AEdge t) = 2 * Z.card - 1 := by
  have hcard : t.numLeaves = Z.card := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup h.1, h.2]
  rw [card_aedge, hcard]

/-! ### The path `0 — 1 — 2` with both edges open -/

theorem path_conn_zero : Conn pathEnds ({0} : Finset (Fin 2)) 0 1 := by
  refine conn_of_adj ?_
  rw [openGraph_adj]
  exact ⟨⟨0, Finset.mem_singleton_self 0, by simp [pathEnds]⟩, by decide⟩

theorem path_conn_one : Conn pathEnds ({1} : Finset (Fin 2)) 1 2 := by
  refine conn_of_adj ?_
  rw [openGraph_adj]
  exact ⟨⟨1, Finset.mem_singleton_self 1, by simp [pathEnds]⟩, by decide⟩

theorem ex_realization : IsRealization pathEnds pathConf exY 1 exPhi exWit := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rcases e with (⟨u, b⟩ | ⟨⟩)
    · rcases u with (u | u | ⟨⟩)
      · exact nomatch u
      · exact nomatch u
      · cases b <;> simp [exWit, pathConf]
    · simp [exWit]
  · intro e e' hne
    rcases e with (⟨u, b⟩ | ⟨⟩)
    · rcases u with (u | u | ⟨⟩)
      · exact nomatch u
      · exact nomatch u
      · rcases e' with (⟨u', b'⟩ | ⟨⟩)
        · rcases u' with (u' | u' | ⟨⟩)
          · exact nomatch u'
          · exact nomatch u'
          · cases b <;> cases b' <;> first
              | exact absurd rfl hne
              | simp [exWit]
        · cases b <;> simp [exWit]
    · rcases e' with (⟨u', b'⟩ | ⟨⟩)
      · rcases u' with (u' | u' | ⟨⟩)
        · exact nomatch u'
        · exact nomatch u'
        · cases b' <;> simp [exWit]
      · exact absurd rfl hne
  · intro e
    rcases e with (⟨u, b⟩ | ⟨⟩)
    · rcases u with (u | u | ⟨⟩)
      · exact nomatch u
      · exact nomatch u
      · cases b
        · change Conn pathEnds ({0} : Finset (Fin 2)) 1 0
          exact conn_symm path_conn_zero
        · change Conn pathEnds ({1} : Finset (Fin 2)) 1 2
          exact path_conn_one
    · change Conn pathEnds (∅ : Finset (Fin 2)) 1 1
      exact conn_refl pathEnds ∅ 1

/-- The witnesses cover the configuration exactly: every open edge is charged to exactly one
atlas edge, so the accounting is not vacuous. -/
theorem ex_cover : (Finset.univ.biUnion exWit) = pathConf := by
  decide

end PercLib.CriticalLRP.TreeExpansion.Real
