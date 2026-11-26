/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0 (read-only package
`.scratch/critical-lrp-orchestration`). Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Transversal
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover

/-!
# The union bound over one representative per child-swap orbit

This file assembles the shape count of `OrbitCount` with the atlas covering of
`AtlasRealization.Cover`: if the diagram events of a plane tree and of a child-swap representative
of its class agree (`RTree.SwapTransport`, the explicit hypothesis, the precise remaining gap),
then the covering can be taken over the transversal `RTree.transversal (Fin q)` alone, and the
union bound, BK, the atlas-to-weight bridge and `treeSum_eq_sum_transversal` give (I.2.2) with the
source constant — no factor `2 ^ (q-1)`.

The single extra premise `RTree.SwapTransport ends x o` is a statement about diagram *events*
(`DiagEvent`), not a probability bound; it does not mention `treeSum`, `prob` or the conclusion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **One plane tree is covered by the events of a transversal representative.**  This is the only
use of the transport hypothesis: it moves a diagram event from `t` to the representative `r` of the
child-swap class of `t`, with `r` supplied by `RTree.transversal_spec`. -/
theorem diagEvent_iUnion_subset_transversal {q : ℕ} (ends : E → Sym2 V) (x : Fin q → V) (o : V)
    (htrans : SwapTransport ends x o) (t : RTree.LT (Fin q)) :
    (⋃ φ : t.val.IPos → V, DiagEvent ends x o t.val φ)
      ⊆ ⋃ r ∈ RTree.transversal (Fin q), ⋃ (φ : r.IPos → V), DiagEvent ends x o r φ := by
  obtain ⟨r, ⟨hrT, hmem⟩, -⟩ := RTree.transversal_spec t
  intro ω hω
  obtain ⟨φ, hφ⟩ := Set.mem_iUnion.mp hω
  obtain ⟨φ', hsub⟩ := htrans t.val r (RTree.swapFiber_symm hmem) φ
  exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hrT, Set.mem_iUnion.mpr ⟨φ', hsub hφ⟩⟩⟩

/-- **Covering by the transversal.**  Every configuration connecting the root `o` to all terminals
`x i` lies in a diagram event of some transversal representative. -/
theorem cover_union_transversal {q : ℕ} (hq : 1 ≤ q) (ends : E → Sym2 V) (x : Fin q → V) (o : V)
    (htrans : SwapTransport ends x o) :
    {ω : Finset E | ∀ i : Fin q, Conn ends ω o (x i)}
      ⊆ ⋃ r ∈ RTree.transversal (Fin q), ⋃ (φ : r.IPos → V), DiagEvent ends x o r φ := by
  classical
  intro ω hω
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨t, φ, wit, hshape, hreal⟩ :=
    exists_realization ends hne (fun a _ => hω a)
  have hfull : RTree.FullyLabelled t := by
    refine ⟨hshape.1, ?_⟩
    rw [← List.toFinset_card_of_nodup hshape.1, hshape.2, Finset.card_univ, Fintype.card_fin]
  have hdiag : ω ∈ DiagEvent ends x o t φ := ⟨wit, hreal⟩
  have hsub := diagEvent_iUnion_subset_transversal ends x o htrans ⟨t, hfull⟩
  exact hsub (Set.mem_iUnion.mpr ⟨φ, hdiag⟩)

/-- **The transversal union bound.**  The probability that `o` is connected to all `q` terminals is
at most the sum, over one representative per child-swap orbit, of the tree weight. -/
theorem prob_conn_le_sum_transversal {q : ℕ} (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) (hq : 1 ≤ q)
    (x : Fin q → V) (htrans : SwapTransport ends x o) :
    prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)}
      ≤ ∑ r ∈ RTree.transversal (Fin q),
          RTree.wtL (fun a b => prob pr {ω | Conn ends ω a b}) r x o := by
  classical
  refine le_trans (prob_mono hp hp1 (cover_union_transversal hq ends x o htrans)) ?_
  refine le_trans (prob_biUnion_le_sum hp hp1 (RTree.transversal (Fin q))
    (fun r => ⋃ (φ : r.IPos → V), DiagEvent ends x o r φ)) ?_
  refine Finset.sum_le_sum fun r _ => ?_
  refine le_trans (prob_iUnion_le_sum hp hp1
    (fun φ : r.IPos → V => DiagEvent ends x o r φ)) ?_
  calc ∑ φ : r.IPos → V, prob pr (DiagEvent ends x o r φ)
      ≤ ∑ φ : r.IPos → V, ∏ e : AEdge r, prob pr (ConnEvent ends x o r φ e) :=
        Finset.sum_le_sum fun φ _ => prob_diagEvent_le hBK ends x o r φ
    _ = posSumWt (fun a b => prob pr {ω | Conn ends ω a b}) r x o := rfl
    _ = RTree.wtL (fun a b => prob pr {ω | Conn ends ω a b}) r x o :=
        posSumWt_eq_wtL _ r x o

/-- **(I.2.2) from the child-swap transport.**  If exchanging children does not change the family
of diagram events (`RTree.SwapTransport`), then the tree-graph inequality holds with the source
tree sum `treeSum`, i.e. with the coefficient `(2p-3)!!` rather than `2^(p-1)·(2p-3)!!`. -/
theorem prob_conn_le_treeSum_of_swapTransport {q : ℕ} (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (o : V) (hq : 1 ≤ q)
    (x : Fin q → V) (htrans : SwapTransport ends x o) :
    prob pr {ω | ∀ i : Fin q, Conn ends ω o (x i)}
      ≤ treeSum (fun a b => prob pr {ω | Conn ends ω a b}) q o x := by
  refine le_trans (prob_conn_le_sum_transversal pr hp hp1 hBK ends o hq x htrans) (le_of_eq ?_)
  exact (RTree.treeSum_eq_sum_transversal
    (fun a b => prob pr {ω | Conn ends ω a b}) q hq o x).symm

end PercLib.CriticalLRP.TreeExpansion.Real
