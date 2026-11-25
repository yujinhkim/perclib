/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m4/.
-/

/-
The all-configurations covering step of Lemma I.4.16.

Main results:

* `exists_split` — the one-step branch decomposition, relative to a *given* open edge set `W`
  carrying the incoming connection.  It has no positivity or non-degeneracy hypothesis: when
  all the terminals of the current group coincide (`y a = y b` for all `a, b` in the group),
  the split is the degenerate one at `w = y a₀` with `W0 = W` and empty arm witnesses, which
  is exactly the case in which the source's tree diagram carries the factor `P(w ↔ w) = 1`.
* `exists_realization` — every finite label set connected to a root admits a labelled binary
  shape and an edge-disjoint realization of its whole atlas inside the incoming witness.  This
  is the union-bound covering of the source proof ("taking a union bound over possible
  combinatorial structures of a tree connecting the origin to `p` labelled vertices"), with the
  shapes running over *all* binary trees with the prescribed leaf labels.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Defs

/-!
# The covering theorem

Nothing here is probabilistic: `Conn` is connectivity in the open subgraph of a finite edge set
(production `PercLib.CriticalLRP.TreeGraph.Conn`), and the content is that one configuration
already contains a complete edge-disjoint atlas for some shape.  The probabilistic consumer is
in `Cover.lean`.
-/
/-! Atlas realization, covering and realize lemmas. -/

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

/-! ### The one-step split -/

/-- **The one-step branch split, relative to the incoming witness `W`.**

If every label of the nonempty set `Z` is connected to `v` inside `W` and `Z` has at least two
elements, then `Z` splits into two nonempty groups `A` and `Z \ A`, and `W` splits into three
pairwise disjoint open sets: `W0` joining `v` to a branch point `w`, `WA` joining `w` to all
labels of `A` and `WB` joining `w` to all labels of `Z \ A`.

When all labels of `Z` have the same value the split is degenerate: `A = {a₀}`, `w = y a₀`,
`W0 = W` and the two arm witnesses are empty, and then `P(w ↔ w) = 1` in the corresponding
product of connection probabilities. -/
theorem exists_split (ends : E → Sym2 V) {W : Finset E} {v : V} {y : α → V}
    {Z : Finset α} (hne : Z.Nonempty) (hconn : ∀ a ∈ Z, Conn ends W v (y a))
    (h2 : 2 ≤ Z.card) :
    ∃ (A : Finset α) (w : V) (W0 WA WB : Finset E), SplitAt ends W v y Z A w W0 WA WB := by
  classical
  by_cases hall : ∀ a ∈ Z, ∀ b ∈ Z, y a = y b
  · -- degenerate split: all labels coincide
    obtain ⟨a₀, ha₀⟩ := hne
    have hsub : ({a₀} : Finset α) ⊆ Z := Finset.singleton_subset_iff.mpr ha₀
    have hBne : (Z \ {a₀}).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have h1 : Z ⊆ {a₀} := (Finset.sdiff_eq_empty_iff_subset).mp h
      have h2' := Finset.card_le_card h1
      rw [Finset.card_singleton] at h2'
      omega
    refine ⟨{a₀}, y a₀, W, ∅, ∅, hsub, Finset.singleton_nonempty a₀, hBne,
      Finset.Subset.refl W, Finset.empty_subset W, Finset.empty_subset W,
      Finset.disjoint_empty_right W, Finset.disjoint_empty_right W, by simp,
      hconn a₀ ha₀, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_singleton.mp ha]
      exact conn_refl ends ∅ (y a₀)
    · intro b hb
      have hbZ : b ∈ Z := (Finset.mem_sdiff.mp hb).1
      rw [hall b hbZ a₀ ha₀]
      exact conn_refl ends ∅ (y a₀)
  · -- genuine split at a branch point
    push Not at hall
    obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := hall
    obtain ⟨w, A, W0, WA, WB, hAne, hAcne, hW0, hWA, hWB, hd0A, hd0B, hdAB, hc0, hcA, hcB⟩ :=
      exists_branch_split (s := W) (v := v) (ends := ends) (α := ↥Z) (fun a : ↥Z => y a.1)
        (fun a => hconn a.1 a.2) ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hab⟩
    have hBne : (Z \ A.image Subtype.val).Nonempty := by
      obtain ⟨b, hb⟩ := hAcne
      refine ⟨b.1, Finset.mem_sdiff.mpr ⟨b.2, ?_⟩⟩
      intro hmem
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hmem
      exact (Finset.mem_compl.mp hb) (by rw [← Subtype.ext hav]; exact ha)
    refine ⟨A.image Subtype.val, w, W0, WA, WB, Finset.image_subset_iff.mpr (fun a _ => a.2),
      hAne.image _, hBne, hW0, hWA, hWB, hd0A, hd0B, hdAB, hc0, ?_, ?_⟩
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
      exact hcA a' ha'
    · intro b hb
      obtain ⟨hbZ, hbnot⟩ := Finset.mem_sdiff.mp hb
      exact hcB ⟨b, hbZ⟩ (Finset.mem_compl.mpr (fun hmem =>
        hbnot (Finset.mem_image.mpr ⟨⟨b, hbZ⟩, hmem, rfl⟩)))

/-! ### The covering theorem -/

/-- The strong-induction form of the covering theorem, with the number of labels explicit. -/
theorem exists_realization_aux (ends : E → Sym2 V) (n : ℕ) :
    ∀ (W : Finset E) (v : V) (y : α → V) (Z : Finset α), Z.card = n → Z.Nonempty →
      (∀ a ∈ Z, Conn ends W v (y a)) →
      ∃ (t : RTree α) (φ : t.IPos → V) (wit : AEdge t → Finset E),
        IsLabelledShape t Z ∧ IsRealization ends W y v φ wit := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W v y Z hZ hne hconn
    classical
    rcases Nat.lt_or_ge Z.card 2 with h1 | h1
    · -- a single label: the shape is that leaf and the root edge is the incoming witness
      have hc1 : Z.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      refine ⟨RTree.leaf a, (fun u => nomatch u), (fun _ => W), ?_, ?_, ?_, ?_⟩
      · exact ⟨by simp, by simp⟩
      · intro e
        exact Finset.Subset.refl W
      · intro e e' hne'
        rcases e with (⟨u, b⟩ | x)
        · exact nomatch u
        · rcases e' with (⟨u, b⟩ | x)
          · exact nomatch u
          · exact absurd rfl hne'
      · intro e
        rcases e with (⟨u, b⟩ | x)
        · exact nomatch u
        · rw [srcPos_root, dstPos_root, rootPos_leaf]
          exact hconn a (Finset.mem_singleton_self a)
    · -- at least two labels: split and recurse
      obtain ⟨A, w, W0, WA, WB, hAZ, hAne, hBne, hW0, hWA, hWB, hd0A, hd0B, hdAB, hc0, hcA,
        hcB⟩ := exists_split ends hne hconn h1
      have hAZne : A ≠ Z := by
        intro h
        rw [h] at hBne
        simp at hBne
      have hAproper : A ⊂ Z := Finset.ssubset_iff_subset_ne.mpr ⟨hAZ, hAZne⟩
      have hAcard : A.card < n := by
        have := Finset.card_lt_card hAproper
        omega
      have hBproper : Z \ A ⊂ Z := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro h
        obtain ⟨a, ha⟩ := hAne
        have hamem : a ∈ Z \ A := by rw [h]; exact hAZ ha
        exact (Finset.mem_sdiff.mp hamem).2 ha
      have hBcard : (Z \ A).card < n := by
        have := Finset.card_lt_card hBproper
        omega
      obtain ⟨tL, φL, witL, hshapeL, hrealL⟩ :=
        ih A.card hAcard WA w y A rfl hAne (fun a ha => hcA a ha)
      obtain ⟨tR, φR, witR, hshapeR, hrealR⟩ :=
        ih (Z \ A).card hBcard WB w y (Z \ A) rfl hBne (fun b hb => hcB b hb)
      refine ⟨RTree.node tL tR, pushPhi w φL φR, pushWit W0 witL witR, ?_, ?_, ?_, ?_⟩
      · -- the leaf labels are exactly `Z`
        refine ⟨?_, ?_⟩
        · refine hshapeL.1.append hshapeR.1 ?_
          rw [List.disjoint_left]
          intro a ha ha'
          have h1 : a ∈ A := by rw [← hshapeL.2]; exact List.mem_toFinset.mpr ha
          have h2 : a ∈ Z \ A := by rw [← hshapeR.2]; exact List.mem_toFinset.mpr ha'
          exact (Finset.mem_sdiff.mp h2).2 h1
        · rw [RTree.leaves_node, List.toFinset_append, hshapeL.2, hshapeR.2,
            Finset.union_sdiff_of_subset hAZ]
      · -- every witness is inside the incoming witness `W`
        intro e
        obtain ⟨s, hs⟩ : ∃ s : AEdge tL ⊕ AEdge tR ⊕ PUnit, aedgeSumFun e = s := ⟨_, rfl⟩
        rcases s with (a | (b | x))
        · have he : e = aedgeSumInv (Sum.inl a) := by rw [← aedgeSumInv_fun e, hs]
          rw [he, pushWit_inl]
          exact fun z hz => hWA (hrealL.subset a hz)
        · have he : e = aedgeSumInv (Sum.inr (Sum.inl b)) := by rw [← aedgeSumInv_fun e, hs]
          rw [he, pushWit_inr_inl]
          exact fun z hz => hWB (hrealR.subset b hz)
        · have he : e = aedgeSumInv (Sum.inr (Sum.inr x)) := by rw [← aedgeSumInv_fun e, hs]
          rw [he, pushWit_none]
          exact hW0
      · -- witnesses of distinct atlas edges are disjoint
        intro e e' hne'
        obtain ⟨s, hs⟩ : ∃ s : AEdge tL ⊕ AEdge tR ⊕ PUnit, aedgeSumFun e = s := ⟨_, rfl⟩
        obtain ⟨s', hs'⟩ : ∃ s' : AEdge tL ⊕ AEdge tR ⊕ PUnit, aedgeSumFun e' = s' :=
          ⟨_, rfl⟩
        have he : e = aedgeSumInv s := by rw [← aedgeSumInv_fun e, hs]
        have he' : e' = aedgeSumInv s' := by rw [← aedgeSumInv_fun e', hs']
        rcases s with (a | (b | x)) <;> rcases s' with (a' | (b' | x'))
        · rw [he, he', pushWit_inl, pushWit_inl]
          exact hrealL.disjoint a a' (fun ha => hne' (by rw [he, he', ha]))
        · rw [he, he', pushWit_inl, pushWit_inr_inl]
          exact hdAB.mono (hrealL.subset a) (hrealR.subset b')
        · rw [he, he', pushWit_inl, pushWit_none]
          exact hd0A.symm.mono (hrealL.subset a) (Finset.Subset.refl W0)
        · rw [he, he', pushWit_inr_inl, pushWit_inl]
          exact hdAB.symm.mono (hrealR.subset b) (hrealL.subset a')
        · rw [he, he', pushWit_inr_inl, pushWit_inr_inl]
          exact hrealR.disjoint b b' (fun hb => hne' (by rw [he, he', hb]))
        · rw [he, he', pushWit_inr_inl, pushWit_none]
          exact hd0B.symm.mono (hrealR.subset b) (Finset.Subset.refl W0)
        · rw [he, he', pushWit_none, pushWit_inl]
          exact hd0A.mono (Finset.Subset.refl W0) (hrealL.subset a')
        · rw [he, he', pushWit_none, pushWit_inr_inl]
          exact hd0B.mono (Finset.Subset.refl W0) (hrealR.subset b')
        · have hxx : x = x' := Subsingleton.elim x x'
          exact absurd (show e = e' by rw [he, he', hxx]) hne'
      · -- each witness connects the two ends of its atlas edge
        intro e
        obtain ⟨s, hs⟩ : ∃ s : AEdge tL ⊕ AEdge tR ⊕ PUnit, aedgeSumFun e = s := ⟨_, rfl⟩
        have he : e = aedgeSumInv s := by rw [← aedgeSumInv_fun e, hs]
        rcases s with (a | (b | x))
        · rw [he, pushWit_inl, srcPos_piece_inl, dstPos_piece_inl]
          exact hrealL.conn a
        · rw [he, pushWit_inr_inl, srcPos_piece_inr_inl, dstPos_piece_inr_inl]
          exact hrealR.conn b
        · rw [he, pushWit_none, srcPos_piece_none, dstPos_piece_none]
          exact hc0

/-- **Every terminal-connected configuration carries an edge-disjoint atlas.**

Let `W` be a finite set of open edges, `v` a vertex, and `Z` a nonempty finite set of labels
whose terminals `y a` are all connected to `v` inside `W`.  Then there are a rooted binary
shape `t` whose leaves are exactly the labels of `Z` (injectively), positions `φ` for its
internal vertices, and witnesses `wit e ⊆ W` for the `2 #Z - 1` atlas edges, connecting the two
ends of each and pairwise disjoint.

The shape is not fixed in advance: all labelled binary shapes are available, and the witnesses
of the two halves are carried inside the two arm witnesses of the split, so no open edge is
charged twice.  Repeated terminal values are allowed and handled by the degenerate split, whose
arm witnesses are empty. -/
theorem exists_realization (ends : E → Sym2 V) {W : Finset E} {v : V} {y : α → V}
    {Z : Finset α} (hne : Z.Nonempty) (hconn : ∀ a ∈ Z, Conn ends W v (y a)) :
    ∃ (t : RTree α) (φ : t.IPos → V) (wit : AEdge t → Finset E),
      IsLabelledShape t Z ∧ IsRealization ends W y v φ wit :=
  exists_realization_aux ends Z.card W v y Z rfl hne hconn

end PercLib.CriticalLRP.TreeExpansion.Real
