/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The deterministic branch-point decomposition of the event "the root is connected to every
terminal", the event-level input to the tree-graph inequality (I.2.2) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

Statement (`exists_branch_split`): if `v` is connected to every value `y a` (`a : α`, `α` a
finite type) and the values are not all equal, then there are

* a vertex `w` (the branch point),
* a partition of the terminals into two nonempty groups `A` and `Aᶜ`,
* pairwise disjoint open edge sets `W0`, `WA`, `WB`, with `W0` witnessing `v ↔ w`,
  `WA` witnessing `w ↔ y a` for all `a ∈ A`, and `WB` witnessing `w ↔ y b` for all `b ∈ Aᶜ`.

Here `w` is the deepest common ancestor of the terminal values in a shortest-path tree
rooted at `v`, and the two groups collect the terminals lying in different child branches
of `w`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Forest

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

variable {ends : E → Sym2 V} {s : Finset E} {v : V}

/-! ### Auxiliary ancestor lemmas -/

/-- `childOf u w` is an ancestor of `u`. -/
theorem anc_childOf {u w : V} (h : Anc ends s v u w) (hw : lvl ends s v w < lvl ends s v u) :
    Anc ends s v u (childOf ends s v u w) :=
  anc_iter (by have := childOf_lvl h hw; omega)

/-- An ancestor at level `lvl w + 1` of a descendant of `w` is the child of `w` on its chain. -/
theorem childOf_eq_of_anc {z c w : V} (hz : Anc ends s v z w) (hzc : Anc ends s v z c)
    (hl : lvl ends s v c = lvl ends s v w + 1) : childOf ends s v z w = c := by
  have hlt : lvl ends s v w < lvl ends s v z := by
    have := anc_lvl_le hzc
    omega
  have h2 : lvl ends s v (childOf ends s v z w) = lvl ends s v w + 1 := childOf_lvl hz hlt
  exact anc_eq_of_lvl_eq (anc_childOf hz hlt) hzc (by rw [h2, hl])

/-- A strict ancestor has a strictly smaller level. -/
theorem lvl_lt_of_anc_ne {z w : V} (h : Anc ends s v z w) (hne : z ≠ w) :
    lvl ends s v w < lvl ends s v z := by
  have h1 := anc_lvl_le h
  rcases Nat.lt_or_ge (lvl ends s v w) (lvl ends s v z) with h2 | h2
  · exact h2
  · exact absurd (anc_eq_of_lvl_eq (anc_refl z) h (by omega)) hne

/-! ### The deepest common ancestor of the terminal values -/

/-- All ancestors of the terminal values `y a`. -/
def ancClosure (ends : E → Sym2 V) (s : Finset E) (v : V) {α : Type*} [Fintype α]
    (y : α → V) : Finset V :=
  Finset.univ.biUnion
    (fun a => (Finset.range (lvl ends s v (y a) + 1)).image (fun k => (par ends s v)^[k] (y a)))

/-- The common ancestors of all terminal values. -/
def commonAnc (ends : E → Sym2 V) (s : Finset E) (v : V) {α : Type*} [Fintype α]
    (y : α → V) : Finset V := by
  classical
  exact (ancClosure ends s v y).filter (fun u => ∀ a : α, Anc ends s v (y a) u)

theorem mem_ancClosure {α : Type*} [Fintype α] {y : α → V} {u : V} :
    u ∈ ancClosure ends s v y ↔ ∃ a : α, Anc ends s v (y a) u := by
  constructor
  · intro h
    rw [ancClosure, Finset.mem_biUnion] at h
    obtain ⟨a, -, hu⟩ := h
    rw [Finset.mem_image] at hu
    obtain ⟨k, hk, rfl⟩ := hu
    exact ⟨a, anc_iter (by rw [Finset.mem_range] at hk; omega)⟩
  · rintro ⟨a, k, hk, hkw⟩
    rw [ancClosure, Finset.mem_biUnion]
    exact ⟨a, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hkw⟩⟩

theorem mem_commonAnc {α : Type*} [Fintype α] {y : α → V} {u : V} :
    u ∈ commonAnc ends s v y ↔ (∃ a : α, Anc ends s v (y a) u) ∧ ∀ a : α, Anc ends s v (y a) u := by
  classical
  rw [commonAnc, Finset.mem_filter, mem_ancClosure]

theorem commonAnc_anc {α : Type*} [Fintype α] {y : α → V} {u : V}
    (h : u ∈ commonAnc ends s v y) : ∀ a : α, Anc ends s v (y a) u :=
  ((mem_commonAnc).mp h).2

theorem commonAnc_mem {α : Type*} [Fintype α] {y : α → V} {u : V} (hα : Nonempty α)
    (h : ∀ a : α, Anc ends s v (y a) u) : u ∈ commonAnc ends s v y := by
  classical
  rw [mem_commonAnc]
  exact ⟨⟨Classical.choice hα, h _⟩, h⟩

theorem commonAnc_nonempty {α : Type*} [Fintype α] (y : α → V)
    (hconn : ∀ a, Conn ends s v (y a)) (hα : Nonempty α) :
    (commonAnc ends s v y).Nonempty := by
  refine ⟨v, commonAnc_mem hα ?_⟩
  intro a
  exact ⟨lvl ends s v (y a), le_rfl, par_iter_root (hconn a)⟩

/-! ### The two kinds of terminal group -/

/-- The group of terminal positions whose value is the vertex `w`. -/
def valueGroup {α : Type*} [Fintype α] (w : V) (y : α → V) : Finset α :=
  Finset.univ.filter (fun a => y a = w)

/-- The group of terminal positions lying in the child branch `c` of the branch point. -/
def childBranch (ends : E → Sym2 V) (s : Finset E) (v : V) {α : Type*} [Fintype α]
    (c : V) (y : α → V) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => Anc ends s v (y a) c)

theorem mem_valueGroup {α : Type*} [Fintype α] {w : V} {y : α → V} {a : α} :
    a ∈ valueGroup w y ↔ y a = w := by
  simp [valueGroup]

theorem mem_childBranch {α : Type*} [Fintype α] {c : V} {y : α → V} {a : α} :
    a ∈ childBranch ends s v c y ↔ Anc ends s v (y a) c := by
  classical
  simp [childBranch]

/-- The conclusion of the branch-point decomposition at a fixed branch point `w`. -/
def BranchSplitW {α : Type*} [Fintype α] [DecidableEq α] (ends : E → Sym2 V) (s : Finset E)
    (v : V) (y : α → V) (w : V) (A : Finset α) (W0 WA WB : Finset E) : Prop :=
  A.Nonempty ∧ Aᶜ.Nonempty ∧ W0 ⊆ s ∧ WA ⊆ s ∧ WB ⊆ s ∧
  Disjoint W0 WA ∧ Disjoint W0 WB ∧ Disjoint WA WB ∧
  Conn ends W0 v w ∧
  (∀ a ∈ A, Conn ends WA w (y a)) ∧
  (∀ b ∈ Aᶜ, Conn ends WB w (y b))

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Case 1 of the branch split: some terminal value sits at the branch point `w`. -/
theorem branch_split_w_mem (y : α → V) {w : V} (hwca : ∀ a : α, Anc ends s v (y a) w)
    (hwv : Anc ends s v w v) (hex : ∃ a : α, y a = w) (hne : ∃ a b : α, y a ≠ y b) :
    BranchSplitW ends s v y w (valueGroup w y) (belowChain ends s v w v) ∅
      ((valueGroup w y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) := by
  classical
  obtain ⟨a₁, ha₁⟩ := hex
  obtain ⟨a₀, b₀, hab⟩ := hne
  have hW0sub : belowChain ends s v w v ⊆ s :=
    belowChain_subset (by rw [lvl_root]; exact Nat.zero_le _)
  have hsub : ∀ b : α, belowChain ends s v (y b) w ⊆ s :=
    fun b => belowChain_subset (anc_lvl_le (hwca b))
  have hlvl_lt : ∀ b : α, y b ≠ w → lvl ends s v w < lvl ends s v (y b) :=
    fun b hb => lvl_lt_of_anc_ne (hwca b) hb
  have hAne : (valueGroup w y).Nonempty := ⟨a₁, mem_valueGroup.mpr ha₁⟩
  have hAcne : (valueGroup w y)ᶜ.Nonempty := by
    rcases eq_or_ne (y a₀) w with h | h
    · refine ⟨b₀, Finset.mem_compl.mpr ?_⟩
      exact fun hmem => hab (by rw [h, mem_valueGroup.mp hmem])
    · exact ⟨a₀, Finset.mem_compl.mpr (fun hmem => h (mem_valueGroup.mp hmem))⟩
  have hWBsub : ((valueGroup w y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) ⊆ s := by
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨b, -, hb⟩ := ha
    exact hsub b hb
  have hd : Disjoint (belowChain ends s v w v)
      ((valueGroup w y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) := by
    rw [Finset.disjoint_biUnion_right]
    intro b hb
    exact disjoint_belowChain_root (hwca b) (hlvl_lt b (fun h => (Finset.mem_compl.mp hb) (mem_valueGroup.mpr h)))
  have hAconn : ∀ a ∈ valueGroup w y, Conn ends ∅ w (y a) := by
    intro a ha
    rw [mem_valueGroup.mp ha]
    exact conn_refl ends ∅ w
  have hBconn : ∀ b ∈ (valueGroup w y)ᶜ,
      Conn ends ((valueGroup w y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) w (y b) := by
    intro b hb
    exact conn_mono (Finset.subset_biUnion_of_mem _ hb) (conn_belowChain (hwca b))
  exact ⟨hAne, hAcne, hW0sub, Finset.empty_subset _, hWBsub, Finset.disjoint_empty_right _,
    hd, Finset.disjoint_empty_left _, conn_belowChain hwv, hAconn, hBconn⟩

/-- Case 2 of the branch split: no terminal value sits at the branch point `w`; the two
groups are the terminals lying in the child branch `c₁` of `w` and in the other branches. -/
theorem branch_split_not_mem (y : α → V) {w c₁ : V} (hwca : ∀ a : α, Anc ends s v (y a) w)
    (hwv : Anc ends s v w v) (hno : ∀ a : α, y a ≠ w)
    (hparc₁ : par ends s v c₁ = w) (hlvlc₁ : lvl ends s v c₁ = lvl ends s v w + 1)
    (hexists : ∃ a : α, Anc ends s v (y a) c₁)
    (hmax : ∀ c : V, (∀ a : α, Anc ends s v (y a) c) → lvl ends s v c ≤ lvl ends s v w) :
    BranchSplitW ends s v y w (childBranch ends s v c₁ y) (belowChain ends s v w v)
      ((childBranch ends s v c₁ y).biUnion (fun a => belowChain ends s v (y a) w))
      ((childBranch ends s v c₁ y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) := by
  classical
  have hW0sub : belowChain ends s v w v ⊆ s :=
    belowChain_subset (by rw [lvl_root]; exact Nat.zero_le _)
  have hsub : ∀ b : α, belowChain ends s v (y b) w ⊆ s :=
    fun b => belowChain_subset (anc_lvl_le (hwca b))
  have hlvl_lt : ∀ b : α, lvl ends s v w < lvl ends s v (y b) :=
    fun b => lvl_lt_of_anc_ne (hwca b) (hno b)
  have hA_child : ∀ a ∈ childBranch ends s v c₁ y, childOf ends s v (y a) w = c₁ :=
    fun a ha => childOf_eq_of_anc (hwca a) (mem_childBranch.mp ha) hlvlc₁
  have hB_child : ∀ b ∈ (childBranch ends s v c₁ y)ᶜ,
      childOf ends s v (y b) w ≠ c₁ := by
    intro b hb hbc
    refine (Finset.mem_compl.mp hb) ?_
    rw [mem_childBranch]
    exact hbc ▸ anc_childOf (hwca b) (hlvl_lt b)
  have hA_anc : ∀ a ∈ childBranch ends s v c₁ y, Anc ends s v (y a) w := by
    intro a ha
    obtain ⟨k, hk, hkw⟩ := mem_childBranch.mp ha
    have hklvl : lvl ends s v c₁ = lvl ends s v (y a) - k := by
      rw [← hkw]
      exact lvl_par_iter_eq (ends := ends) (s := s) (v := v) (y a) hk
    refine ⟨k + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply', hkw, hparc₁]
  have hAne : (childBranch ends s v c₁ y).Nonempty := by
    obtain ⟨a, ha⟩ := hexists
    exact ⟨a, mem_childBranch.mpr ha⟩
  have hAcne : (childBranch ends s v c₁ y)ᶜ.Nonempty := by
    by_contra hcontra
    rw [Finset.not_nonempty_iff_eq_empty] at hcontra
    have hall : ∀ a : α, Anc ends s v (y a) c₁ := by
      intro a
      by_contra ha
      have hmem : a ∈ (childBranch ends s v c₁ y)ᶜ :=
        Finset.mem_compl.mpr (fun h => ha (mem_childBranch.mp h))
      rw [hcontra] at hmem
      exact absurd hmem (Finset.notMem_empty a)
    have := hmax c₁ hall
    omega
  have hWAsub : ((childBranch ends s v c₁ y).biUnion
      (fun a => belowChain ends s v (y a) w)) ⊆ s := by
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨b, -, hb⟩ := ha
    exact hsub b hb
  have hWBsub : ((childBranch ends s v c₁ y)ᶜ.biUnion
      (fun b => belowChain ends s v (y b) w)) ⊆ s := by
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨b, -, hb⟩ := ha
    exact hsub b hb
  have hd0A : Disjoint (belowChain ends s v w v)
      ((childBranch ends s v c₁ y).biUnion (fun a => belowChain ends s v (y a) w)) := by
    rw [Finset.disjoint_biUnion_right]
    intro a ha
    exact disjoint_belowChain_root (hA_anc a ha) (hlvl_lt a)
  have hd0B : Disjoint (belowChain ends s v w v)
      ((childBranch ends s v c₁ y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) := by
    rw [Finset.disjoint_biUnion_right]
    intro b _
    exact disjoint_belowChain_root (hwca b) (hlvl_lt b)
  have hdAB : Disjoint ((childBranch ends s v c₁ y).biUnion (fun a => belowChain ends s v (y a) w))
      ((childBranch ends s v c₁ y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w)) := by
    rw [Finset.disjoint_biUnion_left]
    intro a ha
    rw [Finset.disjoint_biUnion_right]
    intro b hb
    refine disjoint_belowChain (hA_anc a ha) (hwca b) ?_
    rw [hA_child a ha]
    exact fun h => hB_child b hb h.symm
  have hAconn : ∀ a ∈ childBranch ends s v c₁ y,
      Conn ends ((childBranch ends s v c₁ y).biUnion (fun a => belowChain ends s v (y a) w))
        w (y a) :=
    fun a ha => conn_mono (Finset.subset_biUnion_of_mem _ ha) (conn_belowChain (hA_anc a ha))
  have hBconn : ∀ b ∈ (childBranch ends s v c₁ y)ᶜ,
      Conn ends ((childBranch ends s v c₁ y)ᶜ.biUnion (fun b => belowChain ends s v (y b) w))
        w (y b) :=
    fun b hb => conn_mono (Finset.subset_biUnion_of_mem _ hb) (conn_belowChain (hwca b))
  exact ⟨hAne, hAcne, hW0sub, hWAsub, hWBsub, hd0A, hd0B, hdAB, conn_belowChain hwv,
    hAconn, hBconn⟩

/-- **The branch-point decomposition.** -/
theorem exists_branch_split (y : α → V) (hconn : ∀ a, Conn ends s v (y a))
    (hne : ∃ a b : α, y a ≠ y b) :
    ∃ (w : V) (A : Finset α) (W0 WA WB : Finset E),
      BranchSplitW ends s v y w A W0 WA WB := by
  classical
  obtain ⟨a₀, b₀, hab⟩ := hne
  have hα : Nonempty α := ⟨a₀⟩
  obtain ⟨w, hwmem, hwmax⟩ := Finset.exists_max_image
    (commonAnc ends s v y) (lvl ends s v) (commonAnc_nonempty y hconn hα)
  have hwca : ∀ a : α, Anc ends s v (y a) w := commonAnc_anc hwmem
  have hwreach : Conn ends s v w :=
    (hconn a₀).trans (conn_symm (conn_mono (belowChain_subset (anc_lvl_le (hwca a₀)))
      (conn_belowChain (hwca a₀))))
  have hwv : Anc ends s v w v := ⟨lvl ends s v w, le_rfl, par_iter_root hwreach⟩
  have hmax : ∀ c : V, (∀ a : α, Anc ends s v (y a) c) → lvl ends s v c ≤ lvl ends s v w :=
    fun c hc => hwmax c (commonAnc_mem hα hc)
  by_cases hcase : ∃ a, y a = w
  · exact ⟨w, _, _, _, _, branch_split_w_mem y hwca hwv hcase ⟨a₀, b₀, hab⟩⟩
  · push Not at hcase
    have hlt₀ : lvl ends s v w < lvl ends s v (y a₀) := lvl_lt_of_anc_ne (hwca a₀) (hcase a₀)
    have hparc₁ : par ends s v (childOf ends s v (y a₀) w) = w := childOf_par (hwca a₀) hlt₀
    have hlvlc₁ : lvl ends s v (childOf ends s v (y a₀) w) = lvl ends s v w + 1 :=
      childOf_lvl (hwca a₀) hlt₀
    exact ⟨w, _, _, _, _, branch_split_not_mem y hwca hwv hcase hparc₁ hlvlc₁
      ⟨a₀, anc_childOf (hwca a₀) hlt₀⟩ hmax⟩

end

end PercLib.CriticalLRP.TreeGraph
