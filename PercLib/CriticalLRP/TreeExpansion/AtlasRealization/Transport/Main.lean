/- Independently rebuilt Ultramath work: smwwsmqji, member m2.
Production base 4c53bb5a8e76a4358a426adf71169b916b90f51f.

The independently verified scratch sources are in `.ultramath/smwwsmqji/m2/`.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Transport.Defs
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Orbit

/-!
# Child-swap transport of atlas realizations

The child-swap position correspondence transports every atlas-edge witness set with no change
to its endpoints.  Consequences here are equality of the diagram-event unions over all internal
positions and equality of their diagram-event probability sums.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*}
variable {α : Type*} [DecidableEq α]

namespace Real

/-- **The transport datum exists.**  For every plane tree `t'` obtained from `t` by exchanging
children, the internal vertices of `t'` correspond bijectively to those of `t` in such a way
that every child slot keeps its vertex after the direction change `flip`. -/
theorem nonempty_swapIso (t : RTree α) (y : α → V) :
    ∀ {t' : RTree α}, t' ∈ RTree.swapFiber t → Nonempty (SwapIso t y t') := by
  induction t with
  | leaf a =>
      intro t' h
      rw [RTree.swapFiber_leaf, Finset.mem_singleton] at h
      subst h
      exact ⟨⟨Equiv.refl Empty,
        fun (e : Empty) => e.elim,
        fun (φ : (RTree.leaf a).IPos → V) (u : Empty) => u.elim,
        fun (φ : (RTree.leaf a).IPos → V) => rfl⟩⟩
  | node l r ihl ihr =>
      intro t' h
      rw [RTree.swapFiber_node] at h
      rcases Finset.mem_union.mp h with h | h
      · -- the children are not exchanged at the root
        obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h
        obtain ⟨l', r'⟩ := p
        obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
        subst hpv
        obtain ⟨Il⟩ := ihl hl
        obtain ⟨Ir⟩ := ihr hr
        refine ⟨{
          σ := Equiv.sumCongr Il.σ (Equiv.sumCongr Ir.σ (Equiv.refl _))
          flip := flipNode Il.flip Ir.flip false
          child_eq := ?_
          root_eq := ?_ }⟩
        · intro φ u b
          rcases u with (u | ⟨v | x⟩)
          · exact Il.child_eq (fun u' => φ (Sum.inl u')) u b
          · exact Ir.child_eq (fun v' => φ (Sum.inr (Sum.inl v'))) v b
          · obtain ⟨⟩ := x
            cases b with
            | false => exact Il.root_eq (fun u' => φ (Sum.inl u'))
            | true => exact Ir.root_eq (fun v' => φ (Sum.inr (Sum.inl v')))
        · intro φ
          rfl
      · -- the children are exchanged at the root
        obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h
        obtain ⟨l', r'⟩ := p
        obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
        subst hpv
        obtain ⟨Il⟩ := ihl hl
        obtain ⟨Ir⟩ := ihr hr
        refine ⟨{
          σ := sumCongrSwap Il.σ Ir.σ
          flip := flipNode Il.flip Ir.flip true
          child_eq := ?_
          root_eq := ?_ }⟩
        · intro φ u b
          rcases u with (u | ⟨v | x⟩)
          · exact Il.child_eq (fun u' => φ (Sum.inl u')) u b
          · exact Ir.child_eq (fun v' => φ (Sum.inr (Sum.inl v'))) v b
          · obtain ⟨⟩ := x
            cases b with
            | false => exact Il.root_eq (fun u' => φ (Sum.inl u'))
            | true => exact Ir.root_eq (fun v' => φ (Sum.inr (Sum.inl v')))
        · intro φ
          rfl

/-! ### Transport of realizations -/

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem IsRealization.transport {ends : E → Sym2 V} {s : Finset E} {y : α → V} {c : V}
    {t t' : RTree α} {φ : t.IPos → V} {wit : AEdge t → Finset E}
    (I : SwapIso t y t') (h : IsRealization ends s y c φ wit) :
    IsRealization ends s y c (I.phi φ) (fun a' => wit (I.aedgeEquiv.symm a')) where
  subset := fun a' => h.subset _
  disjoint := by
    intro a' a'' hne
    exact h.disjoint _ _ fun h' => hne (I.aedgeEquiv.symm.injective h')
  conn := by
    intro a'
    have hc := h.conn (I.aedgeEquiv.symm a')
    rw [← I.srcPos_aedgeEquiv φ c (I.aedgeEquiv.symm a'),
      ← I.dstPos_aedgeEquiv φ (I.aedgeEquiv.symm a'), I.aedgeEquiv.apply_symm_apply] at hc
    exact hc

theorem IsRealization.transport_symm {ends : E → Sym2 V} {s : Finset E} {y : α → V} {c : V}
    {t t' : RTree α} {φ : t.IPos → V} {wit' : AEdge t' → Finset E}
    (I : SwapIso t y t') (h : IsRealization ends s y c (I.phi φ) wit') :
    IsRealization ends s y c φ (fun a => wit' (I.aedgeEquiv a)) where
  subset := fun a => h.subset _
  disjoint := by
    intro a a' hne
    exact h.disjoint _ _ fun h' => hne (I.aedgeEquiv.injective h')
  conn := by
    intro a
    have hc := h.conn (I.aedgeEquiv a)
    rw [I.srcPos_aedgeEquiv φ c a, I.dstPos_aedgeEquiv φ a] at hc
    exact hc

/-- **The diagram event does not see the child order.**  Transporting the position map along the
transport datum leaves `DiagEvent` unchanged, with the *same witness sets*. -/
theorem diagEvent_eq_of_swapIso {ends : E → Sym2 V} {y : α → V} {c : V} {t t' : RTree α}
    (I : SwapIso t y t') (φ : t.IPos → V) :
    DiagEvent ends y c t φ = DiagEvent ends y c t' (I.phi φ) := by
  ext ω
  constructor
  · rintro ⟨wit, hreal⟩
    exact ⟨fun a' => wit (I.aedgeEquiv.symm a'), hreal.transport I⟩
  · rintro ⟨wit, hreal⟩
    exact ⟨fun a => wit (I.aedgeEquiv a), hreal.transport_symm I⟩

/-- For `t'` in the swap orbit of `t`, every diagram event of `t` is a diagram event of `t'`. -/
theorem exists_diagEvent_eq_of_mem_swapFiber {ends : E → Sym2 V} {y : α → V} {c : V}
    {t : RTree α} (φ : t.IPos → V) {t' : RTree α} (h : t' ∈ RTree.swapFiber t) :
    ∃ φ' : t'.IPos → V, DiagEvent ends y c t φ = DiagEvent ends y c t' φ' := by
  obtain ⟨I⟩ := nonempty_swapIso t y h
  exact ⟨I.phi φ, diagEvent_eq_of_swapIso I φ⟩

/-- **The child-swap invariance of the diagram-event union.**  The set of configurations in
which the atlas of `t` is realized for *some* assignment of internal vertices is the same as
for any other plane representative `t'` of the same non-plane tree. -/
theorem iUnion_diagEvent_eq_of_mem_swapFiber {ends : E → Sym2 V} {y : α → V} {c : V}
    {t t' : RTree α} (h : t' ∈ RTree.swapFiber t) :
    (⋃ φ : t.IPos → V, DiagEvent ends y c t φ)
      = (⋃ φ' : t'.IPos → V, DiagEvent ends y c t' φ') := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.iUnion_subset fun φ => ?_
    obtain ⟨φ', hφ⟩ := exists_diagEvent_eq_of_mem_swapFiber (ends := ends) (y := y) (c := c) φ h
    exact hφ ▸ Set.subset_iUnion (fun φ' : t'.IPos → V => DiagEvent ends y c t' φ') φ'
  · refine Set.iUnion_subset fun φ' => ?_
    obtain ⟨φ, hφ⟩ := exists_diagEvent_eq_of_mem_swapFiber (ends := ends) (y := y) (c := c) φ'
      (RTree.swapFiber_symm h)
    exact hφ ▸ Set.subset_iUnion (fun φ : t.IPos → V => DiagEvent ends y c t φ) φ

/-- **The position sum is constant on a swap orbit.**  Since the position spaces of two plane
representatives are matched by `σ : t.IPos ≃ t'.IPos`, the sum over positions of the
diagram-event probabilities is literally the same number: no factor two, no recalculation. -/
theorem sum_prob_diagEvent_eq_of_mem_swapFiber {pr : E → ℝ} {ends : E → Sym2 V} {y : α → V}
    {c : V} {t : RTree α} [Fintype V] {t' : RTree α} (h : t' ∈ RTree.swapFiber t) :
    (∑ φ : t.IPos → V, prob pr (DiagEvent ends y c t φ))
      = ∑ φ' : t'.IPos → V, prob pr (DiagEvent ends y c t' φ') := by
  obtain ⟨I⟩ := nonempty_swapIso t y h
  refine Fintype.sum_equiv (Equiv.arrowCongr I.σ (Equiv.refl V)) (fun φ : t.IPos → V =>
    prob pr (DiagEvent ends y c t φ)) (fun φ' : t'.IPos → V =>
    prob pr (DiagEvent ends y c t' φ')) (fun φ => ?_)
  exact congrArg (prob pr) (diagEvent_eq_of_swapIso I φ)

end Real

end PercLib.CriticalLRP.TreeExpansion
