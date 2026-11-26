/- Independently rebuilt Ultramath work: smwwsmqji, member m2.
Production base 4c53bb5a8e76a4358a426adf71169b916b90f51f.

The independently verified scratch sources are in `.ultramath/smwwsmqji/m2/`.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.TreeExpansion.Orbit

/-!
# Child-swap atlas transport: definitions

This module supplies the explicit internal-position and atlas-edge correspondences used to
transport the edge-disjoint diagram realization of `TreeExpansion.Real` between two plane
representatives of the same child-swap orbit.  The position map and the endpoint equations
are independent of the configuration.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion.Real

variable {V : Type*}
variable {α : Type*} [DecidableEq α]

/-! ### The direction change of a child slot -/

/-- `flipBit f b` is `!b` when `f` is `true` and `b` otherwise: the direction change a child
slot suffers when the two children of its parent are exchanged. -/
def flipBit (f b : Bool) : Bool := if f then !b else b

@[simp] theorem flipBit_true (b : Bool) : flipBit true b = !b := rfl

@[simp] theorem flipBit_false (b : Bool) : flipBit false b = b := rfl

theorem flipBit_involutive (f : Bool) : Function.Involutive (flipBit f) := by
  intro b
  cases f <;> cases b <;> rfl

theorem flipBit_injective (f : Bool) : Function.Injective (flipBit f) :=
  (flipBit_involutive f).injective

/-- The position correspondence of a root-level child exchange, with an untouched third
summand (`PUnit` for `RTree.IPos`, which is the right-nested `IPos l ⊕ (IPos r ⊕ PUnit)`).
The first summand `α₁` is moved behind `β₂` and the correspondences `e₁`, `e₂` are applied on the
way; this is the position change of `node l r ↦ node r' l'` with `e₁ : l.IPos ≃ l'.IPos` and
`e₂ : r.IPos ≃ r'.IPos`. -/
def sumCongrSwap {α₁ α₂ β₁ β₂ γ : Type*} (e₁ : α₁ ≃ β₁) (e₂ : α₂ ≃ β₂) :
    α₁ ⊕ (α₂ ⊕ γ) ≃ β₂ ⊕ (β₁ ⊕ γ) where
  toFun
    | Sum.inl a => Sum.inr (Sum.inl (e₁ a))
    | Sum.inr (Sum.inl b) => Sum.inl (e₂ b)
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  invFun
    | Sum.inl b => Sum.inr (Sum.inl (e₂.symm b))
    | Sum.inr (Sum.inl a) => Sum.inl (e₁.symm a)
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  left_inv := by
    rintro (a | b | c) <;> simp
  right_inv := by
    rintro (b | a | c) <;> simp

/-- The direction change of the composite shape `node l r`: the changes `fl` and `fr` of the two
halves, and `bt` at the root.  `RTree.IPos (node l r)` is the right-nested
`l.IPos ⊕ (r.IPos ⊕ PUnit)`, matching `RTree.pushPhi` and `Real.childPos`. -/
def flipNode {α : Type*} {l r : RTree α} (fl : l.IPos → Bool) (fr : r.IPos → Bool)
    (bt : Bool) : (RTree.node l r).IPos → Bool :=
  fun u => match u with
    | Sum.inl u => fl u
    | Sum.inr (Sum.inl v) => fr v
    | Sum.inr (Sum.inr _) => bt

@[simp] theorem flipNode_inl {α : Type*} {l r : RTree α} (fl : l.IPos → Bool)
    (fr : r.IPos → Bool) (bt : Bool) (u : l.IPos) :
    flipNode fl fr bt (Sum.inl u) = fl u := rfl

@[simp] theorem flipNode_inr_inl {α : Type*} {l r : RTree α} (fl : l.IPos → Bool)
    (fr : r.IPos → Bool) (bt : Bool) (v : r.IPos) :
    flipNode fl fr bt (Sum.inr (Sum.inl v)) = fr v := rfl

@[simp] theorem flipNode_inr_inr {α : Type*} {l r : RTree α} (fl : l.IPos → Bool)
    (fr : r.IPos → Bool) (bt : Bool) (x : PUnit) :
    flipNode fl fr bt (Sum.inr (Sum.inr x)) = bt := rfl

/-! ### The transport datum -/

/-- **The child-swap transport datum.**  `σ` matches the internal vertices of `t` with those of
`t'`, `flip` says at which internal vertices the two children were exchanged, and the two
equations say that every child slot and the root keep their vertex when the position map of
`t'` is the transported map `φ ∘ σ.symm`.  The atlas edges of `t` and `t'` then match with the
*same ordered pair of ends* via `SwapIso.aedgeEquiv`. -/
structure SwapIso (t : RTree α) (y : α → V) (t' : RTree α) where
  /-- the internal vertices of `t'` are those of `t` -/
  σ : t.IPos ≃ t'.IPos
  /-- at which internal vertices the two children were exchanged -/
  flip : t.IPos → Bool
  /-- the child in direction `b` of `u` in `t` is the child in direction `flipBit (flip u) b`
  of `σ u` in `t'` -/
  child_eq : ∀ (φ : t.IPos → V) (u : t.IPos) (b : Bool),
    childPos t' (fun u' => φ (σ.symm u')) y (σ u) (flipBit (flip u) b) = childPos t φ y u b
  /-- the root of the shape sits at the same vertex -/
  root_eq : ∀ φ : t.IPos → V, rootPos t' (fun u' => φ (σ.symm u')) y = rootPos t φ y

namespace SwapIso

variable {t t' : RTree α} {y : α → V}

/-- The position map of `t'` transported from the position map `φ` of `t`. -/
def phi (I : SwapIso t y t') (φ : t.IPos → V) : t'.IPos → V := fun u' => φ (I.σ.symm u')

theorem phi_apply (I : SwapIso t y t') (φ : t.IPos → V) (u : t.IPos) :
    I.phi φ (I.σ u) = φ u := by
  simp [phi]

/-- The atlas-edge correspondence of the transport data: the down edge of `u` in direction
`b` corresponds to the down edge of `σ u` in the direction changed by `flip`, and the root edge
corresponds to the root edge. -/
def aedgeFun (I : SwapIso t y t') : AEdge t → AEdge t' :=
  fun a => match a with
    | Sum.inl (u, b) => Sum.inl (I.σ u, flipBit (I.flip u) b)
    | Sum.inr x => Sum.inr x

/-- The inverse atlas-edge correspondence. -/
def aedgeInv (I : SwapIso t y t') : AEdge t' → AEdge t :=
  fun a => match a with
    | Sum.inl (u', b) => Sum.inl (I.σ.symm u', flipBit (I.flip (I.σ.symm u')) b)
    | Sum.inr x => Sum.inr x

theorem aedgeInv_fun (I : SwapIso t y t') (a : AEdge t) : I.aedgeInv (I.aedgeFun a) = a := by
  rcases a with (⟨u, b⟩ | x)
  · change Sum.inl (I.σ.symm (I.σ u),
      flipBit (I.flip (I.σ.symm (I.σ u))) (flipBit (I.flip u) b)) = Sum.inl (u, b)
    rw [Equiv.symm_apply_apply, flipBit_involutive]
  · rfl

theorem aedgeFun_inv (I : SwapIso t y t') (a : AEdge t') : I.aedgeFun (I.aedgeInv a) = a := by
  rcases a with (⟨u', b⟩ | x)
  · change Sum.inl (I.σ (I.σ.symm u'),
      flipBit (I.flip (I.σ.symm u')) (flipBit (I.flip (I.σ.symm u')) b)) = Sum.inl (u', b)
    rw [Equiv.apply_symm_apply, flipBit_involutive]
  · rfl

/-- The atlas edges of `t` correspond bijectively to those of `t'`. -/
def aedgeEquiv (I : SwapIso t y t') : AEdge t ≃ AEdge t' where
  toFun := I.aedgeFun
  invFun := I.aedgeInv
  left_inv := I.aedgeInv_fun
  right_inv := I.aedgeFun_inv

/-- The correspondence preserves the upper end of every atlas edge. -/
theorem srcPos_aedgeEquiv (I : SwapIso t y t') (φ : t.IPos → V) (c : V) (a : AEdge t) :
    srcPos t' (I.phi φ) c (I.aedgeEquiv a) = srcPos t φ c a := by
  rcases a with (⟨u, b⟩ | x)
  · exact I.phi_apply φ u
  · rfl

/-- The correspondence preserves the lower end of every atlas edge. -/
theorem dstPos_aedgeEquiv (I : SwapIso t y t') (φ : t.IPos → V) (a : AEdge t) :
    dstPos t' (I.phi φ) y (I.aedgeEquiv a) = dstPos t φ y a := by
  rcases a with (⟨u, b⟩ | x)
  · exact I.child_eq φ u b
  · exact I.root_eq φ

end SwapIso

end PercLib.CriticalLRP.TreeExpansion.Real
