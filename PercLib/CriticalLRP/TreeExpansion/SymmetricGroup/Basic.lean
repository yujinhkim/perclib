/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# Translations on a finite complete graph

Finite componentwise vertex translation and its effect on the complete
configuration of `Sym2 V`. All new definitions live in this Basic module.
-/
module
public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursionFull
public import PercLib.CriticalLRP.BK.Bridge
public import PercLib.CriticalLRP.BK.CanonicalBridge

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open PercLib.CriticalLRP.TreeGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

/-! ### The edge translation of `Sym2 V` -/

/-- Translation of unordered pairs of vertices by `c`. -/
def eshift (c : V) : Sym2 V → Sym2 V := Sym2.map (fun x => x + c)

theorem eshift_mk (c a b : V) : eshift c s(a, b) = s(a + c, b + c) := Sym2.map_mk _ a b

theorem eshift_apply_neg (c : V) (e : Sym2 V) : eshift c (eshift (-c) e) = e := by
  have h : (fun x : V => x + c) ∘ (fun x : V => x + (-c)) = id := by
    funext x; simp
  calc eshift c (eshift (-c) e)
      = (Sym2.map (fun x : V => x + c) ∘ Sym2.map (fun x : V => x + (-c))) e := rfl
    _ = Sym2.map ((fun x : V => x + c) ∘ (fun x : V => x + (-c))) e := by
          rw [Sym2.map_comp]
    _ = Sym2.map id e := by rw [h]
    _ = e := by rw [Sym2.map_id]; rfl

theorem eshift_neg_apply (c : V) (e : Sym2 V) : eshift (-c) (eshift c e) = e := by
  have h : (fun x : V => x + (-c)) ∘ (fun x : V => x + c) = id := by
    funext x; simp
  calc eshift (-c) (eshift c e)
      = (Sym2.map (fun x : V => x + (-c)) ∘ Sym2.map (fun x : V => x + c)) e := rfl
    _ = Sym2.map ((fun x : V => x + (-c)) ∘ (fun x : V => x + c)) e := by
          rw [Sym2.map_comp]
    _ = Sym2.map id e := by rw [h]
    _ = e := by rw [Sym2.map_id]; rfl

/-- The vertex translation `x ↦ x + c` as a permutation of the edge set `Sym2 V`. -/
def eshiftEquiv (c : V) : Sym2 V ≃ Sym2 V where
  toFun := eshift c
  invFun := eshift (-c)
  left_inv := eshift_neg_apply c
  right_inv := eshift_apply_neg c

theorem eshift_injective (c : V) : Function.Injective (eshift c) :=
  (eshiftEquiv c).injective

theorem image_eshift_neg_eshift (c : V) (s : Finset (Sym2 V)) :
    (s.image (eshift c)).image (eshift (-c)) = s := by
  rw [Finset.image_image]
  rw [show (eshift (-c) ∘ eshift c) = id from funext (eshift_neg_apply c)]
  simp

theorem image_eshift_eshift_neg (c : V) (s : Finset (Sym2 V)) :
    (s.image (eshift (-c))).image (eshift c) = s := by
  rw [Finset.image_image]
  rw [show (eshift c ∘ eshift (-c)) = id from funext (eshift_apply_neg c)]
  simp

/-- The bijection of configuration spaces induced by the vertex translation `x ↦ x + c`. -/
def confShift (c : V) : Finset (Sym2 V) ≃ Finset (Sym2 V) where
  toFun s := s.image (eshift c)
  invFun s := s.image (eshift (-c))
  left_inv s := image_eshift_neg_eshift c s
  right_inv s := image_eshift_eshift_neg c s

/-! ### Transport of connectivity -/

/-- The native complete bond graph: every unordered pair is an edge. -/
abbrev cfgEnds : Sym2 V → Sym2 V := PercLib.CriticalLRP.idBondGraph V

theorem openGraph_cfgEnds_adj (s : Finset (Sym2 V)) (u v : V) :
    (TreeGraph.openGraph cfgEnds s).Adj u v ↔ s(u, v) ∈ s ∧ u ≠ v := by
  rw [TreeGraph.openGraph_adj]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hne⟩
    exact ⟨ha, hne⟩
  · rintro ⟨h, hne⟩
    exact ⟨⟨s(u, v), h, rfl⟩, hne⟩

/-- A vertex translation is a graph homomorphism from the open graph of `s` to the open graph
of the translated configuration. -/
def shiftHom (c : V) (s : Finset (Sym2 V)) :
    TreeGraph.openGraph cfgEnds s →g TreeGraph.openGraph cfgEnds (s.image (eshift c)) where
  toFun u := u + c
  map_rel' := by
    intro u v huv
    rw [openGraph_cfgEnds_adj] at huv ⊢
    obtain ⟨huvs, hne⟩ := huv
    exact ⟨Finset.mem_image.mpr ⟨s(u, v), huvs, eshift_mk c u v⟩,
      fun h => hne (add_right_cancel h)⟩

/-- Translation preserves connectivity. -/
theorem conn_image_eshift (c : V) {s : Finset (Sym2 V)} {a b : V}
    (h : Conn cfgEnds s a b) : Conn cfgEnds (s.image (eshift c)) (a + c) (b + c) :=
  SimpleGraph.Reachable.map (shiftHom c s) h

/-- Connectivity is invariant under a vertex translation. -/
theorem conn_image_eshift_iff (c : V) (s : Finset (Sym2 V)) (a b : V) :
    Conn cfgEnds s a b ↔ Conn cfgEnds (s.image (eshift c)) (a + c) (b + c) := by
  refine ⟨conn_image_eshift c, fun h => ?_⟩
  have h2 := conn_image_eshift (-c) h
  rw [image_eshift_neg_eshift] at h2
  simpa using h2

/-! ### Invariance of the constant edge law -/

/-- The constant edge weight `p`. -/
def constP (p : ℝ) : Sym2 V → ℝ := fun _ => p

end

end PercLib.CriticalLRP.TreeExpansion
