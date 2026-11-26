module

public import PercLib.CriticalLRP.BK.FiniteIndex.Canonical
public import PercLib.CriticalLRP.BK.FiniteIndex.Defs
public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Prob

/-!
Join the countable atlas realization to finite-indexed canonical BK.
The countable model is used directly, without finite vertex or edge truncations.
-/

open MeasureTheory

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped ENNReal

namespace CanonAtlas


variable {V : Type*} [DecidableEq V]

/-- The canonical atlas realization carries exactly the witness family on which
finite-index BK was proved. -/
theorem canonAtlasEvent_eq_disjFam {α : Type*} (y : α → V) (x : V)
    (t : PercLib.CriticalLRP.TreeExpansion.RTree α) (φ : t.IPos → V) :
    CanonAtlasEvent y x t φ =
      PercLib.CriticalLRP.Percolation.DisjFam
        (fun e : PercLib.CriticalLRP.TreeExpansion.Real.AEdge t =>
          PercLib.CriticalLRP.connSet
            (PercLib.CriticalLRP.TreeExpansion.Real.srcPos t φ x e)
            (PercLib.CriticalLRP.TreeExpansion.Real.dstPos t φ y e)) := by
  ext ω
  constructor
  · rintro ⟨wit, hsub, hdisj, hconn⟩
    exact ⟨wit, hsub, hconn, hdisj⟩
  · rintro ⟨wit, hsub, hconn, hdisj⟩
    refine ⟨wit, ?_⟩
    exact { subset := hsub
            disjoint := hdisj
            conn := hconn }

end CanonAtlas

namespace CanonAtlas.Measure

variable {V : Type*} [DecidableEq V] [Countable V]

/-- The remaining per-diagram premise is an instance of the independently proved
finite-index canonical BK theorem. -/
theorem canonAtlasEvent_bk (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (x : V) (f : Fin q → V)
    (t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin q) Finset.univ)
    (φ : (t : PercLib.CriticalLRP.TreeExpansion.RTree (Fin q)).IPos → V) :
    PercLib.CriticalLRP.edgeMeasure π (CanonAtlasEvent f x t.1 φ) ≤ atlasProduct π x f t.1 φ := by
  rw [canonAtlasEvent_eq_disjFam]
  exact PercLib.CriticalLRP.edgeMeasure_bk_atlas π hπ f x t.1 φ

/-- The canonical labelled connection event bound, with no residual per-diagram BK premise. -/
theorem measure_labelEvent_le_tsum_bk (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 1 ≤ q) (x : V) (f : Fin q → V) :
    PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' p : (Σ t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin q) Finset.univ, t.1.IPos → V),
        atlasProduct π x f p.1.1 p.2 :=
  measure_labelEvent_le_tsum π hq x f (fun t φ => canonAtlasEvent_bk π hπ x f t φ)

/-- The same canonical atlas/BK bound, split by shape and then internal position. -/
theorem measure_labelEvent_le_tsum_shapes_bk
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 1 ≤ q) (x : V) (f : Fin q → V) :
    PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V,
        atlasProduct π x f t.1 φ :=
  measure_labelEvent_le_tsum_shapes π hq x f (fun t φ => canonAtlasEvent_bk π hπ x f t φ)

end CanonAtlas.Measure

namespace CanAudit
set_option linter.hashCommand false
#print axioms CanonAtlas.canonAtlasEvent_eq_disjFam
#print axioms CanonAtlas.Measure.canonAtlasEvent_bk
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum_bk
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk
end CanAudit
