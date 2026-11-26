module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs
public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join

/-!
# The marked joint-moment bound: the label transport

This file supplies the two transport facts that turn the `p`-armed marked moment
`I417Gen.jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]` into a sum over the *marked carrier*
`Fin (p + 1) → V` of `PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs`.

* `labelEvent_markedExtend` -- the terminal event of the carrier `markedExtend w f` is exactly
  the marked arm event `labelEvent x f ∩ connSet x w`.  Thus the sum over the arm labelling
  `Fin p → V` in `I417Gen.tsum_labelEvent_inter` is the same as a sum over the carriers whose
  last label is `w`, which is the terminal map at which the canonical atlas covering theorem
  `CanonAtlas.exists_canonical_realization` applies.

* `tsum_markedExtend` -- summing a function of the carrier over all arm tuples is the same as
  summing over **all** `(p + 1)`-labelled terminal tuples with the last entry pinned at `w`,
  the pinning written as the `ℝ≥0∞`-indicator `if y (Fin.last p) = w then 1 else 0`.  The
  proof is `Equiv.tsum_eq` for the explicit label equivalence `markedSubtypeEquiv w p`
  followed by `tsum_subtype`; no finiteness of `V` and no truncation of the terminal sum is
  used.

* `markedAtlasBound_eq_tsum_markedExtend` -- consequently the atlas/BK right-hand side of the
  bound is *identically* the sum over the arm labelling of the atlas products at the carriers
  `markedExtend w f`.  This is the honest reindexing of the finite shape family, the position
  family of the internal vertices, and the terminal placements: no shape, position or
  terminal is dropped or duplicated.

Nothing here is an inequality: these are equalities of `ℝ≥0∞`-valued sums.
-/

@[expose] public section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP (connSet mem_cluster_iff)

open PercLib.CriticalLRP.TreeExpansion (LTon)

variable {V : Type*}

/-! ### The terminal event of the marked carrier -/

/-- **The marked arm event is the terminal event of the marked carrier.**

The terminal event of the `p + 1` labels of `markedExtend w f` is the `p`-labelled event of
the arms `f` together with the connection `x ↔ w` of the mark.  In particular the mark is the
*physical* vertex `w`, not a choice of arm. -/
theorem labelEvent_markedExtend [Countable V] (x w : V) {p : ℕ} (f : Fin p → V) :
    I417A.labelEvent x (markedExtend w f) = I417A.labelEvent x f ∩ connSet x w := by
  ext ω
  simp only [I417A.labelEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, connSet, mem_cluster_iff]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last p)⟩
  · rintro ⟨hf, hw⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
    · simpa using hf j
    · subst h
      simpa using hw

/-! ### Summing the carrier family with the last label pinned -/

/-- **The pinning reindexing.**  A sum over the arm labelling `Fin p → V` of the values of `G`
at the carriers `markedExtend w f` equals the sum over *all* `(p + 1)`-labelled terminal
tuples in which the last entry is the physical vertex `w`; the pinning contributes the factor
`if y (Fin.last p) = w then 1 else 0`.

This is `Equiv.tsum_eq` for the label equivalence `markedSubtypeEquiv w p` (whose inverse is
`Fin.init`) composed with `tsum_subtype` for the subtype of pinned tuples. -/
theorem tsum_markedExtend {p : ℕ} (w : V) (G : (Fin (p + 1) → V) → ℝ≥0∞) :
    (∑' f : Fin p → V, G (markedExtend w f)) =
      ∑' y : Fin (p + 1) → V, (if y (Fin.last p) = w then 1 else 0) * G y := by
  have hpin : (∑' y : Fin (p + 1) → V, (if y (Fin.last p) = w then (1 : ℝ≥0∞) else 0) * G y)
      = ∑' y : Fin (p + 1) → V,
          ({y : Fin (p + 1) → V | y (Fin.last p) = w} : Set (Fin (p + 1) → V)).indicator G y :=
    tsum_congr fun y => by
      by_cases h : y (Fin.last p) = w
      · simp [Set.indicator_of_mem, h]
      · simp [Set.indicator_of_notMem, h]
  rw [hpin, ← tsum_subtype]
  refine Eq.trans (tsum_congr fun f => ?_) (Equiv.tsum_eq (markedSubtypeEquiv w p)
    (fun y : {y : Fin (p + 1) → V // y (Fin.last p) = w} => G y.1))
  rw [markedSubtypeEquiv_apply]

/-- **The atlas/BK right-hand side of the marked bound is the arm sum at the carriers.**

The `y`-sum over the pinned terminal tuples of `markedAtlasBound` is exactly the sum over the
`p` arms of the atlas products computed at the carrier `markedExtend w f`; the fully labelled
shape family `LTon (Fin (p + 1)) Finset.univ` and the position family `t.1.IPos → V` are
untouched. -/
theorem markedAtlasBound_eq_tsum_markedExtend (π : Sym2 V → unitInterval) (x w : V) (p : ℕ) :
    markedAtlasBound π x w p =
      ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
        ∑' φ : t.1.IPos → V, ∑' f : Fin p → V,
          CanonAtlas.Measure.atlasProduct π x (markedExtend w f) t.1 φ := by
  refine tsum_congr fun t => tsum_congr fun φ => ?_
  exact (tsum_markedExtend w fun y => CanonAtlas.Measure.atlasProduct π x y t.1 φ).symm

end PercLib.CriticalLRP.I417Marked
