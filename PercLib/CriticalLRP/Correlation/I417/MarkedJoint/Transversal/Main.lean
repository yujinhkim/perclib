/- Independently rebuilt and integrated UltraMath package `smwwz58hv`, member `m1`.
Production integration revision: `4478d0f5a412be93a92b607d6e30a20cbd89bdb6`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Defs
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Main
public import PercLib.CriticalLRP.Correlation.I417.Base.Poly
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Transversal

/-!
# The marked joint moment over a child-swap transversal

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (arbitrary `p`), marked base side.

For a countable vertex type `V`, an opening profile `π` with `π e < 1` for every edge, a root
`x`, a marked vertex `w` and every `p : ℕ`:

`I417Gen.jointPow π x p w ≤ markedTransversalBound π x w p`,

i.e.

`E[|K_x|^p 1(w ∈ K_x)] ≤
  ∑_{r ∈ transversal (Fin (p+1))} ∑_{φ : r.IPos → V} ∑_{y : Fin (p+1) → V}
    [y (Fin.last p) = w] · ∏_{a ∈ AEdge r} P(src_a ↔ dst_a)`.

This is the same marked moment as `I417Marked.jointPow_le_markedAtlasBound`, but the shape family
is the **transversal** `RTree.transversal (Fin (p+1))` — one plane representative per child-swap
orbit — instead of all fully labelled plane shapes.  The proof goes directly through

* `I417Gen.tsum_labelEvent_inter`, which writes the moment as the arm sum of the events
  `labelEvent x f ∩ connSet x w`;
* `I417Marked.labelEvent_markedExtend`, which identifies that event with the terminal event of
  the marked carrier `Fin.snoc f w`, whose last entry is the physical vertex `w`;
* `CanonAtlas.measure_labelEvent_le_sum_transversal_bk` at `q = p + 1 ≥ 1`, the canonical
  orbit-representative union bound, which needs no finite vertex type, no finite edge type, no
  box and no measurability;
* `I417MarkedRelabel.tsum_markedExtend`, the honest pin reindexing which turns the arm sum back
  into the sum over terminal tuples with `y (Fin.last p) = w`.

There is no division anywhere: the inequality is not obtained from the plane-sum bound by
cancelling a factor `2 ^ p` (which would be illegitimate for an `∞`-valued `ℝ≥0∞` sum).  Instead
the two sums are compared *exactly*:

`I417Marked.markedAtlasBound π x w p = 2 ^ p * markedTransversalBound π x w p`

(`markedAtlasBound_eq_two_pow_mul_markedTransversalBound`).  The factor is `2 ^ p` and not
`2 ^ (p+1)`: the marked joint moment at `p` uses `p + 1` labels, so the shape family is
`RTree.LT (Fin (p+1))` and the orbit size is `2 ^ ((p+1) - 1) = 2 ^ p`.  For `p = 0` the factor
is `1`, as it must be: with no arms there is a single terminal and a single shape.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedTransversal

open PercLib.CriticalLRP (edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion (LTon RTree)
open PercLib.CriticalLRP.TreeExpansion.RTree
open PercLib.CriticalLRP.I417Marked (markedExtend markedAtlasBound)
open PercLib.CriticalLRP.I417MarkedRelabel (pinLast)

variable {V : Type*}

/-! ### The pin and the order of the position and terminal sums -/

/-- The pin at the marking label as an explicit `if`. -/
theorem pinLast_eq_ite [DecidableEq V] {p : ℕ} (w : V) (y : Fin (p + 1) → V) :
    pinLast w y = if y (Fin.last p) = w then 1 else 0 := by
  by_cases h : y (Fin.last p) = w
  · rw [PercLib.CriticalLRP.I417MarkedRelabel.pinLast_of_mem h]
    simp only [h, ite_true]
  · rw [PercLib.CriticalLRP.I417MarkedRelabel.pinLast_of_notMem h]
    simp only [h, ite_false]

/-- **The marked transversal sum with the terminal sum outside the position sum.**  The two
`⊤`-valued sums commute; this is the form in which the totalised box product is compared with
the ordinary plane sum. -/
theorem markedTransversalBound_eq_sum_pos (π : Sym2 V → unitInterval) (x w : V) (p : ℕ) :
    markedTransversalBound π x w p =
      ∑ r ∈ RTree.transversal (Fin (p + 1)),
        ∑' y : Fin (p + 1) → V, pinLast w y *
          (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Eq.trans (ENNReal.tsum_comm
    (f := fun (φ : r.IPos → V) (y : Fin (p + 1) → V) =>
      pinLast w y * CanonAtlas.Measure.atlasProduct π x y r φ)) ?_
  exact tsum_congr fun y => ENNReal.tsum_mul_left

/-! ### The marked joint moment over the transversal -/

/-- The arm form of `markedTransversalBound`: summing the terminal tuples with the last entry
pinned at `w` is the same as summing over the `p` arms at the marked carriers. -/
theorem tsum_transversal_eq_markedTransversalBound [Countable V]
    (π : Sym2 V → unitInterval) (x w : V) (p : ℕ) :
    (∑' f : Fin p → V, ∑ r ∈ RTree.transversal (Fin (p + 1)),
        ∑' φ : r.IPos → V,
          CanonAtlas.Measure.atlasProduct π x (markedExtend w f) r φ)
      = markedTransversalBound π x w p := by
  rw [I417Base.tsum_finset_sum]
  rw [markedTransversalBound_eq_sum_pos]
  exact Finset.sum_congr rfl fun r _ =>
    I417MarkedRelabel.tsum_markedExtend w
      (fun y => ∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ)

/-- **Lemma I.4.17, marked base side, over one plane representative per child-swap orbit.**

The `p`-fold cluster moment of `x` through the physical marked vertex `w` is at most the marked
atlas/BK sum over the transversal `RTree.transversal (Fin (p+1))`.  The terminal tuples are still
`Fin (p+1) → V` with the physical mark pinned by `y (Fin.last p) = w`; repeated physical vertices
are allowed and the `Empty` witness at coincident endpoints is untouched. -/
theorem jointPow_le_markedTransversalBound [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x w : V) (p : ℕ) :
    PercLib.CriticalLRP.I417Gen.jointPow π x p w ≤ markedTransversalBound π x w p := by
  classical
  have harm : PercLib.CriticalLRP.I417Gen.jointPow π x p w
      = ∑' f : Fin p → V, edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x
          (markedExtend w f)) := by
    rw [← PercLib.CriticalLRP.I417Gen.tsum_labelEvent_inter π x p w]
    exact tsum_congr fun f => by rw [PercLib.CriticalLRP.I417Marked.labelEvent_markedExtend]
  rw [harm]
  have hbk : ∀ f : Fin p → V,
      edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x (markedExtend w f)) ≤
        ∑ r ∈ RTree.transversal (Fin (p + 1)),
          ∑' φ : r.IPos → V,
            CanonAtlas.Measure.atlasProduct π x (markedExtend w f) r φ :=
    fun f => CanonAtlas.measure_labelEvent_le_sum_transversal_bk π hπ (Nat.succ_pos p) x
      (markedExtend w f)
  exact (ENNReal.tsum_le_tsum hbk).trans
    (le_of_eq (tsum_transversal_eq_markedTransversalBound π x w p))

/-! ### The exact plane multiplicity: the plane marked sum is `2 ^ p` times the transversal one -/

/-- The plane marked atlas sum in the shape-then-terminal order used by the orbit count. -/
theorem markedAtlasBound_eq_tsum_pos (π : Sym2 V → unitInterval) (x w : V)
    (p : ℕ) :
    markedAtlasBound π x w p =
      ∑' t : LTon (Fin (p + 1)) Finset.univ,
        ∑' y : Fin (p + 1) → V, pinLast w y *
          (∑' φ : t.1.IPos → V, CanonAtlas.Measure.atlasProduct π x y t.1 φ) := by
  classical
  rw [PercLib.CriticalLRP.I417Marked.markedAtlasBound]
  refine tsum_congr fun t => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [pinLast_eq_ite]
  exact ENNReal.tsum_mul_left

/-- **The marked atlas bound is exactly `2 ^ p` times the marked transversal bound.**

The two sides differ only by the plane multiplicity of the shape sum: every child-swap orbit of
fully labelled `(p+1)`-leaf shapes has exactly `2 ^ p` plane representatives
(`RTree.swapOrbits_card`), and the position sum of the atlas product is constant on the orbit
(`CanonAtlas.Measure.tsum_atlasProduct_eq_of_mem_swapFiber`).  The factor is `2 ^ p`, not
`2 ^ (p+1)` and not `1`: `p + 1` labels give `(p + 1) - 1 = p` independent child swaps. -/
theorem markedAtlasBound_eq_two_pow_mul_markedTransversalBound [Countable V]
    (π : Sym2 V → unitInterval) (x w : V) (p : ℕ) :
    markedAtlasBound π x w p = (2 : ℝ≥0∞) ^ p * markedTransversalBound π x w p := by
  classical
  set g : RTree (Fin (p + 1)) → ℝ≥0∞ := fun r =>
    ∑' y : Fin (p + 1) → V, pinLast w y *
      (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ) with hg
  have hinv : ∀ t t' : RTree (Fin (p + 1)), t' ∈ t.swapFiber → g t' = g t := by
    intro t t' h
    refine (tsum_congr fun y => congrArg (fun z => pinLast w y * z) ?_).symm
    exact CanonAtlas.Measure.tsum_atlasProduct_eq_of_mem_swapFiber π x y h
  calc markedAtlasBound π x w p
      = ∑' t : LTon (Fin (p + 1)) Finset.univ, g t.1 := markedAtlasBound_eq_tsum_pos π x w p
    _ = ∑ t : LTon (Fin (p + 1)) Finset.univ, g t.1 := tsum_fintype _
    _ = ∑ t : RTree.LT (Fin (p + 1)), g t.1 := CanonAtlas.Measure.sum_LTon_eq_sum_LT g
    _ = (2 : ℝ≥0∞) ^ (Fintype.card (Fin (p + 1)) - 1) *
          ∑ r ∈ RTree.transversal (Fin (p + 1)), g r :=
        CanonAtlas.OrbitSum.sum_LT_eq_pow_mul_sum_transversal_ennreal g hinv
    _ = (2 : ℝ≥0∞) ^ p * ∑ r ∈ RTree.transversal (Fin (p + 1)), g r := by
        rw [Fintype.card_fin, Nat.succ_sub_one]
    _ = (2 : ℝ≥0∞) ^ p * markedTransversalBound π x w p := by
        rw [markedTransversalBound_eq_sum_pos]

end PercLib.CriticalLRP.I417MarkedTransversal

/-! ### Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.I417MarkedTransversal

#print axioms pinLast_eq_ite
#print axioms markedTransversalBound_eq_sum_pos
#print axioms tsum_transversal_eq_markedTransversalBound
#print axioms jointPow_le_markedTransversalBound
#print axioms markedAtlasBound_eq_tsum_pos
#print axioms markedAtlasBound_eq_two_pow_mul_markedTransversalBound

end PercLib.CriticalLRP.I417MarkedTransversal
