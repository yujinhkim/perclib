module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Label

/-!
# The marked joint-moment bound: assembly

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (arbitrary `p`), marked base side.

For a countable vertex type `V`, an opening profile `π : Sym2 V → unitInterval` with
`π e < 1` for every edge `e`, a root `x : V`, a marked vertex `w : V` and every `p : ℕ`, the
`p`-th cluster moment of `x` through `w` is bounded by the explicit canonical atlas/BK sum:

`I417Gen.jointPow π x p w ≤ markedAtlasBound π x w p`

where (see `PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs`)

`markedAtlasBound π x w p
  = ∑_t ∑_{φ : t.IPos → V} ∑_{y : Fin (p+1) → V} [y (last p) = w] · atlasProduct π x y t φ`

with `t` ranging over the fully labelled binary shapes with `p + 1` leaves labelled by
`Fin (p + 1)`, `φ` over the positions of the internal vertices of `t`, and `atlasProduct` the
product of the connection probabilities of the `2 (p + 1) - 1` atlas edges of `t` at
`(x, y, φ)`.  The mark is the **last** label `Fin.last p`, pinned to the physical vertex `w`;
no child/position choice replaces it.

## The proof

1. `I417Gen.tsum_labelEvent_inter` writes the moment as the sum over the arm labelling
   `f : Fin p → V` of the probabilities of `labelEvent x f ∩ connSet x w`.
2. `labelEvent_markedExtend` identifies that event with the terminal event
   `I417A.labelEvent x (markedExtend w f)` of the marked carrier, whose last label is `w`.
3. `CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk` bounds the terminal event of an
   arbitrary `q`-tuple (`q = p + 1 ≥ 1`) by the canonical atlas/BK sum.  It is the composition
   of the covering theorem `CanonAtlas.exists_canonical_realization` (via
   `labelEvent_subset_canonCover`), countable subadditivity of `edgeMeasure π`, and the
   canonical finite-index BK law `edgeMeasure_bk_atlas` for each diagram.  There is no
   finite-box assumption, no measurability of the atlas events, and no interchange of limits.
4. The resulting triple sum is rearranged (`ENNReal.tsum_comm`) and the pinned terminal sum is
   rewritten into the arm sum with `tsum_markedExtend`; this is exactly
   `markedAtlasBound_eq_tsum_markedExtend`, the honest reindexing of the finite shape family,
   the position family and the terminal placements.  Nothing is dropped or double counted, and
   the shapes, positions and terminal assignments are not changed.

Specialisation `p = 0` is included: there are no arms, the only marked carrier is the constant
tuple at `w`, and the bound reads `E[1(w ∈ K_x)] ≤ ∑_{t,φ} atlasProduct π x (fun _ => w) t φ`,
which is the single-marked-leaf instance of the canonical covering bound.

The conclusion is only this marked canonical atlas/BK bound; it is not the full polygon
`∑_ℓ C_{p,q,ℓ}` of Lemma I.4.17 and not the generalized tree-moment bound I.4.16.
-/

@[expose] public section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP (edgeMeasure)

open PercLib.CriticalLRP.TreeExpansion (LTon)

variable {V : Type*}

/-- **The marked joint-moment bound, alias form.**

`E[|K_x|^p 1(w ∈ K_x)]` is at most the sum, over the fully labelled `(p + 1)`-leaf shapes and
the positions of their internal vertices, of the atlas/BK products at the terminal tuples whose
last label is the marked vertex `w`. -/
theorem jointPow_le_markedAtlasBound [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x w : V) (p : ℕ) :
    I417Gen.jointPow π x p w ≤ markedAtlasBound π x w p := by
  classical
  -- Step 1 + 2: the moment as the sum over the arm labelling of the carrier events.
  have harm : I417Gen.jointPow π x p w =
      ∑' f : Fin p → V, edgeMeasure π (I417A.labelEvent x (markedExtend w f)) := by
    rw [← I417Gen.tsum_labelEvent_inter π x p w]
    exact tsum_congr fun f => by rw [labelEvent_markedExtend]
  rw [harm]
  -- Step 3: the canonical atlas/BK bound for each carrier, at `q = p + 1 ≥ 1`.
  have hbk : ∀ f : Fin p → V,
      edgeMeasure π (I417A.labelEvent x (markedExtend w f)) ≤
        ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' φ : t.1.IPos → V,
            CanonAtlas.Measure.atlasProduct π x (markedExtend w f) t.1 φ :=
    fun f => CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk π hπ (Nat.succ_pos p) x
      (markedExtend w f)
  refine (ENNReal.tsum_le_tsum hbk).trans (le_of_eq ?_)
  -- Step 4: reindex the shape, position and terminal sums.
  rw [markedAtlasBound_eq_tsum_markedExtend π x w p]
  conv_lhs => rw [ENNReal.tsum_comm]
  exact tsum_congr fun _t => ENNReal.tsum_comm

/-- **The marked joint-moment bound, in the literal sum form.**

The right-hand side is the one displayed in the target: the outer sums over the fully labelled
`(p + 1)`-leaf shapes and their internal positions, the inner sum over the `(p + 1)`-labelled
terminal tuples with the last terminal pinned at the physical vertex `w` by the indicator
`if y (Fin.last p) = w then 1 else 0`. -/
theorem jointPow_le_tsum_marked_atlas [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x w : V) (p : ℕ) :
    I417Gen.jointPow π x p w ≤
      ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
        ∑' φ : t.1.IPos → V, ∑' y : Fin (p + 1) → V,
          (if y (Fin.last p) = w then 1 else 0) * CanonAtlas.Measure.atlasProduct π x y t.1 φ :=
  jointPow_le_markedAtlasBound π hπ x w p

/-- **The `p = 0` boundary.**  With no arms the marked moment is the connection probability of
the mark itself, `E[1(w ∈ K_x)] = P(x ↔ w)`.  This is the exact value the general bound is
compared with at `p = 0`: the single marked terminal is the only terminal. -/
theorem jointPow_zero_eq [Countable V] (π : Sym2 V → unitInterval) (x w : V) :
    I417Gen.jointPow π x 0 w = edgeMeasure π (PercLib.CriticalLRP.connSet x w) := by
  classical
  rw [← I417Gen.tsum_labelEvent_inter π x 0 w]
  rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i)]
  · simp [I417A.labelEvent]
  · intro f hf
    exact (hf (Subsingleton.elim f _)).elim

end PercLib.CriticalLRP.I417Marked

/-! ### Axiom audit

The bound and its two transport inputs must rest only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. -/

set_option linter.hashCommand false
namespace PercLib.CriticalLRP.I417Marked

#print axioms jointPow_le_markedAtlasBound
#print axioms jointPow_le_tsum_marked_atlas
#print axioms jointPow_zero_eq
#print axioms tsum_markedExtend
#print axioms markedAtlasBound_eq_tsum_markedExtend
#print axioms labelEvent_markedExtend
#print axioms markedSubtypeEquiv_apply_last

end PercLib.CriticalLRP.I417Marked
