/- Independently rebuilt and integrated UltraMath package `smwwz58hv`, member `m1`.
Production integration revision: `4478d0f5a412be93a92b607d6e30a20cbd89bdb6`.
Per-depth comparison with the `Label p` plane coefficients is not claimed here. -/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Main
public import PercLib.CriticalLRP.Correlation.I417.Base.Depth
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.QOne
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Total
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Exact

/-!
# Marked depth coefficients over child-swap orbits

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17, marked base side.

`Main.lean` proves `jointPow ≤ markedTransversalBound`, the marked joint moment bounded by the
marked atlas sum over one plane representative per child-swap orbit, and shows that the plane
marked sum is exactly `2 ^ p` times it.

This file regroups the **transversal** sum by marked depth and so produces the honest non-plane
version of the source's coefficient `C_{p,ℓ}`:

`markedTransversalBound π x w p
   = ∑_{ℓ=1}^{p+1} #{orbits with marked depth ℓ} · χ^(2p+1-ℓ) · T^ℓ(x,w)`.

Two things are checked, not assumed:

* **Child swaps preserve the marked depth.**  A transversal element is a fully labelled plane
  tree; its marking leaf is the leaf carrying the label `Fin.last p`, and the depth of that leaf
  is `RTree.depth r (markPos (Fin.last p) r)`.  Child swaps change the left/right *address* of
  the marked leaf but not the *length* of its path (the segment that has to be traversed keeps
  its length); so the depth is a function of the child-swap orbit and counting one
  representative per orbit counts non-plane diagrams.  This is used through
  `nonplaneMarkedCount`, whose fibres are literally the filtered transversal.

* **The per-diagram value only depends on the marked depth.**  For a fully labelled shape `r`
  with `p+1` leaves the totalised marked diagram is
  `χ ^ (2p+1-ℓ) · T^ℓ(x,w)` with `ℓ` the marked depth — the production evaluation
  `I417Base.tsum_wtE_marked` followed by `I417Base.pathW_eq_iterPow`.

The coefficient is `1` and not `2` at `p = 1`, `ℓ = 2`: there are two plane `2`-leaf shapes and
one child-swap orbit.  Nothing is obtained by dividing a finite family count by `2 ^ p`; the
count is taken on the transversal itself.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedTransversal

open PercLib.CriticalLRP (edgeMeasure connSet)
open PercLib.CriticalLRP.TreeExpansion (LTon RTree)
open PercLib.CriticalLRP.TreeExpansion.RTree
open PercLib.CriticalLRP.I417Marked (markPos markPos_spec markDepth markedExtend markedAtlasBound)
open PercLib.CriticalLRP.I417MarkedRelabel (pinLast)

variable {V : Type*}

/-! ### Transversal elements are fully labelled -/

/-- Every label occurs as a leaf label of a fully labelled shape. -/
theorem mem_leaves_of_fullyLabelled {q : ℕ} {r : RTree (Fin q)} (hr : r.FullyLabelled)
    (a : Fin q) : a ∈ r.leaves := by
  rw [← List.mem_toFinset]
  have hcard : r.leaves.toFinset.card = Fintype.card (Fin q) := by
    rw [List.toFinset_card_of_nodup hr.1, hr.2]
  rw [Finset.eq_univ_of_card r.leaves.toFinset (by simpa using hcard)]
  exact Finset.mem_univ a

/-- A fully labelled shape on `q` labels has `q` leaves. -/
theorem numLeaves_eq_of_fullyLabelled {q : ℕ} {r : RTree (Fin q)} (hr : r.FullyLabelled) :
    r.numLeaves = q :=
  hr.2.trans (Fintype.card_fin q)

/-- **Every element of the transversal of fully labelled shapes is fully labelled.**  The
transversal is a fundamental domain for the child-swap action on `RTree.LT (Fin q)`, and child
swaps only permute the leaf list (`RTree.perm_of_mem_swapFiber`), so the leaf set is unchanged
and the leaf list is still injective with full cardinality. -/
theorem fullyLabelled_of_mem_transversal {q : ℕ} {r : RTree (Fin q)}
    (hr : r ∈ RTree.transversal (Fin q)) : r.FullyLabelled := by
  classical
  obtain ⟨S, rfl⟩ := RTree.mem_transversal.mp hr
  obtain ⟨t, ht⟩ := RTree.mem_swapOrbits.mp S.2
  have hmem : RTree.orbitRep (Fin q) S ∈ t.val.swapFiber := by
    rw [ht, ← RTree.orbitRep_spec S]
    exact RTree.swapFiber_self _
  have hperm := RTree.perm_of_mem_swapFiber hmem
  exact ⟨hperm.nodup_iff.mpr t.2.1, by rw [hperm.length_eq, t.2.2]⟩

/-! ### Reindexing the leaf labels by leaf positions, for a fully labelled shape -/

/-- **`leafOfPos` is a bijection for any fully labelled shape.** -/
theorem leafOfPos_bijective_of_fullyLabelled {q : ℕ} {r : RTree (Fin q)}
    (hr : r.FullyLabelled) : Function.Bijective r.leafOfPos :=
  ⟨RTree.leafOfPos_injective hr.1,
    fun a => RTree.exists_leafOfPos r a (mem_leaves_of_fullyLabelled hr a)⟩

/-- **Change of variables from label assignments to leaf-position assignments** for a fully
labelled shape: with all labels occurring exactly once, assigning a value to every label is the
same as assigning a value to every leaf position. -/
theorem tsum_label_eq_tsum_leafPos_of_fullyLabelled {q : ℕ} {r : RTree (Fin q)}
    (hr : r.FullyLabelled) {W : Type*} (G : (r.LeafPos → W) → ℝ≥0∞) :
    (∑' y : Fin q → W, G (fun p => y (r.leafOfPos p))) = ∑' ζ : r.LeafPos → W, G ζ := by
  classical
  let e : r.LeafPos ≃ Fin q :=
    Equiv.ofBijective r.leafOfPos (leafOfPos_bijective_of_fullyLabelled hr)
  let φ : (Fin q → W) ≃ (r.LeafPos → W) :=
    { toFun := fun (y : Fin q → W) (p : r.LeafPos) => y (r.leafOfPos p)
      invFun := fun (ζ : r.LeafPos → W) (a : Fin q) => ζ (e.symm a)
      left_inv := fun (y : Fin q → W) => by
        funext a
        exact congrArg y (Equiv.apply_symm_apply e a)
      right_inv := fun (ζ : r.LeafPos → W) => by
        funext p
        exact congrArg ζ (Equiv.symm_apply_apply e p) }
  exact Equiv.tsum_eq φ G

/-- **The pin at a label, summed over the terminal labels, is the pin at the corresponding leaf
position, summed over leaf assignments.**  The diagram value is unchanged because for a fully
labelled shape the position sum of the atlas product is the tree weight of the leaf assignment
(`Real.posSumWtE_eq_wtE`). -/
theorem posSum_pin_eq_leafPos [DecidableEq V] {q : ℕ} (π : Sym2 V → unitInterval) (m : Fin q)
    {r : RTree (Fin q)} (hr : r.FullyLabelled) (x w : V) :
    (∑' y : Fin q → V, (if y m = w then 1 else 0) *
        (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ))
      = ∑' ζ : r.LeafPos → V, (if ζ (markPos m r) = w then 1 else 0) *
          PercLib.CriticalLRP.I417Base.wtE
            (fun a b => edgeMeasure π (connSet a b)) r ζ x := by
  classical
  have hk : ∀ y : Fin q → V,
      (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ)
        = PercLib.CriticalLRP.I417Base.wtE (fun a b => edgeMeasure π (connSet a b)) r
            (fun p => y (r.leafOfPos p)) x := by
    intro y
    rw [CanonAtlas.Measure.tsum_atlasProduct_eq_posSumWtE]
    exact PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_eq_wtE _ r y x
  have hpos : r.leafOfPos (markPos m r) = m := markPos_spec (mem_leaves_of_fullyLabelled hr m)
  have hstep : ∀ y : Fin q → V,
      (if y m = w then 1 else 0) *
          (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ)
        = (if y (r.leafOfPos (markPos m r)) = w then 1 else 0) *
            PercLib.CriticalLRP.I417Base.wtE
              (fun a b => edgeMeasure π (connSet a b)) r (fun p => y (r.leafOfPos p)) x := by
    intro y
    rw [hpos, hk y]
  refine Eq.trans (tsum_congr hstep) ?_
  exact tsum_label_eq_tsum_leafPos_of_fullyLabelled hr
    (fun ζ : r.LeafPos → V => (if ζ (markPos m r) = w then 1 else 0) *
      PercLib.CriticalLRP.I417Base.wtE
        (fun a b => edgeMeasure π (connSet a b)) r ζ x)

/-! ### The per-diagram value depends only on the marked depth -/

/-- **Every transversal marked diagram is worth `χ ^ (2p+1-ℓ) · T^ℓ(x,w)`**, `ℓ` the depth
of the marking leaf.  This is the production evaluation of a single marked diagram
(`I417Base.tsum_wtE_marked`, `I417Base.pathW_eq_iterPow`), with the leaf count `p+1` supplied by
full labelling rather than by an `LTon` bundling. -/
theorem transversal_term_eq [DecidableEq V] (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) = χ) (x w : V) (p : ℕ)
    {r : RTree (Fin (p + 1))} (hr : r ∈ RTree.transversal (Fin (p + 1))) :
    (∑' y : Fin (p + 1) → V, pinLast w y *
        (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ))
      = χ ^ (2 * p + 1 - RTree.depth r (markPos (Fin.last p) r)) *
          PercLib.CriticalLRP.I417Base.iterPow (fun a b => edgeMeasure π (connSet a b))
            (RTree.depth r (markPos (Fin.last p) r)) x w := by
  classical
  have hfl : r.FullyLabelled := fullyLabelled_of_mem_transversal hr
  have h1 : (∑' y : Fin (p + 1) → V, pinLast w y *
        (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ))
      = ∑' y : Fin (p + 1) → V, (if y (Fin.last p) = w then 1 else 0) *
        (∑' φ : r.IPos → V, CanonAtlas.Measure.atlasProduct π x y r φ) :=
    tsum_congr fun y => by rw [pinLast_eq_ite]
  rw [h1, posSum_pin_eq_leafPos π (Fin.last p) hfl x w]
  rw [PercLib.CriticalLRP.I417Base.tsum_wtE_marked _ χ hχ r (markPos (Fin.last p) r) x w]
  rw [PercLib.CriticalLRP.I417Base.pathW_eq_iterPow]
  rw [numLeaves_eq_of_fullyLabelled hfl]
  have hexp : 2 * (p + 1) - 1 - r.depth (markPos (Fin.last p) r)
      = 2 * p + 1 - r.depth (markPos (Fin.last p) r) := by omega
  rw [hexp]

/-! ### Regrouping the transversal sum by marked depth -/

/-- **The marked transversal bound, regrouped by marked depth over child-swap orbits.**

For a kernel with constant row sum `χ` the marked atlas sum over the transversal is the finite
expression `∑_{ℓ=1}^{p+1} (non-plane count at depth ℓ) · χ^(2p+1-ℓ) · T^ℓ(x,w)`, where
the
coefficient `nonplaneMarkedCount p ℓ` counts child-swap orbits of fully labelled `(p+1)`-leaf
shapes with marking-leaf depth `ℓ`. -/
theorem markedTransversalBound_eq_sum_depth [DecidableEq V] (π : Sym2 V → unitInterval)
    (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) = χ) (x w : V) (p : ℕ) :
    markedTransversalBound π x w p =
      ∑ ℓ ∈ Finset.Icc 1 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) *
          PercLib.CriticalLRP.I417Base.iterPow
            (fun a b => edgeMeasure π (connSet a b)) ℓ x w) := by
  classical
  have hhi : ∀ r ∈ RTree.transversal (Fin (p + 1)),
      RTree.depth r (markPos (Fin.last p) r) ≤ p + 1 := by
    intro r hr
    have hfl : r.FullyLabelled := fullyLabelled_of_mem_transversal hr
    have h := PercLib.CriticalLRP.I417Marked.markDepth_le_numLeaves (Fin.last p) r
    rwa [numLeaves_eq_of_fullyLabelled hfl] at h
  have hm : ∀ r ∈ RTree.transversal (Fin (p + 1)),
      RTree.depth r (markPos (Fin.last p) r) < p + 2 :=
    fun r hr => by have := hhi r hr; omega
  rw [markedTransversalBound_eq_sum_pos]
  rw [Finset.sum_congr rfl fun r hr => transversal_term_eq π χ hχ x w p hr]
  rw [PercLib.CriticalLRP.I417Base.finset_sum_by_fiber (RTree.transversal (Fin (p + 1)))
    (fun ℓ => χ ^ (2 * p + 1 - ℓ) *
      PercLib.CriticalLRP.I417Base.iterPow (fun a b => edgeMeasure π (connSet a b)) ℓ x w)
    (fun r => RTree.depth r (markPos (Fin.last p) r)) (p + 2) hm]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    exact Finset.mem_range.mpr (by omega)
  · intro ℓ hℓmem hℓ
    have hmem : ℓ < p + 2 := by simpa using hℓmem
    have hdisj : ℓ < 1 ∨ p + 1 < ℓ := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hℓ
    have h0 : ℓ = 0 := by
      rcases hdisj with h | h
      · omega
      · omega
    have hemp : (RTree.transversal (Fin (p + 1))).filter
        (fun r => RTree.depth r (markPos (Fin.last p) r) = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r _ hd
      rw [h0] at hd
      have hpos1 : 1 ≤ RTree.depth r (markPos (Fin.last p) r) :=
        PercLib.CriticalLRP.I417Marked.depth_pos r _
      omega
    rw [hemp]
    simp

/-- At positive `p` there is no transversal marked diagram of depth one: with `p+1 ≥ 2` leaves
every leaf has depth at least two. -/
theorem nonplaneMarkedCount_one_eq_zero {p : ℕ} (hp : 1 ≤ p) : nonplaneMarkedCount p 1 = 0 := by
  classical
  rw [nonplaneMarkedCount]
  have hemp : (RTree.transversal (Fin (p + 1))).filter
      (fun r => RTree.depth r (markPos (Fin.last p) r) = 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro r hr hd
    have hfl : r.FullyLabelled := fullyLabelled_of_mem_transversal hr
    have htwo : 2 ≤ RTree.depth r (markPos (Fin.last p) r) :=
      PercLib.CriticalLRP.I417Marked.two_le_depth_of_two_le_numLeaves r
        (markPos (Fin.last p) r) (by rw [numLeaves_eq_of_fullyLabelled hfl]; omega)
    omega
  rw [hemp, Finset.card_empty]

/-- **The marked joint moment with non-plane marked depth coefficients.**

`E[|K_x|^p 1(w ∈ K_x)] ≤ ∑_{ℓ=2}^{p+1} C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)` where `C_ℓ` is the
number of
child-swap orbits of fully labelled `(p+1)`-leaf shapes whose marked leaf has depth `ℓ`.  This is
the source's marked diagram bound with the honest non-plane coefficient: it is *not* obtained by
dividing a finite plane count, and no diagram is deleted. -/
theorem jointPow_le_nonplane_markedDepth [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) = χ) (x : V) {p : ℕ}
    (hp : 1 ≤ p) (w : V) :
    PercLib.CriticalLRP.I417Gen.jointPow π x p w ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) *
          PercLib.CriticalLRP.I417Base.iterPow
            (fun a b => edgeMeasure π (connSet a b)) ℓ x w) := by
  classical
  refine (jointPow_le_markedTransversalBound π hπ x w p).trans ?_
  rw [markedTransversalBound_eq_sum_depth π χ hχ x w p]
  refine le_of_eq (Finset.sum_subset (s₁ := Finset.Icc 2 (p + 1))
    (s₂ := Finset.Icc 1 (p + 1)) ?_ ?_).symm
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at *
    omega
  · intro ℓ hℓ hℓ'
    have hone : 1 ≤ ℓ ∧ ℓ ≤ p + 1 := by simpa only [Finset.mem_Icc] using hℓ
    have hdisj : ℓ < 2 ∨ p + 1 < ℓ := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hℓ'
    have h1 : ℓ = 1 := by
      rcases hdisj with h | h <;> omega
    subst h1
    rw [nonplaneMarkedCount_one_eq_zero hp, Nat.cast_zero, zero_mul]

/-- **Lemma I.4.17 at `q = 1` with non-plane marked depth coefficients.

The moment gap `E|K_x|^p E|K_x| - E[|K_x|^p |K_y| 1(x ↮ y)]` is bounded by
`∑_{ℓ=2}^{p+1} C_ℓ χ^(2p+2-ℓ) T^(ℓ+1)(x,y)`, where `C_ℓ` counts child-swap orbits of
fully
labelled `(p+1)`-leaf marked shapes with marked depth `ℓ`: one representative per non-plane
diagram, not `2^p` of them. -/
theorem moment_gap_q_one_le_nonplane [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) {p : ℕ} (hp : 1 ≤ p) :
    PercLib.CriticalLRP.I417A.momentProd π x y p 1 -
      PercLib.CriticalLRP.I417A.rawDiff π x y p 1 ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 2 - ℓ) *
          PercLib.CriticalLRP.I417Base.iterPow (fun a b => edgeMeasure π (connSet a b))
            (ℓ + 1) x y) := by
  have hfresh : ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) = I417.meanVol π x := by
    intro v
    change I417.meanVol π v = I417.meanVol π x
    exact hχ v
  have hjoint : ∀ w : V, PercLib.CriticalLRP.I417Gen.jointPow π x p w ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 1 - ℓ) *
          PercLib.CriticalLRP.I417Base.iterPow (fun a b => edgeMeasure π (connSet a b)) ℓ x w) :=
    fun w => jointPow_le_nonplane_markedDepth π hπ (I417.meanVol π x) hfresh x hp w
  exact PercLib.CriticalLRP.I417Base.q_one_polygon π hπ x y hχ p (nonplaneMarkedCount p) hjoint


/-! ### Count normalisation: the non-plane coefficients count child-swap orbits

The coefficient `nonplaneMarkedCount p ℓ` is a cardinality of a filtered transversal, so it is
not obtained by dividing a plane count.  The two totals agree after multiplication by the orbit
size `2 ^ p`, which is the count-normalisation check: the non-plane coefficients are exactly the
plane ones with one representative per orbit, and the sources' total `2 ^ p * (2p-1)!!` is not
changed.
-/

/-- **The non-plane marked depth coefficients total the number of child-swap orbits.** -/
theorem sum_nonplaneMarkedCount_eq_card_transversal (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), nonplaneMarkedCount p ℓ)
      = (RTree.transversal (Fin (p + 1))).card := by
  classical
  have hfr : ∀ r ∈ RTree.transversal (Fin (p + 1)),
      RTree.depth r (markPos (Fin.last p) r) ∈ Finset.Icc 1 (p + 1) := by
    intro r hr
    have hfl : r.FullyLabelled := fullyLabelled_of_mem_transversal hr
    have hle : RTree.depth r (markPos (Fin.last p) r) ≤ p + 1 := by
      have h := PercLib.CriticalLRP.I417Marked.markDepth_le_numLeaves (Fin.last p) r
      rw [numLeaves_eq_of_fullyLabelled hfl] at h
      rwa [PercLib.CriticalLRP.I417Marked.markDepth] at h
    exact Finset.mem_Icc.mpr ⟨PercLib.CriticalLRP.I417Marked.depth_pos r _, hle⟩
  have h := Finset.card_eq_sum_card_fiberwise
    (s := RTree.transversal (Fin (p + 1)))
    (t := Finset.Icc 1 (p + 1))
    (f := fun r => RTree.depth r (markPos (Fin.last p) r)) hfr
  simpa only [nonplaneMarkedCount] using h.symm

/-- **The exact total of the non-plane marked depth coefficients**: the number of non-plane
binary trees with `p+1` distinct labels, i.e. `(2p-1)!!` (`VolumeMoments.M p`). -/
theorem sum_nonplaneMarkedCount (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), nonplaneMarkedCount p ℓ) = VolumeMoments.M p := by
  rw [sum_nonplaneMarkedCount_eq_card_transversal, RTree.transversal_card,
    card_swapOrbits_fin_eq_dfactorial (p + 1) (Nat.succ_le_succ (Nat.zero_le p))]
  congr 1

/-- **Count normalisation.**  The plane marked coefficients of
`I417Marked.markedCount` total exactly `2 ^ p` times the non-plane ones: the discarded factor is
the child-swap orbit size `2 ^ p`, and nothing else. -/
theorem sum_markedCount_eq_two_pow_mul_sum_nonplaneMarkedCount (p : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 (p + 1), PercLib.CriticalLRP.I417Marked.markedCount p ℓ)
      = 2 ^ p * ∑ ℓ ∈ Finset.Icc 1 (p + 1), nonplaneMarkedCount p ℓ := by
  rw [sum_nonplaneMarkedCount,
    PercLib.CriticalLRP.I417Marked.sum_markedCount_eq_plane_count]

/-- The total of the non-plane coefficients at `p = 1` is one: there is exactly one non-plane
marked diagram. -/
theorem sum_nonplaneMarkedCount_one : (∑ ℓ ∈ Finset.Icc 1 2, nonplaneMarkedCount 1 ℓ) = 1 := by
  rw [sum_nonplaneMarkedCount]
  have h := VolumeMoments.M_eq_doubleFactorial 0
  simp only [Nat.zero_add, Nat.reduceMul] at h
  exact h

/-- **The `p = 1` coefficient at path length `2` is `1`**, the honest non-plane count.  The
plane family has two `2`-leaf shapes (`node (leaf 0) (leaf 1)` and its swap) and one
child-swap orbit. -/
theorem nonplaneMarkedCount_one_two : nonplaneMarkedCount 1 2 = 1 := by
  have h := sum_nonplaneMarkedCount_one
  have hsplit : (∑ ℓ ∈ Finset.Icc 1 (1 + 1), nonplaneMarkedCount 1 ℓ)
      = nonplaneMarkedCount 1 1 + nonplaneMarkedCount 1 2 := by
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    simp
  rw [hsplit, nonplaneMarkedCount_one_eq_zero (le_refl 1), Nat.zero_add] at h
  exact h

/-- **The `p = 1` plane coefficient at path length `2` is `2`**, so the non-plane coefficient
above is exactly the plane one divided by `2 ^ 1 = 2` — computed from the orbit count, not
imposed. -/
theorem markedCount_one_two : PercLib.CriticalLRP.I417Marked.markedCount 1 2 = 2 := by
  have h := PercLib.CriticalLRP.I417Marked.sum_markedCount_eq_plane_count 1
  have hsplit : (∑ ℓ ∈ Finset.Icc 1 (1 + 1), PercLib.CriticalLRP.I417Marked.markedCount 1 ℓ)
      = PercLib.CriticalLRP.I417Marked.markedCount 1 1 +
        PercLib.CriticalLRP.I417Marked.markedCount 1 2 := by
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    simp
  rw [hsplit, PercLib.CriticalLRP.I417Marked.markedCount_one_of_pos (le_refl 1),
    Nat.zero_add] at h
  have hM : VolumeMoments.M 1 = 1 := by
    have h2 := VolumeMoments.M_eq_doubleFactorial 0
    simp only [Nat.zero_add, Nat.reduceMul] at h2
    exact h2
  rw [hM] at h
  simpa using h

end PercLib.CriticalLRP.I417MarkedTransversal

/-! ### Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.I417MarkedTransversal

#print axioms fullyLabelled_of_mem_transversal
#print axioms tsum_label_eq_tsum_leafPos_of_fullyLabelled
#print axioms posSum_pin_eq_leafPos
#print axioms transversal_term_eq
#print axioms markedTransversalBound_eq_sum_depth
#print axioms nonplaneMarkedCount_one_eq_zero
#print axioms jointPow_le_nonplane_markedDepth
#print axioms moment_gap_q_one_le_nonplane
#print axioms sum_nonplaneMarkedCount_eq_card_transversal
#print axioms sum_nonplaneMarkedCount
#print axioms sum_markedCount_eq_two_pow_mul_sum_nonplaneMarkedCount
#print axioms nonplaneMarkedCount_one_two
#print axioms markedCount_one_two

end PercLib.CriticalLRP.I417MarkedTransversal
