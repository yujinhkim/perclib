/-
Independently assembled by the coordinator against production base
`54054b7051903bd4990d0dc78cdfcb61d0676288` and the newly integrated marked polygon theorem.
The strict candidate was `.scratch/verification/q-one-assembly/Main.lean`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Main
public import PercLib.CriticalLRP.Correlation.I417.Base.QOne

/-! The positive path-length boundary for the marked polygon sum. -/

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

universe u

/-- A leaf of a tree with at least two leaves is at depth at least two. -/
theorem two_le_depth_of_two_le_numLeaves {α : Type u} (t : RTree α) (q : t.LeafPos)
    (ht : 2 ≤ t.numLeaves) : 2 ≤ RTree.depth t q := by
  cases t with
  | leaf a => simp [RTree.numLeaves] at ht
  | node l r =>
      cases q with
      | inl q =>
          change 2 ≤ RTree.depth l q + 1
          have h := depth_pos l q
          omega
      | inr q =>
          change 2 ≤ RTree.depth r q + 1
          have h := depth_pos r q
          omega

/-- A nonempty arm family forces marked depth at least two. -/
theorem markedShapes_two_le_depth {p : ℕ} (hp : 1 ≤ p) :
    ∀ A ∈ markedShapes p, 2 ≤ RTree.depth A.1 A.2 := by
  intro A hA
  apply two_le_depth_of_two_le_numLeaves A.1 A.2
  have hnum := markedShapes_numLeaves p A hA
  omega

/-- At positive `p`, depth one has coefficient zero. -/
theorem markedCount_one_of_pos {p : ℕ} (hp : 1 ≤ p) : markedCount p 1 = 0 := by
  rw [markedCount]
  have hempty : (markedShapes p).filter (fun A => RTree.depth A.1 A.2 = 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro A hA hdepth
    have htwo := markedShapes_two_le_depth hp A hA
    omega
  rw [hempty, Finset.card_empty]

/-- The polygon sum starts at depth two when at least one arm is present. -/
theorem markedPolygonBound_eq_icc_two_of_pos {W : Type u} [DecidableEq W]
    (χ : ℝ≥0∞) (k : W → W → ℝ≥0∞) {p : ℕ} (hp : 1 ≤ p) (x w : W) :
    markedPolygonBound χ k p x w =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (markedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow k ℓ x w) := by
  classical
  rw [markedPolygonBound]
  symm
  refine Finset.sum_subset (s₁ := Finset.Icc 2 (p + 1))
    (s₂ := Finset.Icc 1 (p + 1)) ?_ ?_
  · exact Finset.Icc_subset_Icc (by omega) (by omega)
  · intro ℓ hℓ hℓ'
    simp only [Finset.mem_Icc] at hℓ hℓ'
    have hℓ1 : ℓ = 1 := by omega
    subst ℓ
    rw [markedCount_one_of_pos hp]
    simp

end PercLib.CriticalLRP.I417Marked

namespace PercLib.CriticalLRP.I417MarkedRelabel

open PercLib.CriticalLRP (connSet edgeMeasure)
open PercLib.CriticalLRP.I417Gen

/-- Lemma I.4.17 with `q = 1` and a positive `p`, with the actual marked-depth
coefficients and no residual marked-diagram premise. -/
theorem moment_gap_q_one_le_of_pos {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd π x y p 1 - I417A.rawDiff π x y p 1 ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (I417Marked.markedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 2 - ℓ) *
          I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) (ℓ + 1) x y) := by
  have hfresh : ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) = I417.meanVol π x := by
    intro v
    change I417.meanVol π v = I417.meanVol π x
    exact hχ v
  have hjoint : ∀ w : V, jointPow π x p w ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (I417Marked.markedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 1 - ℓ) *
          I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ x w) := by
    intro w
    rw [← I417Marked.markedPolygonBound_eq_icc_two_of_pos (I417.meanVol π x)
      (fun a b => (edgeMeasure π) (connSet a b)) hp x w]
    exact jointPow_le_markedPolygonBound π hπ (I417.meanVol π x) hfresh x w p
  exact I417Base.q_one_polygon π hπ x y hχ p (I417Marked.markedCount p) hjoint

end PercLib.CriticalLRP.I417MarkedRelabel

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417Marked.markedShapes_two_le_depth
#print axioms PercLib.CriticalLRP.I417Marked.markedCount_one_of_pos
#print axioms PercLib.CriticalLRP.I417Marked.markedPolygonBound_eq_icc_two_of_pos
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.moment_gap_q_one_le_of_pos
