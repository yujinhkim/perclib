/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Non-vacuity certificates for the m2 deliverables

`Tightness/TreePieces.lean`'s hypothesis is unsatisfiable (`NoCycleFree.lean`), so its tree-piece
lemma is vacuous.  These two examples show that the *revised* statements are not:

* `chain_pieces`: `exists_tree_pieces` applied to the parent map of the 6-vertex chain with
  `lam = 2`, `k = 1` produces at least `3^0 + 1 = 2` pieces (6 marked vertices, each piece with 2 or
  3 of them).
* `complete_pieces`: `exists_open_pieces` applied to the complete bond graph on 6 vertices, the open
  configuration `ω = univ`, `Λ = univ`, `lam = 2`, `k = 1` produces at least 2 pieces with open,
  pairwise disjoint witness edge sets.
-/
/- Non-vacuity checks for the rooted-forest tree partition and open BK witnesses. -/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.RealPower

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true
@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation Hutchcroft

attribute [local instance] Classical.propDecidable

/-! ### A chain parent map: `exists_tree_pieces` is not vacuous -/

/-- The parent map of the chain `0 ← 1 ← 2 ← ⋯ ← 5`. -/
def chainPP (n : Fin 6) : Fin 6 := ⟨n.val - 1, by have := n.isLt; omega⟩

lemma chainPP_zero : chainPP 0 = 0 := by
  apply Fin.ext
  show 0 - 1 = 0
  omega

lemma chainPP_step {k : ℕ} (h : k + 1 < 6) : chainPP ⟨k + 1, h⟩ = ⟨k, by omega⟩ := by
  apply Fin.ext
  show k + 1 - 1 = k
  omega

lemma chainPP_reaches (k : ℕ) (h : k < 6) : chainPP^[k] (⟨k, h⟩ : Fin 6) = 0 := by
  induction k with
  | zero => simpa using chainPP_zero
  | succ k ih =>
      rw [Function.iterate_succ_apply, chainPP_step h]
      exact ih (by omega)

lemma chainRooted : IsRootedForest chainPP 0 := by
  refine ⟨chainPP_zero, fun n => ⟨n.val, ?_⟩⟩
  have h := chainPP_reaches n.val n.isLt
  rwa [show (⟨n.val, n.isLt⟩ : Fin 6) = n from rfl] at h

/-- **Non-vacuity of the rooted-forest tree-piece lemma.** -/
theorem chain_pieces :
    ∃ s : Finset (Fin 6 × Finset (Fin 6)), 3 ^ (1 - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece chainPP p.1 p.2) ∧
      (∀ p ∈ s, 2 ≤ ((Finset.univ : Finset (Fin 6)) ∩ p.2).card ∧
        ((Finset.univ : Finset (Fin 6)) ∩ p.2).card ≤ 2 * 2 - 1) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  have h : 3 ^ 1 * 2 ≤ (Finset.univ : Finset (Fin 6)).card := by decide
  exact exists_tree_pieces chainRooted _ (lam := 2) (k := 1) (by norm_num) (by norm_num) h

/-! ### The complete bond graph on 6 vertices: `exists_open_pieces` is not vacuous -/

/-- The complete bond graph on `Fin 6`, with the ordered pair of endpoints as edge type. -/
def Gcomplete : BondGraph (Fin 6) (Fin 6 × Fin 6) := fun p => s(p.1, p.2)

lemma complete_conn (x : Fin 6) : Conn Gcomplete Set.univ (0 : Fin 6) x := by
  by_cases h : x = 0
  · rw [h]; exact conn_refl Gcomplete Set.univ 0
  · exact Relation.ReflTransGen.single
      ⟨(0, x), Set.mem_univ _, by simp [Gcomplete]⟩

lemma card_cl : Fintype.card (Cl Gcomplete Set.univ 0) = 6 := by
  have h : Fintype.card (Cl Gcomplete Set.univ 0) = Fintype.card (Fin 6) :=
    Fintype.card_congr ⟨fun x => x.1, fun x => ⟨x, complete_conn x⟩,
      fun x => Subtype.ext rfl, fun x => rfl⟩
  simpa using h

/-- **Non-vacuity of the percolation instantiation.** -/
theorem complete_pieces :
    ∃ s : Finset (Cl Gcomplete Set.univ 0 × Finset (Cl Gcomplete Set.univ 0)),
      3 ^ (1 - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece (bfsParent Gcomplete Set.univ 0) p.1 p.2) ∧
      (∀ p ∈ s, (pieceWt Gcomplete Set.univ 0 p.1 p.2 : Set (Fin 6 × Fin 6)) ⊆ Set.univ) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q →
        Disjoint (pieceWt Gcomplete Set.univ 0 p.1 p.2)
          (pieceWt Gcomplete Set.univ 0 q.1 q.2)) := by
  have hcard : (markSet Gcomplete Set.univ 0 Finset.univ).card = 6 := by
    have huniv : markSet Gcomplete Set.univ 0 Finset.univ = Finset.univ := by
      ext a; simp
    rw [huniv, Finset.card_univ, card_cl]
  obtain ⟨s, hscard, hpiece, hmark, hsub, hdisj, -⟩ :=
    exists_open_pieces Gcomplete Set.univ 0 Finset.univ (lam := 2) (k := 1)
      (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
  exact ⟨s, hscard, hpiece, hsub, hdisj⟩

/-- The minimally deep-piece spine is also instantiated, with a root piece and disjoint
remaining parent-edge sets. -/
theorem chain_root_spine :
    ∃ s : Finset (Fin 6 × Finset (Fin 6)), ∃ j, ∃ Q,
      2 ≤ s.card ∧ j ∈ s ∧ IsRootedPiece chainPP 0 Q ∧
      2 ≤ ((Finset.univ : Finset (Fin 6)) ∩ Q).card ∧
      (∀ q ∈ s, q ≠ j → Disjoint (Q.erase 0) (q.2.erase q.1)) := by
  obtain ⟨s, j, Q, hcard, hjs, hpiece, hmarks, hdisj, hQpiece, hjsub, hQmark, hQdisj⟩ :=
    exists_root_spine_pieces chainRooted (Finset.univ : Finset (Fin 6))
      (lam := 2) (k := 1) (by norm_num) (by norm_num) (by decide)
  exact ⟨s, j, Q, by norm_num at hcard ⊢; omega, hjs, hQpiece, hQmark, hQdisj⟩

/-- A nonintegral threshold is instantiated directly: no ceiling is applied to its large-count
hypothesis. -/
theorem chain_pieces_real :
    ∃ s : Finset (Fin 6 × Finset (Fin 6)), 2 ≤ s.card ∧
      (∀ p ∈ s, (3 / 2 : ℝ) ≤ ((Finset.univ : Finset (Fin 6)) ∩ p.2).card ∧
        (((Finset.univ : Finset (Fin 6)) ∩ p.2).card : ℝ) < 2 * (3 / 2 : ℝ)) := by
  obtain ⟨s, hcard, hpiece, hmarks, hdisj⟩ :=
    exists_tree_pieces_real chainRooted (Finset.univ : Finset (Fin 6))
      (lam := (3 / 2 : ℝ)) (k := 1) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨s, by norm_num at hcard ⊢; omega, hmarks⟩

end Hutchcroft
