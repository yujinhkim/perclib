/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Pointed cluster-window pieces and finite-volume (2.11)/(2.9)

For a finite bond graph, `Meets G Λ u lam` is the event that the open cluster of `u` meets the
window `Λ` in at least `lam` vertices. The root-spine theorem upgrades the existing integer
maximal-cluster piece decomposition by adjoining the ancestor chain of a minimally deep piece.
The resulting distinguished parent-edge set forces the pointed event on its own, while the other
piece edge sets force `MaxMeets` and are pairwise disjoint. Applying the repository's `bk_fin`
yields

  `P(|K_u ∩ Λ| ≥ 3^k lam) ≤ P(|K_max(Λ)| ≥ lam)^(3^(k-1)) * P(|K_u ∩ Λ| ≥ lam)`

for integer `lam ≥ 2` and `k ≥ 1`, with all edge probabilities strictly below one. The scope is
finite volume and integer thresholds; no all-edge partition, real-lambda result, or infinite-volume
claim is made.
-/
module

public import PercLib.CriticalLRP.Tightness.RootSpine
public import PercLib.CriticalLRP.Tightness.MaxClusterPower
public import PercLib.CriticalLRP.Tightness.LongRangePower

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
  [Nonempty E]

section PointedEvent

variable (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ)

/-- The pointed cluster-window event `|K_u ∩ Λ| ≥ lam`. -/
def Meets : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y}

@[simp] theorem mem_Meets {ω : Set E} :
    ω ∈ Meets G Λ u lam ↔ ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y := Iff.rfl

/-- The pointed event increases with the open configuration. -/
theorem meets_upper : IsUpperSet (Meets G Λ u lam) := by
  rintro ω ω' hωω' ⟨t, htΛ, hcard, hconn⟩
  exact ⟨t, htΛ, hcard, fun y hy => conn_mono G hωω' (hconn y hy)⟩

/-- A pointed cluster-window event has a finite open-edge witness whenever it occurs. -/
theorem meets_finiteWitness : FiniteWitness (Meets G Λ u lam) := by
  classical
  rintro ω ⟨t, htΛ, hcard, hconn⟩
  set F : V → Finset E := fun y =>
    if h : y ∈ t then (conn_exists_finset G (hconn y h)).choose else ∅ with hF
  have hFsub : ∀ y ∈ t, (F y : Set E) ⊆ ω := by
    intro y hy
    have := (conn_exists_finset G (hconn y hy)).choose_spec.1
    simpa [hF, dite_eq_left hy] using this
  have hFconn : ∀ y ∈ t, Conn G (F y : Set E) u y := by
    intro y hy
    have := (conn_exists_finset G (hconn y hy)).choose_spec.2
    simpa [hF, dite_eq_left hy] using this
  refine ⟨t.biUnion F, ?_, t, htΛ, hcard, ?_⟩
  · intro e he
    obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact hFsub y hy hey
  · intro y hy
    exact conn_mono G (fun e he => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hy, he⟩))
      (hFconn y hy)

end PointedEvent

section PieceForces

variable (G : BondGraph V E) (ω : Set E) (u : V)

/-- A rooted BFS piece supplies marked vertices connected to its root using only its witness
edges, not merely using all edges of the ambient configuration. -/
theorem piece_window_witness {v : Cl G ω u} {P : Finset (Cl G ω u)}
    (hpiece : IsRootedPiece (bfsParent G ω u) v P) (Λ : Finset V) {lam : ℕ}
    (hmark : lam ≤ (markSet G ω u Λ ∩ P).card) :
    ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t,
      Conn G (pieceWt G ω u v P : Set E) (v : V) y := by
  classical
  refine ⟨(markSet G ω u Λ ∩ P).image (Subtype.val : Cl G ω u → V), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_markSet G ω u).mp (Finset.mem_inter.mp ha).1
  · rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)]
    exact hmark
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact piece_conn_pieceWt G ω u hpiece hpiece.1 (Finset.mem_inter.mp ha).2

/-- A rooted piece's parent-edge set forces the corresponding pointed cluster-window event. -/
theorem piece_forces_pointed {v : Cl G ω u} {P : Finset (Cl G ω u)}
    (hpiece : IsRootedPiece (bfsParent G ω u) v P) (Λ : Finset V) {lam : ℕ}
    (hmark : lam ≤ (markSet G ω u Λ ∩ P).card) :
    (pieceWt G ω u v P : Set E) ∈ Meets G Λ (v : V) lam := by
  obtain ⟨t, htΛ, hcard, hconn⟩ := piece_window_witness G ω u hpiece Λ hmark
  exact ⟨t, htΛ, hcard, hconn⟩

/-- The same parent-edge set forces the unpointed maximal-cluster event. -/
theorem piece_forces_max {v : Cl G ω u} {P : Finset (Cl G ω u)}
    (hpiece : IsRootedPiece (bfsParent G ω u) v P) (Λ : Finset V) {lam : ℕ}
    (hmark : lam ≤ (markSet G ω u Λ ∩ P).card) :
    (pieceWt G ω u v P : Set E) ∈ MaxMeets G Λ lam := by
  obtain ⟨t, htΛ, hcard, hconn⟩ := piece_window_witness G ω u hpiece Λ hmark
  exact ⟨t, htΛ, hcard, (v : V), hconn⟩

end PieceForces

section Bound

variable (G : BondGraph V E) (Λ : Finset V)

/-- **Step (2.11), finite integer case.** A large pointed cluster-window event disjointly occurs
as the same event at the lower threshold once and the maximal-cluster event `3^(k-1)` times. -/
theorem meets_pointed_disjointOccurrence (u : V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k) :
    Meets G Λ u (3 ^ k * lam) ⊆ DisjointOccurrenceFin
      (Fin.cases (Meets G Λ u lam) (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam)) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, hconn⟩ := mem_Meets G Λ u (3 ^ k * lam) |>.mp hω
  have hmark : 3 ^ k * lam ≤ (markSet G ω u Λ).card := by
    have hsub : t ⊆ Λ.filter (fun x => Conn G ω u x) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hcard := Finset.card_le_card hsub
    have hmt : (markSet G ω u Λ).card = (Λ.filter (fun x => Conn G ω u x)).card := by
      rw [markSet, ← Finset.subtype_map (fun x => Conn G ω u x) (s := Λ), Finset.card_map]
    omega
  obtain ⟨s, j, Q, hscard, hjs, hpiece, hmarks, hdisj, hQpiece, hjsub, hQmark, hQdisj⟩ :=
    exists_root_spine_pieces (bfsParent_isRootedForest G ω u) (markSet G ω u Λ) hlam hk hmark
  have hrem : 3 ^ (k - 1) ≤ (s.erase j).card := by
    rw [Finset.card_erase_of_mem hjs]
    omega
  obtain ⟨s', hs', hs'card⟩ := Finset.exists_subset_card_eq hrem
  let e : s' ≃ Fin (3 ^ (k - 1)) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact hs'card)
  let W0 : Finset E := pieceWt G ω u (clRoot G ω u) Q
  let Ws : Fin (3 ^ (k - 1)) → Finset E :=
    fun i => pieceWt G ω u (e.symm i).1.1 (e.symm i).1.2
  let W : Fin (3 ^ (k - 1) + 1) → Finset E := Fin.cases W0 Ws
  have hmem (i : Fin (3 ^ (k - 1))) : (e.symm i).1 ∈ s :=
    Finset.mem_of_mem_erase (hs' (e.symm i).2)
  have hne (i : Fin (3 ^ (k - 1))) : (e.symm i).1 ≠ j :=
    Finset.ne_of_mem_erase (hs' (e.symm i).2)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · change (W0 : Set E) ⊆ ω
      exact pieceWt_subset G ω u hQpiece
    · change (Ws i' : Set E) ⊆ ω
      exact pieceWt_subset G ω u (hpiece _ (hmem i'))
  · intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · change (W0 : Set E) ∈ Meets G Λ u lam
      exact piece_forces_pointed G ω u hQpiece Λ hQmark
    · change (Ws i' : Set E) ∈ MaxMeets G Λ lam
      exact piece_forces_max G ω u (hpiece _ (hmem i')) Λ (hmarks _ (hmem i')).1
  · intro i₁
    induction i₁ using Fin.cases with
    | zero =>
        intro i₂
        induction i₂ using Fin.cases with
        | zero => intro hcon; exact (hcon rfl).elim
        | succ b =>
            intro _
            change Disjoint W0 (Ws b)
            exact pieceWt_disjoint G ω u (p := (clRoot G ω u, Q)) (q := (e.symm b).1)
              (hQdisj _ (hmem b) (hne b)) hQpiece (hpiece _ (hmem b))
    | succ a =>
        intro i₂
        induction i₂ using Fin.cases with
        | zero =>
            intro _
            change Disjoint (Ws a) W0
            exact pieceWt_disjoint G ω u (p := (e.symm a).1) (q := (clRoot G ω u, Q))
              (hQdisj _ (hmem a) (hne a)).symm (hpiece _ (hmem a)) hQpiece
        | succ b =>
            intro hnei
            change Disjoint (Ws a) (Ws b)
            have hpq : (e.symm a).1 ≠ (e.symm b).1 := by
              intro heq
              apply hnei
              exact congrArg Fin.succ (e.symm.injective (Subtype.ext heq))
            exact pieceWt_disjoint G ω u (p := (e.symm a).1) (q := (e.symm b).1)
              (hdisj _ (hmem a) _ (hmem b) hpq) (hpiece _ (hmem a)) (hpiece _ (hmem b))

/-- **Finite-volume (2.9), integer thresholds.** -/
theorem meets_pointed_pow_bound (u : V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (Meets G Λ u (3 ^ k * lam)) ≤
      (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (Meets G Λ u lam) := by
  classical
  set m : ℕ := 3 ^ (k - 1) with hm
  let f : Fin (m + 1) → Set (Set E) :=
    Fin.cases (Meets G Λ u lam) (fun _ : Fin m => MaxMeets G Λ lam)
  have hmono : (edgeLaw p).real (Meets G Λ u (3 ^ k * lam)) ≤
      (edgeLaw p).real (DisjointOccurrenceFin f) :=
    measureReal_mono (meets_pointed_disjointOccurrence G Λ u hlam hk)
  have hbk : (edgeLaw p).real (DisjointOccurrenceFin f) ≤
      ∏ i : Fin (m + 1), (edgeLaw p).real (f i) := by
    apply bk_fin p hp
    · intro i
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact meets_upper G Λ u lam
      · exact maxMeets_upper G Λ lam
    · intro i
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact meets_finiteWitness G Λ u lam
      · exact maxMeets_finiteWitness G Λ lam
  have hprod : (∏ i : Fin (m + 1), (edgeLaw p).real (f i)) =
      (edgeLaw p).real (MaxMeets G Λ lam) ^ m * (edgeLaw p).real (Meets G Λ u lam) := by
    rw [Fin.prod_univ_succ]
    simp only [f, Fin.cases_zero, Fin.cases_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  exact hmono.trans (hbk.trans_eq (hprod.trans (by rw [hm])))

/-- The finite long-range model's own edge probabilities meet the strict BK premise. -/
theorem model_meets_pointed_pow_bound (u : V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (edgeLaw (modelP J β hβ hJ)).real (Meets G Λ u (3 ^ k * lam)) ≤
      (edgeLaw (modelP J β hβ hJ)).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw (modelP J β hβ hJ)).real (Meets G Λ u lam) :=
  meets_pointed_pow_bound G Λ u hlam hk _ (modelP_lt_one J β hβ hJ)

end Bound

end Hutchcroft
