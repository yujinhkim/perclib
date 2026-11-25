/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Finite-volume (2.8)/(2.9) at real thresholds

The real tree-piece extraction yields exactly `lam ≤ |A ∩ P|`; no rounded threshold is used on
its high side. Since each individual event is a statement about a finite integer cardinality,
its lower side is equivalently the corresponding natural-threshold event at `⌈lam⌉₊`. The real
root-spine lemma supplies the distinguished pointed witness for (2.11), and the repository's
finite iterated BK inequality gives the two displayed probability bounds for real `lam ≥ 1` and
natural `k ≥ 1`, with every edge probability strictly below one.

The printed `k = 0` endpoint of Theorem 2.3 is false; no such case is claimed here.
-/
module

public import PercLib.CriticalLRP.Tightness.RealPieces
public import PercLib.CriticalLRP.Tightness.PointedPower
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

section RealEvents

variable (G : BondGraph V E) (Λ : Finset V) (lam : ℝ)

/-- The unpointed cluster-window event at a real threshold. -/
def MaxMeetsReal : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ (t.card : ℝ) ∧ ∃ u : V, ∀ y ∈ t, Conn G ω u y}

/-- The pointed cluster-window event at a real threshold. -/
def MeetsReal (u : V) : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ (t.card : ℝ) ∧ ∀ y ∈ t, Conn G ω u y}

/-- Only the low side of a real-threshold argument is rounded: its finite integer cardinality is
at least `lam` exactly when it is at least `⌈lam⌉₊`. -/
theorem maxMeetsReal_eq_ceil : MaxMeetsReal G Λ lam = MaxMeets G Λ ⌈lam⌉₊ := by
  simp [MaxMeetsReal, MaxMeets, Nat.ceil_le]

/-- Pointed form of the same exact count/ceiling equivalence. -/
theorem meetsReal_eq_ceil (u : V) : MeetsReal G Λ lam u = Meets G Λ u ⌈lam⌉₊ := by
  simp [MeetsReal, Meets, Nat.ceil_le]

theorem maxMeetsReal_upper : IsUpperSet (MaxMeetsReal G Λ lam) := by
  rw [maxMeetsReal_eq_ceil]
  exact maxMeets_upper G Λ _

theorem maxMeetsReal_finiteWitness : FiniteWitness (MaxMeetsReal G Λ lam) := by
  rw [maxMeetsReal_eq_ceil]
  exact maxMeets_finiteWitness G Λ _

theorem meetsReal_upper (u : V) : IsUpperSet (MeetsReal G Λ lam u) := by
  rw [meetsReal_eq_ceil]
  exact meets_upper G Λ u _

theorem meetsReal_finiteWitness (u : V) : FiniteWitness (MeetsReal G Λ lam u) := by
  rw [meetsReal_eq_ceil]
  exact meets_finiteWitness G Λ u _

end RealEvents

section RealBounds

variable (G : BondGraph V E) (Λ : Finset V)

/-- **Real-lambda (2.10).** Only the output event is expressed through its equivalent integer
ceiling; the input keeps its exact real size. -/
theorem maxMeets_real_disjointOccurrence {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k) :
    MaxMeetsReal G Λ (3 ^ k * lam) ⊆ DisjointOccurrenceFin
      (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ ⌈lam⌉₊) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, u, hconn⟩ := hω
  have hmark : 3 ^ k * lam ≤ ((markSet G ω u Λ).card : ℝ) := by
    have hsub : t ⊆ Λ.filter (fun x => Conn G ω u x) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hc := Finset.card_le_card hsub
    have hc' : (t.card : ℝ) ≤ (((Λ.filter (fun x => Conn G ω u x)).card : ℕ) : ℝ) := by
      exact_mod_cast hc
    have hmt : (markSet G ω u Λ).card = (Λ.filter (fun x => Conn G ω u x)).card := by
      rw [markSet, ← Finset.subtype_map (fun x => Conn G ω u x) (s := Λ), Finset.card_map]
    rw [hmt]
    exact htcard.trans hc'
  obtain ⟨s, hscard, hpiece, hmarks, hdisj⟩ :=
    exists_tree_pieces_real (bfsParent_isRootedForest G ω u) (markSet G ω u Λ) hlam hk hmark
  obtain ⟨s', hs', hs'card⟩ := Finset.exists_subset_card_eq hscard
  let e : s' ≃ Fin (3 ^ (k - 1) + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hs'card)
  let W : Fin (3 ^ (k - 1) + 1) → Finset E :=
    fun i => pieceWt G ω u (e.symm i).1.1 (e.symm i).1.2
  have hmem (i : Fin (3 ^ (k - 1) + 1)) : (e.symm i).1 ∈ s := hs' (e.symm i).2
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    exact pieceWt_subset G ω u (hpiece _ (hmem i))
  · intro i
    have hlow : ((markSet G ω u Λ ∩ (e.symm i).1.2).card : ℝ) ≥ lam :=
      (hmarks _ (hmem i)).1
    apply piece_forces_max G ω u (hpiece _ (hmem i)) Λ (lam := ⌈lam⌉₊)
    exact Nat.ceil_le.mpr hlow
  · intro i j hij
    have hpq : (e.symm i).1 ≠ (e.symm j).1 := by
      intro heq
      exact hij (e.symm.injective (Subtype.ext heq))
    exact pieceWt_disjoint G ω u (hdisj _ (hmem i) _ (hmem j) hpq)
      (hpiece _ (hmem i)) (hpiece _ (hmem j))

/-- **Real-lambda (2.11):** one pointed witness and `3^(k-1)` maximum-cluster witnesses. -/
theorem meetsReal_disjointOccurrence (u : V) {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k) :
    MeetsReal G Λ (3 ^ k * lam) u ⊆ DisjointOccurrenceFin
      (Fin.cases (Meets G Λ u ⌈lam⌉₊) (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ ⌈lam⌉₊)) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, hconn⟩ := hω
  have hmark : 3 ^ k * lam ≤ ((markSet G ω u Λ).card : ℝ) := by
    have hsub : t ⊆ Λ.filter (fun x => Conn G ω u x) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hc := Finset.card_le_card hsub
    have hc' : (t.card : ℝ) ≤ (((Λ.filter (fun x => Conn G ω u x)).card : ℕ) : ℝ) := by
      exact_mod_cast hc
    have hmt : (markSet G ω u Λ).card = (Λ.filter (fun x => Conn G ω u x)).card := by
      rw [markSet, ← Finset.subtype_map (fun x => Conn G ω u x) (s := Λ), Finset.card_map]
    rw [hmt]
    exact htcard.trans hc'
  obtain ⟨s, j, Q, hscard, hjs, hpiece, hmarks, hdisj, hQpiece, hjsub, hQmark, hQdisj⟩ :=
    exists_root_spine_pieces_real (bfsParent_isRootedForest G ω u) hlam hk
      (A := markSet G ω u Λ) hmark
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
    · exact pieceWt_subset G ω u hQpiece
    · exact pieceWt_subset G ω u (hpiece _ (hmem i'))
  · intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · apply piece_forces_pointed G ω u hQpiece Λ (lam := ⌈lam⌉₊)
      exact Nat.ceil_le.mpr hQmark
    · apply piece_forces_max G ω u (hpiece _ (hmem i')) Λ (lam := ⌈lam⌉₊)
      exact Nat.ceil_le.mpr (hmarks _ (hmem i')).1
  · intro i₁
    induction i₁ using Fin.cases with
    | zero =>
        intro i₂
        induction i₂ using Fin.cases with
        | zero => intro hcon; exact (hcon rfl).elim
        | succ b =>
            intro _
            exact pieceWt_disjoint G ω u (p := (clRoot G ω u, Q)) (q := (e.symm b).1)
              (hQdisj _ (hmem b) (hne b)) hQpiece (hpiece _ (hmem b))
    | succ a =>
        intro i₂
        induction i₂ using Fin.cases with
        | zero =>
            intro _
            exact pieceWt_disjoint G ω u (p := (e.symm a).1) (q := (clRoot G ω u, Q))
              (hQdisj _ (hmem a) (hne a)).symm (hpiece _ (hmem a)) hQpiece
        | succ b =>
            intro hnei
            have hpq : (e.symm a).1 ≠ (e.symm b).1 := by
              intro heq
              apply hnei
              exact congrArg Fin.succ (e.symm.injective (Subtype.ext heq))
            exact pieceWt_disjoint G ω u (p := (e.symm a).1) (q := (e.symm b).1)
              (hdisj _ (hmem a) _ (hmem b) hpq) (hpiece _ (hmem a)) (hpiece _ (hmem b))

/-- **(2.8), finite graph, real `lam ≥ 1`.** -/
theorem maxMeets_real_pow_bound {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1) + 1) := by
  classical
  let f : Fin (3 ^ (k - 1) + 1) → Set (Set E) := fun _ => MaxMeets G Λ ⌈lam⌉₊
  have hmono : (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (DisjointOccurrenceFin f) :=
    measureReal_mono (maxMeets_real_disjointOccurrence G Λ hlam hk)
  have hbk : (edgeLaw p).real (DisjointOccurrenceFin f) ≤
      ∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i) :=
    bk_fin p hp _ (fun _ => maxMeets_upper G Λ _) (fun _ => maxMeets_finiteWitness G Λ _)
  have hprod : (∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i)) =
      (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1) + 1) := by
    simp [f, Finset.prod_const]
  calc
    (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam))
        ≤ (edgeLaw p).real (DisjointOccurrenceFin f) := hmono
    _ ≤ ∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i) := hbk
    _ = (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1) + 1) := hprod
    _ = (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1) + 1) := by
        rw [maxMeetsReal_eq_ceil]

/-- **(2.9), finite graph, real `lam ≥ 1`.** -/
theorem meetsReal_pow_bound (u : V) {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u) ≤
      (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (MeetsReal G Λ lam u) := by
  classical
  let f : Fin (3 ^ (k - 1) + 1) → Set (Set E) :=
    Fin.cases (Meets G Λ u ⌈lam⌉₊) (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ ⌈lam⌉₊)
  have hmono : (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u) ≤
      (edgeLaw p).real (DisjointOccurrenceFin f) :=
    measureReal_mono (meetsReal_disjointOccurrence G Λ u hlam hk)
  have hbk : (edgeLaw p).real (DisjointOccurrenceFin f) ≤
      ∏ i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f i) := by
    apply bk_fin p hp
    · intro i
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact meets_upper G Λ u _
      · exact maxMeets_upper G Λ _
    · intro i
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact meets_finiteWitness G Λ u _
      · exact maxMeets_finiteWitness G Λ _
  have hprod : (∏ i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f i)) =
      (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) := by
    rw [Fin.prod_univ_succ]
    simp only [f, Fin.cases_zero, Fin.cases_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  calc
    (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u)
        ≤ (edgeLaw p).real (DisjointOccurrenceFin f) := hmono
    _ ≤ ∏ i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f i) := hbk
    _ = (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) := hprod
    _ = (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (MeetsReal G Λ lam u) := by
        rw [maxMeetsReal_eq_ceil, meetsReal_eq_ceil]

/-- (2.8) for the finite long-range model, with real thresholds. -/
theorem model_maxMeets_real_pow_bound {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (edgeLaw (modelP J β hβ hJ)).real (MaxMeetsReal G Λ (3 ^ k * lam)) ≤
      (edgeLaw (modelP J β hβ hJ)).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1) + 1) :=
  maxMeets_real_pow_bound G Λ hlam hk _ (modelP_lt_one J β hβ hJ)

/-- (2.9) for the finite long-range model, with real thresholds. -/
theorem model_meetsReal_pow_bound (u : V) {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (J : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    (edgeLaw (modelP J β hβ hJ)).real (MeetsReal G Λ (3 ^ k * lam) u) ≤
      (edgeLaw (modelP J β hβ hJ)).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw (modelP J β hβ hJ)).real (MeetsReal G Λ lam u) :=
  meetsReal_pow_bound G Λ u hlam hk _ (modelP_lt_one J β hβ hJ)

end RealBounds

end Hutchcroft
