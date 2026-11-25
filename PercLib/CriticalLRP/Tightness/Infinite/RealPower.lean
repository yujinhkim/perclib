/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Arbitrary-vertex (2.8)/(2.9) at real thresholds, with a countable edge type

The finite ancestor closure of a marked window is a finite rooted forest, so the real tree-piece
partition applies without assuming finiteness or countability of the vertex type. The same
minimally deep piece and ancestor spine supplies the distinguished pointed witness in (2.11).
Applying `bk_fin` and `bkEdge`, both available on a countable edge type, yields the two probability
bounds at real `lam ≥ 1` and natural `k ≥ 1`, for every `p e < 1`.
-/
module

public import PercLib.CriticalLRP.Tightness.RealPower
public import PercLib.CriticalLRP.Tightness.Infinite.Power

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft
namespace Countable

open PercLib.CriticalLRP.Percolation Hutchcroft MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] {E : Type*} [DecidableEq E] [Nonempty E]

/-! ## Real threshold/event conversions, independent of the ambient finiteness -/

section RealEvents

variable (G : BondGraph V E) (Λ : Finset V) (lam : ℝ)

theorem maxMeetsReal_eq_ceil_anyV : MaxMeetsReal G Λ lam = MaxMeets G Λ ⌈lam⌉₊ := by
  simp [MaxMeetsReal, MaxMeets, Nat.ceil_le]

theorem meetsReal_eq_ceil_anyV (u : V) : MeetsReal G Λ lam u = Meets G Λ u ⌈lam⌉₊ := by
  simp [MeetsReal, Meets, Nat.ceil_le]

theorem meets_upper_anyV (u : V) : IsUpperSet (Meets G Λ u ⌈lam⌉₊) := by
  rintro ω ω' hωω' ⟨t, htΛ, hcard, hconn⟩
  exact ⟨t, htΛ, hcard, fun y hy => conn_mono G hωω' (hconn y hy)⟩

variable [Countable E]

theorem meets_finiteWitness_anyV (u : V) : FiniteWitness (Meets G Λ u ⌈lam⌉₊) := by
  classical
  rintro ω ⟨t, htΛ, hcard, hconn⟩
  set F : V → Finset E := fun y =>
    if h : y ∈ t then (conn_exists_finset_anyV G (hconn y h)).choose else ∅ with hF
  have hFsub : ∀ y ∈ t, (F y : Set E) ⊆ ω := by
    intro y hy
    have := (conn_exists_finset_anyV G (hconn y hy)).choose_spec.1
    simpa [hF, dite_eq_left hy] using this
  have hFconn : ∀ y ∈ t, Conn G (F y : Set E) u y := by
    intro y hy
    have := (conn_exists_finset_anyV G (hconn y hy)).choose_spec.2
    simpa [hF, dite_eq_left hy] using this
  refine ⟨t.biUnion F, ?_, t, htΛ, hcard, ?_⟩
  · intro e he
    obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact hFsub y hy hey
  · intro y hy
    exact conn_mono G (fun e he => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hy, he⟩))
      (hFconn y hy)

end RealEvents

/-! ## The real tree partition of the finite ancestor closure -/

section RealPieces

variable (G : BondGraph V E) (ω : Set E) (r : V) {A : Finset V}

/-- The real analogue of `exists_trunc_pieces`. -/
theorem exists_trunc_pieces_real (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k) (hA : 3 ^ k * lam ≤ (A.card : ℝ)) :
    ∃ s : Finset (TS G ω r A × Finset (TS G ω r A)),
      3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece (parS G ω r hAc) p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ ((markSetS G ω r A ∩ p.2).card : ℝ) ∧
        ((markSetS G ω r A ∩ p.2).card : ℝ) < 2 * lam) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  classical
  have hcard : 3 ^ k * lam ≤ ((markSetS G ω r A).card : ℝ) := by
    rw [card_markSetS G ω r (subset_truncSet G ω r A)]
    exact hA
  exact exists_tree_pieces_real (parS_isRootedForest G ω r hAc hne)
    (markSetS G ω r A) hlam hk hcard

end RealPieces

/-! ## The two disjoint-occurrence inclusions at real thresholds -/

section Inclusions

variable (G : BondGraph V E)

/-- **(2.10), arbitrary vertex type, real threshold. -/
theorem maxMeetsReal_disjointOccurrence_anyV {lam : ℝ} {k : ℕ}
    (hlam : 1 ≤ lam) (hk : 1 ≤ k) (Λ : Finset V) :
    MaxMeetsReal G Λ (3 ^ k * lam) ⊆ DisjointOccurrenceFin
      (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ ⌈lam⌉₊) := by
  classical
  have hlNat : 1 ≤ ⌈lam⌉₊ := Nat.ceil_pos.mpr (zero_lt_one.trans_le hlam)
  intro ω hω
  obtain ⟨t, htΛ, htcard, u, hconn⟩ := hω
  set A : Finset V := Λ.filter (fun x => Conn G ω u x) with hAdef
  have hAΛ : A ⊆ Λ := Finset.filter_subset _ _
  have hAc : ∀ x ∈ A, Conn G ω u x := fun x hx => (Finset.mem_filter.mp hx).2
  have hAcard : 3 ^ k * lam ≤ (A.card : ℝ) := by
    have hsub : t ⊆ A := fun y hy => Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hc := Finset.card_le_card hsub
    have hc' : (t.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hc
    exact htcard.trans hc'
  have hne : A.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < 3 ^ k * lam := by positivity
    have hc : (0 : ℝ) < (A.card : ℝ) := hpos.trans_le hAcard
    exact_mod_cast hc
  obtain ⟨s, hscard, hp, hmark, hdisj⟩ :=
    exists_trunc_pieces_real G ω u hAc hne hlam hk hAcard
  obtain ⟨s', hs'sub, hs'card⟩ : ∃ s' ⊆ s, s'.card = 3 ^ (k - 1) + 1 :=
    Finset.exists_subset_card_eq hscard
  let e : s' ≃ Fin (3 ^ (k - 1) + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hs'card)
  refine ⟨fun i => pieceEdgesS G ω u hAc (e.symm i).1, ?_, ?_, ?_⟩
  · intro i
    exact pieceEdgesS_subset G ω u hAc hne (hp _ (hs'sub (e.symm i).2))
  · intro i
    apply pieceEdgesS_mem_maxMeets G ω u hAΛ hAc hne hlNat (hp _ (hs'sub (e.symm i).2))
    exact Nat.ceil_le.mpr (hmark _ (hs'sub (e.symm i).2)).1
  · intro i j hij
    have hne' : (e.symm i).1 ≠ (e.symm j).1 := by
      intro h
      exact hij (e.symm.injective (Subtype.ext h))
    exact pieceEdgesS_disjoint G ω u hAc hne (hp _ (hs'sub (e.symm i).2))
      (hp _ (hs'sub (e.symm j).2))
      (hdisj _ (hs'sub (e.symm i).2) _ (hs'sub (e.symm j).2) hne')

/-- **(2.11), arbitrary vertex type, real threshold:** one pointed witness followed by the
iterated maximal-cluster disjoint occurrence. -/
theorem meetsReal_disjointOccurrence_anyV {lam : ℝ} {k : ℕ}
    (hlam : 1 ≤ lam) (hk : 1 ≤ k) (Λ : Finset V) (u : V) :
    MeetsReal G Λ (3 ^ k * lam) u ⊆ DisjointOccurrence (Meets G Λ u ⌈lam⌉₊)
      (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ ⌈lam⌉₊)) := by
  classical
  have hlNat : 1 ≤ ⌈lam⌉₊ := Nat.ceil_pos.mpr (zero_lt_one.trans_le hlam)
  intro ω hω
  obtain ⟨t, htΛ, htcard, hconn⟩ := hω
  set A : Finset V := Λ.filter (fun x => Conn G ω u x) with hAdef
  have hAΛ : A ⊆ Λ := Finset.filter_subset _ _
  have hAc : ∀ x ∈ A, Conn G ω u x := fun x hx => (Finset.mem_filter.mp hx).2
  have hAcard : 3 ^ k * lam ≤ (A.card : ℝ) := by
    have hsub : t ⊆ A := fun y hy => Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hc := Finset.card_le_card hsub
    have hc' : (t.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hc
    exact htcard.trans hc'
  have hne : A.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < 3 ^ k * lam := by positivity
    have hc : (0 : ℝ) < (A.card : ℝ) := hpos.trans_le hAcard
    exact_mod_cast hc
  obtain ⟨s, hscard, hp, hmark, hdisj⟩ :=
    exists_trunc_pieces_real G ω u hAc hne hlam hk hAcard
  have hsne : s.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_le_succ (Nat.zero_le _)) hscard)
  obtain ⟨pstar, hpstar_mem, hpstar_min⟩ :=
    Finset.exists_min_image s
      (fun p : TS G ω u A × Finset (TS G ω u A) => bdist G ω u (p.1 : V)) hsne
  have hpps : IsRootedPiece (parS G ω u hAc) pstar.1 pstar.2 := hp pstar hpstar_mem
  obtain ⟨s', hs'sub, hs'card⟩ : ∃ s' ⊆ s.erase pstar, s'.card = 3 ^ (k - 1) := by
    refine Finset.exists_subset_card_eq ?_
    rw [Finset.card_erase_of_mem hpstar_mem]
    omega
  have hs's : s' ⊆ s := hs'sub.trans (Finset.erase_subset _ _)
  have hpstar_notin : pstar ∉ s' := by
    intro h
    exact (Finset.mem_erase.mp (hs'sub h)).1 rfl
  let e : s' ≃ Fin (3 ^ (k - 1)) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hs'card)
  set Wf : Fin (3 ^ (k - 1)) → Finset E :=
    fun i => pieceEdgesS G ω u hAc (e.symm i).1 with hWf
  set Wstar : Finset E := pieceEdgesS G ω u hAc pstar ∪ spineTo G ω u hAc pstar.1 with hWstar
  have hWs1 : (pieceEdgesS G ω u hAc pstar : Set E) ⊆ (Wstar : Set E) := by
    rw [hWstar]; exact Finset.subset_union_left
  have hWs2 : (spineTo G ω u hAc pstar.1 : Set E) ⊆ (Wstar : Set E) := by
    rw [hWstar]; exact Finset.subset_union_right
  refine ⟨Wstar, Finset.univ.sup Wf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, hWstar, Finset.mem_union] at hx
    rcases hx with h | h
    · exact pieceEdgesS_subset G ω u hAc hne hpps h
    · exact spineTo_subset G ω u hAc pstar.1 h
  · intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp (Finset.mem_coe.mp hx)
    exact pieceEdgesS_subset G ω u hAc hne (hp _ (hs's (e.symm i).2)) (Finset.mem_coe.mp hi)
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp hx'
    have hq : (e.symm i).1 ∈ s := hs's (e.symm i).2
    have hqp : (e.symm i).1 ≠ pstar := by
      intro h
      exact hpstar_notin (h ▸ (e.symm i).2)
    have hdq : Disjoint (Wstar) (pieceEdgesS G ω u hAc (e.symm i).1) := by
      rw [hWstar, Finset.disjoint_union_left]
      exact ⟨pieceEdgesS_disjoint G ω u hAc hne hpps (hp _ hq)
          (hdisj pstar hpstar_mem _ hq hqp.symm),
        spineTo_disjoint_piece G ω u hAc hne hp hpstar_min hq hqp⟩
    exact Finset.disjoint_left.mp hdq hx hi
  · have hmarkstar : lam ≤ ((markSetS G ω u A ∩ pstar.2).card : ℝ) :=
      (hmark pstar hpstar_mem).1
    have hpos : 0 < (markSetS G ω u A ∩ pstar.2).card := by
      have hpos' : (0 : ℝ) < ((markSetS G ω u A ∩ pstar.2).card : ℝ) := by
        exact zero_lt_one.trans_le (hlam.trans hmarkstar)
      exact_mod_cast hpos'
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have haP : a ∈ pstar.2 := (Finset.mem_inter.mp ha).2
    refine ⟨(markSetS G ω u A ∩ pstar.2).image (Subtype.val : TS G ω u A → V), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hAΛ ((mem_markSetS (G := G) (ω := ω) (r := u) (A := A)).mp
        (Finset.mem_inter.mp hb).1)
    · rw [Finset.card_image_of_injective _ (fun p q hpq => Subtype.ext hpq)]
      exact Nat.ceil_le.mpr hmarkstar
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hbP : b ∈ pstar.2 := (Finset.mem_inter.mp hb).2
      have h1 : Conn G ((Wstar : Finset E) : Set E) (u : V) (pstar.1 : V) :=
        conn_mono G hWs2 (conn_spineTo G ω u hAc pstar.1)
      have h2 : Conn G ((Wstar : Finset E) : Set E) (pstar.1 : V) (b : V) :=
        conn_mono G hWs1 (piece_conn_pieceEdgesS G ω u hAc hne hpps hpps.1 hbP)
      exact conn_trans (G := G) (ω := ((Wstar : Finset E) : Set E)) h1 h2
  · refine ⟨Wf, ?_, ?_, ?_⟩
    · intro i
      exact Finset.le_sup (f := Wf) (Finset.mem_univ i)
    · intro i
      apply pieceEdgesS_mem_maxMeets G ω u hAΛ hAc hne hlNat (hp _ (hs's (e.symm i).2))
      exact Nat.ceil_le.mpr (hmark _ (hs's (e.symm i).2)).1
    · intro i j hij
      have hne' : (e.symm i).1 ≠ (e.symm j).1 := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      exact pieceEdgesS_disjoint G ω u hAc hne (hp _ (hs's (e.symm i).2))
        (hp _ (hs's (e.symm j).2))
        (hdisj _ (hs's (e.symm i).2) _ (hs's (e.symm j).2) hne')

end Inclusions

/-! ## Probability bounds under the countable independent edge law -/

section Probability

variable [Countable E]

/-- **(2.8), arbitrary vertex type and real threshold.** -/
theorem maxMeetsReal_pow_bound_anyV (G : BondGraph V E) (Λ : Finset V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1) + 1) := by
  classical
  let f : Fin (3 ^ (k - 1) + 1) → Set (Set E) := fun _ => MaxMeets G Λ ⌈lam⌉₊
  have hmono : (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (DisjointOccurrenceFin f) :=
    measureReal_mono (maxMeetsReal_disjointOccurrence_anyV G hlam hk Λ)
  have hbk : (edgeLaw p).real (DisjointOccurrenceFin f) ≤
      ∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i) :=
    bk_fin p hp _ (fun _ => maxMeets_upper_anyV G Λ _)
    (fun _ => maxMeets_finiteWitness_anyV G Λ _)
  have hprod : (∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i)) =
      (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1) + 1) := by
    simp [f, Finset.prod_const]
  calc
    (edgeLaw p).real (MaxMeetsReal G Λ (3 ^ k * lam))
        ≤ (edgeLaw p).real (DisjointOccurrenceFin f) := hmono
    _ ≤ ∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (f _i) := hbk
    _ = (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1) + 1) := hprod
    _ = (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1) + 1) := by
        rw [maxMeetsReal_eq_ceil_anyV]

/-- **(2.9), arbitrary vertex type and real threshold. -/
theorem meetsReal_pow_bound_anyV (G : BondGraph V E) (Λ : Finset V) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u) ≤
      (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (MeetsReal G Λ lam u) := by
  classical
  let f : Fin (3 ^ (k - 1)) → Set (Set E) := fun _ => MaxMeets G Λ ⌈lam⌉₊
  have hmono : (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u) ≤
      (edgeLaw p).real (DisjointOccurrence (Meets G Λ u ⌈lam⌉₊)
        (DisjointOccurrenceFin f)) :=
    measureReal_mono (meetsReal_disjointOccurrence_anyV G hlam hk Λ u)
  have hbk := bkEdge p hp (Meets G Λ u ⌈lam⌉₊) (DisjointOccurrenceFin f)
    (meets_upper_anyV G Λ (lam := lam) u) (disjointOccurrenceFin_upper _)
    (meets_finiteWitness_anyV G Λ (lam := lam) u) (disjointOccurrenceFin_finiteWitness _)
  have hfin := bk_fin p hp f (fun _ => maxMeets_upper_anyV G Λ _)
    (fun _ => maxMeets_finiteWitness_anyV G Λ _)
  have hprod : (∏ _i : Fin (3 ^ (k - 1)), (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊)) =
      (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hstep : (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) *
      (edgeLaw p).real (DisjointOccurrenceFin f) ≤
      (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) *
        (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1)) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left hfin (by positivity)
  calc
    (edgeLaw p).real (MeetsReal G Λ (3 ^ k * lam) u)
        ≤ (edgeLaw p).real (DisjointOccurrence (Meets G Λ u ⌈lam⌉₊)
          (DisjointOccurrenceFin f)) := hmono
    _ ≤ (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) *
        (edgeLaw p).real (DisjointOccurrenceFin f) := hbk
    _ ≤ (edgeLaw p).real (Meets G Λ u ⌈lam⌉₊) *
        (edgeLaw p).real (MaxMeets G Λ ⌈lam⌉₊) ^ (3 ^ (k - 1)) := hstep
    _ = (edgeLaw p).real (MaxMeetsReal G Λ lam) ^ (3 ^ (k - 1)) *
        (edgeLaw p).real (MeetsReal G Λ lam u) := by
        rw [maxMeetsReal_eq_ceil_anyV, meetsReal_eq_ceil_anyV]
        ring

end Probability

end Countable
end Hutchcroft
