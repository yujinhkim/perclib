/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# (2.11) for an arbitrary vertex type: the pointed single-cluster step

Reference: T. Hutchcroft, arXiv:2008.11197v2, Section 2.1, proof of Theorem 2.3, step (2.11).

(2.11) is the *pointed* form of the disjoint-occurrence inclusion: for `{|K_u ∩ Λ| ≥ 3^k λ}` one of
the `3^(k-1)+1` disjoint witnesses must force `{|K_u ∩ Λ| ≥ λ}` (it must connect `u` itself to `λ`
marked vertices), and only the remaining `3^(k-1)` need force the maximal-cluster event
`{|K_max(Λ)| ≥ λ}`.  The finite-vertex form is in `Tightness/PointedPower.lean`; this file removes the finiteness assumption on the vertex type.

The source gets it from Lemma 2.4(2) ("every vertex is incident to some piece").  Here that is
replaced by the repair of m7 (`Spine.lean`, previous swarm): take the piece whose root is *closest*
to the cluster root `u` and adjoin the ancestor spine of that root up to `u`.  Every proper ancestor
of that root lies outside every piece — otherwise the piece holding it would have a root strictly
closer to `u`, contradicting minimality — so the augmented witness is edge-disjoint from all the
other pieces and contains `u`.

Scope: arbitrary vertex type `V` (no finiteness, no countability), integer `lam ≥ 2`, `k ≥ 1`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.Infinite.Truncated

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft
namespace Countable

open PercLib.CriticalLRP.Percolation Hutchcroft

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] {E : Type*} [DecidableEq E] [Nonempty E]

/-! ### The BFS distance along parent iterates -/

section Iter

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- `n` parent steps from a point of the cluster land exactly `n` levels closer to the root. -/
theorem par_iterate_bdist_eq {x : V} (hc : Conn G ω r x) {n : ℕ}
    (hn : n ≤ bdist G ω r x) :
    bdist G ω r ((par G ω r)^[n] x) + n = bdist G ω r x := by
  induction n with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hcj := par_iterate_conn G ω r hc j
      have hjle : bdist G ω r ((par G ω r)^[j] x) + j = bdist G ω r x := ih (by omega)
      have hpos : bdist G ω r ((par G ω r)^[j] x) ≠ 0 := by omega
      have hne : (par G ω r)^[j] x ≠ r := fun h => hpos ((bdist_eq_zero_iff G ω r hcj).mpr h)
      have hstep := par_bdist_succ G ω r hcj hne
      omega

/-- After `bdist x` parent steps everything is the root. -/
theorem par_iterate_bdist_zero {x : V} (hc : Conn G ω r x) {n : ℕ}
    (hn : bdist G ω r x ≤ n) : bdist G ω r ((par G ω r)^[n] x) = 0 := by
  have hsplit : (par G ω r)^[n] x
      = (par G ω r)^[n - bdist G ω r x] ((par G ω r)^[bdist G ω r x] x) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn]
  rw [hsplit, par_bdist_iterate G ω r hc, par_iterate_root G ω r]
  exact (bdist_eq_zero_iff G ω r (conn_refl G ω r)).mpr rfl

theorem par_iterate_bdist_le {x : V} (hc : Conn G ω r x) (n : ℕ) :
    bdist G ω r ((par G ω r)^[n] x) ≤ bdist G ω r x := by
  by_cases h : n ≤ bdist G ω r x
  · have := par_iterate_bdist_eq G ω r hc h
    omega
  · push Not at h
    have := par_iterate_bdist_zero G ω r hc (le_of_lt h)
    omega

end Iter

/-! ### The pointed event `{|K_u ∩ Λ| ≥ lam}` -/

section Event

variable (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ)

/-- `PointedMeets G Λ u lam`: the cluster of `u` meets the finite window `Λ` in at least `lam`
vertices, i.e. the event `{|K_u ∩ Λ| ≥ lam}` of (2.9)/(2.11). -/
def PointedMeets : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y}

theorem mem_PointedMeets {ω : Set E} :
    ω ∈ PointedMeets G Λ u lam ↔
      ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y :=
  Iff.rfl

theorem pointedMeets_upper : IsUpperSet (PointedMeets G Λ u lam) := by
  rintro ω ω' hωω' ⟨t, ht, hcard, hc⟩
  exact ⟨t, ht, hcard, fun y hy => conn_mono G hωω' (hc y hy)⟩

/-- The pointed event is contained in the maximal-cluster event. -/
theorem pointedMeets_subset_max : PointedMeets G Λ u lam ⊆ MaxMeets G Λ lam := by
  rintro ω ⟨t, ht, hcard, hc⟩
  exact ⟨t, ht, hcard, u, hc⟩

end Event

/-! ### Depths in the truncated tree: ancestors are closer to the root -/

section Depth

variable (G : BondGraph V E) (ω : Set E) (u : V) {A : Finset V}

/-- A point of the descendant closure of `w` is at least as deep as `w`. -/
theorem bdist_le_of_mem_desc (hAc : ∀ x ∈ A, Conn G ω u x) {w y : TS G ω u A}
    (h : y ∈ desc (parS G ω u hAc) w) :
    bdist G ω u (w : V) ≤ bdist G ω u (y : V) := by
  classical
  rw [mem_desc] at h
  obtain ⟨n, hn⟩ := h
  have hw : (w : V) = ((parS G ω u hAc)^[n] y : V) := by rw [hn]
  rw [hw, parS_iterate_val]
  exact par_iterate_bdist_le G ω u (truncSet_conn_of_mem G ω u hAc y.2) n

/-- A *proper* descendant of `w` is strictly deeper. -/
theorem bdist_lt_of_mem_desc_ne (hAc : ∀ x ∈ A, Conn G ω u x) (hne : A.Nonempty)
    {w y : TS G ω u A} (h : y ∈ desc (parS G ω u hAc) w) (hyw : y ≠ w) :
    bdist G ω u (w : V) < bdist G ω u (y : V) := by
  classical
  rw [mem_desc] at h
  obtain ⟨n, hn⟩ := h
  have hnpos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0] at hn
      simp only [Function.iterate_zero_apply] at hn
      exact hyw hn
    · exact h0
  have hyu : (y : V) ≠ u := by
    intro hcon
    have hyroot : y = (⟨u, root_mem_truncSet G ω u hAc hne⟩ : TS G ω u A) := Subtype.ext hcon
    rw [hyroot] at hn
    have hfix := isRootedForest_fix (parS_isRootedForest G ω u hAc hne) n
    exact hyw (hyroot.trans (hfix.symm.trans hn))
  have hyle : 1 ≤ bdist G ω u (y : V) := by
    rcases Nat.eq_zero_or_pos (bdist G ω u (y : V)) with h0 | h0
    · exact absurd ((bdist_eq_zero_iff G ω u (truncSet_conn_of_mem G ω u hAc y.2)).mp h0) hyu
    · exact h0
  have hbw : bdist G ω u (w : V) = bdist G ω u ((par G ω u)^[n] (y : V)) := by
    have hw : (w : V) = ((parS G ω u hAc)^[n] y : V) := by rw [hn]
    rw [hw, parS_iterate_val]
  by_cases hcase : n ≤ bdist G ω u (y : V)
  · have hbez := par_iterate_bdist_eq G ω u (truncSet_conn_of_mem G ω u hAc y.2) hcase
    omega
  · push Not at hcase
    have hz := par_iterate_bdist_zero G ω u (truncSet_conn_of_mem G ω u hAc y.2)
      (le_of_lt hcase)
    omega

end Depth

/-! ### The spine from a point of the closure up to the cluster root -/

section Spine

variable (G : BondGraph V E) (ω : Set E) (u : V) {A : Finset V}

/-- The parent edges along the `par`-chain from `x` up to the root. -/
noncomputable def spineTo (hAc : ∀ x ∈ A, Conn G ω u x) (x : TS G ω u A) : Finset E :=
  (Finset.range (bdist G ω u (x : V))).image
    (fun i => parEdgeS G ω u hAc
      ⟨(par G ω u)^[i] (x : V), par_iterate_mem_truncSet G ω u hAc x.2 i⟩)

theorem mem_spineTo {hAc : ∀ x ∈ A, Conn G ω u x} {x : TS G ω u A} {e : E} :
    e ∈ spineTo G ω u hAc x ↔ ∃ i < bdist G ω u (x : V),
      parEdgeS G ω u hAc
        ⟨(par G ω u)^[i] (x : V), par_iterate_mem_truncSet G ω u hAc x.2 i⟩ = e := by
  classical
  simp only [spineTo, Finset.mem_image, Finset.mem_range]

/-- The levels of the spine are non-root points, so their chosen edges are open. -/
theorem spineTo_subset (hAc : ∀ x ∈ A, Conn G ω u x) (x : TS G ω u A) :
    (spineTo G ω u hAc x : Set E) ⊆ ω := by
  classical
  intro e he
  rw [Finset.mem_coe, mem_spineTo] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hb := par_iterate_bdist_eq G ω u (truncSet_conn_of_mem G ω u hAc x.2) (le_of_lt hi)
  have hne : ((par G ω u)^[i] (x : V)) ≠ u := by
    intro hcon
    rw [hcon] at hb
    have hz : bdist G ω u u = 0 := (bdist_eq_zero_iff G ω u (conn_refl G ω u)).mpr rfl
    rw [hz] at hb
    omega
  exact (parEdgeS_spec G ω u hAc hne).1

/-- **The spine joins a point of the closure to the root.** -/
theorem conn_spineTo (hAc : ∀ x ∈ A, Conn G ω u x) (x : TS G ω u A) :
    Conn G ((spineTo G ω u hAc x : Finset E) : Set E) (u : V) (x : V) := by
  classical
  have key : ∀ n ≤ bdist G ω u (x : V),
      Conn G ((spineTo G ω u hAc x : Finset E) : Set E) (x : V)
        ((par G ω u)^[n] (x : V)) := by
    intro n hn
    induction n with
    | zero => simpa using conn_refl G ((spineTo G ω u hAc x : Finset E) : Set E) (x : V)
    | succ j ih =>
        have hjn : j < bdist G ω u (x : V) := by omega
        have hb := par_iterate_bdist_eq G ω u (truncSet_conn_of_mem G ω u hAc x.2)
          (le_of_lt hjn)
        have hne : ((par G ω u)^[j] (x : V)) ≠ u := by
          intro hcon
          rw [hcon] at hb
          have hz : bdist G ω u u = 0 := (bdist_eq_zero_iff G ω u (conn_refl G ω u)).mpr rfl
          rw [hz] at hb
          omega
        have hstep : ∃ e ∈ ((spineTo G ω u hAc x : Finset E) : Set E),
            G e = s(((par G ω u)^[j] (x : V)), (par G ω u ((par G ω u)^[j] (x : V)))) := by
          refine ⟨parEdgeS G ω u hAc
              ⟨(par G ω u)^[j] (x : V), par_iterate_mem_truncSet G ω u hAc x.2 j⟩, ?_, ?_⟩
          · rw [Finset.mem_coe, mem_spineTo]
            exact ⟨j, hjn, rfl⟩
          · exact (parEdgeS_spec G ω u hAc hne).2
        rw [Function.iterate_succ_apply']
        exact (ih (by omega)).tail hstep
  have hlast := key (bdist G ω u (x : V)) le_rfl
  rw [par_bdist_iterate G ω u (truncSet_conn_of_mem G ω u hAc x.2)] at hlast
  exact conn_symm (G := G) (ω := ((spineTo G ω u hAc x : Finset E) : Set E)) hlast

/-- **Every proper ancestor level of a piece root is outside every piece** of a family whose roots
are all at least as deep.  This is the combinatorial heart of the spine repair. -/
theorem spine_ancestor_not_mem (hAc : ∀ x ∈ A, Conn G ω u x) (hne : A.Nonempty)
    {s : Finset (TS G ω u A × Finset (TS G ω u A))}
    {pstar : TS G ω u A × Finset (TS G ω u A)}
    (hp : ∀ p ∈ s, IsRootedPiece (parS G ω u hAc) p.1 p.2)
    (hpstar_min : ∀ q ∈ s, bdist G ω u (pstar.1 : V) ≤ bdist G ω u (q.1 : V))
    {q : TS G ω u A × Finset (TS G ω u A)} (hq : q ∈ s) (hqp : q ≠ pstar)
    {i : ℕ} (hi : i < bdist G ω u (pstar.1 : V)) :
    (⟨(par G ω u)^[i] (pstar.1 : V),
      par_iterate_mem_truncSet G ω u hAc pstar.1.2 i⟩ : TS G ω u A) ∉ q.2.erase q.1 := by
  classical
  intro hmem
  obtain ⟨hyv, hyq⟩ := Finset.mem_erase.mp hmem
  have hdesc : (⟨(par G ω u)^[i] (pstar.1 : V),
      par_iterate_mem_truncSet G ω u hAc pstar.1.2 i⟩ : TS G ω u A)
      ∈ desc (parS G ω u hAc) q.1 := isRootedPiece_subset_desc (hp q hq) hyq
  have hdepth := bdist_lt_of_mem_desc_ne G ω u hAc hne hdesc hyv
  have hle := par_iterate_bdist_le G ω u (truncSet_conn_of_mem G ω u hAc pstar.1.2) i
  have hmin := hpstar_min q hq
  exact absurd (lt_of_le_of_lt hmin (lt_of_lt_of_le hdepth hle)) (lt_irrefl _)

/-- **The spine of a minimal-depth piece is edge-disjoint from every other piece.** -/
theorem spineTo_disjoint_piece (hAc : ∀ x ∈ A, Conn G ω u x) (hne : A.Nonempty)
    {s : Finset (TS G ω u A × Finset (TS G ω u A))}
    {pstar : TS G ω u A × Finset (TS G ω u A)}
    (hp : ∀ p ∈ s, IsRootedPiece (parS G ω u hAc) p.1 p.2)
    (hpstar_min : ∀ q ∈ s, bdist G ω u (pstar.1 : V) ≤ bdist G ω u (q.1 : V))
    {q : TS G ω u A × Finset (TS G ω u A)} (hq : q ∈ s) (hqp : q ≠ pstar) :
    Disjoint (spineTo G ω u hAc pstar.1) (pieceEdgesS G ω u hAc q) := by
  classical
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_spineTo] at he
  obtain ⟨i, hi, rfl⟩ := he
  rw [mem_pieceEdgesS] at he'
  obtain ⟨z, hz, hze⟩ := he'
  have hb := par_iterate_bdist_eq G ω u (truncSet_conn_of_mem G ω u hAc pstar.1.2) (le_of_lt hi)
  have hyu : ((par G ω u)^[i] (pstar.1 : V)) ≠ u := by
    intro hcon
    rw [hcon] at hb
    have hz0 : bdist G ω u u = 0 := (bdist_eq_zero_iff G ω u (conn_refl G ω u)).mpr rfl
    rw [hz0] at hb
    omega
  have hzu : (z : V) ≠ u := piece_erase_ne_root G ω u hAc hne (hp q hq) hz
  have hzy : z = (⟨(par G ω u)^[i] (pstar.1 : V),
      par_iterate_mem_truncSet G ω u hAc pstar.1.2 i⟩ : TS G ω u A) :=
    parEdgeS_inj G ω u hAc hzu hyu hze
  exact spine_ancestor_not_mem G ω u hAc hne hp hpstar_min hq hqp hi (hzy ▸ hz)

end Spine

/-! ### (2.11) for an arbitrary vertex type -/

section Main

variable (G : BondGraph V E) (ω : Set E) (u : V)

/-- **(2.11) for an arbitrary vertex type.**  If the cluster of `u` meets the finite window `Λ` in
at least `3^k lam` vertices (`lam ≥ 2`, `k ≥ 1`), then `ω` has disjoint finite witnesses: one set of
open edges forcing `{|K_u ∩ Λ| ≥ lam}` (it connects `u` to `lam` marked vertices) and `3^(k-1)`
further sets each forcing `{|K_max(Λ)| ≥ lam}`. -/
theorem pointed_disjointOccurrence_anyV {Λ : Finset V} {lam k : ℕ}
    (hlam : 2 ≤ lam) (hk : 1 ≤ k) :
    PointedMeets G Λ u (3 ^ k * lam) ⊆
      DisjointOccurrence (PointedMeets G Λ u lam)
        (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam)) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, hconn⟩ : ∃ t : Finset V, t ⊆ Λ ∧ 3 ^ k * lam ≤ t.card ∧
      ∀ y ∈ t, Conn G ω u y := hω
  set A : Finset V := Λ.filter (fun x => Conn G ω u x) with hAdef
  have hAΛ : A ⊆ Λ := Finset.filter_subset _ _
  have hAc : ∀ x ∈ A, Conn G ω u x := fun x hx => (Finset.mem_filter.mp hx).2
  have hAcard : 3 ^ k * lam ≤ A.card := by
    have hsub : t ⊆ A := fun y hy => Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    exact le_trans htcard (Finset.card_le_card hsub)
  have hne : A.Nonempty := by
    have hpos : 0 < 3 ^ k * lam := Nat.mul_pos (by positivity) (by omega)
    exact Finset.card_pos.mp (lt_of_lt_of_le hpos hAcard)
  obtain ⟨s, hscard, hp, hmark, hdisj⟩ := exists_trunc_pieces G ω u hAc hne hlam hk hAcard
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
  · -- the pointed witness is open
    intro x hx
    rw [Finset.mem_coe, hWstar, Finset.mem_union] at hx
    rcases hx with h | h
    · exact pieceEdgesS_subset G ω u hAc hne hpps h
    · exact spineTo_subset G ω u hAc pstar.1 h
  · -- the remaining witnesses are open
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp (Finset.mem_coe.mp hx)
    exact pieceEdgesS_subset G ω u hAc hne (hp _ (hs's (e.symm i).2)) (Finset.mem_coe.mp hi)
  · -- disjointness of the pointed witness from the union of the others
    rw [Finset.disjoint_left]
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
  · -- the pointed witness forces `{|K_u ∩ Λ| ≥ lam}`
    have hpos : 0 < (markSetS G ω u A ∩ pstar.2).card :=
      lt_of_lt_of_le (by omega : 0 < lam) (hmark pstar hpstar_mem).1
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have haP : a ∈ pstar.2 := (Finset.mem_inter.mp ha).2
    refine ⟨(markSetS G ω u A ∩ pstar.2).image (Subtype.val : TS G ω u A → V), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hAΛ ((mem_markSetS (G := G) (ω := ω) (r := u) (A := A)).mp
        (Finset.mem_inter.mp hb).1)
    · rw [Finset.card_image_of_injective _ (fun p q hpq => Subtype.ext hpq)]
      exact (hmark pstar hpstar_mem).1
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hbP : b ∈ pstar.2 := (Finset.mem_inter.mp hb).2
      have h1 : Conn G ((Wstar : Finset E) : Set E) (u : V) (pstar.1 : V) :=
        conn_mono G hWs2 (conn_spineTo G ω u hAc pstar.1)
      have h2 : Conn G ((Wstar : Finset E) : Set E) (pstar.1 : V) (b : V) :=
        conn_mono G hWs1 (piece_conn_pieceEdgesS G ω u hAc hne hpps hpps.1 hbP)
      exact conn_trans (G := G) (ω := ((Wstar : Finset E) : Set E)) h1 h2
  · -- the union is an iterated disjoint occurrence of `3^(k-1)` maximal-cluster events
    refine ⟨Wf, ?_, ?_, ?_⟩
    · intro i
      exact Finset.le_sup (f := Wf) (Finset.mem_univ i)
    · intro i
      exact pieceEdgesS_mem_maxMeets G ω u hAΛ hAc hne (by omega) (hp _ (hs's (e.symm i).2))
        (hmark _ (hs's (e.symm i).2)).1
    · intro i j hij
      have hne' : (e.symm i).1 ≠ (e.symm j).1 := by
        intro h
        exact hij (e.symm.injective (Subtype.ext h))
      exact pieceEdgesS_disjoint G ω u hAc hne (hp _ (hs's (e.symm i).2))
        (hp _ (hs's (e.symm j).2))
        (hdisj _ (hs's (e.symm i).2) _ (hs's (e.symm j).2) hne')

end Main

end Countable
end Hutchcroft
