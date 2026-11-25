/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Step (2.10) of arXiv:2008.11197v2: the `3^k λ → λ` BK bound for the maximal cluster-window size

This file turns the combinatorics of `ClusterWitness.lean` into the probability estimate (2.8) of
T. Hutchcroft, *Power-law bounds for critical long-range percolation below the upper-critical
dimension*, arXiv:2008.11197v2, Section 2.1.

Setting: a finite bond graph `G` on a finite vertex type `V` with edge-dependent Bernoulli
parameters `p : E → unitInterval`, all `< 1`, and a finite window `Λ`.

* `MaxMeets G Λ lam` is the event `{|K_max(Λ)| ≥ lam}`: some cluster meets `Λ` in at least `lam`
  vertices.  It is increasing (`maxMeets_upper`) and finitely witnessed
  (`maxMeets_finiteWitness`: only finitely many open edges are needed).
* `meets_pow_bound` is (2.8) for integer `lam ≥ 2`, `k ≥ 1`:
  `P(|K_max(Λ)| ≥ 3^k lam) ≤ P(|K_max(Λ)| ≥ lam) ^ (3^(k-1)+1)`.

The proof is the source's: for every configuration in the left-hand event, the cluster of a vertex
`u` with `|K_u ∩ Λ| ≥ 3^k lam` is cut by `exists_open_pieces` into `≥ 3^(k-1)+1` pieces whose
parent-edge sets are pairwise disjoint *open* witnesses, each certifying `{|K_max(Λ)| ≥ lam}` on its
own.  That is exactly a disjoint occurrence of `3^(k-1)+1` copies of the event, so the iterated BK
inequality `bk_fin` (repo, `BK/Finite.lean`) gives the bound.

Scope, exactly: finite `V` and finite `E`; integer `lam ≥ 2` and `k ≥ 1`; strictly subcritical
edge probabilities `p e < 1`. Real `λ` needs the separate real-threshold piece extraction. The
printed domain `k ≥ 0` of Theorem 2.3 contains the false endpoint `k = 0`; the paper's proof and
the formal statement both use `k ≥ 1`.  The case `p e = 1`
is *not* claimed: `bk_fin` requires `p e < 1`, and nothing here proves the `p_e = 1` extension.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.ClusterWitness
public import PercLib.CriticalLRP.BK.Finite

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation Hutchcroft MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
  [Nonempty E]

/-- If two vertices of the open graph are connected, the connection already holds using a finite
set of open edges. -/
theorem conn_exists_finset (G : BondGraph V E) {ω : Set E} {x y : V} (h : Conn G ω x y) :
    ∃ W : Finset E, (W : Set E) ⊆ ω ∧ Conn G (W : Set E) x y := by
  classical
  induction h with
  | refl => exact ⟨∅, by simp, conn_refl G ((∅ : Finset E) : Set E) x⟩
  | tail _ hstep ih =>
      obtain ⟨W, hW, hconn⟩ := ih
      obtain ⟨e, he, hE⟩ := hstep
      refine ⟨insert e W, ?_, ?_⟩
      · intro e' he'
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp he') with rfl | he''
        · exact he
        · exact hW (Finset.mem_coe.mpr he'')
      · refine (conn_mono G ?_ hconn).tail ⟨e, ?_, hE⟩
        · intro e' he'
          exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp he'))
        · rw [Finset.mem_coe]
          exact Finset.mem_insert_self e W

/-! ### The event `{|K_max(Λ)| ≥ lam}` -/

section MaxMeets

variable (G : BondGraph V E) (Λ : Finset V) (lam : ℕ)

/-- `MaxMeets G Λ lam`: some cluster of the open graph meets the finite window `Λ` in at least
`lam` vertices, i.e. the event `{|K_max(Λ)| ≥ lam}` of (2.8). -/
def MaxMeets : Set (Set E) :=
  {ω | ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∃ u : V, ∀ y ∈ t, Conn G ω u y}

@[simp] theorem mem_MaxMeets {ω : Set E} :
    ω ∈ MaxMeets G Λ lam ↔
      ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∃ u : V, ∀ y ∈ t, Conn G ω u y :=
  Iff.rfl

/-- The event is increasing in the configuration. -/
theorem maxMeets_upper : IsUpperSet (MaxMeets G Λ lam) := by
  rintro ω ω' hωω' ⟨t, ht, hcard, u, hc⟩
  exact ⟨t, ht, hcard, u, fun y hy => conn_mono G hωω' (hc y hy)⟩

/-- The event is finitely witnessed: finitely many open edges suffice. -/
theorem maxMeets_finiteWitness : FiniteWitness (MaxMeets G Λ lam) := by
  classical
  rintro ω ⟨t, ht, hcard, u, hc⟩
  -- a finite connecting edge set for every marked vertex
  set F : V → Finset E := fun y =>
    if h : y ∈ t then (conn_exists_finset G (hc y h)).choose else ∅ with hF
  have hFsub : ∀ y ∈ t, (F y : Set E) ⊆ ω := by
    intro y hy
    have := (conn_exists_finset G (hc y hy)).choose_spec.1
    simpa [hF, dite_eq_left hy] using this
  have hFconn : ∀ y ∈ t, Conn G (F y : Set E) u y := by
    intro y hy
    have := (conn_exists_finset G (hc y hy)).choose_spec.2
    simpa [hF, dite_eq_left hy] using this
  refine ⟨t.biUnion F, ?_, t, ht, hcard, u, ?_⟩
  · -- the union is contained in `ω`
    intro e he
    obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact hFsub y hy hey
  · intro y hy
    exact conn_mono G (fun e he => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hy, he⟩))
      (hFconn y hy)

end MaxMeets

/-! ### Step (2.10): the disjoint-occurrence inclusion and the BK bound -/

section Bound

variable (G : BondGraph V E) (Λ : Finset V)

/-- **The disjoint-occurrence inclusion (2.10).**

If a configuration has a cluster meeting `Λ` in at least `3^k lam` vertices, then the cluster of a
suitable vertex `u` contains `3^(k-1)+1` pairwise disjoint sets of open edges, each of which on its
own already forces `{|K_max(Λ)| ≥ lam}`.  In other words

  `{|K_max(Λ)| ≥ 3^k lam} ⊆ {|K_max(Λ)| ≥ lam} ∘ ⋯ ∘ {|K_max(Λ)| ≥ lam}`  (`3^(k-1)+1` copies),

which is (2.10) of the source, with the witnesses produced by the BFS tree pieces. -/
theorem meets_disjointOccurrence {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k) :
    MaxMeets G Λ (3 ^ k * lam) ⊆
      DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ lam) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, u, hconn⟩ := mem_MaxMeets G Λ (3 ^ k * lam) |>.mp hω
  -- the marked vertices of the cluster of `u`
  have hmark : 3 ^ k * lam ≤ (markSet G ω u Λ).card := by
    have hsub : t ⊆ Λ.filter (fun x => Conn G ω u x) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    have hcard := Finset.card_le_card hsub
    have hmt : (markSet G ω u Λ).card = (Λ.filter (fun x => Conn G ω u x)).card := by
      rw [markSet, ← Finset.subtype_map (fun x => Conn G ω u x) (s := Λ), Finset.card_map]
    omega
  obtain ⟨s, hscard, hpiece, hmark', hsubω, hdisj, hev⟩ :=
    exists_open_pieces G ω u Λ hlam hk hmark
  -- select exactly `3^(k-1)+1` of the pieces
  obtain ⟨s', hs'sub, hs'card⟩ := Finset.exists_subset_card_eq hscard
  let e : s' ≃ Fin (3 ^ (k - 1) + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hs'card)
  -- their witness edge sets
  let W : Fin (3 ^ (k - 1) + 1) → Finset E :=
    fun i => pieceWt G ω u (e.symm i).1.1 (e.symm i).1.2
  refine ⟨W, ?_, ?_, ?_⟩
  · -- each witness set consists of open edges
    intro i
    exact hsubω _ (hs'sub (e.symm i).2)
  · -- each witness set forces the `lam`-event on its own
    intro i
    obtain ⟨t', ht'⟩ := hev _ (hs'sub (e.symm i).2)
    have hWi : W i = pieceWt G ω u (e.symm i).1.1 (e.symm i).1.2 := rfl
    rw [mem_MaxMeets, hWi]
    exact ⟨t', ht'.1, ht'.2.1, ht'.2.2⟩
  · -- the witness sets are pairwise disjoint
    intro i j hij
    have hne : (e.symm i).1 ≠ (e.symm j).1 := by
      intro h
      exact hij (e.symm.injective (Subtype.ext h))
    exact hdisj _ (hs'sub (e.symm i).2) _ (hs'sub (e.symm j).2) hne

/-- **(2.8) of arXiv:2008.11197v2, finite case, integer thresholds.**

For a finite bond graph, a finite window `Λ`, integer `lam ≥ 2`, `k ≥ 1`, and edge probabilities
`p e < 1`,

  `P(|K_max(Λ)| ≥ 3^k lam) ≤ P(|K_max(Λ)| ≥ lam) ^ (3^(k-1)+1)`.

This is the probabilistic step of universal tightness at the level of the maximal cluster-window
size: it converts the linear-in-`λ` size `3^k λ` into a `3^(k-1)+1`-th power of the probability of
the size-`λ` event. -/
theorem meets_pow_bound {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1) + 1) := by
  classical
  set m : ℕ := 3 ^ (k - 1) + 1 with hm
  have hmono : (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (DisjointOccurrenceFin (fun _ : Fin m => MaxMeets G Λ lam)) :=
    measureReal_mono (meets_disjointOccurrence G Λ hlam hk)
  have hbk : (edgeLaw p).real (DisjointOccurrenceFin (fun _ : Fin m => MaxMeets G Λ lam)) ≤
      ∏ _i : Fin m, (edgeLaw p).real (MaxMeets G Λ lam) :=
    bk_fin p hp _ (fun _ => maxMeets_upper G Λ lam) (fun _ => maxMeets_finiteWitness G Λ lam)
  have hprod : (∏ _i : Fin m, (edgeLaw p).real (MaxMeets G Λ lam)) =
      (edgeLaw p).real (MaxMeets G Λ lam) ^ m := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hm] at hprod ⊢
  calc (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam))
      ≤ (edgeLaw p).real (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1) + 1) =>
          MaxMeets G Λ lam)) := hmono
    _ ≤ _ := hbk
    _ = _ := hprod

end Bound

end Hutchcroft
