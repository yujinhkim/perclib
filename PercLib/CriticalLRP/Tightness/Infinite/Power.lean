/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# (2.8) and (2.9) for an arbitrary vertex type and a *countable* edge set

Reference: T. Hutchcroft, arXiv:2008.11197v2, Section 2.1, Theorem 2.3, inequalities (2.8),(2.9).

`Tightness/MaxClusterPower.meets_pow_bound` proves (2.8) for `[Fintype V] [Fintype E]`, by applying
`bk_fin` to the disjoint witnesses of `meets_disjointOccurrence`.  Nothing in `bkEdge` / `bk_fin`
needs finiteness of the edge set — both are stated for `[Countable E]` — so with the witness
inclusions of `TruncatedWindow.lean` ((2.10), arbitrary `V`) and `PointedWindow.lean` ((2.11),
arbitrary `V`) the probabilistic inequalities follow for an **arbitrary vertex type** and a
**countable edge set**:

* `meets_pow_bound_anyV` : `P(|K_max(Λ)| ≥ 3^k lam) ≤ P(|K_max(Λ)| ≥ lam) ^ (3^(k-1)+1)`;
* `pointed_pow_bound_anyV` : `P(|K_u ∩ Λ| ≥ 3^k lam) ≤ P(|K_u ∩ Λ| ≥ lam) · P(|K_max(Λ)| ≥ lam) ^ 3^(k-1)`.

The only measure-dependent hypothesis is `p e < 1` (needed by BK); no `p e = 1` case is claimed.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.Infinite.Pointed

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft
namespace Countable

open PercLib.CriticalLRP.Percolation Hutchcroft MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] {E : Type*} [DecidableEq E] [Nonempty E] [Countable E]

/-! ### Finite witnesses, without finiteness of `V` -/

/-- A connection already holds using finitely many open edges. -/
theorem conn_exists_finset_anyV (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) : ∃ W : Finset E, (W : Set E) ⊆ ω ∧ Conn G (W : Set E) x y := by
  induction h with
  | refl => exact ⟨∅, by simp, conn_refl G _ _⟩
  | tail _ hstep ih =>
      obtain ⟨W, hW, hc⟩ := ih
      obtain ⟨e, he, hE⟩ := hstep
      refine ⟨insert e W, ?_, ?_⟩
      · intro e' he'
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp he') with rfl | h'
        · exact he
        · exact hW (Finset.mem_coe.mp h')
      · exact (conn_mono G (by
          intro e' he'
          exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp he'))) hc).tail
          ⟨e, Finset.mem_coe.mpr (Finset.mem_insert_self e W), hE⟩

/-- The maximal-cluster event is increasing (arbitrary `V`). -/
theorem maxMeets_upper_anyV (G : BondGraph V E) (Λ : Finset V) (lam : ℕ) :
    IsUpperSet (MaxMeets G Λ lam) := by
  rintro ω ω' hωω' ⟨t, ht, hcard, u, hc⟩
  exact ⟨t, ht, hcard, u, fun y hy => conn_mono G hωω' (hc y hy)⟩

/-- The maximal-cluster event is finitely witnessed (arbitrary `V`). -/
theorem maxMeets_finiteWitness_anyV (G : BondGraph V E) (Λ : Finset V) (lam : ℕ) :
    FiniteWitness (MaxMeets G Λ lam) := by
  classical
  rintro ω ⟨t, ht, hcard, u, hc⟩
  set F : V → Finset E := fun y =>
    if h : y ∈ t then (conn_exists_finset_anyV G (hc y h)).choose else ∅ with hF
  have hFsub : ∀ y ∈ t, (F y : Set E) ⊆ ω := by
    intro y hy
    have := (conn_exists_finset_anyV G (hc y hy)).choose_spec.1
    simpa [hF, dite_eq_left hy] using this
  have hFconn : ∀ y ∈ t, Conn G (F y : Set E) u y := by
    intro y hy
    have := (conn_exists_finset_anyV G (hc y hy)).choose_spec.2
    simpa [hF, dite_eq_left hy] using this
  refine ⟨t.biUnion F, ?_, t, ht, hcard, u, ?_⟩
  · intro e he
    obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact hFsub y hy hey
  · intro y hy
    exact conn_mono G (fun e he => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hy, he⟩))
      (hFconn y hy)

/-- The pointed event is finitely witnessed (arbitrary `V`). -/
theorem pointedMeets_finiteWitness (G : BondGraph V E) (Λ : Finset V) (u : V) (lam : ℕ) :
    FiniteWitness (PointedMeets G Λ u lam) := by
  classical
  rintro ω ⟨t, ht, hcard, hc⟩
  set F : V → Finset E := fun y =>
    if h : y ∈ t then (conn_exists_finset_anyV G (hc y h)).choose else ∅ with hF
  have hFsub : ∀ y ∈ t, (F y : Set E) ⊆ ω := by
    intro y hy
    have := (conn_exists_finset_anyV G (hc y hy)).choose_spec.1
    simpa [hF, dite_eq_left hy] using this
  have hFconn : ∀ y ∈ t, Conn G (F y : Set E) u y := by
    intro y hy
    have := (conn_exists_finset_anyV G (hc y hy)).choose_spec.2
    simpa [hF, dite_eq_left hy] using this
  refine ⟨t.biUnion F, ?_, t, ht, hcard, ?_⟩
  · intro e he
    obtain ⟨y, hy, hey⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp he)
    exact hFsub y hy hey
  · intro y hy
    exact conn_mono G (fun e he => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hy, he⟩))
      (hFconn y hy)

/-! ### (2.8) and (2.9) -/

/-- **(2.8) of arXiv:2008.11197v2 for an arbitrary vertex type and a countable edge set.**
`P(|K_max(Λ)| ≥ 3^k lam) ≤ P(|K_max(Λ)| ≥ lam) ^ (3^(k-1)+1)`, for integer `lam ≥ 2`, `k ≥ 1`
and edge probabilities `p e < 1`. -/
theorem meets_pow_bound_anyV (G : BondGraph V E) (Λ : Finset V) {lam k : ℕ}
    (hlam : 2 ≤ lam) (hk : 1 ≤ k) (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1) + 1) := by
  classical
  have hmono : (edgeLaw p).real (MaxMeets G Λ (3 ^ k * lam)) ≤
      (edgeLaw p).real
        (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ lam)) :=
    measureReal_mono (meets_disjointOccurrence_anyV G hlam hk)
  have hbk := bk_fin p hp (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ lam)
    (fun _ => maxMeets_upper_anyV G Λ lam) (fun _ => maxMeets_finiteWitness_anyV G Λ lam)
  have hprod : (∏ _i : Fin (3 ^ (k - 1) + 1), (edgeLaw p).real (MaxMeets G Λ lam)) =
      (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1) + 1) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  linarith [hmono, hbk, hprod]

/-- **(2.9) of arXiv:2008.11197v2 for an arbitrary vertex type and a countable edge set.**

`P(|K_u ∩ Λ| ≥ 3^k lam) ≤ P(|K_u ∩ Λ| ≥ lam) · P(|K_max(Λ)| ≥ lam) ^ 3^(k-1)`:

one witness is the pointed (single-cluster) one, the remaining `3^(k-1)` are maximal-cluster
witnesses, and BK is applied to the pair (pointed event, iterated maximal event). -/
theorem pointed_pow_bound_anyV (G : BondGraph V E) (Λ : Finset V) (u : V) {lam k : ℕ}
    (hlam : 2 ≤ lam) (hk : 1 ≤ k) (p : E → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real (PointedMeets G Λ u (3 ^ k * lam)) ≤
      (edgeLaw p).real (PointedMeets G Λ u lam) *
        (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1)) := by
  classical
  have hmono : (edgeLaw p).real (PointedMeets G Λ u (3 ^ k * lam)) ≤
      (edgeLaw p).real (DisjointOccurrence (PointedMeets G Λ u lam)
        (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam))) :=
    measureReal_mono (pointed_disjointOccurrence_anyV G u hlam hk)
  have hbk := bkEdge p hp (PointedMeets G Λ u lam)
    (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam))
    (pointedMeets_upper G Λ u lam) (disjointOccurrenceFin_upper _)
    (pointedMeets_finiteWitness G Λ u lam) (disjointOccurrenceFin_finiteWitness _)
  have hfin := bk_fin p hp (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam)
    (fun _ => maxMeets_upper_anyV G Λ lam) (fun _ => maxMeets_finiteWitness_anyV G Λ lam)
  have hprod : (∏ _i : Fin (3 ^ (k - 1)), (edgeLaw p).real (MaxMeets G Λ lam)) =
      (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hstep : (edgeLaw p).real (PointedMeets G Λ u lam) *
      (edgeLaw p).real (DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1)) => MaxMeets G Λ lam)) ≤
      (edgeLaw p).real (PointedMeets G Λ u lam) *
        (edgeLaw p).real (MaxMeets G Λ lam) ^ (3 ^ (k - 1)) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left hfin (by positivity)
  exact le_trans hmono (le_trans hbk hstep)

end Countable
end Hutchcroft
