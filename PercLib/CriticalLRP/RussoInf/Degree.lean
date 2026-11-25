/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The lattice degree bound for the cut-off kernel

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Lemma I.4.1, where the pivotal sum over
edges is reorganized vertex by vertex (`∑_{x∈K} ∑_{y ∈ B_r(x)}`), and
Definition I.1.5.

For the cut-off model on `ℤ^d` (Definition I.1.5) only edges of `‖·‖_∞`-length at
most `r` are active, so every lattice point is incident to at most
`(2⌈r⌉₊ + 1)^d` active edges.  This file records the resulting combinatorial
counts, which turn the pivotal sum over *edges* into a sum over the (small)
cluster:

* `edgeLen` — the `‖·‖_∞` length of an unordered lattice pair;
* `activeEdges_subset_image_box` and `card_activeEdgesAt_le` — the active edges at
  a vertex inject into the box `B_{⌈r⌉}`, so there are at most `(2⌈r⌉₊+1)^d` of them;
* `sum_activeWeight_incident_le` — the per-vertex weight bound for the cut-off
  edge weight `γ 1(‖e‖ ≤ r)`;
* `tsum_touchSet_le` — for any nonnegative edge weight `w` with per-vertex bound
  `∑_{e ∈ u} w e 1(x ∈ e) ≤ D` on every finite set `u` of edges, the total weight
  of the edges touching a finite vertex set `S` is at most `D * |S|`.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace FiniteVolume

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The `‖·‖_∞`-length of an unordered pair of lattice points, as a natural number. -/
noncomputable def edgeLen (e : Sym2 (Fin d → ℤ)) : ℕ :=
  Sym2.lift ⟨fun x y => linfNorm (x - y), by
    intro x y
    show linfNorm (x - y) = linfNorm (y - x)
    rw [show y - x = -(x - y) by abel, linfNorm_neg]⟩ e

theorem edgeLen_mk (x y : Fin d → ℤ) : edgeLen s(x, y) = linfNorm (x - y) := rfl

/-- If the edge `e` is incident to `x` then it is `s(x, y)` for some `y`, and its length is the
sup-norm distance from `x` to `y`. -/
theorem exists_eq_mk_of_mem {x : Fin d → ℤ} {e : Sym2 (Fin d → ℤ)} (hx : x ∈ e) :
    ∃ y, e = s(x, y) ∧ edgeLen e = linfNorm (x - y) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨b, rfl, rfl⟩
    · refine ⟨a, ?_, ?_⟩
      · rw [Sym2.eq_swap]
      · rw [edgeLen_mk, show a - x = -(x - a) by abel, linfNorm_neg]

/-- The active edges at a vertex are contained in the image of the box of radius `⌈r⌉₊` under
`z ↦ s(x, x + z)`. -/
theorem activeEdges_subset_image_box (x : Fin d → ℤ) (r : ℝ) :
    {e : Sym2 (Fin d → ℤ) | x ∈ e ∧ (edgeLen e : ℝ) ≤ r}
      ⊆ ((box d ⌈r⌉₊).image fun z => s(x, x + z) : Finset (Sym2 (Fin d → ℤ))) := by
  intro e he
  obtain ⟨he1, he2⟩ := he
  obtain ⟨y, rfl, hlen⟩ := exists_eq_mk_of_mem he1
  have hz : y - x ∈ box d ⌈r⌉₊ := by
    rw [mem_box_iff]
    have h3 : (linfNorm (y - x) : ℝ) ≤ r := by
      rw [show y - x = -(x - y) by abel, linfNorm_neg, ← hlen]
      exact he2
    have h2 : (linfNorm (y - x) : ℝ) ≤ (⌈r⌉₊ : ℝ) := h3.trans (Nat.le_ceil r)
    exact_mod_cast h2
  refine Finset.mem_image.mpr ⟨y - x, hz, ?_⟩
  rw [show x + (y - x) = y by abel]

/-- **The degree bound of the cut-off graph**: a vertex is incident to at most
`(2⌈r⌉₊ + 1)^d` edges of length at most `r`. -/
theorem card_activeEdgesAt_le (x : Fin d → ℤ) (r : ℝ) :
    {e : Sym2 (Fin d → ℤ) | x ∈ e ∧ (edgeLen e : ℝ) ≤ r}.Finite ∧
      {e : Sym2 (Fin d → ℤ) | x ∈ e ∧ (edgeLen e : ℝ) ≤ r}.ncard
        ≤ (2 * ⌈r⌉₊ + 1) ^ d := by
  have hsub := activeEdges_subset_image_box (d := d) x r
  have hfin : {e : Sym2 (Fin d → ℤ) | x ∈ e ∧ (edgeLen e : ℝ) ≤ r}.Finite :=
    (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
  rw [Set.ncard_coe_finset]
  exact le_trans Finset.card_image_le (le_of_eq (card_box ⌈r⌉₊))

/-- **Per-vertex weight bound.**  The cut-off edge weight `γ 1(‖e‖ ≤ r)` has total mass at most
`γ (2⌈r⌉₊+1)^d` at any vertex, uniformly over all finite sets of edges. -/
theorem sum_activeWeight_incident_le (x : Fin d → ℤ) (r γ : ℝ) (hγ : 0 ≤ γ)
    (u : Finset (Sym2 (Fin d → ℤ))) :
    ∑ e ∈ u, γ * (if (edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0)
        * (if x ∈ e then (1 : ℝ) else 0)
      ≤ γ * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ) := by
  classical
  set A : Finset (Sym2 (Fin d → ℤ)) := (box d ⌈r⌉₊).image fun z => s(x, x + z) with hAdef
  have hsub : ∀ e ∈ u, (edgeLen e : ℝ) ≤ r → x ∈ e → e ∈ A := by
    intro e _ he1 he2
    exact activeEdges_subset_image_box x r ⟨he2, he1⟩
  have hterm : ∀ e ∈ u,
      γ * (if (edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0) * (if x ∈ e then (1 : ℝ) else 0)
        ≤ γ * (if e ∈ A then (1 : ℝ) else 0) := by
    intro e heu
    by_cases h : (edgeLen e : ℝ) ≤ r ∧ x ∈ e
    · rw [ite_eq_left h.1, ite_eq_left h.2, ite_eq_left (hsub e heu h.1 h.2), mul_one, mul_one]
    · have h0 : γ * (if (edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0)
          * (if x ∈ e then (1 : ℝ) else 0) = 0 := by
        rcases not_and_or.mp h with h' | h'
        · rw [ite_eq_right h', mul_zero, zero_mul]
        · rw [ite_eq_right h', mul_zero]
      rw [h0]
      have hP : (0 : ℝ) ≤ (if e ∈ A then (1 : ℝ) else 0) := by split <;> norm_num
      exact mul_nonneg hγ hP
  have hcalc : ∑ e ∈ u, γ * (if e ∈ A then (1 : ℝ) else 0)
      = γ * ((u.filter (fun e => e ∈ A)).card : ℝ) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ e ∈ u, γ * (if (edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0)
        * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, γ * (if e ∈ A then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
    _ = γ * ((u.filter (fun e => e ∈ A)).card : ℝ) := hcalc
    _ ≤ γ * (A.card : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hγ
        have hle : (u.filter (fun e => e ∈ A)).card ≤ A.card :=
          Finset.card_le_card (fun e he => (Finset.mem_filter.mp he).2)
        exact_mod_cast hle
    _ ≤ γ * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ) := by
        refine mul_le_mul_of_nonneg_left ?_ hγ
        have hle : ((A.card : ℕ) : ℝ) ≤ (((2 * ⌈r⌉₊ + 1) ^ d : ℕ) : ℝ) := by
          have h1 : A.card ≤ (2 * ⌈r⌉₊ + 1) ^ d := by
            rw [hAdef]
            exact le_trans Finset.card_image_le (le_of_eq (card_box ⌈r⌉₊))
          exact_mod_cast h1
        exact hle

/-- **The touching-set weight bound (finite sums).**  A nonnegative edge weight whose total mass
at each vertex is at most `D` (uniformly over finite sets of edges) has total mass at most
`D * |S|` on the set of edges touching the finite vertex set `S`. -/
theorem sum_touchSet_le {V : Type*} [Countable V] (w : Sym2 V → ℝ) (D : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (S : Finset V) (u : Finset (Sym2 V)) :
    ∑ e ∈ u, w e * (if ∃ x ∈ S, x ∈ e then (1 : ℝ) else 0) ≤ D * S.card := by
  classical
  have hstep : ∑ e ∈ u, w e * (if ∃ x ∈ S, x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, w e * ∑ x ∈ S, (if x ∈ e then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun e _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hw e)
    by_cases h : ∃ x ∈ S, x ∈ e
    · rw [ite_eq_left h]
      obtain ⟨x, hxS, hxe⟩ := h
      have h2 := Finset.single_le_sum (f := fun x => if x ∈ e then (1 : ℝ) else 0)
        (fun i _ => by positivity) hxS
      simpa [hxe] using h2
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun i _ => by positivity
  have hswap : ∑ e ∈ u, w e * ∑ x ∈ S, (if x ∈ e then (1 : ℝ) else 0)
      = ∑ x ∈ S, ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  calc ∑ e ∈ u, w e * (if ∃ x ∈ S, x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ x ∈ S, ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0) := hstep.trans_eq hswap
    _ ≤ ∑ _x ∈ S, D := Finset.sum_le_sum fun x _ => hdeg x u
    _ = D * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The touching-set weight bound.**  A nonnegative edge weight whose total mass at each vertex
is at most `D` (uniformly over finite sets of edges) has total mass at most `D * |S|` on the set
of edges touching the finite vertex set `S`. -/
theorem tsum_touchSet_le {V : Type*} [Countable V] (w : Sym2 V → ℝ) (D : ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (S : Finset V) :
    ∑' e : Sym2 V, w e * (if ∃ x ∈ S, x ∈ e then (1 : ℝ) else 0) ≤ D * S.card := by
  classical
  refine Real.tsum_le_of_sum_le (fun e => mul_nonneg (hw e) (by positivity)) fun u => ?_
  exact sum_touchSet_le w D hw hdeg S u

end FiniteVolume

end PercLib.CriticalLRP
