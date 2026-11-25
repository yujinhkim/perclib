/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lemma I.4.1 of Hutchcroft, "Critical long-range percolation I",
arXiv:2508.18807v1, in finite volume.

The paper's Lemma I.4.1 asserts

  ∂/∂r E_{β,r}|K|^p = β|J'(r)| ∑_{ℓ=0}^{p−1} binom(p,ℓ)
      E_{β,r}[ |K|^{ℓ+1} ∑_{y∈B_r} 1(y ∉ K) |K_y|^{p−ℓ} ],

and its proof proceeds in three steps:

1. Russo's formula in the form
   `∂/∂r E_{β,r} X = β|J'(r)| E_{β,r}[∑_{x∈K}∑_{y∈B_r(x)} 1(y ∉ K)
        (X(ω with {x,y} open) − X(ω))]`
   with the bare `β|J'(r)|` — proved in `CutoffRusso`;
2. the mass-transport principle, replacing `∑_{x∈K}` by `|K| ∑_{y∈B_r}`;
3. expanding `(|K| + |K_y|)^p − |K|^p` binomially — proved in `MomentExpansion`.

In finite volume, step 1 is `hasDerivAt_expectation_cutoff`. This file supplies
what step 1 needs about the integrand for `X = |K|^p`: flipping the edge `e`
changes `|K|` to `|K| + |K_{t e}|` when exactly the `s e`-endpoint of `e` lies
in `K`, and leaves `|K|` unchanged otherwise. Step 2 is a statement about the
translation-invariant infinite-lattice measure and is not available in finite
volume; see the accompanying notes file.
-/
module

public import PercLib.CriticalLRP.CutoffRusso
public import PercLib.CriticalLRP.FiniteGraphCluster
public import PercLib.CriticalLRP.MomentExpansion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The cluster volume of the origin, as a real number. -/
noncomputable def clusterVol (s t : E → V) (o : V) (ω : Finset E) : ℝ :=
  ((cluster s t ω o).card : ℝ)

/-- Case `s e ∈ K`, `t e ∉ K` of the flip: the two clusters merge. -/
theorem clusterVol_insert_of_mem_not_mem {s t : E → V} {o : V} {e : E} {ω : Finset E}
    (h1 : Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    clusterVol s t o (insert e ω) = clusterVol s t o ω + clusterVol s t (t e) ω := by
  classical
  have hst : ¬ Conn s t ω (s e) (t e) := fun h => h2 (h1.trans h)
  have hcongr : cluster s t (insert e ω) o = cluster s t (insert e ω) (s e) :=
    cluster_eq_of_conn (conn_mono (subset_insert e ω) h1)
  have hc : cluster s t ω (s e) = cluster s t ω o := (cluster_eq_of_conn h1).symm
  unfold clusterVol
  rw [hcongr, card_cluster_insert_of_not_conn hst, hc]
  push_cast
  ring

/-- Case `t e ∈ K`, `s e ∉ K` of the flip: the two clusters merge. -/
theorem clusterVol_insert_of_not_mem_mem {s t : E → V} {o : V} {e : E} {ω : Finset E}
    (h1 : ¬ Conn s t ω o (s e)) (h2 : Conn s t ω o (t e)) :
    clusterVol s t o (insert e ω) = clusterVol s t o ω + clusterVol s t (s e) ω := by
  classical
  have hst : ¬ Conn s t ω (s e) (t e) := fun h => h1 (h2.trans (conn_symm h))
  have hcongr : cluster s t (insert e ω) o = cluster s t (insert e ω) (t e) :=
    cluster_eq_of_conn (conn_mono (subset_insert e ω) h2)
  have hc : cluster s t ω (t e) = cluster s t ω o := (cluster_eq_of_conn h2).symm
  unfold clusterVol
  rw [hcongr, card_cluster_insert_right hst, hc]
  push_cast
  ring

/-- Case `s e ∈ K`, `t e ∈ K`: the flip changes nothing. -/
theorem clusterVol_insert_of_mem_mem {s t : E → V} {o : V} {e : E} {ω : Finset E}
    (h1 : Conn s t ω o (s e)) (h2 : Conn s t ω o (t e)) :
    clusterVol s t o (insert e ω) = clusterVol s t o ω := by
  classical
  unfold clusterVol
  rw [cluster_insert_of_conn ((conn_symm h1).trans h2) o]

/-- Case `s e ∉ K`, `t e ∉ K`: the flip changes nothing. -/
theorem clusterVol_insert_of_not_mem_not_mem {s t : E → V} {o : V} {e : E} {ω : Finset E}
    (h1 : ¬ Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    clusterVol s t o (insert e ω) = clusterVol s t o ω := by
  classical
  unfold clusterVol
  rw [cluster_insert_of_not_conn_both h1 h2]

/-- **The flip difference `|K|^p` in the four cases**, exhaustively. -/
theorem clusterVol_pow_flip_cases {s t : E → V} {o : V} {e : E} {ω : Finset E} (p : ℕ) :
    ((Conn s t ω o (s e) ∧ ¬ Conn s t ω o (t e)) ∧
        (clusterVol s t o (insert e ω) ^ p - clusterVol s t o ω ^ p
          = (clusterVol s t o ω + clusterVol s t (t e) ω) ^ p - clusterVol s t o ω ^ p))
    ∨ ((¬ Conn s t ω o (s e) ∧ Conn s t ω o (t e)) ∧
        (clusterVol s t o (insert e ω) ^ p - clusterVol s t o ω ^ p
          = (clusterVol s t o ω + clusterVol s t (s e) ω) ^ p - clusterVol s t o ω ^ p))
    ∨ (Conn s t ω o (s e) ∧ Conn s t ω o (t e) ∧
        clusterVol s t o (insert e ω) ^ p - clusterVol s t o ω ^ p = 0)
    ∨ (¬ Conn s t ω o (s e) ∧ ¬ Conn s t ω o (t e) ∧
        clusterVol s t o (insert e ω) ^ p - clusterVol s t o ω ^ p = 0) := by
  classical
  by_cases h1 : Conn s t ω o (s e) <;> by_cases h2 : Conn s t ω o (t e)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, by
      rw [clusterVol_insert_of_mem_mem h1 h2]; ring⟩))
  · exact Or.inl ⟨⟨h1, h2⟩, by rw [clusterVol_insert_of_mem_not_mem h1 h2]⟩
  · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, by rw [clusterVol_insert_of_not_mem_mem h1 h2]⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, by
      rw [clusterVol_insert_of_not_mem_not_mem h1 h2]; ring⟩))

/-- **The binomial form of the merged case**, matching the paper's display
(I.4.1): after multiplication by `|K|` (which the mass-transport step supplies),
the flip difference is `∑_{ℓ<p} binom(p,ℓ) |K|^{ℓ+1} |K_y|^{p−ℓ}`. -/
theorem clusterVol_pow_flip_binomial {s t : E → V} {o : V} {e : E} {ω : Finset E} (p : ℕ)
    (h1 : Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    clusterVol s t o ω
        * (clusterVol s t o (insert e ω) ^ p - clusterVol s t o ω ^ p)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * clusterVol s t o ω ^ (ℓ + 1)
          * clusterVol s t (t e) ω ^ (p - ℓ) := by
  rw [clusterVol_insert_of_mem_not_mem h1 h2]
  exact mul_pow_sub_pow_eq_sum_choose _ _ p

/-- **Lemma I.4.1 in finite volume, step 1**: the `r`-derivative of the `p`-th
cluster-volume moment in the cut-off model, with the paper's constant
`β|J'(r)|` and the flip differences of `clusterVol_pow_flip_cases`. -/
theorem hasDerivAt_expectation_clusterVol_pow
    (s t : E → V) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ) {r β : ℝ} (p : ℕ)
    (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (fun ω => clusterVol s t o ω ^ p))
      (β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (clusterVol s t o (insert e τ) ^ p - clusterVol s t o τ ^ p)) r :=
  hasDerivAt_expectation_cutoff len K K' hne hK (fun ω => clusterVol s t o ω ^ p)

end PercLib.CriticalLRP.FiniteVolume
