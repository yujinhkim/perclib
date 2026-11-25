/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

The binomial weight identity that turns a pivotal (single-edge flip) increment of the `p`-th
cluster moment into the paper's `ℓ`-sum, and the monotonicity of the anchored cluster moment
that makes the pivotal mass nonnegative.

This is where the off-corner binomial structure of Lemma I.4.1 lives: when the flipped edge
merges the cluster of `x` with a *disjoint* cluster of size `B`, the `p`-th moment changes by
`∑_{ℓ<p} C(p,ℓ) A^ℓ B^{p-ℓ}` with `A` the old cluster size.  No derivative, no radius and no
corner is involved: the identity is pointwise in the configuration.

Reference: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Lemma I.4.1 (the `ℓ`-sum and binomial coefficient step).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Increment

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The binomial weight identity -/

/-- **Binomial weight identity.**  The increment of the `p`-th power when a disjoint cluster of
size `b` is merged into a cluster of size `a` is the paper's `ℓ`-sum, with `ℓ` running from `0`
to `p - 1`. -/
theorem add_pow_sub_pow (a b : ℝ) (p : ℕ) :
    (a + b) ^ p - a ^ p
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ) := by
  rw [add_pow]
  rw [sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_sub_cancel_right]
  exact sum_congr rfl fun ℓ _ => by ring

/-- The `ℕ`-valued form, for cluster cardinalities. -/
theorem add_pow_sub_pow_nat (a b p : ℕ) :
    ((a + b : ℕ) : ℝ) ^ p - (a : ℝ) ^ p
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * (a : ℝ) ^ ℓ * (b : ℝ) ^ (p - ℓ) := by
  have h : ((a : ℝ) + (b : ℝ)) = ((a + b : ℕ) : ℝ) := by push_cast; ring
  rw [← h]
  exact add_pow_sub_pow (a : ℝ) (b : ℝ) p

/-! ### Monotonicity of the anchored cluster in the configuration -/

theorem cluster_subset_of_subset {s t : E → V} {ω ω' : Configuration E} (h : ω ⊆ ω') (u : V) :
    cluster s t ω u ⊆ cluster s t ω' u := by
  intro v hv
  rw [mem_cluster] at hv ⊢
  exact conn_mono h hv

theorem cluster_card_mono {s t : E → V} {ω ω' : Configuration E} (h : ω ⊆ ω') (u : V) :
    (cluster s t ω u).card ≤ (cluster s t ω' u).card :=
  Finset.card_le_card (cluster_subset_of_subset h u)

/-- The anchored `p`-th cluster moment is a monotone function of the open-edge configuration:
this is what makes the pivotal mass, and hence the incremental Russo flux, nonnegative. -/
theorem clusterMoment_mono (s t : E → V) (x : V) (p : ℕ) :
    Monotone (clusterMoment s t x p) := by
  intro ω ω' h
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast cluster_card_mono h x) p

/-! ### The cluster identity for a flip -/

/-- Opening an edge that merges two disjoint clusters grows the anchored cluster of `x` to the
union when `x` sits in the first of them, hence adds the second cluster's cardinality. -/
theorem card_cluster_insert_left {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (hxy : ¬ Conn s t ω (s e) (t e)) (hx : Conn s t ω x (s e)) :
    (cluster s t (insert e ω) x).card
      = (cluster s t ω (s e)).card + (cluster s t ω (t e)).card := by
  have hx' : Conn s t (insert e ω) x (s e) := conn_mono (subset_insert e ω) hx
  rw [cluster_eq_of_conn hx', card_cluster_insert_of_not_conn hxy]

/-- The symmetric statement, for `x` in the cluster of the second endpoint. -/
theorem card_cluster_insert_right_of_conn {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (hxy : ¬ Conn s t ω (s e) (t e)) (hx : Conn s t ω x (t e)) :
    (cluster s t (insert e ω) x).card
      = (cluster s t ω (t e)).card + (cluster s t ω (s e)).card := by
  have hx' : Conn s t (insert e ω) x (t e) := conn_mono (subset_insert e ω) hx
  rw [cluster_eq_of_conn hx', card_cluster_insert_right hxy]

/-- **Pointwise binomial weight of a flip, anchored case.**  If the flipped edge merges the
cluster of `x` with a disjoint cluster of size `B`, the increment of the `p`-th moment is the
`ℓ`-sum of Lemma I.4.1 with `A` the old cluster size. -/
theorem clusterMoment_flip_eq_sum {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (p : ℕ) (hxy : ¬ Conn s t ω (s e) (t e)) (hx : Conn s t ω x (s e)) :
    clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ ℓ
          * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ) := by
  have hold : (cluster s t ω x).card = (cluster s t ω (s e)).card := by
    rw [cluster_eq_of_conn hx]
  unfold clusterMoment
  rw [card_cluster_insert_left hxy hx, hold, add_pow_sub_pow_nat]

/-- If the endpoints of the flipped edge are already connected, the anchored moment does not
change. -/
theorem clusterMoment_flip_eq_zero_of_conn {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (p : ℕ) (hxy : Conn s t ω (s e) (t e)) :
    clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω = 0 := by
  unfold clusterMoment
  rw [cluster_insert_of_conn hxy]
  ring

/-- If `x` is connected to neither endpoint of the flipped edge, the anchored moment does not
change either. -/
theorem clusterMoment_flip_eq_zero_of_not_conn_both {s t : E → V} {e : E} {ω : Configuration E}
    {x : V} (p : ℕ) (h1 : ¬ Conn s t ω x (s e)) (h2 : ¬ Conn s t ω x (t e)) :
    clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω = 0 := by
  unfold clusterMoment
  rw [cluster_insert_of_not_conn_both h1 h2]
  ring

/-- The mirrored binomial weight identity: if `x` lies in the cluster of the *second* endpoint,
the merged cluster has size `B + A` and the increment is the `ℓ`-sum with the two clusters
interchanged. -/
theorem clusterMoment_flip_eq_sum_right {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (p : ℕ) (hxy : ¬ Conn s t ω (s e) (t e)) (hx : Conn s t ω x (t e)) :
    clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t ω (t e)).card : ℝ) ^ ℓ
          * ((cluster s t ω (s e)).card : ℝ) ^ (p - ℓ) := by
  classical
  have hold : (cluster s t ω x).card = (cluster s t ω (t e)).card := by
    rw [cluster_eq_of_conn hx]
  unfold clusterMoment
  rw [card_cluster_insert_right_of_conn hxy hx, hold]
  exact add_pow_sub_pow_nat _ _ _

/-- **Pointwise decomposition of a flip into the two binomial weights.**  This is the exact
per-configuration form of the `ℓ`-sum in Lemma I.4.1: the flip changes the anchored moment only
when it merges the anchored cluster with a disjoint one, and then by the binomial weight. -/
theorem clusterMoment_flip_eq_left_add_right {s t : E → V} {e : E} {ω : Configuration E} {x : V}
    (p : ℕ) :
    clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω
      = leftWeight s t x p e ω + rightWeight s t x p e ω := by
  classical
  unfold leftWeight rightWeight
  by_cases hxy : Conn s t ω (s e) (t e)
  · rw [clusterMoment_flip_eq_zero_of_conn p hxy]
    rw [ite_eq_right (fun h => h.1 hxy), ite_eq_right (fun h => h.1 hxy)]
    ring
  · by_cases hx : Conn s t ω x (s e)
    · have hy : ¬ Conn s t ω x (t e) := by
        intro hy
        exact hxy ((conn_symm hx).trans hy)
      rw [clusterMoment_flip_eq_sum p hxy hx]
      rw [ite_eq_left ⟨hxy, hx⟩, ite_eq_right (fun h => hy h.2)]
      ring
    · by_cases hy : Conn s t ω x (t e)
      · rw [clusterMoment_flip_eq_sum_right p hxy hy]
        rw [ite_eq_right (fun h => hx h.2), ite_eq_left ⟨hxy, hy⟩]
        ring
      · rw [clusterMoment_flip_eq_zero_of_not_conn_both p hx hy]
        rw [ite_eq_right (fun h => hx h.2), ite_eq_right (fun h => hy h.2)]
        ring

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
