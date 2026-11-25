/-
New applications of mathlib's first Borel–Cantelli lemma and graph-walk API at
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream percolation theorem is assumed.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # Almost-sure local finiteness

Finite off-diagonal row sums imply finite open neighbor sets almost surely.
Applying this simultaneously at all vertices gives finite graph-distance balls.
There is no subcriticality assumption or assertion that the clusters are finite.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace SimpleGraph

variable {V : Type*}

/-- Finite neighbor sets imply finiteness of every bounded-length reachability set. -/
theorem finite_setOf_exists_walk_length_le (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).Finite) (n : ℕ) (v : V) :
    {w | ∃ p : G.Walk v w, p.length ≤ n}.Finite := by
  induction n generalizing v with
  | zero =>
    apply (Set.finite_singleton v).subset
    rintro w ⟨p, hp⟩
    cases p with
    | nil => rfl
    | cons h p => simp at hp
  | succ n ih =>
    apply ((Set.finite_singleton v).union ((hG v).biUnion fun w _ => ih w)).subset
    rintro w ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | cons h p =>
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨h, ⟨p, by simpa using hp⟩⟩⟩

/-- Finite-radius balls in the extended graph metric are finite in a locally finite graph.
Using `edist` excludes disconnected vertices, whose natural-valued `dist` is zero. -/
theorem finite_ball_of_finite_neighborSet (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).Finite) (n : ℕ) (v : V) :
    (G.ball v n).Finite := by
  apply (finite_setOf_exists_walk_length_le G hG n v).subset
  intro w hw
  have hd : G.edist v w < (n : ℕ∞) := by
    change G.edist w v < (n : ℕ∞) at hw
    rwa [G.edist_comm] at hw
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top (ne_top_of_lt hd)
  refine ⟨p, ?_⟩
  have : (p.length : ℕ∞) < n := hp ▸ hd
  exact Nat.le_of_lt (by exact_mod_cast this)

end SimpleGraph

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*} [Countable V]

/-- A finite off-diagonal row sum gives a finite neighbor set almost surely at one vertex. -/
theorem ae_finite_neighbors_of_rowSum_lt_top (q : Sym2 V → unitInterval) (v : V)
    (hrow : (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) < ∞) :
    ∀ᵐ ω ∂law q, ((openGraph ω).neighborSet v).Finite := by
  have hm (w : V) : law q {ω | (openGraph ω).Adj v w} =
      if w = v then 0 else (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) := by
    by_cases h : w = v
    · subst w
      simp
    · simpa [law, openGraph_adj_iff, h, Ne.symm h] using
        prodBernoulli_setOf_mem q s(v, w)
  exact ae_finite_setOfPred_mem (μ := law q) (s := fun w => {ω | (openGraph ω).Adj v w})
    (by simpa only [hm] using ne_of_lt hrow)

/-- Finite row sums at every vertex give simultaneous almost-sure local finiteness. -/
theorem ae_all_finite_neighbors_of_rowSum_lt_top (q : Sym2 V → unitInterval)
    (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) < ∞) :
    ∀ᵐ ω ∂law q, ∀ v, ((openGraph ω).neighborSet v).Finite :=
  ae_all_iff.mpr fun v => ae_finite_neighbors_of_rowSum_lt_top q v (hrow v)

/-- Almost surely every finite-radius graph ball is finite; clusters may still be infinite. -/
theorem ae_finite_balls_of_rowSum_lt_top (q : Sym2 V → unitInterval)
    (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) < ∞) :
    ∀ᵐ ω ∂law q, ∀ (v : V) (n : ℕ), ((openGraph ω).ball v n).Finite := by
  filter_upwards [ae_all_finite_neighbors_of_rowSum_lt_top q hrow] with ω hω
  exact fun v n => (openGraph ω).finite_ball_of_finite_neighborSet hω n v

-- Boundary and non-vacuity witnesses. The first row sum is exactly one,
-- so no subcritical row bound is hidden in the result.
example : ∀ᵐ ω ∂law (fun _ : Sym2 Bool => 1),
    ∀ (v : Bool) (n : ℕ), ((openGraph ω).ball v n).Finite := by
  apply ae_finite_balls_of_rowSum_lt_top
  intro v
  cases v <;> simp [tsum_fintype]

-- Infinitely many diagonal coordinates may be always open; none counts as a neighbor.
example : ∀ᵐ ω ∂law (fun e : Sym2 ℕ => if e.IsDiag then 1 else 0),
    ∀ v, ((openGraph ω).neighborSet v).Finite := by
  apply ae_all_finite_neighbors_of_rowSum_lt_top
  intro v
  calc
    _ = ∑' _ : ℕ, (0 : ℝ≥0∞) := by
      apply tsum_congr
      intro w
      by_cases hw : w = v
      · subst w; simp
      · simp [hw, Ne.symm hw, Sym2.mk_isDiag_iff]
    _ < ∞ := by simp

end PercLib.Percolation.Bond
