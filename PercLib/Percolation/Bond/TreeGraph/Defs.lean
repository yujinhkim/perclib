/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-49: the three-point Aizenman–Newman tree-graph target on the D-2 interface.
The full inequality is a target, not an assumed theorem. Its BK-dependent proof
belongs to a later package. The elementary witnesses below are new proofs.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

/-- The three-point tree-graph inequality for independent bond percolation.
The profile is arbitrary, including its diagonal, and the sum may be infinite.
This declaration records a proposition to prove, without asserting its truth. -/
@[tag "L82Q"]
def TreeGraphInequality (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (x y z : V),
    law q (conn x y ∩ conn x z) ≤ ∑' w, tau q x w * tau q w y * tau q w z

/-- The repeated-root case is already a consequence of the w=x summand. -/
theorem treeGraph_le_of_middle_eq_root {V : Type*} (q : Sym2 V → unitInterval) (x z : V) :
    law q (conn x x ∩ conn x z) ≤ ∑' w, tau q x w * tau q w x * tau q w z := by
  simpa [conn_self, tau_self, tau] using
    (ENNReal.le_tsum (f := fun w => tau q x w * tau q w x * tau q w z) x)

/-- On two vertices, connection is exactly the single off-diagonal cylinder. -/
private theorem conn_bool_eq : (conn false true : Set (Config Bool)) = {ω | s(false,true) ∈ ω} := by
  ext ω
  constructor
  · rintro ⟨r⟩
    cases r with
    | @cons a b c hab r =>
      cases b
      · exact ((openGraph_adj_iff ω false false).mp hab).2 rfl |>.elim
      · exact ((openGraph_adj_iff ω false true).mp hab).1
  · exact mem_conn_of_mem (by decide)

/-- Exact two-vertex witness: the joint connection probability is t and the
three-point diagram is t²+t. Diagonal probabilities remain arbitrary. -/
theorem treeGraph_bool_values (q : Sym2 Bool → unitInterval) :
    law q (conn false true ∩ conn false true) =
      (unitInterval.toNNReal (q s(false,true)) : ℝ≥0∞) ∧
    (∑' w, tau q false w * tau q w true * tau q w true) =
      (unitInterval.toNNReal (q s(false,true)) : ℝ≥0∞)^2 +
        (unitInterval.toNNReal (q s(false,true)) : ℝ≥0∞) := by
  have ht : tau q false true = (unitInterval.toNNReal (q s(false,true)) : ℝ≥0∞) := by
    rw [tau, conn_bool_eq]
    exact prodBernoulli_setOf_mem q _
  constructor
  · simpa only [Set.inter_self, tau] using ht
  · simp only [tsum_fintype, Fintype.sum_bool, tau_self, ht, one_mul, mul_one]
    ring

example {V : Type*} (q : Sym2 V → unitInterval) (x z : V) :
    law q (conn x x ∩ conn x z) ≤ ∑' w, tau q x w * tau q w x * tau q w z :=
  treeGraph_le_of_middle_eq_root q x z

example (q : Sym2 Bool → unitInterval) :
    law q (conn false true ∩ conn false true) ≤
      ∑' w, tau q false w * tau q w true * tau q w true := by
  rw [(treeGraph_bool_values q).1, (treeGraph_bool_values q).2]
  exact le_add_left le_rfl

end PercLib.Percolation.Bond
