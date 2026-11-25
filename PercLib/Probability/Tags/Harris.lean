/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PercLib.Probability.OpenEventHarris

/-! The grouped connection and escape corollary in the Harris article.
The increasing-event and observable notions are mathlib's `IsUpperSet` and `Monotone`;
no replacement definitions are introduced here. -/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Three-point association, escape-event regularity, and the infinite-cluster
intersection characterization and regularity, as grouped in the Harris article. -/
@[tag "UPFU"] theorem harris_connection_escape [Countable V]
    (q : Sym2 V → unitInterval) (x y z : V) :
    tau q x y * tau q y z ≤ tau q x z ∧
    (∀ S : Set V, IsUpperSet (⋃ v ∈ Sᶜ, conn x v : Set (Config V)) ∧
      MeasurableSet (⋃ v ∈ Sᶜ, conn x v : Set (Config V))) ∧
    {ω : Config V | (cluster ω x).Infinite} =
      (⋂ F : Finset V, ⋃ v ∈ (↑F : Set V)ᶜ, conn x v) ∧
    IsUpperSet {ω : Config V | (cluster ω x).Infinite} ∧
    MeasurableSet {ω : Config V | (cluster ω x).Infinite} :=
  ⟨tau_mul_tau_le q x y z, fun S => ⟨isUpperSet_escape x S, measurableSet_escape x S⟩,
    cluster_infinite_eq_iInter x, isUpperSet_cluster_infinite x,
    measurableSet_cluster_infinite x⟩

end PercLib.Percolation.Bond

section Witnesses
open PercLib.Probability PercLib.Percolation.Bond

/-- The empty finite family has both sides equal to one. -/
example (q : ℕ → unitInterval) (A : ℕ → Set (Set ℕ)) :
    (∏ a ∈ (∅ : Finset ℕ), prodBernoulli q (A a)) = 1 ∧
      prodBernoulli q (⋂ a ∈ (∅ : Finset ℕ), A a) = 1 := by simp

/-- Repeated vertices and both endpoint profiles are admitted. -/
example (q : Sym2 ℕ → unitInterval) : tau q 0 0 * tau q 0 0 ≤ tau q 0 0 :=
  (harris_connection_escape q 0 0 0).1

example : tau (fun _ : Sym2 ℕ => 0) 0 1 * tau (fun _ => 0) 1 2 ≤
    tau (fun _ => 0) 0 2 := (harris_connection_escape (fun _ => 0) 0 1 2).1

example : tau (fun _ : Sym2 ℕ => 1) 0 1 * tau (fun _ => 1) 1 2 ≤
    tau (fun _ => 1) 0 2 := (harris_connection_escape (fun _ => 1) 0 1 2).1

end Witnesses
