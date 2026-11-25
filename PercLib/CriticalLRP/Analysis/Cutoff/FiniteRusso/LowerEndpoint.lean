/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

The trivial (lower) endpoint of the interval: at a cut-off radius not exceeding the norm-length of
every edge of the finite edge set, no edge is switched on, the law is concentrated on the empty
configuration, and the `p`-th anchored cluster moment equals `1`.  This is the concrete form of the
"the lower endpoint never cuts" half of the boundary convention.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.OffCorner

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With no open edge the anchored cluster of `u` is the singleton `{u}`. -/
theorem cluster_empty (s t : E → V) (u : V) : cluster s t (∅ : Configuration E) u = {u} := by
  classical
  ext v
  rw [mem_cluster, Finset.mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc _ =>
        obtain ⟨e, he, _⟩ := hbc
        exact absurd he (notMem_empty e)
  · intro h
    rw [h]
    exact conn_refl s t ∅ u

/-- Under the all-closed law the expectation is the observable at the empty configuration. -/
theorem expectation_zero_param (X : Configuration E → ℝ) :
    expectation (fun _ => (0 : ℝ)) X = X ∅ := by
  classical
  have hlaw : ∀ s : Configuration E, configurationLaw (fun _ => (0 : ℝ)) s
      = if s = ∅ then 1 else 0 := by
    intro s
    rw [configurationLaw]
    by_cases hs : s = ∅
    · subst hs; simp
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      rw [ite_eq_right hs]
      exact Finset.prod_eq_zero (mem_univ e) (by simp [he])
  rw [expectation, Finset.sum_congr rfl (fun s _ => by rw [hlaw s])]
  simp

/-- **Lower endpoint.**  If the cut-off radius does not exceed the norm-length of any edge of the
finite edge set, the `p`-th anchored cutoff cluster moment equals `1`: the finite cluster is the
single vertex `x`. -/
theorem cutoffMoment_lower_endpoint {K : ℝ → ℝ} {β : ℝ} {len : E → ℝ} {s t : E → V} {x : V}
    {p : ℕ} {r : ℝ} (h : ∀ e, r ≤ len e) :
    cutoffMoment K β len s t x p r = 1 := by
  have hp : cutoffParam K β len r = fun _ => (0 : ℝ) :=
    funext fun e => cutoffParam_eq_zero_of_le e (h e)
  unfold cutoffMoment
  rw [hp, expectation_zero_param, clusterMoment, cluster_empty]
  simp

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
