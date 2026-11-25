module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
# Definitions for the mixed incident-edge transport

Direction (activity 4) of swarm `smwtzmkep`, member `m5`.

The coupled events of the per-edge standardised bound, and the two weight functionals used to state
the vertex-degree hypothesis of the finite incident transport:

* `evEdge e` — `{y ∈ K_0} ∩ {e touches K_0}`;
* `evVert x` — `{x ∈ K_0} ∩ {y ∈ K_0}`;
* `vertexWeight w x u` — the weight of a finite edge set `u` at a vertex `x`, i.e. the degree form
  used by `FiniteVolume.sum_touchSet_weight_le`, fixed once here so that the decidability witness
  does not depend on the elaboration context;
* `incidentWeight w x` — the full incident series at `x`, the intended `D_std` per-vertex
  quantity.

Compiled before `Incident/Transport.lean`; no theorem of the transport is used here.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false


@[expose] public section


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The edge-weight mass at a vertex `x`, summed over a finite edge set `u`.  This is the `if`-form
of the vertex-degree bound, packaged as a definition so that the statement is stable across
elaboration contexts (the decidability witness is fixed once, at this definition). -/
def vertexWeight {V : Type*} (w : Sym2 V → ℝ) (x : V) (u : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0)

theorem vertexWeight_eq_sum {V : Type*} (w : Sym2 V → ℝ) (x : V) (u : Finset (Sym2 V)) :
    vertexWeight w x u = ∑ e ∈ u, w e * (if x ∈ e then (1 : ℝ) else 0) := rfl

/-- **The per-vertex incident weight.**  This is the intended `D_std`-type quantity: the total
standardised weight of the edges incident to a vertex, i.e. the incident-edge sum over a cluster
vertex. -/
noncomputable def incidentWeight {V : Type*} (w : Sym2 V → ℝ) (x : V) : ℝ :=
  ∑' e : Sym2 V, w e * (if x ∈ e then (1 : ℝ) else 0)

/-- A finite-set vertex bound is dominated by the incident series of that vertex. -/
theorem vertexWeight_le_incidentWeight {V : Type*} {w : Sym2 V → ℝ} (hw : ∀ e, 0 ≤ w e) {x : V}
    (hsum : Summable fun e : Sym2 V => w e * (if x ∈ e then (1 : ℝ) else 0))
    (u : Finset (Sym2 V)) :
    vertexWeight w x u ≤ incidentWeight w x := by
  rw [vertexWeight_eq_sum]
  exact hsum.sum_le_tsum u fun e _ => mul_nonneg (hw e) (by split <;> norm_num)

variable {V : Type*} [Countable V]

/-! ## 1. The pointwise finite-set bound -/

/-- `s.indicator (fun _ => 1) ω * t.indicator (fun _ => 1) ω` is the indicator of `s ∩ t`. -/
theorem indicator_mul_indicator_one' {α : Type*} (s t : Set α) (ω : α) :
    s.indicator (fun _ => (1 : ℝ)) ω * t.indicator (fun _ => (1 : ℝ)) ω
      = (s ∩ t).indicator (fun _ => (1 : ℝ)) ω := by
  by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, ht]

/-- The **coupled edge event**: `y` is in the cluster of `o` and the edge `e` touches it. -/
def evEdge {o y : V} (e : Sym2 V) : Set (Config V) :=
  {ω : Config V | y ∈ cluster ω o} ∩ {ω : Config V | e ∈ touchSet ω o}

/-- The **coupled vertex event**: `y` and `x` are both in the cluster of `o`. -/
def evVert {o y : V} (x : V) : Set (Config V) :=
  {ω : Config V | x ∈ cluster ω o} ∩ {ω : Config V | y ∈ cluster ω o}

theorem measurableSet_evEdge {o y : V} (e : Sym2 V) : MeasurableSet (evEdge (o := o) (y := y) e) :=
  (measurableSet_cluster_mem o y).inter (measurableSet_touchSet_mem e)

theorem measurableSet_evVert {o y : V} (x : V) : MeasurableSet (evVert (o := o) (y := y) x) :=
  (measurableSet_cluster_mem o x).inter (measurableSet_cluster_mem o y)

/-- The mean of the coupled edge integrand is the coupled edge measure. -/
theorem integral_evEdge {o y : V} (μ : Measure (Config V)) [IsFiniteMeasure μ] (e : Sym2 V) :
    ∫ ω, (if y ∈ cluster ω o then (1 : ℝ) else 0)
        * (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ
      = μ.real (evEdge (o := o) (y := y) e) := by
  have hcongr : ∀ ω : Config V, (if y ∈ cluster ω o then (1 : ℝ) else 0)
      * (if e ∈ touchSet ω o then (1 : ℝ) else 0)
      = (evEdge (o := o) (y := y) e).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hy : y ∈ cluster ω o <;> by_cases ht : e ∈ touchSet ω o <;>
      simp [evEdge, hy, ht]
  rw [show ∫ ω, (if y ∈ cluster ω o then (1 : ℝ) else 0)
        * (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ
      = ∫ ω, (evEdge (o := o) (y := y) e).indicator (fun _ => (1 : ℝ)) ω ∂μ from
    integral_congr_ae (Eventually.of_forall hcongr)]
  exact integral_indicator_one (measurableSet_evEdge (o := o) (y := y) e)

/-- The mean of the coupled vertex integrand is the coupled vertex measure. -/
theorem integral_evVert {o y : V} (μ : Measure (Config V)) [IsFiniteMeasure μ] (x : V) :
    ∫ ω, (if x ∈ cluster ω o then (1 : ℝ) else 0)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0) ∂μ
      = μ.real (evVert (o := o) (y := y) x) := by
  have hcongr : ∀ ω : Config V, (if x ∈ cluster ω o then (1 : ℝ) else 0)
      * (if y ∈ cluster ω o then (1 : ℝ) else 0)
      = (evVert (o := o) (y := y) x).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hx : x ∈ cluster ω o <;> by_cases hy : y ∈ cluster ω o <;>
      simp [evVert, hx, hy]
  rw [show ∫ ω, (if x ∈ cluster ω o then (1 : ℝ) else 0)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0) ∂μ
      = ∫ ω, (evVert (o := o) (y := y) x).indicator (fun _ => (1 : ℝ)) ω ∂μ from
    integral_congr_ae (Eventually.of_forall hcongr)]
  exact integral_indicator_one (measurableSet_evVert (o := o) (y := y) x)

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.vertexWeight_eq_sum
#print axioms PercLib.CriticalLRP.vertexWeight_le_incidentWeight
#print axioms PercLib.CriticalLRP.indicator_mul_indicator_one'
#print axioms PercLib.CriticalLRP.measurableSet_evEdge
#print axioms PercLib.CriticalLRP.measurableSet_evVert
#print axioms PercLib.CriticalLRP.integral_evEdge
#print axioms PercLib.CriticalLRP.integral_evVert
