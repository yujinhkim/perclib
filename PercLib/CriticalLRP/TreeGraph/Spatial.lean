/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Clusters, cluster volume and spatial moments in finite-edge Bernoulli bond percolation,
for Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.1 and §I.5.1.

This file ties the probabilistic moments used in the moment bounds to the actual cluster
random variable:

* `clusterF ends s x` is the cluster of `x` in the configuration `s`, as a `Finset V`;
* `clusterVol ends s x` is its cardinality `|K_x|`;
* `expectation_clusterVol`: `E|K_x| = ∑_y P(x ↔ y)` (`= clusterVolume`, the definition used
  in `Moments.lean`);
* `expectation_clusterVol_sq`: `E[|K_x|²] = ∑_{y,z} P(x ↔ y, x ↔ z)` (`= clusterVolSq`);
* `expectation_spatialMoment`: for any weight `w : V → ℝ`,
  `E[∑_{y ∈ K_x} w y] = ∑_y w y · P(x ↔ y)`;
* `radiusOfGyration`: the paper's `ξ₂²` (§I.5.1), with the identity above as its content.

All sums are finite (the vertex set is a fintype), so nothing here needs a limiting argument.
-/
module

public import PercLib.CriticalLRP.TreeGraph.ClusterMoments

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset
open Classical

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The cluster of a vertex -/

/-- The cluster of `x` in the configuration `s`: the set of vertices joined to `x` by an open
path. -/
def clusterF (ends : E → Sym2 V) (s : Finset E) (x : V) : Finset V := by
  classical
  exact univ.filter fun y => Conn ends s x y

/-- The cluster volume `|K_x|` as a natural number. -/
def clusterVol (ends : E → Sym2 V) (s : Finset E) (x : V) : ℕ := (clusterF ends s x).card

theorem mem_clusterF {ends : E → Sym2 V} {s : Finset E} {x y : V} :
    y ∈ clusterF ends s x ↔ Conn ends s x y := by
  classical
  simp [clusterF]

theorem self_mem_clusterF (ends : E → Sym2 V) (s : Finset E) (x : V) :
    x ∈ clusterF ends s x :=
  mem_clusterF.mpr (conn_refl ends s x)

/-- The cluster is the equivalence class of `x`. -/
theorem clusterF_eq_of_conn {ends : E → Sym2 V} {s : Finset E} {x y : V}
    (h : Conn ends s x y) : clusterF ends s x = clusterF ends s y := by
  classical
  ext z
  simp only [mem_clusterF]
  exact ⟨fun hxz => conn_trans (conn_symm h) hxz, fun hyz => conn_trans h hyz⟩

theorem clusterVol_eq_sum (ends : E → Sym2 V) (s : Finset E) (x : V) :
    clusterVol ends s x = ∑ y : V, if Conn ends s x y then 1 else 0 := by
  classical
  rw [clusterVol, clusterF, Finset.card_eq_sum_ones, Finset.sum_filter]

/-! ### Expectations of cluster functionals -/

/-- Indicator function of a set of configurations, valued in `ℝ`. -/
def indicatorR (A : Set (Finset E)) (s : Finset E) : ℝ := if s ∈ A then 1 else 0

theorem prob_eq_sum_indicator (p : E → ℝ) (A : Set (Finset E)) :
    prob p A = ∑ s, PercLib.CriticalLRP.configurationLaw p s * indicatorR A s := rfl

/-- Expectation of a functional of the configuration. -/
def expectReal (p : E → ℝ) (X : Finset E → ℝ) : ℝ :=
  ∑ s, PercLib.CriticalLRP.configurationLaw p s * X s

/-- `E|K_x| = ∑_y P(x ↔ y)`: the expected cluster volume is the total mass of the two-point
function. -/
theorem expectation_clusterVol (p : E → ℝ) (ends : E → Sym2 V) (x : V) :
    expectReal p (fun s => (clusterVol ends s x : ℝ)) = clusterVolume p ends x := by
  classical
  have h1 : ∀ s : Finset E, (clusterVol ends s x : ℝ)
      = ∑ y : V, indicatorR {s | Conn ends s x y} s := by
    intro s
    rw [clusterVol_eq_sum]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rfl
  simp only [h1, expectReal, clusterVolume, twoPoint, prob_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `E[|K_x|²] = ∑_{y,z} P(x ↔ y, x ↔ z)`. -/
theorem expectation_clusterVol_sq (p : E → ℝ) (ends : E → Sym2 V) (x : V) :
    expectReal p (fun s => (clusterVol ends s x : ℝ) ^ 2) = clusterVolSq p ends x := by
  classical
  have h1 : ∀ s : Finset E, (clusterVol ends s x : ℝ) ^ 2
      = ∑ y : V, ∑ z : V, indicatorR {s | Conn ends s x y ∧ Conn ends s x z} s := by
    intro s
    rw [clusterVol_eq_sum]
    push_cast
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    by_cases hy : Conn ends s x y <;> by_cases hz : Conn ends s x z <;> simp [indicatorR, hy, hz]
  simp only [h1, expectReal, clusterVolSq, prob_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

/-- `E[∑_{y ∈ K_x} w y] = ∑_y w y · P(x ↔ y)` for any weight `w`. -/
theorem expectation_spatialMoment (p : E → ℝ) (ends : E → Sym2 V) (x : V) (w : V → ℝ) :
    expectReal p (fun s => ∑ y ∈ clusterF ends s x, w y)
      = ∑ y : V, w y * twoPoint p ends x y := by
  classical
  have h1 : ∀ s : Finset E, (∑ y ∈ clusterF ends s x, w y)
      = ∑ y : V, w y * indicatorR {s | Conn ends s x y} s := by
    intro s
    rw [clusterF, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : Conn ends s x y <;> simp [indicatorR, h]
  simp only [h1, expectReal, twoPoint, prob_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => by ring

/-! ### Elementary bounds and the Harris--FKG consequence `(E|K|)² ≤ E|K|²` -/

theorem twoPoint_nonneg {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (ends : E → Sym2 V) (x y : V) : 0 ≤ twoPoint p ends x y :=
  prob_nonneg hp hp1 _

theorem prob_univ (p : E → ℝ) : prob p Set.univ = 1 := by
  simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
  simp [PercLib.CriticalLRP.configurationLaw_sum]

theorem twoPoint_le_one {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (ends : E → Sym2 V) (x y : V) : twoPoint p ends x y ≤ 1 := by
  refine le_trans (prob_mono hp hp1 (Set.subset_univ _)) (le_of_eq (prob_univ p))

theorem twoPoint_symm (p : E → ℝ) (ends : E → Sym2 V) (x y : V) :
    twoPoint p ends x y = twoPoint p ends y x := by
  unfold twoPoint
  congr 1
  ext s
  exact ⟨conn_symm, conn_symm⟩

theorem monotone_clusterVol (ends : E → Sym2 V) (x : V) :
    Monotone fun s : Finset E => (clusterVol ends s x : ℝ) := by
  intro s t hst
  have hsub : clusterF ends s x ⊆ clusterF ends t x := fun _ hy =>
    mem_clusterF.mpr (conn_mono hst (mem_clusterF.mp hy))
  have h := Finset.card_le_card hsub
  simp only [clusterVol]
  exact_mod_cast h

theorem clusterF_mono {ends : E → Sym2 V} {s t : Finset E} (hst : s ⊆ t) (x : V) :
    clusterF ends s x ⊆ clusterF ends t x := fun _ hy =>
  mem_clusterF.mpr (conn_mono hst (mem_clusterF.mp hy))

theorem expectReal_eq_expectation (p : E → ℝ) (X : Finset E → ℝ) :
    expectReal p X = PercLib.CriticalLRP.expectation p X := rfl

/-- Harris--FKG gives `(E|K_x|)² ≤ E|K_x|²`: the cluster volume is an increasing function of
the configuration, so its two lowest moments are ordered. -/
theorem clusterVolume_sq_le_clusterVolSq {p : E → ℝ} (hp : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (ends : E → Sym2 V) (x : V) :
    (clusterVolume p ends x) ^ 2 ≤ clusterVolSq p ends x := by
  have hF := PercLib.CriticalLRP.expectation_mul_expectation_le p hp hp1
    (fun s => (clusterVol ends s x : ℝ)) (fun s => (clusterVol ends s x : ℝ))
    (fun s => by positivity) (fun s => by positivity)
    (monotone_clusterVol ends x) (monotone_clusterVol ends x)
  rw [← expectation_clusterVol, ← expectation_clusterVol_sq, expectReal_eq_expectation,
    expectReal_eq_expectation]
  calc (PercLib.CriticalLRP.expectation p (fun s => (clusterVol ends s x : ℝ))) ^ 2
      = PercLib.CriticalLRP.expectation p (fun s => (clusterVol ends s x : ℝ)) *
        PercLib.CriticalLRP.expectation p (fun s => (clusterVol ends s x : ℝ)) := sq _
    _ ≤ PercLib.CriticalLRP.expectation p
          (fun s => (clusterVol ends s x : ℝ) * (clusterVol ends s x : ℝ)) := hF
    _ = PercLib.CriticalLRP.expectation p (fun s => (clusterVol ends s x : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp [sq]

/-! ### The radius of gyration -/

/-- The second spatial moment of the cluster of `x` with respect to the weight `w` (in the
paper, `w y = ‖y‖₂²`): `∑_y w y · P(x ↔ y) = E[∑_{y ∈ K_x} w y]`. -/
def spatialMoment (p : E → ℝ) (ends : E → Sym2 V) (x : V) (w : V → ℝ) : ℝ :=
  ∑ y : V, w y * twoPoint p ends x y

/-- The radius of gyration `ξ₂²` of §I.5.1, with `w y = ‖y‖₂²`. -/
def radiusOfGyration (p : E → ℝ) (ends : E → Sym2 V) (x : V) (w : V → ℝ) : ℝ :=
  spatialMoment p ends x w / clusterVolume p ends x

theorem spatialMoment_eq_expectation (p : E → ℝ) (ends : E → Sym2 V) (x : V)
    (w : V → ℝ) :
    spatialMoment p ends x w = expectReal p (fun s => ∑ y ∈ clusterF ends s x, w y) :=
  (expectation_spatialMoment p ends x w).symm

end

end PercLib.CriticalLRP.TreeGraph
