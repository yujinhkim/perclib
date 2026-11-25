/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Definitions preserving the normalized kernel, norm, cutoff, model data and moment formulas
of Hutchcroft Critical LRP I, arXiv:2508.18807v1, organized in dependency order.
No theorem conclusion is asserted here.
-/
module

public import PercLib.CriticalLRP.Orchestration.SourceModel
public import PercLib.CriticalLRP.Orchestration.Data.Defs
public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.CriticalLRP.Tightness.MaxCluster
public import PercLib.CriticalLRP.Analysis.RegularVariation
public import PercLib.CriticalLRP.VolumeMoments.DFactorial
public import PercLib.CriticalLRP.KernelGeometry
public import PercLib.CriticalLRP.LatticeGeometry

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.Orchestration

def toVec {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => (x i : ℝ)

theorem toVec_sub {d : ℕ} (x y : Fin d → ℤ) : toVec (x - y) = toVec x - toVec y := by
  funext i
  simp [toVec]

theorem toVec_sub_eq_neg {d : ℕ} (x y : Fin d → ℤ) : toVec (y - x) = -(toVec (x - y)) := by
  funext i
  simp only [toVec, Pi.sub_apply, Pi.neg_apply, Int.cast_sub]
  ring


def SourceNormData.dist {d : ℕ} (S : SourceNormData d) (x y : Fin d → ℤ) : ℝ := S.ρ (toVec (x - y))

theorem SourceNormData.dist_pos {d : ℕ} (S : SourceNormData d) {x y : Fin d → ℤ} (h : x ≠ y) :
    0 < S.dist x y := by
  refine S.ρ_pos _ ?_
  intro hc
  apply h
  funext i
  have h1 : (((x i : ℤ) - (y i : ℤ) : ℤ) : ℝ) = 0 := by
    simpa [toVec] using congrFun hc i
  have h2 : (x i : ℤ) - (y i : ℤ) = 0 := by exact_mod_cast h1
  exact sub_eq_zero.mp h2

theorem SourceNormData.dist_comm {d : ℕ} (S : SourceNormData d) (x y : Fin d → ℤ) :
    S.dist y x = S.dist x y := by
  rw [SourceNormData.dist, SourceNormData.dist, toVec_sub_eq_neg, S.ρ_neg]






theorem SourceNormData.ball_count {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) :
    (fun r : ℝ => (({y : Fin d → ℤ | S.ρ (fun j => (y j : ℝ)) ≤ r} : Set (Fin d → ℤ)).ncard : ℝ))
      ~[atTop] (fun r : ℝ => r ^ d) :=
  LatticeGeometry.lemma_I_4_6_isEquivalent (d := d) hd (ρ := S.ρ)
    S.ρ_add_le S.ρ_neg S.ρ_continuous S.ρ_smul S.unitBall_volume





def radialSym {d : ℕ} (S : SourceNormData d) (K : ℝ → ℝ) : Sym2 (Fin d → ℤ) → ℝ :=
  Sym2.lift ⟨fun x y => if x = y then 0 else K (S.dist x y), by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := fun hh => h hh.symm
      show (if x = y then (0 : ℝ) else K (S.dist x y))
        = (if y = x then (0 : ℝ) else K (S.dist y x))
      rw [ite_eq_right h, ite_eq_right h', SourceNormData.dist_comm S y x]⟩

theorem radialSym_mk {d : ℕ} (S : SourceNormData d) (K : ℝ → ℝ) (x y : Fin d → ℤ) :
    radialSym S K s(x, y) = if x = y then 0 else K (S.dist x y) := rfl

theorem radialSym_nonneg {d : ℕ} (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : ∀ s : ℝ, 0 < s → 0 ≤ K s) (e : Sym2 (Fin d → ℤ)) : 0 ≤ radialSym S K e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [radialSym_mk]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h]
      exact hK _ (S.dist_pos h)




def cutRadialSym {d : ℕ} (S : SourceNormData d) (K : ℝ → ℝ) (r : ℝ) :
    Sym2 (Fin d → ℤ) → ℝ :=
  radialSym S (FiniteVolume.cutoffProfile K r)

theorem cutoffProfile_nonneg_on {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0)) {r s : ℝ}
    (hs : 0 < s) : 0 ≤ FiniteVolume.cutoffProfile K r s := by
  rcases le_or_gt s r with h | h
  · exact FiniteVolume.cutoffProfile_nonneg hK hs (lt_of_lt_of_le hs h) h
  · rw [FiniteVolume.cutoffProfile_of_lt h]










namespace SourceModelData

variable (M : SourceModelData)


abbrev V : Type := Fin M.d → ℤ


def kernel : Sym2 M.V → ℝ := radialSym M.S M.K

theorem kernel_nonneg : ∀ e : Sym2 M.V, 0 ≤ M.kernel e :=
  radialSym_nonneg M.S M.K_nonneg


def law (β : ℝ≥0) : Measure (Config M.V) := longRangeMeasure M.kernel M.kernel_nonneg β



def betaCrit : ℝ≥0 := criticalBeta M.kernel M.kernel_nonneg


def criticalLaw : Measure (Config M.V) := M.law M.betaCrit


def cutKernel (r : ℝ) : Sym2 M.V → ℝ := cutRadialSym M.S M.K r

theorem cutKernel_nonneg (r : ℝ) : ∀ e : Sym2 M.V, 0 ≤ M.cutKernel r e :=
  radialSym_nonneg M.S (fun _s hs => cutoffProfile_nonneg_on M.K_antitone hs)


def cutLaw (r : ℝ) : Measure (Config M.V) :=
  longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit



def cutMoment (p : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (clusterVol ω (0 : M.V)) ^ p ∂(M.cutLaw r)


def tailProb (n : ℕ) : ℝ :=
  M.criticalLaw.real {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}


def twoPoint (β : ℝ≥0) (x y : M.V) : ℝ :=
  (M.law β).real {ω : Config M.V | Connects ω x y}


def ball (r : ℝ) : Set M.V := {y : M.V | M.S.ρ (toVec y) ≤ r}




def maxClusterInBall (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ⨆ x : M.V, clusterVolIn ω x (M.ball r)





def Mr (r : ℝ) : ℕ :=
  sInf ({n : ℕ | (M.cutLaw r).real {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
      ≤ Real.exp (-1)} : Set ℕ)

end SourceModelData













/-- Ball-count asymptotics in the notation of the model, derived from the normalized unit ball. -/
theorem SourceModelData.ball_count (M : SourceModelData) :
    (fun r : ℝ => ((M.ball r).ncard : ℝ)) ~[atTop] (fun r : ℝ => r ^ M.d) :=
  M.S.ball_count M.hd



def HD (M : SourceModelData) : Prop :=
  (3 * M.α < (M.d : ℝ)) ∨
  (6 < M.d ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) ∨
  (M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y
        ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
            * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))


def Hydro (M : SourceModelData) : Prop :=
  Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ (((M.d : ℝ) + M.α) / 2)) atTop (𝓝 0)



def HDplus (M : SourceModelData) : Prop :=
  HD M ∨ ((M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ Hydro M)








def I16rhs (M : SourceModelData) (A : ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  (VolumeMoments.M (p - 1) : ℝ) * A ^ (p - 1) * (M.α / (M.betaCrit : ℝ))
    * r ^ ((2 * (p : ℝ) - 1) * M.α)












def scaleMap (α : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ := A r * r ^ (2 * α)


def invScaleMap (α : ℝ) (Astar : ℝ → ℝ) (n : ℝ) : ℝ :=
  (Astar n) ^ (-1 / (2 * α)) * n ^ (1 / (2 * α))


def MutuallyInverse (α : ℝ) (A Astar : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → invScaleMap α Astar (scaleMap α A r) = r) ∧
  (∀ n : ℝ, 0 < n → scaleMap α A (invScaleMap α Astar n) = n)


def BoundedFun (f : ℝ → ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |f x| ≤ C


def I116rhs (M : SourceModelData) (A : ℝ → ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  (VolumeMoments.M (p - 1) : ℝ) * (A r) ^ (p - 1) * (M.α / (M.betaCrit : ℝ))
    * r ^ ((2 * (p : ℝ) - 1) * M.α)






end PercLib.CriticalLRP.Orchestration
