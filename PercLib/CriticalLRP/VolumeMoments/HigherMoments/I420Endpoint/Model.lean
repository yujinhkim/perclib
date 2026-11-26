/- Reflection invariance at a normalized radial lattice. -/

module

public import PercLib.CriticalLRP.Correlation.I417Example.Trans
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Endpoint.Main

/-! Midpoint reflection for normalized radial cut-off models. -/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.I420Endpoint

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal Topology

/-- At zero, reflection preserves the normalized source norm of a difference. -/
theorem dist_reflect_norm {d : ℕ} (S : Orchestration.SourceNormData d)
    (y u v : Fin d → ℤ) :
    S.dist (reflect 0 y u) (reflect 0 y v) = S.dist u v := by
  rw [Orchestration.SourceNormData.dist, Orchestration.SourceNormData.dist]
  have huv : (reflect (0 : Fin d → ℤ) y u) - (reflect (0 : Fin d → ℤ) y v)
      = v - u := by
    simp only [reflect_apply, zero_add]
    abel
  rw [huv, Orchestration.toVec_sub_eq_neg, S.ρ_neg]

/-- Any radial function of the source norm is invariant at the midpoint reflection from zero. -/
theorem radial_reflect_norm {d : ℕ} (S : Orchestration.SourceNormData d)
    (K : ℝ → ℝ) (y : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    Orchestration.radialSym S K (Sym2.map (reflect 0 y) e) = Orchestration.radialSym S K e := by
  induction e using Sym2.ind with
  | h u v =>
    change Orchestration.radialSym S K s(reflect 0 y u, reflect 0 y v) = _
    rw [Orchestration.radialSym_mk, Orchestration.radialSym_mk]
    by_cases huv : u = v
    · simp [huv]
    · have hne : reflect (0 : Fin d → ℤ) y u ≠ reflect (0 : Fin d → ℤ) y v := by
        exact fun h => huv ((reflect (0 : Fin d → ℤ) y).injective h)
      simp only [huv, hne, dist_reflect_norm]

/-- The cut-off source radial kernel is preserved by every reflection from the origin. -/
theorem cutKernel_reflect_norm (M : Orchestration.SourceModelData) (y : M.V) (r : ℝ)
    (e : Sym2 M.V) :
    M.cutKernel r (Sym2.map (reflect 0 y) e) = M.cutKernel r e := by
  exact radial_reflect_norm M.S (FiniteVolume.cutoffProfile M.K r) y e

/-- **The mixed endpoint identity at the actual normalized radial cutoff profile.**
The window is an arbitrary finite set; no extra symmetry or moment-finiteness premise is used. -/
theorem mixedExcl_cutKernel_swap (M : Orchestration.SourceModelData) (r : ℝ)
    (a b : ℕ) (B : Finset M.V) :
    I420Case1.mixedExcl (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
      0 a b B =
    I420Case1.mixedExcl (bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
      0 b a B := by
  apply mixedExcl_swap_window
  intro y hy e
  simp only [bernoulliEdgeProb, cutKernel_reflect_norm]

end PercLib.CriticalLRP.I420Endpoint
end
