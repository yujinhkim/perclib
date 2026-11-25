/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.Expectation.Basic
public import PercLib.CriticalLRP.Correlation.HvolPermutation

/-
A finite torus instantiation of the third-moment error estimate used after
Lemma I.4.7. This is a native-model non-vacuity example, not the infinite
lattice cutoff theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

/-- On a finite torus with translation-invariant edge probabilities, all
moment, root-independence and non-degeneracy premises of the third-moment
`cE1` estimate hold. Hence `0 ≤ cE1 ≤ 3 (E|K_0|)^3 / |B|`. -/
theorem torus_cE1_le_three_mul_cube_div (d n : ℕ) [NeZero n]
    (π : Sym2 (Fin d → ZMod n) → unitInterval)
    (hπ : ∀ e, (π e : ℝ) < 1)
    (hπinv : ∀ (a : Fin d → ZMod n) (e : Sym2 (Fin d → ZMod n)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (B : Finset (Fin d → ZMod n)) (hB : B.Nonempty) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
      ∂(edgeMeasure π)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) ∂(edgeMeasure π)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        3 * A.toReal ^ 3 / B.card := by
  refine Hrest.cE1_le_three_mul_cube_div_of_finite (V := Fin d → ZMod n)
    ?_ 0 B hB (fun _ => Finset.univ) (fun _ _ _ => Finset.subset_univ _)
    (fun _ => ⟨0, Finset.mem_univ _⟩)
    (∫⁻ ω, Percolation.cardFun (cluster ω 0) ∂(edgeMeasure π)) rfl
    (fun y _ => Hvol.hvol_cardFun_torus d n π hπinv 0 y) ?_ ?_
  · exact_mod_cast hπ
  · rw [lintegral_cardFun_cluster]
    exact ENNReal.ofReal_ne_top
  · exact third_moment_le_native_of_translation_invariant π hπ hπinv

end
end PercLib.CriticalLRP.TreeExpansion
