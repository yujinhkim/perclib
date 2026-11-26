/- Endpoint symmetry under reflection preserving a profile and root marker. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Endpoint.Defs

/-! Reflection at the midpoint of two roots, and transfer of mixed cluster-window expectations. -/
@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace PercLib.CriticalLRP.I420Endpoint

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal Topology

variable {V : Type*} [Countable V] [AddCommGroup V]

@[simp] theorem reflect_apply (x y z : V) : reflect x y z = x + y - z := rfl

@[simp] theorem reflect_left (x y : V) : reflect x y x = y := by
  simp [reflect]

@[simp] theorem reflect_right (x y : V) : reflect x y y = x := by
  simp [reflect]

/-- Root cardinalities are preserved by a vertex permutation. -/
theorem clusterVol_perm (g : V ≃ V) (ω : Config V) (v : V) :
    clusterVol (Hvol.permConfig g ω) (g v) = clusterVol ω v := by
  rw [← PercLib.CriticalLRP.I420Case1.cardFun_cluster_eq_clusterVol,
    ← PercLib.CriticalLRP.I420Case1.cardFun_cluster_eq_clusterVol, Hvol.cluster_permConfig]
  exact Hvol.cardFun_image_equiv g (cluster ω v)

/-- A point index transports compatibly with cluster membership. -/
theorem mem_cluster_perm (g : V ≃ V) (ω : Config V) (x y : V) :
    y ∈ cluster ω x ↔ g y ∈ cluster (Hvol.permConfig g ω) (g x) := by
  rw [mem_cluster_iff, mem_cluster_iff]
  exact (I417Example.connects_permConfig_iff g ω x y).symm

/-- The point moment is invariant when roots and marker are permuted together. -/
theorem mixedPoint_perm (g : V ≃ V) (x y : V) (a b : ℕ) (ω : Config V) :
    mixedPoint (g x) (g y) a b (Hvol.permConfig g ω) = mixedPoint x y a b ω := by
  rw [mixedPoint, mixedPoint, clusterVol_perm, clusterVol_perm]
  by_cases hz : y ∈ cluster ω x
  · have hz' : g y ∈ cluster (Hvol.permConfig g ω) (g x) := (mem_cluster_perm g ω x y).mp hz
    have h0 : g y ∉ (cluster (Hvol.permConfig g ω) (g x))ᶜ := by simpa using hz'
    have h1 : y ∉ (cluster ω x)ᶜ := by simpa using hz
    rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]
  · have hz' : g y ∉ cluster (Hvol.permConfig g ω) (g x) := (mem_cluster_perm g ω x y).not.mp hz
    have h0 : g y ∈ (cluster (Hvol.permConfig g ω) (g x))ᶜ := by simpa using hz'
    have h1 : y ∈ (cluster ω x)ᶜ := by simpa using hz
    rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1]

/-- Connection is symmetric with respect to the two root points. -/
theorem mem_cluster_comm (x y : V) (ω : Config V) :
    y ∈ cluster ω x ↔ x ∈ cluster ω y := by
  constructor
  · intro hy
    apply mem_cluster_iff.mpr
    exact connects_symm (mem_cluster_iff.mp hy)
  · intro hx
    apply mem_cluster_iff.mpr
    exact connects_symm (mem_cluster_iff.mp hx)

/-- Applying the reflection transports both roots and maps the roots `y,x` to `x,y`. -/
theorem mixedPoint_reflect (x y : V) (a b : ℕ) (ω : Config V) :
    mixedPoint x y a b (Hvol.permConfig (reflect x y) ω) = mixedPoint y x a b ω := by
  simpa using mixedPoint_perm (reflect x y) y x a b ω

/-- Symmetry in `a,b` per site: no moment-finiteness or symmetry of the window is needed. -/
theorem mixedPoint_swap (x y : V) (a b : ℕ) (ω : Config V) :
    mixedPoint y x a b ω = mixedPoint x y b a ω := by
  by_cases hxy : Connects ω x y
  · have hyx : Connects ω y x := connects_symm hxy
    rw [mixedPoint, mixedPoint]
    have h1 : x ∈ cluster ω y := mem_cluster_iff.mpr hyx
    have h2 : y ∈ cluster ω x := mem_cluster_iff.mpr hxy
    rw [Set.indicator_of_notMem (by simpa using h1),
      Set.indicator_of_notMem (by simpa using h2)]
    simp
  · have hyx : ¬ Connects ω y x := fun h => hxy (connects_symm h)
    rw [mixedPoint, mixedPoint]
    have h1 : x ∈ (cluster ω y)ᶜ := by
      rw [Set.mem_compl_iff]
      exact fun hm => hyx (mem_cluster_iff.mp hm)
    have h2 : y ∈ (cluster ω x)ᶜ := by
      rw [Set.mem_compl_iff]
      exact fun hm => hxy (mem_cluster_iff.mp hm)
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    ring

/-- The reflection implements the per-site endpoint identity exactly. -/
theorem mixedPoint_reflect_ba (x y : V) (a b : ℕ) (ω : Config V) :
    mixedPoint x y b a (Hvol.permConfig (reflect x y) ω) = mixedPoint x y a b ω := by
  calc
    mixedPoint x y b a (Hvol.permConfig (reflect x y) ω)
        = mixedPoint y x b a ω := mixedPoint_reflect x y b a ω
    _ = mixedPoint x y a b ω := mixedPoint_swap x y b a ω

/-- Measurability of the mixed point moment for independent percolation. -/
theorem measurable_mixedPoint (x y : V) (a b : ℕ) :
    Measurable (mixedPoint x y a b) := by
  have hm := ((measurable_clusterVol x).pow_const a)
  exact hm.mul ((measurable_const.indicator (measurableSet_cluster_mem x y).compl).mul
    ((measurable_clusterVol y).pow_const b))

/-- The per-site endpoint expectation is symmetric after any profile-preserving permutation;
window B is untouched and infinite moments are retained. -/
theorem lintegral_mixedPoint_reflect (π : Sym2 V → unitInterval)
    (x y : V) (hg : ∀ e : Sym2 V, π (Sym2.map (reflect x y) e) = π e) (a b : ℕ) :
    ∫⁻ ω, mixedPoint x y b a ω ∂(edgeMeasure π) = ∫⁻ ω, mixedPoint x y a b ω ∂(edgeMeasure π) := by
  calc
    (∫⁻ ω, mixedPoint x y b a ω ∂(edgeMeasure π))
        = ∫⁻ ω, mixedPoint x y a b (Hvol.permConfig (reflect x y) ω) ∂(edgeMeasure π) :=
          lintegral_congr fun ω => (mixedPoint_reflect_ba x y b a ω).symm
    _ = ∫⁻ ω, mixedPoint x y a b ω ∂(edgeMeasure π).map (Hvol.permConfig (reflect x y)) :=
          (lintegral_map (measurable_mixedPoint x y a b)
            (Hvol.measurable_permConfig (reflect x y))).symm
    _ = ∫⁻ ω, mixedPoint x y a b ω ∂(edgeMeasure π) := by
          rw [Hvol.edgeMeasure_permConfig_invariant π (reflect x y) hg]

/-- **Endpoint mass transport for finite windows**, with no symmetry assumption on `B`. -/
theorem mixedExcl_swap (π : Sym2 V → unitInterval)
    (x y : V) (hg : ∀ e : Sym2 V, π (Sym2.map (reflect x y) e) = π e)
    (a b : ℕ) :
    ∫⁻ ω, mixedPoint x y b a ω ∂(edgeMeasure π) = ∫⁻ ω, mixedPoint x y a b ω ∂(edgeMeasure π) :=
  lintegral_mixedPoint_reflect π x y hg a b

/-- The full finite-window sum preserves the mixed endpoint terms. -/
theorem mixedExcl_swap_window (π : Sym2 V → unitInterval) (x : V) (a b : ℕ)
    (B : Finset V) (hg : ∀ y ∈ B, ∀ e : Sym2 V, π (Sym2.map (reflect x y) e) = π e) :
    I420Case1.mixedExcl π x a b B = I420Case1.mixedExcl π x b a B := by
  rw [PercLib.CriticalLRP.I420Case1.mixedExcl_eq_sum_lintegral,
    PercLib.CriticalLRP.I420Case1.mixedExcl_eq_sum_lintegral]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∫⁻ ω, {ω' : Config V | ¬ Connects ω' x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω x ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π))
        = ∫⁻ ω, mixedPoint x y a b ω ∂(edgeMeasure π) := by
          apply lintegral_congr
          intro ω
          rw [mixedPoint]
          rw [I420Case1.indicator_compl_cluster]
          ring
    _ = ∫⁻ ω, mixedPoint x y b a ω ∂(edgeMeasure π) :=
        lintegral_mixedPoint_reflect π x y (hg y hy) b a
    _ = ∫⁻ ω, {ω' : Config V | ¬ Connects ω' x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω x ^ b * clusterVol ω y ^ a) ∂(edgeMeasure π) := by
          apply lintegral_congr
          intro ω
          rw [mixedPoint]
          rw [I420Case1.indicator_compl_cluster]
          ring

/-- The real-valued endpoint identity consumed by the higher-moment induction. -/
theorem mixedExcl_toReal_swap_window (π : Sym2 V → unitInterval) (x : V) (a b : ℕ)
    (B : Finset V) (hg : ∀ y ∈ B, ∀ e : Sym2 V, π (Sym2.map (reflect x y) e) = π e) :
    (I420Case1.mixedExcl π x a b B).toReal = (I420Case1.mixedExcl π x b a B).toReal := by
  rw [mixedExcl_swap_window π x a b B hg]

end PercLib.CriticalLRP.I420Endpoint
end
