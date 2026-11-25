/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity

/-!
# Moving-window vocabulary for the connected window mass `connMass`

`E1Sign.connMass M r` is the mark-space integral of

`|K|² · ∑_{y ∈ B_r} 1(y ∈ K)`,

whose integrand carries the *moving* lattice window `B_r = {ρ ≤ r}`.  To state the radius
regularity of this object honestly we need to name:

* `connMarkFun M r` — the integrand on the common mark space (the object whose measurability,
  monotonicity and pointwise bounds are proved in the consumer module);
* `ballFLt M r` — the strict window `{ρ < r}`;
* `connMassLt M r` — the strict-window connected mass (the left limit of `connMass`, see the
  consumer module);
* `sphereMass M r` — the sphere layer `{ρ = r}` (the exact obstruction to left continuity);
* `connAnnulusFun M r₀ r` / `connAnnulusMass M r₀ r` — the annulus `B_r \ B_{r₀}` term used in
  the continuity-from-above decomposition.

No mathematical statement is asserted here.
-/



set_option autoImplicit false

@[expose] public section

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The mark-space integrand of `E1Sign.connMass M r`. -/
noncomputable def connMarkFun (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => (M.markVol r u) ^ 2 *
    ∑ y ∈ E1Sign.ballF M r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y

/-- The *strict* lattice window `{y | ρ y < r}`, as a `Finset`. -/
noncomputable def ballFLt (r : ℝ) : Finset M.V :=
  (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) < r)

theorem mem_ballFLt {r : ℝ} {y : M.V} :
    y ∈ M.ballFLt r ↔ M.S.ρ (toVec y) < r := by
  rw [ballFLt, Finset.mem_filter, E1Sign.mem_ballF]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- The strict-window mark integrand. -/
noncomputable def connMarkFunLt (r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => (M.markVol r u) ^ 2 *
    ∑ y ∈ M.ballFLt r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y

/-- The strict-window connected mass: the same expression as `connMass` but with the moving
window replaced by `{ρ < r}`.  This is the left limit of `E1Sign.connMass`. -/
noncomputable def connMassLt (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.connMarkFunLt r u ∂(markMeasure M.V)

/-- The sphere layer `{ρ = r}`, the exact difference between `connMass` and `connMassLt`. -/
noncomputable def sphereMass (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, (M.markVol r u) ^ 2 *
    ∑ y ∈ (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) = r),
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y
      ∂(markMeasure M.V)

/-- The annulus integrand of the moving window `B_r \ B_{r₀}`, with the `r₀`-cluster weight. -/
noncomputable def connAnnulusFun (r0 r : ℝ) : (Sym2 M.V → ℝ) → ℝ≥0∞ :=
  fun u => (M.markVol r0 u) ^ 2 *
    ∑ y ∈ (E1Sign.ballF M r).filter (fun y => y ∉ E1Sign.ballF M r0),
      (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y

/-- The mark-space mass of the annulus term. -/
noncomputable def connAnnulusMass (r0 r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, M.connAnnulusFun r0 r u ∂(markMeasure M.V)

end SourceModelData

end PercLib.CriticalLRP.Orchestration
