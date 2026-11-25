module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main

/-!
# Right-hand excluded-mass limits at attained radii: definitions

Direction B6 of swarm `smwv6er9k`.

At a radius `r` that *is* an attained length of the source norm, the closed window
`B_r = {ρ ≤ r}` of the excluded mass `E1Sign.exclMass` carries a shell `{ρ = r}` that the strict
window `{ρ < r}` does not.  The right-hand side handled in this direction is the side on which
that shell is *present*, so the two window conventions have to be named separately:

* `shellF r` — the lattice points of the sphere `{ρ = r}` (a `Finset`, since they lie in the
  finite ball `B_r`);
* `exclShellFun r` — the shell summand of the excluded integrand;
* `exclMassShell r` — its mass, so that `exclMass r = exclMassStrict r + exclMassShell r`;
* `exclMassStrict r` — the excluded mass with the window frozen at the *strict* window
  `{ρ < r}` and the law still `cutLaw r`;
* `exclScalarStrict r` — its real form.

Nothing here asserts a limit, a continuity or a moment finiteness; those live in `Main.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The shell at radius `r`.**  The lattice points exactly on the norm sphere `{ρ = r}`; the
difference between the closed window `B_r` and the strict window `{ρ < r}`.  At an attained radius
this set is nonempty by definition of `attainedRadii`. -/
noncomputable def shellF (r : ℝ) : Finset M.V :=
  (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) = r)

theorem mem_shellF {r : ℝ} {y : M.V} :
    y ∈ M.shellF r ↔ M.S.ρ (toVec y) = r := by
  rw [shellF, Finset.mem_filter, E1Sign.mem_ballF]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem shellF_subset_ballF (r : ℝ) : M.shellF r ⊆ E1Sign.ballF M r :=
  Finset.filter_subset _ _

theorem ballFLt_sdiff_shellF (r : ℝ) : E1Sign.ballF M r \ M.ballFLt r = M.shellF r := by
  classical
  ext y
  rw [Finset.mem_sdiff, E1Sign.mem_ballF, M.mem_ballFLt, M.mem_shellF]
  constructor
  · rintro ⟨hle, hlt⟩
    exact le_antisymm hle (not_lt.mp hlt)
  · intro h
    exact ⟨h.le, not_lt.mpr h.ge⟩

/-- **The shell summand of the excluded integrand**, with the same law `cutLaw r` and the closed
window.  Its sum with the strict-window summand is the full `E1Sign.exclMass` integrand. -/
noncomputable def exclShellFun (r : ℝ) : Config M.V → ℝ≥0∞ :=
  fun ω => clusterVol ω (0 : M.V) *
    ∑ y ∈ M.shellF r,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y

/-- **The strict-window excluded mass at radius `r`.**  The same expression as
`E1Sign.exclMass` with the closed window replaced by `{ρ < r}`; the law is still `cutLaw r`, so
this is *not* a limit, it is the value against which the right-hand (closed-window) value is
compared. -/
noncomputable def exclMassStrict (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) *
    ∑ y ∈ M.ballFLt r,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
    ∂(M.cutLaw r)

/-- **The shell part of the excluded mass.** -/
noncomputable def exclMassShell (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, M.exclShellFun r ω ∂(M.cutLaw r)

/-- The strict-window excluded mass in `ℝ`. -/
noncomputable def exclScalarStrict (r : ℝ) : ℝ := (M.exclMassStrict r).toReal


/-- The vertices of the normalized ball of integral radius. -/
noncomputable def vertexExhaustion (M : SourceModelData) (n : ℕ) : Finset M.V :=
  E1Sign.ballF M (n : ℝ)

/-- All unordered vertex pairs in that same ball. -/
noncomputable def edgeExhaustion (M : SourceModelData) (n : ℕ) : Finset (Sym2 M.V) :=
  (M.vertexExhaustion n).sym2

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.shellF

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclShellFun

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassStrict

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclScalarStrict

end PercLib.CriticalLRP.Orchestration
