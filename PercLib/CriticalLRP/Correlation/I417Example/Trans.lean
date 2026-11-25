/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Trans.lean ; module path rewritten only.
-/

/-
# Transitivity: `E|K|` does not depend on the root

The hypotheses `hχ : ∀ v, meanVol π v = meanVol π x` used in `I417Example/Joint`, `I417Example/Excess` and
`I417Example/Printed` is the honest transitivity assumption on the weighted graph.  This file derives it
from the vertex-transitivity data used elsewhere in the repository: a `π`-preserving permutation of
the vertex set acting transitively on vertices.

(For the paper's vertex-transitive weighted graphs such permutations exist for every pair of
vertices; on `Z^d` they are the translations.)
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Excess
public import PercLib.CriticalLRP.Correlation.HvolPermutation

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

variable {V : Type*} [Countable V]

/-- A `π`-preserving permutation maps connection events to connection events, in both
directions. -/
theorem connects_permConfig_iff (g : V ≃ V) (ω : Config V) (a b : V) :
    Connects (Hvol.permConfig g ω) (g a) (g b) ↔ Connects ω a b := by
  refine ⟨fun h => ?_, fun h => Hvol.connects_permConfig g h⟩
  have h2 := Hvol.connects_permConfig (g := g.symm) (ω := Hvol.permConfig g ω) h
  rw [Hvol.permConfig_inv_perm] at h2
  simpa using h2

/-- The two-point function is invariant under `π`-preserving permutations. -/
theorem measure_connSet_perm (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hg : ∀ e : Sym2 V, π (Sym2.map g e) = π e) (a b : V) :
    (edgeMeasure π) (connSet (g a) (g b)) = (edgeMeasure π) (connSet a b) := by
  have hmap := Hvol.edgeMeasure_permConfig_invariant π g hg
  have hpre : (Hvol.permConfig g) ⁻¹' connSet (g a) (g b) = connSet a b := by
    ext ω
    exact connects_permConfig_iff g ω a b
  have h := Measure.map_apply (μ := edgeMeasure π) (Hvol.measurable_permConfig g)
    (measurableSet_connSet (g a) (g b))
  rw [hmap] at h
  calc (edgeMeasure π) (connSet (g a) (g b))
      = (edgeMeasure π) (Hvol.permConfig g ⁻¹' connSet (g a) (g b)) := h
    _ = (edgeMeasure π) (connSet a b) := by rw [hpre]

/-- **Transitivity of `E|K|`** under a `π`-preserving permutation. -/
theorem meanVol_perm (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hg : ∀ e : Sym2 V, π (Sym2.map g e) = π e) (v : V) :
    meanVol π (g v) = meanVol π v := by
  have h1 : ∀ w : V, (edgeMeasure π) (connSet (g v) w) =
      (edgeMeasure π) (connSet v (g.symm w)) := by
    intro w
    have h := measure_connSet_perm π g hg v (g.symm w)
    rwa [Equiv.apply_symm_apply] at h
  rw [meanVol, tsum_congr h1]
  exact Equiv.tsum_eq g.symm (fun u => (edgeMeasure π) (connSet v u))

/-- **The transitivity hypothesis of the development**, derived from vertex transitivity: if for
every vertex `v` there is a `π`-preserving permutation carrying `x` to `v`, then `meanVol` is
constant. -/
theorem meanVol_eq_of_transitive (π : Sym2 V → unitInterval) (x : V)
    (h : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    ∀ v : V, meanVol π v = meanVol π x := by
  intro v
  obtain ⟨g, hg, hgx⟩ := h v
  have := meanVol_perm π g hg x
  rwa [hgx] at this

end PercLib.CriticalLRP.I417Example
