/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Main.lean ; module path rewritten only.
-/

/-
# Lemma I.4.17 at `p = 2`, `q = 1`: assembled statements

This file collects the end-to-end statements of direction A.

* `printed_le_lintegral` — the printed display of Lemma I.4.17 at `p = 2`, `q = 1`, with the
  printed constants `1` and `2`, for the true difference
  `E|K|² E|K| − E[|Kx|²|Ky|1(x↮y)]` (using the tight covering `I417Example/Printed`).
* `printed_le_of_transitive` — the same with the transitivity hypothesis discharged from
  vertex-transitivity data (a `π`-preserving permutation taking `x` to each other vertex).
* `source_le_two_four` — the same difference bounded with uniform constants `2` and `4`, obtained
  by feeding `I417Example/Excess.excess_le_two_four` (the bound on the larger `I417.excess`) into
  direction B's conditional consumer `I417.I417_p21_of_diagram`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Printed
public import PercLib.CriticalLRP.Correlation.I417Example.Trans

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

variable {V : Type*} [Countable V]

/-- The printed display with the susceptibility written as a `lintegral`. -/
theorem printed_le_lintegral (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 := by
  rw [← tsum_connSet_eq_lintegral]
  exact printed_le π hπ x y hχ

/-- **The printed `p = 2`, `q = 1` display of Lemma I.4.17**, with the transitivity hypothesis
discharged from vertex-transitivity data. -/
theorem printed_le_of_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (h : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    volSq π x * meanVol π y - exclMomentSq π x y ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 :=
  printed_le π hπ x y (meanVol_eq_of_transitive π x h)

/-- **The uniform-constant corollary**: the difference is bounded by `2 T³ χ⁴ + 4 T⁴ χ³`.  This is
what the bound on the (larger) `I417.excess` gives; it holds without using the redundancy of the
`y ∈ Kx` family. -/
theorem source_le_two_four (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    volSq π x * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π)) - exclMomentSq π x y ≤
      2 * T3 π x y * (meanVol π x) ^ 4 + 4 * T4 π x y * (meanVol π x) ^ 3 :=
  I417_p21_of_diagram π hπ x y 2 4 (excess_le_two_four π hπ x y hχ)

end PercLib.CriticalLRP.I417Example
