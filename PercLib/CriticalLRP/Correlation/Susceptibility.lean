/-
# The cluster-volume susceptibility in the canonical model

This is the bridge between the native `chi = ∑' tau` theorem and the
`CountableProduct` notation used by the long-range covariance modules.
-/
module

public import PercLib.CriticalLRP.Correlation.TwoClusterGap
public import PercLib.Percolation.Bond.Susceptibility

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory

open scoped ENNReal NNReal

variable {V : Type*} [Countable V]

/-- The expected extended cluster volume is the sum of the connection
probabilities from the root. -/
theorem lintegral_clusterVol_eq_tsum_connSet (π : Sym2 V → unitInterval) (o : V) :
    (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) = ∑' y : V, (edgeMeasure π) (connSet o y) := by
  change (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ∂(edgeMeasure π)) =
    ∑' y : V, Percolation.Bond.tau π o y
  exact Percolation.Bond.chi_eq_tsum_tau π o

end PercLib.CriticalLRP
