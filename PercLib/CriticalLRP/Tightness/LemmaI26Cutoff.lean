/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.6 for the paper's cut-off measures `P_{β,r}`

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and Lemma I.2.6.

Definition I.1.5 defines the cut-off kernel `J_r(x,y) = 1(x ≠ y, ‖x-y‖ ≤ r) ∫_{‖x-y‖}^r |J'|`
and writes `P_{β,r}`, `E_{β,r}` for the law of long-range percolation with kernel `J_r` at
parameter `β`.  In this development that kernel is `CutoffKernel.cutoffSymKernel K d r`
(with `K = J` the profile and `∫_{‖x-y‖}^r |J'| = cutoffProfile K r ‖x-y‖`), and the law is
`longRangeMeasure (cutoffSymKernel K d r) (cutoffSymKernel_nonneg hK hr) β`.

The only input needed from translation invariance of the law is
`CutoffKernel.cutoffSymKernel_shift`, combined with `edgeMeasure_shift_invariant`; this is
discharged inside `lemma_I_2_6_longRange`.  So Lemma I.2.6 for `P_{β,r}` is unconditional here:
no subcriticality, no tail hypothesis, no a.e. finiteness of clusters.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging
public import PercLib.CriticalLRP.MassTransportI41

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

variable {d : ℕ}

/-- **Lemma I.2.6 for the cut-off law `P_{β,r}`**: for every profile `K` that is antitone and
nonnegative on `(0,∞)` and every `r > 0`, `β ≥ 0`,

  `E_{β,r}|K|^p ≥ (M_{β,r}-1)^{p+1}/(e|B_r|)`,

where `M_{β,r}` is the edian of `|K_max(B_r)|` under `P_{β,r}`, `|B_r| = (2n+1)^d` for the
natural radius `n`, and `p > 0` (the paper states `p ≥ 1`). -/
theorem lemma_I_2_6_cutoff (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (r : ℝ) (hr : 0 < r) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal ((((edianMaxVol (longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
              (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) (FiniteVolume.box d n)
            (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1)) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ))) ≤
      ∫⁻ ω, clusterVol ω 0 ^ p ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) :=
  lemma_I_2_6_longRange (CutoffKernel.cutoffSymKernel K d r)
    (fun a e => CutoffKernel.cutoffSymKernel_shift K d r a e)
    (CutoffKernel.cutoffSymKernel_nonneg hK hr) β n hp

/-- **Lemma I.2.6 for `P_{β,r}` in the paper's real-expectation form**, under the finiteness of
the `p`-th moment (automatic for the subcritical cut-off laws used in the paper). -/
theorem lemma_I_2_6_cutoff_real_integral (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (r : ℝ) (hr : 0 < r) (β : NNReal) (n : ℕ) {p : ℝ} (hp : 0 < p)
    (hfin : ∫⁻ ω, clusterVol ω 0 ^ p ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) ≠ ⊤) :
    ((edianMaxVol (longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) (FiniteVolume.box d n)
        (exists_edianMaxVol _) : ℝ) - 1) ^ (p + 1) /
        (Real.exp 1 * ((FiniteVolume.box d n).card : ℝ)) ≤
      ∫ ω, (clusterVol ω 0).toReal ^ p ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) :=
  lemma_I_2_6_real_integral (longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    (fun a => edgeMeasure_shift_invariant (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
      (bernoulliEdgeProb_shift (fun a e => CutoffKernel.cutoffSymKernel_shift K d r a e)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) a)
    n hp hfin

end Percolation

end PercLib.CriticalLRP
