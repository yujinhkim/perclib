/- Integrated from `.scratch/case3-split-draft/Eventually.lean` at production base
`33a88a132b440224d63869caa28e7f10dc46e390`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Assembly

/-! # Split Case-3 error bounds with eventual inputs -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-- `case3_i421_family_split` with every finite-window and moment input required
only eventually. Small radii are irrelevant to the limit and no patching of the
laws, windows, or polygon factors is needed. -/
theorem case3_i421_family_split_eventually (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) (Bthree Btail : ℝ → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hthree : Tendsto Bthree atTop (𝓝 0))
    (htail : Tendsto Btail atTop (𝓝 0))
    (hTree : ∀ᶠ r in atTop, HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) C)
    (hPoly : ∀ᶠ r in atTop, HasSplitPolygonBound (π r) o (B r) p (poly r) (Bthree r) (Btail r))
    (hcard : ∀ᶠ r in atTop, 0 < (B r).card)
    (hM1 : ∀ᶠ r in atTop, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ᶠ r in atTop, I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ᶠ r in atTop, ∀ y ∈ B r, I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p) atTop (𝓝 0) := by
  have hsum : Tendsto (fun r => Bthree r + Btail r) atTop (𝓝 0) := by
    simpa using hthree.add htail
  have hbound : ∀ᶠ r in atTop, discR (π r) o (ℓ + 1) (p - ℓ) (B r) ≤
      coeffSum C p * (Bthree r + Btail r) * momOf π o 1 r ^ (2 * p) := by
    filter_upwards [hTree, hPoly, hcard, hM1, hMa, hMb] with r hTr hPol hc hm1 hma hmb
    exact discR_le_splitPolygon (hπ r) 𝓔 h𝓔mono h𝓔 hp hC hTr hPol hc hm1 hma hmb
  have hD0 : ∀ᶠ r in atTop, 0 ≤ discR (π r) o (ℓ + 1) (p - ℓ) (B r) := by
    filter_upwards [hcard, hMa, hMb] with r hc hma hmb
    exact discR_nonneg (hπ r) 𝓔 h𝓔mono h𝓔 hc hma hmb
  have hB0 : ∀ᶠ r in atTop, 0 ≤ Bthree r + Btail r := by
    filter_upwards [hPoly] with r hPol
    exact add_nonneg hPol.nonneg_three hPol.nonneg_tail
  have hm1 : ∀ᶠ r in atTop, 0 < momOf π o 1 r := by
    filter_upwards [hM1] with r hm1
    exact momR_pos hm1
  exact tendsto_div_biasTarget_zero hp (Finset.sum_nonneg fun j _ => hC j) hc3 hD0
    hbound hB0 hsum hm1 hgm

end I420Case3

end PercLib.CriticalLRP
