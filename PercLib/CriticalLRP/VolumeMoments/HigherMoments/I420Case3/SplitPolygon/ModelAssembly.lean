/- Integrated from `.scratch/case3-split-draft/ModelAssembly.lean` at production base
`33a88a132b440224d63869caa28e7f10dc46e390`, using the accepted canonical bridge. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Model
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Eventually
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Bridge

/-! # Canonical cutoff assembly from near/far and split polygon estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- The normalized Case-3 error at the canonical cutoff family, from the proved
I.4.17 tree expansion, the genuine near/far averaged threefold bound and the
higher-depth polygon estimate.

The remaining analytical assumptions are the first-moment asymptotic `hP`, the
finite triangle `hTri`, decay of the chosen near/far tail and cardinality ratio,
decay of the power-rescaled triangle tails, moment finiteness and non-degeneracy,
and the second-moment lower comparison `hgm`. No vanishing uniform polygon factor
is assumed. -/
theorem case3_i421_cutPoly_near_far (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    (B s : ℝ → Finset M.V) (R : ℝ → ℝ)
    (hcard : ∀ r : ℝ, 1 ≤ r → 0 < (B r).card)
    (hfar : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ B r, y ∉ s r → R r ≤ M.S.dist 0 y)
    (hTail : Tendsto (fun r => (M.nablaTail (R r)).toReal) atTop (𝓝 0))
    (hCardRatio : Tendsto (fun r => ((s r).card : ℝ) / ((B r).card : ℝ)) atTop (𝓝 0))
    (hNab : ∀ c : ℝ, 0 < c →
      Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0))
    (hMa : ∀ r : ℝ, 1 ≤ r → I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    (hMb : ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ B r,
      I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ) (B r) /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hSplit⟩ := exists_hasSplitPolygonBound_cutPoly_near_far M hP hTri
  obtain ⟨c₀, hc₀, hχall⟩ := AuditM2.cutMassAt_ne_top_of_hP M hP
  let Bthree : ℝ → ℝ := fun r => (M.nablaTail (R r)).toReal +
    (((s r).card : ℝ) / ((B r).card : ℝ)) * M.triSelf
  let Btail : ℝ → ℝ := fun r => C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))
  have hthree : Tendsto Bthree atTop (𝓝 0) := tendsto_near_far_factor M B s R hTail hCardRatio
  have htail : Tendsto Btail atTop (𝓝 0) :=
    tendsto_rate_of_nablaTail M hc (hNab c hc)
  have hTree : ∀ᶠ r in atTop, HasTreeExpansion (M.cutProb r) (0 : M.V) (B r)
      (ℓ + 1) (p - ℓ) p (cutPoly M r)
        (fun j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
    exact AuditM2.hasTreeExpansion_cutPoly M r (hχall r hrpos) (B r) hℓ
  have hPoly : ∀ᶠ r in atTop, HasSplitPolygonBound (M.cutProb r) (0 : M.V) (B r) p
      (cutPoly M r) (Bthree r) (Btail r) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact hSplit hp hr (B r) (s r) (hcard r hr) (hfar r hr)
  have hev : ∀ᶠ r : ℝ in atTop, 1 ≤ r := eventually_ge_atTop 1
  have hcardEv : ∀ᶠ r in atTop, 0 < (B r).card := hev.mono hcard
  have hM1 : ∀ᶠ r in atTop, I420Case1.powMomentAt (M.cutProb r) 1 (0 : M.V) ≠ ⊤ := by
    filter_upwards [hev] with r hr
    rw [powMomentAt_cutProb_one M r]
    exact hχall r (lt_of_lt_of_le one_pos hr)
  have hMaEv : ∀ᶠ r in atTop, I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ :=
    hev.mono hMa
  have hMbEv : ∀ᶠ r in atTop, ∀ y ∈ B r, I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ :=
    hev.mono hMb
  refine ⟨c, C, hc, hC, ?_⟩
  exact case3_i421_family_split_eventually (fun r => M.cutProb r) (0 : M.V) B 𝓔 h𝓔mono h𝓔
    p ℓ hp (fun r e => AuditM2.cutProb_lt_one M r e) (fun r => cutPoly M r)
    (fun j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) Bthree Btail
    (fun j => AuditM1.composedCoeff_nonneg (ℓ + 1) (p - ℓ) j) hthree htail hTree hPoly
    hcardEv hM1 hMaEv hMbEv hc3 hgm

#print axioms case3_i421_cutPoly_near_far

end I420Case3

end PercLib.CriticalLRP
