/- Integrated from `.scratch/case3-split-draft/DirectEventually.lean` at production base
`bcc1ad841c2aaf6a8d1dc28d5bf7cd885a304d65`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Eventually

/-! # Direct Case-3 ratio limits with eventual inputs -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-- `case3_hAmid_of_i421` at a fixed index, with its finite-window and moment
hypotheses required only eventually. The comparison against `biasTarget` is an
explicit eventual input here; the full family below derives it by log-convexity. -/
theorem case3_hAmid_of_i421_eventually (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (hcard : ∀ᶠ r in atTop, 0 < (B r).card)
    (hhom : ∀ᶠ r in atTop, ∀ y ∈ B r,
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ᶠ r in atTop, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ᶠ r in atTop, I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ᶠ r in atTop, ∀ y ∈ B r, I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    (hstep1 : Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p) atTop (𝓝 0))
    {c3 c4 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r)
    (hc4 : 0 < c4)
    (hcmp : ∀ᶠ r in atTop, c4 * biasTarget (momOf π o 1 r) (momOf π o 2 r) p
      ≤ momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hm1 : ∀ᶠ r in atTop, 0 < momOf π o 1 r := by
    filter_upwards [hM1] with r hr
    exact momR_pos hr
  have hT : ∀ᶠ r in atTop, 0 < biasTarget (momOf π o 1 r) (momOf π o 2 r) p := by
    filter_upwards [hgm, hm1] with r hgmr hm1r
    exact biasTarget_pos hp hm1r hc3 hgmr
  have hXpos : ∀ᶠ r in atTop, 0 < momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r := by
    filter_upwards [hT, hcmp] with r hTr hcmpr
    exact lt_of_lt_of_le (mul_pos hc4 hTr) hcmpr
  have hD0 : ∀ᶠ r in atTop, 0 ≤ discR (π r) o (ℓ + 1) (p - ℓ) (B r) := by
    filter_upwards [hcard, hMa, hMb] with r hc hma hmb
    exact discR_nonneg (hπ r) 𝓔 h𝓔mono h𝓔 hc hma hmb
  have hstep2 : Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r)) atTop (𝓝 0) :=
    tendsto_div_zero_of_le_mul hstep1 hD0 hT hc4 hcmp
  have hcardne : ∀ᶠ r in atTop, ((B r).card : ℝ) ≠ 0 := by
    filter_upwards [hcard] with r hc
    have hc' : 0 < (B r).card := hc
    exact_mod_cast ne_of_gt hc'
  have hrel : ∀ᶠ r in atTop, discR (π r) o (ℓ + 1) (p - ℓ) (B r) =
      momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r -
        (I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) / ballCard B r) := by
    filter_upwards [hcardne, hhom] with r hc hh
    have hP := I420Case1.prodFactor_toReal (π r) o (ℓ + 1) (p - ℓ) (B r) hh
    rw [discR, hP]
    simp only [ballCard, momOf, I420Case1.mixedExclR]
    field_simp
  have hne : ∀ᶠ r in atTop, momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r ≠ 0 :=
    hXpos.mono fun r h => h.ne'
  have hmain := tendsto_one_of_tendsto_div_sub hrel hstep2 hne
  refine hmain.congr' ?_
  filter_upwards [hcardne, hne] with r hc hne
  simp only [ballCard]
  field_simp

/-- The full direct Case-3 endpoint/middle-index pair from eventual split
polygon, tree, window and moment inputs. The denominator comparison is derived
with constant one by `MomentLogConvex`. -/
theorem case3_hAend_hAmid_split_eventually (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℕ → ℝ) (Bthree Btail : ℝ → ℝ)
    (hC : ∀ ℓ j, 0 ≤ C ℓ j) (hthree : Tendsto Bthree atTop (𝓝 0))
    (htail : Tendsto Btail atTop (𝓝 0))
    (hTree : ∀ (ℓ : ℕ), ℓ + 1 ≤ p → ∀ᶠ r in atTop,
      HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) (C ℓ))
    (hPoly : ∀ᶠ r in atTop, HasSplitPolygonBound (π r) o (B r) p (poly r) (Bthree r) (Btail r))
    (hcard : ∀ᶠ r in atTop, 0 < (B r).card)
    (hhom : ∀ᶠ r in atTop, ∀ (ℓ : ℕ), ℓ + 1 ≤ p → ∀ y ∈ B r,
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ᶠ r in atTop, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ᶠ r in atTop, ∀ ℓ : ℕ, ℓ ≤ p → I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ᶠ r in atTop, ∀ (ℓ : ℕ), ℓ + 1 ≤ p → ∀ y ∈ B r,
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hone : ∀ ℓ, ℓ + 1 ≤ p → Tendsto (fun r =>
      I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
        (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
    intro ℓ hℓ
    have hb1 : 1 ≤ ℓ + 1 := by omega
    have hb2 : 1 ≤ p - ℓ := by omega
    have hb3 : ℓ + 1 + (p - ℓ) = p + 1 := by omega
    have hstep1 := case3_i421_family_split_eventually π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega)
      hπ poly (C ℓ) Bthree Btail (hC ℓ) hthree htail (hTree ℓ hℓ) hPoly hcard hM1
      (hMa.mono fun r hr => hr ℓ (by omega)) (hMb.mono fun r hr => hr ℓ hℓ) hc3 hgm
    refine case3_hAmid_of_i421_eventually π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega) hπ hcard
      (hhom.mono fun r hr => hr ℓ hℓ) hM1 (hMa.mono fun r hr => hr ℓ (by omega))
      (hMb.mono fun r hr => hr ℓ hℓ) hstep1 hc3 hgm (c4 := 1) (by norm_num) ?_
    filter_upwards [hMa] with r hr
    have h := biasTarget_le_mul_momOf (p := p) (a := ℓ + 1) (b := p - ℓ) π o hp
      hb1 hb2 hb3 r (powMomentAt_ne_top_of_le_succ hr)
    simpa only [one_mul] using h
  exact ⟨hone 0 (by omega), fun ℓ h1 h2 => hone ℓ (by omega)⟩

end I420Case3

end PercLib.CriticalLRP
