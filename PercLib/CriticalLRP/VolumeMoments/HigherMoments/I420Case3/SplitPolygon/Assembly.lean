/- Integrated from `.scratch/case3-split-draft/Assembly.lean` at production base
`1266415364a0ad5f96cb689b36fbed1778a2af1f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.MomentLogConvex.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.TreeInterface

/-! # Case 3 asymptotics from split polygon rates and positive tree exponents -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-- The normalized Case-3 error tends to zero when both the averaged threefold
factor and the higher-depth tail factor do. This does not assert that either
rate is available for a particular model. -/
theorem case3_i421_family_split (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) (Bthree Btail : ℝ → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hthree : Tendsto Bthree atTop (𝓝 0))
    (htail : Tendsto Btail atTop (𝓝 0))
    (hTree : ∀ r, HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) C)
    (hPoly : ∀ r, HasSplitPolygonBound (π r) o (B r) p (poly r) (Bthree r) (Btail r))
    (hcard : ∀ r, 0 < (B r).card)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ r, I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (y : V), y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p) atTop (𝓝 0) := by
  have hsum : Tendsto (fun r => Bthree r + Btail r) atTop (𝓝 0) := by
    simpa using hthree.add htail
  have hbound : ∀ᶠ r in atTop, discR (π r) o (ℓ + 1) (p - ℓ) (B r) ≤
      coeffSum C p * (Bthree r + Btail r) * momOf π o 1 r ^ (2 * p) := by
    filter_upwards with r
    exact discR_le_splitPolygon (hπ r) 𝓔 h𝓔mono h𝓔 hp hC (hTree r) (hPoly r)
      (hcard r) (hM1 r) (hMa r) (hMb r)
  have hD0 : ∀ᶠ r in atTop, 0 ≤ discR (π r) o (ℓ + 1) (p - ℓ) (B r) := by
    filter_upwards with r
    exact discR_nonneg (hπ r) 𝓔 h𝓔mono h𝓔 (hcard r) (hMa r) (hMb r)
  have hB0 : ∀ᶠ r in atTop, 0 ≤ Bthree r + Btail r :=
    Eventually.of_forall fun r => add_nonneg (hPoly r).nonneg_three (hPoly r).nonneg_tail
  have hm1 : ∀ᶠ r in atTop, 0 < momOf π o 1 r :=
    Eventually.of_forall fun r => momR_pos (hM1 r)
  exact tendsto_div_biasTarget_zero hp (Finset.sum_nonneg fun j _ => hC j) hc3 hD0
    hbound hB0 hsum hm1 hgm

/-- Case 3 with an averaged threefold rate, a separate higher-depth tail rate,
and the tree input only at positive second exponents. The conclusion is exactly
the endpoint and middle-index pair used by the second induction. -/
theorem case3_hAend_hAmid_split (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℕ → ℝ) (Bthree Btail : ℝ → ℝ)
    (hC : ∀ ℓ j, 0 ≤ C ℓ j) (hthree : Tendsto Bthree atTop (𝓝 0))
    (htail : Tendsto Btail atTop (𝓝 0))
    (hTree : ∀ (r : ℝ) (ℓ : ℕ), ℓ + 1 ≤ p →
      HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) (C ℓ))
    (hPoly : ∀ r, HasSplitPolygonBound (π r) o (B r) p (poly r) (Bthree r) (Btail r))
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ + 1 ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p →
      I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ + 1 ≤ p → y ∈ B r →
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
    have hℓp : ℓ ≤ p := by omega
    have hb1 : 1 ≤ ℓ + 1 := by omega
    have hb2 : 1 ≤ p - ℓ := by omega
    have hb3 : ℓ + 1 + (p - ℓ) = p + 1 := by omega
    refine case3_hAmid_of_i421 π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega) hπ hcard
      (fun r y hy => hhom r ℓ y hℓ hy) hM1 (fun r => hMa r ℓ hℓp)
      (fun r y hy => hMb r ℓ y hℓ hy) ?_ hc3 hgm (c4 := 1) (by norm_num) ?_
    · exact case3_i421_family_split π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega) hπ poly
        (C ℓ) Bthree Btail (hC ℓ) hthree htail (fun r => hTree r ℓ hℓ) hPoly hcard
        hM1 (fun r => hMa r ℓ hℓp) (fun r y hy => hMb r ℓ y hℓ hy) hc3 hgm
    · refine Eventually.of_forall fun r => ?_
      have h := biasTarget_le_mul_momOf (p := p) (a := ℓ + 1) (b := p - ℓ) π o hp
        hb1 hb2 hb3 r (powMomentAt_ne_top_of_le_succ (hMa r))
      simpa only [one_mul] using h
  exact ⟨hone 0 (by omega), fun ℓ h1 h2 => hone ℓ (by omega)⟩

/-- The split Case-3 wrapper with every required positive-exponent tree record
constructed from the proved summed form of Lemma I.4.17. Only first-moment row
constancy is needed for that tree input; higher-moment finiteness remains explicit
and the two polygon rates remain separate hypotheses. -/
theorem case3_hAend_hAmid_split_of_i417 {V : Type*} [Countable V] [DecidableEq V]
    (π : ℝ → Sym2 V → unitInterval) (o : V) (B : ℝ → Finset V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1) (Bthree Btail : ℝ → ℝ)
    (hthree : Tendsto Bthree atTop (𝓝 0)) (htail : Tendsto Btail atTop (𝓝 0))
    (hχ : ∀ (r : ℝ) (v : V), I417.meanVol (π r) v = I417.meanVol (π r) o)
    (hPoly : ∀ r, HasSplitPolygonBound (π r) o (B r) p
      (fun y j => I417Base.iterPow (fun u v => (edgeMeasure (π r)) (connSet u v)) j o y)
      (Bthree r) (Btail r))
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ + 1 ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p →
      I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ + 1 ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) :=
  case3_hAend_hAmid_split π o B 𝓔 h𝓔mono h𝓔 p hp hπ
    (fun r y j => I417Base.iterPow (fun u v => (edgeMeasure (π r)) (connSet u v)) j o y)
    (fun ℓ j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ))
    Bthree Btail (fun _ℓ j => AuditM1.composedCoeff_nonneg (_ℓ + 1) (p - _ℓ) j)
    hthree htail (fun r ℓ hℓ => AuditM1.hasTreeExpansion_family (p := p) (ℓ := ℓ)
      (π r) (hπ r) o (B r) hℓ (hχ r))
    hPoly hcard hhom hM1 hMa hMb hc3 hgm

end I420Case3

end PercLib.CriticalLRP
