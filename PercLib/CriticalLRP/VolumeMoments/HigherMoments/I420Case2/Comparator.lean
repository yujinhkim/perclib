/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The `= o(|B_r| (M₂/M₁)^{p-1} M₁²)` form of the Case 2 decorrelation bound
(`(I.4.21)` with the
normalized target), plus the relation between `interVol` and the production quantity
`maxClusterInBall` that defines the quantile `M_r` used in the `Hydro` hypothesis.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Assembly

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

namespace PercLib.CriticalLRP.Analysis.I420Case2

/-- `|K ∩ B_r|` is dominated by the largest cluster volume in the ball, the quantity
defining `M_r`. -/
theorem interVol_le_maxClusterInBall (M : Orchestration.SourceModelData) (r : ℝ)
    (ω : Config M.V) : interVol M r ω ≤ M.maxClusterInBall r ω :=
  le_iSup (fun x : M.V => clusterVolIn ω x (M.ball r)) (0 : M.V)

/-- The Cauchy–Schwarz/tightness/(I.4.19) bound is `o` of the normalized target, in eventual-`η`
form.  No moment input (`hI419`, `hTight`) is needed here: those only identify the joint moment. -/
theorem jointUpper_eventually_le (M : Orchestration.SourceModelData) (p : ℕ) (hp : 1 ≤ p)
    (m₁ m₂ : ℝ → ℝ) (C γ A A' c : ℝ)
    (hH : Orchestration.Hydro M) (hd : (M.d : ℝ) = 3 * M.α)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hA : 0 < A) (hA' : 0 < A') (hc : 0 < c)
    (hdrive : ∀ᶠ r : ℝ in atTop, m₂ r / m₁ r ≤ γ * m₁ r ^ 2)
    (hdrive0 : ∀ᶠ r : ℝ in atTop, 0 ≤ m₂ r / m₁ r)
    (hm₁hi : ∀ᶠ r : ℝ in atTop, m₁ r ≤ A * r ^ M.α)
    (hm₁lo : ∀ᶠ r : ℝ in atTop, A' * r ^ M.α ≤ m₁ r)
    (hm₁pos : ∀ᶠ r : ℝ in atTop, 0 < m₁ r)
    (hball : ∀ᶠ r : ℝ in atTop, c * r ^ (M.d : ℝ) ≤ ballCard M r) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop,
      jointUpper M p C m₁ m₂ r ≤ η * normTarget M p m₁ m₂ r := by
  intro η hη
  obtain ⟨ε, hε0, hεK⟩ := exists_eps_sqrt_mul_lt
    (K := Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) (η := η) (by positivity) hη
  have hMrle := Mr_eventually_le M hH hε0
  filter_upwards [hdrive, hdrive0, hm₁hi, hm₁lo, hm₁pos, hball, hMrle,
    eventually_ge_atTop (1 : ℝ)] with r hd1 hd0 hhi hlo hpos hb hMr hr1
  have h3 : 3 * M.α ≤ (M.d : ℝ) := by rw [hd]
  have hbc : (0 : ℝ) ≤ ballCard M r :=
    le_trans (le_of_lt (mul_pos hc (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < r) _))) hb
  have hN : (0 : ℝ) ≤ normTarget M p m₁ m₂ r := by
    rw [normTarget]
    exact mul_nonneg (mul_nonneg hbc (pow_nonneg hd0 (p - 1))) (by positivity)
  have hmain := sqrt_bound_le (p := p) (α := M.α) (d := (M.d : ℝ)) (C := C) (γ := γ) (A := A)
    (A' := A') (c := c) (ε := ε) (b := ballCard M r) (s := m₂ r / m₁ r) (m := m₁ r)
    (Mr := (M.Mr r : ℝ)) (r := r) hp h3 hr1 hC hγ (le_of_lt hA) hA' hc (le_of_lt hε0)
    hd0 hpos (by positivity) hd1 hhi hlo (by simpa using hMr) (by simpa using hb)
  have hfin : (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
      * normTarget M p m₁ m₂ r ≤ η * normTarget M p m₁ m₂ r :=
    by nlinarith [hεK, hN]
  calc jointUpper M p C m₁ m₂ r
      ≤ (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
          * normTarget M p m₁ m₂ r := by
        simpa only [jointUpper, i419Factor, tightFactor, normTarget] using hmain
    _ ≤ η * normTarget M p m₁ m₂ r := hfin

/-- **The comparator**: the Cauchy–Schwarz bound on `E_r[|K|^{p+1}|K ∩ B_r|]` is
`o(|B_r| (M₂/M₁)^{p-1} M₁²)` — estimate (I.4.21) with the normalized target of
Proposition I.4.20,
case `d = 3α`. -/
theorem jointUpper_isLittleO (M : Orchestration.SourceModelData) (p : ℕ) (hp : 1 ≤ p)
    (m₁ m₂ : ℝ → ℝ) (C γ A A' c : ℝ)
    (hH : Orchestration.Hydro M) (hd : (M.d : ℝ) = 3 * M.α)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hA : 0 < A) (hA' : 0 < A') (hc : 0 < c)
    (hdrive : ∀ᶠ r : ℝ in atTop, m₂ r / m₁ r ≤ γ * m₁ r ^ 2)
    (hdrive0 : ∀ᶠ r : ℝ in atTop, 0 ≤ m₂ r / m₁ r)
    (hm₁hi : ∀ᶠ r : ℝ in atTop, m₁ r ≤ A * r ^ M.α)
    (hm₁lo : ∀ᶠ r : ℝ in atTop, A' * r ^ M.α ≤ m₁ r)
    (hm₁pos : ∀ᶠ r : ℝ in atTop, 0 < m₁ r)
    (hball : ∀ᶠ r : ℝ in atTop, c * r ^ (M.d : ℝ) ≤ ballCard M r) :
    jointUpper M p C m₁ m₂ =o[atTop] normTarget M p m₁ m₂ := by
  refine (isLittleO_iff_eventually_le ?_ ?_).mpr
    (jointUpper_eventually_le M p hp m₁ m₂ C γ A A' c hH hd hC hγ hA hA' hc hdrive hdrive0
      hm₁hi hm₁lo hm₁pos hball)
  · filter_upwards with r
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · filter_upwards [hdrive0, hm₁pos, hball, eventually_gt_atTop (0 : ℝ)] with r hd0 hpos hb hr0
    have hbc : (0 : ℝ) ≤ ballCard M r :=
      le_trans (le_of_lt (mul_pos hc (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < r) _))) hb
    rw [normTarget]
    exact mul_nonneg (mul_nonneg hbc (pow_nonneg hd0 (p - 1))) (by positivity)

end PercLib.CriticalLRP.Analysis.I420Case2
