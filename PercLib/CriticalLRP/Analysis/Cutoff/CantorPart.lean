/-
# The Cantor part of the cut-mass Stieltjes measure

`M.cutMassReal r = (M.cutMassAt r 0).toReal` is the source's `χ(r)`.  At campaign HEAD the
real-variable side of `χ` is known: `χ` is monotone on a window with finite mass at the right
endpoint (`cutMassReal_mono`), a.e. differentiable (`cutMassReal_ae_differentiableWithinAt`), its
derivative is interval integrable (`intervalIntegrable_deriv_cutMassReal`), and `∫ χ' ≤ χ(b) - χ(a)`
(`integral_deriv_cutMassReal_le_sub`).  What was missing is the *exact* defect in that inequality.

This file supplies it.  For a window `a ≤ b` with `0 < a` and finite mass at a strictly larger
radius `b' > b` we build the Stieltjes measure `μ` of `χ` (via the radius-clamped cut mass, which is
globally monotone and continuous) and prove the Lebesgue decomposition of the increment

  `χ(b) - χ(a) = (μ.singularPart volume)(Ioc a b) + ∫_a^b χ'`

(`cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral`), the `ℝ≥0∞` form
(`cutMassReal_ofReal_sub_eq_singularPart_add_lintegral_deriv`), and the resulting criterion

  `∫_a^b χ' = χ(b) - χ(a)  ↔  (μ.singularPart volume)(Ioc a b) = 0`

(`cutMassReal_intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero`).  Absolute continuity of `χ`
forces the vanishing (`cutMassReal_singularPart_eq_zero_of_absolutelyContinuousOn`).

Moreover the Cantor part is atomless (`cutMassCantorPart_singleton_eq_zero`), so the defect is
neither a jump nor an absolutely continuous remainder: it is a purely singular-continuous (Cantor)
measure and can be accounted for neither by the locally finite corner set nor by any countable set
of radii.

The Cantor part is canonical on a subwindow (`cutMassCantorPart_Ioc_congr`): it does not depend on
which enclosing window the clamped Stieltjes function was built from, so it is a genuine measure of
the increment.

Consequently the residual input of every "mass transport" / cutoff-ODE identity for `χ` is exactly
the vanishing of the Cantor part `M.cutMassCantorPart` of this Stieltjes measure: the a.e. flux
identity `χ' = F` is *not* by itself an increment identity, and the difference is that measure.  The
flux form `cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral_of_ae_deriv` states the
decomposition for an arbitrary a.e. representative `F` of `χ'`, so a flux computation can be
inserted without any further real analysis.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CantorPart.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.Analysis.MonotoneStieltjes

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The clamped cut mass and its Stieltjes function -/

theorem cutMassStieltjesMeasure_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    M.cutMassStieltjesMeasure ha hab hbb' hfin (Ioc a b)
      = ENNReal.ofReal (M.cutMassReal b - M.cutMassReal a) := by
  have hb : (M.cutMassStieltjes ha hab hbb' hfin) b = M.cutMassReal b := by
    have h := M.clampedCutMass_eq (a := a) (b := b) (r := b) ⟨hab, le_rfl⟩
    exact h
  have haa : (M.cutMassStieltjes ha hab hbb' hfin) a = M.cutMassReal a :=
    M.clampedCutMass_eq (a := a) (b := b) (r := a) ⟨le_rfl, hab⟩
  rw [cutMassStieltjesMeasure, StieltjesFunction.measure_Ioc, hb, haa]

/-- On the window, the derivative of the Stieltjes function of the clamped cut mass agrees a.e.
with the derivative of `M.cutMassReal`. -/
theorem ae_deriv_clampedCutMass_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    ∀ᵐ x ∂volume, x ∈ Ioc a b →
      deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x = deriv M.cutMassReal x := by
  have hmem : ∀ᵐ x ∂volume, x ∈ Ioc a b → x ∈ Ioo a b := by
    filter_upwards [show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b from by
      rw [MeasureTheory.ae_iff]; simp] with x hx hxI
    exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩
  filter_upwards [hmem] with x hx hxI
  exact M.deriv_clampedCutMass (hx hxI)

/-! ## The Lebesgue decomposition of the cut-mass increment -/

/-- **Lebesgue decomposition of the cut-mass increment** (`ℝ≥0∞` form): the increment of `χ` over
`(a,b]` is the Cantor part of its Stieltjes measure plus the integral of the a.e. derivative. -/
theorem cutMassReal_ofReal_sub_eq_singularPart_add_lintegral_deriv {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    ENNReal.ofReal (M.cutMassReal b - M.cutMassReal a)
      = M.cutMassCantorPart ha hab hbb' hfin (Ioc a b)
        + ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv M.cutMassReal x) := by
  have h := UltraCriticalLRP.ofReal_sub_eq_singularPart_add_lintegral_deriv
    (M.cutMassStieltjes ha hab hbb' hfin) a b
  have hb : (M.cutMassStieltjes ha hab hbb' hfin) b = M.cutMassReal b :=
    M.clampedCutMass_eq (a := a) (b := b) (r := b) ⟨hab, le_rfl⟩
  have haa : (M.cutMassStieltjes ha hab hbb' hfin) a = M.cutMassReal a :=
    M.clampedCutMass_eq (a := a) (b := b) (r := a) ⟨le_rfl, hab⟩
  have hcongr : ∫⁻ x in Ioc a b, ENNReal.ofReal
        (deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x)
      = ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv M.cutMassReal x) := by
    refine lintegral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mpr
      (M.ae_deriv_clampedCutMass_eq ha hab hbb' hfin)] with x hx
    rw [hx]
  rw [hb, haa, hcongr] at h
  exact h

/-- The real integral of the a.e. derivative of `χ` is the `toReal` of its `ℝ≥0∞`-integral. -/
theorem cutMassReal_toReal_lintegral_deriv_eq_intervalIntegral {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv M.cutMassReal x)).toReal
      = ∫ x in a..b, deriv M.cutMassReal x := by
  have habs := UltraCriticalLRP.toReal_lintegral_ofReal_deriv_eq_intervalIntegral
    (M.cutMassStieltjes ha hab hbb' hfin) hab
  have h1 : ∫⁻ x in Ioc a b, ENNReal.ofReal
        (deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x)
      = ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv M.cutMassReal x) := by
    refine lintegral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mpr
      (M.ae_deriv_clampedCutMass_eq ha hab hbb' hfin)] with x hx
    rw [hx]
  have h2 : ∫ x in a..b, deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x
      = ∫ x in a..b, deriv M.cutMassReal x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [M.ae_deriv_clampedCutMass_eq ha hab hbb' hfin] with x hx hxI
    exact hx hxI
  change (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv M.cutMassReal x)).toReal
      = ∫ x in a..b, deriv M.cutMassReal x
  rw [← h1, habs, h2]

/-- **Real form of the Lebesgue decomposition**: the increment of `χ` is the Cantor part of its
Stieltjes measure plus the integral of its a.e. derivative. -/
theorem cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    M.cutMassReal b - M.cutMassReal a
      = (M.cutMassCantorPart ha hab hbb' hfin (Ioc a b)).toReal
        + ∫ x in a..b, deriv M.cutMassReal x := by
  have h := UltraCriticalLRP.sub_eq_singularPart_toReal_add_intervalIntegral
    (M.cutMassStieltjes ha hab hbb' hfin) hab
  have hb : (M.cutMassStieltjes ha hab hbb' hfin) b = M.cutMassReal b :=
    M.clampedCutMass_eq (a := a) (b := b) (r := b) ⟨hab, le_rfl⟩
  have haa : (M.cutMassStieltjes ha hab hbb' hfin) a = M.cutMassReal a :=
    M.clampedCutMass_eq (a := a) (b := b) (r := a) ⟨le_rfl, hab⟩
  have h2 : ∫ x in a..b, deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x
      = ∫ x in a..b, deriv M.cutMassReal x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [M.ae_deriv_clampedCutMass_eq ha hab hbb' hfin] with x hx hxI
    exact hx hxI
  rw [hb, haa, h2] at h
  exact h

/-- **The mass-transport / FTC criterion for the cut mass**: the fundamental theorem of calculus
`∫_a^b χ' = χ(b) - χ(a)` holds exactly when the Cantor part of the Stieltjes measure of `χ`
vanishes on `(a,b]`. -/
theorem cutMassReal_intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    ∫ x in a..b, deriv M.cutMassReal x = M.cutMassReal b - M.cutMassReal a
      ↔ M.cutMassCantorPart ha hab hbb' hfin (Ioc a b) = 0 := by
  have habs := UltraCriticalLRP.intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero
    (M.cutMassStieltjes ha hab hbb' hfin) hab
  have hb : (M.cutMassStieltjes ha hab hbb' hfin) b = M.cutMassReal b :=
    M.clampedCutMass_eq (a := a) (b := b) (r := b) ⟨hab, le_rfl⟩
  have haa : (M.cutMassStieltjes ha hab hbb' hfin) a = M.cutMassReal a :=
    M.clampedCutMass_eq (a := a) (b := b) (r := a) ⟨le_rfl, hab⟩
  have h2 : ∫ x in a..b, deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) x
      = ∫ x in a..b, deriv M.cutMassReal x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [M.ae_deriv_clampedCutMass_eq ha hab hbb' hfin] with x hx hxI
    exact hx hxI
  rw [hb, haa, h2] at habs
  exact habs

/-- Absolute continuity of the cut mass forces the Cantor part of its Stieltjes measure to vanish
on the window. -/
theorem cutMassReal_singularPart_eq_zero_of_absolutelyContinuousOn {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤)
    (hac : AbsolutelyContinuousOnInterval M.cutMassReal a b) :
    M.cutMassCantorPart ha hab hbb' hfin (Ioc a b) = 0 := by
  refine (M.cutMassReal_intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero
    ha hab hbb' hfin).mp ?_
  exact hac.integral_deriv_eq_sub

/-- **The decomposition with an arbitrary a.e. flux `F`**: if `F` represents the a.e. derivative of
`χ` on the window (`IsFluxOn` in the informal language of the campaign), then
`χ(b) - χ(a) = Cantor part + ∫ F`.  In particular a flux computation alone cannot replace the
increment; the Cantor part is what is left over. -/
theorem cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral_of_ae_deriv {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤)
    {F : ℝ → ℝ}
    (hF : ∀ᵐ x ∂volume, x ∈ Ioo a b → F x = deriv M.cutMassReal x) :
    M.cutMassReal b - M.cutMassReal a
      = (M.cutMassCantorPart ha hab hbb' hfin (Ioc a b)).toReal
        + ∫ x in a..b, F x := by
  rw [M.cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral ha hab hbb' hfin]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le hab]
  filter_upwards [hF, show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b from by
    rw [MeasureTheory.ae_iff]; simp] with x hx hxne hxI
  exact (hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxne⟩).symm

/-! ## One Cantor measure serves every subwindow -/

/-- **Subwindow form of the decomposition.**  For `a ≤ x ≤ y ≤ b` the increment `χ(y) - χ(x)` is
the mass of the *same* Cantor part `M.cutMassCantorPart ha hab hbb' hfin` on `(x,y]` plus the
integral of `χ'` over `[x,y]`.  Since the measure does not depend on the subwindow, the
decomposition can be summed over any finite partition of `[a,b]`. -/
theorem cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral_subwindow {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤)
    {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    M.cutMassReal y - M.cutMassReal x
      = (M.cutMassCantorPart ha hab hbb' hfin (Ioc x y)).toReal
        + ∫ t in x..y, deriv M.cutMassReal t := by
  have h := UltraCriticalLRP.sub_eq_singularPart_toReal_add_intervalIntegral
    (M.cutMassStieltjes ha hab hbb' hfin) hxy
  have hyb : (M.cutMassStieltjes ha hab hbb' hfin) y = M.cutMassReal y :=
    M.clampedCutMass_eq (a := a) (b := b) (r := y) ⟨le_trans hx hxy, hy⟩
  have hxb : (M.cutMassStieltjes ha hab hbb' hfin) x = M.cutMassReal x :=
    M.clampedCutMass_eq (a := a) (b := b) (r := x) ⟨hx, le_trans hxy hy⟩
  have h2 : ∫ t in x..y, deriv (⇑(M.cutMassStieltjes ha hab hbb' hfin)) t
      = ∫ t in x..y, deriv M.cutMassReal t := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hxy]
    filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ y from by
      rw [MeasureTheory.ae_iff]; simp] with t htne htI
    have hty : t < y := lt_of_le_of_ne htI.2 htne
    have ht : t ∈ Ioo a b := ⟨lt_of_le_of_lt hx htI.1, lt_of_lt_of_le hty hy⟩
    exact M.deriv_clampedCutMass ht
  rw [hyb, hxb, h2] at h
  exact h

/-! ## The Cantor part is atomless -/

/-- The Stieltjes measure of the cut mass has no atoms inside the window: `χ` is continuous there
(`continuousOn_cutMassReal`), so the left and right limits agree with the value. -/
theorem cutMassStieltjesMeasure_singleton_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) (r : ℝ) :
    M.cutMassStieltjesMeasure ha hab hbb' hfin {r} = 0 := by
  have hcont : ContinuousAt (⇑(M.cutMassStieltjes ha hab hbb' hfin)) r :=
    (M.clampedCutMass_continuous ha hab hbb' hfin).continuousAt
  rw [cutMassStieltjesMeasure, StieltjesFunction.measure_singleton,
    hcont.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- **The Cantor part of the cut-mass Stieltjes measure is atomless** on the window.  Together with
`cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral` this says that the defect in the
mass-transport identity is neither a jump nor an absolutely continuous remainder: it is a purely
singular-continuous (Cantor) measure, so it cannot be accounted for by the locally finite corner
set or by any countable set of radii. -/
theorem cutMassCantorPart_singleton_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) (r : ℝ) :
    M.cutMassCantorPart ha hab hbb' hfin {r} = 0 := by
  have hle : (M.cutMassStieltjesMeasure ha hab hbb' hfin).singularPart volume
      ≤ M.cutMassStieltjesMeasure ha hab hbb' hfin :=
    Measure.singularPart_le _ _
  have h0 := M.cutMassStieltjesMeasure_singleton_eq_zero ha hab hbb' hfin r
  refine le_antisymm ?_ (by simp)
  calc M.cutMassCantorPart ha hab hbb' hfin {r}
      = (M.cutMassStieltjesMeasure ha hab hbb' hfin).singularPart volume {r} := rfl
    _ ≤ M.cutMassStieltjesMeasure ha hab hbb' hfin {r} := hle {r}
    _ = 0 := h0


/-- The Cantor part of a subwindow is never `⊤` (its mass is bounded by the finite increment). -/
theorem cutMassCantorPart_Ioc_ne_top {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {b' : ℝ}
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y)
    (hy : y ≤ b) : M.cutMassCantorPart ha hab hbb' hfin (Ioc x y) ≠ ⊤ := by
  have hval : M.cutMassStieltjesMeasure ha hab hbb' hfin (Ioc x y)
      = ENNReal.ofReal (M.cutMassReal y - M.cutMassReal x) := by
    rw [cutMassStieltjesMeasure, StieltjesFunction.measure_Ioc,
      show (M.cutMassStieltjes ha hab hbb' hfin) y = M.cutMassReal y from
        M.clampedCutMass_eq (a := a) (b := b) (r := y) ⟨le_trans hx hxy, hy⟩,
      show (M.cutMassStieltjes ha hab hbb' hfin) x = M.cutMassReal x from
        M.clampedCutMass_eq (a := a) (b := b) (r := x) ⟨hx, le_trans hxy hy⟩]
  have hle : (M.cutMassStieltjesMeasure ha hab hbb' hfin).singularPart volume
      ≤ M.cutMassStieltjesMeasure ha hab hbb' hfin := Measure.singularPart_le _ _
  exact ne_top_of_le_ne_top (b := M.cutMassStieltjesMeasure ha hab hbb' hfin (Ioc x y))
    (hval ▸ ENNReal.ofReal_ne_top) (hle (Ioc x y))


/-! ## The Cantor part is canonical on a subwindow -/

/-- **The Cantor part does not depend on the enclosing window.**  If `[x,y]` lies in two windows
`[a,b]` and `[a',b']` on which the cut mass is finite, the Cantor part of the increment over
`(x,y]` is the same.  Hence `M.cutMassCantorPart` is a genuine measure of the increment, not an
artefact of the clamping window: the mass-transport identity on `[x,y]` holds iff this canonical
measure vanishes there. -/
theorem cutMassCantorPart_Ioc_congr {a b a' b' x y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {b₁ : ℝ} (hb₁ : b < b₁) (hf₁ : M.cutMassAt b₁ 0 ≠ ⊤)
    (ha' : 0 < a') (hab' : a' ≤ b') {b₂ : ℝ} (hb₂ : b' < b₂) (hf₂ : M.cutMassAt b₂ 0 ≠ ⊤)
    (hx : max a a' ≤ x) (hxy : x ≤ y) (hy : y ≤ min b b') :
    M.cutMassCantorPart ha hab hb₁ hf₁ (Ioc x y)
      = M.cutMassCantorPart ha' hab' hb₂ hf₂ (Ioc x y) := by
  have hx1 : a ≤ x := le_trans (le_max_left a a') hx
  have hx2 : a' ≤ x := le_trans (le_max_right a a') hx
  have hy1 : y ≤ b := le_trans hy (min_le_left b b')
  have hy2 : y ≤ b' := le_trans hy (min_le_right b b')
  have h1 := M.cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral_subwindow
    ha hab hb₁ hf₁ hx1 hxy hy1
  have h2 := M.cutMassReal_sub_eq_singularPart_toReal_add_intervalIntegral_subwindow
    ha' hab' hb₂ hf₂ hx2 hxy hy2
  have hreal : (M.cutMassCantorPart ha hab hb₁ hf₁ (Ioc x y)).toReal
      = (M.cutMassCantorPart ha' hab' hb₂ hf₂ (Ioc x y)).toReal := by linarith
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hreal with h | h | h
  · exact h
  · exact absurd h.2 (M.cutMassCantorPart_Ioc_ne_top ha' hab' hb₂ hf₂ hx2 hxy hy2)
  · exact absurd h.1 (M.cutMassCantorPart_Ioc_ne_top ha hab hb₁ hf₁ hx1 hxy hy1)


end SourceModelData

end PercLib.CriticalLRP.Orchestration
