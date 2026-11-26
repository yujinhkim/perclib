/-
Independent Ultramath work for Case 3 of Proposition I.4.20 — direction (B), the polygon
interface.

`I420Case3.HasPolygonBound (M.cutProb r) 0 B p (cutPoly M r) Bpoly` is proved here for the
*genuine* range-truncated matrix powers `cutPoly M r y j = T^j_{β_c,r}(0,y)` of `Defs.lean`,
from the existing production Lemma I.4.18 assembly
(`I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment`, valid for `ℓ ≥ 4`)
and the landed `ℓ = 3` constant bound (`I418C.source_polyK_three_le_triSelf`).

The honest factor is `max M.triSelf (C * (∇_{r^c} + r^{-c}))`; see
`one_le_Bpoly_of_hasPolygonBound` for the reason the constant `M.triSelf` cannot be dropped:
the diagonal entry `T^3_{β_c,r}(0,0) ≥ 1` forces every `Bpoly` of a `HasPolygonBound` whose
ball contains the origin to be at least `1`, so no *vanishing* factor is available through
this interface, and `no_vanishing_uniform_polygon_factor` records that as a theorem.

Remaining inputs, stated explicitly: `hP` (the Proposition I.4.2 first-moment asymptotic,
used only to make `χ = M.cutMassAt r 0` finite and `⪰ r^α`) and `hTri` (`∇ < ∞`, the
hypothesis of Lemma I.4.18).  The triangle condition `∇_{r^c} → 0` is *not* used and *not*
proved here: it is exactly what would be needed to make the `j ≥ 4` part of the factor
vanish.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Polygon

/-! # Cutoff polygon bounds and the nonvanishing uniform threefold corner -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open PercLib.CriticalLRP Orchestration

namespace CutPoly

variable (M : SourceModelData)

/-- **The `j ≥ 4` part of Lemma I.4.18 in `HasPolygonBound` form.**

This is the landed source assembly `I418C.source_polygon_bound_tail_cc` read through the
bridges of `Defs.lean`: for `4 ≤ j` the genuine cutoff polygon power is bounded by the
source's `C (∇_{r^c} + r^{-c}) χ^{j-3}`, with `χ = M.cutMassAt r 0` replaced by the
canonical-law first moment `I420Case1.powMomentAt (M.cutProb r) 1 0`. -/
theorem cutPoly_le_rate (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {j : ℕ}, 4 ≤ j → ∀ {r : ℝ}, 1 ≤ r → ∀ y : M.V,
      cutPoly M r y j ≤ ENNReal.ofReal (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))) *
        I420Case1.powMomentAt (M.cutProb r) 1 0 ^ (j - 3) := by
  obtain ⟨c, C, hc, hC, hb⟩ :=
    I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment M hP hTri
  obtain ⟨c₀, hc₀, hχu⟩ := I418C.ChiInput.exists_chi_lower_uniform M
    (I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP) hP
  refine ⟨c, C, hc, hC, ?_⟩
  intro j hj r hr y
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hχfin : M.cutMassAt r 0 ≠ ⊤ :=
    I418C.ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hrpos (hχu r hrpos)
  have hsrc : I418C.polyK (M.cutTwoPoint r) j 0 y
      ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))
        * ((M.cutMassAt r 0).toReal) ^ (j - 3) := (hb hj r hr y).2
  have hnn : (0 : ℝ) ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) :=
    mul_nonneg hC.le (by positivity)
  calc cutPoly M r y j
      = ENNReal.ofReal (I418C.polyK (M.cutTwoPoint r) j 0 y) := rfl
    _ ≤ ENNReal.ofReal (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))
          * ((M.cutMassAt r 0).toReal) ^ (j - 3)) := ENNReal.ofReal_le_ofReal hsrc
    _ = ENNReal.ofReal (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
          * ENNReal.ofReal (((M.cutMassAt r 0).toReal) ^ (j - 3)) :=
        ENNReal.ofReal_mul hnn
    _ = ENNReal.ofReal (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
          * (M.cutMassAt r 0) ^ (j - 3) := by
        rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hχfin]
    _ = ENNReal.ofReal (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
          * I420Case1.powMomentAt (M.cutProb r) 1 0 ^ (j - 3) := by
        rw [powMomentAt_cutProb_one M r]

end CutPoly

/-- **`I420Case3.HasPolygonBound` for the genuine cutoff matrix entries.**

For every `r ≥ 1` and every `Finset B` (the source's ball `B_r`, but the statement is
uniform in `B`, as in the interface), the polygon powers `T^j_{β_c,r}(0,·)`,
`j ∈ [3, p+2]`, satisfy the polygon bound with the explicit factor

`max ∇ (C (∇_{r^c} + r^{-c}))`,  i.e. `max M.triSelf (C * (∇_{r^c} + r^{-c}))`,

where `∇ = M.triSelf` is the uncut triangle (the `ℓ = 3` constant bound) and
`C (∇_{r^c} + r^{-c})` is the source's Lemma I.4.18 factor for `ℓ ≥ 4`.
The only hypotheses are the two source inputs: the first-moment asymptotic `hP` and
`hTri : ∇ < ∞`.

Nothing else is assumed: `hχfin` (`χ ≠ ⊤`) is *derived* from `hP`
(`I418C.ChiInput.exists_chi_lower_uniform` + `cutMassAt_ne_top_of_le_toReal`), not added. -/
theorem exists_hasPolygonBound_cutPoly (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {p : ℕ}, 1 ≤ p → ∀ {r : ℝ}, 1 ≤ r →
      ∀ B : Finset M.V,
        HasPolygonBound (M.cutProb r) (0 : M.V) B p (cutPoly M r)
          (max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))) := by
  obtain ⟨c, C, hc, hC, hb⟩ :=
    I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment M hP hTri
  obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
  obtain ⟨c₀, hc₀, hχu⟩ := I418C.ChiInput.exists_chi_lower_uniform M
    (I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP) hP
  refine ⟨c, C, hc, hC, ?_⟩
  intro p _hp r hr B
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hχfin : M.cutMassAt r 0 ≠ ⊤ :=
    I418C.ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hrpos (hχu r hrpos)
  have hrate : (0 : ℝ) ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) :=
    mul_nonneg hC.le (by positivity)
  have hnonneg : (0 : ℝ) ≤ max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))) :=
    le_trans ENNReal.toReal_nonneg (le_max_left _ _)
  refine ⟨hnonneg, ?_⟩
  intro y _hy j hj
  obtain ⟨h3, _⟩ := Finset.mem_Icc.mp hj
  rw [powMomentAt_cutProb_one M r]
  rcases eq_or_lt_of_le h3 with h3eq | h3lt
  · -- `j = 3`: the landed constant bound `T^3 ≤ ∇ = M.triSelf`
    obtain rfl : j = 3 := h3eq.symm
    rw [Nat.sub_self, pow_zero, mul_one]
    exact ENNReal.ofReal_le_ofReal
      ((I418C.source_polyK_three_le_triSelf M r hχfin hTri hB2 hB3 hlink y).trans
        (le_max_left _ _))
  · -- `4 ≤ j`: the source polygon estimate with the tail factor
    have h4 : 4 ≤ j := h3lt
    have hsrc : I418C.polyK (M.cutTwoPoint r) j 0 y
        ≤ max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
          * ((M.cutMassAt r 0).toReal) ^ (j - 3) :=
      ((hb h4 r hr y).2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    calc cutPoly M r y j
        = ENNReal.ofReal (I418C.polyK (M.cutTwoPoint r) j 0 y) := rfl
      _ ≤ ENNReal.ofReal (max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
            * ((M.cutMassAt r 0).toReal) ^ (j - 3)) := ENNReal.ofReal_le_ofReal hsrc
      _ = ENNReal.ofReal (max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))))
            * ENNReal.ofReal (((M.cutMassAt r 0).toReal) ^ (j - 3)) :=
          ENNReal.ofReal_mul hnonneg
      _ = ENNReal.ofReal (max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))))
            * (M.cutMassAt r 0) ^ (j - 3) := by
          rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hχfin]

/-- **The `j = 3` corner of `HasPolygonBound` cannot be made small.**

`T^3_{β_c,r}(0,0) ≥ 1` (`one_le_polyK_three_of_chi_ne_top`), hence any
`HasPolygonBound (M.cutProb r) 0 B p (cutPoly M r) Bpoly` whose ball contains the origin
satisfies `1 ≤ Bpoly`.  In particular the polygon factor of a `HasPolygonBound` on `B_r`
is never `o(1)`: the `j = 3` term of the tree expansion has to be absorbed by the constant
triangle value `∇`, not by `∇_{r^c} + r^{-c}`.

This is the precise sense in which the printed display of Lemma I.4.18 at `ℓ = 3`
(`sup_x T^3(0,x) ≤ C(∇_{r^c}+r^{-c})`, which would need to tend to `0`) is not available in
this interface: at `x = 0` its left-hand side is the diagonal threefold power, at least `1`. -/
theorem one_le_Bpoly_of_hasPolygonBound (M : SourceModelData) {r : ℝ}
    (hχ : M.cutMassAt r 0 ≠ ⊤) {p : ℕ} (hp : 1 ≤ p)
    {B : Finset M.V} (h0 : (0 : M.V) ∈ B) {Bpoly : ℝ}
    (h : HasPolygonBound (M.cutProb r) (0 : M.V) B p (cutPoly M r) Bpoly) :
    1 ≤ Bpoly := by
  have hj : (3 : ℕ) ∈ Finset.Icc 3 (p + 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hb := h.bound 0 h0 3 hj
  rw [powMomentAt_cutProb_one M r, Nat.sub_self, pow_zero, mul_one, cutPoly] at hb
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Bpoly := by
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (I418C.polyK (M.cutTwoPoint r) 3 0 0) :=
          ENNReal.ofReal_le_ofReal (one_le_polyK_three_of_chi_ne_top M r hχ)
      _ ≤ ENNReal.ofReal Bpoly := hb
  rw [← ENNReal.ofReal_one] at hone
  exact (ENNReal.ofReal_le_ofReal_iff h.nonneg).mp hone

/-- A sequence eventually `≥ 1` does not tend to `0`. -/
theorem not_tendsto_zero_of_one_le_eventually {f : ℝ → ℝ}
    (h : ∀ᶠ r : ℝ in atTop, 1 ≤ f r) : ¬ Tendsto f atTop (𝓝 0) := by
  intro hf
  have h10 : (1 : ℝ) ≤ 0 := ge_of_tendsto hf h
  norm_num at h10

/-- **The `j ≥ 4` part of the polygon factor vanishes iff the triangle tail does.**

`C * (∇_{r^c} + r^{-c}) → 0` as soon as `∇_{r^c} = (M.nablaTail (r^c)).toReal → 0` (and
`c > 0`, when `r^{-c} → 0` automatically).  So the *only* analytic input missing from a
vanishing (`j ≥ 4`) polygon factor is the triangle condition's tail decay
`∇_{r^c} → 0`; nothing about `χ` or the finite-cutoff susceptibility enters. -/
theorem tendsto_rate_of_nablaTail (M : SourceModelData) {c C : ℝ} (hc : 0 < c)
    (hnab : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))) atTop (𝓝 0) := by
  have hrpow : Tendsto (fun r : ℝ => r ^ (-c)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  simpa using ((hnab.add hrpow).const_mul C)

/-- **The honest polygon factor converges to the uncut triangle value `∇`.**

Under the triangle tail decay `∇_{r^c} → 0`, the factor
`max M.triSelf (C (∇_{r^c} + r^{-c}))` of `exists_hasPolygonBound_cutPoly` tends to
`M.triSelf = ∇`, not to `0`.  Together with `no_vanishing_uniform_polygon_factor` this
identifies the exact limitation of the polygon interface: the `j = 3` corner keeps the
factor at `∇ ≥ 1`. -/
theorem tendsto_polygonFactor (M : SourceModelData) {c C : ℝ} (hc : 0 < c)
    (hnab : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))))
      atTop (𝓝 M.triSelf) := by
  have hrate : Tendsto (fun r : ℝ => C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))
      atTop (𝓝 0) := tendsto_rate_of_nablaTail M hc hnab
  have h : Tendsto (fun r : ℝ => max M.triSelf (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))))
      atTop (𝓝 (max M.triSelf 0)) := tendsto_const_nhds.max hrate
  rwa [max_eq_left (show (0 : ℝ) ≤ M.triSelf from ENNReal.toReal_nonneg)] at h

/-- **No vanishing uniform polygon factor exists for the genuine cutoff matrix entries.**

If, for all large `r`, some `Bpoly r` satisfies `HasPolygonBound` on a ball containing the
origin (with any `p ≥ 1`), then `Bpoly r ≥ 1` eventually, so `Bpoly r ↛ 0`.  Consequently
`Bpoly → 0` — the requirement that turns Lemma I.4.18 into the Case 3 estimate
`(∇_{r^c}+r^{-c})(E|K|)^{2p}` — cannot be met by this interface at `j = 3`; what is needed
in addition is a polygon bound that excludes the diagonal pair `y = 0` (or a tree expansion
supported on `j ≥ 4`), which the current Case 3 interface does not provide. -/
theorem no_vanishing_uniform_polygon_factor (M : SourceModelData)
    (B : ℝ → Finset M.V) (bp : ℝ → ℝ)
    (hB : ∀ᶠ r : ℝ in atTop, (0 : M.V) ∈ B r)
    (hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (h : ∀ᶠ r : ℝ in atTop, ∃ p : ℕ, 1 ≤ p ∧
      HasPolygonBound (M.cutProb r) (0 : M.V) (B r) p (cutPoly M r) (bp r)) :
    ¬ Tendsto bp atTop (𝓝 0) := by
  refine not_tendsto_zero_of_one_le_eventually ?_
  filter_upwards [hB, hχ, h] with r h0 hfin ⟨p, hp, hb⟩
  exact one_le_Bpoly_of_hasPolygonBound M hfin hp h0 hb

/-- **No vanishing `HasPolygonBound` factor exists at all** (negation form).

Even allowing an arbitrary radius-dependent factor `bp` and an arbitrary order `p ≥ 1`,
if the ball contains the origin eventually then `HasPolygonBound` forces `bp r ≥ 1`, so
`bp` cannot tend to `0`.  This is the precise obstruction to deriving the Case 3 estimate
`⪯ (∇_{r^c}+r^{-c})(E|K|)^{2p}` from the polygon interface alone. -/
theorem not_exists_vanishing_hasPolygonBound (M : SourceModelData)
    (B : ℝ → Finset M.V)
    (hB : ∀ᶠ r : ℝ in atTop, (0 : M.V) ∈ B r)
    (hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    ¬ ∃ bp : ℝ → ℝ, Tendsto bp atTop (𝓝 0) ∧ ∀ᶠ r : ℝ in atTop, ∃ p : ℕ, 1 ≤ p ∧
      HasPolygonBound (M.cutProb r) (0 : M.V) (B r) p (cutPoly M r) (bp r) := by
  rintro ⟨bp, hbp, h⟩
  exact no_vanishing_uniform_polygon_factor M B bp hB hχ h hbp

/-- **Pointwise Case 3 discrepancy bound with the honest polygon factor.**

The polygon interface proved above composes with the landed Case 3 summation
(`I420Case3.prodFactor_le_mixedExcl_add_polygon`) as soon as a *tree expansion*
`HasTreeExpansion` is supplied at the same `poly`.  This is only the pre-asymptotic
bound.  The normalized little-o conclusion additionally needs a shared tree/cutoff
polynomial bridge and a separate averaged or split treatment of the `j = 3` corner;
the uniform factor above does not tend to zero, and no such asymptotic consumer is
claimed here. -/
theorem prodFactor_le_mixedExcl_add_cutPoly (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {p : ℕ} (hp : 1 ≤ p) {r : ℝ} (hr : 1 ≤ r) {B : Finset M.V}
    {a b : ℕ} {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hTree : HasTreeExpansion (M.cutProb r) (0 : M.V) B a b p (cutPoly M r) C) :
    ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      I420Case1.prodFactor (M.cutProb r) 0 a b B ≤
        I420Case1.mixedExcl (M.cutProb r) 0 a b B +
          (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
            ENNReal.ofReal (max M.triSelf (Cp * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)))) *
              I420Case1.powMomentAt (M.cutProb r) 1 0 ^ (2 * p) := by
  obtain ⟨c, Cp, hc, hCp, hpoly⟩ := exists_hasPolygonBound_cutPoly M hP hTri
  exact ⟨c, Cp, hc, hCp,
    prodFactor_le_mixedExcl_add_polygon hp hC hTree (hpoly hp hr B)⟩

end I420Case3

end PercLib.CriticalLRP
