/-
The per-vertex `ℓ = 3` input `hT3` of the Case-3 assembly is unsatisfiable.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

## The source statement being refuted

Lemma I.4.18 (Hutchcroft, *Critical long-range percolation I*, p. 46) is printed as

  `sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}`
  for each integer `ℓ ≥ 3`,

and its `ℓ = 3` instance is used in Case 3 of Proposition I.4.15 to bound the `ℓ = 3`
summand of Lemma I.4.17 at `p = 3`, `q = 0` *uniformly over the window vertex*.  The
formal counterpart is the hypothesis

  `hT3 : ∀ r ≥ 1, ∀ y, polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r`

of `SecondMomentCase3.connCubeMass_le_of_windowGap`, with `M.case3Driver c r` the source's
`∇_{r^c} + r^{-c}`.

## Why it cannot hold

`T_{β_c,r}(0,0) = P_{β_c,r}(0 ↔ 0) = 1`, so `T³_{β_c,r}(0,0) ≥ 1` for every `r`
(`I418C.one_le_polyK_three`); this is the landed model-level statement
`I420Case3.one_le_polyK_three_of_chi_ne_top`.  On the other hand `M.case3Driver c r → 0`
as `r → ∞` under the triangle condition (`M.nablaTail → 0` plus `r^{-c} → 0`), so
`Cp * M.case3Driver c r < 1` eventually.  Taking `y = 0` gives the contradiction.

The same argument refutes the bound at *every* fixed vertex `y` for which
`T_{β_c,r}(0,y)` stays bounded below, since `T³(0,y) ≥ T(0,y)` (the walk `0 → 0 → 0 → y`).
So the defect is not an artefact of the origin: it is a defect of the *per-vertex,
vanishing* form of the statement, and the repair must be either a constant (non-vanishing)
bound near the origin, or — as in `Defs.lean`/`Windowed.lean` — a bound on the *windowed*
sum `∑_{y ∈ B_r} T³_{β_c,r}(0,y)`, which is the quantity the window summation actually uses.
No coefficient of the source is altered here and nothing is repaired silently.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Defs
public import PercLib.CriticalLRP.Analysis.Polygon.Bridge

/-! # `hT3` is unsatisfiable: the per-vertex `ℓ = 3` bound cannot hold with a vanishing driver -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-- **The diagonal defeats any constant multiple of the driver.**

If the Case-3 driver vanishes then, for every constant `Cp` and every radius `R`, there is
`r ≥ R` at which the `ℓ = 3` cutoff polygon entry at the origin exceeds
`Cp * (∇_{r^c} + r^{-c})`.  The entry is at least `T(0,0)³ = 1` there, while the driver is
eventually below `1/Cp`.

`hχ` is the finiteness of the truncated first moment `χ = E_{β_c,r}|K|` used to pass from
the `ℝ≥0∞` power `Kpow` to the real iterated sum (`cutKpow_toReal_eq_polyK`); it is the same
hypothesis the source's applications carry (`h2` below derives it from `E|K|² < ∞`). -/
theorem exists_polyK_three_diag_gt_const_mul_case3Driver {c Cp : ℝ}
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) {r₀ : ℝ}
    (hχ : ∀ r : ℝ, r₀ ≤ r → M.cutMassAt r 0 ≠ ⊤) (R : ℝ) :
    ∃ r : ℝ, R ≤ r ∧ 1 ≤ r ∧
      Cp * M.case3Driver c r < I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 := by
  have hsmall : ∀ᶠ r : ℝ in atTop, Cp * M.case3Driver c r < 1 := by
    have h0 : Tendsto (fun r : ℝ => Cp * M.case3Driver c r) atTop (𝓝 (Cp * 0)) :=
      tendsto_const_nhds.mul hdrv
    rw [mul_zero] at h0
    filter_upwards [h0 (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with r hr
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] at hr
    exact lt_of_le_of_lt (le_abs_self _) hr
  obtain ⟨r, h1, h2⟩ := ((eventually_ge_atTop (max (max R 1) r₀)).and hsmall).exists
  have hR : R ≤ r := le_trans (le_trans (le_max_left R 1) (le_max_left _ r₀)) h1
  have hr1 : 1 ≤ r := le_trans (le_trans (le_max_right R 1) (le_max_left _ r₀)) h1
  have hr₀ : r₀ ≤ r := le_trans (le_max_right _ r₀) h1
  have hone : 1 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 :=
    I420Case3.one_le_polyK_three_of_chi_ne_top M r (hχ r hr₀)
  exact ⟨r, hR, hr1, lt_of_lt_of_le h2 hone⟩

/-- **The per-vertex `ℓ = 3` input `hT3` is refutable**: no constant `Cp` makes
`polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * (∇_{r^c} + r^{-c})` hold for all `r ≥ 1` and all
vertices `y` when the driver vanishes. -/
theorem not_perVertexEllThreeGap {c Cp : ℝ}
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) {r₀ : ℝ}
    (hχ : ∀ r : ℝ, r₀ ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ¬ M.PerVertexEllThreeGap c Cp := by
  intro h
  obtain ⟨r, -, hr1, hgt⟩ :=
    M.exists_polyK_three_diag_gt_const_mul_case3Driver hdrv hχ 1
  exact absurd (h r hr1 (0 : M.V)) (not_le.mpr hgt)

/-- **The Case-3 polygon bundle of `secondMoment_asymptotic_case3` is empty.**

The bundle is the one the landed assembly consumes: a positive `c` and `Cp` for which the
driver vanishes, is logarithmically integrable, and both polygon conjuncts hold —
`ℓ = 3` per-vertex and `ℓ = 4` per-vertex.  The `ℓ = 3` conjunct is the false one, so the
whole bundle is unsatisfiable and the assembly must carry the windowed `ℓ = 3` input
(`Defs.WindowedEllThreeGap`) instead. -/
theorem not_exists_case3_polygon_bundle {r₀ : ℝ}
    (hχ : ∀ r : ℝ, r₀ ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
  rintro ⟨c, Cp, -, -, hdrv, -, hT3, -⟩
  exact M.not_perVertexEllThreeGap hdrv hχ hT3

/-- The same emptiness with `hχ` derived from the finiteness of the *second* cutoff moment,
i.e. from the hypothesis `h2` of `secondMoment_asymptotic_case3`. -/
theorem not_exists_case3_polygon_bundle_of_cutMoment_two {r₀ : ℝ}
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :=
  M.not_exists_case3_polygon_bundle fun r hr =>
    M.cutMassAt_zero_eq_cutMoment r ▸ M.cutMoment_one_ne_top_of_two (h2 r hr)

/-! ## The failure is not an artefact of the origin -/

/-- **Every cutoff polygon entry dominates the corresponding two-point entry**:
`T_{β_c,r}(0,y) ≤ T³_{β_c,r}(0,y)`.  In walk language the right-hand side contains the walk
`0 → 0 → 0 → y`, whose weight is `T(0,0)² T(0,y) = T(0,y)`.  (Proved in `ℝ≥0∞` with
`Kpow`, so no summability of the real iterated sum is needed beyond `χ < ∞`.) -/
theorem cutTwoPoint_le_polyK_three (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    M.cutTwoPoint r 0 y ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := by
  have hK : M.cutTwoPointE r (0 : M.V) 0 = 1 := by
    rw [M.cutTwoPointE_eq_ofReal, M.cutTwoPoint_self_eq_one r 0, ENNReal.ofReal_one]
  -- `1 ≤ T²(0,0)`
  have htwo : (1 : ℝ≥0∞) ≤ Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 := by
    have hstep : Kpow (M.cutTwoPointE r) 1 (0 : M.V) 0 ≤ Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 := by
      have h : (1 : ℝ≥0∞)
          ≤ ∑' u : M.V, Kpow (M.cutTwoPointE r) 1 (0 : M.V) u * M.cutTwoPointE r u 0 := by
        have h := ENNReal.le_tsum
          (f := fun z : M.V => Kpow (M.cutTwoPointE r) 1 (0 : M.V) z * M.cutTwoPointE r z 0) 0
        rwa [Kpow_one, hK, one_mul] at h
      calc Kpow (M.cutTwoPointE r) 1 (0 : M.V) 0 = 1 := by rw [Kpow_one, hK]
        _ ≤ ∑' u : M.V, Kpow (M.cutTwoPointE r) 1 (0 : M.V) u * M.cutTwoPointE r u 0 := h
        _ = Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 := rfl
    calc (1 : ℝ≥0∞) = M.cutTwoPointE r (0 : M.V) 0 := hK.symm
      _ = Kpow (M.cutTwoPointE r) 1 (0 : M.V) 0 := (Kpow_one (0 : M.V) 0).symm
      _ ≤ Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 := hstep
  -- `T(0,y) = 1 · T(0,y) ≤ T²(0,0) · T(0,y) ≤ T³(0,y)`
  have hstep3 : Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 * M.cutTwoPointE r 0 y
      ≤ Kpow (M.cutTwoPointE r) 3 (0 : M.V) y := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Kpow_succ]
    exact ENNReal.le_tsum
      (f := fun z : M.V => Kpow (M.cutTwoPointE r) 2 (0 : M.V) z * M.cutTwoPointE r z y) 0
  have hmul : M.cutTwoPointE r 0 y
      ≤ Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 * M.cutTwoPointE r 0 y := by
    calc M.cutTwoPointE r 0 y = 1 * M.cutTwoPointE r 0 y := (one_mul _).symm
      _ ≤ Kpow (M.cutTwoPointE r) 2 (0 : M.V) 0 * M.cutTwoPointE r 0 y :=
          mul_le_mul_of_nonneg_right htwo bot_le
  have hmono := hmul.trans hstep3
  have hne : Kpow (M.cutTwoPointE r) 3 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y
  have hreal := ENNReal.toReal_mono hne hmono
  rwa [M.cutKpow_toReal_eq_polyK r hχ 3 0 y, M.cutTwoPointE_eq_ofReal,
    ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r 0 y)] at hreal

/-- **The per-vertex `ℓ = 3` input fails at every vertex whose two-point function is bounded
below.**  With `δ ≤ T_{β_c,r}(0,y)` for all `r ≥ 1` (and `δ > 0`), the bound
`T³_{β_c,r}(0,y) ≤ Cp (∇_{r^c} + r^{-c})` fails for large `r`, because the driver vanishes
while `T³(0,y) ≥ T(0,y) ≥ δ`.  So no "off-diagonal uniform driver" can repair the per-vertex
form: the repair has to count or sum, as the windowed bound `Defs.WindowedEllThreeGap` does. -/
theorem not_perVertexEllThreeGap_of_lower_bound {c Cp : ℝ}
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) {r₀ : ℝ}
    (hχ : ∀ r : ℝ, r₀ ≤ r → M.cutMassAt r 0 ≠ ⊤) {y : M.V} {δ : ℝ} (hδ : 0 < δ)
    (hy : ∀ r : ℝ, 1 ≤ r → δ ≤ M.cutTwoPoint r 0 y) :
    ¬ M.PerVertexEllThreeGap c Cp := by
  intro h
  have hsmall : ∀ᶠ r : ℝ in atTop, Cp * M.case3Driver c r < δ := by
    have h0 : Tendsto (fun r : ℝ => Cp * M.case3Driver c r) atTop (𝓝 (Cp * 0)) :=
      tendsto_const_nhds.mul hdrv
    rw [mul_zero] at h0
    filter_upwards [h0 (Metric.ball_mem_nhds (0 : ℝ) hδ)] with r hr
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] at hr
    exact lt_of_le_of_lt (le_abs_self _) hr
  obtain ⟨r, h1, h2⟩ := ((eventually_ge_atTop (max 1 r₀)).and hsmall).exists
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) h1
  have hr₀ : r₀ ≤ r := le_trans (le_max_right _ _) h1
  have hlow : δ ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
    (hy r hr1).trans (M.cutTwoPoint_le_polyK_three r (hχ r hr₀) y)
  linarith [h r hr1 y]

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
