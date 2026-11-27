/-
Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m4`, direction d5.

# The `ℓ = 3` terminal input of Lemma I.4.18 and the Case-3 driver

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.18 (p. 46) and the proof of Proposition I.4.15, Case 3 (p. 47).

Lemma I.4.18 as printed states, for **each** integer `ℓ ≥ 3`,

```
  sup_x T^ℓ_{β_c,r}(0, x) = T^ℓ_{β_c,r}(0, 0) ≤ C (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}.
```

At `ℓ = 3` the exponent is `0`, so the right-hand side is `C (∇_{r^c} + r^{-c})`, which
converges to `0` under the triangle condition, while `T^3_{β_c,r}(0,0) ≥ T(0,0)^3 = 1` because
`T(x,x) = 1` for the truncated law.  The `ℓ = 3` instance of the printed display is therefore
**false**, and no refinement of the driver can repair it: the terminal-maxi input that the
proof of Lemma I.4.18 actually supplies at `ℓ = 3` is the *non-vanishing* constant `∇_{β_c}`
(`T^3(0,0) = ∇(0,0) = ∇_{β_c}`), exactly as `I418C.source_ell_three_le` records.

This file machine-checks the consequences that matter for the Case-3 assembly:

* `not_exists_case3_hypothesis_bundle` — the hypothesis bundle `hcase3` of
  `secondMoment_asymptotic_case3` is **unsatisfiable**: it contains both
  `Tendsto (M.case3Driver c) atTop (𝓝 0)` and the uniform `ℓ = 3` polygon bound
  `∀ y, T^3(0,y) ≤ Cp * (∇_{r^c} + r^{-c})` with `Cp > 0`.  Hence the landed Case-3 theorem
  proves nothing as stated.
* `sum_ballF_polyK_three_le` / `connCubeMass_le_of_windowGap_colsum` — the exact
  replacement that *is* available at this base: the window column sum of `T^3` is bounded by
  `χ^3` (the `ℓ = 3` case of `∑_y T^ℓ(x,y) = χ^ℓ`, from `cutKpow_rowSum_toReal`), which is
  finite but does not vanish; it leaves the residual `C₃ χ^3 / |B_r|` in the second-moment
  error.  The residual is proved explicit, with the correct powers.

No `sorry`, no extra axioms; only the three standard Lean axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # The `ℓ = 3` driver obstruction of Lemma I.4.18 -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The obstruction: the driver cannot bound `T^3(0,0)` -/

/-- **The `ℓ = 3` instance of the printed Lemma I.4.18 is incompatible with the driver.**

If `T^3(0, ·)` is uniformly bounded by `Cp * (∇_{r^c} + r^{-c})` with `Cp > 0` at every vertex
(including the origin) for all large radii, and `χ = E_{β_c,r}|K|` is finite eventually, then the
driver cannot converge to `0`.

The proof is the origin: `T^3_{β_c,r}(0,0) ≥ T_{β_c,r}(0,0)^3 = 1`
(`I420Case3.one_le_polyK_three_of_chi_ne_top`), while `Cp * (∇_{r^c} + r^{-c}) < 1` for large `r`
once the driver is below `1 / Cp`. -/
theorem not_tendsto_case3Driver_zero_of_uniform_ell_three
    {c Cp : ℝ} (hCp : 0 < Cp)
    (hchi : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hT3 : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) :
    ¬ Tendsto (M.case3Driver c) atTop (𝓝 0) := by
  intro hdrv
  have hsmall : ∀ᶠ r : ℝ in atTop, M.case3Driver c r < 1 / Cp :=
    hdrv.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨r, hr_lt, hr_chi, hr_one⟩ :=
    (hsmall.and (hchi.and (eventually_ge_atTop (1 : ℝ)))).exists
  have hge : (1 : ℝ) ≤ I418C.polyK (M.cutTwoPoint r) 3 0 0 :=
    I420Case3.one_le_polyK_three_of_chi_ne_top M r hr_chi
  have hle : I418C.polyK (M.cutTwoPoint r) 3 0 0 ≤ Cp * M.case3Driver c r := hT3 r hr_one 0
  have hmono : Cp * M.case3Driver c r < Cp * (1 / Cp) :=
    mul_lt_mul_of_pos_left hr_lt hCp
  have hcancel : Cp * (1 / Cp) = 1 := by field_simp
  linarith

/-- The `∃`-form of `not_tendsto_case3Driver_zero_of_uniform_ell_three`: there are no positive
constants `c`, `Cp` for which the driver vanishes *and* bounds `T^3(0, ·)` uniformly. -/
theorem not_exists_case3Driver_bundle
    (hchi : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) := by
  rintro ⟨c, Cp, -, hCp, hdrv, hT3⟩
  exact not_tendsto_case3Driver_zero_of_uniform_ell_three M hCp hchi hT3 hdrv

/-- **The Case-3 hypothesis bundle `hcase3` of `secondMoment_asymptotic_case3` is
unsatisfiable.**  This is the bundle, with its two polygon conjuncts and the driver conditions,
exactly as it is consumed by `secondMoment_asymptotic_case3`.  The `ℓ = 3` conjunct is the
printed Lemma I.4.18 at `ℓ = 3`; it contradicts the vanishing of the driver. -/
theorem not_exists_case3_hypothesis_bundle
    (hchi : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
          * (M.cutMassAt r 0).toReal) := by
  rintro ⟨c, Cp, -, hCp, hdrv, -, hT3, -⟩
  exact not_tendsto_case3Driver_zero_of_uniform_ell_three M hCp hchi hT3 hdrv

/-- The unsatisfiability of the Case-3 bundle from the *model* finiteness hypothesis that
`secondMoment_asymptotic_case3` carries: finiteness of the second cutoff moment for all large `r`
implies finiteness of `χ = E_{β_c,r}|K|` there. -/
theorem not_exists_case3_hypothesis_bundle_of_cutMoment_two
    {r₀ : ℝ} (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
          * (M.cutMassAt r 0).toReal) := by
  refine not_exists_case3_hypothesis_bundle M ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  rw [M.cutMassAt_zero_eq_cutMoment r]
  exact M.cutMoment_one_ne_top_of_two (h2 r hr)

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## The exact `ℓ = 3` window column sum available at this base -/

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The `ℓ = 3` column sum is summable in `ℝ` whenever `χ = E_{β_c,r}|K|` is finite.**

This is `∑_y T^3_{β_c,r}(0,y) = χ^3` read as a summability statement: the extended-real row sum
`cutKpow_rowSum` is `χ^3 ≠ ⊤`, and `cutKpow_toReal_eq_polyK` identifies each real summand. -/
theorem summable_polyK_three (r : ℝ) (hchi : M.cutMassAt r 0 ≠ ⊤) :
    Summable (fun y : M.V => I418C.polyK (M.cutTwoPoint r) 3 0 y) := by
  have htop : (∑' y : M.V, KernelPower.Kpow (M.cutTwoPointE r) 3 0 y) ≠ ⊤ := by
    rw [M.cutKpow_rowSum r 3 0]
    exact ENNReal.pow_ne_top hchi
  have h := ENNReal.summable_toReal htop
  simpa only [M.cutKpow_toReal_eq_polyK r hchi] using h

/-- **The `ℓ = 3` window column sum is at most `χ^3`.**

This is the exact bound that replaces the false pointwise `ℓ = 3` display of Lemma I.4.18: the
full column sum `∑_y T^3_{β_c,r}(0,y)` equals `χ^3` (`cutKpow_rowSum_toReal`), so its restriction
to the window `B_r` is at most `χ^3`.  It is *finite* but does **not** vanish as `r → ∞`; this is
the source of the residual `C₃ χ^3 / |B_r|` in the second-moment error. -/
theorem sum_ballF_polyK_three_le (r : ℝ) (hchi : M.cutMassAt r 0 ≠ ⊤) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y
      ≤ (M.cutMassAt r 0).toReal ^ 3 := by
  refine (Summable.sum_le_tsum (E1Sign.ballF M r)
    (fun i _ => I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 i)
    (M.summable_polyK_three r hchi)).trans_eq ?_
  rw [← M.cutKpow_rowSum_toReal r hchi 3 0]
  exact tsum_congr fun y => (M.cutKpow_toReal_eq_polyK r hchi 3 0 y).symm

/-! ## The repaired consumer: the column sum instead of the false pointwise bound -/

/-- **Window summation with the `ℓ = 3` column sum instead of a pointwise driver bound.**

Per window vertex, `F y ≤ C₃ T³(0,y) χ^4 + C₄ T⁴(0,y) χ^3` (Lemma I.4.17 at `p = 3`, `q = 0`).
If the `ℓ = 3` column sum over the window is at most `C3c` and the `ℓ = 4` entries are controlled
by the driver (Lemma I.4.18 at `ℓ = 4`, which is sound), then

`∑_{y∈s} F y ≤ C₃ C3c χ^4 + |s| C₄ Cp drv χ^4`.

The difference from `sum_perVertex_le` is exactly that the `|s|` produced by the `ℓ = 3` term is
replaced by the single factor `C3c`: the `ℓ = 3` term is summed, not bounded vertex by vertex. -/
theorem sum_perVertex_le_colsum {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ)
    {χ drv C3 C4 Cp C3c : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∑ y ∈ s, T3 y ≤ C3c)
    (hT4 : ∀ y ∈ s, T4 y ≤ Cp * drv * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (_hCp : 0 ≤ Cp) (hχ : 0 ≤ χ) (_hdrv : 0 ≤ drv) :
    ∑ y ∈ s, F y ≤ C3 * C3c * χ ^ 4 + (s.card : ℝ) * (C4 * Cp) * drv * χ ^ 4 := by
  have hstep : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * (Cp * drv * χ) * χ ^ 3 := by
    intro y hy
    refine (hF y hy).trans ?_
    have h4 : C4 * T4 y * χ ^ 3 ≤ C4 * (Cp * drv * χ) * χ ^ 3 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ 3)
      exact mul_le_mul_of_nonneg_left (hT4 y hy) hC4
    linarith
  have hsum : ∑ y ∈ s, (C3 * T3 y * χ ^ 4) = C3 * χ ^ 4 * ∑ y ∈ s, T3 y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hconst : ∑ y ∈ s, (C4 * (Cp * drv * χ) * χ ^ 3)
      = (s.card : ℝ) * (C4 * (Cp * drv * χ) * χ ^ 3) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hmain : ∑ y ∈ s, F y ≤ ∑ y ∈ s, (C3 * T3 y * χ ^ 4 + C4 * (Cp * drv * χ) * χ ^ 3) :=
    Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, hsum, hconst] at hmain
  have hcoef : (0 : ℝ) ≤ C3 * χ ^ 4 := by positivity
  have h3 : C3 * χ ^ 4 * (∑ y ∈ s, T3 y) ≤ C3 * χ ^ 4 * C3c :=
    mul_le_mul_of_nonneg_left hT3 hcoef
  have hgoal : C3 * χ ^ 4 * C3c + (s.card : ℝ) * (C4 * (Cp * drv * χ) * χ ^ 3)
      = C3 * C3c * χ ^ 4 + (s.card : ℝ) * (C4 * Cp) * drv * χ ^ 4 := by ring
  linarith [hmain, h3, hgoal.le, hgoal.ge]

/-- **Case 3, the repaired numerator inequality.**

Identical to `connCubeMass_le_of_windowGap` except that the unsatisfiable pointwise `hT3` is
replaced by the column-sum hypothesis `hT3col`; the conclusion gains the separate term
`C₃ C3c χ^4` in place of the `|B_r|` copies that the pointwise bound would have produced. -/
theorem connCubeMass_le_of_windowGap_colsum {c Cp C3 C4 : ℝ} {C3c : ℝ → ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3col : ∀ r : ℝ, 1 ≤ r →
      ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ C3c r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
        * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal
      ≤ C3 * C3c r * (M.cutMassAt r 0).toReal ^ 4
        + ((M.ball r).ncard : ℝ) * (C4 * Cp) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  rw [M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)]
  have hmain := sum_perVertex_le_colsum (s := E1Sign.ballF M r)
    (F := fun y => (M.connCubeVertexMass r y).toReal)
    (T3 := fun y => I418C.polyK (M.cutTwoPoint r) 3 0 y)
    (T4 := fun y => I418C.polyK (M.cutTwoPoint r) 4 0 y)
    (χ := (M.cutMassAt r 0).toReal) (drv := M.case3Driver c r) (C3c := C3c r)
    (C3 := C3) (C4 := C4) (Cp := Cp)
    (hgap r hr) (hT3col r hr) (fun y _ => hpoly4 r hr y) hC3 hC4 hCp hχ hdrv
  calc ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal
      ≤ C3 * C3c r * (M.cutMassAt r 0).toReal ^ 4
          + ((E1Sign.ballF M r).card : ℝ) * (C4 * Cp) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := hmain
    _ = C3 * C3c r * (M.cutMassAt r 0).toReal ^ 4
          + ((M.ball r).ncard : ℝ) * (C4 * Cp) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
        rw [E1Sign.card_ballF M r]

/-- **The repaired numerator inequality with the `ℓ = 3` input *proved*, not assumed.**

Taking `C3c r = χ^3` in `connCubeMass_le_of_windowGap_colsum`, the column-sum hypothesis is
`sum_ballF_polyK_three_le`, so the only remaining analytic inputs are the source's per-vertex
Lemma I.4.17 at `p = 3`, `q = 0` (`hgap`) and the sound `ℓ = 4` polygon bound (`hpoly4`). -/
theorem connCubeMass_le_of_windowGap_chi_cube {c Cp C3 C4 : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hchi : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
        * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal
      ≤ C3 * (M.cutMassAt r 0).toReal ^ 3 * (M.cutMassAt r 0).toReal ^ 4
        + ((M.ball r).ncard : ℝ) * (C4 * Cp) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 :=
  M.connCubeMass_le_of_windowGap_colsum hCp hC3 hC4 hc hgap
    (fun r hr => M.sum_ballF_polyK_three_le r (hchi r hr)) hpoly4

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## The repaired second-moment error: the residual `C₃ χ^3 / (c₃ |B_r|)` -/

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 second-moment error with the `ℓ = 3` column sum instead of the driver.**

`E_{2,r} ≤ connCubeMass/(|B_r| χ E|K|²)` (`p2ExclError_le_connCubeMass_div`), the moment gap
`c₃ χ^3 ≤ E|K|²` kills `χ^4` against `χ E|K|²`, and the `ℓ = 3` column sum `C3c r` stays:

`E_{2,r} ≤ (C₄ Cp / c₃) (∇_{r^c} + r^{-c}) + C₃ C3c r / (c₃ |B_r|)`.

With the only available bound `C3c r = χ^3` (`sum_ballF_polyK_three_le`) the second term is
`C₃ χ^3 / (c₃ |B_r|)`, i.e. `≈ r^{3α - d}`: it vanishes exactly when `3α < d` (Case 1) and
diverges in Case 3.  This is the precise sense in which the `ℓ = 3` term is Case-1-only. -/
theorem p2ExclError_le_colsum {c Cp C3 C4 c3 : ℝ} {C3c : ℝ → ℝ} {r₀ : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hc3 : 0 < c3)
    (hC3c : ∀ r : ℝ, 1 ≤ r → 0 ≤ C3c r)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3col : ∀ r : ℝ, 1 ≤ r →
      ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ C3c r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
        * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ (C4 * Cp / c3) * M.case3Driver c r
        + C3 * C3c r / (c3 * ((M.ball r).ncard : ℝ)) := by
  have hnum := M.connCubeMass_le_of_windowGap_colsum hCp hC3 hC4 hc hgap hT3col hpoly4
  filter_upwards [hnum, hgm, eventually_ge_atTop (max r₀ 1)] with r hnum_r hgm_r hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one (le_trans (le_max_right _ _) hr)
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have h2r : M.cutMoment 2 r ≠ ⊤ := h2 r (le_trans (le_max_left _ _) hr)
  have hcr : M.connCubeMass r ≠ ⊤ := hc r hr1
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have h := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at h
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have h := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  have hC3c_r : (0 : ℝ) ≤ C3c r := hC3c r hr1
  refine (M.p2ExclError_le_connCubeMass_div r hr0 h2r hcr).trans ?_
  set b : ℝ := ((M.ball r).ncard : ℝ) with hbdef
  set χ : ℝ := (M.cutMassAt r 0).toReal with hchi_def
  set A2 : ℝ := (M.cutMoment 2 r).toReal with hA2_def
  set drv : ℝ := M.case3Driver c r with hdrv_def
  have hgap' : c3 * χ ^ 3 ≤ A2 := hgm_r
  have hbpos : (0 : ℝ) < b := hb
  have hden : (0 : ℝ) < b * χ * A2 := by positivity
  rw [hχeq, div_le_iff₀ hden]
  have hdist : ((C4 * Cp / c3) * drv + C3 * C3c r / (c3 * b)) * (b * χ * A2)
      = (C4 * Cp / c3) * drv * (b * χ * A2) + C3 * C3c r * (χ * A2) / c3 := by
    field_simp
  rw [hdist]
  have h1 : C3 * C3c r * χ ^ 4 ≤ C3 * C3c r * (χ * A2) / c3 := by
    rw [le_div_iff₀ hc3]
    have e : C3 * C3c r * χ ^ 4 * c3 = (C3 * C3c r * χ) * (c3 * χ ^ 3) := by ring
    have e' : C3 * C3c r * (χ * A2) = (C3 * C3c r * χ) * A2 := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hgap' (by positivity)
  have h2' : b * (C4 * Cp) * drv * χ ^ 4 ≤ (C4 * Cp / c3) * drv * (b * χ * A2) := by
    have hA2c : χ ^ 3 ≤ A2 / c3 := by
      rw [le_div_iff₀ hc3]
      linarith [hgap']
    have step : (C4 * Cp) * drv * (b * χ) * χ ^ 3 ≤ (C4 * Cp) * drv * (b * χ) * (A2 / c3) :=
      mul_le_mul_of_nonneg_left hA2c (by positivity)
    have e1 : b * (C4 * Cp) * drv * χ ^ 4 = (C4 * Cp) * drv * (b * χ) * χ ^ 3 := by ring
    have e2 : (C4 * Cp / c3) * drv * (b * χ * A2) = (C4 * Cp) * drv * (b * χ) * (A2 / c3) := by
      field_simp
    rw [e1, e2]
    exact step
  linarith [hnum_r, h1, h2']

/-- **The repaired Case-3 error with the `ℓ = 3` input discharged by `χ^3`.**

Same statement as `p2ExclError_le_colsum` with `C3c = χ^3` supplied by
`sum_ballF_polyK_three_le`: the only remaining inputs are the source's per-vertex Lemma I.4.17 at
`p = 3`, `q = 0`, the sound `ℓ = 4` polygon bound, and the moment gap. -/
theorem p2ExclError_le_chi_cube {c Cp C3 C4 c3 : ℝ} {r₀ : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hchi : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
        * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ (C4 * Cp / c3) * M.case3Driver c r
        + C3 * (M.cutMassAt r 0).toReal ^ 3 / (c3 * ((M.ball r).ncard : ℝ)) :=
  M.p2ExclError_le_colsum hCp hC3 hC4 hc3
    (fun _ _ => pow_nonneg ENNReal.toReal_nonneg 3)
    h2 hc hgap (fun r hr => M.sum_ballF_polyK_three_le r (hchi r hr))
    hpoly4 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## The residual `χ^3 / |B_r|`: divergence exactly when `d < 3α` -/

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The residual `C₃ χ^3 / (c₃ |B_r|)` diverges when `d < 3 α`.**

The repaired Case-3 error bound `p2ExclError_le_chi_cube` carries the additive residual
`χ^3 / |B_r|`.  With the source's first-moment asymptotic `χ / (c₀ r^α) → 1` and the lattice
ball growth `|B_r| ~ r^d` (`SourceModelData.ball_count`), that residual is asymptotic to
`c₀^3 r^{3α - d}`; when `d < 3α` it tends to `+∞`.  Consequently no choice of the constants
`C₃, c₃` makes the column-sum route give `E_{2,r} → 0` in that regime: the `ℓ = 3` term needs a
genuinely different treatment there, not a better constant. -/
theorem tendsto_chi_cube_div_ball_ncard_atTop {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) atTop (𝓝 1))
    (hd : (M.d : ℝ) < 3 * M.α) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal ^ 3 / ((M.ball r).ncard : ℝ))
      atTop atTop := by
  -- the `χ` factor: its cube still tends to `1`
  have hA : Tendsto (fun r : ℝ => ((M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) ^ 3)
      atTop (𝓝 1) := by
    have := hP.pow 3
    simpa using this
  -- the ball factor: `|B_r| / r^d → 1`, hence `r^d / |B_r| → 1`
  have hB : Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ M.d) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp (M.ball_count)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (pow_pos hr M.d).ne'
  have hD' : Tendsto (fun r : ℝ => r ^ M.d / ((M.ball r).ncard : ℝ)) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp (M.ball_count.symm)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h := M.ball_ncard_pos r hr.le
    positivity
  have hD : Tendsto (fun r : ℝ => r ^ (M.d : ℝ) / ((M.ball r).ncard : ℝ)) atTop (𝓝 1) := by
    refine hD'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _
    rw [Real.rpow_natCast]
  -- the growth factor
  have hE : Tendsto (fun r : ℝ => r ^ (3 * M.α - (M.d : ℝ))) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hcomb : Tendsto (fun r : ℝ =>
      ((M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) ^ 3
        * (c₀ ^ 3 * (r ^ (M.d : ℝ) / ((M.ball r).ncard : ℝ)))) atTop (𝓝 (c₀ ^ 3)) := by
    have h := hA.mul (hD.const_mul (c₀ ^ 3))
    simpa using h
  have hfinal := hcomb.pos_mul_atTop (C := c₀ ^ 3) (by positivity) hE
  refine hfinal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
    have h := M.ball_ncard_pos r hr.le
    positivity
  have h3a : r ^ (3 * M.α) = (r ^ M.α) ^ 3 := by
    rw [← Real.rpow_natCast (r ^ M.α) 3, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hsub : r ^ (3 * M.α - (M.d : ℝ)) = r ^ (3 * M.α) / r ^ (M.d : ℝ) :=
    Real.rpow_sub hr (3 * M.α) (M.d : ℝ)
  have hrd : r ^ (M.d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr (M.d : ℝ)).ne'
  have hra : r ^ M.α ≠ 0 := (Real.rpow_pos_of_pos hr M.α).ne'
  rw [hsub, h3a]
  field_simp
end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The residual `χ^3 / |B_r|` vanishes when `3 α < d` (Case 1).**

The mirror of `tendsto_chi_cube_div_ball_ncard_atTop`: with `χ / (c₀ r^α) → 1` and
`|B_r| ~ r^d`, the residual `χ^3/|B_r|` is asymptotic to `c₀^3 r^{3α - d}`, which tends to `0`
when `3α < d`.  Together with `p2ExclError_le_chi_cube` this shows that the repaired column-sum
consumer *does* close the `ℓ = 3` term in Case 1, at rate `r^{3α-d}`, without any `ℓ = 3` polygon
hypothesis. -/
theorem tendsto_chi_cube_div_ball_ncard_zero {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) atTop (𝓝 1))
    (hd : 3 * M.α < (M.d : ℝ)) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal ^ 3 / ((M.ball r).ncard : ℝ))
      atTop (𝓝 0) := by
  have hA : Tendsto (fun r : ℝ => ((M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) ^ 3)
      atTop (𝓝 1) := by
    have := hP.pow 3
    simpa using this
  have hD : Tendsto (fun r : ℝ => r ^ (M.d : ℝ) / ((M.ball r).ncard : ℝ)) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp (M.ball_count.symm) |>.congr' ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      have h := M.ball_ncard_pos r hr.le
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _
      simp only [Pi.div_apply, Real.rpow_natCast]
  have hE : Tendsto (fun r : ℝ => r ^ (3 * M.α - (M.d : ℝ))) atTop (𝓝 0) := by
    have hpos : Tendsto (fun r : ℝ => r ^ ((M.d : ℝ) - 3 * M.α)) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    have hinv := hpos.inv_tendsto_atTop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    change (r ^ ((M.d : ℝ) - 3 * M.α))⁻¹ = r ^ (3 * M.α - (M.d : ℝ))
    rw [← Real.rpow_neg hr.le]
    congr 1
    ring
  have hcomb : Tendsto (fun r : ℝ =>
      ((M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) ^ 3
        * (c₀ ^ 3 * (r ^ (M.d : ℝ) / ((M.ball r).ncard : ℝ)))) atTop (𝓝 (c₀ ^ 3)) := by
    have h := hA.mul (hD.const_mul (c₀ ^ 3))
    simpa using h
  have hfinal : Tendsto (fun r : ℝ =>
      ((M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) ^ 3
        * (c₀ ^ 3 * (r ^ (M.d : ℝ) / ((M.ball r).ncard : ℝ)))
        * r ^ (3 * M.α - (M.d : ℝ))) atTop (𝓝 0) := by
    have h := hcomb.mul hE
    simpa using h
  refine hfinal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
    have h := M.ball_ncard_pos r hr.le
    positivity
  have h3a : r ^ (3 * M.α) = (r ^ M.α) ^ 3 := by
    rw [← Real.rpow_natCast (r ^ M.α) 3, ← Real.rpow_mul hr.le]
    congr 1
    ring
  have hsub : r ^ (3 * M.α - (M.d : ℝ)) = r ^ (3 * M.α) / r ^ (M.d : ℝ) :=
    Real.rpow_sub hr (3 * M.α) (M.d : ℝ)
  have hrd : r ^ (M.d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr (M.d : ℝ)).ne'
  have hra : r ^ M.α ≠ 0 := (Real.rpow_pos_of_pos hr M.α).ne'
  rw [hsub, h3a]
  field_simp

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Case 1 (`3α < d`): the repaired assembly proves `E_{2,r} → 0` with no `ℓ = 3` polygon
hypothesis.**

Every input is the source's own except the per-vertex Lemma I.4.17 at `p = 3`, `q = 0` (`hgap`):
the sound `ℓ = 4` polygon bound (`hpoly4`), the moment gap, the first-moment asymptotic
`χ / (c₀ r^α) → 1`, the divergence of the driver, and `3α < d`.  The `ℓ = 3` term is handled by
the *proved* column sum `χ^3` (`sum_ballF_polyK_three_le`), and the residual `χ^3/|B_r|` tends to
zero precisely because `3α < d` (`tendsto_chi_cube_div_ball_ncard_zero`).

This is the honest replacement for `p2ExclError_tendsto_zero_of_case3`, whose `hT3` hypothesis is
unsatisfiable (`not_exists_case3_hypothesis_bundle`). -/
theorem tendsto_p2ExclError_zero_of_case1 {c Cp C3 C4 c3 c₀ : ℝ} {r₀ : ℝ}
    (hCp : 0 ≤ Cp) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hc3 : 0 < c3) (hc₀ : 0 < c₀)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hchi : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r
        * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c₀ * r ^ M.α)) atTop (𝓝 1))
    (hd : 3 * M.α < (M.d : ℝ))
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hupper := M.p2ExclError_le_chi_cube hCp hC3 hC4 hc3 h2 hchi hc hgap hpoly4 hgm
  have hres : Tendsto (fun r : ℝ =>
      C3 * (M.cutMassAt r 0).toReal ^ 3 / (c3 * ((M.ball r).ncard : ℝ))) atTop (𝓝 0) := by
    have h := (M.tendsto_chi_cube_div_ball_ncard_zero hc₀ hP hd).const_mul (C3 / c3)
    have h' : Tendsto (fun r : ℝ =>
        (C3 / c3) * ((M.cutMassAt r 0).toReal ^ 3 / ((M.ball r).ncard : ℝ)))
        atTop (𝓝 0) := by
      simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
      have hpos := M.ball_ncard_pos r hr.le
      positivity
    field_simp
  have hlim : Tendsto (fun r : ℝ => (C4 * Cp / c3) * M.case3Driver c r
      + C3 * (M.cutMassAt r 0).toReal ^ 3 / (c3 * ((M.ball r).ncard : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => (C4 * Cp / c3) * M.case3Driver c r) atTop (𝓝 0) := by
      simpa using hdrv.const_mul (C4 * Cp / c3)
    simpa using h1.add hres
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ hupper
  filter_upwards [eventually_ge_atTop (max r₀ 1)] with r hr
  exact M.p2ExclError_nonneg r
    (le_trans zero_le_one (le_trans (le_max_right _ _) hr))
    (h2 r (le_trans (le_max_left _ _) hr))

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
