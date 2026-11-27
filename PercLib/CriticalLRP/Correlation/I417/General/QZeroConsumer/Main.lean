/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# Two-term `q = 0` star gap: sufficient profile, exact summed residual, no absorption

Consumer-side bookkeeping for the `q = 0` instance of Hutchcroft's Lemma I.4.17 at `p = 3`
(source: *Critical long-range percolation I*, arXiv:2508.18807v1, p. 45), whose per-vertex
right-hand side is `C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³` (`starRHS`) with `χ = (E_{β_c,r}|K|)` and
`T = T_{β_c,r}`.

* `one_le_chi` — `1 ≤ χ` at finite truncated cluster mass.
* `cutTwoPoint_le_polyK` — `T(0,y) ≤ T^ℓ(0,y)` for every `ℓ ≥ 1` (the degenerate path summand).
* `sharpProfile_implies_twoTermStarGap` — the target follows from the sharper profile bound
  `E[|K_0]³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)`.
* `tsum_starRHS` — the sum over *all* vertices of the two-term right-hand side is exactly
  `(C₃ + C₄) χ⁷`: the summed (window) form of the target is worth only the `χ⁷` residual, which is
  why the source states it per vertex.
* `not_absorbable_ell_one`, `not_absorbable_ell_two` — no constant absorbs the `ℓ = 1` (`T χ⁶`)
  or `ℓ = 2` (`T² χ⁵`) class of the landed `ℓ = 1..4` marked-joint bound into the two-term
  right-hand side, uniformly in `T ∈ (0,1]`, `χ ≥ 1`.  Hence the low orders cannot be removed by
  algebra, only by an event-level argument.

The target `TwoTermStarGap` itself is *not* proved here.  No `sorry`, no `admit`, no
`native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Defs
public import PercLib.CriticalLRP.Analysis.Polygon.Bridge
public import PercLib.CriticalLRP.Analysis.Polygon.Core
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # Consumer-side bookkeeping for the two-term `q = 0` star gap -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-! ## The two normalisations `χ ≥ 1` and `T ≤ T^ℓ` -/

/-- **`χ ≥ 1`**: at finite truncated cluster mass, `T_r(0,0) = 1` is a summand of the row sum
`∑_y T_r(0,y) = E_{β_c,r}|K_0| = χ`. -/
theorem one_le_chi (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) : 1 ≤ chi M r := by
  have hrow : (∑' y, M.cutTwoPointE r (0 : M.V) y) = M.cutMassAt r 0 :=
    M.tsum_cutTwoPointE_eq_cutMassAt r 0
  have hle : (1 : ℝ≥0∞) ≤ M.cutMassAt r 0 := by
    rw [← hrow]
    calc (1 : ℝ≥0∞) = M.cutTwoPointE r (0 : M.V) 0 := (M.cutTwoPointE_self_eq_one r 0).symm
      _ ≤ ∑' y, M.cutTwoPointE r (0 : M.V) y :=
          ENNReal.le_tsum (f := fun y : M.V => M.cutTwoPointE r (0 : M.V) y) 0
  have h := ENNReal.toReal_mono hχ hle
  rw [ENNReal.toReal_one] at h
  simpa only [chi] using h

/-- `cutTwoPoint r x y` is the `toReal` of `cutTwoPointE r x y`. -/
theorem cutTwoPoint_eq_toReal (r : ℝ) (x y : M.V) :
    M.cutTwoPoint r x y = (M.cutTwoPointE r x y).toReal := by
  rw [M.cutTwoPointE_eq_ofReal, ENNReal.toReal_ofReal (M.cutTwoPoint_nonneg r x y)]

/-- The diagonal entries of every matrix power of the truncated two-point kernel are at least
`1` (the degenerate path through the diagonal). -/
theorem one_le_Kpow_diag (r : ℝ) (n : ℕ) :
    (1 : ℝ≥0∞) ≤ Kpow (M.cutTwoPointE r) n (0 : M.V) 0 := by
  induction n with
  | zero =>
    rw [Kpow_zero]
    exact le_of_eq (deltaE_self 0).symm
  | succ n ih =>
    calc (1 : ℝ≥0∞) ≤ Kpow (M.cutTwoPointE r) n (0 : M.V) 0 := ih
      _ = Kpow (M.cutTwoPointE r) n (0 : M.V) 0 * M.cutTwoPointE r 0 0 := by
          rw [M.cutTwoPointE_self_eq_one r 0, mul_one]
      _ ≤ ∑' u, Kpow (M.cutTwoPointE r) n (0 : M.V) u * M.cutTwoPointE r u 0 :=
          ENNReal.le_tsum (f := fun u : M.V =>
            Kpow (M.cutTwoPointE r) n (0 : M.V) u * M.cutTwoPointE r u 0) 0
      _ = Kpow (M.cutTwoPointE r) (n + 1) (0 : M.V) 0 := (Kpow_succ _ _ _ _).symm

/-- **`T(0,y) ≤ T^ℓ(0,y)` for every `ℓ ≥ 1`**, in `ℝ≥0∞`: the degenerate path that stays at
`0` for `ℓ - 1` steps and then jumps to `y` contributes the single summand
`T(0,0)^{ℓ-1} T(0,y) = T(0,y)`. -/
theorem cutTwoPointE_le_Kpow (r : ℝ) {ell : ℕ} (hell : 1 ≤ ell) (y : M.V) :
    M.cutTwoPointE r (0 : M.V) y ≤ Kpow (M.cutTwoPointE r) ell (0 : M.V) y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  have hdiag : M.cutTwoPointE r (0 : M.V) 0 ≤ Kpow (M.cutTwoPointE r) n (0 : M.V) 0 := by
    rw [M.cutTwoPointE_self_eq_one r 0]
    exact one_le_Kpow_diag M r n
  calc M.cutTwoPointE r (0 : M.V) y
      = M.cutTwoPointE r (0 : M.V) 0 * M.cutTwoPointE r 0 y := by
        rw [M.cutTwoPointE_self_eq_one r 0, one_mul]
    _ ≤ Kpow (M.cutTwoPointE r) n (0 : M.V) 0 * M.cutTwoPointE r 0 y :=
        mul_le_mul_left hdiag _
    _ ≤ ∑' u, Kpow (M.cutTwoPointE r) n (0 : M.V) u * M.cutTwoPointE r u y :=
        ENNReal.le_tsum (f := fun u : M.V =>
          Kpow (M.cutTwoPointE r) n (0 : M.V) u * M.cutTwoPointE r u y) 0
    _ = Kpow (M.cutTwoPointE r) (n + 1) (0 : M.V) y := (Kpow_succ _ _ _ _).symm

/-- **`T(0,y) ≤ T^ℓ(0,y)` for every `ℓ ≥ 1`**, in `ℝ`. -/
theorem cutTwoPoint_le_polyK (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) {ell : ℕ} (hell : 1 ≤ ell)
    (y : M.V) : M.cutTwoPoint r 0 y ≤ I418C.polyK (M.cutTwoPoint r) ell (0 : M.V) y := by
  have hne : Kpow (M.cutTwoPointE r) ell (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ ell 0 y
  have h := ENNReal.toReal_mono hne (cutTwoPointE_le_Kpow M r hell y)
  rw [M.cutKpow_toReal_eq_polyK r hχ ell 0 y] at h
  rwa [cutTwoPoint_eq_toReal]

/-! ## The sharper profile suffices -/

/-- **The target follows from the `χ³ T` profile.**  If
`E[|K_0|³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)` for every `r ≥ 1` and every vertex `y`, then the source's
two-term statement holds with `C₃ = C`, `C₄ = 0`: by `T ≤ T³` and `1 ≤ χ`,
`χ³ T(0,y) ≤ T³(0,y) χ⁴` for every `y` and every `r ≥ 1`. -/
theorem sharpProfile_implies_twoTermStarGap (C : ℝ) (hC : 0 ≤ C) (hsharp : SharpProfile M C)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) : TwoTermStarGap M C 0 := by
  intro r hr y
  have hχr := hχ r hr
  have hχ1 : 1 ≤ chi M r := one_le_chi M r hχr
  have hχ0 : 0 ≤ chi M r := le_trans zero_le_one hχ1
  have hT0 : 0 ≤ M.cutTwoPoint r 0 y := M.cutTwoPoint_nonneg r 0 y
  have hPK3 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hTle : M.cutTwoPoint r (0 : M.V) y ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
    cutTwoPoint_le_polyK M r hχr (by norm_num) y
  have hkey : chi M r ^ 3 * M.cutTwoPoint r 0 y
      ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4 := by
    have h1 : M.cutTwoPoint r 0 y ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r := by
      calc M.cutTwoPoint r 0 y ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := hTle
        _ = I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * 1 := (mul_one _).symm
        _ ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r :=
            mul_le_mul_of_nonneg_left hχ1 hPK3
    calc chi M r ^ 3 * M.cutTwoPoint r 0 y
        ≤ chi M r ^ 3 * (I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hχ0 3)
      _ = I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4 := by ring
  calc (M.connCubeVertexMass r y).toReal
      ≤ C * chi M r ^ 3 * M.cutTwoPoint r 0 y := hsharp r hr y
    _ = C * (chi M r ^ 3 * M.cutTwoPoint r 0 y) := by ring
    _ ≤ C * (I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4) :=
        mul_le_mul_of_nonneg_left hkey hC
    _ ≤ starRHS M C 0 r y := by
        have hPK4 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3 :=
          mul_nonneg (I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 0 y)
            (pow_nonneg hχ0 3)
        simp only [starRHS, zero_mul, add_zero]
        exact le_of_eq (by ring)

/-! ## Row sums and the exact summed residual -/

/-- The row sums `∑_y T^ℓ(0,y) = χ^ℓ` of the truncated matrix powers, in `ℝ`. -/
theorem tsum_polyK_row (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) :
    (∑' y : M.V, I418C.polyK (M.cutTwoPoint r) n (0 : M.V) y) = chi M r ^ n := by
  have h := M.cutKpow_rowSum_toReal r hχ n 0
  rw [show (∑' y : M.V, I418C.polyK (M.cutTwoPoint r) n (0 : M.V) y)
      = ∑' y : M.V, (Kpow (M.cutTwoPointE r) n (0 : M.V) y).toReal from
      tsum_congr fun y => (M.cutKpow_toReal_eq_polyK r hχ n 0 y).symm]
  exact h

/-- The rows of every truncated matrix power are summable in `ℝ`. -/
theorem summable_polyK_row (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) :
    Summable (fun y : M.V => I418C.polyK (M.cutTwoPoint r) n (0 : M.V) y) := by
  have hsum : (∑' y : M.V, Kpow (M.cutTwoPointE r) n (0 : M.V) y)
      = M.cutMassAt r 0 ^ n := M.cutKpow_rowSum r n 0
  have h := ENNReal.summable_toReal (f := fun y : M.V =>
    Kpow (M.cutTwoPointE r) n (0 : M.V) y) (by rw [hsum]; exact ENNReal.pow_ne_top hχ)
  simpa only [M.cutKpow_toReal_eq_polyK r hχ] using h

/-- **The summed two-term right-hand side is exactly `(C₃ + C₄) χ⁷`.**  Summing the source's
per-vertex display over *all* vertices and using `∑_y T^ℓ(0,y) = χ^ℓ` collapses the two-term
bound to a single multiple of `χ⁷`: the summed (window) form carries no more information than the
landed `ℓ = 1..4` marked bound.  This is the precise sense in which the per-vertex statement is
the one with content. -/
theorem tsum_starRHS (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (C3 C4 : ℝ) :
    (∑' y : M.V, starRHS M C3 C4 r y) = (C3 + C4) * chi M r ^ 7 := by
  have h3 := summable_polyK_row M r hχ 3
  have h4 := summable_polyK_row M r hχ 4
  have hpt : ∀ y : M.V, starRHS M C3 C4 r y
      = (C3 * chi M r ^ 4) * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        + (C4 * chi M r ^ 3) * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y := by
    intro y
    simp only [starRHS]
    ring
  have hs3 : Summable (fun y : M.V =>
      (C3 * chi M r ^ 4) * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y) := h3.mul_left _
  have hs4 : Summable (fun y : M.V =>
      (C4 * chi M r ^ 3) * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y) := h4.mul_left _
  rw [tsum_congr hpt, Summable.tsum_add hs3 hs4, tsum_mul_left, tsum_mul_left,
    tsum_polyK_row M r hχ 3, tsum_polyK_row M r hχ 4]
  ring

/-! ## The low orders of the marked bound are not absorbable

The landed `ℓ = 1..4` marked bound (`connCubeVertexMass_toReal_le_markedPolygon`) has the classes
`χ^{7-ℓ} T^ℓ`, i.e. `T χ⁶` at `ℓ = 1` and `T² χ⁵` at `ℓ = 2`, versus `T³ χ⁴` and `T⁴ χ³` in the
source's two-term display.  The next two lemmas record that *no* constant absorbs either class
into the two-term right-hand side, uniformly over `T ∈ (0,1]`, `χ ≥ 1`; the low orders have to be
removed by an event-level argument, never by algebra. -/

/-- There is no constant absorbing the `ℓ = 1` class `T χ⁶` into the two-term right-hand side. -/
theorem not_absorbable_ell_one (C : ℝ) :
    ∃ T χ : ℝ, 0 ≤ T ∧ T ≤ 1 ∧ 1 ≤ χ ∧
      C * (T ^ 3 * χ ^ 4 + T ^ 4 * χ ^ 3) < T * χ ^ 6 := by
  have hbase : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ C * t ^ 2 * (1 + t) < 1 := by
    refine ⟨1 / (4 * (|C| + 1)), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      linarith [abs_nonneg C]
    · have hpos : (0 : ℝ) < 4 * (|C| + 1) := by positivity
      have hT1 : 1 / (4 * (|C| + 1)) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [abs_nonneg C])
      have hCT : |C| * (1 / (4 * (|C| + 1))) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ hpos]
        linarith [abs_nonneg C]
      have hTnn : (0 : ℝ) ≤ 1 / (4 * (|C| + 1)) := by positivity
      have hmain : |C| * (1 / (4 * (|C| + 1))) ^ 2 * (1 + 1 / (4 * (|C| + 1))) ≤ 1 / 2 := by
        have h2 : (1 / (4 * (|C| + 1))) * (1 + 1 / (4 * (|C| + 1))) ≤ 1 * 2 := by
          nlinarith [hT1, hTnn]
        calc |C| * (1 / (4 * (|C| + 1))) ^ 2 * (1 + 1 / (4 * (|C| + 1)))
            = (|C| * (1 / (4 * (|C| + 1))))
                * ((1 / (4 * (|C| + 1))) * (1 + 1 / (4 * (|C| + 1)))) := by ring
          _ ≤ (1 / 4) * (1 * 2) := mul_le_mul hCT h2 (by positivity) (by norm_num)
          _ = 1 / 2 := by norm_num
      have hle : C * (1 / (4 * (|C| + 1))) ^ 2 * (1 + 1 / (4 * (|C| + 1)))
          ≤ |C| * (1 / (4 * (|C| + 1))) ^ 2 * (1 + 1 / (4 * (|C| + 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) ?_) ?_
        · positivity
        · positivity
      linarith
  obtain ⟨t, ht0, ht1, htC⟩ := hbase
  refine ⟨t, 1, ht0.le, ht1, le_refl 1, ?_⟩
  have hsq : 0 < t ^ 2 := by positivity
  have h : C * (t ^ 3 + t ^ 4) = t * (C * t ^ 2 * (1 + t)) := by ring
  have : t * (C * t ^ 2 * (1 + t)) < t * 1 := by
    exact mul_lt_mul_of_pos_left htC ht0
  calc C * (t ^ 3 * 1 ^ 4 + t ^ 4 * 1 ^ 3) = C * (t ^ 3 + t ^ 4) := by norm_num
    _ = t * (C * t ^ 2 * (1 + t)) := h
    _ < t * 1 := this
    _ = t * 1 ^ 6 := by norm_num

/-- There is no constant absorbing the `ℓ = 2` class `T² χ⁵` into the two-term right-hand side. -/
theorem not_absorbable_ell_two (C : ℝ) :
    ∃ T χ : ℝ, 0 ≤ T ∧ T ≤ 1 ∧ 1 ≤ χ ∧
      C * (T ^ 3 * χ ^ 4 + T ^ 4 * χ ^ 3) < T ^ 2 * χ ^ 5 := by
  have hbase : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ C * t * (1 + t) < 1 := by
    refine ⟨1 / (4 * (|C| + 1)), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      linarith [abs_nonneg C]
    · have hpos : (0 : ℝ) < 4 * (|C| + 1) := by positivity
      have hCT : |C| * (1 / (4 * (|C| + 1))) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ hpos]
        linarith [abs_nonneg C]
      have hT1 : 1 / (4 * (|C| + 1)) ≤ 1 := by
        rw [div_le_one hpos]
        linarith [abs_nonneg C]
      have hle : C * (1 / (4 * (|C| + 1))) * (1 + 1 / (4 * (|C| + 1)))
          ≤ |C| * (1 / (4 * (|C| + 1))) * (1 + 1 / (4 * (|C| + 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) ?_) ?_
        · positivity
        · positivity
      have hmain : |C| * (1 / (4 * (|C| + 1))) * (1 + 1 / (4 * (|C| + 1))) ≤ 1 / 2 := by
        have h2 : 1 + 1 / (4 * (|C| + 1)) ≤ 2 := by linarith
        have hTnn : (0 : ℝ) ≤ |C| * (1 / (4 * (|C| + 1))) := by positivity
        nlinarith [hCT, h2, hTnn]
      linarith
  obtain ⟨t, ht0, ht1, htC⟩ := hbase
  refine ⟨t, 1, ht0.le, ht1, le_refl 1, ?_⟩
  have h : C * (t ^ 3 + t ^ 4) = t ^ 2 * (C * t * (1 + t)) := by ring
  have : t ^ 2 * (C * t * (1 + t)) < t ^ 2 * 1 := by
    exact mul_lt_mul_of_pos_left htC (by positivity)
  calc C * (t ^ 3 * 1 ^ 4 + t ^ 4 * 1 ^ 3) = C * (t ^ 3 + t ^ 4) := by norm_num
    _ = t ^ 2 * (C * t * (1 + t)) := h
    _ < t ^ 2 * 1 := this
    _ = t ^ 2 * 1 ^ 5 := by norm_num

/-- The source's exponent bookkeeping at `p = 3`, `q = 0`: the total number of kernel factors is
`2p + 2q + 1 = 7`, so the path lengths `ℓ = 3, 4` carry `χ⁴` and `χ³`. -/
theorem source_exponents :
    2 * 3 + 2 * 0 + 1 - 3 = (4 : ℕ) ∧ 2 * 3 + 2 * 0 + 1 - 4 = (3 : ℕ) := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## The consumer step: the per-vertex two-term bound summed over the Case-3 window -/

/-- **Per-vertex two-term bound `⟹` the window numerator bound.**  Summing the target over the
window `B_r` and using the polygon inputs `T³(0,y) ≤ Cp drv` and `T⁴(0,y) ≤ Cp drv χ` gives

`E[|K_0|³ |K_0 ∩ B_r|] ≤ (C₃ + C₄) Cp |B_r| drv χ⁴`,

which is exactly the source-shaped numerator hypothesis `hnum` of
`SourceModelData.p2ExclError_le_case3Driver`.  The constants propagate as `(C₃ + C₄) Cp`, and no
other input is used. -/
theorem connCubeMass_toReal_le_of_twoTermStarGap (C3 C4 Cp drv : ℝ)
    (hgap : TwoTermStarGap M C3 C4) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (_hCp : 0 ≤ Cp)
    (_hdrv : 0 ≤ drv) (r : ℝ) (hr : 1 ≤ r) (hM3 : M.cutMoment 3 r ≠ ⊤)
    (hT3 : ∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * drv)
    (hT4 : ∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ Cp * drv * chi M r) :
    (M.connCubeMass r).toReal
      ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4 := by
  classical
  have hχ0 : 0 ≤ chi M r := ENNReal.toReal_nonneg
  have hne : ∀ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y ≠ ⊤ := fun y _ =>
    ne_top_of_le_ne_top hM3 (M.connCubeVertexMass_le_cutMoment_three r y)
  have hb : ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal ≤ ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by
    intro y hy
    refine (hgap r hr y).trans ?_
    have h3 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        ≤ C3 * (Cp * drv) * chi M r ^ 4 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ0 4)
      exact mul_le_mul_of_nonneg_left (hT3 y hy) hC3
    have h4 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
        ≤ C4 * (Cp * drv * chi M r) * chi M r ^ 3 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ0 3)
      exact mul_le_mul_of_nonneg_left (hT4 y hy) hC4
    have hsum : C3 * (Cp * drv) * chi M r ^ 4 + C4 * (Cp * drv * chi M r) * chi M r ^ 3
        = ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by ring
    have hrhs : starRHS M C3 C4 r y
        = C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3 := rfl
    rw [hrhs]
    linarith [h3, h4, hsum.le, hsum.ge]
  rw [M.connCubeMass_eq_sum_vertex r, ENNReal.toReal_sum hne]
  calc ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal
      ≤ ∑ _y ∈ E1Sign.ballF M r, ((C3 + C4) * Cp) * drv * chi M r ^ 4 :=
        Finset.sum_le_sum hb
    _ = (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul, E1Sign.card_ballF]
        ring

/-- **The final consumer bridge.**  The per-vertex two-term bound, together with the polygon
driver inputs for `ℓ = 3, 4` and the Case-3 moment gap, yields the source's Case-3 error estimate
`E_{2,r} ≤ ((C₃ + C₄) Cp / c₃) (∇_{r^c} + r^{-c})` eventually, with no other input.  The remaining
open input is `TwoTermStarGap` itself. -/
theorem p2ExclError_le_of_twoTermStarGap (C3 C4 Cp c c3 : ℝ) (hgap : TwoTermStarGap M C3 C4)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hM3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hT3 : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r)
    (hT4 : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ Cp * M.case3Driver c r * chi M r)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop,
      M.p2ExclError r ≤ (((C3 + C4) * Cp) / c3) * M.case3Driver c r := by
  have hK : (0 : ℝ) ≤ (C3 + C4) * Cp := by positivity
  refine M.p2ExclError_le_case3Driver (K := (C3 + C4) * Cp) (c := c) (r₀ := 1) hK hc3
    (fun r hr => h2 r hr) hcm ?_ hgm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact connCubeMass_toReal_le_of_twoTermStarGap M C3 C4 Cp (M.case3Driver c r) hgap hC3 hC4 hCp
    (M.case3Driver_nonneg_of_one_le hr) r hr (hM3 r hr) (hT3 r hr) (hT4 r hr)

/-! ## The residual: the pointwise `ℓ = 3` driver is not instantiable -/

/-- **The pointwise `ℓ = 3` polygon driver of the consumer bridge cannot hold.**  The diagonal
entry satisfies `T³(0,0) ≥ T(0,0)³ = 1`, so a per-vertex driver `T³(0,y) ≤ Cp drv` with
`Cp drv < 1` fails at `y = 0` whenever the window contains the origin.  This is the precise reason
why `connCubeMass_toReal_le_of_twoTermStarGap` cannot be fed by the landed pointwise `ℓ = 4`
manufacturer alone: the `ℓ = 3` term needs the windowed near/far treatment, and this packet does
not supply it. -/
theorem pointwise_driver_three_obstructed (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) {Cp drv : ℝ}
    (h0 : (0 : M.V) ∈ E1Sign.ballF M r) (hh : Cp * drv < 1) :
    ¬ (∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * drv) := by
  intro h
  have h1 : 1 ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 :=
    PercLib.CriticalLRP.I420Case3.one_le_polyK_three_of_chi_ne_top M r hχ
  have h2 := h 0 h0
  linarith

end PercLib.CriticalLRP.I417QZeroConsumer
