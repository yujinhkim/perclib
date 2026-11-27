/-
Ultramath swarm `smwziumdb`, member `m5`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`, member `m5`.
Product-numerator integration based on production commit `e59e9347a3988d8c181ba0308758fa84fc2ec15f`.

# Case 3 of Proposition I.4.15 from the *proved* `(2,1)` product gap

See `Defs.lean` for the statement of the reduction.  This file proves:

* `case3Numerator_eq_sum_sub_sum` — the source's Case-3 numerator `|B_r|E|K|E|K|² −
  E[|K|∑1(y∉K)|K_y|²]` is the difference of the two window sums of the `(2,1)` factors, with the
  second moment moved to the window vertex (`volSq_cutProb_eq`, the only place translation
  invariance is used) and the excluded moment read at the swapped pair (`exclMassQuad_eq_sum_exclMomentSq`,
  pure pointwise connectivity symmetry `0 ∉ K_y ↔ y ∉ K_0`);
* `case3Numerator_le_case3DiffWindow` — difference of sums to sum of differences;
* `case3Numerator_le_polygonWindow` — the landed printed `p = 2`, `q = 1` display
  (`I417Example.printed_le`) summed over the window;
* the real-valued consumer: `p2ExclError_le_polygonWindow_div`, the polygon-input producer
  `polygonWindow_toReal_le_of_inputs`, and `p2ExclError_le_case3Driver_of_polygonWindow`.

The `q = 0` star `E[|K|³|K ∩ B_r|]` (`M.connCubeMass`) and the `p = 3`, `q = 0` input `hgap` of
`SecondMomentCase3` do not appear anywhere below.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.Defs

/-! # Case-3 product-numerator identities and consumers -/

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The pointwise integrand identity

`|K_y|² 1(0 ∉ K_y) |K_0| = |K_0| 1(y ∉ K_0) |K_y|²`, purely from `0 ∈ K_y ↔ y ∈ K_0`. -/

theorem exclMomentSq_integrand_eq (y : M.V) (ω : Config M.V) :
    clusterVol ω (0 : M.V) * ((((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) *
        clusterVol ω y ^ 2)
      = clusterVol ω y ^ 2 * ((cluster ω y)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) (0 : M.V) *
          clusterVol ω (0 : M.V) := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have h' : (0 : M.V) ∈ cluster ω y :=
      (PercLib.Percolation.Bond.mem_cluster_comm ω (0 : M.V) y).mp h
    rw [Set.indicator_of_notMem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h),
      Set.indicator_of_notMem (s := (cluster ω y)ᶜ) (by simpa using h')]
    simp
  · have h' : (0 : M.V) ∉ cluster ω y :=
      fun hh => h ((PercLib.Percolation.Bond.mem_cluster_comm ω (0 : M.V) y).mpr hh)
    rw [Set.indicator_of_mem (s := (cluster ω (0 : M.V))ᶜ) (by simpa using h),
      Set.indicator_of_mem (s := (cluster ω y)ᶜ) (by simpa using h')]
    ring

/-! ## 2. The excluded mass is the window sum of the per-vertex `(2,1)` excluded moments -/

theorem exclMassQuad_eq_sum_exclMomentSq (r : ℝ) :
    M.exclMassQuad r =
      ∑ y ∈ E1Sign.ballF M r, I417.exclMomentSq (M.cutProb r) y (0 : M.V) := by
  rw [exclMassQuad, E1Sign.cutLaw_eq_edgeMeasure]
  simp only [exclSumQuad]
  have hstep : ∀ y : M.V,
      ∫⁻ ω, clusterVol ω (0 : M.V) *
        ((((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) * clusterVol ω y ^ 2)
        ∂(edgeMeasure (M.cutProb r))
        = I417.exclMomentSq (M.cutProb r) y (0 : M.V) := by
    intro y
    rw [I417.exclMomentSq]
    exact lintegral_congr fun ω => exclMomentSq_integrand_eq (M := M) y ω
  calc ∫⁻ ω, clusterVol ω (0 : M.V) *
        ∑ y ∈ E1Sign.ballF M r,
          (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) * clusterVol ω y ^ 2
        ∂(edgeMeasure (M.cutProb r))
      = ∫⁻ ω, ∑ y ∈ E1Sign.ballF M r, clusterVol ω (0 : M.V) *
          ((((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) * clusterVol ω y ^ 2)
          ∂(edgeMeasure (M.cutProb r)) := by
          refine lintegral_congr fun ω => ?_
          rw [Finset.mul_sum]
    _ = ∑ y ∈ E1Sign.ballF M r, ∫⁻ ω, clusterVol ω (0 : M.V) *
          ((((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) * clusterVol ω y ^ 2)
          ∂(edgeMeasure (M.cutProb r)) := by
          refine lintegral_finsetSum _ fun y _ => ?_
          have hind : Measurable fun ω : Config M.V =>
              ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y :=
            Measurable.indicator (f := fun _ : Config M.V => (1 : ℝ≥0∞)) measurable_const
              (measurableSet_cluster_mem (0 : M.V) y).compl
          exact (measurable_clusterVol (0 : M.V)).mul
            (hind.mul ((measurable_clusterVol y).pow_const 2))
    _ = ∑ y ∈ E1Sign.ballF M r, I417.exclMomentSq (M.cutProb r) y (0 : M.V) :=
          Finset.sum_congr rfl fun y _ => hstep y

/-! ## 3. Root independence of the two moments at the cutoff law

The first moment is landed (`M.cutProb_rowSum`); the second moment is translation invariance of
`|K_v|²`, transported exactly as `M.cutMassAt_translate`. -/

/-- `E|K_y| = E|K_0|` at the cutoff law, as `I417.meanVol`. -/
theorem meanVol_cutProb (r : ℝ) (v : M.V) :
    I417.meanVol (M.cutProb r) v = M.cutMoment 1 r := by
  rw [I417.meanVol, M.cutProb_rowSum r v, M.cutMassAt_zero_eq_cutMoment r]

/-- The transitivity hypothesis of `I417Example.printed_le` at the cutoff model. -/
theorem meanVol_cutProb_root (r : ℝ) (v : M.V) :
    I417.meanVol (M.cutProb r) v = I417.meanVol (M.cutProb r) (0 : M.V) := by
  rw [meanVol_cutProb M r v, meanVol_cutProb M r (0 : M.V)]

/-- Second cutoff moment at any vertex equals the root second moment (translation invariance). -/
theorem cutMomentTwoAt_translate (r : ℝ) (a x : M.V) :
    (∫⁻ ω, clusterVol ω (x + a) ^ 2 ∂(M.cutLaw r)) =
      ∫⁻ ω, clusterVol ω x ^ 2 ∂(M.cutLaw r) := by
  have hlin : ∫⁻ ω, clusterVol ω (x + a) ^ 2 ∂((M.cutLaw r).map (shiftConfig a)) =
      ∫⁻ ω, clusterVol (shiftConfig a ω) (x + a) ^ 2 ∂(M.cutLaw r) :=
    lintegral_map ((measurable_clusterVol (x + a)).pow_const 2) (measurable_shiftConfig a)
  rw [M.cutLaw_map_shiftConfig r a] at hlin
  rw [hlin]
  exact lintegral_congr fun ω => by rw [M.clusterVol_shiftConfig a ω x]

/-- `E|K_y|² = E|K_0|²` at the cutoff law: `I417.volSq` is the second cutoff moment. -/
theorem volSq_cutProb_eq (r : ℝ) (y : M.V) :
    I417.volSq (M.cutProb r) y = M.cutMoment 2 r := by
  have h := M.cutMomentTwoAt_translate r y (0 : M.V)
  simp only [zero_add] at h
  change (∫⁻ ω, clusterVol ω y ^ 2 ∂(edgeMeasure (M.cutProb r))) = M.cutMoment 2 r
  rw [show (edgeMeasure (M.cutProb r)) = M.cutLaw r from rfl, cutMoment]
  exact h

/-! ## 4. The matrix powers `T^ℓ` as iterated powers, and their symmetry -/

theorem iterPow_three_eq {V : Type*} [Countable V] [DecidableEq V]
    (k : V → V → ℝ≥0∞) (x y : V) :
    I417Base.iterPow k 3 x y = ∑' a, ∑' b, k x a * k a b * k b y := by
  classical
  have hinner : ∀ b : V, (∑' c : V, k b c * (if c = y then (1 : ℝ≥0∞) else 0)) = k b y := by
    intro b
    rw [tsum_eq_single y]
    · simp
    · intro c hc; simp [hc]
  simp only [I417Base.iterPow, I417Base.step, hinner]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun b => (mul_assoc _ _ _).symm

theorem iterPow_four_eq {V : Type*} [Countable V] [DecidableEq V]
    (k : V → V → ℝ≥0∞) (x y : V) :
    I417Base.iterPow k 4 x y = ∑' a, ∑' b, ∑' c, k x a * k a b * k b c * k c y := by
  classical
  have hinner : ∀ c : V, (∑' d : V, k c d * (if d = y then (1 : ℝ≥0∞) else 0)) = k c y := by
    intro c
    rw [tsum_eq_single y]
    · simp
    · intro d hd; simp [hd]
  simp only [I417Base.iterPow, I417Base.step, hinner]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [← mul_assoc, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun c => (by ring)

/-- `I417.T3` is the threefold iterated power of the connection kernel. -/
theorem T3_eq_iterPow (r : ℝ) (x y : M.V) :
    I417.T3 (M.cutProb r) x y =
      I417Base.iterPow (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) 3 x y := by
  rw [iterPow_three_eq]
  rfl

/-- `I417.T4` is the fourfold iterated power of the connection kernel. -/
theorem T4_eq_iterPow (r : ℝ) (x y : M.V) :
    I417.T4 (M.cutProb r) x y =
      I417Base.iterPow (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) 4 x y := by
  rw [iterPow_four_eq]
  rfl

/-- Powers of the cutoff connection kernel are symmetric (the kernel is). -/
theorem iterPow_cutProb_comm (r : ℝ) (n : ℕ) (x y : M.V) :
    I417Base.iterPow (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) n x y
      = I417Base.iterPow (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) n y x :=
  I417Base.iterPow_comm _ (fun a b => by rw [I417Example.connSet_comm]) n x y

/-- The `ℓ = 3` cutoff matrix power is symmetric. -/
theorem T3_comm_cutProb (r : ℝ) (x y : M.V) :
    I417.T3 (M.cutProb r) x y = I417.T3 (M.cutProb r) y x := by
  rw [T3_eq_iterPow M r x y, T3_eq_iterPow M r y x]
  exact iterPow_cutProb_comm M r 3 x y

/-- The `ℓ = 4` cutoff matrix power is symmetric. -/
theorem T4_comm_cutProb (r : ℝ) (x y : M.V) :
    I417.T4 (M.cutProb r) x y = I417.T4 (M.cutProb r) y x := by
  rw [T4_eq_iterPow M r x y, T4_eq_iterPow M r y x]
  exact iterPow_cutProb_comm M r 4 x y

/-! ## 5. The source numerator as a difference of window sums -/

/-- **The Case-3 numerator, exactly.**  The product term is `∑_y E|K_y|² E|K_0|` (the second
moment at the window vertex, root-independent by `volSq_cutProb_eq`) and the subtracted term is
the window sum of the `(2,1)` excluded moments at the swapped pair. -/
theorem case3Numerator_eq_sum_sub_sum (r : ℝ) :
    M.case3Numerator r
      = (∑ y ∈ E1Sign.ballF M r,
            I417.volSq (M.cutProb r) y * I417.meanVol (M.cutProb r) (0 : M.V))
          - ∑ y ∈ E1Sign.ballF M r, I417.exclMomentSq (M.cutProb r) y (0 : M.V) := by
  rw [case3Numerator, exclMassQuad_eq_sum_exclMomentSq M r]
  congr 1
  rw [Finset.sum_congr rfl (fun y _ => by rw [volSq_cutProb_eq M r y, meanVol_cutProb M r (0 : M.V)]),
    Finset.sum_const, nsmul_eq_mul, E1Sign.card_ballF, mul_assoc]

/-- **The per-vertex identity (exact).**  For each window vertex `y`, the `(2,1)`
product-minus-excluded difference at the swapped pair `(y,0)` *is* the `y`-summand of the source's
Case-3 numerator:

`E|K|²·E|K| − E[|K_0| 1(y∉K_0)|K_y|²] = I417.volSq y · I417.meanVol 0 − I417.exclMomentSq y 0`.

The first equality of the proof is root independence of the second moment (`volSq_cutProb_eq`)
and of the first moment (`meanVol_cutProb`); the second is the pointwise swap
`exclMomentSq_integrand_eq` (connectivity symmetry only). -/
theorem perVertex_case3_eq_p21 (r : ℝ) (y : M.V) :
    M.cutMoment 2 r * M.cutMoment 1 r -
        ∫⁻ ω, clusterVol ω (0 : M.V) *
          ((((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y) * clusterVol ω y ^ 2)
          ∂(M.cutLaw r)
      = I417.volSq (M.cutProb r) y * I417.meanVol (M.cutProb r) (0 : M.V) -
          I417.exclMomentSq (M.cutProb r) y (0 : M.V) := by
  rw [volSq_cutProb_eq M r y, meanVol_cutProb M r (0 : M.V)]
  congr 1
  rw [I417.exclMomentSq, show (edgeMeasure (M.cutProb r)) = M.cutLaw r from rfl]
  exact lintegral_congr fun ω => exclMomentSq_integrand_eq (M := M) y ω

/-- **Difference of sums to sum of differences** (the `ℝ≥0∞` direction needed here:
`∑ A − ∑ B ≤ ∑ (A − B)`). -/
theorem tsub_sum_le_sum_tsub {ι : Type*} (s : Finset ι) (A B : ι → ℝ≥0∞) :
    (∑ i ∈ s, A i) - (∑ i ∈ s, B i) ≤ ∑ i ∈ s, (A i - B i) := by
  rw [tsub_le_iff_right]
  calc (∑ i ∈ s, A i) ≤ ∑ i ∈ s, ((A i - B i) + B i) :=
        Finset.sum_le_sum fun i _ => le_tsub_add
    _ = (∑ i ∈ s, (A i - B i)) + ∑ i ∈ s, B i := Finset.sum_add_distrib

/-- The transitivity hypothesis of `I417Example.printed_le`: all roots agree. -/
theorem meanVol_cutProb_eq (r : ℝ) (v w : M.V) :
    I417.meanVol (M.cutProb r) v = I417.meanVol (M.cutProb r) w := by
  rw [meanVol_cutProb M r v, meanVol_cutProb M r w]

/-- **Difference of sums to sum of differences.** -/
theorem case3Numerator_le_case3DiffWindow (r : ℝ) :
    M.case3Numerator r ≤ M.case3DiffWindow r := by
  rw [case3Numerator_eq_sum_sub_sum M r, case3DiffWindow]
  exact tsub_sum_le_sum_tsub _ _ _

/-! ## 6. Summing the printed `(2,1)` display over the window -/

theorem case3DiffWindow_le_polygonWindow (r : ℝ) :
    M.case3DiffWindow r ≤ M.polygonWindow r := by
  refine Finset.sum_le_sum fun y _ => ?_
  have h := I417Example.printed_le (M.cutProb r) (fun e => AuditM2.cutProb_lt_one M r e)
    y (0 : M.V) (meanVol_cutProb_eq M r · y)
  rw [meanVol_cutProb M r y] at h
  refine h.trans (le_of_eq ?_)
  rw [T3_comm_cutProb M r y (0 : M.V), T4_comm_cutProb M r y (0 : M.V),
    ← M.cutMassAt_zero_eq_cutMoment r]
  ring

/-- **The Case-3 numerator is bounded by the window sum of the printed `(2,1)` display.**
No star, no joint moment, no restoration. -/
theorem case3Numerator_le_polygonWindow (r : ℝ) :
    M.case3Numerator r ≤ M.polygonWindow r :=
  (case3Numerator_le_case3DiffWindow M r).trans (case3DiffWindow_le_polygonWindow M r)

/-! ## 7. Real-valued form: the two matrix powers are the landed `polyK` entries

`I417.T3/Eq_iterPow` composed with `AuditM2.iterPow_eq_Kpow`, `AuditM2.cutProb_kernel` and
`M.cutKpow_toReal_eq_polyK` identifies the `ℝ≥0∞` powers of the printed display with the real
`I418C.polyK (M.cutTwoPoint r) ℓ 0 y` used by the landed Lemma-I.4.18 inputs. -/

theorem T3_toReal_eq_polyK (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    (I417.T3 (M.cutProb r) (0 : M.V) y).toReal =
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := by
  rw [T3_eq_iterPow, AuditM2.iterPow_eq_Kpow, AuditM2.cutProb_kernel]
  exact M.cutKpow_toReal_eq_polyK r hχ 3 (0 : M.V) y

theorem T4_toReal_eq_polyK (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    (I417.T4 (M.cutProb r) (0 : M.V) y).toReal =
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y := by
  rw [T4_eq_iterPow, AuditM2.iterPow_eq_Kpow, AuditM2.cutProb_kernel]
  exact M.cutKpow_toReal_eq_polyK r hχ 4 (0 : M.V) y

theorem T3_ne_top_cutProb (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    I417.T3 (M.cutProb r) (0 : M.V) y ≠ ⊤ := by
  rw [T3_eq_iterPow, AuditM2.iterPow_eq_Kpow, AuditM2.cutProb_kernel]
  exact M.cutKpow_ne_top_of_chi_ne_top r hχ 3 (0 : M.V) y

theorem T4_ne_top_cutProb (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    I417.T4 (M.cutProb r) (0 : M.V) y ≠ ⊤ := by
  rw [T4_eq_iterPow, AuditM2.iterPow_eq_Kpow, AuditM2.cutProb_kernel]
  exact M.cutKpow_ne_top_of_chi_ne_top r hχ 4 (0 : M.V) y

/-- **The windowed numerator estimate in `ℝ`**: the `ℝ≥0∞` polygon window is the explicit real
sum of the landed `polyK` entries. -/
theorem polygonWindow_toReal_eq (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    (M.polygonWindow r).toReal =
      ∑ y ∈ E1Sign.ballF M r,
        (I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4 +
          2 * (I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3)) := by
  have hpow : (M.cutMassAt r 0) ≠ ⊤ := hχ
  have hne : ∀ y ∈ E1Sign.ballF M r,
      I417.T3 (M.cutProb r) (0 : M.V) y * (M.cutMassAt r 0) ^ 4 +
        2 * (I417.T4 (M.cutProb r) (0 : M.V) y * (M.cutMassAt r 0) ^ 3) ≠ ⊤ := by
    intro y _
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top (M.T3_ne_top_cutProb r hχ y) (ENNReal.pow_ne_top hpow)
    · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (M.T4_ne_top_cutProb r hχ y)
        (ENNReal.pow_ne_top hpow))
  rw [polygonWindow, ENNReal.toReal_sum hne]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h3 : I417.T3 (M.cutProb r) (0 : M.V) y ≠ ⊤ := M.T3_ne_top_cutProb r hχ y
  have h4 : I417.T4 (M.cutProb r) (0 : M.V) y ≠ ⊤ := M.T4_ne_top_cutProb r hχ y
  have h34 : I417.T4 (M.cutProb r) (0 : M.V) y * (M.cutMassAt r 0) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top h4 (ENNReal.pow_ne_top hχ)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top h3 (ENNReal.pow_ne_top hχ))
      (ENNReal.mul_ne_top (by norm_num) h34),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, M.T3_toReal_eq_polyK r hχ y,
    M.T4_toReal_eq_polyK r hχ y]

/-- The polygon window is finite as soon as the first moment is. -/
theorem polygonWindow_ne_top (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    M.polygonWindow r ≠ ⊤ := by
  rw [polygonWindow]
  refine ENNReal.sum_ne_top.2 fun y _ => ?_
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · exact ENNReal.mul_ne_top (M.T3_ne_top_cutProb r hχ y) (ENNReal.pow_ne_top hχ)
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (M.T4_ne_top_cutProb r hχ y)
      (ENNReal.pow_ne_top hχ))

/-! ## 8. `𝓔_{2,r}` as the normalised Case-3 numerator -/

/-- **`𝓔_{2,r}` is the normalised Case-3 numerator.**  This is the definition of `cE2` together
with `ENNReal.toReal_sub_of_le` and the non-negativity `exclMassQuad_le_ball_mul_moments`; no
`⊤ ↦ 0` conversion is made. -/
theorem p2ExclError_eq_case3Numerator_toReal (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2ExclError r =
      (M.case3Numerator r).toReal /
        (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hA : ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 2 r * M.cutMoment 1 r ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) h2) h1
  have hBA : M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 2 r * M.cutMoment 1 r := by
    refine (M.exclMassQuad_le_ball_mul_moments r).trans (le_of_eq ?_)
    ring
  have hsub : (M.case3Numerator r).toReal
      = ((M.ball r).ncard : ℝ) * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal
        - (M.exclMassQuad r).toReal := by
    rw [case3Numerator, ENNReal.toReal_sub_of_le hBA hA, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [hsub, p2ExclError, VolumeMoments.cE2]
  ring

/-! ## 9. The real-valued Case-3 error bound -/

/-- **`𝓔_{2,r}` is bounded by the normalised polygon window.** -/
theorem p2ExclError_le_polygonWindow_div (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2ExclError r ≤ (M.polygonWindow r).toReal /
      (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hχ : M.cutMassAt r 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment r]; exact h1
  have hmono : (M.case3Numerator r).toReal ≤ (M.polygonWindow r).toReal :=
    ENNReal.toReal_mono (M.polygonWindow_ne_top r hχ) (M.case3Numerator_le_polygonWindow r)
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1; linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2; linarith
  rw [p2ExclError_eq_case3Numerator_toReal M r h2]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr hmono

/-- **The windowed polygon inputs give the source's numerator estimate.**

`x ↦ (polygonWindow r).toReal` is split as `(∑_y T³(0,y)) χ⁴ + 2 (∑_y T⁴(0,y)) χ³`; the
windowed `ℓ = 3` input bounds the first factor and the per-vertex `ℓ = 4` input bounds the
second summand by `|B_r| Cp drv χ`.  With the printed constants `1` and `2` this is
`|B_r| · 3Cp · (∇_{r^c}+r^{-c}) · χ⁴`. -/
theorem polygonWindow_toReal_le_of_inputs {Cp c r : ℝ} (hP : M.PolygonWindowInputs Cp c)
    (hr1 : 1 ≤ r) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    (M.polygonWindow r).toReal ≤
      ((M.ball r).ncard : ℝ) * (3 * Cp) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4 := by
  obtain ⟨hW3, hP4⟩ := hP
  have hχ0 : 0 ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ ((M.ball r).ncard : ℝ) := by positivity
  have hsplit : (M.polygonWindow r).toReal
      = (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
          * (M.cutMassAt r 0).toReal ^ 4
        + 2 * ((∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
          * (M.cutMassAt r 0).toReal ^ 3) := by
    rw [polygonWindow_toReal_eq M r hχ, Finset.sum_add_distrib, Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_mul]
  have h3 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
      ≤ Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r := hW3 r hr1
  have h4 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
      ≤ ((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
    calc (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
        ≤ ∑ _y ∈ E1Sign.ballF M r, Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal :=
          Finset.sum_le_sum fun y _ => hP4 r (by linarith) y
      _ = ((E1Sign.ballF M r).card : ℝ) *
            (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((M.ball r).ncard : ℝ) *
            (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by rw [E1Sign.card_ballF]
  have hfirst := mul_le_mul_of_nonneg_right h3 (pow_nonneg hχ0 4)
  have hsecond := mul_le_mul_of_nonneg_right h4 (pow_nonneg hχ0 3)
  calc (M.polygonWindow r).toReal
      = (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
          * (M.cutMassAt r 0).toReal ^ 4
        + 2 * ((∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
          * (M.cutMassAt r 0).toReal ^ 3) := hsplit
    _ ≤ (Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r) * (M.cutMassAt r 0).toReal ^ 4
        + 2 * ((((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal))
          * (M.cutMassAt r 0).toReal ^ 3) := by linarith
    _ = ((M.ball r).ncard : ℝ) * (3 * Cp) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4 := by
        ring

/-! ## 10. Case 3: `𝓔_{2,r} ⪯ (∇_{r^c} + r^{-c})` from the `(2,1)` route -/

/-- **The new Case-3 consumer**: from the windowed `(2,1)` numerator estimate and the moment gap,
`𝓔_{2,r} ≤ (K/c₃)(∇_{r^c}+r^{-c})` eventually.  This is the replacement for the `hgap` consumer
`SecondMomentCase3.p2ExclError_le_case3Driver`, whose numerator input was the `p = 3`, `q = 0`
star `M.connCubeMass`. -/
theorem p2ExclError_le_case3Driver_of_polygonWindow {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    {r₀ : ℝ} (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hwin : ∀ᶠ r : ℝ in atTop, (M.polygonWindow r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤ (K / c3) * M.case3Driver c r := by
  filter_upwards [hwin, hgm, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hn hg hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h2r := h2 r hr
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at this
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0.le
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  refine (M.p2ExclError_le_polygonWindow_div r hr0.le h2r).trans ?_
  have hA1 : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    rw [hχeq]
    exact hχ
  refine SecondMomentCase3.ratio_le_of_moment_gap (C := (M.polygonWindow r).toReal)
    (b := ((M.ball r).ncard : ℝ)) (A1 := (M.cutMoment 1 r).toReal)
    (A2 := (M.cutMoment 2 r).toReal) (χ := (M.cutMassAt r 0).toReal)
    (drv := M.case3Driver c r) (K := K) (c3 := c3) hb hA1 hA2 hχ hdrv hχeq hK hc3 hg hn

/-- **Case 3: `𝓔_{2,r} → 0` from the `(2,1)` route.** -/
theorem p2ExclError_tendsto_zero_of_polygonWindow {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    {r₀ : ℝ} (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hwin : ∀ᶠ r : ℝ in atTop, (M.polygonWindow r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hle := M.p2ExclError_le_case3Driver_of_polygonWindow hK hc3 h2 hwin hgm
  have hratio : Tendsto (fun r : ℝ => (K / c3) * M.case3Driver c r) atTop (𝓝 0) := by
    have h := tendsto_const_nhds.mul hdrv (a := K / c3)
    simpa using h
  refine squeeze_zero' ?_ hle hratio
  filter_upwards [eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  exact M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)

/-- **Case 3: logarithmic integrability of `𝓔_{2,r}` from the `(2,1)` route.** -/
theorem logIntegrable_p2ExclError_of_polygonWindow {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hmeas : Measurable M.p2ExclError)
    {r₀ : ℝ} (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hwin : ∀ᶠ r : ℝ in atTop, (M.polygonWindow r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c)) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  have hle := M.p2ExclError_le_case3Driver_of_polygonWindow hK hc3 h2 hwin hgm
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le_const_mul hmeas hlogdrv
    (div_nonneg hK hc3.le) ?_
  filter_upwards [hle, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hbnd hr hr1
  have h0 : 0 ≤ M.p2ExclError r :=
    M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)
  have hd : 0 ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  rw [abs_of_nonneg h0, abs_of_nonneg hd]
  exact hbnd

/-! ## 11. Case 3 with the windowed polygon bundle and no star input

The bundle consumed here is the polygon part of the landed
`SecondMomentCase3.Case3PolygonBundleWindowed` — the windowed `ℓ = 3` sum and the per-vertex
`ℓ = 4` bound — which `WindowedEllThree/Repaired.lean`'s
`M.exists_repaired_case3_polygon_bundle` produces from the paper's own hypotheses (triangle
condition, first-moment asymptotic, open-triangle log-radial bound).  The star hypotheses
`hc : M.connCubeMass r ≠ ⊤` and `hgap` of `secondMoment_asymptotic_case3_windowed` are absent. -/

theorem p2ExclError_tendsto_zero_of_polygonBundle {c Cp : ℝ} (hCp : 0 < Cp)
    (hW3 : M.WindowedEllThreeGap c Cp)
    (hP4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    {r₀ : ℝ} (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hPw : M.PolygonWindowInputs Cp c := ⟨hW3, hP4⟩
  have hK : (0 : ℝ) ≤ 3 * Cp := by linarith
  have hwin : ∀ᶠ r : ℝ in atTop, (M.polygonWindow r).toReal ≤
      (3 * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r *
        (M.cutMassAt r 0).toReal ^ 4 := by
    filter_upwards [eventually_ge_atTop (max r₀ 1)] with r hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hr
    have hχ : M.cutMassAt r 0 ≠ ⊤ := by
      rw [M.cutMassAt_zero_eq_cutMoment r]; exact h1 r hr0
    refine (M.polygonWindow_toReal_le_of_inputs hPw hr1 hχ).trans (le_of_eq ?_)
    ring
  exact M.p2ExclError_tendsto_zero_of_polygonWindow hK hc3 h2 hwin hgm hdrv

theorem logIntegrable_p2ExclError_of_polygonBundle {c Cp : ℝ} (hCp : 0 < Cp)
    (hW3 : M.WindowedEllThreeGap c Cp)
    (hP4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hmeas : Measurable M.p2ExclError)
    {r₀ : ℝ} (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  have hPw : M.PolygonWindowInputs Cp c := ⟨hW3, hP4⟩
  have hK : (0 : ℝ) ≤ 3 * Cp := by linarith
  have hwin : ∀ᶠ r : ℝ in atTop, (M.polygonWindow r).toReal ≤
      (3 * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r *
        (M.cutMassAt r 0).toReal ^ 4 := by
    filter_upwards [eventually_ge_atTop (max r₀ 1)] with r hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hr
    have hχ : M.cutMassAt r 0 ≠ ⊤ := by
      rw [M.cutMassAt_zero_eq_cutMoment r]; exact h1 r hr0
    refine (M.polygonWindow_toReal_le_of_inputs hPw hr1 hχ).trans (le_of_eq ?_)
    ring
  exact M.logIntegrable_p2ExclError_of_polygonWindow hK hc3 hmeas h2 hwin hgm hlogdrv

/-- **Proposition I.4.15, Case 3 (`E_{β_c,r}|K|² ∼ A r^{3α}`) with the `p = 2`, `q = 1` product
gap as numerator input.**  Every hypothesis is one of the source's own inputs or the windowed
polygon bundle; neither `M.connCubeMass r ≠ ⊤` nor the `p = 3`, `q = 0` gap `hgap` occurs. -/
theorem secondMoment_asymptotic_case3_p21 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c Cp : ℝ} (hCp : 0 < Cp)
    (hW3 : M.WindowedEllThreeGap c Cp)
    (hP4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have hH := M.p2H_tendsto_zero_of_hP hP
  exact M.tendsto_div_two hα hr₀ hβ hac hae h1 h2
    (M.p2ExclError_tendsto_zero_of_polygonBundle hCp hW3 hP4 hdrv h1 h2 hc3 hgm)
    hH (PivotFlux.tendsto_cutE0 M)
    (M.logIntegrable_p2Ebar hmeasEbar
      (M.logIntegrable_p2ExclError_of_polygonBundle hCp hW3 hP4 hlogdrv hmeasE2 h1 h2 hc3 hgm)
      hlogH hlogE0 hH)

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
