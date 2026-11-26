/- Integrated from `.scratch/case3-split-draft/Main.lean` at production base
`1266415364a0ad5f96cb689b36fbed1778a2af1f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Bound

/-! # Discrepancy bounds from the split polygon interface -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Finset
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-- Sum the tree polynomial against a summed threefold estimate and a pointwise
higher-depth estimate. The two factors remain explicit in the conclusion. -/
theorem polygon_sum_le_split {π : Sym2 V → unitInterval} {o : V} {B : Finset V}
    {p : ℕ} (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ} {Bthree Btail : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hPoly : HasSplitPolygonBound π o B p poly Bthree Btail) :
    ∑ y ∈ B, treePoly poly C (I420Case1.powMomentAt π 1 o) p y ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
        (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          I420Case1.powMomentAt π 1 o ^ (2 * p) := by
  let M := I420Case1.powMomentAt π 1 o
  have hswap := sum_treePoly_eq B poly C M p
  have hstep : ∀ j ∈ Finset.Icc 3 (p + 2),
      ∑ y ∈ B, ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j) =
        ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j) := by
    intro j _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hsum : ∀ j ∈ Finset.Icc 3 (p + 2),
      (∑ y ∈ B, poly y j) ≤ (B.card : ℝ≥0∞) *
        ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3)) := by
    intro j hj
    have h3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ p + 2 := (Finset.mem_Icc.mp hj).2
    by_cases hje : j = 3
    · subst j
      calc (∑ y ∈ B, poly y 3) ≤ (B.card : ℝ≥0∞) * ENNReal.ofReal Bthree :=
            hPoly.three
        _ ≤ (B.card : ℝ≥0∞) *
            ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (3 - 3)) := by
          simp only [Nat.sub_self, pow_zero, mul_one]
          exact mul_le_mul_right le_self_add _
    · have h4 : 4 ≤ j := by omega
      have hb : ∀ y ∈ B, poly y j ≤ ENNReal.ofReal Btail * M ^ (j - 3) :=
        fun y hy => hPoly.tail y hy j (Finset.mem_Icc.mpr ⟨h4, hj2⟩)
      calc (∑ y ∈ B, poly y j)
          ≤ (B.card : ℝ≥0∞) * (ENNReal.ofReal Btail * M ^ (j - 3)) :=
            sum_poly_le B poly M j Btail hb
        _ ≤ (B.card : ℝ≥0∞) *
            ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3)) := by
          exact mul_le_mul_right (mul_le_mul_left le_add_self _) _
  have hbound : ∀ j ∈ Finset.Icc 3 (p + 2),
      ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j) ≤
        ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
          ((B.card : ℝ≥0∞) *
            ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3))) := by
    intro j hj
    exact mul_le_mul_right (hsum j hj) _
  have hcollapse : ∀ j ∈ Finset.Icc 3 (p + 2),
      ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
          ((B.card : ℝ≥0∞) *
            ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3))) =
        (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          (ENNReal.ofReal (C j) * M ^ (2 * p)) := by
    intro j hj
    have h3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ p + 2 := (Finset.mem_Icc.mp hj).2
    calc ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
          ((B.card : ℝ≥0∞) *
            ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3))) =
        ENNReal.ofReal (C j) * (M ^ (2 * p + 3 - j) * M ^ (j - 3)) *
          ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail)) := by ring
      _ = ENNReal.ofReal (C j) * M ^ (2 * p) *
          ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail)) := by
        rw [polygon_pow_identity (p := p) M h3 (le_two_mul_add_three hp hj2)]
      _ = (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          (ENNReal.ofReal (C j) * M ^ (2 * p)) := by ring
  calc ∑ y ∈ B, treePoly poly C M p y
      = ∑ j ∈ Finset.Icc 3 (p + 2), ∑ y ∈ B,
          ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j) := hswap
    _ = ∑ j ∈ Finset.Icc 3 (p + 2),
          ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j) :=
        Finset.sum_congr rfl hstep
    _ ≤ ∑ j ∈ Finset.Icc 3 (p + 2),
          ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
            ((B.card : ℝ≥0∞) *
              ((ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (j - 3))) :=
        Finset.sum_le_sum hbound
    _ = ∑ j ∈ Finset.Icc 3 (p + 2),
          (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
            (ENNReal.ofReal (C j) * M ^ (2 * p)) := Finset.sum_congr rfl hcollapse
    _ = (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          (∑ j ∈ Finset.Icc 3 (p + 2), ENNReal.ofReal (C j) * M ^ (2 * p)) := by
        rw [Finset.mul_sum]
    _ = (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          ((∑ j ∈ Finset.Icc 3 (p + 2), ENNReal.ofReal (C j)) * M ^ (2 * p)) := by
        rw [Finset.sum_mul]
    _ = (B.card : ℝ≥0∞) * (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          (ENNReal.ofReal (coeffSum C p) * M ^ (2 * p)) := by
        rw [coeffSum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hC j)]
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
          (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) * M ^ (2 * p) := by ring

/-- The canonical pair discrepancy with separate threefold and higher-depth
polygon factors. -/
theorem prodFactor_le_mixedExcl_add_splitPolygon {π : Sym2 V → unitInterval} {o : V}
    {B : Finset V} {a b p : ℕ} (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {Bthree Btail : ℝ} (hC : ∀ j, 0 ≤ C j)
    (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasSplitPolygonBound π o B p poly Bthree Btail) :
    I420Case1.prodFactor π o a b B ≤ I420Case1.mixedExcl π o a b B +
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
        (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          I420Case1.powMomentAt π 1 o ^ (2 * p) := by
  have hsum : ∑ y ∈ B, pairFactor π o y a b ≤
      ∑ y ∈ B, (pairExcl π o y a b + treePoly poly C
        (I420Case1.powMomentAt π 1 o) p y) := Finset.sum_le_sum hTree.expansion
  rw [Finset.sum_add_distrib, sum_pairFactor] at hsum
  have hstep : ∑ y ∈ B, pairExcl π o y a b = I420Case1.mixedExcl π o a b B :=
    sum_pairExcl o a b B
  rw [hstep] at hsum
  exact hsum.trans (add_le_add_right (polygon_sum_le_split hp hC hPoly) _)

/-- Real-valued version of `prodFactor_le_mixedExcl_add_splitPolygon`, with the same
finiteness hypotheses as the uniform polygon theorem. -/
theorem discrepancy_toReal_le_splitPolygon {π : Sym2 V → unitInterval} {o : V}
    {B : Finset V} {a b p : ℕ} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (hp : 1 ≤ p)
    {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ} {Bthree Btail : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasSplitPolygonBound π o B p poly Bthree Btail)
    (hM1 : I420Case1.powMomentAt π 1 o ≠ ⊤)
    (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    (I420Case1.prodFactor π o a b B).toReal - (I420Case1.mixedExcl π o a b B).toReal ≤
      (B.card : ℝ) * coeffSum C p * (Bthree + Btail) *
        (I420Case1.momR π 1 o) ^ (2 * p) := by
  have hBK : I420Case1.mixedExcl π o a b B ≤ I420Case1.prodFactor π o a b B :=
    I420Case1.mixedExcl_le_prodFactor hπ 𝓔 h𝓔mono h𝓔 o a b B
  have hle : I420Case1.prodFactor π o a b B ≤ I420Case1.mixedExcl π o a b B +
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
        (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          I420Case1.powMomentAt π 1 o ^ (2 * p) :=
    prodFactor_le_mixedExcl_add_splitPolygon hp hC hTree hPoly
  have hprodfin : I420Case1.prodFactor π o a b B ≠ ⊤ := prodFactor_ne_top hMa hMb
  have hmixedfin : I420Case1.mixedExcl π o a b B ≠ ⊤ :=
    ne_top_of_le_ne_top hprodfin hBK
  have hPfin : (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
      (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
        I420Case1.powMomentAt π 1 o ^ (2 * p) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top B.card) ENNReal.ofReal_ne_top)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
      (ENNReal.pow_ne_top hM1)
  have hsub : I420Case1.prodFactor π o a b B - I420Case1.mixedExcl π o a b B ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
        (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          I420Case1.powMomentAt π 1 o ^ (2 * p) :=
    tsub_le_iff_right.mpr (by rw [add_comm]; exact hle)
  have h1 : (I420Case1.prodFactor π o a b B - I420Case1.mixedExcl π o a b B).toReal ≤
      ((B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) *
        (ENNReal.ofReal Bthree + ENNReal.ofReal Btail) *
          I420Case1.powMomentAt π 1 o ^ (2 * p)).toReal :=
    ENNReal.toReal_mono hPfin hsub
  rw [ENNReal.toReal_sub_of_le hBK hprodfin] at h1
  have hCsum : 0 ≤ coeffSum C p := Finset.sum_nonneg fun j _ => hC j
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hCsum,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hPoly.nonneg_three,
    ENNReal.toReal_ofReal hPoly.nonneg_tail, ENNReal.toReal_pow] at h1
  simpa only [I420Case1.momR] using h1

/-- Averaged real discrepancy from the split polygon interface. -/
theorem discR_le_splitPolygon {π : Sym2 V → unitInterval} {o : V} {B : Finset V}
    {a b p : ℕ} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (hp : 1 ≤ p)
    {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ} {Bthree Btail : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasSplitPolygonBound π o B p poly Bthree Btail) (hcard : 0 < B.card)
    (hM1 : I420Case1.powMomentAt π 1 o ≠ ⊤)
    (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    discR π o a b B ≤ coeffSum C p * (Bthree + Btail) *
      (I420Case1.momR π 1 o) ^ (2 * p) := by
  have hc : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hcard
  have h := discrepancy_toReal_le_splitPolygon hπ 𝓔 h𝓔mono h𝓔 hp hC hTree hPoly hM1 hMa hMb
  rw [discR, div_le_iff₀ hc]
  calc (I420Case1.prodFactor π o a b B).toReal - (I420Case1.mixedExcl π o a b B).toReal
      ≤ (B.card : ℝ) * coeffSum C p * (Bthree + Btail) *
          (I420Case1.momR π 1 o) ^ (2 * p) := h
    _ = coeffSum C p * (Bthree + Btail) * (I420Case1.momR π 1 o) ^ (2 * p) *
        (B.card : ℝ) := by ring

end I420Case3

end PercLib.CriticalLRP
