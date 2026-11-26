/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Case 3 of Proposition I.4.20: the discrepancy bound in `ℝ`.  Independent work.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Polygon
public import PercLib.CriticalLRP.Analysis.Route3.Percolation

/-!
# The Case 3 discrepancy bound in `ℝ`, and positivity of the moments

Two things are proved here.

* **Positivity of the moments.**  On the canonical law every cluster contains its
  base point, so `|K_v| ≥ 1` and hence `E|K_v|^m ≥ 1`; consequently every *finite*
  moment is strictly positive.  This is what makes the divisions in the target
  `(E|K|²/E|K|)^{p-1}(E|K|)²` of (I.4.21) legitimate.
* **The `ℝ`-valued Case 3 bound.**  `prodFactor - mixedExcl` is at most
  `|B_r| (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`, and its average over `B_r` is at most
  `(Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`.  The finite `toReal` cases are handled by
  explicit `≠ ⊤` hypotheses, one per moment that occurs.

The source inputs are exactly `HasTreeExpansion` (Lemma I.4.17) and `HasPolygonBound`
(Lemma I.4.18); the BK inequality enters through `I420Case1.mixedExcl_le_prodFactor`,
which is proved in production.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Finset
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-! ## Positivity of the moments -/

/-- Every cluster contains its base point, so `|K_v|^m ≥ 1` pointwise. -/
theorem one_le_clusterVol_pow (ω : Config V) (v : V) (m : ℕ) :
    (1 : ℝ≥0∞) ≤ clusterVol ω v ^ m := by
  calc (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ m := by simp
    _ ≤ clusterVol ω v ^ m := pow_le_pow_left₀ bot_le (one_le_clusterVol ω v) m

/-- **`E|K_v|^m ≥ 1`.**  The canonical law is a probability law and `|K_v| ≥ 1`
identically, so no moment vanishes. -/
theorem one_le_powMomentAt (π : Sym2 V → unitInterval) (m : ℕ) (v : V) :
    (1 : ℝ≥0∞) ≤ I420Case1.powMomentAt π m v := by
  rw [I420Case1.powMomentAt]
  calc (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂(edgeMeasure π) := by
        rw [lintegral_one, measure_univ]
    _ ≤ ∫⁻ ω, clusterVol ω v ^ m ∂(edgeMeasure π) :=
        lintegral_mono fun ω => one_le_clusterVol_pow ω v m

/-- **`E|K_v|^m ≥ 1` for a finite moment**, as a real number. -/
theorem one_le_momR {π : Sym2 V → unitInterval} {m : ℕ} {v : V}
    (h : I420Case1.powMomentAt π m v ≠ ⊤) : 1 ≤ I420Case1.momR π m v := by
  change (1 : ℝ) ≤ (I420Case1.powMomentAt π m v).toReal
  have h1 : ((1 : ℝ≥0∞)).toReal ≤ (I420Case1.powMomentAt π m v).toReal :=
    ENNReal.toReal_mono h (one_le_powMomentAt π m v)
  simpa using h1

/-- **Finiteness makes a moment strictly positive**, `0 < E|K_v|^m`. -/
theorem momR_pos {π : Sym2 V → unitInterval} {m : ℕ} {v : V}
    (h : I420Case1.powMomentAt π m v ≠ ⊤) : 0 < I420Case1.momR π m v :=
  lt_of_lt_of_le one_pos (one_le_momR h)

/-! ## The Case 3 bound in `ℝ` -/

/-- Finiteness of the product factor from finiteness of the two moments. -/
theorem prodFactor_ne_top {π : Sym2 V → unitInterval} {o : V} {B : Finset V} {a b : ℕ}
    (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    I420Case1.prodFactor π o a b B ≠ ⊤ := by
  rw [← sum_pairFactor]
  exact ENNReal.sum_ne_top.mpr fun y hy => ENNReal.mul_ne_top hMa (hMb y hy)

/-- **The Case 3 discrepancy bound in `ℝ`** (the Case 3 display of the proof of
Proposition I.4.20):
`|B| E|K|^a E|K|^b - A_ℓ(r) ≤ |B| (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`. -/
theorem discrepancy_toReal_le_polygon {π : Sym2 V → unitInterval} {o : V} {B : Finset V}
    {a b p : ℕ} (hπ : ∀ e, π e < 1) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {Bpoly : ℝ} (hC : ∀ j, 0 ≤ C j) (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasPolygonBound π o B p poly Bpoly)
    (hM1 : I420Case1.powMomentAt π 1 o ≠ ⊤) (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    (I420Case1.prodFactor π o a b B).toReal - (I420Case1.mixedExcl π o a b B).toReal ≤
      (B.card : ℝ) * coeffSum C p * Bpoly * (I420Case1.momR π 1 o) ^ (2 * p) := by
  have hBK : I420Case1.mixedExcl π o a b B ≤ I420Case1.prodFactor π o a b B :=
    I420Case1.mixedExcl_le_prodFactor hπ 𝓔 h𝓔mono h𝓔 o a b B
  have hle : I420Case1.prodFactor π o a b B ≤ I420Case1.mixedExcl π o a b B +
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
        I420Case1.powMomentAt π 1 o ^ (2 * p) :=
    prodFactor_le_mixedExcl_add_polygon hp hC hTree hPoly
  have hprodfin : I420Case1.prodFactor π o a b B ≠ ⊤ := prodFactor_ne_top hMa hMb
  have hmixedfin : I420Case1.mixedExcl π o a b B ≠ ⊤ :=
    ne_top_of_le_ne_top hprodfin hBK
  have hPfin : (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
      I420Case1.powMomentAt π 1 o ^ (2 * p) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top B.card) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top hM1)
  have hsub : I420Case1.prodFactor π o a b B - I420Case1.mixedExcl π o a b B ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
        I420Case1.powMomentAt π 1 o ^ (2 * p) :=
    tsub_le_iff_right.mpr (by rw [add_comm]; exact hle)
  have h1 : (I420Case1.prodFactor π o a b B -
        I420Case1.mixedExcl π o a b B).toReal ≤
      ((B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
        I420Case1.powMomentAt π 1 o ^ (2 * p)).toReal :=
    ENNReal.toReal_mono hPfin hsub
  rw [ENNReal.toReal_sub_of_le hBK hprodfin] at h1
  have hCsum : 0 ≤ coeffSum C p := Finset.sum_nonneg fun j _ => hC j
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hCsum,
    ENNReal.toReal_ofReal hPoly.nonneg, ENNReal.toReal_pow] at h1
  simpa only [I420Case1.momR] using h1

/-- **The averaged Case 3 bound**: dividing by `|B_r|` gives
`|B_r|^{-1}(|B_r| E|K|^a E|K|^b - A_ℓ(r)) ≤ (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`,
the form in which the source's Case 3 display is used. -/
theorem discR_le_polygon {π : Sym2 V → unitInterval} {o : V} {B : Finset V} {a b p : ℕ}
    (hπ : ∀ e, π e < 1) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {Bpoly : ℝ} (hC : ∀ j, 0 ≤ C j) (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasPolygonBound π o B p poly Bpoly) (hcard : 0 < B.card)
    (hM1 : I420Case1.powMomentAt π 1 o ≠ ⊤) (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    discR π o a b B ≤ coeffSum C p * Bpoly * (I420Case1.momR π 1 o) ^ (2 * p) := by
  have hc : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hcard
  have h := discrepancy_toReal_le_polygon hπ 𝓔 h𝓔mono h𝓔 hp hC hTree hPoly hM1 hMa hMb
  rw [discR, div_le_iff₀ hc]
  calc (I420Case1.prodFactor π o a b B).toReal - (I420Case1.mixedExcl π o a b B).toReal
      ≤ (B.card : ℝ) * coeffSum C p * Bpoly * (I420Case1.momR π 1 o) ^ (2 * p) := h
    _ = coeffSum C p * Bpoly * (I420Case1.momR π 1 o) ^ (2 * p) * (B.card : ℝ) := by ring

/-- **The discrepancy is non-negative**: `A_ℓ(r) ≤ |B_r| E|K|^a E|K|^b` (BK), hence
the averaged discrepancy `discR` is non-negative.  This is the lower half of the
two-sided estimate (I.4.20). -/
theorem discR_nonneg {π : Sym2 V → unitInterval} {o : V} {B : Finset V} {a b : ℕ}
    (hπ : ∀ e, π e < 1) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (hcard : 0 < B.card)
    (hMa : I420Case1.powMomentAt π a o ≠ ⊤)
    (hMb : ∀ y ∈ B, I420Case1.powMomentAt π b y ≠ ⊤) :
    0 ≤ discR π o a b B := by
  have hc : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hcard
  have hBK := I420Case1.mixedExcl_le_prodFactor hπ 𝓔 h𝓔mono h𝓔 o a b B
  have htop : I420Case1.prodFactor π o a b B ≠ ⊤ := prodFactor_ne_top hMa hMb
  have hmom : (I420Case1.mixedExcl π o a b B).toReal ≤
      (I420Case1.prodFactor π o a b B).toReal := ENNReal.toReal_mono htop hBK
  rw [discR, div_nonneg_iff]
  left
  exact ⟨sub_nonneg.mpr hmom, le_of_lt hc⟩

end I420Case3

end PercLib.CriticalLRP
