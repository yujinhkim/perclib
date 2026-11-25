/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  Lemma I.4.12 (p. 39) and the display in the proof of Lemma I.4.11 (p. 40):

  `P_{β_c,r}(0↔x) P_{β_c,r}(y↔z) − P_{β_c,r}(0↔x ↮ y↔z)`
  `  ≤ ∑_{a,b∈Z^d} P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`                       (I.4.12)

  `|B_r| (E_{β_c,r}|K|)² − E_{β_c,r}[ |K| ∑_{y∈B_r} 1(y ∉ K) |K_y| ]`
  `  = ∑_{y∈B_r} ∑_{x,z} [ P(0↔x) P(y↔z) − P(0↔x ↮ y↔z) ]`                 (proof of I.4.11)

  `  ≤ ∑_{y∈B_r} ∇(0,y) (E_{β_c,r}|K|)²`   with   `∇(0,x) = τ ∗ τ ∗ τ (x)`   (p. 41)

**What this file does (the "five-factor diagram assembly" half).**  It sums the right-hand side of
(I.4.12) over `x` and `z` in `ℝ≥0∞`, and identifies the result with the paper's
`∇(0,y) (E|K|)²`, with every reordering and every renaming of indices isolated as its own lemma:

* `tsum_twoPointFunction_eq_origin` — `∑_x τ(a,x) = ∑_x τ(0,x)` (translation invariance
  `CountableProduct.Lattice.twoPointFunction_eq_origin` plus the reindexing `x ↦ x - a`);
* `lintegral_clusterVol_eq_tsum_twoPoint` — `∫⁻ |K_v| ∂P_β = ∑_w τ(v,w)` (Tonelli applied to
  `CountableProduct.Base.clusterVol_eq_tsum`), and `lintegral_clusterVol_eq_origin`: the expected
  cluster volume does not depend on the site.  This is where `E|K|` is *identified* with the
  τ-sum rather than assumed;
* `tsum_tsum_five_factor_mul` — the elementary factoring of constants out of the `x`, `z` sums;
* `tsum_fiveFactor_eq` — the collapse
  `∑_{a,b} ∑_{x,z} τ(0,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z) = (∑_w τ(0,w))² ∑_{a,b} τ(0,a)τ(a,b)τ(y,b)`,
  i.e. after the `x,z` sums the five factors are a *constant* `τ(0,a)τ(a,b)τ(y,b)` times the
  square of the mean cluster volume;
* `tsum_three_comm_last` — the paper's last factor `τ(y,b)` is the convolution's `τ(b,y)`: the
  endpoints do point the right way, and the flip is by symmetry of the two-point function;
* `tsum_fiveFactor_eq_nabla`, `tsum_fiveFactor_eq_nabla_paper` — the same in the `∇` normalisation
  and in the paper's factor order `∇(0,y) (E|K|)²`;
* `tsum_fiveFactor_eq_lintegral` — the second factor written as `(∫⁻ |K_0|)²`;
* `tsum_three_eq_conv` — `∇(0,y) = τ ∗ τ ∗ τ (y)` in the explicit convolution form
  `∑_a τ(a) ∑_b τ(b-a) τ(y-b)`;
* `tsum_tsum_twoPoint_eq_sq`, `sum_tsum_tsum_twoPoint_eq_card` — the first term of the display:
  `∑_{y∈B} ∑_{x,z} τ(0,x)τ(y,z) = |B| (E|K|)²`;
* `tsum_fiveFactor_swap` — `∑_{x,z} ∑_{a,b} = ∑_{a,b} ∑_{x,z}`, needed because (I.4.12) has
  `a,b` outside while the proof of I.4.11 sums `x,z` first;
* `sum_fiveFactor_eq` — the finite-`B` display `∑_{y∈B} ∑_{x,z} ∑_{a,b} (five) = (E|K|)² ∑_{y∈B} ∇(0,y)`;
* `tsum_fiveFactor_ne_top`, `toReal_tsum_fiveFactor_eq` — the finiteness premises and the
  `toReal` bridge needed before the `ℝ≥0∞` assembly can be compared with the paper's real
  numbers.  No `∞ − ∞` and no `toReal ⊤ = 0` occurs anywhere;
* `sum_twoCluster_le_of_pointwise` — the composition interface: from any pointwise bound
  `τ(0,x)τ(y,z) ≤ gap y x z + (five factors)` (for `y ∈ B`, all `x,z`), the summed comparison
  `∑_{y∈B}∑_{x,z} τ(0,x)τ(y,z) ≤ ∑_{y∈B}∑_{x,z} gap + (E|K|)² ∑_{y∈B} ∇(0,y)` follows.

**What this file does not do.**  The left-hand side of I.4.11 — the excluded expectation
`E[|K| ∑_{y∈B} 1(y ∉ K)|K_y|]` and its decomposition into `∑_{y} ∑_{x,z} P(0↔x ↮ y↔z)` — and the
pointwise gap inequality itself are separate components; this file only supplies the right-hand
side comparison.  (Note the gap event: `0↔x ↮ y↔z` is `BK/CanonicalBridge.apartSet`, strictly
smaller than `Correlation.TwoClusterGap.disjSet`, so `longRange_twoCluster_gap` alone is not the
pointwise input I.4.11 needs — swarm finding f1.)  Nothing here claims I.4.11 as a whole.

No `sorry`, no custom axioms.  Everything is `ℝ≥0∞`-valued, so no summability hypotheses are
needed and the identities hold also when `E|K| = ⊤`.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Lattice

set_option autoImplicit true
set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}

/-- **The τ-sum does not depend on the root.**  `∑_x τ(a,x) = ∑_x τ(0,x)`, by translation
invariance `τ(a,x) = τ(0, x - a)` and the reindexing `x ↦ x - a`. -/
theorem tsum_twoPointFunction_eq_origin
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (a : Fin d → ℤ) :
    (∑' x : Fin d → ℤ, twoPointFunction J hJ β a x)
      = ∑' x : Fin d → ℤ, twoPointFunction J hJ β 0 x := by
  have h1 : ∀ x : Fin d → ℤ,
      twoPointFunction J hJ β a x = twoPointFunction J hJ β 0 (x - a) := fun x =>
    twoPointFunction_eq_origin hJinv hJ β a x
  rw [tsum_congr h1]
  exact Equiv.tsum_eq (Equiv.subRight a) (fun u => twoPointFunction J hJ β 0 u)

/-- The measure of `{ω | w ∈ K_v}` is the two-point function. -/
theorem measure_cluster_mem_eq_twoPoint (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (v w : Fin d → ℤ) :
    longRangeMeasure J hJ β {ω : Config (Fin d → ℤ) | w ∈ cluster ω v}
      = twoPointFunction J hJ β v w := by
  simp only [longRangeMeasure, twoPointFunction]
  rw [show {ω : Config (Fin d → ℤ) | w ∈ cluster ω v}
        = {ω : Config (Fin d → ℤ) | Connects ω v w} from Set.ext fun ω => mem_cluster_iff]

/-- **Expected cluster volume = τ-sum** (Tonelli on `clusterVol_eq_tsum`):
`E_β |K_v| = ∑_w τ(v,w)` in `ℝ≥0∞`. -/
theorem lintegral_clusterVol_eq_tsum_twoPoint (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (v : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)
      = ∑' w : Fin d → ℤ, twoPointFunction J hJ β v w := by
  have hfun : (fun ω : Config (Fin d → ℤ) => clusterVol ω v)
      = fun ω => ∑' w : Fin d → ℤ, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    funext ω; exact clusterVol_eq_tsum ω v
  rw [hfun, lintegral_tsum]
  · refine tsum_congr fun w => ?_
    have hind : (fun ω : Config (Fin d → ℤ) =>
          (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w)
        = {ω : Config (Fin d → ℤ) | w ∈ cluster ω v}.indicator (1 : Config (Fin d → ℤ) → ℝ≥0∞) := by
      funext ω
      by_cases hw : w ∈ cluster ω v
      · rw [Set.indicator_of_mem hw,
          Set.indicator_of_mem (show ω ∈ {ω | w ∈ cluster ω v} from hw), Pi.one_apply]
      · rw [Set.indicator_of_notMem hw,
          Set.indicator_of_notMem (show ω ∉ {ω | w ∈ cluster ω v} from hw)]
    rw [hind, lintegral_indicator_one (measurableSet_cluster_mem v w),
      measure_cluster_mem_eq_twoPoint hJ β v w]
  · intro w
    exact (Measurable.indicator measurable_const (measurableSet_cluster_mem v w)).aemeasurable

/-- The expected cluster volume is the same at every site. -/
theorem lintegral_clusterVol_eq_origin
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (v : Fin d → ℤ) :
    ∫⁻ ω, clusterVol ω v ∂(longRangeMeasure J hJ β)
      = ∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β) := by
  rw [lintegral_clusterVol_eq_tsum_twoPoint hJ β v,
    tsum_twoPointFunction_eq_origin hJinv hJ β v,
    ← lintegral_clusterVol_eq_tsum_twoPoint hJ β 0]


/-! ## §2  The five factors: constants out of the `x,z` sums -/

/-- Elementary `ℝ≥0∞` fact: `∑_x ∑_z p F x q r G z = p q r ((∑_x F x)(∑_z G z))`. -/
theorem tsum_tsum_five_factor_mul (p q r : ℝ≥0∞) (F G : (Fin d → ℤ) → ℝ≥0∞) :
    (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, p * F x * q * r * G z)
      = p * q * r * ((∑' x : Fin d → ℤ, F x) * (∑' z : Fin d → ℤ, G z)) := by
  have hz : ∀ x : Fin d → ℤ,
      (∑' z : Fin d → ℤ, p * F x * q * r * G z)
        = (p * F x * q * r) * (∑' z : Fin d → ℤ, G z) :=
    fun x => ENNReal.tsum_mul_left
  simp only [hz]
  have h1 : (∑' x : Fin d → ℤ, p * F x * q * r * (∑' z : Fin d → ℤ, G z))
      = (∑' x : Fin d → ℤ, p * F x * q * r) * (∑' z : Fin d → ℤ, G z) :=
    ENNReal.tsum_mul_right
  have hx : (∑' x : Fin d → ℤ, p * F x * q * r) = p * q * r * (∑' x : Fin d → ℤ, F x) := by
    have hpt : ∀ x : Fin d → ℤ, p * F x * q * r = p * q * r * F x := fun x => by ring
    rw [tsum_congr hpt, ENNReal.tsum_mul_left]
  rw [h1, hx]
  ring

/-- **Lemma I.4.12, right-hand side after the `x` and `z` sums** (paper's factor order):
`∑_{a,b} ∑_{x,z} τ(0,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z)`
`  = (∑_w τ(0,w)) · (∑_w τ(0,w)) · ∑_{a,b} τ(0,a)τ(a,b)τ(y,b)`.

The two `x`, `z` sums are `∑_x τ(a,x) = ∑_w τ(0,w)` and `∑_z τ(b,z) = ∑_w τ(0,w)` by translation
invariance (`tsum_twoPointFunction_eq_origin`); no summability is needed because everything is
`ℝ≥0∞`-valued. -/
theorem tsum_fiveFactor_eq
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β y b) := by
  have hinner : ∀ a b : Fin d → ℤ,
      (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z)
        = twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
            * twoPointFunction J hJ β y b
            * ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
              * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)) := by
    intro a b
    rw [tsum_tsum_five_factor_mul (p := twoPointFunction J hJ β 0 a)
      (q := twoPointFunction J hJ β a b) (r := twoPointFunction J hJ β y b)
      (F := fun x => twoPointFunction J hJ β a x) (G := fun z => twoPointFunction J hJ β b z)]
    rw [tsum_twoPointFunction_eq_origin hJinv hJ β a,
      tsum_twoPointFunction_eq_origin hJinv hJ β b]
  simp only [hinner]
  have h2 : (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
          * twoPointFunction J hJ β y b
          * ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
            * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)))
      = (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
            * twoPointFunction J hJ β y b)
        * ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
          * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)) := by
    simp only [ENNReal.tsum_mul_right]
  rw [h2]
  ring

/-- **Endpoint bookkeeping**: the paper's last factor in (I.4.12) is `τ(y,b)`, the convolution
`∇(0,y) = τ * τ * τ (y)` has `τ(b,y)`.  They agree by symmetry of the two-point function. -/
theorem tsum_three_comm_last (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
          * twoPointFunction J hJ β y b)
      = ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
          * twoPointFunction J hJ β b y := by
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [twoPointFunction_comm J hJ β y b]

/-- **The five-factor diagram collapse in the paper's `∇` normalisation**:
`∑_{a,b} ∑_{x,z} τ(0,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z) = (E|K|)² · ∇(0,y)` with
`∇(0,y) = τ ∗ τ ∗ τ (y) = ∑_{a,b} τ(0,a)τ(a,b)τ(b,y)`. -/
theorem tsum_fiveFactor_eq_nabla
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β b y) := by
  rw [tsum_fiveFactor_eq hJinv hJ β y, tsum_three_comm_last hJ β y]

/-- **The second factor is the square of the expected cluster volume**: replacing the τ-sums by
`∫⁻ ω, |K_0(ω)| ∂P_β` (`lintegral_clusterVol_eq_tsum_twoPoint`). -/
theorem tsum_fiveFactor_eq_lintegral
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
        * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
        * (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β b y) := by
  rw [tsum_fiveFactor_eq_nabla hJinv hJ β y,
    lintegral_clusterVol_eq_tsum_twoPoint hJ β 0]

/-! ## §3  The mean-volume square on its own, the reordering, and the finite-`B` form -/

/-- **`∑_{x,z} P(0↔x) P(y↔z) = (E|K|)²`**, the first term of the display in the proof of
Lemma I.4.11 (with `E|K| = ∑_w τ(0,w) = ∫⁻ |K_0|`, `lintegral_clusterVol_eq_tsum_twoPoint`). -/
theorem tsum_tsum_twoPoint_eq_sq
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      = (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) := by
  have h1 : (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      = (∑' x : Fin d → ℤ, twoPointFunction J hJ β 0 x)
        * (∑' z : Fin d → ℤ, twoPointFunction J hJ β y z) := by
    have hz : ∀ x : Fin d → ℤ,
        (∑' z : Fin d → ℤ, twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
          = twoPointFunction J hJ β 0 x
            * (∑' z : Fin d → ℤ, twoPointFunction J hJ β y z) :=
      fun x => ENNReal.tsum_mul_left
    simp only [hz]
    exact ENNReal.tsum_mul_right
  rw [h1, tsum_twoPointFunction_eq_origin hJinv hJ β y]

/-- **Commutation of the four sums** `x,z` and `a,b`.  Lemma I.4.12 is stated with `a,b` outside,
the proof of Lemma I.4.11 sums `x,z` first; in `ℝ≥0∞` the two orders agree. -/
theorem tsum_fiveFactor_swap (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z := by
  calc (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∑' x : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z) := by
        refine tsum_congr fun x => ?_
        exact ENNReal.tsum_comm
    _ = (∑' a : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z) := ENNReal.tsum_comm
    _ = (∑' a : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' z : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z) := by
        refine tsum_congr fun a => tsum_congr fun x => ?_
        exact ENNReal.tsum_comm
    _ = (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z) := by
        refine tsum_congr fun a => ?_
        exact ENNReal.tsum_comm

/-- **The display in the proof of Lemma I.4.11 after applying Lemma I.4.12**, in `ℝ≥0∞`:
for a finite `B`,

`∑_{y∈B} ∑_{x,z} ∑_{a,b} τ(0,a)τ(a,x)τ(a,b)τ(y,b)τ(b,z) = (E|K|)² ∑_{y∈B} ∇(0,y)`.

This is the right-hand side comparison; the left-hand side of I.4.11 (the excluded expectation)
and the subtraction are not part of this statement. -/
theorem sum_fiveFactor_eq
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) :
    (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
        * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
        * ∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β b y := by
  have hpt : ∀ y : Fin d → ℤ,
      (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z)
        = (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
            * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
            * (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
                twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
                  * twoPointFunction J hJ β b y) := by
    intro y
    rw [tsum_fiveFactor_swap hJ β y, tsum_fiveFactor_eq_lintegral hJinv hJ β y]
  simp only [hpt]
  rw [← Finset.mul_sum]

/-- **`|B| (E|K|)² = ∑_{y∈B} ∑_{x,z} P(0↔x) P(y↔z)`**, the first term of the display in the proof
of Lemma I.4.11, with `B` a finite set of sites. -/
theorem sum_tsum_tsum_twoPoint_eq_card
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) :
    (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      = (B.card : ℝ≥0∞)
        * ((∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
          * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)) := by
  simp only [tsum_tsum_twoPoint_eq_sq hJinv hJ β]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §4  The convolution form, the paper's factor order, and the real-quotient bridge -/

/-- **`∇(0,y) = τ ∗ τ ∗ τ (y)`**: with `τ(v) := τ(0,v)` the double sum of (I.4.12) is the triple
convolution `∑_a τ(a) ∑_b τ(b-a) τ(y-b)`.  This is the only "convolution identity" used; it is a
two-step rewriting by translation invariance, and `PercLib` has no separate `∇` object. -/
theorem tsum_three_eq_conv
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
          * twoPointFunction J hJ β b y)
      = ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β 0 (b - a)
          * twoPointFunction J hJ β 0 (y - b) := by
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [twoPointFunction_eq_origin hJinv hJ β a b, twoPointFunction_eq_origin hJinv hJ β b y]

/-- The collapse in the paper's factor order `∇(0,y) (E_{\beta_c,r}|K|)^2`. -/
theorem tsum_fiveFactor_eq_nabla_paper
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
            * twoPointFunction J hJ β b y)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) := by
  rw [tsum_fiveFactor_eq_nabla hJinv hJ β y]
  ring

/-- **Finiteness of the assembled diagram under the actual finite-moment premises.**  The two
premises are exactly "the expected cluster volume is finite" and "the triangle diagram at `y` is
finite"; they are what a real-valued (`toReal`) quotient of the `ℝ≥0∞` assembly must supply. -/
theorem tsum_fiveFactor_ne_top
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ)
    (hS : (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) ≠ ⊤)
    (hD : (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
          * twoPointFunction J hJ β b y) ≠ ⊤) :
    (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z) ≠ ⊤ := by
  rw [tsum_fiveFactor_eq_nabla_paper hJinv hJ β y]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hD hS) hS

/-- **Real-quotient bridge.**  `ENNReal.toReal` of the assembled diagram is the product of the real
values of the three factors.  This identity is unconditional in `ℝ≥0∞`; it only becomes a
comparison of the paper's real numbers together with `tsum_fiveFactor_ne_top`, which supplies the
finiteness premises.  (No `toReal ⊤ = 0` step is used: `ENNReal.toReal_mul` is an
`ℝ≥0∞` identity.) -/
theorem toReal_tsum_fiveFactor_eq
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    ENNReal.toReal
        (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
            * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
            * twoPointFunction J hJ β b z)
      = (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
              * twoPointFunction J hJ β b y).toReal
          * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w).toReal
          * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w).toReal := by
  rw [tsum_fiveFactor_eq_nabla_paper hJinv hJ β y, ENNReal.toReal_mul, ENNReal.toReal_mul]


/-- **The form used downstream**: with `x,z` outermost (as in the proof of Lemma I.4.11), the
five-factor right-hand side of (I.4.12) is `∇(0,y) (E|K|)²`. -/
theorem tsum_xz_fiveFactor_eq_nabla_paper
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (y : Fin d → ℤ) :
    (∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
          * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
          * twoPointFunction J hJ β b z)
      = (∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
          twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
            * twoPointFunction J hJ β b y)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w)
        * (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) := by
  rw [tsum_fiveFactor_swap hJ β y, tsum_fiveFactor_eq_nabla_paper hJinv hJ β y]

/-! ## §5  Composition interface: from the pointwise (I.4.12) bound to the summed comparison -/

/-- **Summed comparison.**  If the additive form of Lemma I.4.12 holds for every `y ∈ B` and all
`x, z` (with `gap y x z` the probability of the corresponding two-cluster gap event), then summing
over `x, z` and over `y ∈ B` and applying the five-factor collapse gives

`∑_{y∈B} ∑_{x,z} τ(0,x)τ(y,z) ≤ ∑_{y∈B} ∑_{x,z} gap(y,x,z) + (E|K|)² ∑_{y∈B} ∇(0,y)`.

Nothing is assumed about `gap` beyond the pointwise inequality, so this composes with whatever
pointwise bound on `τ(0,x)τ(y,z)` is eventually available; the gap event itself must be the paper's
`0↔x ↮ y↔z` (the repository's `apartSet`, see `BK/CanonicalBridge.lean`), *not* the disjoint
occurrence `Correlation.TwoClusterGap.disjSet`, which is a strictly larger event (swarm finding f1).
Only nonnegative quantities are added: no subtraction and no `∞ − ∞`. -/
theorem sum_twoCluster_le_of_pointwise
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ))
    (gap : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞)
    (hpoint : ∀ y ∈ B, ∀ x z : Fin d → ℤ,
      twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z
        ≤ gap y x z + ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
              * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
              * twoPointFunction J hJ β b z) :
    (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      ≤ (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, gap y x z)
        + (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
              twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
                * twoPointFunction J hJ β b y) := by
  calc (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
        twoPointFunction J hJ β 0 x * twoPointFunction J hJ β y z)
      ≤ (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ,
          (gap y x z + ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
              * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
              * twoPointFunction J hJ β b z)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun z => hpoint y hy x z
    _ = (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, gap y x z)
        + (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' a : Fin d → ℤ,
            ∑' b : Fin d → ℤ,
            twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a x
              * twoPointFunction J hJ β a b * twoPointFunction J hJ β y b
              * twoPointFunction J hJ β b z) := by
        simp only [ENNReal.tsum_add, Finset.sum_add_distrib]
    _ = (∑ y ∈ B, ∑' x : Fin d → ℤ, ∑' z : Fin d → ℤ, gap y x z)
        + (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β))
          * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
              twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b
                * twoPointFunction J hJ β b y) := by
        rw [sum_fiveFactor_eq hJinv hJ β B]
/-! ### Axiom audit -/


end PercLib.CriticalLRP
