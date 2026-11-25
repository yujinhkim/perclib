/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

/-
# High-temperature finiteness of the susceptibility for the power-law kernel on `ℤ^d`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.3 and §I.1.2: the stationary lattice model in which
each pair `{x,y}` of `ℤ^d` is open independently with probability
`1 − exp(−β J(x,y))`, where `J(x,y) = 1(x ≠ y) ‖x − y‖^{-d-α}`.

This file proves the *high-temperature end* of the susceptibility statement: for every
`d ≥ 1` and `s > d`, the power-law profile `‖z‖_∞^{-s}` has finite total mass
`M = ∑_z ‖z‖_∞^{-s}` (`summable_linfNorm_rpow`, `PercLib.CriticalLRP.LatticeGeometry`), and
consequently every off-diagonal row of the pair intensity sums to at most `M`, so the
row-sum (first-moment / branching) criterion gives

* `χ(x) ≤ (1 − β M)⁻¹ < ∞` whenever `β M < 1`,
* the expected cluster volume is finite at the same parameters,
* almost surely no cluster is infinite at the same parameters,
* the critical intensity is strictly positive.

Nothing here is a sharpness statement at `β_c`: the subcritical region obtained is the
explicit interval `β < 1/M`, not `β < β_c`. No moment bound, translation-invariant
second moment, or sharpness differential inequality is used, and the conclusion is a
genuine finiteness statement, so it is not exposed to the binary-tree obstruction
(`θ = 0` with infinite mean).

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/

public import PercLib.CriticalLRP.LatticeGeometry
public import PercLib.Models.TranslationInvariant
public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.CountableProduct.FiniteFirstMoment
public import PercLib.Percolation.Bond.IntensityScaling

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical

namespace PercLib.CriticalLRP.PowerLawHighTemp

open PercLib.CriticalLRP.FiniteVolume
open PercLib.Percolation.Bond

variable {d : ℕ}

/-! ## The mass of the power-law profile -/

/-- The power-law profile `‖z‖_∞^{-s}` is nonnegative. -/
theorem powerProfile_nonneg {s : ℝ} (z : Fin d → ℤ) : 0 ≤ (linfNorm z : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The power-law profile is even, so it defines a symmetric pair intensity. -/
theorem powerProfile_even (s : ℝ) :
    ∀ x : Fin d → ℤ,
      (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (-x)
        = (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) x := by
  intro x
  show (linfNorm (-x) : ℝ) ^ (-s) = (linfNorm x : ℝ) ^ (-s)
  rw [linfNorm_neg]

/-- **Summability of the power-law profile on `ℤ^d`**, for `s > d`
(`summable_linfNorm_rpow` of `LatticeGeometry`).  With `s = d + α` this is
`∑_{z ≠ 0} ‖z‖_∞^{-d-α} < ∞` for every `α > 0`, i.e. finiteness of the expected degree. -/
theorem summable_powerProfile (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    Summable (fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-s)) :=
  summable_linfNorm_rpow hd hs

/-- The total mass `∑_z ‖z‖_∞^{-s}` is nonnegative. -/
theorem powerMass_nonneg {s : ℝ} :
    0 ≤ ∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s) :=
  tsum_nonneg fun z => powerProfile_nonneg z

/-- The mass of the power-law profile as an `ℝ≥0∞`, in the form in which it appears in
the row-sum bound: `ENNReal.ofReal M = ↑M.toNNReal`. -/
theorem ofReal_powerMass_eq_coe {s : ℝ} :
    ENNReal.ofReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s))
      = ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ powerMass_nonneg]

/-- **The off-diagonal total mass of the power-law profile as an `ℝ≥0∞` sum**: the
sum of the `ℝ≥0` profile over `ℤ^d` is the mass `M`.  This is the `hk` hypothesis of
`Models.rowSum_le_tsum_of_translationInvariant`. -/
theorem tsum_toNNReal_powerProfile_eq (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    (∑' z : Fin d → ℤ, ((Real.toNNReal ((linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞))
      = ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) := by
  have hterm : ∀ z : Fin d → ℤ,
      ((Real.toNNReal ((linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal ((linfNorm z : ℝ) ^ (-s)) := by
    intro z
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (powerProfile_nonneg z)]
  refine Eq.trans (tsum_congr hterm) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => powerProfile_nonneg z)
    (summable_powerProfile hd hs)]
  exact ofReal_powerMass_eq_coe

/-! ## The real-valued power-law kernel of the paper

`CutoffDominated` writes the uncut kernel of Definition I.1.3 as
`kernelJ (fun y => K ↑(linfNorm y)) (profile_even K)`; with `K t = t^{-s}` this is
`kernelJ (fun y => (↑(linfNorm y) : ℝ)^{-s})`.  The two statements below record its
value on a pair and its nonnegativity. -/

/-- The power-law kernel `J(x,y) = ‖x − y‖_∞^{-s}` is nonnegative. -/
theorem power_kernelJ_nonneg {s : ℝ} (e : Sym2 (Fin d → ℤ)) :
    0 ≤ PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s) e := by
  induction e using Sym2.ind with
  | _ a b => exact powerProfile_nonneg (b - a)

/-- The power-law kernel of Definition I.1.3: `J(x,y) = ‖x − y‖_∞^{-s}`, with `s = d + α`.
This is the uncut kernel `kernelJ` at the profile `K t = t^{-s}`. -/
theorem power_kernelJ_mk {s : ℝ} (x y : Fin d → ℤ) :
    PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s) s(x, y)
      = (latticeDist x y) ^ (-s) := by
  show (linfNorm (y - x) : ℝ) ^ (-s) = (latticeDist x y) ^ (-s)
  rw [latticeDist, show x - y = -(y - x) by abel, linfNorm_neg]

/-! ## The row-sum bound and finite susceptibility -/

/-- **A row-sum bound from a translation-invariant displacement profile.**  This is the
same argument as `Models.rowSum_le_tsum_of_translationInvariant`, stated for the
unguarded sum (the diagonal term is bounded by itself), which avoids any interaction
between the `if w = v` decidability instance and the ambient one. -/
theorem rowSum_le_tsum_of_profile {G : Type*} [AddGroup G] (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y : G, J s(x, y) = k (y - x)) (v : G) :
    (∑' w : G, (J s(v, w) : ℝ≥0∞)) ≤ ∑' z : G, (k z : ℝ≥0∞) := by
  rw [← (Equiv.addRight v).tsum_eq]
  refine ENNReal.tsum_le_tsum fun z => ?_
  simp only [Equiv.coe_addRight]
  rw [hJ v (z + v), add_sub_cancel_right]

/-- **The row of the power-law pair intensity is at most the mass `M`.**  This is the
hypothesis of the P-5/P-6 row-sum theorems, discharged here from the lattice summability
of the profile via translation invariance. -/
theorem power_rowSum_le (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    (v : Fin d → ℤ) :
    (∑' w : Fin d → ℤ, (J s(v, w) : ℝ≥0∞))
      ≤ ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) :=
  (rowSum_le_tsum_of_profile J
      (fun z : Fin d → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-s))) hJ v).trans
    (le_of_eq (tsum_toNNReal_powerProfile_eq hd hs))

/-- **The explicit high-temperature susceptibility bound.** For the power-law
profile on `ℤ^d` with `s > d`, this is `χ(x) ≤ (1 - β M)⁻¹` for every vertex,
where `M` is the total profile mass and `β M < 1`. -/
theorem power_chi_intensity_le (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile J β) x ≤
      (1 - (β : ℝ≥0∞) *
        ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞))⁻¹ := by
  refine chi_intensity_le J _ (fun v => ?_) β hβ x
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs with h <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- **Finite susceptibility of the power-law intensity in the high-temperature regime.**
If the pair intensity has the power-law profile `‖x − y‖_∞^{-s}` on `ℤ^d` with `s > d`,
then for `β M < 1`, where `M = ∑_z ‖z‖_∞^{-s}` is the mass of the profile, the expected
cluster volume at every vertex is finite. -/
theorem power_chi_intensity_lt_top (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile J β) x < ⊤ := by
  refine chi_intensity_lt_top J _ (fun v => ?_) β hβ x
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs with h <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- The intensity profile `1 − exp(−β J e)` of a `ℝ≥0`-valued `J` is the Bernoulli edge
function of the same `J` read as a real-valued kernel. -/
theorem intensityProfile_eq_bernoulliEdgeProb {V : Type*} (J : Sym2 V → ℝ≥0) (β : ℝ≥0) :
    intensityProfile J β
      = PercLib.CriticalLRP.bernoulliEdgeProb (fun e => (J e : ℝ))
          (fun e => (J e).coe_nonneg) β := by
  refine funext fun e => Subtype.ext ?_
  simp [intensityProfile, PercLib.CriticalLRP.bernoulliEdgeProb]

/-- **Finite susceptibility for the paper's power-law kernel**, in the `kernelJ`
presentation used by `CutoffDominated`. -/
theorem power_kernelJ_chi_lt_top (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (PercLib.CriticalLRP.bernoulliEdgeProb
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
        power_kernelJ_nonneg β) x < ⊤ := by
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel
    (fun z : Fin d → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-s)))
    (fun z => by
      show Real.toNNReal ((linfNorm (-z) : ℝ) ^ (-s))
        = Real.toNNReal ((linfNorm z : ℝ) ^ (-s))
      rw [linfNorm_neg])
  have hchi := power_chi_intensity_lt_top hd hs hJ hβ x
  rw [intensityProfile_eq_bernoulliEdgeProb] at hchi
  have hq : PercLib.CriticalLRP.bernoulliEdgeProb (fun e => (J e : ℝ))
        (fun e => (J e).coe_nonneg) β
      = PercLib.CriticalLRP.bernoulliEdgeProb
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
          power_kernelJ_nonneg β := by
    refine funext fun e => Subtype.ext ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [PercLib.CriticalLRP.bernoulliEdgeProb_coe,
        PercLib.CriticalLRP.bernoulliEdgeProb_coe, hJ a b,
        Real.coe_toNNReal _ (powerProfile_nonneg (b - a))]
      rfl
  rwa [hq] at hchi

/-! ## Finiteness of the expected cluster volume and absence of percolation -/

/-- **The expected cluster volume of the power-law model is finite at small `β`**, in the
`clusterVol`/`longRangeMeasure` form used by `CutoffDominated` (there as the premise
`hfin` "the uncut mean at the reduced parameter is finite"). -/
theorem power_kernelJ_lintegral_clusterVol_ne_top (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
          power_kernelJ_nonneg β)) ≠ ⊤ :=
  (power_kernelJ_chi_lt_top hd hs hβ x).ne

/-- **No percolation at small `β`**: for `β` with `β M < 1` the probability that an
infinite cluster exists is zero.  This is the percolation-probability part of
subcriticality, *additional* to the finiteness of the mean above (neither is derived from
the other here). -/
theorem power_kernelJ_infiniteClusterProb_eq_zero (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1) :
    PercLib.CriticalLRP.infiniteClusterProb
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
        power_kernelJ_nonneg β = 0 := by
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel
    (fun z : Fin d → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-s)))
    (fun z => by
      show Real.toNNReal ((linfNorm (-z) : ℝ) ^ (-s))
        = Real.toNNReal ((linfNorm z : ℝ) ^ (-s))
      rw [linfNorm_neg])
  have hzero : PercLib.Percolation.Bond.law (intensityProfile J β)
      {ω | ∃ x, (PercLib.Percolation.Bond.cluster ω x).Infinite} = 0 := by
    refine law_exists_infinite_intensity_eq_zero J _ (fun v => ?_) β hβ
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs with h <;> simp).trans
      (power_rowSum_le hd hs hJ v)
  rw [intensityProfile_eq_bernoulliEdgeProb] at hzero
  have hq : PercLib.CriticalLRP.bernoulliEdgeProb (fun e => (J e : ℝ))
        (fun e => (J e).coe_nonneg) β
      = PercLib.CriticalLRP.bernoulliEdgeProb
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
          power_kernelJ_nonneg β := by
    refine funext fun e => Subtype.ext ?_
    induction e using Sym2.ind with
    | _ a b =>
      rw [PercLib.CriticalLRP.bernoulliEdgeProb_coe,
        PercLib.CriticalLRP.bernoulliEdgeProb_coe, hJ a b,
        Real.coe_toNNReal _ (powerProfile_nonneg (b - a))]
      rfl
  show PercLib.CriticalLRP.longRangeMeasure
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
      power_kernelJ_nonneg β (PercLib.CriticalLRP.existsInfiniteClusterEvent (Fin d → ℤ)) = 0
  unfold PercLib.CriticalLRP.longRangeMeasure PercLib.CriticalLRP.edgeMeasure
  rw [← hq]
  refine measure_mono_null (fun ω hω => ?_) hzero
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, (PercLib.CriticalLRP.inInfiniteCluster_iff_infinite ω v).mp hv⟩

/-! ## Exact kernel conversion to the paper-literal `lrKernel` -/

/-- Mathlib's supremum norm on `Fin d → ℤ` agrees with the campaign's natural-valued
`linfNorm` after coercion to `ℝ`.  The second inequality is deliberately obtained by
rounding to `ℕ`, rather than by introducing a separate norm or a normalization factor. -/
theorem coe_norm_eq_linfNorm {d : ℕ} (z : Fin d → ℤ) :
    (‖z‖ : ℝ) = (linfNorm z : ℝ) := by
  have hzi : ∀ i : Fin d, ‖z i‖ = ((z i).natAbs : ℝ) := by
    intro i
    rw [← NNReal.coe_natCast (n := (z i).natAbs), NNReal.natCast_natAbs]
    rfl
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ (linfNorm z : ℝ))]
    intro i
    rw [hzi i]
    exact_mod_cast linfNorm_le_iff.mp le_rfl i
  · have key : (Finset.univ.sup fun i : Fin d => (z i).natAbs) ≤ ⌊‖z‖⌋₊ := by
      rw [Finset.sup_le_iff]
      intro i _
      exact Nat.le_floor ((hzi i).ge.trans (norm_le_pi_norm z i))
    rw [linfNorm]
    calc ((Finset.univ.sup fun i : Fin d => (z i).natAbs : ℕ) : ℝ)
        ≤ ((⌊‖z‖⌋₊ : ℕ) : ℝ) := by exact_mod_cast key
      _ ≤ ‖z‖ := Nat.floor_le (norm_nonneg z)

/-- Equality on arbitrary unordered pairs of the paper's `lrKernel` and the `kernelJ`
presentation used by the high-temperature bounds.  No positivity hypothesis is needed:
at the diagonal both sides are `0^{-d-α}`, which `power_kernelJ_mk` also handles. -/
theorem lrKernel_mk_eq_power_kernelJ_mk (d : ℕ) {α : ℝ} (x y : Fin d → ℤ) :
    PercLib.CriticalLRP.lrKernel d α s(x, y)
      = PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
          (powerProfile_even ((d : ℝ) + α)) s(x, y) := by
  rw [power_kernelJ_mk]
  simp only [PercLib.CriticalLRP.lrKernel, Sym2.lift_mk, latticeDist]
  rw [coe_norm_eq_linfNorm (x - y)]

/-- The two kernel presentations are equal, including the proof-dependent nonnegativity
arguments in their downstream laws. -/
theorem lrKernel_eq_power_kernelJ (d : ℕ) {α : ℝ} :
    PercLib.CriticalLRP.lrKernel d α
      = PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
          (powerProfile_even ((d : ℝ) + α)) := by
  funext e
  induction e using Sym2.ind with
  | _ x y => exact lrKernel_mk_eq_power_kernelJ_mk d x y

/-- **High-temperature non-percolation for the paper's actual `lrKernel`.**  This is the
same explicit condition `β M < 1` as above, now with no incidental `kernelJ` mismatch. -/
theorem lrKernel_infiniteClusterProb_eq_zero {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) :
    PercLib.CriticalLRP.infiniteClusterProb (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α) β = 0 := by
  simp only [lrKernel_eq_power_kernelJ]
  exact power_kernelJ_infiniteClusterProb_eq_zero hd (by linarith) hβ

/-- The finite first moment at every lattice vertex in the same high-temperature region. -/
theorem lrKernel_lintegral_clusterVol_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ∂
      (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ := by
  simp only [lrKernel_eq_power_kernelJ]
  exact power_kernelJ_lintegral_clusterVol_ne_top hd (by linarith) hβ x

/-- The literal critical parameter is bounded below at every high-temperature parameter,
once the critical set is known to be nonempty.  Supercriticality is separately required;
none of these high-temperature results supplies it. -/
theorem lrKernel_le_criticalBeta_of_nonempty {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hne : (PercLib.CriticalLRP.criticalBetaSet (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α)).Nonempty) :
    β ≤ PercLib.CriticalLRP.criticalBeta (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α) :=
  PercLib.CriticalLRP.le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty hne
    (lrKernel_infiniteClusterProb_eq_zero hd hα hβ)

/-! ## Literal `criticalBeta` lower bounds -/

/-- The explicit high-temperature region gives a lower bound for the paper's literal
critical parameter, provided it is proved to percolate at some finite parameter.
Nonemptiness is not proved here; the `globalCriticalIntensity` and `rootCriticalIntensity`
results below use a different interface and are not substitutes for this missing input. -/
theorem power_kernelJ_le_criticalBeta_of_nonempty {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (hne : (criticalBetaSet
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
      power_kernelJ_nonneg).Nonempty) :
    β ≤ criticalBeta
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
      power_kernelJ_nonneg :=
  le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty hne
    (power_kernelJ_infiniteClusterProb_eq_zero hd hs hβ)

/-- A positive lower bound for the literal critical parameter of the power-law model at
`β₀=(M+1)⁻¹`, conditional on a finite-parameter percolation witness.  The latter remains
an independent obligation: for this `NNReal`-valued infimum, nonemptiness cannot be inferred
from finite first moments alone (the empty set also has infimum zero in this convention). -/
theorem power_kernelJ_criticalBeta_pos_of_nonempty {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s)
    (hne : (criticalBetaSet
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
      power_kernelJ_nonneg).Nonempty) :
    0 < criticalBeta
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
      power_kernelJ_nonneg := by
  let M : ℝ≥0 := Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s))
  have hβ : (((M + 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * (M : ℝ≥0∞) < 1 := by
    rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe,
      NNReal.coe_one, NNReal.coe_mul]
    have hm : (0 : ℝ) ≤ M := M.coe_nonneg
    rcases eq_or_lt_of_le hm with h0 | hpos
    · simp [← h0]
    · have hstep : (((M + 1)⁻¹ : ℝ≥0) : ℝ) * (M : ℝ) < 1 := by
        rw [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one]
        rw [inv_mul_eq_div, div_lt_one (by positivity)]
        linarith
      exact hstep
  exact lt_of_lt_of_le (inv_pos.mpr (by positivity))
    (power_kernelJ_le_criticalBeta_of_nonempty hd hs hβ hne)

/-- Positivity of the literal `criticalBeta` for `lrKernel` at `s = d + α`, conditional on
an almost-sure percolation witness.  That witness remains an explicit unproved input. -/
theorem lrKernel_criticalBeta_pos_of_nonempty {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α)
    (hne : (PercLib.CriticalLRP.criticalBetaSet (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α)).Nonempty) :
    0 < PercLib.CriticalLRP.criticalBeta (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α) := by
  have hne' : ∀ (hJ : ∀ e, 0 ≤ (PercLib.CriticalLRP.TreeExpansion.kernelJ
      (fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
      (powerProfile_even ((d : ℝ) + α))) e),
      (criticalBetaSet _ hJ).Nonempty := by
    rw [← lrKernel_eq_power_kernelJ (d := d) (α := α)]
    exact fun _ => hne
  have hne := hne' power_kernelJ_nonneg
  have hp := power_kernelJ_criticalBeta_pos_of_nonempty hd (by linarith : (d : ℝ) < (d : ℝ) + α) hne
  simpa only [lrKernel_eq_power_kernelJ] using hp

/-! ## The critical intensity is strictly positive -/

/-- **The critical intensity of the power-law model on `ℤ^d` is positive.**  The mass
`M = ∑_z ‖z‖_∞^{-s}` bounds every off-diagonal row, so no parameter below `M⁻¹` can
produce an infinite cluster with positive probability. -/
theorem power_globalCriticalIntensity_pos (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s))) :
    0 < globalCriticalIntensity J := by
  refine lt_of_lt_of_le ?_ (inv_le_globalCriticalIntensity J (Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s))) (fun v => ?_))
  · rw [ENNReal.inv_pos]
    exact ENNReal.coe_ne_top
  · exact (ENNReal.tsum_le_tsum fun w => by split_ifs with h <;> simp).trans
      (power_rowSum_le hd hs hJ v)

/-- **The root threshold of the power-law model is positive.** -/
theorem power_rootCriticalIntensity_pos (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    (x : Fin d → ℤ) :
    0 < rootCriticalIntensity J x := by
  refine lt_of_lt_of_le ?_ (inv_le_rootCriticalIntensity J (Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s))) (fun v => ?_) x)
  · rw [ENNReal.inv_pos]
    exact ENNReal.coe_ne_top
  · exact (ENNReal.tsum_le_tsum fun w => by split_ifs with h <;> simp).trans
      (power_rowSum_le hd hs hJ v)

/-! ## A positive interval of parameters with finite susceptibility -/

/-- **There is a positive interval of parameters with finite susceptibility.**  Taking
`β₀ = (M + 1)⁻¹`, every `β < β₀` satisfies `β M < 1`, so the expected cluster volume of
the power-law model at every vertex is finite.  This exhibits the high-temperature region
as a genuine nonempty interval, rather than a single point. -/
theorem exists_beta_interval_power_kernelJ_chi_lt_top (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s) (x : Fin d → ℤ) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧
      ∀ β : ℝ≥0, β < β₀ →
        chi (PercLib.CriticalLRP.bernoulliEdgeProb
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) (powerProfile_even s))
          power_kernelJ_nonneg β) x < ⊤ := by
  refine ⟨((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) + 1)⁻¹,
    ?_, fun β hβ => ?_⟩
  · exact inv_pos.mpr (by positivity)
  · refine power_kernelJ_chi_lt_top hd hs ?_ x
    set m : ℝ≥0 := Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) with hm
    rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, NNReal.coe_one,
      NNReal.coe_mul]
    have hβr : (β : ℝ) < ((m : ℝ) + 1)⁻¹ := by
      have h' : (β : ℝ) < (((m + 1)⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.mpr hβ
      rwa [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one] at h'
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := m.coe_nonneg
    rcases eq_or_lt_of_le hmnn with h0 | hpos
    · rw [← h0, mul_zero]; norm_num
    · have hstep : (β : ℝ) * (m : ℝ) < ((m : ℝ) + 1)⁻¹ * (m : ℝ) :=
        mul_lt_mul_of_pos_right hβr hpos
      have hlt : ((m : ℝ) + 1)⁻¹ * (m : ℝ) < 1 := by
        rw [inv_mul_eq_div, div_lt_one (by linarith)]
        linarith
      linarith

/-! ## Glue for the `kernelJ` presentation of `CutoffDominated`

`CutoffDominated` writes the uncut kernel of a profile `K` as
`kernelJ (fun y => K ↑(linfNorm y)) (profile_even K)`, while the results above use the
same function with the evenness proof `powerProfile_even`.  The two differ only in a proof
term, so they agree; the lemmas below record that, plus the corresponding facts for the
law.  They are what an instantiation of `CutoffDominated` needs. -/

/-- The `kernelJ` construction depends on its evenness hypothesis only through a proof, so
two evenness proofs give the same kernel. -/
theorem kernelJ_even_irrel {V : Type*} [AddCommGroup V] (J : V → ℝ)
    (h1 h2 : ∀ x : V, J (-x) = J x) :
    PercLib.CriticalLRP.TreeExpansion.kernelJ J h1
      = PercLib.CriticalLRP.TreeExpansion.kernelJ J h2 := by
  unfold PercLib.CriticalLRP.TreeExpansion.kernelJ
  congr 1

/-- The Bernoulli edge probabilities of a kernel depend on the nonnegativity proof only
through a proof. -/
theorem bernoulliEdgeProb_proof_irrel {V : Type*} (J : Sym2 V → ℝ)
    (h1 h2 : ∀ e, 0 ≤ J e) (β : ℝ≥0) :
    PercLib.CriticalLRP.bernoulliEdgeProb J h1 β
      = PercLib.CriticalLRP.bernoulliEdgeProb J h2 β := by
  funext e
  rfl

/-- The long-range law depends on the nonnegativity proof of the kernel only through a
proof. -/
theorem longRangeMeasure_proof_irrel {V : Type*} [Countable V] (J : Sym2 V → ℝ)
    (h1 h2 : ∀ e, 0 ≤ J e) (β : ℝ≥0) :
    PercLib.CriticalLRP.longRangeMeasure J h1 β
      = PercLib.CriticalLRP.longRangeMeasure J h2 β := by
  show PercLib.CriticalLRP.edgeMeasure (PercLib.CriticalLRP.bernoulliEdgeProb J h1 β)
    = PercLib.CriticalLRP.edgeMeasure (PercLib.CriticalLRP.bernoulliEdgeProb J h2 β)
  rw [bernoulliEdgeProb_proof_irrel J h1 h2 β]

/-- The long-range law of equal kernels is equal. -/
theorem longRangeMeasure_congr {V : Type*} [Countable V] {J1 J2 : Sym2 V → ℝ}
    (h : J1 = J2) (h1 : ∀ e, 0 ≤ J1 e) (h2 : ∀ e, 0 ≤ J2 e) (β : ℝ≥0) :
    PercLib.CriticalLRP.longRangeMeasure J1 h1 β
      = PercLib.CriticalLRP.longRangeMeasure J2 h2 β := by
  subst h
  exact longRangeMeasure_proof_irrel _ h1 h2 β

/-- The radial profile `t ↦ t^{-s}` of the power law is antitone on the positive reals. -/
theorem powerProfile_antitone {s : ℝ} (hs : 0 < s) :
    AntitoneOn (fun t : ℝ => t ^ (-s)) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- The radial profile `t ↦ t^{-s}` is nonnegative on the positive reals. -/
theorem powerProfile_nonnegPos {s : ℝ} : ∀ t : ℝ, 0 < t → 0 ≤ t ^ (-s) :=
  fun _ ht => Real.rpow_nonneg (le_of_lt ht) _

/-- The radial profile `t ↦ t^{-s}` vanishes at `0` for `s > 0`. -/
theorem powerProfile_zero {s : ℝ} (hs : 0 < s) : (0 : ℝ) ^ (-s) = 0 :=
  Real.zero_rpow (by linarith)

/-- **Unconditional finiteness of the first moment of the uncut power-law model in the
`CutoffDominated` shape**: the kernel there is `kernelJ (fun y => K ↑(linfNorm y))`
with `K t = t^{-s}`, and the parameter is any `γ` with `γ M < 1`.  This is exactly the
`hfin` premise of `CutoffDominated.lintegral_clusterVol_cutoff_ne_top` at a small reduced
parameter. -/
theorem power_uncutFirstMoment_ne_top (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => (↑(linfNorm y) : ℝ) ^ (-s))
            (PercLib.CriticalLRP.CutoffLimit.profile_even (fun t : ℝ => t ^ (-s))))
          (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg
            powerProfile_nonnegPos (powerProfile_zero (by linarith : (0 : ℝ) < s)) d)
          γ)) ≠ ⊤ := by
  rw [longRangeMeasure_congr (kernelJ_even_irrel _ _ _) _ _ γ]
  exact power_kernelJ_lintegral_clusterVol_ne_top hd hs hγ o

/-! ## Monotone comparison with any smaller pair intensity

The truncated kernel `J_r` of Definition I.1.5 satisfies `J_r ≤ J` pointwise, so the
susceptibility of every model with a smaller pair intensity is finite whenever the
power-law model's is.  This is the interface through which the cut-off model `P_{β,r}`
inherits the bound (instantiate `Jr` with the `ℝ≥0`-valued cut-off kernel and `hJr` with
`CutoffDominated.cutoffSymKernel_le_scaled`, or with `cutoffProfile_le` directly). -/

theorem chi_lt_top_of_le_powerLaw (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-s)))
    {Jr : Sym2 (Fin d → ℤ) → ℝ≥0} (hJr : Jr ≤ J)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile Jr β) x < ⊤ :=
  lt_of_le_of_lt (PercLib.Percolation.Bond.chi_le_of_le hJr β x)
    (power_chi_intensity_lt_top hd hs hJ hβ x)

/-! ## Axiom audit -/



/-! ## The paper's own normalisation `J(r) = r^{-d-α}` -/

/-- The `kernelJ` construction is congruent in its kernel. -/
theorem kernelJ_congr {V : Type*} [AddCommGroup V] {J1 J2 : V → ℝ} (h : J1 = J2)
    (h1 : ∀ x : V, J1 (-x) = J1 x) (h2 : ∀ x : V, J2 (-x) = J2 x) :
    PercLib.CriticalLRP.TreeExpansion.kernelJ J1 h1
      = PercLib.CriticalLRP.TreeExpansion.kernelJ J2 h2 := by
  subst h
  exact kernelJ_even_irrel _ _ _

/-- The model profile `J(r) = r^{-d-α}` of Definition I.1.3 satisfies all the side
conditions required by the uncut kernel of `CutoffDominated`. -/
theorem modelProfile_side_conditions {d : ℕ} {α : ℝ} (hα : 0 < α) :
    (∀ t : ℝ, 0 < t → 0 ≤ modelProfile d α t) ∧ modelProfile d α 0 = 0 := by
  refine ⟨fun t ht => Real.rpow_nonneg (le_of_lt ht) _, ?_⟩
  unfold modelProfile
  rw [Real.zero_rpow]
  linarith [Nat.cast_nonneg (α := ℝ) d]

/-- **Finiteness of the first moment of the uncut model with the paper's kernel
`J(x,y) = ‖x − y‖_∞^{-d-α}`**, in the exact `kernelJ`/`longRangeMeasure` shape of
`CutoffDominated`, at every parameter `γ` with `γ M < 1`. -/
theorem modelProfile_uncutFirstMoment_ne_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) :
        ℝ≥0∞) < 1)
    (o : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
            (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) (modelProfile d α)))
          (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg
            (modelProfile_side_conditions hα).1 (modelProfile_side_conditions hα).2 d)
          γ)) ≠ ⊤ := by
  have hfun : PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
        (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) (modelProfile d α))
      = PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α)))
          (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d)
            (fun t : ℝ => t ^ (-((d : ℝ) + α)))) := by
    refine kernelJ_congr (funext fun y => ?_) _ _
    show (↑(linfNorm y) : ℝ) ^ (-(d : ℝ) - α) = (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α))
    rw [show -(d : ℝ) - α = -((d : ℝ) + α) by ring]
  rw [longRangeMeasure_congr hfun _ _ γ]
  exact power_uncutFirstMoment_ne_top hd (by linarith : (d : ℝ) < (d : ℝ) + α) hγ o


/-! ## Non-vacuity witnesses

The hypothesis `β M < 1` is not merely satisfiable at `β = 0`: the interval theorem above
produces a positive `β₀`, so the finite-mean region is a genuine interval.  The witnesses
below are compiled instances at `d = 1`, `s = 2`. -/

/-- At `β = 0` the power-law model has finite susceptibility (trivially, and the theorem
applies). -/
example : chi (PercLib.CriticalLRP.bernoulliEdgeProb
      (PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin 1 → ℤ => (linfNorm y : ℝ) ^ (-(2 : ℝ))) (powerProfile_even (2 : ℝ)))
      power_kernelJ_nonneg 0) 0 < ⊤ :=
  power_kernelJ_chi_lt_top (d := 1) le_rfl (by norm_num) (by simp) 0

/-- On `ℤ^1` with the profile `‖z‖^{-2}` there is a strictly positive interval of
parameters with finite susceptibility. -/
example : ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ →
      chi (PercLib.CriticalLRP.bernoulliEdgeProb
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin 1 → ℤ => (linfNorm y : ℝ) ^ (-(2 : ℝ))) (powerProfile_even (2 : ℝ)))
        power_kernelJ_nonneg β) 0 < ⊤ :=
  exists_beta_interval_power_kernelJ_chi_lt_top (d := 1) le_rfl (by norm_num) 0

/-- The global critical intensity of the power-law model with `s = 2` on `ℤ^1` is
positive. -/
example : ∃ J : Sym2 (Fin 1 → ℤ) → ℝ≥0,
      (∀ x y : Fin 1 → ℤ, J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-(2 : ℝ)))) ∧
      0 < globalCriticalIntensity J := by
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel
    (fun z : Fin 1 → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-(2 : ℝ))))
    (fun z => by
      show Real.toNNReal ((linfNorm (-z) : ℝ) ^ (-(2 : ℝ)))
        = Real.toNNReal ((linfNorm z : ℝ) ^ (-(2 : ℝ)))
      rw [linfNorm_neg])
  exact ⟨J, hJ, power_globalCriticalIntensity_pos (d := 1) le_rfl (by norm_num) hJ⟩

/-! ## Exact-kernel and conditional literal-threshold wrapper audits -/

#print axioms coe_norm_eq_linfNorm
#print axioms lrKernel_mk_eq_power_kernelJ_mk
#print axioms lrKernel_eq_power_kernelJ
#print axioms lrKernel_infiniteClusterProb_eq_zero
#print axioms lrKernel_lintegral_clusterVol_ne_top
#print axioms lrKernel_le_criticalBeta_of_nonempty
#print axioms lrKernel_criticalBeta_pos_of_nonempty
#print axioms power_kernelJ_le_criticalBeta_of_nonempty
#print axioms power_kernelJ_criticalBeta_pos_of_nonempty

end PercLib.CriticalLRP.PowerLawHighTemp
