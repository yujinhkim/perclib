/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Diagonal bounds and tail conversions for the configured open triangle

Accepted from independent submission `smwp648b3` direction D2.  The tail need
not tend to zero merely from Cauchy–Schwarz: Kozma's operator square-root step
is separate and remains a source-gap hypothesis in `TriTailSqrt`.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The open-triangle tail `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.4.1, paragraph at `paper.html#S4.SS1.p1.1@L2077-L2077`:

  "Recall that the triangle diagram is defined by
   `∇_β = ∑_{x,y} P_β(0↔x) P_β(x↔y) P_β(y↔0)`
   and that the triangle condition is said to hold if `∇_{β_c} < ∞`. We also define the open
   triangle `∇_β(0,x) = ∑_{y,z} P_β(0↔y) P_β(y↔z) P_β(z↔x)` and write
   `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`, which goes to zero as `r → ∞` whenever the triangle
   condition holds [83, 12]."

The cited proof is G. Kozma, *The triangle and the open triangle*, Ann. IHP Probab. Stat. 47
(2011) 75--79 (arXiv:0907.1959): "for percolation on any transitive graph, the triangle condition
implies the open triangle condition", i.e.
`lim_{R→∞} max_{w ∉ B(v,R)} ∑_{x,y} P(v↔x) P(x↔y) P(y↔w) = 0`.

## What this file proves (all on the model's actual configured two-point function)

* `openTriangle` / `openTriangleSelf`: the source's `∇_β(0,x)` and `∇_β`.
* `openTriangle_le_diagonal_rpow`, `openTriangle_le_diagonal`: the pointwise bound
  `∇(0,x) ≤ (∇(0,0) ∇(x,x))^{1/2}`, transported from the native
  `PercLib.Percolation.Bond.triangle_le_rpow`; this is where the *constant* comes from.
* `openTriangleSelf_eq_origin`: `∇(x,x) = ∇(0,0)` for every `x`, by translation invariance.
  Together: `∇(0,x) ≤ ∇_{β_c}` for all `x`.
* `openTriangleTail`: the source's literal `∇_r = sup_{‖x‖ ≥ r} ∇(0,x)`.
* `openTriangleTail_le_diagonal`, `openTriangleTail_ne_top`: `∇_r ≤ ∇_{β_c} < ∞`.
* `openTriangleTail_antitone`, `openTriangleTail_le_iff`, and the strict/ball form
  `openTriangleTailOpen_eq_iSup_compl_ball`: Kozma's `sup_{w ∉ B(v,R)}` form.
* `tendsto_openTriangleTail_iff`: `∇_r → 0` iff for every `ε > 0` the pointwise bound
  `∇(0,x) ≤ ε` holds for all `x` of norm at least some `R`. This is the exact formal content of
  the source's "`∇_r → 0`", and the form in which the §I.4.18 consumers use it.

## What this file does *not* prove

The implication `∇_{β_c} < ∞ ⟹ ∇_r → 0` (Kozma's theorem) is **not** proved here. It does not
follow from the pointwise bound or from monotonicity: `∇_r ≤ ∇_{β_c}` gives boundedness only.
`TriTailSqrt.lean` reduces Kozma's proof to an explicit, checkable operator-theoretic input (an
`ℓ²` square root of the open-triangle kernel) and proves everything after it; `REPORT.md` records
the exact missing input.

No `sorry`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTail.Defs
public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging
public import PercLib.Percolation.Bond.ConnectionKernel
public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.CountableProduct.LRPTailBounds

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal Topology
open Filter

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}

/-! ### The configured kernel and the two spellings of `τ` -/

/-- The migrated long-range two-point function is the native bond connection kernel at the
Bernoulli edge probability `1 - exp(-β J e)`. -/
theorem tau_bernoulliEdgeProb (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : Fin d → ℤ) :
    PercLib.Percolation.Bond.tau (bernoulliEdgeProb J hJ β) x y
      = twoPointFunction J hJ β x y := by
  simp only [PercLib.Percolation.Bond.tau, twoPointFunction, longRangeMeasure,
    PercLib.Percolation.Bond.conn, edgeMeasure_eq_law]

/-! ### The open triangle -/

theorem openTriangleSelf_eq_def (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x : Fin d → ℤ) :
    openTriangleSelf J hJ β x =
      ∑' u, ∑' v, twoPointFunction J hJ β x u * twoPointFunction J hJ β u v *
        twoPointFunction J hJ β v x := rfl

/-! ### The diagonal supplies the constant -/

/-- **Cauchy--Schwarz for the open triangle**, at the configured kernel:
`∇(x,y) ≤ (∇(x,x) ∇(y,y))^{1/2}`. No finiteness hypothesis is needed. -/
theorem openTriangle_le_diagonal_rpow (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : Fin d → ℤ) :
    openTriangle J hJ β x y ≤
      (openTriangleSelf J hJ β x * openTriangleSelf J hJ β y) ^ (1 / 2 : ℝ) := by
  have h := PercLib.Percolation.Bond.triangle_le_rpow (bernoulliEdgeProb J hJ β) x y
  simpa only [openTriangle, openTriangleSelf, tau_bernoulliEdgeProb] using h

/-- **The diagonal does not depend on the site**, `∇(x,x) = ∇(0,0)`, by translation invariance
of the two-point function. This is what makes the diagonal value a single *constant*. -/
theorem openTriangleSelf_eq_origin {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x : Fin d → ℤ) :
    openTriangleSelf J hJ β x = openTriangleSelf J hJ β 0 := by
  have hA : ∀ u' : Fin d → ℤ,
      twoPointFunction J hJ β x (u' + x) = twoPointFunction J hJ β 0 u' := by
    intro u'
    simpa using twoPointFunction_shift hJinv hJ β x (0 : Fin d → ℤ) u'
  have hB : ∀ u' v' : Fin d → ℤ,
      twoPointFunction J hJ β (u' + x) (v' + x) = twoPointFunction J hJ β u' v' :=
    fun u' v' => twoPointFunction_shift hJinv hJ β x u' v'
  have hC : ∀ v' : Fin d → ℤ,
      twoPointFunction J hJ β (v' + x) x = twoPointFunction J hJ β v' 0 := by
    intro v'
    simpa using twoPointFunction_shift hJinv hJ β x v' (0 : Fin d → ℤ)
  rw [openTriangleSelf_eq_def, openTriangleSelf_eq_def]
  rw [← Equiv.tsum_eq (Equiv.addRight x)
    (fun u => ∑' v, twoPointFunction J hJ β x u * twoPointFunction J hJ β u v *
      twoPointFunction J hJ β v x)]
  simp only [Equiv.coe_addRight]
  have hinner : ∀ u' : Fin d → ℤ,
      (∑' v, twoPointFunction J hJ β x (u' + x) * twoPointFunction J hJ β (u' + x) v *
          twoPointFunction J hJ β v x)
        = ∑' v', twoPointFunction J hJ β x (u' + x) *
            twoPointFunction J hJ β (u' + x) (v' + x) *
            twoPointFunction J hJ β (v' + x) x := by
    intro u'
    rw [← Equiv.tsum_eq (Equiv.addRight x)
      (fun v => twoPointFunction J hJ β x (u' + x) * twoPointFunction J hJ β (u' + x) v *
        twoPointFunction J hJ β v x)]
    simp only [Equiv.coe_addRight]
  simp only [hinner]
  simp only [hA, hB, hC]

/-- **`∇(0,x) ≤ ∇_{β_c}`**: the diagonal value is a uniform bound for the open triangle. -/
theorem openTriangle_le_diagonal {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x : Fin d → ℤ) :
    openTriangle J hJ β 0 x ≤ openTriangleSelf J hJ β 0 := by
  have h := openTriangle_le_diagonal_rpow J hJ β 0 x
  rw [openTriangleSelf_eq_origin hJinv hJ β x, ← sq] at h
  refine h.trans (le_of_eq ?_)
  simpa [one_div] using
    ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (openTriangleSelf J hJ β 0)

/-! ### The tail `∇_r = sup_{‖x‖ ≥ r} ∇(0,x)` -/

/-- The tail is a supremum, so it is bounded by `a` exactly when the pointwise tail bound holds. -/
theorem openTriangleTail_le_iff (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {r : ℝ} {a : ℝ≥0∞} :
    openTriangleTail J hJ β r ≤ a ↔ ∀ x, r ≤ FiniteVolume.latticeDist 0 x →
      openTriangle J hJ β 0 x ≤ a := by
  rw [openTriangleTail, iSup₂_le_iff]

/-- Every individual value with `‖x‖ ≥ r` is below the tail value `∇_r`. -/
theorem le_openTriangleTail (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {r : ℝ} {x : Fin d → ℤ} (hx : r ≤ FiniteVolume.latticeDist 0 x) :
    openTriangle J hJ β 0 x ≤ openTriangleTail J hJ β r :=
  le_iSup₂ (f := fun x (_ : r ≤ FiniteVolume.latticeDist 0 x) => openTriangle J hJ β 0 x) x hx

/-- `∇_r` is nonincreasing in `r`. -/
theorem openTriangleTail_antitone (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    Antitone (openTriangleTail J hJ β) := by
  intro r r' hrr'
  refine iSup_le fun x => iSup_le fun hx =>
    le_iSup₂ (f := fun x (_ : r ≤ FiniteVolume.latticeDist 0 x) => openTriangle J hJ β 0 x)
      x (le_trans hrr' hx)

/-- **`∇_r ≤ ∇_{β_c}`**: the tail is bounded by the (finite, under the triangle condition)
diagonal value. This is the only use of the triangle condition in this file. -/
theorem openTriangleTail_le_diagonal {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (r : ℝ) :
    openTriangleTail J hJ β r ≤ openTriangleSelf J hJ β 0 :=
  (openTriangleTail_le_iff J hJ β).mpr fun x _ => openTriangle_le_diagonal hJinv hJ β x

/-- Under the triangle condition `∇_{β_c} < ∞` the tail is finite. -/
theorem openTriangleTail_ne_top {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (r : ℝ)
    (hTri : openTriangleSelf J hJ β 0 < ⊤) :
    openTriangleTail J hJ β r < ⊤ :=
  (openTriangleTail_le_diagonal hJinv hJ β r).trans_lt hTri

/-- **The tail over the complement of the closed lattice ball**: `∇^{>}_{r} = sup_{w ∉ B_r(0)}`,
the exact form of the "open triangle condition" in Kozma (2011). -/
theorem openTriangleTailOpen_eq_iSup_compl_ball (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (r : ℝ) :
    openTriangleTailOpen J hJ β r =
      ⨆ x, ⨆ (_ : x ∉ Percolation.latticeBallR r 0), openTriangle J hJ β 0 x := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x => iSup_le fun hx => ?_
    refine le_iSup₂ (f := fun x (_ : x ∉ Percolation.latticeBallR r 0) =>
      openTriangle J hJ β 0 x) x ?_
    rw [Percolation.mem_latticeBallR_iff]
    exact not_le.2 hx
  · refine iSup_le fun x => iSup_le fun hx => ?_
    refine le_iSup₂ (f := fun x (_ : r < FiniteVolume.latticeDist 0 x) =>
      openTriangle J hJ β 0 x) x ?_
    by_contra hcon
    exact hx (by rw [Percolation.mem_latticeBallR_iff]; exact not_lt.mp hcon)

/-- `∇^{>}_{r} ≤ ∇_r`: the strict condition implies the closed one. -/
theorem openTriangleTailOpen_le_tail (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (r : ℝ) :
    openTriangleTailOpen J hJ β r ≤ openTriangleTail J hJ β r :=
  iSup_le fun x => iSup_le fun hx =>
    le_iSup₂ (f := fun x (_ : r ≤ FiniteVolume.latticeDist 0 x) =>
      openTriangle J hJ β 0 x) x (le_of_lt hx)

/-- **The source's `‖x‖ ≥ r` and Kozma's `w ∉ B(v,r)` have the same tail**: the strict tail at
`r - 1` is sandwiched between the closed tail at `r` and the strict tail at `r`. -/
theorem openTriangleTail_sandwich (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (r : ℝ) :
    openTriangleTail J hJ β r ≤ openTriangleTailOpen J hJ β (r - 1) ∧
      openTriangleTailOpen J hJ β r ≤ openTriangleTail J hJ β r := by
  refine ⟨iSup_le fun x => iSup_le fun hx => ?_, openTriangleTailOpen_le_tail J hJ β r⟩
  refine le_iSup₂ (f := fun x (_ : r - 1 < FiniteVolume.latticeDist 0 x) =>
    openTriangle J hJ β 0 x) x ?_
  linarith

/-! ### `∇_r → 0`: the exact formal content -/

/-- **The two formulations of `∇_r → 0` agree**: the supremum formulation converges to `0` iff
for every `ε > 0` the pointwise bound `∇(0,x) ≤ ε` holds on the tail `{‖x‖ ≥ r}`. This is the
form in which the §I.4.18 consumers use the source's `∇_r → 0`. -/
theorem tendsto_openTriangleTail_iff (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ x : Fin d → ℤ,
        R ≤ FiniteVolume.latticeDist 0 x → openTriangle J hJ β 0 x ≤ ε := by
  rw [ENNReal.tendsto_nhds_zero]
  constructor
  · intro h ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.1 (h ε hε)
    exact ⟨R, fun x hx => (le_openTriangleTail J hJ β hx).trans (hR R le_rfl)⟩
  · intro h ε hε
    obtain ⟨R, hR⟩ := h ε hε
    refine eventually_atTop.2 ⟨R, fun r hr => ?_⟩
    exact (openTriangleTail_le_iff J hJ β).mpr fun x hx => hR x (le_trans hr hx)


/-! ### Sharpness: the diagonal/Cauchy--Schwarz hypotheses alone cannot give decay

`openTriangle_le_diagonal` uses exactly three properties: `τ` is a positive-semidefinite (Gram)
kernel, `τ(x,y)` depends only on `y - x` (translation invariance), and the diagonal value is finite.
The constant kernel below has all three and its tail does **not** vanish. Hence `∇_r ≤ ∇_{β_c}`
cannot be turned into `∇_r → 0` by any argument from those properties alone; Kozma's theorem uses
more of the model (the `ℓ²` square root of the open-triangle kernel, `TriTailSqrt.lean`). -/

/-- The constant kernel `k ≡ 1` on any vertex set is a Gram (positive-semidefinite) kernel: every
finite section is PSD, in the `∑ᵢⱼ aᵢaⱼ k(f i - f j) ≥ 0` form used by the native
`sum_mul_tau_nonneg`. -/
theorem constantKernel_psd {G ι : Type*} [Fintype ι] (_f : ι → G) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * (1 : ℝ) := by
  have h : ∑ i, ∑ j, a i * a j * (1 : ℝ) = (∑ i, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  exact sq_nonneg _

/-- **Sharpness.** The constant kernel is translation invariant (it is constant), has
`k 0 = 1 < ∞`, and its tail does not vanish: `sup_{‖x‖ ≥ r} k x = 1` for every `r`. So the
hypotheses used by `openTriangle_le_diagonal` / `openTriangleTail_le_diagonal`
(PSD kernel + translation invariance + finite diagonal) do not imply decay, and `∇_r ≤ ∇_{β_c}`
cannot be upgraded to `∇_r → 0` without further input from the model. -/
theorem constantKernel_not_tendsto_zero {G : Type*} [Infinite G] :
    ¬ Tendsto (fun _ : G => (1 : ℝ)) cofinite (𝓝 0) := by
  intro h
  have hε : ∀ᶠ x : G in cofinite, |(1 : ℝ)| < 1 / 2 := by
    have h' := (Metric.tendsto_nhds (f := cofinite) (u := fun _ : G => (1 : ℝ)) (a := 0)).1 h
    filter_upwards [h' (1 / 2) (by norm_num)] with x hx
    simpa [Real.dist_eq] using hx
  have hfin : {x : G | ¬ |(1 : ℝ)| < 1 / 2}.Finite := eventually_cofinite.1 hε
  have huniv : {x : G | ¬ |(1 : ℝ)| < 1 / 2} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    norm_num
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

end PercLib.CriticalLRP.TriTail

#print axioms PercLib.CriticalLRP.TriTail.tau_bernoulliEdgeProb
#print axioms PercLib.CriticalLRP.TriTail.openTriangle_le_diagonal_rpow
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_eq_origin
#print axioms PercLib.CriticalLRP.TriTail.openTriangle_le_diagonal
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_le_diagonal
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_ne_top
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_sandwich
#print axioms PercLib.CriticalLRP.TriTail.tendsto_openTriangleTail_iff
#print axioms PercLib.CriticalLRP.TriTail.constantKernel_psd
#print axioms PercLib.CriticalLRP.TriTail.constantKernel_not_tendsto_zero
