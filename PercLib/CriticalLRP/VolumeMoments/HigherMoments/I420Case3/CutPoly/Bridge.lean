/- Integrated and pruned from independently verified `.ultramath/smwxw44gu/m2/Defs.lean`
at production base `33a88a132b440224d63869caa28e7f10dc46e390`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.TreeInterface

/-! # Canonical tree/cutoff polynomial bridges -/

set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval Finset Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP

namespace AuditM2

/-! ## §1. The two iterated-power definitions coincide -/

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **`iterPow K n` and `Kpow K n` are the same kernel for every kernel `K`.**

`iterPow` composes on the left and `Kpow` on the right, but both are the plain
`n`-fold iterated sum `∑_{u₁,…,u_{n-1}} K x u₁ ⋯ K u_{n-1} y`; the induction step is
`Kpow_add K 1 n` (which for `m = 1` reads exactly like `iterPow`'s step) and
`Kpow_one`.  No symmetry of `K` is used, and no summability condition: everything is
`ℝ≥0∞`, where `tsum` is unconditionally associative. -/
theorem iterPow_eq_Kpow (K : V → V → ℝ≥0∞) (n : ℕ) (x y : V) :
    I417Base.iterPow K n x y = KernelPower.Kpow K n x y := by
  induction n generalizing x with
  | zero =>
    rw [KernelPower.Kpow_zero]
    change (if x = y then 1 else 0) = KernelPower.deltaE x y
    by_cases h : x = y
    · subst h
      simp [KernelPower.deltaE_self']
    · rw [KernelPower.deltaE_of_ne' h]
      simp [h]
  | succ n ih =>
    have h1 : KernelPower.Kpow K (n + 1) x y
        = ∑' u, K x u * KernelPower.Kpow K n u y := by
      rw [show n + 1 = 1 + n from by omega, KernelPower.Kpow_add]
      exact tsum_congr fun u => by rw [KernelPower.Kpow_one]
    rw [h1]
    change (∑' u, K x u * I417Base.iterPow K n u y)
      = ∑' u, K x u * KernelPower.Kpow K n u y
    exact tsum_congr fun u => by rw [ih u]

/-- Function-level form of `iterPow_eq_Kpow`. -/
theorem iterPow_eq_Kpow_fun (K : V → V → ℝ≥0∞) (n : ℕ) :
    I417Base.iterPow K n = KernelPower.Kpow K n :=
  funext fun x => funext fun y => iterPow_eq_Kpow K n x y

/-! ## §2. The kernel of the pending tree interface is the cutoff two-point function

`TreeInterface` writes the kernel of `iterPow` as
`fun u v => edgeMeasure π (connSet u v)`.  At the canonical cutoff law
`π = M.cutProb r` this is `M.cutTwoPointE r` *by definition*: `cutLaw r` is
`longRangeMeasure (cutKernel r) (cutKernel_nonneg r) β_c`, `longRangeMeasure` is
`edgeMeasure` of the `bernoulliEdgeProb` profile, and `cutProb r` is that same
profile; `cutTwoPointE r x y` is `(cutLaw r) {ω | Connects ω x y}` and
`connSet x y` is `{ω | Connects ω x y}`.  Basepoints agree: `TreeInterface` uses
`iterPow … j o y` with `o = 0`, `cutPoly` uses `polyK … j 0 y`. -/

/-- The `TreeInterface` kernel at the canonical cutoff law is `M.cutTwoPointE r`,
definitionally. -/
theorem cutProb_kernel (M : Orchestration.SourceModelData) (r : ℝ) :
    (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) = M.cutTwoPointE r :=
  rfl

/-- **The pending tree polynomial is the CutPoly polynomial, at the canonical cutoff
family and with basepoint `0`.** -/
theorem iterPow_cutProb_eq_cutPoly (M : Orchestration.SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) (j : ℕ) :
    I417Base.iterPow (fun u v => (edgeMeasure (M.cutProb r)) (connSet u v)) j 0 y
      = I420Case3.cutPoly M r y j := by
  rw [cutProb_kernel, iterPow_eq_Kpow, I420Case3.cutPoly_eq_Kpow M r hχ]

/-- The same identity in the direction the `poly` slots of the two record structures
need it, as an equality of functions `V → ℕ → ℝ≥0∞`. -/
theorem cutPoly_eq_iterPow_cutProb (M : Orchestration.SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤) :
    (fun y j => I417Base.iterPow
        (fun u v => (edgeMeasure (M.cutProb r)) (connSet u v)) j 0 y)
      = I420Case3.cutPoly M r :=
  funext fun y => funext fun j => iterPow_cutProb_eq_cutPoly M r hχ y j

/-- Depth `0` agrees without any finiteness hypothesis: both sides are the identity
kernel at `0`.  This is the case where a semantic mismatch would be most likely to
hide (`iterPow`'s base is `1[v = w]`, `polyK`'s is `1[x = y]`). -/
theorem iterPow_cutProb_zero_eq_cutPoly_zero (M : Orchestration.SourceModelData) (r : ℝ)
    (y : M.V) :
    I417Base.iterPow (fun u v => (edgeMeasure (M.cutProb r)) (connSet u v)) 0 0 y
      = I420Case3.cutPoly M r y 0 := by
  rw [cutProb_kernel, iterPow_eq_Kpow, I420Case3.cutPoly_zero]
  by_cases h : y = 0
  · subst h
    simp [KernelPower.Kpow_zero, KernelPower.deltaE_self]
  · rw [KernelPower.Kpow_zero, KernelPower.deltaE_of_ne' (Ne.symm h)]
    simp [h]

/-- Exponent `1` agrees without any finiteness hypothesis: both sides are the cutoff
two-point function itself. -/
theorem iterPow_cutProb_one_eq_cutPoly_one (M : Orchestration.SourceModelData) (r : ℝ)
    (y : M.V) :
    I417Base.iterPow (fun u v => (edgeMeasure (M.cutProb r)) (connSet u v)) 1 0 y
      = I420Case3.cutPoly M r y 1 := by
  rw [cutProb_kernel, iterPow_eq_Kpow, KernelPower.Kpow_one, I420Case3.cutPoly_one,
    M.cutTwoPointE_eq_ofReal]

/-! ## §3. The I.4.17 record at the canonical cutoff family, in CutPoly's vocabulary -/

/-- `M.cutProb r e < 1`: the Bond--Küneth hypothesis of I.4.17 at the truncated law
(`1 - e^{-βJ}` is `< 1` because the exponential is positive; it is `0` on edges with
`J e = 0`, still `< 1`). -/
theorem cutProb_lt_one (M : Orchestration.SourceModelData) (r : ℝ) (e : Sym2 M.V) :
    M.cutProb r e < 1 := by
  rw [← Subtype.coe_lt_coe]
  have hcoe : ((M.cutProb r e : unitInterval) : ℝ) =
      1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) := rfl
  rw [hcoe]
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [hone]
  have h := Real.exp_pos (-((M.betaCrit : ℝ) * M.cutKernel r e))
  linarith

/-- The first-moment row constancy `hχ` of I.4.17 holds at the truncated law: the
`τ`-row sum is the cutoff cluster mass, which is basepoint-independent
(`SourceModelData.cutMassAt_eq_zero`). -/
theorem meanVol_cutProb_eq_zero (M : Orchestration.SourceModelData) (r : ℝ) (v : M.V) :
    I417.meanVol (M.cutProb r) v = I417.meanVol (M.cutProb r) 0 := by
  rw [I417.meanVol, I417.meanVol]
  have h1 : ∀ x : M.V, (∑' w : M.V, (edgeMeasure (M.cutProb r)) (connSet x w))
      = M.cutMassAt r x := by
    intro x
    rw [← M.tsum_cutTwoPointE_eq_cutMassAt r x]
    exact tsum_congr fun w => rfl
  rw [h1 v, h1 0, M.cutMassAt_eq_zero r v]

/-- `treePoly` only sees its `poly` argument pointwise, so equal `poly`s give equal
`treePoly`s. -/
theorem treePoly_congr {W : Type*} [Countable W] {poly poly' : W → ℕ → ℝ≥0∞}
    (C : ℕ → ℝ) (Mo : ℝ≥0∞) (p : ℕ)
    (h : ∀ y j, poly y j = poly' y j) (y : W) :
    I420Case3.treePoly poly C Mo p y = I420Case3.treePoly poly' C Mo p y := by
  simp only [I420Case3.treePoly]
  exact Finset.sum_congr rfl fun j _ => by rw [h y j]

/-- **The `HasTreeExpansion` record of `TreeInterface`, rewritten in CutPoly's
vocabulary.**

This is the step the `CutPoly` capstone documents as missing ("a shared tree/cutoff
polynomial bridge"): the pending producer supplies the record for
`poly = fun y j => iterPow … j 0 y`, the polygon side needs it for
`poly = cutPoly M r`, and §2 identifies them.  Residual hypotheses: only `hχ`
(finiteness of `E_{β_c,r}|K|`), `ℓ + 1 ≤ p`, and the two automatic facts of §3.
In particular no triangle condition, no first-moment asymptotic, no homogeneity. -/
theorem hasTreeExpansion_cutPoly (M : Orchestration.SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤) (B : Finset M.V) {p ℓ : ℕ} (hℓ : ℓ + 1 ≤ p) :
    I420Case3.HasTreeExpansion (M.cutProb r) (0 : M.V) B (ℓ + 1) (p - ℓ) p
      (I420Case3.cutPoly M r)
      (fun j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) := by
  have hfam := AuditM1.hasTreeExpansion_family (π := M.cutProb r) (cutProb_lt_one M r)
    (0 : M.V) B (p := p) (ℓ := ℓ) hℓ (meanVol_cutProb_eq_zero M r)
  refine ⟨fun y hy => ?_⟩
  have h := hfam.expansion y hy
  rw [treePoly_congr (C := fun j => ((I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℕ) : ℝ))
    (Mo := I420Case1.powMomentAt (M.cutProb r) 1 0) (p := p)
    (fun y j => iterPow_cutProb_eq_cutPoly M r hχ y j) y] at h
  exact h


/-- Finiteness of the cutoff susceptibility from the source's first-moment
asymptotic, packaged for the canonical tree/polygon assembly. -/
theorem cutMassAt_ne_top_of_hP (M : Orchestration.SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r → M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨c₀, hc₀, hχu⟩ := I418C.ChiInput.exists_chi_lower_uniform M
    (I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP) hP
  exact ⟨c₀, hc₀, fun r hr =>
    I418C.ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hr (hχu r hr)⟩

end AuditM2

end PercLib.CriticalLRP
