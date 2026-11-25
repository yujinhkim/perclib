/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Kernel and cut-off kernel geometry for Hutchcroft, "Critical long-range
percolation I", arXiv:2508.18807v1, Definitions I.1.3 and I.1.5.

The paper works with a radial profile `r ↦ J(r)` which is decreasing and
differentiable on `(0,∞)`, with `J(x,y) = 1(x ≠ y) J(‖x − y‖)` and
`J(x,y) = 1(x ≠ y) ∫_{‖x−y‖}^∞ |J'(s)| ds`, and defines the cut-off kernel
(Definition I.1.5) as

  `J_r(x,y) = 1(x ≠ y, ‖x − y‖ ≤ r) ∫_{‖x−y‖}^r |J'(s)| ds`
            `= 1(x ≠ y, ‖x − y‖ ≤ r) (J(‖x−y‖) − J(r))`.

We take the closed form as the definition and record, with no hypotheses
beyond antitonicity and nonnegativity of the profile:

* `J_r ≤ J` and `J_r` is increasing in `r` (so that `P_{β,r} ⇀ P_β`);
* the quantitative strict domination `J_r ≤ (1 − ε) J` of Definition I.1.5,
  valid on a lattice whose distinct points are at distance `≥ 1`;
* `∂/∂r J_r(x,y) = |J'(r)|`, hence `∂/∂r (1 − exp(−β J_r)) = β|J'(r)|(1 − p)`,
  the "rate at which `{x,y}` flips from closed to open" used in the proof of
  Lemma I.4.1;
* the model profile `r ↦ r^{-(d+α)}` with its exact derivative, giving
  `J(r) = r^{-d-α}` and `|J'(r)| = (d+α) r^{-d-α-1}`.

Faithfulness note. `r ↦ J_r(x,y)` is not differentiable at `r = ‖x−y‖` (the
left derivative is `0`, the right derivative is `|J'(r)|`). Consequently the
identity (I.4.1) of the paper, stated there for every `r > 0`, holds at every
`r` outside the locally finite set `{‖x−y‖ : x ≠ y}` of edge lengths of the
cut-off graph, and hence almost everywhere; that is all its use as a
differential equation requires.
-/
module

public import PercLib.CriticalLRP.FiniteBernoulli
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Topology

namespace PercLib.CriticalLRP.FiniteVolume

/-! ## Monotonicity of the edge probability in `β` and in `J` -/

theorem longRangeEdgeProbability_mono_beta {J β β' : ℝ} (hJ : 0 ≤ J) (h : β ≤ β') :
    longRangeEdgeProbability β J ≤ longRangeEdgeProbability β' J := by
  have hle : β * J ≤ β' * J := mul_le_mul_of_nonneg_right h hJ
  have hle' : -(β' * J) ≤ -(β * J) := neg_le_neg hle
  have hexp : Real.exp (-(β' * J)) ≤ Real.exp (-(β * J)) := Real.exp_le_exp.mpr hle'
  unfold longRangeEdgeProbability
  linarith

theorem longRangeEdgeProbability_mono_J {β J J' : ℝ} (hβ : 0 ≤ β) (h : J ≤ J') :
    longRangeEdgeProbability β J ≤ longRangeEdgeProbability β J' := by
  have hle : β * J ≤ β * J' := mul_le_mul_of_nonneg_left h hβ
  have hle' : -(β * J') ≤ -(β * J) := neg_le_neg hle
  have hexp : Real.exp (-(β * J')) ≤ Real.exp (-(β * J)) := Real.exp_le_exp.mpr hle'
  unfold longRangeEdgeProbability
  linarith

theorem longRangeEdgeProbability_zero_right (β : ℝ) :
    longRangeEdgeProbability β 0 = 0 := by
  simp [longRangeEdgeProbability]

theorem hasDerivAt_longRangeEdgeProbability (β J : ℝ) :
    HasDerivAt (fun b => longRangeEdgeProbability b J)
      (Real.exp (-(β * J)) * J) β := by
  have h1 : HasDerivAt (fun b : ℝ => b * (-J)) (-J) β := by
    simpa only [id, one_mul] using (hasDerivAt_id β).mul_const (-J)
  have h3 : HasDerivAt (fun b : ℝ => Real.exp (b * (-J))) (Real.exp (β * (-J)) * (-J)) β :=
    h1.exp
  have h4 : HasDerivAt (fun b : ℝ => 1 - Real.exp (b * (-J)))
      (0 - Real.exp (β * (-J)) * (-J)) β := (hasDerivAt_const (x := β) (c := (1 : ℝ))).sub h3
  have harg : β * (-J) = -(β * J) := by ring
  rw [harg] at h4
  have h5 : (0 : ℝ) - Real.exp (-(β * J)) * (-J) = Real.exp (-(β * J)) * J := by ring
  rw [h5] at h4
  simpa only [longRangeEdgeProbability, mul_neg] using h4

/-! ## The model profile `r ↦ r^{-(d+α)}` -/

/-- The radial profile `J(r) = r^{-d-α}` of Definition I.1.3 with `δ ≡ 0`. -/
noncomputable def modelProfile (d : ℕ) (α s : ℝ) : ℝ := s ^ (-(d : ℝ) - α)

theorem modelProfile_pos {d : ℕ} {α s : ℝ} (hs : 0 < s) : 0 < modelProfile d α s :=
  Real.rpow_pos_of_pos hs _

theorem modelProfile_nonneg {d : ℕ} {α s : ℝ} (hs : 0 ≤ s) : 0 ≤ modelProfile d α s :=
  Real.rpow_nonneg hs _

theorem modelProfile_antitoneOn (d : ℕ) {α : ℝ} (h : 0 ≤ (d : ℝ) + α) :
    AntitoneOn (modelProfile d α) (Set.Ioi 0) := by
  intro s hs t ht hst
  simp only [Set.mem_Ioi] at hs ht
  exact Real.rpow_le_rpow_of_nonpos hs hst (by linarith)

/-- On the interior the profile is differentiable with the exact derivative
`J'(r) = -(d+α) r^{-d-α-1}`. -/
theorem hasDerivAt_modelProfile {d : ℕ} {α s : ℝ} (hs : 0 < s) :
    HasDerivAt (modelProfile d α) (-((d : ℝ) + α) * s ^ (-(d : ℝ) - α - 1)) s := by
  have h := Real.hasDerivAt_rpow_const (p := -(d : ℝ) - α) (x := s) (Or.inl hs.ne')
  convert h using 1
  · funext x
    rfl
  · ring

/-- In the notation `|J'(r)|` of the paper: the derivative of the model profile
is `-(d+α) r^{-d-α-1}`, whose absolute value is `(d+α) r^{-d-α-1}`. -/
theorem abs_modelProfile_deriv {d : ℕ} {α s : ℝ} (hs : 0 < s) (hd : 0 ≤ (d : ℝ) + α) :
    |(-((d : ℝ) + α)) * s ^ (-(d : ℝ) - α - 1)| =
      ((d : ℝ) + α) * s ^ (-(d : ℝ) - α - 1) := by
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hs.le _), abs_of_nonneg (by linarith)]

/-! ## The cut-off profile of Definition I.1.5 -/

/-- The cut-off profile `∫_s^r |J'| = J(s) − J(r)` for `s ≤ r`, and `0` for `s > r`.
This is Definition I.1.5 with the fundamental theorem of calculus already applied. -/
noncomputable def cutoffProfile (K : ℝ → ℝ) (r s : ℝ) : ℝ :=
  if s ≤ r then K s - K r else 0

theorem cutoffProfile_of_le {K : ℝ → ℝ} {r s : ℝ} (h : s ≤ r) :
    cutoffProfile K r s = K s - K r := by
  unfold cutoffProfile
  rw [ite_eq_left h]

theorem cutoffProfile_of_lt {K : ℝ → ℝ} {r s : ℝ} (h : r < s) :
    cutoffProfile K r s = 0 := by
  unfold cutoffProfile
  rw [ite_eq_right (not_le.mpr h)]

theorem cutoffProfile_nonneg {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    {r s : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s ≤ r) : 0 ≤ cutoffProfile K r s := by
  rw [cutoffProfile_of_le hsr]
  have := hK hs hr hsr
  linarith

/-- `J_r ≤ J`: cutting off at `r` can only lower the kernel (Definition I.1.5). -/
theorem cutoffProfile_le {K : ℝ → ℝ} (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    {r s : ℝ} (hs : 0 < s) (hr : 0 < r) : cutoffProfile K r s ≤ K s := by
  rcases le_or_gt s r with h | h
  · rw [cutoffProfile_of_le h]
    have h1 := hKnn r hr
    linarith
  · rw [cutoffProfile_of_lt h]
    exact hKnn s hs

/-- `J_r` is increasing in `r`: the cut-off kernels increase to `J`. -/
theorem cutoffProfile_mono_r {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    {r r' s : ℝ} (hr : 0 < r) (hr' : 0 < r') (hs : 0 < s) (h : r ≤ r') :
    cutoffProfile K r s ≤ cutoffProfile K r' s := by
  rcases le_or_gt s r with hsr | hsr
  · rw [cutoffProfile_of_le hsr, cutoffProfile_of_le (le_trans hsr h)]
    have := hK hr hr' h
    linarith
  · rw [cutoffProfile_of_lt hsr]
    rcases le_or_gt s r' with h' | h'
    · exact cutoffProfile_nonneg hK hs hr' h'
    · rw [cutoffProfile_of_lt h']

/-- `J_r → J` pointwise as `r → ∞`, provided the profile vanishes at infinity.
Together with `cutoffProfile_mono_r` this says `J_r ↑ J`. -/
theorem tendsto_cutoffProfile {K : ℝ → ℝ} {s : ℝ} (hK : Tendsto K atTop (𝓝 0)) :
    Tendsto (fun r => cutoffProfile K r s) atTop (𝓝 (K s)) := by
  have h' : Tendsto (fun r => K s - K r) atTop (𝓝 (K s)) := by
    have h := hK.const_sub (K s)
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop s] with r hr
  exact (cutoffProfile_of_le hr).symm

/-- **Definition I.1.5, strict domination.** On a lattice in which distinct
points are at distance at least `1`, the cut-off kernel is dominated by
`(1 − ε) J` with `ε = J(r)/J(1) > 0`, hence `P_{β_c, r}` is stochastically
dominated by a subcritical measure, as the paper asserts. -/
theorem cutoffProfile_dominated {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    {r s : ℝ} (hs : 1 ≤ s) (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) :
    cutoffProfile K r s ≤ (1 - K r / K 1) * K s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hKs1 : K s ≤ K 1 := hK (Set.mem_Ioi.mpr zero_lt_one) hs0 hs
  have hKr1 : K r ≤ K 1 := hK (Set.mem_Ioi.mpr zero_lt_one) hr0 hr
  have hε : 0 < K r / K 1 := div_pos hKr hK1
  have hε1 : K r / K 1 ≤ 1 := by rw [div_le_one hK1]; exact hKr1
  rcases le_or_gt s r with h | h
  · rw [cutoffProfile_of_le h]
    have hcoef : 0 ≤ K r * (K 1 - K s) / K 1 :=
      div_nonneg (mul_nonneg hKr.le (by linarith)) hK1.le
    have heq : K s - K r = (1 - K r / K 1) * K s - K r * (K 1 - K s) / K 1 := by
      field_simp; ring
    rw [heq]
    linarith
  · rw [cutoffProfile_of_lt h]
    have hKsn : 0 ≤ K s := hKnn s hs0
    have hnn : 0 ≤ (1 - K r / K 1) * K s := mul_nonneg (by linarith) hKsn
    linarith

/-! ## Derivative of the cut-off profile in `r` -/

/-- For `s < r`, `r' ↦ J_{r'}(s)` is differentiable with derivative `|J'(r)|`,
given that the profile has derivative `−|J'(r)|` at `r`. This is the "rate at
which an edge of length `s` flips from closed to open as `r` is increased". -/
theorem hasDerivAt_cutoffProfile {K : ℝ → ℝ} {K' r s : ℝ} (hsr : s < r)
    (hK : HasDerivAt K (-K') r) :
    HasDerivAt (fun r' => cutoffProfile K r' s) K' r := by
  have hev : ∀ᶠ r' in 𝓝 r, s ≤ r' := eventually_ge_nhds hsr
  have hder : HasDerivAt (fun r' => K s - K r') K' r := by
    have h := hK.const_sub (K s)
    simpa only [neg_neg] using h
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [hev] with r' hr'
  rw [cutoffProfile_of_le hr']

/-- For `s > r` the cut-off profile is locally zero, so its derivative vanishes. -/
theorem hasDerivAt_cutoffProfile_of_lt {K : ℝ → ℝ} {r s : ℝ} (hrs : r < s) :
    HasDerivAt (fun r' => cutoffProfile K r' s) 0 r := by
  have hev : ∀ᶠ r' in 𝓝 r, r' < s := eventually_lt_nhds hrs
  refine (hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with r' hr'
  rw [cutoffProfile_of_lt hr']

/-- **The rate identity of the proof of Lemma I.4.1**: with `q(r)` the open
probability of an edge of length `s < r` under the cut-off kernel,
`q'(r) = β |J'(r)| (1 − q(r))`. -/
theorem hasDerivAt_cutoffEdgeProbability {K : ℝ → ℝ} {K' r s : ℝ} (hsr : s < r)
    (hK : HasDerivAt K (-K') r) (β : ℝ) :
    HasDerivAt (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (β * K' * Real.exp (-(β * cutoffProfile K r s))) r := by
  have hu : HasDerivAt (fun r' => cutoffProfile K r' s) K' r :=
    hasDerivAt_cutoffProfile hsr hK
  have hb : HasDerivAt (fun r' => β * cutoffProfile K r' s) (β * K') r := hu.const_mul β
  have hb' : HasDerivAt (fun r' => -(β * cutoffProfile K r' s)) (-(β * K')) r := hb.neg
  have he : HasDerivAt (fun r' => Real.exp (-(β * cutoffProfile K r' s)))
      (Real.exp (-(β * cutoffProfile K r s)) * (-(β * K'))) r := hb'.exp
  have hf : HasDerivAt (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s)))
      (0 - Real.exp (-(β * cutoffProfile K r s)) * (-(β * K'))) r :=
    (hasDerivAt_const (x := r) (c := (1 : ℝ))).sub he
  have hval : (0 : ℝ) - Real.exp (-(β * cutoffProfile K r s)) * (-(β * K'))
      = β * K' * Real.exp (-(β * cutoffProfile K r s)) := by ring
  rw [hval] at hf
  simpa only [longRangeEdgeProbability] using hf

/-- The `(1 − q)` form of the rate identity: `1 − q(r) = exp(−β J_r)`. -/
theorem one_sub_cutoffEdgeProbability {K : ℝ → ℝ} {r s β : ℝ} :
    1 - longRangeEdgeProbability β (cutoffProfile K r s)
      = Real.exp (-(β * cutoffProfile K r s)) := by
  simp [longRangeEdgeProbability]

/-! ## Lattice kernels

The following definitions package the pointwise facts above into the kernels of
the paper, for a vertex type `V` equipped with a "distance" `ρ` (for
`V = ℤ^d` this is `‖x − y‖` for the chosen norm). -/

/-- The kernel `J(x,y) = 1(x ≠ y) J(ρ x y)`. -/
noncomputable def radialKernel {V : Type*} [DecidableEq V] (K : ℝ → ℝ) (ρ : V → V → ℝ)
    (x y : V) : ℝ :=
  if x = y then 0 else K (ρ x y)

/-- The cut-off kernel `J_r` of Definition I.1.5. -/
noncomputable def cutoffKernel {V : Type*} [DecidableEq V] (K : ℝ → ℝ) (ρ : V → V → ℝ) (r : ℝ)
    (x y : V) : ℝ :=
  if x = y then 0 else cutoffProfile K r (ρ x y)

theorem cutoffKernel_eq_of_ne {V : Type*} [DecidableEq V] (K : ℝ → ℝ) (ρ : V → V → ℝ) (r : ℝ)
    {x y : V} (h : x ≠ y) : cutoffKernel K ρ r x y = cutoffProfile K r (ρ x y) := by
  simp [cutoffKernel, h]

theorem radialKernel_eq_of_ne {V : Type*} [DecidableEq V] (K : ℝ → ℝ) (ρ : V → V → ℝ)
    {x y : V} (h : x ≠ y) : radialKernel K ρ x y = K (ρ x y) := by
  simp [radialKernel, h]

theorem cutoffKernel_le_radialKernel {V : Type*} [DecidableEq V] {K : ℝ → ℝ}
    (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    {ρ : V → V → ℝ} {r : ℝ} (hr : 0 < r)
    (hρ : ∀ x y : V, x ≠ y → 0 < ρ x y) (x y : V) :
    cutoffKernel K ρ r x y ≤ radialKernel K ρ x y := by
  by_cases h : x = y
  · simp [cutoffKernel, radialKernel, h]
  · rw [cutoffKernel_eq_of_ne K ρ r h, radialKernel_eq_of_ne K ρ h]
    exact cutoffProfile_le hKnn (hρ x y h) hr

theorem cutoffKernel_mono_r {V : Type*} [DecidableEq V] {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0))
    {ρ : V → V → ℝ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hρ : ∀ x y : V, x ≠ y → 0 < ρ x y) (x y : V) (h : r ≤ r') :
    cutoffKernel K ρ r x y ≤ cutoffKernel K ρ r' x y := by
  by_cases hxy : x = y
  · simp [cutoffKernel, hxy]
  · rw [cutoffKernel_eq_of_ne K ρ r hxy, cutoffKernel_eq_of_ne K ρ r' hxy]
    exact cutoffProfile_mono_r hK hr hr' (hρ x y hxy) h

end PercLib.CriticalLRP.FiniteVolume
