/-
Independently recovered from Ultramath `smwywszgo/m5` findings and rebuilt.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Primitive consistency for the radius identity

Swarm `smwywszgo`, member `m5`, direction `d7`.

The `p = 2` cutoff-moment identity of the critical-LRP second-moment development is proved
window by window on *corner-free* radius windows, i.e. on intervals whose interior avoids the
locally finite set `C` of attained edge lengths.  This file isolates the purely
order-theoretic/additive facts that transfer such a window-by-window statement to a single
identity with one fixed base point on a window that *contains* corner radii:

* `integral_sub_base` — the base-point form of Chasles' relation: the integral over `[u,x]` is
  the difference of the two integrals with common base `a`.  It is pure additivity of the
  interval integral; no continuity, no differentiability and no primitive theory are involved.
* `integral_eq_sub_of_offCorner` — if `f` is continuous on `[a,b]`, `g` is interval integrable on
  `[a,b]`, `C` is finite and the identity `∫_u^x g = f x - f u` holds on every corner-free
  closed subwindow `[u,v] ⊆ [a,b]` (with base point the *left* endpoint `u` of that subwindow,
  which is what the off-corner producers give), then the identity holds on all of `[a,b]` with
  the single base point `a`.

The mechanism is not a limiting argument at the corner radii and assumes nothing about one-sided
limits of the primitive or of `f` there.  Instead the difference

`H x = f x - ∫_a^x g`

is *locally constant* at every non-corner radius (base-point change converts the identity of the
subwindow into constancy of `H` on that subwindow), `H` is continuous on `[a,b]` because both `f`
and the interval primitive are, and a continuous function that is locally constant off a finite
set is constant.  The finite-set step is `exists_const_of_localConst_off_finite`, proved by
splitting the window at the largest exceptional radius, where the two sides of the split are
handled by the induction hypothesis and by the corner-free case respectively.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Set.Finite.Basic

/-!
# Primitive consistency across finite exceptional sets
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM5

variable {f g : ℝ → ℝ}

/-! ## 1. Base-point change of the integrated identity -/

/-- **Chasles' relation in base-point form.**  For `a ≤ u ≤ x ≤ b` and `g` interval integrable on
`[a,b]`, the integral of `g` over `[u,x]` is the difference of the two integrals with common base
point `a`.  This is pure additivity of the interval integral: neither continuity of `g`, nor any
primitive theory, is used. -/
theorem integral_sub_base {a u x : ℝ} (hau : a ≤ u) {b : ℝ} (hxb : x ≤ b) (hux : u ≤ x)
    (hg : IntervalIntegrable g volume a b) :
    ∫ t in u..x, g t = (∫ t in a..x, g t) - (∫ t in a..u, g t) := by
  have hab : a ≤ b := le_trans hau (le_trans hux hxb)
  have hax : IntervalIntegrable g volume a x := by
    refine hg.mono_set ?_
    rw [uIcc_of_le (le_trans hau hux), uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hxb
  have hau' : IntervalIntegrable g volume a u := by
    refine hg.mono_set ?_
    rw [uIcc_of_le hau, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl (le_trans hux hxb)
  exact (intervalIntegral.integral_interval_sub_left hax hau').symm

/-- **Base-point transitivity of the integrated identity.**  If the identity `∫_a^x g = f x - f a`
holds on `[a,b]` and `g` is interval integrable there, then the same identity with the same `f`
holds with any base point `u ∈ [a,b]`.  No continuity of `f` is used. -/
theorem integral_eq_sub_of_base {a u b : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (h : ∀ x ∈ Icc a b, ∫ t in a..x, g t = f x - f a) :
    ∀ x ∈ Icc u b, ∫ t in u..x, g t = f x - f u := by
  intro x hx
  have hxb : x ≤ b := hx.2
  have hux : u ≤ x := hx.1
  have hxab : x ∈ Icc a b := ⟨le_trans hau hux, hxb⟩
  have huab : u ∈ Icc a b := ⟨hau, hub⟩
  rw [integral_sub_base hau hxb hux hg, h x hxab, h u huab]
  ring

/-! ## 2. A continuous function that is locally constant off a finite set is constant -/

/-- **Constancy on an interval from pointwise local constancy at every interior point.**  A
function continuous on `[p,q]` which is locally constant at each point of `(p,q)` is constant on
`[p,q]`.  The open interval is preconnected, so local constancy propagates; the two endpoints
follow from continuity. -/
theorem exists_const_of_localConst {H : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hcont : ContinuousOn H (Icc p q))
    (hlc : ∀ x ∈ Ioo p q, ∀ᶠ y in 𝓝 x, H y = H x) :
    ∃ k, ∀ x ∈ Icc p q, H x = k := by
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact ⟨H p, fun x hx => by rw [Icc_self] at hx; rw [hx]⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m ∈ Ioo p q := ⟨(p + q) / 2, by constructor <;> linarith⟩
  haveI hpc : PreconnectedSpace ↥(Ioo p q) := isPreconnected_iff_preconnectedSpace.mp
    isPreconnected_Ioo
  haveI hnb1 : NeBot (𝓝[Ioo p q] p) := left_nhdsWithin_Ioo_neBot hlt
  haveI hnb2 : NeBot (𝓝[Ioo p q] q) := right_nhdsWithin_Ioo_neBot hlt
  have hLC : IsLocallyConstant fun x : ↥(Ioo p q) => H ↑x := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact ((hlc x x.2).filter_mono nhdsWithin_le_nhds).comap Subtype.val
  have hconst : ∀ x ∈ Ioo p q, H x = H m := fun x hx =>
    hLC.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨m, hm⟩
  have hleft : H p = H m := by
    have h1 : Tendsto H (𝓝[Ioo p q] p) (𝓝 (H p)) :=
      (hcont p ⟨le_rfl, hpq⟩).mono Ioo_subset_Icc_self
    have h2 : Tendsto H (𝓝[Ioo p q] p) (𝓝 (H m)) :=
      tendsto_nhds_of_eventually_eq (eventually_mem_nhdsWithin.mono fun y hy => hconst y hy)
    exact tendsto_nhds_unique h1 h2
  have hright : H q = H m := by
    have h1 : Tendsto H (𝓝[Ioo p q] q) (𝓝 (H q)) :=
      (hcont q ⟨hpq, le_rfl⟩).mono Ioo_subset_Icc_self
    have h2 : Tendsto H (𝓝[Ioo p q] q) (𝓝 (H m)) :=
      tendsto_nhds_of_eventually_eq (eventually_mem_nhdsWithin.mono fun y hy => hconst y hy)
    exact tendsto_nhds_unique h1 h2
  refine ⟨H m, fun x hx => ?_⟩
  rcases lt_or_eq_of_le hx.1 with hpx | hpx
  · rcases lt_or_eq_of_le hx.2 with hxq | hxq
    · exact hconst x ⟨hpx, hxq⟩
    · rw [hxq]; exact hright
  · rw [← hpx]; exact hleft

/-- **Constancy on an interval from local constancy off a finite set.**  A function continuous on
`[A,B]` that is locally constant at every point of `(A,B)` outside a finite set `C` is constant on
`[A,B]`.

The finite set is handled by splitting at its largest element: on the left piece the induction
hypothesis applies, on the right piece no exceptional point is left, so the corner-free case
applies; the two constants agree because both are the value at the splitting point.  No one-sided
limit of `H` at a point of `C` and no value of `H` off `[A,B]` is used. -/
theorem exists_const_of_localConst_off_finite {H : ℝ → ℝ} {A B : ℝ} {C : Set ℝ}
    (hAB : A ≤ B) (hC : C.Finite) (hcont : ContinuousOn H (Icc A B))
    (hlc : ∀ x ∈ Ioo A B, x ∉ C → ∀ᶠ y in 𝓝 x, H y = H x) :
    ∃ k, ∀ x ∈ Icc A B, H x = k := by
  classical
  have key : ∀ D : Finset ℝ, ∀ A B : ℝ, A ≤ B → (∀ d ∈ D, A < d ∧ d < B) →
      (∀ x ∈ Ioo A B, x ∉ (D : Set ℝ) → ∀ᶠ y in 𝓝 x, H y = H x) →
      ContinuousOn H (Icc A B) → ∃ k, ∀ x ∈ Icc A B, H x = k := by
    intro D
    induction D using Finset.induction_on_max with
    | empty =>
        intro A B hAB' _ hlc' hcont'
        exact exists_const_of_localConst hAB' hcont' fun x hx => hlc' x hx (by simp)
    | insert c D' hlt ih =>
        intro A B hAB' hmem hlc' hcont'
        have hc : c ∈ Ioo A B := hmem c (Finset.mem_insert_self c D')
        have hsub1 : Icc A c ⊆ Icc A B := Icc_subset_Icc le_rfl hc.2.le
        obtain ⟨k₁, hk₁⟩ := ih A c hc.1.le
          (fun d hd => ⟨(hmem d (Finset.mem_insert_of_mem hd)).1, hlt d hd⟩)
          (fun x hx hxnot => hlc' x ⟨hx.1, lt_trans hx.2 hc.2⟩ (by
            simp only [Finset.coe_insert, mem_insert_iff, not_or]
            exact ⟨ne_of_lt hx.2, hxnot⟩))
          (hcont'.mono hsub1)
        have hsub2 : Icc c B ⊆ Icc A B := Icc_subset_Icc hc.1.le le_rfl
        obtain ⟨k₂, hk₂⟩ := exists_const_of_localConst hc.2.le (hcont'.mono hsub2)
          (fun x hx => hlc' x ⟨lt_trans hc.1 hx.1, hx.2⟩ (by
            simp only [Finset.coe_insert, mem_insert_iff, not_or]
            exact ⟨ne_of_gt hx.1, fun hd => absurd (hlt x hd) (not_lt.mpr hx.1.le)⟩))
        refine ⟨k₁, fun x hx => ?_⟩
        by_cases hxc : x ≤ c
        · exact hk₁ x ⟨hx.1, hxc⟩
        · have hxc' : x ∈ Icc c B := ⟨(not_le.mp hxc).le, hx.2⟩
          have h2 : H x = k₂ := hk₂ x hxc'
          have hc2 : H c = k₂ := hk₂ c ⟨le_rfl, hc.2.le⟩
          have hc1 : H c = k₁ := hk₁ c ⟨hc.1.le, le_rfl⟩
          rw [h2, ← hc2, hc1]
  have hDfin : (C ∩ Ioo A B).Finite := hC.subset inter_subset_left
  refine key hDfin.toFinset A B hAB ?_ ?_ hcont
  · intro d hd
    have hmem : d ∈ C ∩ Ioo A B := by
      simpa only [Set.Finite.mem_toFinset] using hd
    exact hmem.2
  · intro x hx hxnot
    refine hlc x hx fun hxC => hxnot ?_
    rw [Set.Finite.coe_toFinset]
    exact ⟨hxC, hx⟩

/-! ## 3. The integrated identity from its corner-free instances -/

/-- **The integrated identity on a window from its corner-free instances.**  Let `f : ℝ → ℝ` be
continuous on `[a,b]`, `g` interval integrable on `[a,b]`, and `C` a finite set of exceptional
radii.  If on every corner-free closed subwindow `[u,v] ⊆ [a,b]` (with `u < v`, `a ≤ u`, `v ≤ b`)
the identity `∫_u^x g = f x - f u` holds for all `x ∈ [u,v]`, then the identity holds on the
whole window with one fixed base point: `∫_a^x g = f x - f a` for all `x ∈ [a,b]`.

Neither the value of the identity at an exceptional radius nor a one-sided limit is assumed; the
transfer is via constancy of `x ↦ f x - ∫_a^x g` off the finite set `C`. -/
theorem integral_eq_sub_of_offCorner {C : Set ℝ} {a b : ℝ} (hab : a ≤ b) (hC : C.Finite)
    (hg : IntervalIntegrable g volume a b) (hfcont : ContinuousOn f (Icc a b))
    (hwin : ∀ u v : ℝ, a ≤ u → u < v → v ≤ b → Icc u v ∩ C = ∅ →
      ∀ x ∈ Icc u v, ∫ t in u..x, g t = f x - f u) :
    ∀ x ∈ Icc a b, ∫ t in a..x, g t = f x - f a := by
  set H : ℝ → ℝ := fun x => f x - ∫ t in a..x, g t with hH
  have hprim : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (f := g) (μ := volume)
      (a := a) (b₁ := a) (b₂ := b) hg left_mem_uIcc
    rwa [uIcc_of_le hab] at h
  have hHcont : ContinuousOn H (Icc a b) := by
    rw [hH]
    exact hfcont.sub hprim
  have hlc : ∀ x ∈ Ioo a b, x ∉ C → ∀ᶠ y in 𝓝 x, H y = H x := by
    intro x hx hxC
    obtain ⟨ε, hεpos, hball⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x| < ε → y ∉ C := by
      obtain ⟨ε, hεpos, hb⟩ := Metric.isOpen_iff.mp hC.isClosed.isOpen_compl x hxC
      exact ⟨ε, hεpos, fun y hy => hb (by rw [Metric.mem_ball, Real.dist_eq]; exact hy)⟩
    have hux : max a (x - ε / 2) < x := max_lt hx.1 (by linarith)
    have hxv : x < min b (x + ε / 2) := lt_min hx.2 (by linarith)
    have huv : max a (x - ε / 2) < min b (x + ε / 2) := lt_of_lt_of_le hux hxv.le
    have hgb : max a (x - ε / 2) ≤ b := le_trans huv.le (min_le_left b (x + ε / 2))
    have hdisj : Icc (max a (x - ε / 2)) (min b (x + ε / 2)) ∩ C = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro y ⟨hy, hyC⟩
      exact absurd hyC (hball y (by
        have hy1 : x - ε / 2 ≤ y := le_trans (le_max_right a (x - ε / 2)) hy.1
        have hy2 : y ≤ x + ε / 2 := le_trans hy.2 (min_le_right b (x + ε / 2))
        rw [abs_lt]
        constructor <;> linarith))
    have hval : ∀ y ∈ Icc (max a (x - ε / 2)) (min b (x + ε / 2)),
        H y = H (max a (x - ε / 2)) := by
      intro y hy
      have hyb : y ≤ b := le_trans hy.2 (min_le_left b (x + ε / 2))
      have h1 : IntervalIntegrable g volume a (max a (x - ε / 2)) := by
        refine hg.mono_set ?_
        rw [uIcc_of_le (le_max_left a (x - ε / 2)), uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl hgb
      have h2 : IntervalIntegrable g volume (max a (x - ε / 2)) y := by
        refine hg.mono_set ?_
        rw [uIcc_of_le hy.1, uIcc_of_le hab]
        exact Icc_subset_Icc (le_max_left a (x - ε / 2)) hyb
      have hCh : (∫ t in a..y, g t) = (∫ t in a..max a (x - ε / 2), g t)
          + ∫ t in max a (x - ε / 2)..y, g t :=
        (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
      have hid := hwin (max a (x - ε / 2)) (min b (x + ε / 2)) (le_max_left a (x - ε / 2))
        huv (min_le_left b (x + ε / 2)) hdisj y hy
      simp only [hH]
      rw [hCh, hid]
      ring
    have hHx : H x = H (max a (x - ε / 2)) := hval x ⟨hux.le, hxv.le⟩
    filter_upwards [Icc_mem_nhds hux hxv] with y hy
    rw [hval y hy, hHx]
  obtain ⟨k, hk⟩ := exists_const_of_localConst_off_finite hab hC hHcont hlc
  intro x hx
  have h1 : H x = H a := by rw [hk x hx, hk a ⟨le_rfl, hab⟩]
  simp only [hH, intervalIntegral.integral_same, sub_zero] at h1
  linarith

end PercLib.CriticalLRP.Orchestration.SmwywszgoM5


/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_sub_base
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_eq_sub_of_base
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.exists_const_of_localConst
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.exists_const_of_localConst_off_finite
#print axioms PercLib.CriticalLRP.Orchestration.SmwywszgoM5.integral_eq_sub_of_offCorner
