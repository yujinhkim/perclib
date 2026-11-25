/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Square-root factorization entails open-triangle tail decay

Accepted from independent submission `smwp648b3` direction D2.  The missing
construction of the square root from the triangle condition is not supplied.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Kozma's analytic step: `ℓ²` vectors are asymptotically orthogonal to far translations

This file supplies the analytic heart of G. Kozma, *The triangle and the open triangle*
(Ann. IHP Probab. Stat. 47 (2011) 75--79, arXiv:0907.1959), §2:

  "`Q(v,w) = ⟨S 1_v, S 1_w⟩` ... `S` is invariant to the automorphisms of `G` ... so
   `S 1_w` is a map of `S 1_v` under an automorphism `φ` taking `v` to `w`. But any vector in
   `ℓ²` is almost orthogonal to sufficiently far away 'translations' ... so
   `⟨S 1_v, S 1_w⟩ → 0` as the graph distance of `v` and `w` goes to `∞`."

The italic statement is `exists_linfNorm_tsum_mul_shift_le` below, proved here in full for
`ℤ^d` with the sup-norm: for `ξ ∈ ℓ²(ℤ^d)` (i.e. `∑ ξ²` summable) the "autocorrelation"
`⟨ξ, T_x ξ⟩ = ∑_y ξ y ξ(y-x)` is uniformly small on `‖x‖ ≥ N`.

The proof is elementary and uses only `ℓ² ⊂ c₀`, Cauchy--Schwarz on a finite set, and the
AM--GM inequality on the complement; no spectral theory is needed *once the `ℓ²` vector `ξ`
is given*.

`openTriangleTail_tendsto_of_sqrtKernel` then transports this to the configured kernel: if the
open triangle is the Gram matrix of such a vector, `∇(0,x) = ⟨ξ, T_x ξ⟩`, then `∇_r → 0`.

No `sorry`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.DiagramAssembly
public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging
public import PercLib.CriticalLRP.Analysis.TriTail

@[expose] public section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal Topology
open Filter

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-! ### `ℓ² ⊂ c₀` with the lattice sup-norm -/

/-- **`ℓ²` sequences on `ℤ^d` vanish at infinity**: for `∑ ξ² < ∞` and `ε > 0` there is `N` with
`|ξ y| ≤ ε` for every `‖y‖_∞ ≥ N`. (The sup-norm threshold is what the tail `∇_r` needs.) -/
theorem exists_linfNorm_le_of_summable_sq {ξ : (Fin d → ℤ) → ℝ}
    (hξ : Summable fun y => ξ y ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ y : Fin d → ℤ, N ≤ FiniteVolume.linfNorm y → |ξ y| ≤ ε := by
  have h0 : Tendsto (fun y : Fin d → ℤ => ξ y ^ 2) cofinite (𝓝 0) := hξ.tendsto_cofinite_zero
  have hcont : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto (0 : ℝ)
  have hsq : Tendsto (fun y : Fin d → ℤ => Real.sqrt (ξ y ^ 2)) cofinite (𝓝 0) :=
    hcont.comp h0
  have habs : Tendsto (fun y : Fin d → ℤ => |ξ y|) cofinite (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs] using hsq
  have hξ0 : Tendsto ξ cofinite (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero ξ).mpr habs
  have hev : ∀ᶠ y : Fin d → ℤ in cofinite, |ξ y| < ε := by
    have h := (Metric.tendsto_nhds.1 hξ0) ε hε
    simpa [Real.dist_eq] using h
  have hfin : {y : Fin d → ℤ | ε ≤ |ξ y|}.Finite := by
    have h := eventually_cofinite.1 hev
    simpa only [not_lt] using h
  refine ⟨hfin.toFinset.sum FiniteVolume.linfNorm + 1, fun y hy => ?_⟩
  by_contra hcon
  have hyS : y ∈ {y : Fin d → ℤ | ε ≤ |ξ y|} := by
    simp only [Set.mem_ofPred_eq]
    exact le_of_lt (not_le.1 hcon)
  have hmem : y ∈ hfin.toFinset := hfin.mem_toFinset.mpr hyS
  have hle : FiniteVolume.linfNorm y ≤ hfin.toFinset.sum FiniteVolume.linfNorm :=
    Finset.single_le_sum (f := FiniteVolume.linfNorm) (fun i _ => Nat.zero_le _) hmem
  omega

/-- **The near part of the correlation vanishes**: for a fixed finite `F` and any `s > 0`, once
`‖x‖_∞` is large the whole sum `∑_{y ∈ F} ξ(y-x)²` is at most `s²`. This is where `ξ ∈ c₀` is
consumed (`ℓ²` only enters through `ξ → 0`). -/
theorem exists_linfNorm_le_finset_sum_sq {ξ : (Fin d → ℤ) → ℝ}
    (hξ : Summable fun y => ξ y ^ 2) (F : Finset (Fin d → ℤ)) {s : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, ∀ x : Fin d → ℤ, N ≤ FiniteVolume.linfNorm x →
      ∑ y ∈ F, ξ (y - x) ^ 2 ≤ s ^ 2 := by
  set b : ℝ := s / (Real.sqrt (F.card : ℝ) + 1) with hb
  have hden : (0 : ℝ) < Real.sqrt (F.card : ℝ) + 1 := by positivity
  have hbpos : 0 < b := div_pos hs hden
  obtain ⟨N₀, hN₀⟩ := exists_linfNorm_le_of_summable_sq hξ hbpos
  refine ⟨N₀ + ∑ y ∈ F, FiniteVolume.linfNorm y, fun x hx => ?_⟩
  have hcard : (F.card : ℝ) ≤ (Real.sqrt (F.card : ℝ) + 1) ^ 2 := by
    have h1 : Real.sqrt (F.card : ℝ) ^ 2 = (F.card : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg F.card)
    nlinarith [Real.sqrt_nonneg (F.card : ℝ)]
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hbound : ∀ y ∈ F, ξ (y - x) ^ 2 ≤ b ^ 2 := by
    intro y hyF
    have h1 : FiniteVolume.linfNorm y ≤ ∑ z ∈ F, FiniteVolume.linfNorm z :=
      Finset.single_le_sum (f := FiniteVolume.linfNorm) (fun i _ => Nat.zero_le _) hyF
    have h3 : FiniteVolume.linfNorm x ≤
        FiniteVolume.linfNorm (x - y) + FiniteVolume.linfNorm y := by
      have h := Percolation.linfNorm_add_le (x - y) y
      simpa using h
    have h4 : FiniteVolume.linfNorm (x - y) = FiniteVolume.linfNorm (y - x) := by
      have h : y - x = -(x - y) := by abel
      rw [h, FiniteVolume.linfNorm_neg]
    have h2 : N₀ ≤ FiniteVolume.linfNorm (y - x) := by omega
    have h5 : |ξ (y - x)| ≤ b := hN₀ (y - x) h2
    nlinarith [h5, abs_nonneg (ξ (y - x)), sq_abs (ξ (y - x))]
  calc ∑ y ∈ F, ξ (y - x) ^ 2 ≤ ∑ _y ∈ F, b ^ 2 := Finset.sum_le_sum hbound
    _ = (F.card : ℝ) * b ^ 2 := by simp
    _ ≤ (Real.sqrt (F.card : ℝ) + 1) ^ 2 * b ^ 2 := by nlinarith
    _ = s ^ 2 := by
        rw [hb]
        field_simp


/-! ### Summability of finitely supported families -/

/-- A family vanishing off a fixed finite set is summable. -/
theorem summable_ite_finset (F : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → ℝ) :
    Summable (fun y : Fin d → ℤ => if y ∈ F then g y else 0) := by
  have h : HasSum (fun y : Fin d → ℤ => if y ∈ F then g y else 0) (∑ y ∈ F, g y) := by
    show Tendsto (fun s : Finset (Fin d → ℤ) => ∑ y ∈ s, (if y ∈ F then g y else 0))
      atTop (𝓝 (∑ y ∈ F, g y))
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_atTop.2 ⟨F, fun s hs => hs⟩] with s hs
    calc ∑ y ∈ s, (if y ∈ F then g y else 0)
        = ∑ y ∈ F, (if y ∈ F then g y else 0) :=
          (Finset.sum_subset (s₂ := s) hs (fun y _ hyF => by rw [ite_eq_right hyF])).symm
      _ = ∑ y ∈ F, g y := Finset.sum_congr rfl (fun y hy => by rw [ite_eq_left hy])
  exact h.summable

/-- **The complement of a finite set carries at most `s²` of the `ℓ²` mass.** -/
theorem exists_finset_tsum_ite_le {ξ : (Fin d → ℤ) → ℝ}
    (hξ : Summable fun y => ξ y ^ 2) {s : ℝ} (hs : 0 < s) :
    ∃ F : Finset (Fin d → ℤ), ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2) ≤ s ^ 2 := by
  obtain ⟨F, hF⟩ := eventually_atTop.1
    ((Metric.tendsto_nhds.1 hξ.hasSum) (s ^ 2) (by positivity))
  refine ⟨F, ?_⟩
  have hdist : dist (∑ y ∈ F, ξ y ^ 2) (∑' y : Fin d → ℤ, ξ y ^ 2) < s ^ 2 := hF F le_rfl
  rw [Real.dist_eq] at hdist
  have hle : ∑ y ∈ F, ξ y ^ 2 ≤ ∑' y : Fin d → ℤ, ξ y ^ 2 :=
    Summable.sum_le_tsum F (fun i _ => sq_nonneg _) hξ
  have h1 : Summable (fun y : Fin d → ℤ => if y ∈ F then ξ y ^ 2 else 0) :=
    summable_ite_finset F _
  have h2 : Summable (fun y : Fin d → ℤ => if y ∈ F then 0 else ξ y ^ 2) := by
    refine (hξ.sub h1).congr (fun y => ?_)
    by_cases hy : y ∈ F <;> simp [hy]
  have hsplit : (∑' y : Fin d → ℤ, ξ y ^ 2)
      = (∑' y : Fin d → ℤ, (if y ∈ F then ξ y ^ 2 else 0))
        + ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2) := by
    rw [← Summable.tsum_add h1 h2]
    exact tsum_congr (fun y => by by_cases hy : y ∈ F <;> simp [hy])
  have hfin : (∑' y : Fin d → ℤ, (if y ∈ F then ξ y ^ 2 else 0)) = ∑ y ∈ F, ξ y ^ 2 := by
    rw [tsum_eq_sum (f := fun y : Fin d → ℤ => if y ∈ F then ξ y ^ 2 else 0)
      (fun y hy => by rw [ite_eq_right hy])]
    exact Finset.sum_congr rfl (fun y hy => by rw [ite_eq_left hy])
  have hge : (∑' y : Fin d → ℤ, ξ y ^ 2) - s ^ 2 < ∑ y ∈ F, ξ y ^ 2 := by
    have := abs_lt.1 hdist
    linarith [this.1]
  linarith [hsplit, hfin]

/-- **The shifted far mass is bounded by the total mass**: `∑_{y∉F} ξ(y-x)² ≤ ∑ ξ²`. -/
theorem tsum_ite_shift_le {ξ : (Fin d → ℤ) → ℝ} (hξ : Summable fun y => ξ y ^ 2)
    (F : Finset (Fin d → ℤ)) (x : Fin d → ℤ) :
    ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ (y - x) ^ 2)
      ≤ ∑' y : Fin d → ℤ, ξ y ^ 2 := by
  have hshift : Summable (fun y : Fin d → ℤ => ξ (y - x) ^ 2) := by
    have h := (Equiv.summable_iff (f := fun y : Fin d → ℤ => ξ y ^ 2)
      (Equiv.subRight x)).mpr hξ
    simpa [Equiv.subRight_apply, Function.comp_def] using h
  have h1 : Summable (fun y : Fin d → ℤ => if y ∈ F then ξ (y - x) ^ 2 else 0) :=
    summable_ite_finset F _
  have h2 : Summable (fun y : Fin d → ℤ => if y ∈ F then 0 else ξ (y - x) ^ 2) := by
    refine (hshift.sub h1).congr (fun y => ?_)
    by_cases hy : y ∈ F <;> simp [hy]
  set g : (Fin d → ℤ) → ℝ := fun y => if y ∈ F then 0 else ξ (y - x) ^ 2 with hg
  have h2' : Summable (fun c : Fin d → ℤ => g ((Equiv.addRight x) c)) :=
    (Equiv.summable_iff (f := g) (Equiv.addRight x)).mpr h2
  have e1 : (∑' y : Fin d → ℤ, g y) = ∑' c : Fin d → ℤ, g ((Equiv.addRight x) c) :=
    (Equiv.tsum_eq (Equiv.addRight x) g).symm
  rw [e1]
  refine Summable.tsum_le_tsum (fun c => ?_) h2' hξ
  simp only [hg, Equiv.coe_addRight, add_sub_cancel_right]
  by_cases hc : c + x ∈ F
  · simpa [hc] using sq_nonneg (ξ c)
  · simp [hc]


/-! ### The analytic heart of Kozma's theorem -/

/-- **`ℓ²` vectors are asymptotically orthogonal to far translations** (Kozma 2011, §2:
"any vector in `ℓ²` is almost orthogonal to sufficiently far away translations"). For
`∑ ξ² < ∞` and any `ε > 0`, the autocorrelation `⟨ξ, T_x ξ⟩ = ∑_y ξ y · ξ(y-x)` is at most `ε`
in absolute value once `‖x‖_∞ ≥ N`.

The split is: the finite window `F` (where `ξ → 0` because `ℓ² ⊂ c₀`) versus its complement
(where the AM--GM inequality with the optimised weight `t = √M / s` uses only that the far `ℓ²`
mass is at most `s²` and the shifted far mass is at most the total `M = ∑ ξ²`). -/
theorem exists_linfNorm_tsum_mul_shift_le {ξ : (Fin d → ℤ) → ℝ}
    (hξ : Summable fun y => ξ y ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : Fin d → ℤ, N ≤ FiniteVolume.linfNorm x →
      |∑' y : Fin d → ℤ, ξ y * ξ (y - x)| ≤ ε := by
  set M : ℝ := ∑' y : Fin d → ℤ, ξ y ^ 2 with hM
  have hM0 : 0 ≤ M := tsum_nonneg (fun y => sq_nonneg _)
  rcases eq_or_lt_of_le hM0 with hMzero | hMpos
  · have hzero : ∀ y : Fin d → ℤ, ξ y = 0 := by
      intro y
      have h1 : ξ y ^ 2 ≤ M := by
        rw [hM]
        simpa using Summable.sum_le_tsum {y} (fun i _ => sq_nonneg (ξ i)) hξ
      rw [← hMzero] at h1
      nlinarith [sq_nonneg (ξ y)]
    refine ⟨0, fun x _ => ?_⟩
    have hc : (∑' y : Fin d → ℤ, ξ y * ξ (y - x)) = 0 := by
      rw [show (fun y : Fin d → ℤ => ξ y * ξ (y - x)) = fun _ => 0 from
        funext (fun y => by rw [hzero y, zero_mul])]
      simp
    rw [hc, abs_zero]
    exact le_of_lt hε
  · have hc : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
    set s : ℝ := ε / (2 * (Real.sqrt M + 1)) with hs
    have hspos : 0 < s := by rw [hs]; positivity
    have hden : (0 : ℝ) < Real.sqrt M + 1 := by positivity
    have hcs : 2 * Real.sqrt M * s ≤ ε := by
      have h2 : 2 * Real.sqrt M * s = ε * (Real.sqrt M / (Real.sqrt M + 1)) := by
        rw [hs]; field_simp
      have h3 : Real.sqrt M / (Real.sqrt M + 1) ≤ 1 := by
        rw [div_le_one hden]; linarith [Real.sqrt_nonneg M]
      calc 2 * Real.sqrt M * s = ε * (Real.sqrt M / (Real.sqrt M + 1)) := h2
        _ ≤ ε * 1 := by
            exact mul_le_mul_of_nonneg_left h3 (le_of_lt hε)
        _ = ε := mul_one ε
    obtain ⟨F, hF⟩ := exists_finset_tsum_ite_le hξ hspos
    obtain ⟨N, hN⟩ := exists_linfNorm_le_finset_sum_sq hξ F hspos
    refine ⟨N, fun x hx => ?_⟩
    have hshift : Summable (fun y : Fin d → ℤ => ξ (y - x) ^ 2) := by
      have h := (Equiv.summable_iff (f := fun y : Fin d → ℤ => ξ y ^ 2)
        (Equiv.subRight x)).mpr hξ
      simpa [Equiv.subRight_apply, Function.comp_def] using h
    have hprod : Summable (fun y : Fin d → ℤ => ξ y * ξ (y - x)) := by
      refine Summable.of_norm_bounded (g := fun y : Fin d → ℤ =>
        (ξ y ^ 2 + ξ (y - x) ^ 2) / 2) ?_ (fun y => ?_)
      · have h := (hξ.add hshift).div_const 2
        simpa [add_div] using h
      · rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|ξ y| - |ξ (y - x)|), sq_abs (ξ y), sq_abs (ξ (y - x))]
    -- the finite-window part
    have hfin_prod : (∑' y : Fin d → ℤ, (if y ∈ F then ξ y * ξ (y - x) else 0))
        = ∑ y ∈ F, ξ y * ξ (y - x) := by
      rw [tsum_eq_sum (f := fun y : Fin d → ℤ => if y ∈ F then ξ y * ξ (y - x) else 0)
        (fun y hy => by rw [ite_eq_right hy])]
      exact Finset.sum_congr rfl (fun y hy => by rw [ite_eq_left hy])
    have h1f : Summable (fun y : Fin d → ℤ => if y ∈ F then ξ y * ξ (y - x) else 0) :=
      summable_ite_finset F _
    have h2f : Summable (fun y : Fin d → ℤ => if y ∈ F then 0 else ξ y * ξ (y - x)) := by
      refine (hprod.sub h1f).congr (fun y => ?_)
      by_cases hy : y ∈ F <;> simp [hy]
    have hkey : (∑' y : Fin d → ℤ, ξ y * ξ (y - x))
        = (∑' y : Fin d → ℤ, (if y ∈ F then ξ y * ξ (y - x) else 0))
          + ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y * ξ (y - x)) := by
      rw [← Summable.tsum_add h1f h2f]
      exact tsum_congr (fun y => by by_cases hy : y ∈ F <;> simp [hy])
    rw [hkey, hfin_prod]
    -- bound on the finite-window part
    have hnear : |∑ y ∈ F, ξ y * ξ (y - x)| ≤ Real.sqrt M * s := by
      refine abs_le_of_sq_le_sq ?_ (by positivity)
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq F (fun y : Fin d → ℤ => ξ y)
        (fun y : Fin d → ℤ => ξ (y - x))
      have h2 : ∑ y ∈ F, ξ y ^ 2 ≤ M := by
        rw [hM]; exact Summable.sum_le_tsum F (fun i _ => sq_nonneg _) hξ
      have h3 : ∑ y ∈ F, ξ (y - x) ^ 2 ≤ s ^ 2 := hN x hx
      calc (∑ y ∈ F, ξ y * ξ (y - x)) ^ 2
          ≤ (∑ y ∈ F, ξ y ^ 2) * ∑ y ∈ F, ξ (y - x) ^ 2 := h1
        _ ≤ M * s ^ 2 := mul_le_mul h2 h3 (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hM0
        _ = (Real.sqrt M * s) ^ 2 := by rw [mul_pow, Real.sq_sqrt hM0]
    -- bound on the far part via AM--GM with the optimised weight
    set t : ℝ := Real.sqrt M / s with ht
    have htpos : 0 < t := div_pos hc hspos
    have hg1 : Summable (fun y : Fin d → ℤ => if y ∈ F then 0 else ξ y ^ 2) := by
      refine (hξ.sub (summable_ite_finset F (fun y => ξ y ^ 2))).congr (fun y => ?_)
      by_cases hy : y ∈ F <;> simp [hy]
    have hg2 : Summable (fun y : Fin d → ℤ => if y ∈ F then 0 else ξ (y - x) ^ 2) := by
      refine (hshift.sub (summable_ite_finset F (fun y => ξ (y - x) ^ 2))).congr (fun y => ?_)
      by_cases hy : y ∈ F <;> simp [hy]
    have hbndsumm : Summable (fun y : Fin d → ℤ =>
        t * (if y ∈ F then 0 else ξ y ^ 2) + (1 / t) * (if y ∈ F then 0 else ξ (y - x) ^ 2)) :=
      ((hg1.mul_left t).add (hg2.mul_left (1 / t)))
    have hpt : ∀ y : Fin d → ℤ,
        2 * ‖(if y ∈ F then 0 else ξ y * ξ (y - x))‖ ≤
          t * (if y ∈ F then 0 else ξ y ^ 2) + (1 / t) * (if y ∈ F then 0 else ξ (y - x) ^ 2) := by
      intro y
      by_cases hy : y ∈ F
      · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left hy]
        simp
      · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy, Real.norm_eq_abs, abs_mul]
        have hsq : 0 ≤ (t * |ξ y| - |ξ (y - x)|) ^ 2 := sq_nonneg _
        rw [sub_sq, mul_pow, sq_abs, sq_abs] at hsq
        have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
        have h2 : 2 * (|ξ y| * |ξ (y - x)|) ≤ t * ξ y ^ 2 + 1 / t * ξ (y - x) ^ 2 := by
          have hle : 2 * (|ξ y| * |ξ (y - x)|) * t ≤ t ^ 2 * ξ y ^ 2 + ξ (y - x) ^ 2 := by
            nlinarith [hsq]
          have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.2 htpos))
          field_simp at hmul ⊢
          linarith [hmul]
        linarith [h2]
    have hsum_le : 2 * ∑' y : Fin d → ℤ, ‖(if y ∈ F then 0 else ξ y * ξ (y - x))‖
        ≤ t * (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2))
          + (1 / t) * ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ (y - x) ^ 2) := by
      have h := Summable.tsum_le_tsum hpt ((h2f.norm).mul_left 2) hbndsumm
      rw [tsum_mul_left, Summable.tsum_add (hg1.mul_left t) (hg2.mul_left (1 / t)),
        tsum_mul_left, tsum_mul_left] at h
      exact h
    have hT1 : (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2)) ≤ s ^ 2 := hF
    have hT2 : (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ (y - x) ^ 2)) ≤ M := by
      rw [hM]; exact tsum_ite_shift_le hξ F x
    have htval : t * s ^ 2 + (1 / t) * M = 2 * Real.sqrt M * s := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hcne : Real.sqrt M ≠ 0 := ne_of_gt hc
      have hMval : M = Real.sqrt M * Real.sqrt M := by
        rw [Real.mul_self_sqrt hM0]
      rw [ht, hMval]
      field_simp
      rw [Real.sqrt_sq (Real.sqrt_nonneg M)]
      ring
    have hfar : |∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y * ξ (y - x))| ≤ Real.sqrt M * s := by
      have hb : ‖∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y * ξ (y - x))‖
          ≤ ∑' y : Fin d → ℤ, ‖(if y ∈ F then 0 else ξ y * ξ (y - x))‖ :=
        norm_tsum_le_tsum_norm h2f.norm
      have hsum2 : ∑' y : Fin d → ℤ, ‖(if y ∈ F then 0 else ξ y * ξ (y - x))‖
          ≤ Real.sqrt M * s := by
        have hle : t * (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2))
            + (1 / t) * (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ (y - x) ^ 2))
            ≤ 2 * Real.sqrt M * s := by
          have h1 : t * (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y ^ 2)) ≤ t * s ^ 2 :=
            mul_le_mul_of_nonneg_left hT1 (le_of_lt htpos)
          have h2 : (1 / t) * (∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ (y - x) ^ 2))
              ≤ (1 / t) * M := mul_le_mul_of_nonneg_left hT2 (by positivity)
          linarith [htval]
        linarith [hsum_le]
      rw [← Real.norm_eq_abs]
      linarith [hb, hsum2]
    have h2 : |∑' y : Fin d → ℤ, (if y ∈ F then ξ y * ξ (y - x) else 0)| ≤ Real.sqrt M * s := by
      rw [hfin_prod]; exact hnear
    calc |∑ y ∈ F, ξ y * ξ (y - x)
          + ∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y * ξ (y - x))|
        ≤ |∑ y ∈ F, ξ y * ξ (y - x)|
          + |∑' y : Fin d → ℤ, (if y ∈ F then 0 else ξ y * ξ (y - x))| := abs_add_le _ _
      _ ≤ Real.sqrt M * s + Real.sqrt M * s := add_le_add hnear hfar
      _ = 2 * Real.sqrt M * s := by ring
      _ ≤ ε := hcs


/-! ### Kozma's reduction at the configured kernel -/

/-- **Kozma's reduction.** If the open triangle at the configured kernel is the Gram matrix of an
`ℓ²` vector `ξ` under translations, `∇(0,x) = ⟨ξ, T_x ξ⟩ = ∑_y ξ y ξ(y-x)` (Kozma's
`Q(v,w) = ⟨S 1_v, S 1_w⟩` with `ξ = S 1_0`), then the open-triangle tail satisfies `∇_r → 0`.

The hypothesis `hfac` is exactly the operator-theoretic input of Kozma (2011), §2: the square root
of the positive operator `B³` applied to `1_0`, plus its invariance under translations. It is an
explicit, checkable hypothesis, not a silent assumption; `REPORT.md` records it as the remaining
upstream input. -/
theorem openTriangleTail_tendsto_of_sqrtKernel {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} {ξ : (Fin d → ℤ) → ℝ} (hξ : Summable fun y => ξ y ^ 2)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal (∑' y : Fin d → ℤ, ξ y * ξ (y - x))) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  rw [tendsto_openTriangleTail_iff]
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨0, fun x _ => ?_⟩
    rw [htop]
    exact le_top
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
    obtain ⟨N, hN⟩ := exists_linfNorm_tsum_mul_shift_le (d := d) hξ
      (show (0 : ℝ) < ε.toReal / 2 by linarith)
    refine ⟨(N : ℝ), fun x hx => ?_⟩
    have hNx : N ≤ FiniteVolume.linfNorm x := by
      have h3 : FiniteVolume.latticeDist (d := d) 0 x = (FiniteVolume.linfNorm x : ℝ) := by
        rw [Percolation.latticeDist_eq_linfNorm]
        simp
      rw [h3] at hx
      exact_mod_cast hx
    have h1 : |∑' y : Fin d → ℤ, ξ y * ξ (y - x)| ≤ ε.toReal / 2 := hN x hNx
    have h2 : ∑' y : Fin d → ℤ, ξ y * ξ (y - x) ≤ ε.toReal := by
      have := (abs_le.1 h1).2
      linarith
    rw [hfac x]
    calc ENNReal.ofReal (∑' y : Fin d → ℤ, ξ y * ξ (y - x))
        ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal h2
      _ = ε := ENNReal.ofReal_toReal htop


/-! ### Consistency of the input, and the form the §I.4.18 consumers use -/

/-- **The square-root input entails the triangle condition**: under `hfac`,
`∇_{β_c} = ∇(0,0) = ∑_y ξ y ξ y = ‖ξ‖²₂ < ∞`. So the hypothesis is not an assumption of anything
stronger than the triangle condition — it is precisely the `Δ < ∞` regime, as in Kozma (2011)
(`Q(v,v) < ∞` iff `S 1_v ∈ ℓ²`). -/
theorem openTriangleSelf_lt_top_of_sqrtKernel {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} {ξ : (Fin d → ℤ) → ℝ}
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal (∑' y : Fin d → ℤ, ξ y * ξ (y - x))) :
    openTriangleSelf J hJ β 0 < ⊤ := by
  have h0 : openTriangleSelf J hJ β 0
      = ENNReal.ofReal (∑' y : Fin d → ℤ, ξ y * ξ (y - 0)) := hfac 0
  rw [h0]
  exact ENNReal.ofReal_lt_top

/-- **Composition with a diverging radius**, the form in which the §I.4.18 consumers use the tail:
`∇_{φ(r)} → 0` for any `φ(r) → ∞` (e.g. `φ r = r ^ c` or `φ r = r ^ θ`). -/
theorem tendsto_openTriangleTail_comp {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} (h : Tendsto (openTriangleTail J hJ β) atTop (𝓝 0)) {φ : ℝ → ℝ}
    (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun r => openTriangleTail J hJ β (φ r)) atTop (𝓝 0) := h.comp hφ

/-- `r ↦ r ^ c` diverges for `c > 0`, so `∇_{r^c} → 0`. -/
theorem tendsto_openTriangleTail_rpow {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} (h : Tendsto (openTriangleTail J hJ β) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => openTriangleTail J hJ β (r ^ c)) atTop (𝓝 0) :=
  h.comp (tendsto_rpow_atTop hc)


/-- **Unrolled consumer form**: if `∇_r → 0` then for every `ε > 0` and every `c > 0` the bound
`∇_{r^c} ≤ ε` holds for all sufficiently large `r`. This is the exact shape in which the §I.4.18
consumers use `tri.tail` ("`∇_{r^c}` and `r^{-c}` are small", "`∇_{r^θ} → 0` makes the replacement
small"). -/
theorem eventually_openTriangleTail_rpow_le {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} (h : Tendsto (openTriangleTail J hJ β) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, openTriangleTail J hJ β (r ^ c) ≤ ε :=
  (ENNReal.tendsto_nhds_zero.1 (tendsto_openTriangleTail_rpow h hc)) ε hε

end PercLib.CriticalLRP.TriTail

#print axioms PercLib.CriticalLRP.TriTail.exists_linfNorm_tsum_mul_shift_le
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_sqrtKernel
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_sqrtKernel
#print axioms PercLib.CriticalLRP.TriTail.tendsto_openTriangleTail_rpow
#print axioms PercLib.CriticalLRP.TriTail.eventually_openTriangleTail_rpow_le
