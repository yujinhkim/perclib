/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Monotonicity of finite Bernoulli percolation probabilities in the edge probabilities:
if `p ≤ q` pointwise then `P_p(A) ≤ P_q(A)` for every increasing event `A`. This is the
stochastic domination used throughout Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1 (p. 7: "`J_r(x,y) ≤ (1−ε)J(x,y)` for every `x ≠ y`, so that `P_{β_c,r}` is
stochastically dominated by the subcritical measure `P_{(1−ε)β_c}`"; and the definition of
`β_c` on p. 6 uses monotonicity of `β ↦ P_β`).

The proof is an induction on the set of active edges, conditioning one coordinate at a time;
no coupling theory or calculus is needed.
-/
module

public import PercLib.CriticalLRP.TreeGraph.ThreePoint

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset
open Classical

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The product law of the edges in `S`, evaluated on a configuration `s`. -/
def lawOn (p : E → ℝ) (S : Finset E) (s : Finset E) : ℝ :=
  ∏ e ∈ S, if e ∈ s then p e else 1 - p e

theorem lawOn_univ (p : E → ℝ) (s : Finset E) :
    lawOn p univ s = PercLib.CriticalLRP.configurationLaw p s := rfl

theorem lawOn_nonneg {p : E → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (S s : Finset E) : 0 ≤ lawOn p S s := by
  refine Finset.prod_nonneg fun e _ => ?_
  by_cases h : e ∈ s <;> simp [h, hp0 e, sub_nonneg.mpr (hp1 e)]

/-- Probability computed on the edge set `S`, summing over sub-configurations of `S`. -/
def probS (p : E → ℝ) (S : Finset E) (A : Set (Finset E)) : ℝ :=
  ∑ s ∈ S.powerset, lawOn p S s * (if s ∈ A then 1 else 0)

theorem probS_univ (p : E → ℝ) (A : Set (Finset E)) : probS p univ A = prob p A := by
  classical
  simp only [probS, prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation,
    Finset.powerset_univ, lawOn_univ]

theorem probS_empty (p : E → ℝ) (A : Set (Finset E)) :
    probS p ∅ A = (if (∅ : Finset E) ∈ A then 1 else 0) := by
  classical
  rw [probS, Finset.powerset_empty, Finset.sum_singleton, lawOn, Finset.prod_empty, one_mul]

/-- Conditioning on the last coordinate. -/
theorem probS_insert {p : E → ℝ} {e : E} {S : Finset E} (he : e ∉ S)
    (A : Set (Finset E)) :
    probS p (insert e S) A
      = (1 - p e) * probS p S A + p e * probS p S {s | insert e s ∈ A} := by
  classical
  have hlaw1 : ∀ t ∈ S.powerset, e ∉ t := fun t ht => fun h => he (Finset.mem_powerset.mp ht h)
  have h1 : ∀ t ∈ S.powerset,
      lawOn p (insert e S) (insert e t) = p e * lawOn p S t := by
    intro t ht
    have het : e ∉ t := hlaw1 t ht
    simp only [lawOn, Finset.prod_insert he]
    rw [ite_eq_left (Finset.mem_insert_self e t)]
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxe : x ≠ e := fun h => he (h ▸ hx)
    simp only [Finset.mem_insert, hxe, false_or]
  have h2 : ∀ t ∈ S.powerset,
      lawOn p (insert e S) t = (1 - p e) * lawOn p S t := by
    intro t ht
    have het : e ∉ t := hlaw1 t ht
    simp only [lawOn, Finset.prod_insert he]
    rw [ite_eq_right (by simp [het])]
  have hL : probS p (insert e S) A
      = (∑ t ∈ S.powerset, lawOn p (insert e S) t * (if t ∈ A then 1 else 0))
        + ∑ t ∈ S.powerset,
            lawOn p (insert e S) (insert e t) * (if insert e t ∈ A then 1 else 0) := by
    rw [probS, Finset.sum_powerset_insert he]
  have e1 : (∑ t ∈ S.powerset, lawOn p (insert e S) t * (if t ∈ A then 1 else 0))
      = ∑ t ∈ S.powerset, (1 - p e) * lawOn p S t * (if t ∈ A then 1 else 0) :=
    Finset.sum_congr rfl fun t ht => by rw [h2 t ht]
  have e2 : (∑ t ∈ S.powerset,
        lawOn p (insert e S) (insert e t) * (if insert e t ∈ A then 1 else 0))
      = ∑ t ∈ S.powerset, p e * lawOn p S t * (if insert e t ∈ A then 1 else 0) :=
    Finset.sum_congr rfl fun t ht => by rw [h1 t ht]
  rw [hL, e1, e2, probS, probS, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]
  rfl

theorem probS_mono_event {p : E → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {A B : Set (Finset E)} (hAB : A ⊆ B) (S : Finset E) : probS p S A ≤ probS p S B := by
  classical
  refine Finset.sum_le_sum fun s _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (lawOn_nonneg hp0 hp1 S s)
  by_cases hs : s ∈ A
  · rw [ite_eq_left hs, ite_eq_left (hAB hs)]
  · by_cases hs' : s ∈ B <;> simp [hs, hs']

/-- **Monotonicity in the edge probabilities.** If `p ≤ q` pointwise (and both have values in
`[0,1]`) then every increasing event has larger probability under `q`. -/
theorem probS_mono {p q : E → ℝ} (hpq : ∀ e, p e ≤ q e) (hp0 : ∀ e, 0 ≤ p e)
    (hq1 : ∀ e, q e ≤ 1) :
    ∀ (A : Set (Finset E)), IsIncreasing A → ∀ S : Finset E, probS p S A ≤ probS q S A := by
  classical
  have hq0 : ∀ e, 0 ≤ q e := fun e => le_trans (hp0 e) (hpq e)
  intro A hA S
  induction S using Finset.induction_on generalizing A with
  | empty => simp [probS_empty]
  | @insert e S he ih =>
    have hA1 : IsIncreasing {s : Finset E | insert e s ∈ A} := by
      intro s hs t hst
      refine hA hs ?_
      intro x hx
      rw [Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hst hx)
    have hmem : A ⊆ {s : Finset E | insert e s ∈ A} := fun s hs =>
      hA hs fun x hx => Finset.mem_insert_of_mem hx
    have ihA : probS p S A ≤ probS q S A := ih A hA
    have ihA1 : probS p S {s : Finset E | insert e s ∈ A}
        ≤ probS q S {s : Finset E | insert e s ∈ A} := ih _ hA1
    have hqmono : probS q S A ≤ probS q S {s : Finset E | insert e s ∈ A} :=
      probS_mono_event hq0 hq1 hmem S
    have hpUp : 0 ≤ probS p S A := by
      refine Finset.sum_nonneg fun s _ => ?_
      exact mul_nonneg (lawOn_nonneg hp0 (fun e => le_trans (hpq e) (hq1 e)) S s)
        (by split <;> norm_num)
    have hUq0 : 0 ≤ probS q S A := by
      refine Finset.sum_nonneg fun s _ => ?_
      exact mul_nonneg (lawOn_nonneg hq0 hq1 S s) (by split <;> norm_num)
    rw [probS_insert he, probS_insert he]
    have hstep1 : (1 - p e) * probS p S A + p e * probS p S {s : Finset E | insert e s ∈ A}
        ≤ (1 - p e) * probS q S A + p e * probS q S {s : Finset E | insert e s ∈ A} :=
      add_le_add (mul_le_mul_of_nonneg_left ihA (by linarith [hp0 e, hpq e, hq1 e]))
        (mul_le_mul_of_nonneg_left ihA1 (hp0 e))
    have hstep2 : (1 - p e) * probS q S A + p e * probS q S {s : Finset E | insert e s ∈ A}
        ≤ (1 - q e) * probS q S A + q e * probS q S {s : Finset E | insert e s ∈ A} := by
      have hprod : 0 ≤ (q e - p e) *
          (probS q S {s : Finset E | insert e s ∈ A} - probS q S A) :=
        mul_nonneg (by linarith [hpq e]) (by linarith [hqmono])
      nlinarith [hprod]
    linarith

/-- **Monotonicity in the edge probabilities** (unfolded form). -/
theorem prob_mono_prob {p q : E → ℝ} (hpq : ∀ e, p e ≤ q e) (hp0 : ∀ e, 0 ≤ p e)
    (hq1 : ∀ e, q e ≤ 1) {A : Set (Finset E)} (hA : IsIncreasing A) :
    prob p A ≤ prob q A := by
  rw [← probS_univ p A, ← probS_univ q A]
  exact probS_mono hpq hp0 hq1 A hA univ

/-- Monotonicity of the two-point function in the edge probabilities. -/
theorem twoPoint_mono_prob {p q : E → ℝ} (hpq : ∀ e, p e ≤ q e) (hp0 : ∀ e, 0 ≤ p e)
    (hq1 : ∀ e, q e ≤ 1) (ends : E → Sym2 V) (x y : V) :
    prob p {s | Conn ends s x y} ≤ prob q {s | Conn ends s x y} :=
  prob_mono_prob hpq hp0 hq1 (conn_isIncreasing ends x y)

/-! ### Monotonicity in the long-range parameter `β` -/

/-- The edge probability `1 - exp(-(β * J))` of the long-range model is nondecreasing in `β`. -/
theorem longRangeEdgeProbability_mono {β₁ β₂ J : ℝ} (hJ : 0 ≤ J) (h : β₁ ≤ β₂) :
    PercLib.CriticalLRP.longRangeEdgeProbability β₁ J
      ≤ PercLib.CriticalLRP.longRangeEdgeProbability β₂ J := by
  have h1 : β₁ * J ≤ β₂ * J := mul_le_mul_of_nonneg_right h hJ
  have h2 : Real.exp (-(β₂ * J)) ≤ Real.exp (-(β₁ * J)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  simp only [PercLib.CriticalLRP.longRangeEdgeProbability]
  linarith

/-- **Monotonicity in `β`** for the long-range model on a finite edge type: for increasing
events, `P_β` is nondecreasing in `β`. -/
theorem lrp_prob_mono_beta {J : E → ℝ} (hJ : ∀ e, 0 ≤ J e) {β₁ β₂ : ℝ} (h : β₁ ≤ β₂)
    (hβ₁ : 0 ≤ β₁) {A : Set (Finset E)} (hA : IsIncreasing A) :
    prob (fun e => PercLib.CriticalLRP.longRangeEdgeProbability β₁ (J e)) A
      ≤ prob (fun e => PercLib.CriticalLRP.longRangeEdgeProbability β₂ (J e)) A := by
  refine prob_mono_prob (fun e => longRangeEdgeProbability_mono (hJ e) h) (fun e => ?_)
    (fun e => PercLib.CriticalLRP.longRangeEdgeProbability_le_one (le_trans hβ₁ h) (hJ e)) hA
  exact PercLib.CriticalLRP.longRangeEdgeProbability_nonneg hβ₁ (hJ e)

end

end PercLib.CriticalLRP.TreeGraph
