/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New boundary-wiring proofs using pinned mathlib product measures and independence
(56a005855ea17e0b0958f73ec801ae140b0a1679), on the canonical bond law.
No new intensity definition or sharpness inequality is introduced.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.ProdBernoulliIndependence
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Reading a family of distinct coordinates gives its product of Bernoulli marginals. -/
theorem law_map_injective_coordinates {J : Type*} (q : Sym2 V → unitInterval)
    (e : J → Sym2 V) (he : Function.Injective e) :
    (law q).map (fun ω j => e j ∈ ω) =
      Measure.infinitePi (fun j => bernoulliMeasure True False (q (e j))) := by
  rw [law, prodBernoulli_eq_map, Measure.map_map (by fun_prop) measurable_setOfPred]
  exact Measure.map_infinitePi_infinitePi_of_inj he

/-- One endpoint fixed makes unordered-pair indexing injective. -/
theorem boundary_pair_injective (x : V) (Λ : Set V) :
    Function.Injective (fun y : (Λᶜ : Set V) => s(x, (y : V))) := by
  intro y z h
  apply Subtype.ext
  simp only [Sym2.eq_iff, true_and] at h
  rcases h with h | ⟨h₁, h₂⟩
  · exact h
  · exact h₂.trans h₁

/-- Disjoint coordinate blocks are independent as full predicate tuples. -/
theorem law_iIndepFun_injective_blocks {B : Type*} {K : B → Type*}
    (q : Sym2 V → unitInterval) (e : (b : B) × K b → Sym2 V)
    (he : Function.Injective e) :
    iIndepFun (fun b (ω : Config V) k => e ⟨b, k⟩ ∈ ω) (law q) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have h : (law q).map (fun ω b k => e ⟨b, k⟩ ∈ ω) =
      Measure.infinitePi (fun b => Measure.infinitePi
        (fun k => bernoulliMeasure True False (q (e ⟨b, k⟩)))) := by
    change (law q).map ((MeasurableEquiv.piCurry (fun _ _ => Prop)) ∘
      (fun ω a => e a ∈ ω)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      law_map_injective_coordinates q e he]
    exact Measure.infinitePi_map_piCurry
      (fun b k => bernoulliMeasure True False (q (e ⟨b, k⟩)))
  rw [h]
  congr 1
  funext b
  exact (law_map_injective_coordinates q (fun k => e ⟨b, k⟩)
    (he.comp (by intro k l hkl; simpa using hkl))).symm

variable [Countable V]

/-- Boundary ghost indicators and all internal edge coordinates are mutually independent.
The domain need not be finite; countability makes each exterior existence event measurable. -/
theorem law_iIndepFun_boundary_internal (q : Sym2 V → unitInterval) (Λ : Set V) :
    iIndepFun (Sum.elim
      (fun (x : Λ) (ω : Config V) => ∃ y : (Λᶜ : Set V), s((x : V), (y : V)) ∈ ω)
      (fun (z : Sym2 Λ) (ω : Config V) => Sym2.map Subtype.val z ∈ ω)) (law q) := by
  let K : Λ ⊕ Sym2 Λ → Type _ := Sum.elim (fun _ => (Λᶜ : Set V)) (fun _ => PUnit)
  let e : (b : Λ ⊕ Sym2 Λ) × K b → Sym2 V := fun a =>
    match a with
    | ⟨Sum.inl x, y⟩ => s((x : V), (y : (Λᶜ : Set V)).val)
    | ⟨Sum.inr z, _⟩ => Sym2.map Subtype.val z
  have he : Function.Injective e := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change s((a : V), (x : (Λᶜ : Set V)).val) = s((b : V), (y : (Λᶜ : Set V)).val) at h
        rcases Sym2.eq_iff.mp h with ⟨ha, hxy⟩ | ⟨hay, hxb⟩
        · have ha' := Subtype.ext ha
          have hx' := Subtype.ext hxy
          subst b
          subst y
          rfl
        · exact (x.property (hxb ▸ b.property)).elim
      | inr b =>
        obtain ⟨b₁, b₂⟩ := b
        change s((a : V), (x : (Λᶜ : Set V)).val) = s((b₁ : V), (b₂ : V)) at h
        rcases Sym2.eq_iff.mp h with ⟨_, hx⟩ | ⟨_, hx⟩
        · exact (x.property (hx ▸ b₂.property)).elim
        · exact (x.property (hx ▸ b₁.property)).elim
    | inr a =>
      cases b with
      | inl b =>
        obtain ⟨a₁, a₂⟩ := a
        change s((a₁ : V), (a₂ : V)) = s((b : V), (y : (Λᶜ : Set V)).val) at h
        rcases Sym2.eq_iff.mp h with ⟨_, hy⟩ | ⟨hy, _⟩
        · exact (y.property (hy ▸ a₂.property)).elim
        · exact (y.property (hy ▸ a₁.property)).elim
      | inr b =>
        have hab : a = b := by
          obtain ⟨a₁, a₂⟩ := a
          obtain ⟨b₁, b₂⟩ := b
          change s((a₁ : V), (a₂ : V)) = s((b₁ : V), (b₂ : V)) at h
          simpa only [Sym2.eq_iff, Subtype.ext_iff] using h
        subst b
        have hxy : x = y := by
          exact @Subsingleton.elim PUnit inferInstance x y
        cases hxy
        rfl
  have h := law_iIndepFun_injective_blocks q e he
  let : ∀ b, Countable (K b) := fun b => by cases b <;> dsimp [K] <;> infer_instance
  have hm (b) : Measurable (fun f : K b → Prop => ∃ k, f k) := by
    have heq : {f : K b → Prop | ∃ k, f k} = ⋃ k, {f : K b → Prop | f k} := by
      ext f
      simp
    have hmset : MeasurableSet {f : K b → Prop | ∃ k, f k} := by
      rw [heq]
      exact MeasurableSet.iUnion (fun k => (measurable_pi_apply k).setOf)
    exact hmset.mem
  have hc := h.comp (fun b (f : K b → Prop) => ∃ k, f k) hm
  convert hc using 1
  funext b ω
  cases b <;> simp [K, e]

/-- The ghost at x is closed exactly when all its exterior bonds are closed. -/
theorem law_boundary_closed (q : Sym2 V → unitInterval) (Λ : Set V) (x : V) :
    law q {ω | ∀ y : (Λᶜ : Set V), s(x, (y : V)) ∉ ω} =
      ∏' y : (Λᶜ : Set V), (unitInterval.toNNReal (unitInterval.symm (q s(x, (y : V)))) : ℝ≥0∞) := by
  have h := law_map_injective_coordinates q (fun y : (Λᶜ : Set V) => s(x, (y : V)))
    (boundary_pair_injective x Λ)
  have hm : MeasurableSet (Set.pi Set.univ (fun _ : (Λᶜ : Set V) => ({False} : Set Prop))) := by
    exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_singleton _)
  have he := congrArg (fun μ : Measure ((Λᶜ : Set V) → Prop) =>
    μ (Set.pi Set.univ (fun _ => ({False} : Set Prop)))) h
  rw [Measure.map_apply (by fun_prop) hm, Measure.infinitePi_pi_of_countable _
    (Set.to_countable _) (fun _ _ => measurableSet_singleton _)] at he
  rw [tprod_univ (f := fun y : (Λᶜ : Set V) =>
    bernoulliMeasure True False (q s(x, (y : V))) {False})] at he
  convert he using 1
  · congr 1
    ext ω
    simp
  · simp

/-- In the summable exponential-intensity case the exterior product is an exponential
of the total exterior intensity. Nonnegativity and summability are explicit. -/
theorem law_boundary_closed_exponential (q : Sym2 V → unitInterval) (Λ : Set V) (x : V)
    (J : Sym2 V → ℝ) (β : ℝ) (_hβ : 0 ≤ β) (_hJ : ∀ e, 0 ≤ J e)
    (hs : Summable (fun y : (Λᶜ : Set V) => J s(x, (y : V))))
    (hq : ∀ y : (Λᶜ : Set V), (q s(x, (y : V)) : ℝ) =
      1 - Real.exp (-β * J s(x, (y : V)))) :
    law q {ω | ∀ y : (Λᶜ : Set V), s(x, (y : V)) ∉ ω} =
      ENNReal.ofReal (Real.exp (-β * ∑' y : (Λᶜ : Set V), J s(x, (y : V)))) := by
  rw [law_boundary_closed]
  have he (y : (Λᶜ : Set V)) :
      (unitInterval.toNNReal (unitInterval.symm (q s(x, (y : V)))) : ℝ≥0∞) =
        ENNReal.ofReal (Real.exp (-β * J s(x, (y : V)))) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [hq y]
  simp_rw [he]
  have ht := (Real.continuous_exp.tendsto _).comp (hs.hasSum.mul_left (-β))
  have ht' := (ENNReal.continuous_ofReal.tendsto _).comp ht
  have hp : HasProd (fun y : (Λᶜ : Set V) =>
      ENNReal.ofReal (Real.exp (-β * J s(x, (y : V)))))
      (ENNReal.ofReal (Real.exp (-β * ∑' y : (Λᶜ : Set V), J s(x, (y : V))))) := by
    unfold HasProd
    convert ht' using 1
    funext F
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
      ← Real.exp_sum]
    rfl
  exact hp.tprod_eq

-- Zero intensity satisfies every side condition, including exterior summability.
example (Λ : Set V) (x : V) :
    law (fun _ : Sym2 V => 0) {ω | ∀ y : (Λᶜ : Set V), s(x, (y : V)) ∉ ω} = 1 := by
  simpa using law_boundary_closed_exponential (fun _ => 0) Λ x (fun _ => 0) 1
    (by norm_num) (by simp) (by simp) (by simp)

-- With no exterior vertices the ghost is always closed, at every profile.
example (q : Sym2 V → unitInterval) (x : V) :
    law q {ω | ∀ y : ((Set.univ : Set V)ᶜ : Set V), s(x, (y : V)) ∉ ω} = 1 := by
  simp

-- A genuine boundary edge at probability one forces the corresponding ghost open.
example : law (fun _ : Sym2 Bool => 1)
    {ω | ∀ y : (({false} : Set Bool)ᶜ : Set Bool), s(false, (y : Bool)) ∉ ω} = 0 := by
  simp [law, prodBernoulli_const]

end PercLib.Percolation.Bond
