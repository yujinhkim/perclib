/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Association wrappers for the product-model, product-symmetries and finite-transcripts
articles; all probability statements use the existing canonical product law.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Exploration.Transcript
public import PercLib.Probability.Transport.Reindexing

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace PercLib.Probability
variable {I K : Type*}

/-- The full measurable-bijection and probability-transport contract. -/
@[tag "6RZ8"] theorem product_relabelling (p : I → unitInterval) (e : I ≃ K) :
    Measurable (fun ω : Set I => e '' ω) ∧
    Measurable (fun ω : Set K => e.symm '' ω) ∧
    Function.LeftInverse (fun ω : Set K => e.symm '' ω) (fun ω : Set I => e '' ω) ∧
    Function.RightInverse (fun ω : Set K => e.symm '' ω) (fun ω : Set I => e '' ω) ∧
    (prodBernoulli p).map (fun ω => e '' ω) = prodBernoulli (p ∘ e.symm) ∧
    (∀ A : Set (Set K), MeasurableSet A →
      prodBernoulli p ((fun ω => e '' ω) ⁻¹' A) = prodBernoulli (p ∘ e.symm) A) := by
  refine ⟨measurable_image_equiv e, measurable_image_equiv e.symm, ?_, ?_,
    prodBernoulli_map_image_equiv p e, prodBernoulli_preimage_image_equiv p e⟩
  · intro ω; ext i; simp
  · intro ω; ext k; simp

/-- Profile preservation gives both pushforward and measurable-event invariance. -/
@[tag "VEUZ"] theorem product_relabelling_invariant (p : I → unitInterval) (e : I ≃ I)
    (hp : ∀ i, p (e i) = p i) :
    (prodBernoulli p).map (fun ω => e '' ω) = prodBernoulli p ∧
    (∀ A : Set (Set I), MeasurableSet A →
      prodBernoulli p ((fun ω => e '' ω) ⁻¹' A) = prodBernoulli p A) := by
  refine ⟨prodBernoulli_map_image_invariant p e hp, ?_⟩
  intro A hA
  rw [← Measure.map_apply (measurable_image_equiv e) hA,
    prodBernoulli_map_image_invariant p e hp]

/-- Restriction to any coordinate set has the original restricted profile. -/
theorem prodBernoulli_restrict_apply (p : I → unitInterval) (S : Set I)
    (B : Set (Set S)) (hB : MeasurableSet B) :
    prodBernoulli p {ω | (Subtype.val ⁻¹' ω : Set S) ∈ B} =
      prodBernoulli (fun i : S => p i) B := by
  have hm : Measurable (fun ω : Set I => (Subtype.val ⁻¹' ω : Set S)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  have hmap : (prodBernoulli p).map (fun ω => (Subtype.val ⁻¹' ω : Set S)) =
      prodBernoulli (fun i : S => p i) := by
    rw [prodBernoulli_eq_map (fun i : S => p i),
      ← prodBernoulli_map_query p (fun i : S => (i : I)) Subtype.val_injective,
      Measure.map_map measurable_setOfPred (by fun_prop)]
    rfl
  rw [← hmap, Measure.map_apply hm hB]
  rfl

/-- Transcript probability and factorization against the unrevealed product law. -/
@[tag "EE11"] theorem transcript_probability_and_factorization {J : Type*} [Fintype J]
    (p : I → unitInterval) (e : J → I) (he : Function.Injective e) (b : J → Bool) :
    prodBernoulli p {ω | ∀ j, e j ∈ ω ↔ b j = true} =
      (∏ j, if b j then (unitInterval.toNNReal (p (e j)) : ℝ≥0∞)
        else (unitInterval.toNNReal (unitInterval.symm (p (e j))) : ℝ≥0∞)) ∧
    (∀ B : Set (Set ((Set.range e)ᶜ : Set I)), MeasurableSet B →
      prodBernoulli p {ω | (∀ j, e j ∈ ω ↔ b j = true) ∧
        (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set I)) ∈ B} =
      prodBernoulli p {ω | ∀ j, e j ∈ ω ↔ b j = true} *
        prodBernoulli (fun i : ((Set.range e)ᶜ : Set I) => p i) B) := by
  refine ⟨prodBernoulli_transcript p e he b, ?_⟩
  intro B hB
  rw [prodBernoulli_transcript_inter p e he b B hB,
    prodBernoulli_transcript p e he b, prodBernoulli_restrict_apply p _ B hB]

/-- Positive-probability conditioning on a deterministic adaptive transcript leaves
its unqueried coordinates with the original product law. The quotient is explicit. -/
@[tag "56TE"] theorem adaptive_transcript_conditional {n : ℕ} (p : I → unitInterval)
    (next : (k : Fin n) → (Fin k.val → Bool) → I)
    (answers : Set I → Fin n → Bool)
    (hrun : ∀ ω k, answers ω k = true ↔
      next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω)
    (b : Fin n → Bool) (e : Fin n → I)
    (heq : ∀ k, e k = next k (fun j => b ⟨j.val, j.isLt.trans k.isLt⟩))
    (he : Function.Injective e) (hpos : 0 < prodBernoulli p {ω | answers ω = b})
    (B : Set (Set ((Set.range e)ᶜ : Set I))) (hB : MeasurableSet B) :
    prodBernoulli p {ω | answers ω = b ∧
        (Subtype.val ⁻¹' ω : Set ((Set.range e)ᶜ : Set I)) ∈ B} /
      prodBernoulli p {ω | answers ω = b} =
        prodBernoulli (fun i : ((Set.range e)ᶜ : Set I) => p i) B := by
  rw [prodBernoulli_adaptive_answers_inter p next answers hrun b e heq he B hB,
    prodBernoulli_restrict_apply p _ B hB]
  rw [mul_comm, ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top _ _)]

/-- The finite disjoint open/closed cylinder formula, with no countability assumption. -/
@[tag "5PAT"] theorem prodBernoulli_open_closed (p : I → unitInterval)
    (F H : Finset I) (hFH : Disjoint F H) :
    prodBernoulli p {ω | (↑F : Set I) ⊆ ω ∧ Disjoint (↑H : Set I) ω} =
      (∏ i ∈ F, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
      ∏ i ∈ H, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  let e : F ⊕ H → I := Sum.elim Subtype.val Subtype.val
  have he : Function.Injective e := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
        change (a : I) = b at hab
        exact (Finset.disjoint_left.mp hFH a.property (hab.symm ▸ b.property)).elim
    | inr a =>
      cases b with
      | inl b =>
        change (a : I) = b at hab
        exact (Finset.disjoint_left.mp hFH b.property (hab ▸ a.property)).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext hab)
  have ht := prodBernoulli_transcript p e he (Sum.elim (fun _ => true) (fun _ => false))
  convert ht using 1
  · congr 1
    ext ω
    simp only [e, Sum.forall, Sum.elim_inl, Sum.elim_inr,
      iff_true, Bool.false_eq_true, iff_false, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨fun i => h.1 i.property, fun i => Set.disjoint_left.mp h.2 i.property⟩,
      fun h => ⟨fun i hi => h.1 ⟨i, hi⟩,
        Set.disjoint_left.mpr fun i hi => h.2 ⟨i, hi⟩⟩⟩
  · simp only [Fintype.prod_sum_type, e, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ite_false, ite_true]
    congr 1
    · exact Finset.prod_subtype F (fun _ => Iff.rfl) _
    · exact Finset.prod_subtype H (fun _ => Iff.rfl) _

/-! Witnesses include empty families and mixed endpoint profiles. -/
example (p : I → unitInterval) :
    prodBernoulli p {ω | (↑(∅ : Finset I) : Set I) ⊆ ω ∧
      Disjoint (↑(∅ : Finset I) : Set I) ω} = 1 := by
  simp

example : prodBernoulli (fun b : Bool => if b then 0 else 1)
    {ω | (↑({false} : Finset Bool) : Set Bool) ⊆ ω ∧
      Disjoint (↑({true} : Finset Bool) : Set Bool) ω} = 1 := by
  simpa using prodBernoulli_open_closed (fun b : Bool => if b then 0 else 1)
    {false} {true} (by simp)

/-- A genuine one-step open transcript at probability one has positive mass. -/
example (i : I) :
    0 < prodBernoulli (fun _ : I => 1)
      {ω | (fun _ : Fin 1 => decide (i ∈ ω)) = (fun _ => true)} := by
  have h := prodBernoulli_adaptive_answers (fun _ : I => 1) (fun _ _ => i)
    (fun ω _ => decide (i ∈ ω)) (by intro ω k; simp) (fun _ : Fin 1 => true)
    (fun _ _ _ => Subsingleton.elim _ _)
  rw [h]
  simp

end PercLib.Probability
