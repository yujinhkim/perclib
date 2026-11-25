/-
Generalises the product-law transport in
near-critical-diffusivity/Percolation/Literature/BondPercolationSymmetry.lean,
setBernoulli_map_relabel and setBernoulli_real_preimage_relabel, at revision
c820fea91a7482c1755de0ec94ecb9f59ccfcacc. Native reuse permission: DECISIONS R-3.
The law here is the existing arbitrary-profile prodBernoulli; no host graph or
new configuration equivalence is introduced. Uses pinned mathlib reindexing.
-/
module

public import PercLib.Meta.Tag

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Data.Sym.Sym2

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace PercLib.Probability
variable {I K : Type*}

/-- Relabelling a set by an equivalence is measurable for arbitrary index types. -/
theorem measurable_image_equiv (e : I ≃ K) : Measurable (fun ω : Set I => e '' ω) := by
  apply measurable_set_iff.mpr
  intro k
  simpa only [Set.mem_image_equiv] using measurable_set_mem (e.symm k)

/-- Reindexing the canonical product law transports the full coordinate profile. -/
theorem prodBernoulli_map_image_equiv (p : I → unitInterval) (e : I ≃ K) :
    (prodBernoulli p).map (fun ω => e '' ω) = prodBernoulli (p ∘ e.symm) := by
  let ν : K → Measure Prop := fun k => bernoulliMeasure True False (p (e.symm k))
  have hν : (fun i => ν (e i)) = fun i => bernoulliMeasure True False (p i) := by
    funext i
    simp [ν]
  have hpi := Measure.infinitePi_map_piCongrLeft (X := fun _ : K => Prop) ν e
  have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ : K => Prop) e) =
      fun χ : I → Prop => fun k => χ (e.symm k) := by
    funext χ k
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  have hcomm : (fun ω : Set I => e '' ω) ∘ (fun χ : I → Prop => {i | χ i}) =
      (fun χ : K → Prop => {k | χ k}) ∘ (fun χ : I → Prop => fun k => χ (e.symm k)) := by
    funext χ
    ext k
    simp
  simp only [prodBernoulli_eq_map]
  rw [Measure.map_map (measurable_image_equiv e) measurable_setOfPred, hcomm,
    ← Measure.map_map measurable_setOfPred (by fun_prop), ← hν, ← hcoe, hpi]
  rfl

/-- The probability of a relabelled measurable event is its transported-profile probability. -/
theorem prodBernoulli_preimage_image_equiv (p : I → unitInterval) (e : I ≃ K)
    (A : Set (Set K)) (hA : MeasurableSet A) :
    prodBernoulli p ((fun ω => e '' ω) ⁻¹' A) = prodBernoulli (p ∘ e.symm) A := by
  rw [← Measure.map_apply (measurable_image_equiv e) hA, prodBernoulli_map_image_equiv]

/-- Real-valued form, including profiles with probability zero or one. -/
theorem prodBernoulli_real_preimage_image_equiv (p : I → unitInterval) (e : I ≃ K)
    (A : Set (Set K)) (hA : MeasurableSet A) :
    (prodBernoulli p).real ((fun ω => e '' ω) ⁻¹' A) =
      (prodBernoulli (p ∘ e.symm)).real A := by
  simp only [measureReal_def, prodBernoulli_preimage_image_equiv p e A hA]

/-- A profile-preserving permutation leaves the law invariant. -/
theorem prodBernoulli_map_image_invariant (p : I → unitInterval) (e : I ≃ I)
    (hp : ∀ i, p (e i) = p i) :
    (prodBernoulli p).map (fun ω => e '' ω) = prodBernoulli p := by
  rw [prodBernoulli_map_image_equiv]
  congr 1
  funext i
  simpa using (hp (e.symm i)).symm

/-- Vertex relabelling transports the arbitrary profile on unordered pairs.
The equivalence is assembled locally from mathlib Sym2.map; no new public alias. -/
@[tag "6VY0"] theorem prodBernoulli_map_image_sym2 {V W : Type*}
    (p : Sym2 V → unitInterval) (e : V ≃ W) :
    (prodBernoulli p).map (fun ω => Sym2.map e '' ω) =
      prodBernoulli (p ∘ Sym2.map e.symm) := by
  let e2 : Sym2 V ≃ Sym2 W :=
    { toFun := Sym2.map e
      invFun := Sym2.map e.symm
      left_inv := by intro a; induction a using Sym2.ind with | _ x y => simp
      right_inv := by intro a; induction a using Sym2.ind with | _ x y => simp }
  exact prodBernoulli_map_image_equiv p e2

/-- Vertex-permutation symmetry of a bond profile gives symmetry of its entire law.
Diagonal coordinates are retained and need no special value. -/
theorem prodBernoulli_map_image_sym2_invariant {V : Type*}
    (p : Sym2 V → unitInterval) (e : V ≃ V)
    (hp : ∀ a, p (Sym2.map e a) = p a) :
    (prodBernoulli p).map (fun ω => Sym2.map e '' ω) = prodBernoulli p := by
  rw [prodBernoulli_map_image_sym2]
  congr 1
  funext a
  induction a using Sym2.ind with
  | _ x y => simpa using (hp s(e.symm x, e.symm y)).symm

/-- Swapping two coordinates swaps distinct endpoint probabilities. -/
example :
    (prodBernoulli (fun b : Bool => if b then 1 else 0)).map
      (fun ω => (Equiv.swap false true) '' ω) =
    prodBernoulli (fun b : Bool => if b then 0 else 1) := by
  rw [prodBernoulli_map_image_equiv]
  congr 1
  funext b
  cases b <;> simp

/-- Empty index types are allowed. -/
example (p : Empty → unitInterval) :
    (prodBernoulli p).map (fun ω => (Equiv.refl Empty) '' ω) = prodBernoulli p := by
  simp

/-- A nonzero constant bond profile, including its loops, is invariant. -/
example (e : Bool ≃ Bool) :
    (prodBernoulli (fun _ : Sym2 Bool => (1 : unitInterval))).map
      (fun ω => Sym2.map e '' ω) = prodBernoulli (fun _ : Sym2 Bool => 1) :=
  prodBernoulli_map_image_sym2_invariant _ e (fun _ => rfl)

end PercLib.Probability
