/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# A finite-ambient third-moment bound

Translation invariance and the finite third-moment estimate proved in
`SymmetricGroup.Basic`, with `0 ≤ p < 1`. No stationarity hypothesis is added.
-/
module
public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open PercLib.CriticalLRP.TreeGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

/-! ### Invariance of the constant edge law -/

theorem mem_image_eshift_iff (c : V) (s : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ s.image (eshift c) ↔ eshift (-c) e ∈ s := by
  constructor
  · intro h
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    rwa [← hae, eshift_neg_apply]
  · intro h
    exact Finset.mem_image.mpr ⟨eshift (-c) e, h, eshift_apply_neg c e⟩

theorem configurationLaw_const_image (p : ℝ) (c : V) (s : Finset (Sym2 V)) :
    PercLib.CriticalLRP.configurationLaw (constP (V := V) p) (s.image (eshift c)) =
      PercLib.CriticalLRP.configurationLaw (constP (V := V) p) s := by
  rw [PercLib.CriticalLRP.configurationLaw, PercLib.CriticalLRP.configurationLaw]
  refine Fintype.prod_equiv (eshiftEquiv (-c)) (fun e => if e ∈ s.image (eshift c) then p else 1 - p)
    (fun e => if e ∈ s then p else 1 - p) ?_
  intro e
  have h := mem_image_eshift_iff c s e
  show (if e ∈ s.image (eshift c) then p else 1 - p) = (if eshift (-c) e ∈ s then p else 1 - p)
  by_cases he : e ∈ s.image (eshift c)
  · simp only [he, h.mp he, ite_true]
  · have hc : ¬ eshift (-c) e ∈ s := fun hc => he (h.mpr hc)
    simp only [he, hc, ite_false]

theorem prob_image_eshift (p : ℝ) (c : V) (B : Set (Finset (Sym2 V))) :
    prob (constP (V := V) p) {s | s.image (eshift c) ∈ B} = prob (constP (V := V) p) B := by
  classical
  simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
  refine Fintype.sum_equiv (confShift c)
    (fun s => PercLib.CriticalLRP.configurationLaw (constP (V := V) p) s *
      (if s.image (eshift c) ∈ B then (1 : ℝ) else 0))
    (fun t => PercLib.CriticalLRP.configurationLaw (constP (V := V) p) t *
      (if t ∈ B then (1 : ℝ) else 0)) ?_
  intro s
  have hφ : (confShift c) s = s.image (eshift c) := rfl
  rw [hφ, configurationLaw_const_image]

/-- **Translation invariance of the two-point function** for the constant complete-graph model:
`P(a ↔ b) = P(0 ↔ b − a)`.  This is the hypothesis `hinv` of
`moment_bound_of_bk_expectation`, derived here from the invariance of the model rather than
assumed. -/
theorem twoPoint_const_translation (p : ℝ) (a b : V) :
    twoPoint (constP (V := V) p) cfgEnds a b = twoPoint (constP (V := V) p) cfgEnds 0 (b - a) := by
  classical
  unfold twoPoint
  have hset : {s : Finset (Sym2 V) | Conn cfgEnds s a b}
      = {s | s.image (eshift (-a)) ∈ {t : Finset (Sym2 V) | Conn cfgEnds t 0 (b - a)}} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [conn_image_eshift_iff (-a) s a b]
    simp [sub_eq_add_neg]
  rw [hset]
  exact prob_image_eshift p (-a) _

/-! ### The third-moment bound -/

/-- **(I.2.3) at `q = 3`, finite-ambient instance, no translation hypothesis.**
For Bernoulli bond percolation with constant weight `p` on the complete graph of a finite
abelian group, `E|K₀|³ ≤ 3!! (E|K₀|)⁵ = 3 (E|K₀|)⁵`.

Both hypotheses of `moment_bound_of_bk_expectation` are discharged: translation invariance of
the two-point function by `twoPoint_const_translation`, and BK by
`TreeGraph.BKIncreasing_of_bkFin`. -/
theorem third_moment_bound_complete (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    expectReal (constP (V := V) p) (fun s => (TreeGraph.clusterVol cfgEnds s 0 : ℝ) ^ 3)
      ≤ 3 * (clusterVolume (constP (V := V) p) cfgEnds 0) ^ 5 := by
  have hM : ((PercLib.CriticalLRP.VolumeMoments.M (3 - 1) : ℕ) : ℝ) = 3 := by
    norm_num [PercLib.CriticalLRP.VolumeMoments.M]
  have h := moment_bound_of_bk_expectation (constP (V := V) p) (fun _ => hp)
    (fun _ => hp1.le) cfgEnds 0 (fun a b => twoPoint_const_translation p a b)
    (BKIncreasing_of_bkFin _ (fun _ => hp) (fun _ => hp1)) 3 (by norm_num)
  rw [hM] at h
  simpa using h

/-- The same bound on the `d`-dimensional torus `(ZMod n)^d`, i.e. the constant-kernel
long-range model in a periodic box: `E|K₀|³ ≤ 3 (E|K₀|)⁵`. -/
theorem third_moment_bound_torus (d n : ℕ) [NeZero n] (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    expectReal (constP (V := Fin d → ZMod n) p)
        (fun s => (TreeGraph.clusterVol cfgEnds s 0 : ℝ) ^ 3)
      ≤ 3 * (clusterVolume (constP (V := Fin d → ZMod n) p) cfgEnds 0) ^ 5 :=
  third_moment_bound_complete p hp hp1

end

end PercLib.CriticalLRP.TreeExpansion
