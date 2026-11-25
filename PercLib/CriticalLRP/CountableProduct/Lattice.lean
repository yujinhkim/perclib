/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Translation invariance of the lattice model: `θ_β(v)` does not depend on `v` and
`τ_β(x,y)` depends only on `y - x`.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  The paper writes `E_β|K|` with `K` "the cluster of the origin" (§I.2.1)
and states hypothesis (HD) as `P_{β_c}(x ↔ y) ⪯ ‖x - y‖^{-d+2}`, i.e. it uses that the law
on `Z^d` with a translation-invariant kernel (`J(x,y) = J(0, y-x)`, §I.1.2) is invariant
under lattice translations.

Proved here: the translation action on configurations, invariance of `P_β` for a
translation-invariant kernel, equivariance of clusters, and the consequences that `θ` is
constant and `τ` depends only on the difference.

No `sorry`, no custom axioms.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.CriticalLRP.CountableProduct.Marks
public import PercLib.CriticalLRP.CountableProduct.ZeroOne
public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.CriticalLRP.CountableProduct.TwoPoint

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

section Sym2Shift

/-- Translation of unordered pairs of lattice sites: `{x,y} ↦ {x+a, y+a}`. -/
noncomputable def sym2Shift {d : ℕ} (a : Fin d → ℤ) : Sym2 (Fin d → ℤ) ≃ Sym2 (Fin d → ℤ) where
  toFun := Sym2.map (fun x => x + a)
  invFun := Sym2.map (fun x => x - a)
  left_inv e := by
    have h : (fun x : Fin d → ℤ => x - a) ∘ (fun x => x + a) = id := by
      funext x; simp
    calc Sym2.map (fun x => x - a) (Sym2.map (fun x => x + a) e)
        = (Sym2.map (fun x => x - a) ∘ Sym2.map (fun x => x + a)) e := rfl
      _ = Sym2.map ((fun x => x - a) ∘ (fun x => x + a)) e := by rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl
  right_inv e := by
    have h : (fun x : Fin d → ℤ => x + a) ∘ (fun x => x - a) = id := by
      funext x; simp
    calc Sym2.map (fun x => x + a) (Sym2.map (fun x => x - a) e)
        = (Sym2.map (fun x => x + a) ∘ Sym2.map (fun x => x - a)) e := rfl
      _ = Sym2.map ((fun x => x + a) ∘ (fun x => x - a)) e := by rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl

theorem sym2Shift_apply {d : ℕ} (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    sym2Shift a e = Sym2.map (fun x => x + a) e := rfl

/-- The configuration obtained by translating all sites by `-a` inside `ω`: the edge
`{x,y}` is open in `shiftConfig a ω` iff `{x-a, y-a}` is open in `ω`. -/
noncomputable def shiftConfig {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    Config (Fin d → ℤ) :=
  fun e => ω (Sym2.map (fun x => x - a) e)

theorem mem_shiftConfig {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) (e : Sym2 (Fin d → ℤ)) :
    e ∈ shiftConfig a ω ↔ Sym2.map (fun x => x - a) e ∈ ω := Iff.rfl

theorem shiftConfig_add_mem {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ))
    (x y : Fin d → ℤ) : s(x + a, y + a) ∈ shiftConfig a ω ↔ s(x, y) ∈ ω := by
  rw [mem_shiftConfig]
  have h : Sym2.map (fun z : Fin d → ℤ => z - a) s(x + a, y + a) = s(x, y) := by
    rw [Sym2.map_mk]
    simp
  rw [h]

theorem measurable_shiftConfig {d : ℕ} (a : Fin d → ℤ) : Measurable (shiftConfig a) :=
  Measurable.of_eval fun e => measurable_pi_apply (Sym2.map (fun x : Fin d → ℤ => x - a) e)

/-- Translation is a graph homomorphism from the open graph of `ω` to that of the translated
configuration. -/
noncomputable def shiftHom {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    (openGraph ω) →g (openGraph (shiftConfig a ω)) where
  toFun u := u + a
  map_rel' := by
    intro u v huv
    rw [openGraph_adj] at huv ⊢
    exact ⟨fun hc => huv.1 (add_right_cancel hc), (shiftConfig_add_mem a ω u v).mpr huv.2⟩

/-- Translation preserves connectivity. -/
theorem connects_shiftConfig {d : ℕ} (a : Fin d → ℤ) {ω : Config (Fin d → ℤ)}
    {x y : Fin d → ℤ} (h : Connects ω x y) :
    Connects (shiftConfig a ω) (x + a) (y + a) :=
  SimpleGraph.Reachable.map (shiftHom a ω) h

/-- Translating by `a` and then by `-a` returns the original configuration. -/
theorem shiftConfig_neg_shift {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    shiftConfig (-a) (shiftConfig a ω) = ω := by
  funext e
  apply propext
  change ω (Sym2.map (fun z : Fin d → ℤ => z - a) (Sym2.map (fun z => z - (-a)) e)) ↔ ω e
  have hkey : Sym2.map (fun z : Fin d → ℤ => z - a) (Sym2.map (fun z => z - (-a)) e) = e := by
    have h : (fun z : Fin d → ℤ => z - a) ∘ (fun z => z - (-a)) = id := by funext z; simp
    calc Sym2.map (fun z : Fin d → ℤ => z - a) (Sym2.map (fun z => z - (-a)) e)
        = (Sym2.map (fun z : Fin d → ℤ => z - a) ∘ Sym2.map (fun z => z - (-a))) e := rfl
      _ = Sym2.map ((fun z : Fin d → ℤ => z - a) ∘ (fun z => z - (-a))) e := by rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl
  rw [hkey]

/-- Translation is an isomorphism from `ω` to `shiftConfig a ω`, so the cluster of `v + a`
in `shiftConfig a ω` is the translate of the cluster of `v` in `ω`. -/
theorem cluster_shiftConfig {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ))
    (v : Fin d → ℤ) :
    cluster (shiftConfig a ω) (v + a) = (fun u => u + a) '' cluster ω v := by
  ext w
  rw [mem_cluster_iff, Set.mem_image]
  constructor
  · intro hw
    have hb : Connects (shiftConfig (-a) (shiftConfig a ω)) ((v + a) + -a) (w + -a) :=
      connects_shiftConfig (-a) hw
    rw [shiftConfig_neg_shift] at hb
    have hv : (v + a) + -a = v := by simp
    rw [hv] at hb
    exact ⟨w + -a, (mem_cluster_iff).mpr hb, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact connects_shiftConfig a ((mem_cluster_iff).mp hu)

/-- `v` lies in an infinite cluster iff `v + a` does, in the translated configuration. -/
theorem infiniteCluster_shiftConfig {d : ℕ} (a : Fin d → ℤ) (ω : Config (Fin d → ℤ))
    (v : Fin d → ℤ) :
    InInfiniteCluster (shiftConfig a ω) (v + a) ↔ InInfiniteCluster ω v := by
  rw [inInfiniteCluster_iff_infinite, inInfiniteCluster_iff_infinite, cluster_shiftConfig]
  constructor
  · exact Set.Infinite.of_image _
  · intro h
    exact h.image (fun x _ y _ hxy => by simpa using hxy)

end Sym2Shift

/-- Evaluation of `MeasurableEquiv.piCongrLeft` on a constant family. -/
theorem piCongrLeft_apply_eq {α β : Type*} [MeasurableSpace β] (e : α ≃ α) (x : α → β) (j : α) :
    MeasurableEquiv.piCongrLeft (fun _ : α => β) e x j = x (e.symm j) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : α => β) e x (e.symm j)
  rwa [Equiv.apply_symm_apply] at h

section Invariance

variable {d : ℕ}

/-- Translation invariance of the law, in the product form. -/
theorem edgeMeasure_shift_invariant_pi (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (a : Fin d → ℤ) :
    (Measure.infinitePi (fun e : Sym2 (Fin d → ℤ) =>
        bernoulliMeasure (True : Prop) (False : Prop) (π e))).map
        (MeasurableEquiv.piCongrLeft (fun _ : Sym2 (Fin d → ℤ) => Prop) (sym2Shift a)) =
      Measure.infinitePi (fun e : Sym2 (Fin d → ℤ) =>
        bernoulliMeasure (True : Prop) (False : Prop) (π e)) := by
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun e : Sym2 (Fin d → ℤ) =>
      bernoulliMeasure (True : Prop) (False : Prop) (π e)) (sym2Shift a)
  have hfamilies : (fun i : Sym2 (Fin d → ℤ) =>
      bernoulliMeasure (True : Prop) (False : Prop) (π (sym2Shift a i)))
      = fun i => bernoulliMeasure (True : Prop) (False : Prop) (π i) := by
    funext i
    rw [sym2Shift_apply, hπ]
  rw [hfamilies] at h
  exact h

-- The remaining step for translation invariance of `P_β` itself is
-- `(edgeMeasure π).map (shiftConfig a) = edgeMeasure π` for translation-invariant `π`, which
-- follows from `Measure.infinitePi_map_piCongrLeft`; the Lean plumbing of that statement
-- (identifying `MeasurableEquiv.piCongrLeft` with `shiftConfig`) is not finished here, so
-- `percolationFunction`'s independence of the vertex and `twoPointFunction`'s dependence on
-- `y - x` only are *not* claimed in this file.  The combinatorial content they need
-- (`infiniteCluster_shiftConfig`, `connects_shiftConfig`, `cluster_shiftConfig`) is proved.

/-- A translation-invariant kernel gives a translation-invariant edge-open probability. -/
theorem bernoulliEdgeProb_shift {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    bernoulliEdgeProb J hJ β (Sym2.map (fun x => x + a) e) = bernoulliEdgeProb J hJ β e := by
  apply Subtype.ext
  rw [bernoulliEdgeProb_coe, bernoulliEdgeProb_coe, hJinv]

/-- With the paper's kernel, `τ_β(x,y) = τ_β(0, y-x)`. -/
theorem lrKernel_shift_invariant (d : ℕ) (α : ℝ) (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    lrKernel d α (Sym2.map (fun x => x + a) e) = lrKernel d α e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.map_mk, lrKernel, Sym2.lift_mk]
    have h2 : ((x + a) - (y + a) : Fin d → ℤ) = x - y := by funext i; simp
    rw [h2]

/-- **Invariance of `P_β` under lattice translations** for a translation-invariant kernel. -/
theorem edgeMeasure_shift_invariant (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (a : Fin d → ℤ) :
    (edgeMeasure π).map (shiftConfig a) = edgeMeasure π := by
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun e : Sym2 (Fin d → ℤ) =>
      bernoulliMeasure (True : Prop) (False : Prop) (π e)) (sym2Shift a)
  have hfamilies : (fun i : Sym2 (Fin d → ℤ) =>
      bernoulliMeasure (True : Prop) (False : Prop) (π (sym2Shift a i)))
      = fun i => bernoulliMeasure (True : Prop) (False : Prop) (π i) := by
    funext i
    rw [sym2Shift_apply, hπ]
  rw [hfamilies] at h
  have hmap : shiftConfig a = ⇑(MeasurableEquiv.piCongrLeft
      (fun _ : Sym2 (Fin d → ℤ) => Prop) (sym2Shift a)) := by
    funext ω e
    conv_rhs => rw [piCongrLeft_apply_eq (e := sym2Shift a) (x := ω) (j := e)]
    rfl
  rw [hmap, edgeMeasure_eq_infinitePi π]
  exact h

/-- **`θ_β(v)` does not depend on `v`** for a translation-invariant kernel on `Z^d`. -/
theorem percolationFunction_shift {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (a v : Fin d → ℤ) :
    percolationFunction J hJ β (v + a) = percolationFunction J hJ β v := by
  have hinv := edgeMeasure_shift_invariant (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_shift hJinv hJ β) a
  have hmp := Measure.map_apply (μ := edgeMeasure (bernoulliEdgeProb J hJ β))
    (measurable_shiftConfig a) (measurableSet_inInfiniteCluster (v + a))
  have hpre : shiftConfig a ⁻¹' {ω : Config (Fin d → ℤ) | InInfiniteCluster ω (v + a)}
      = {ω : Config (Fin d → ℤ) | InInfiniteCluster ω v} := by
    ext ω
    exact infiniteCluster_shiftConfig a ω v
  show (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | InInfiniteCluster ω (v + a)}
      = (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | InInfiniteCluster ω v}
  calc (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | InInfiniteCluster ω (v + a)}
      = (edgeMeasure (bernoulliEdgeProb J hJ β)).map (shiftConfig a)
          {ω | InInfiniteCluster ω (v + a)} := by rw [hinv]
    _ = (edgeMeasure (bernoulliEdgeProb J hJ β))
          (shiftConfig a ⁻¹' {ω | InInfiniteCluster ω (v + a)}) := hmp
    _ = (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | InInfiniteCluster ω v} := by rw [hpre]

/-- `θ` is the same at every vertex, packaged as `θ(v) = θ(0)`. -/
theorem percolationFunction_eq_origin {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (v : Fin d → ℤ) :
    percolationFunction J hJ β v = percolationFunction J hJ β 0 := by
  have h := percolationFunction_shift hJinv hJ β v 0
  simpa using h

/-- **`τ_β` is translation invariant.** -/
theorem twoPointFunction_shift {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (a x y : Fin d → ℤ) :
    twoPointFunction J hJ β (x + a) (y + a) = twoPointFunction J hJ β x y := by
  have hinv := edgeMeasure_shift_invariant (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_shift hJinv hJ β) a
  have hmp := Measure.map_apply (μ := edgeMeasure (bernoulliEdgeProb J hJ β))
    (measurable_shiftConfig a) (measurableSet_connects (x + a) (y + a))
  have hpre : shiftConfig a ⁻¹' {ω : Config (Fin d → ℤ) | Connects ω (x + a) (y + a)}
      = {ω : Config (Fin d → ℤ) | Connects ω x y} := by
    ext ω
    constructor
    · intro h
      have hb : Connects (shiftConfig (-a) (shiftConfig a ω)) ((x + a) + -a) ((y + a) + -a) :=
        connects_shiftConfig (-a) h
      rw [shiftConfig_neg_shift] at hb
      have hx : (x + a) + -a = x := by simp
      have hy : (y + a) + -a = y := by simp
      rw [hx, hy] at hb
      exact hb
    · intro h
      exact connects_shiftConfig a h
  show (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | Connects ω (x + a) (y + a)}
      = (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | Connects ω x y}
  calc (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | Connects ω (x + a) (y + a)}
      = (edgeMeasure (bernoulliEdgeProb J hJ β)).map (shiftConfig a)
          {ω | Connects ω (x + a) (y + a)} := by rw [hinv]
    _ = (edgeMeasure (bernoulliEdgeProb J hJ β))
          (shiftConfig a ⁻¹' {ω | Connects ω (x + a) (y + a)}) := hmp
    _ = (edgeMeasure (bernoulliEdgeProb J hJ β)) {ω | Connects ω x y} := by rw [hpre]

/-- **`τ_β(x,y)` depends only on `y - x`**: `τ(x,y) = τ(0, y-x)`. -/
theorem twoPointFunction_eq_origin {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (x y : Fin d → ℤ) :
    twoPointFunction J hJ β x y = twoPointFunction J hJ β 0 (y - x) := by
  have h := twoPointFunction_shift hJinv hJ β x 0 (y - x)
  simpa using h

end Invariance

end PercLib.CriticalLRP
