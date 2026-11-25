/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# `hvol` for any permutation-invariant edge law: the torus and vertex-transitive case

`HvolRootIndependence.lean` proves the repeated-mean symmetry
`E |K_y| = E |K_x|` (`hvol` of `Correlation/Hrest.lean`) for the lattice
law on `Z^d`, from `edgeMeasure_shift_invariant`.

Nothing in that argument is specific to `Z^d`.  The independent-edge law
`edgeMeasure π` on `Config V = Set (Sym2 V)` is defined for *every* countable
vertex set `V`, and so are `openGraph`, `cluster` and `Connects`.  Here the same
argument is carried out for an arbitrary vertex permutation `g : V ≃ V` with
`π (Sym2.map g e) = π e`:

* `sym2Perm`, `permConfig` : the induced permutation of edges and of
  configurations;
* `permConfig_pair`, `permHom`, `connects_permConfig`, `cluster_permConfig` :
  the relabelling is a graph isomorphism, so `cluster (permConfig g ω) (g v)`
  `= g '' cluster ω v`;
* `edgeMeasure_permConfig_invariant` : `(edgeMeasure π).map (permConfig g)`
  `= edgeMeasure π`;
* `lintegral_cardFun_permConfig` : **`hvol` along `g`**,
  `E |K_{g v}| = E |K_v|`;
* `sum_lintegral_cardFun_permConfig` : the repeated mean over a finite orbit sum;
* `hvol_cardFun_torus` : the same on the finite torus `(Z/n)^d`, i.e. `hvol`
  holds for the finite-torus model with any translation-invariant `π` — the
  model of direction (E) — with no extra hypotheses and no new analysis.

Model: canonical independent percolation on `(V, Sym2 V)` with the product law
`edgeMeasure π`; the torus statements are the special case
`V = Fin d → ZMod n`.  Not an abstract weighted model.
No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.Hrest
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.Correlation.HvolRootIndependence

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP
namespace Hvol

variable {V : Type*} [Countable V]

/-! ## 1. Vertex permutations act on configurations -/

/-- The permutation of unordered pairs induced by a vertex permutation. -/
noncomputable def sym2Perm (g : V ≃ V) : Equiv.Perm (Sym2 V) where
  toFun := Sym2.map g
  invFun := Sym2.map g.symm
  left_inv e := by
    have h : (⇑g.symm ∘ ⇑g) = id := by funext x; simp
    calc Sym2.map g.symm (Sym2.map g e)
        = (Sym2.map g.symm ∘ Sym2.map g) e := rfl
      _ = Sym2.map (⇑g.symm ∘ ⇑g) e := by rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl
  right_inv e := by
    have h : (⇑g ∘ ⇑g.symm) = id := by funext x; simp
    calc Sym2.map g (Sym2.map g.symm e)
        = (Sym2.map g ∘ Sym2.map g.symm) e := rfl
      _ = Sym2.map (⇑g ∘ ⇑g.symm) e := by rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl

theorem sym2Perm_apply (g : V ≃ V) (e : Sym2 V) : sym2Perm g e = Sym2.map g e := rfl

/-- Relabelling of configurations by a vertex permutation: the edge `e` is open in
`permConfig g ω` iff `g⁻¹ e` is open in `ω`. -/
noncomputable def permConfig (g : V ≃ V) (ω : Config V) : Config V :=
  fun e => ω (Sym2.map g.symm e)

theorem mem_permConfig (g : V ≃ V) (ω : Config V) (e : Sym2 V) :
    e ∈ permConfig g ω ↔ Sym2.map g.symm e ∈ ω := Iff.rfl

theorem permConfig_pair (g : V ≃ V) (ω : Config V) (x y : V) :
    s(g x, g y) ∈ permConfig g ω ↔ s(x, y) ∈ ω := by
  rw [mem_permConfig]
  have h : Sym2.map (fun z : V => g.symm z) s(g x, g y) = s(x, y) := by
    rw [Sym2.map_mk]
    simp
  rw [h]

theorem measurable_permConfig (g : V ≃ V) : Measurable (permConfig g) :=
  Measurable.of_eval fun e => measurable_pi_apply (Sym2.map g.symm e)

/-! ## 2. Relabelling is a graph isomorphism -/

/-- `g` is a graph isomorphism from the open graph of `ω` to that of
`permConfig g ω`. -/
noncomputable def permHom (g : V ≃ V) (ω : Config V) :
    (openGraph ω) →g (openGraph (permConfig g ω)) where
  toFun v := g v
  map_rel' := by
    intro u v huv
    rw [openGraph_adj] at huv ⊢
    exact ⟨fun hc => huv.1 (g.injective hc), (permConfig_pair g ω u v).mpr huv.2⟩

theorem connects_permConfig (g : V ≃ V) {ω : Config V} {x y : V}
    (h : Connects ω x y) : Connects (permConfig g ω) (g x) (g y) :=
  SimpleGraph.Reachable.map (permHom g ω) h

theorem permConfig_inv_perm (g : V ≃ V) (ω : Config V) :
    permConfig g.symm (permConfig g ω) = ω := by
  funext e
  apply propext
  change ω (Sym2.map g.symm (Sym2.map g e)) ↔ ω e
  have h : (fun z : V => g.symm z) ∘ (fun z : V => g z) = id := by
    funext z; simp
  have hkey : Sym2.map (fun z : V => g.symm z) (Sym2.map (fun z : V => g z) e) = e := by
    calc Sym2.map (fun z : V => g.symm z) (Sym2.map (fun z : V => g z) e)
        = (Sym2.map (fun z : V => g.symm z) ∘ Sym2.map (fun z : V => g z)) e := rfl
      _ = Sym2.map ((fun z : V => g.symm z) ∘ (fun z : V => g z)) e := by
            rw [← Sym2.map_comp]
      _ = Sym2.map id e := by rw [h]
      _ = e := by rw [Sym2.map_id]; rfl
  rw [hkey]

/-- **Cluster covariance** under a vertex permutation. -/
theorem cluster_permConfig (g : V ≃ V) (ω : Config V) (v : V) :
    cluster (permConfig g ω) (g v) = g '' cluster ω v := by
  ext w
  rw [mem_cluster_iff, Set.mem_image]
  constructor
  · intro hw
    have hb : Connects (permConfig g.symm (permConfig g ω)) (g.symm (g v)) (g.symm w) :=
      connects_permConfig g.symm hw
    rw [permConfig_inv_perm] at hb
    have hv : g.symm (g v) = v := by simp
    rw [hv] at hb
    exact ⟨g.symm w, (mem_cluster_iff).mpr hb, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact connects_permConfig g ((mem_cluster_iff).mp hu)

/-! ## 3. Permutation invariance of the law -/

/-- **Invariance of `edgeMeasure π` under a vertex permutation** that preserves
`π`.  This is `edgeMeasure_shift_invariant` with the translation replaced by an
arbitrary permutation, hence in particular with `Z^d` replaced by any vertex set
(finite tori, Cayley graphs, ...). -/
theorem edgeMeasure_permConfig_invariant (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hπ : ∀ e : Sym2 V, π (Sym2.map g e) = π e) :
    (edgeMeasure π).map (permConfig g) = edgeMeasure π := by
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun e : Sym2 V => bernoulliMeasure (True : Prop) (False : Prop) (π e))
    (sym2Perm g)
  have hfamilies : (fun i : Sym2 V =>
        bernoulliMeasure (True : Prop) (False : Prop) (π (sym2Perm g i)))
      = fun i => bernoulliMeasure (True : Prop) (False : Prop) (π i) := by
    funext i
    rw [sym2Perm_apply, hπ]
  rw [hfamilies] at h
  have hmap : permConfig g = ⇑(MeasurableEquiv.piCongrLeft
      (fun _ : Sym2 V => Prop) (sym2Perm g)) := by
    funext ω e
    conv_rhs => rw [piCongrLeft_apply_eq (e := sym2Perm g) (x := ω) (j := e)]
    rfl
  rw [hmap, edgeMeasure_eq_infinitePi π]
  exact h

/-! ## 4. `hvol` along a vertex permutation -/

/-- **`hvol` for any permutation-invariant law**: `E|K_{g v}| = E|K_v|`. -/
theorem lintegral_cardFun_permConfig (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hπ : ∀ e : Sym2 V, π (Sym2.map g e) = π e) (x : V) :
    ∫⁻ ω, Percolation.cardFun (cluster ω (g x)) ∂(edgeMeasure π)
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) :=
  lintegral_cardFun_root_indep (edgeMeasure π) (measurable_permConfig g)
    (edgeMeasure_permConfig_invariant π g hπ) (e := ⇑g) g.injective
    (fun ω v => cluster_permConfig g ω v) x

/-- The repeated mean over a finite family of permuted roots: each permuted root
contributes the same expected volume. -/
theorem sum_lintegral_cardFun_orbit (π : Sym2 V → unitInterval) (G : Finset (V ≃ V))
    (hG : ∀ g ∈ G, ∀ e : Sym2 V, π (Sym2.map g e) = π e) (x : V) :
    ∑ g ∈ G, ∫⁻ ω, Percolation.cardFun (cluster ω (g x)) ∂(edgeMeasure π)
      = (G.card : ℝ≥0∞) *
        ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) := by
  rw [Finset.sum_congr rfl
      (fun g hg => lintegral_cardFun_permConfig π g (hG g hg) x),
    Finset.sum_const, nsmul_eq_mul]

/-! ## 5. The finite torus `(Z/n)^d`

`Config V`, `openGraph`, `cluster` and `edgeMeasure` are defined for every
countable `V`, so the finite torus `V = Fin d → ZMod n` is an instance of the
same canonical model, and `hvol` holds there by the generic permutation result.
Nothing below is specific to how the torus kernel is chosen: only its translation
invariance is used, so this covers *any* finite-cutoff torus law of the form
`edgeMeasure π`. -/

/-- Translation of the torus vertex set `(Z/n)^d`. -/
noncomputable def torusShift {d n : ℕ} [NeZero n] (a : Fin d → ZMod n) :
    Equiv.Perm (Fin d → ZMod n) where
  toFun u := u + a
  invFun u := u - a
  left_inv u := by simp
  right_inv u := by simp

@[simp] theorem torusShift_apply {d n : ℕ} [NeZero n] (a u : Fin d → ZMod n) :
    torusShift a u = u + a := rfl

/-- **`hvol` on the finite torus.**  For any translation-invariant `π` on the
torus edge set, the expected extended cluster cardinality does not depend on the
root.  This is the `hvol` input of `Correlation/Hrest.lean` in the finite-torus
model, with no hypotheses beyond translation invariance of `π`. -/
theorem hvol_cardFun_torus (d n : ℕ) [NeZero n]
    (π : Sym2 (Fin d → ZMod n) → unitInterval)
    (hπ : ∀ (a : Fin d → ZMod n) (e : Sym2 (Fin d → ZMod n)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (x y : Fin d → ZMod n) :
    ∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) := by
  have h := lintegral_cardFun_permConfig π (torusShift (y - x))
    (fun e => hπ (y - x) e) x
  have hxy : x + (y - x) = y := by
    funext i
    simp
  simpa only [torusShift_apply, hxy] using h

end Hvol
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hvol.sym2Perm
#print axioms PercLib.CriticalLRP.Hvol.permConfig_pair
#print axioms PercLib.CriticalLRP.Hvol.measurable_permConfig
#print axioms PercLib.CriticalLRP.Hvol.connects_permConfig
#print axioms PercLib.CriticalLRP.Hvol.cluster_permConfig
#print axioms PercLib.CriticalLRP.Hvol.edgeMeasure_permConfig_invariant
#print axioms PercLib.CriticalLRP.Hvol.lintegral_cardFun_permConfig
#print axioms PercLib.CriticalLRP.Hvol.sum_lintegral_cardFun_orbit
#print axioms PercLib.CriticalLRP.Hvol.hvol_cardFun_torus
