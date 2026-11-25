/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The law of a finite edge window, and the finite-product form of `hfin`

Source: T. Hutchcroft, arXiv:2008.11197v2, §2.1, proof of Theorem 2.3, last paragraph
("The infinite cases of (2.8) and (2.9) follow straightforwardly from the finite cases by
passing to the limit in an exhaustion over finite subgraphs").

The exhaustion passage of `.ultramath/smwgfehv2/m4` reduces the countable-graph bound (2.8) to
the per-stage hypothesis

  `hfin r : P(|K_max(W) ∩ (A r)| ≥ 3^k λ) ≤ P(|K_max(W) ∩ (A r)| ≥ λ)^(3^(k-1)+1)`,

where both probabilities are computed in the *ambient* law `μ` of the countable graph, and
`|K_max(W) ∩ (A r)|` is the window maximum *restricted to `A r`*.  m4 left open the
"law identification": `hfin r` is a statement about finitely many edge coordinates, and the
point of this file is to show that its probability is literally a probability under the
**finite product Bernoulli law of that finite edge set** — i.e. that `hfin r` is the
finite-graph case of (2.8), where the source's BK argument lives.

What is proved here (all for an arbitrary countable `V`, arbitrary `π : Sym2 V → unitInterval`,
no subcriticality/nonintegrality hypothesis and no new definitions of the model's objects):

* `restrictEdge F ω` — the configuration `ω` restricted to the edge coordinates in the finite
  set `F`;  `extendEdge F f` — the configuration equal to `f` on `F` and closed elsewhere.
* `map_restrictEdge_edgeMeasure` — **the law identification**:
  `(edgeMeasure π).map (restrictEdge F) = edgeLaw (fun e : F => π e.1)`, i.e. the law of the
  finitely many coordinates in `F` is the finite independent-edge product law.  This is
  Mathlib's `Measure.infinitePi_map_restrict'` applied to the repository's two definitions
  (`edgeMeasure` is `Measure.infinitePi` of the per-edge Bernoulli laws by definition, and
  `edgeLaw` is the same thing by `edgeLaw_eq_infinitePi`).
* `measure_maxVol_event_eq` / `measure_vol_event_eq` — the per-stage event of the exhaustion,
  `{|K_max(W) ∩ (A r)| ≥ λ}` (resp. `{|K_u ∩ (A r)| ≥ λ}`), has, under `edgeMeasure π`, exactly
  the probability that the corresponding event has under the finite product law of the internal
  edge set of `A r`.
* `per_scale_of_finiteEdgeLaw` — hence the exhaustion passage of m4 applies with `hfin` supplied
  by the **finite product-space** bound alone.  Nothing else is assumed.

Exact scope: this file does *not* prove the finite product-space bound.  What it does is remove
the measure-theoretic gap between the two: after this file, the finite case of (2.8) can be
proved in the finite product space `Set ↑F` (a finite product of Bernoulli laws) and transported
verbatim.  The translation of the repository's `BondGraph`/`MaxMeets` formulation
(`Tightness/MaxClusterPower.lean`) into the predicate `vol`/`maxVol` used here is a separate
combinatorial statement about `Conn` versus `PathIn`, recorded in the README; it is *not* used by
anything below.
-/
module

public import PercLib.CriticalLRP.Tightness.LongRangePower
public import PercLib.CriticalLRP.Tightness.Exhaustion.Locality

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

set_option linter.unusedSectionVars false

open PercLib.CriticalLRP.Percolation

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-! ## 1. Restriction and extension of a configuration along a finite edge set -/

/-- The configuration `ω` restricted to the edge coordinates in the finite set `F`. -/
def restrictEdge (F : Finset (Sym2 V)) : Config V → Set ↑F :=
  Set.domRestrict (F : Set (Sym2 V))

lemma measurable_restrictEdge (F : Finset (Sym2 V)) :
    Measurable (restrictEdge (V := V) F) :=
  Set.measurable_restrict (F : Set (Sym2 V))

/-- The configuration that opens exactly the edges of `f` inside `F` and no other edge. -/
def extendEdge (F : Finset (Sym2 V)) (f : Set ↑F) : Config V :=
  fun e => ∃ x : ↑F, x ∈ f ∧ (x : Sym2 V) = e

/-- Inside `F`, extending the restriction of `ω` recovers `ω`. -/
lemma extendEdge_restrictEdge {F : Finset (Sym2 V)} (ω : Config V) {e : Sym2 V} (he : e ∈ F) :
    e ∈ extendEdge F (restrictEdge F ω) ↔ e ∈ ω := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨⟨e, he⟩, h, rfl⟩

/-- Restricting an extension recovers the finite configuration. -/
lemma restrictEdge_extendEdge {F : Finset (Sym2 V)} (f : Set ↑F) :
    restrictEdge F (extendEdge F f) = f := by
  funext x
  refine propext ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  rw [← Subtype.ext hyx]
  exact hy

/-! ## 2. The law identification -/

/-- **The law of a finite edge window is the finite product Bernoulli law.**

Under the countable independent-edge law `edgeMeasure π`, the joint law of the coordinates in a
finite edge set `F` is the finite product law `edgeLaw (π|F)` of those coordinates.  This is the
cylinder/independence identification which turns the per-stage hypothesis `hfin` of the exhaustion
into a genuine finite-graph statement. -/
theorem map_restrictEdge_edgeMeasure (π : Sym2 V → unitInterval) (F : Finset (Sym2 V)) :
    (edgeMeasure π).map (restrictEdge (V := V) F) =
      edgeLaw (fun e : ↑F => π (e : Sym2 V)) := by
  rw [restrictEdge, edgeMeasure_eq_infinitePi, edgeLaw_eq_infinitePi]
  exact Measure.infinitePi_map_restrict' (fun e : Sym2 V => _) (I := (F : Set (Sym2 V)))

/-- Preimage form of the law identification, for an arbitrary measurable set of finite
configurations. -/
theorem measure_restrictEdge_preimage (π : Sym2 V → unitInterval) (F : Finset (Sym2 V))
    {S : Set (Set ↑F)} (hS : MeasurableSet S) :
    edgeMeasure π (restrictEdge (V := V) F ⁻¹' S) = edgeLaw (fun e : ↑F => π (e : Sym2 V)) S := by
  rw [← Measure.map_apply (measurable_restrictEdge F) hS, map_restrictEdge_edgeMeasure]

/-! ## 3. Internal edge sets, and the window volumes as functions of them -/

/-- The finite set of edges with both endpoints in the finite vertex set `A`. -/
noncomputable def edgeSetIn (A : Finset V) : Finset (Sym2 V) := by
  classical
  exact (A.product A).image (fun p : V × V => s(p.1, p.2))

lemma edgeIn_mem_edgeSetIn {A : Finset V} {e : Sym2 V} (h : EdgeIn (A : Set V) e) :
    e ∈ edgeSetIn A := by
  classical
  obtain ⟨z, hz, w, hw, hzw⟩ := h
  rw [← hzw]
  refine Finset.mem_image.mpr ⟨(z, w), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨by simpa using hz, by simpa using hw⟩

/-- **Locality of the restricted window volume**: extending the restriction of `ω` to the internal
edges of `A` does not change the `A`-restricted volume.  (This is `vol_congr` of `m4`, applied to
the two configurations `ω` and `extendEdge … (restrictEdge … ω)`.) -/
theorem vol_extendEdge_restrictEdge (A : Finset V) (ω : Config V) (u : V) (W : Finset V) :
    vol (A : Set V) ω u W =
      vol (A : Set V) (extendEdge (edgeSetIn A) (restrictEdge (edgeSetIn A) ω)) u W :=
  vol_congr (A := (A : Set V))
    (fun e he => (extendEdge_restrictEdge (F := edgeSetIn A) ω (edgeIn_mem_edgeSetIn he)).symm)
    u W

/-- The same for the window maximum. -/
theorem maxVol_extendEdge_restrictEdge (A : Finset V) (ω : Config V) (W : Finset V) :
    maxVol (A : Set V) ω W =
      maxVol (A : Set V) (extendEdge (edgeSetIn A) (restrictEdge (edgeSetIn A) ω)) W := by
  simp only [maxVol]
  exact Finset.sup_congr rfl fun w _ => vol_extendEdge_restrictEdge A ω w W

/-! ## 4. The per-stage event of the exhaustion, under the finite product law -/

/-- **The per-stage event `{|K_max(W) ∩ A| ≥ λ}` has the finite product law of the internal
edges.** -/
theorem measure_maxVol_event_eq (π : Sym2 V → unitInterval) (A : Finset V) (W : Finset V)
    (lam : ℝ) :
    edgeMeasure π {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A : Set V) ω W} =
      edgeLaw (fun e : ↑(edgeSetIn A) => π (e : Sym2 V))
        {f : Set ↑(edgeSetIn A) |
          ENNReal.ofReal lam ≤ maxVol (A : Set V) (extendEdge (edgeSetIn A) f) W} := by
  have hS : MeasurableSet {f : Set ↑(edgeSetIn A) |
      ENNReal.ofReal lam ≤ maxVol (A : Set V) (extendEdge (edgeSetIn A) f) W} :=
    MeasurableSet.of_discrete
  rw [← measure_restrictEdge_preimage π (edgeSetIn A) hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [maxVol_extendEdge_restrictEdge]

/-- **The per-stage event `{|K_u ∩ A| ≥ λ}` has the finite product law of the internal edges.** -/
theorem measure_vol_event_eq (π : Sym2 V → unitInterval) (A : Finset V) (u : V) (W : Finset V)
    (lam : ℝ) :
    edgeMeasure π {ω : Config V | ENNReal.ofReal lam ≤ vol (A : Set V) ω u W} =
      edgeLaw (fun e : ↑(edgeSetIn A) => π (e : Sym2 V))
        {f : Set ↑(edgeSetIn A) |
          ENNReal.ofReal lam ≤ vol (A : Set V) (extendEdge (edgeSetIn A) f) u W} := by
  have hS : MeasurableSet {f : Set ↑(edgeSetIn A) |
      ENNReal.ofReal lam ≤ vol (A : Set V) (extendEdge (edgeSetIn A) f) u W} :=
    MeasurableSet.of_discrete
  rw [← measure_restrictEdge_preimage π (edgeSetIn A) hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [vol_extendEdge_restrictEdge]

/-! ## 5. The exhaustion passage with `hfin` supplied by the finite product law -/

/-- **Exhaustion passage for (2.8) with the finite-subgraph hypothesis in finite-product form.**

If for every stage `r` the per-scale bound (2.8) holds for the internal edge set of `A r` under the
finite product Bernoulli law of that edge set — which is the finite-graph case of the source, with
the finite graph being the one on the vertex set `A r` — then the countable-graph bound (2.8)
holds for the repository's `|K_max(W)|`.

This is m4's `per_scale_of_finite` with the hypothesis `hfin` discharged through the law
identification of §2, and nothing else.  `lam` is an arbitrary real and `k` an arbitrary natural:
`lam ≥ 1` and `k ≥ 1` belong to the finite-case proof, not to the exhaustion. -/
theorem per_scale_of_finiteEdgeLaw (π : Sym2 V → unitInterval)
    (A : ℕ → Finset V) (hmono : Monotone fun r => (A r : Set V))
    (hcover : Covers fun r => (A r : Set V)) (W : Finset V) {lam : ℝ} {k : ℕ}
    (h : ∀ r : ℕ,
      edgeLaw (fun e : ↑(edgeSetIn (A r)) => π (e : Sym2 V))
          {f : Set ↑(edgeSetIn (A r)) |
            ENNReal.ofReal (3 ^ k * lam) ≤
              maxVol (A r : Set V) (extendEdge (edgeSetIn (A r)) f) W}
        ≤ (edgeLaw (fun e : ↑(edgeSetIn (A r)) => π (e : Sym2 V))
            {f : Set ↑(edgeSetIn (A r)) |
              ENNReal.ofReal lam ≤
                maxVol (A r : Set V) (extendEdge (edgeSetIn (A r)) f) W}) ^ (3 ^ (k - 1) + 1)) :
    edgeMeasure π {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W}
      ≤ (edgeMeasure π {ω : Config V |
            ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^ (3 ^ (k - 1) + 1) := by
  refine per_scale_of_finite hmono hcover W (fun r => ?_)
  rw [measure_maxVol_event_eq π (A r) W (3 ^ k * lam),
    measure_maxVol_event_eq π (A r) W lam]
  exact h r

/-- **Exhaustion passage for (2.9) with the finite-subgraph hypothesis in finite-product form.** -/
theorem per_scale_single_of_finiteEdgeLaw (π : Sym2 V → unitInterval)
    (A : ℕ → Finset V) (hmono : Monotone fun r => (A r : Set V))
    (hcover : Covers fun r => (A r : Set V)) (W : Finset V) (u : V) {lam : ℝ} {k : ℕ}
    (h : ∀ r : ℕ,
      edgeLaw (fun e : ↑(edgeSetIn (A r)) => π (e : Sym2 V))
          {f : Set ↑(edgeSetIn (A r)) |
            ENNReal.ofReal (3 ^ k * lam) ≤
              vol (A r : Set V) (extendEdge (edgeSetIn (A r)) f) u W}
        ≤ (edgeLaw (fun e : ↑(edgeSetIn (A r)) => π (e : Sym2 V))
            {f : Set ↑(edgeSetIn (A r)) |
              ENNReal.ofReal lam ≤
                maxVol (A r : Set V) (extendEdge (edgeSetIn (A r)) f) W}) ^ (3 ^ (k - 1)) *
          edgeLaw (fun e : ↑(edgeSetIn (A r)) => π (e : Sym2 V))
            {f : Set ↑(edgeSetIn (A r)) |
              ENNReal.ofReal lam ≤
                vol (A r : Set V) (extendEdge (edgeSetIn (A r)) f) u W}) :
    edgeMeasure π {ω : Config V |
        ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)}
      ≤ (edgeMeasure π {ω : Config V |
            ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^ (3 ^ (k - 1)) *
          edgeMeasure π {ω : Config V |
            ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  refine per_scale_single_of_finite hmono hcover W u (fun r => ?_)
  rw [measure_vol_event_eq π (A r) u W (3 ^ k * lam),
    measure_maxVol_event_eq π (A r) W lam,
    measure_vol_event_eq π (A r) u W lam]
  exact h r

/-! ## 6. The same for the long-range law `P_β` of the repository -/

/-- **The law identification for `P_β`.**  Under `longRangeMeasure J hJ β`, the joint law of the
edge coordinates in a finite `F` is the finite product law with edge probabilities
`1 - exp (-(β J e))`. -/
theorem map_restrictEdge_longRangeMeasure (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (F : Finset (Sym2 V)) :
    (longRangeMeasure J hJ β).map (restrictEdge (V := V) F) =
      edgeLaw (fun e : ↑F => bernoulliEdgeProb J hJ β (e : Sym2 V)) := by
  rw [longRangeMeasure]
  exact map_restrictEdge_edgeMeasure (bernoulliEdgeProb J hJ β) F

end Exhaustion

end PercLib.CriticalLRP
