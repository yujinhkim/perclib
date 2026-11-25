/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Fails.lean ; module path rewritten only.
-/

/-
# The diagonal event is *not* an event of the base configuration

The printed proof of Lemma I.4.17 writes

  `E|K|^p E|K|^q = ∑_{x_i,y_i} P(x₁,…,x_p ∈ Kx, y₁,…,y_q ∈ K̃y)`

and then treats the two conditions as independent ("since the events defining the conditions on
`Kx` and `K̃y` in the last line are independent").  The condition on `K̃y` is *not* a condition on
the base configuration `ω₁` alone: `y₁ ∈ K̃y` is a statement about the fresh copy that also depends
on `ω₁` through the avoiding set.

Concretely, this file records a configuration pair `(ω₂, ω₁)` on four vertices for which

* `y = 1 ∉ Kx(ω₁)` with `x = 0`, and `x₁ = x₂ = 0 ∈ Kx(ω₁)` — so the pair lies in the diagonal
  event `diagSet 0 1 0 0 2`;
* `y₁ = 2 ∉ Ky(ω₁)` — so the same pair lies *outside* the printed event `{y₁ ∈ Ky}` of the base
  configuration.

Hence `diagSet` is not contained in the base-configuration event `{y₁ ∈ Ky(ω₁)}`, and no event
identity can replace the restored cluster `K̃y` by the base cluster `Ky` — in either direction
(`Ky ⊄ K̃y` is `not_cluster_subset_forceOn_compl`; here `K̃y ⊄ Ky` on `{y ∉ Kx}`).  This does not
affect the *statement* of the printed `p = 2`, `q = 1` display, only the printed derivation; the
repair is `I417.prodSet_subset`, which uses the correct event `diagSet` together with the marked
crossing alternative.

No `sorry`, no custom axioms; no definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fails.Defs

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

-- The two configuration definitions live in `Fails/Defs.lean`.

theorem not_mem_baseCfg_iff (e : Sym2 (Fin 4)) : e ∈ baseCfg ↔ e = s(2, 3) := by
  simp [baseCfg]

theorem mem_freshCfg_iff (e : Sym2 (Fin 4)) : e ∈ freshCfg ↔ e = s(1, 2) := by
  simp [freshCfg]

/-- Vertex `1` is isolated in the base configuration, so `K_1 = {1}`. -/
theorem cluster_baseCfg_one : cluster baseCfg (1 : Fin 4) = {1} := by
  refine cluster_eq_singleton_of_isolated fun u => ?_
  rw [not_mem_baseCfg_iff]
  revert u
  decide

/-- Vertex `0` is isolated in the base configuration, so `K_0 = {0}`. -/
theorem cluster_baseCfg_zero : cluster baseCfg (0 : Fin 4) = {0} := by
  refine cluster_eq_singleton_of_isolated fun u => ?_
  rw [not_mem_baseCfg_iff]
  revert u
  decide

/-- In the base configuration `y₁ = 2` does **not** lie in the cluster of `y = 1`. -/
theorem two_not_mem_cluster_baseCfg_one : (2 : Fin 4) ∉ cluster baseCfg 1 := by
  rw [cluster_baseCfg_one]
  simp

/-- `y = 1 ∉ K_0` in the base configuration. -/
theorem one_not_mem_cluster_baseCfg_zero : (1 : Fin 4) ∉ cluster baseCfg 0 := by
  rw [cluster_baseCfg_zero]
  simp

/-- The fresh edge `{1,2}` is an open walk from `1` to `2` avoiding `K_0(ω₁) = {0}`. -/
theorem two_mem_cluster_restored_one :
    (2 : Fin 4) ∈ cluster (restoreMap (0 : Fin 4) (freshCfg, baseCfg)) 1 := by
  rw [restoreMap]
  refine mem_cluster_iff.mp ?_
  refine (mem_cluster_forceOn_compl_iff (ω := baseCfg) (ω' := freshCfg) (o := (0 : Fin 4))
    (y := (1 : Fin 4)) (z := (2 : Fin 4)) one_not_mem_cluster_baseCfg_zero).mpr ⟨?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.cons (by rw [SimpleGraph.top_adj]; exact (by decide : (1 : Fin 4) ≠ 2))
      SimpleGraph.Walk.nil
  · intro e he
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_singleton] at he
    rw [he, mem_freshCfg_iff]
  · intro e he v hv
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_singleton] at he
    rw [he] at hv
    rw [cluster_baseCfg_zero]
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp

/-- **The diagonal event is not a base-configuration event.**  The pair `(freshCfg, baseCfg)`
lies in `diagSet 0 1 0 0 2` — `x₁ = x₂ = 0 ∈ Kx(ω₁)`, `y = 1 ∉ Kx(ω₁)`, `y₁ = 2 ∈ K̃y` — while
`y₁ = 2 ∉ Ky(ω₁)`.

So the printed identification of `P(x₁,x₂ ∈ Kx, y₁ ∈ K̃y)` with a probability involving the base
cluster `Ky` is not an identity, and the printed "some `yᵢ ∉ Ky`" alternative is not the event the
coupling produces. -/
theorem diagSet_not_base :
    (freshCfg, baseCfg) ∈ diagSet (0 : Fin 4) 1 0 0 2 ∧ (2 : Fin 4) ∉ cluster baseCfg 1 := by
  refine ⟨?_, two_not_mem_cluster_baseCfg_one⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact connects_refl baseCfg 0
  · exact connects_refl baseCfg 0
  · intro h
    exact one_not_mem_cluster_baseCfg_zero (mem_cluster_iff.mpr h)
  · rw [connSet]
    exact mem_cluster_iff.mp two_mem_cluster_restored_one

end PercLib.CriticalLRP.I417
