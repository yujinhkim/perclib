/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m2/MarkedP1.lean.
-/

/-
Marked base factor of Lemma I.4.17 at `p = 1`, in the canonical model.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17 (p. 45).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Base.Depth
public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.BK.BoolMeasure
public import PercLib.CriticalLRP.CountableProduct.Base

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP
namespace MarkedP1

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The deterministic branch-point decomposition -/

/-- The two pieces of a split of a geodesic are geodesics. -/
theorem split_len {G : SimpleGraph V} {a b y : V} {R : G.Walk a b}
    (hlen : R.length = G.dist a b)
    {R₁ : G.Walk a y} {R₂ : G.Walk y b} (h : R = R₁.append R₂) :
    R₁.length = G.dist a y ∧ R₂.length = G.dist y b := by
  have hlen' : R.length = R₁.length + R₂.length := by
    rw [h, SimpleGraph.Walk.length_append]
  have h1 : G.dist a y ≤ R₁.length := SimpleGraph.dist_le R₁
  have h2 : G.dist y b ≤ R₂.length := SimpleGraph.dist_le R₂
  have h3 : G.dist a b ≤ G.dist a y + G.dist y b := R₁.reachable.dist_triangle_left b
  constructor <;> omega

/-- The edge set of an open walk witnesses the connection of its endpoints. -/
theorem connects_of_walk_edges {ω : Config V} {a b : V} (p : (openGraph ω).Walk a b) :
    Connects ((p.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) a b := by
  obtain ⟨q, hq⟩ := exists_walk_top_of_walk p
  refine pathConnects_iff.mp ⟨q, fun e he => ?_⟩
  rw [hq] at he
  exact List.mem_toFinset.mpr he

/-- Edges of an open walk are open. -/
theorem walk_edges_subset {ω : Config V} {a b : V} (p : (openGraph ω).Walk a b) :
    ((p.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω := by
  intro e he
  exact edgeSet_openGraph_subset (SimpleGraph.Walk.edges_subset_edgeSet p (List.mem_toFinset.mp he))

/-- **Branch-point decomposition with three edge-disjoint witnesses.**  If `x` is connected to
both `u` and `w` in `ω`, then there is a vertex `v` and pairwise edge-disjoint open edge sets
witnessing `x ↔ v`, `v ↔ u` and `v ↔ w`.  The case `v = x` is allowed: the witness for `x ↔ x`
is then empty, which is the paper's two-term alternative. -/
theorem branch_three {ω : Config V} {x u w : V}
    (h1 : Connects ω x u) (h2 : Connects ω x w) :
    ∃ (v : V) (W₀ WA WB : Finset (Sym2 V)),
      ((W₀ : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω ∧
      ((WA : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω ∧
      ((WB : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω ∧
      Disjoint W₀ WA ∧ Disjoint W₀ WB ∧ Disjoint WA WB ∧
      Connects ((W₀ : Finset (Sym2 V)) : Set (Sym2 V)) x v ∧
      Connects ((WA : Finset (Sym2 V)) : Set (Sym2 V)) v u ∧
      Connects ((WB : Finset (Sym2 V)) : Set (Sym2 V)) v w := by
  classical
  obtain ⟨P, hPpath, hPlen⟩ := h1.exists_path_of_dist
  obtain ⟨Q, hQpath, hQlen⟩ := h2.exists_path_of_dist
  have hPnd : P.support.Nodup := SimpleGraph.Walk.isPath_def P |>.mp hPpath
  have hQnd : Q.support.Nodup := SimpleGraph.Walk.isPath_def Q |>.mp hQpath
  -- the common vertices
  set S : Finset V := P.support.toFinset ∩ Q.support.toFinset with hS
  have hxS : x ∈ S := by
    rw [hS, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset]
    exact ⟨SimpleGraph.Walk.start_mem_support P, SimpleGraph.Walk.start_mem_support Q⟩
  obtain ⟨v, hvS, hvmax⟩ :=
    Finset.exists_max_image S (fun y => (openGraph ω).dist x y) ⟨x, hxS⟩
  have hvP : v ∈ P.support :=
    (Finset.mem_inter.mp (hS ▸ hvS)).1 |> List.mem_toFinset.mp
  have hvQ : v ∈ Q.support :=
    (Finset.mem_inter.mp (hS ▸ hvS)).2 |> List.mem_toFinset.mp
  -- split the two geodesics at `v`
  obtain ⟨B, A, hBpath, hApath, hPBA⟩ := (hPpath.mem_support_iff_exists_append).mp hvP
  obtain ⟨D, C, hDpath, hCpath, hQDC⟩ := (hQpath.mem_support_iff_exists_append).mp hvQ
  obtain ⟨hBlen, hAlen⟩ := split_len hPlen hPBA
  obtain ⟨hDlen, hClen⟩ := split_len hQlen hQDC
  -- membership of the pieces in the two geodesics
  have hA_memP : ∀ y ∈ A.support, y ∈ P.support := by
    intro y hy
    rw [hPBA, SimpleGraph.Walk.support_append]
    rw [← SimpleGraph.Walk.cons_tail_support A] at hy
    rcases List.mem_cons.mp hy with h | h
    · exact List.mem_append.mpr (Or.inl (h ▸ SimpleGraph.Walk.end_mem_support B))
    · exact List.mem_append.mpr (Or.inr h)
  have hB_memP : ∀ y ∈ B.support, y ∈ P.support := by
    intro y hy
    rw [hPBA, SimpleGraph.Walk.support_append]
    exact List.mem_append.mpr (Or.inl hy)
  have hC_memQ : ∀ y ∈ C.support, y ∈ Q.support := by
    intro y hy
    rw [hQDC, SimpleGraph.Walk.support_append]
    rw [← SimpleGraph.Walk.cons_tail_support C] at hy
    rcases List.mem_cons.mp hy with h | h
    · exact List.mem_append.mpr (Or.inl (h ▸ SimpleGraph.Walk.end_mem_support D))
    · exact List.mem_append.mpr (Or.inr h)
  -- the geodesic betweenness facts on the pieces
  have hAbtw : ∀ y ∈ A.support,
      (openGraph ω).dist x y = (openGraph ω).dist x v + (openGraph ω).dist v y := by
    intro y hy
    obtain ⟨A₁, A₂, hA₁, hA₂, hAA⟩ := hApath.mem_support_iff_exists_append.mp hy
    obtain ⟨hA₁len, -⟩ := split_len hAlen hAA
    have hPsplit : P = (B.append A₁).append A₂ := by
      rw [hPBA, hAA, SimpleGraph.Walk.append_assoc]
    obtain ⟨hkey, -⟩ := split_len hPlen hPsplit
    calc (openGraph ω).dist x y = (B.append A₁).length := hkey.symm
      _ = B.length + A₁.length := SimpleGraph.Walk.length_append B A₁
      _ = (openGraph ω).dist x v + (openGraph ω).dist v y := by rw [hBlen, hA₁len]
  have hCbtw : ∀ y ∈ C.support,
      (openGraph ω).dist x y = (openGraph ω).dist x v + (openGraph ω).dist v y := by
    intro y hy
    obtain ⟨C₁, C₂, hC₁, hC₂, hCC⟩ := hCpath.mem_support_iff_exists_append.mp hy
    obtain ⟨hC₁len, -⟩ := split_len hClen hCC
    have hQsplit : Q = (D.append C₁).append C₂ := by
      rw [hQDC, hCC, SimpleGraph.Walk.append_assoc]
    obtain ⟨hkey, -⟩ := split_len hQlen hQsplit
    calc (openGraph ω).dist x y = (D.append C₁).length := hkey.symm
      _ = D.length + C₁.length := SimpleGraph.Walk.length_append D C₁
      _ = (openGraph ω).dist x v + (openGraph ω).dist v y := by rw [hDlen, hC₁len]
  have hBbtw : ∀ y ∈ B.support,
      (openGraph ω).dist x y + (openGraph ω).dist y v = (openGraph ω).dist x v := by
    intro y hy
    obtain ⟨B₁, B₂, hB₁, hB₂, hBB⟩ := hBpath.mem_support_iff_exists_append.mp hy
    obtain ⟨hB₁len, hB₂len⟩ := split_len hBlen hBB
    calc (openGraph ω).dist x y + (openGraph ω).dist y v
        = B₁.length + B₂.length := by rw [hB₁len, hB₂len]
      _ = B.length := by rw [hBB, SimpleGraph.Walk.length_append]
      _ = (openGraph ω).dist x v := hBlen
  -- the only vertex common to the left part and the right part is `v`
  have honly : ∀ y ∈ B.support, y ∈ C.support → y = v := by
    intro y hyB hyC
    have hdB := hBbtw y hyB
    have hdC := hCbtw y hyC
    have hd : (openGraph ω).dist v y = 0 := by omega
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hd with h | h
    · exact h.symm
    · exact absurd (hCpath.mem_support_iff_exists_append.mp hyC).choose.reachable h
  have honlyA : ∀ y ∈ A.support, y ∈ C.support → y = v := by
    intro y hyA hyC
    have hmem : y ∈ S := by
      rw [hS, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset]
      exact ⟨hA_memP y hyA, hC_memQ y hyC⟩
    have hle : (openGraph ω).dist x y ≤ (openGraph ω).dist x v := hvmax y hmem
    have hdC := hCbtw y hyC
    have hd : (openGraph ω).dist v y = 0 := by omega
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hd with h | h
    · exact h.symm
    · exact absurd (hCpath.mem_support_iff_exists_append.mp hyC).choose.reachable h
  -- edge-disjointness
  have hBAnd : P.edges.Nodup := SimpleGraph.Walk.edges_nodup_of_support_nodup hPnd
  have hBA : Disjoint B.edges.toFinset A.edges.toFinset := by
    refine Finset.disjoint_left.mpr fun e heB heA => ?_
    have hdisj : B.edges.Disjoint A.edges := by
      refine List.Nodup.disjoint ?_
      rw [← SimpleGraph.Walk.edges_append, ← hPBA]
      exact hBAnd
    exact (hdisj (List.mem_toFinset.mp heB)) (List.mem_toFinset.mp heA)
  have hBC : Disjoint B.edges.toFinset C.edges.toFinset := by
    refine Finset.disjoint_left.mpr fun e heB heC => ?_
    induction e using Sym2.ind with
    | h s t =>
    have hBs : s ∈ B.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges B (by
      simpa using List.mem_toFinset.mp heB)
    have hBt : t ∈ B.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges B (by
      simpa using List.mem_toFinset.mp heB)
    have hCs : s ∈ C.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges C (by
      simpa using List.mem_toFinset.mp heC)
    have hCt : t ∈ C.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges C (by
      simpa using List.mem_toFinset.mp heC)
    have hsv : s = v := honly s hBs hCs
    have htv : t = v := honly t hBt hCt
    have hadj : (openGraph ω).Adj s t :=
      SimpleGraph.Walk.adj_of_mem_edges B (by simpa using List.mem_toFinset.mp heB)
    rw [hsv, htv] at hadj
    exact hadj.ne rfl
  have hAC : Disjoint A.edges.toFinset C.edges.toFinset := by
    refine Finset.disjoint_left.mpr fun e heA heC => ?_
    induction e using Sym2.ind with
    | h s t =>
    have hAs : s ∈ A.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges A (by
      simpa using List.mem_toFinset.mp heA)
    have hAt : t ∈ A.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges A (by
      simpa using List.mem_toFinset.mp heA)
    have hCs : s ∈ C.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges C (by
      simpa using List.mem_toFinset.mp heC)
    have hCt : t ∈ C.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges C (by
      simpa using List.mem_toFinset.mp heC)
    have hsv : s = v := honlyA s hAs hCs
    have htv : t = v := honlyA t hAt hCt
    have hadj : (openGraph ω).Adj s t :=
      SimpleGraph.Walk.adj_of_mem_edges A (by simpa using List.mem_toFinset.mp heA)
    rw [hsv, htv] at hadj
    exact hadj.ne rfl
  refine ⟨v, B.edges.toFinset, A.edges.toFinset, C.edges.toFinset,
    walk_edges_subset B, walk_edges_subset A, walk_edges_subset C, hBA, hBC, hAC,
    connects_of_walk_edges B, connects_of_walk_edges A, connects_of_walk_edges C⟩


/-! ## 2. The iterated BK bound for the two-arm marked event -/

/-- **The marked moment at `p = 1` is bounded by the polygon/two-point sum.**  In the canonical
model, `E[|K_x| 1(w ∈ K_x)] ≤ χ · ∑_v T(x,v) T(v,w)`, `χ` the constant row sum of the two-point
function (transitivity).  The proof is the `p = 1` case of the tree-graph expansion of Lemma
I.4.17: `branch_three` turns `{u ∈ K_x, w ∈ K_x}` into a three-fold disjoint occurrence through a
branch point `v`, the iterated BK inequality bounds its probability by the product of the three
two-point functions, and the free sum over the arm `u` is evaluated by the constant row sum. -/
theorem jointPow_one_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x w : V) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, (edgeMeasure π) (connSet v y) = χ) :
    I417Gen.jointPow π x 1 w ≤
      χ * (∑' v, (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v w)) := by
  classical
  have hstep1 : I417Gen.jointPow π x 1 w =
      ∑' u : V, (edgeMeasure π) (I417A.labelEvent x (fun _ : Fin 1 => u) ∩ connSet x w) := by
    rw [← I417Gen.tsum_labelEvent_inter π x 1 w]
    let e : V ≃ (Fin 1 → V) :=
      { toFun := fun u _ => u, invFun := fun f => f 0,
        left_inv := fun _ => rfl,
        right_inv := fun f => by funext i; exact (congrArg f (Subsingleton.elim i 0)).symm }
    exact (Equiv.tsum_eq e (fun f : Fin 1 → V =>
      (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x w))).symm
  rw [hstep1]
  -- the per-arm bound
  have hterm : ∀ u : V, (edgeMeasure π) (I417A.labelEvent x (fun _ : Fin 1 => u) ∩ connSet x w) ≤
      ∑' v, (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
        (edgeMeasure π) (connSet v w) := by
    intro u
    -- covering by the three-fold disjoint occurrence
    have hsub : I417A.labelEvent x (fun _ : Fin 1 => u) ∩ connSet x w ⊆
        ⋃ v : V, Percolation.DisjointOccurrenceList
          [connSet x v, connSet v u, connSet v w] := by
      rintro ω ⟨hu, hw⟩
      have hu' : Connects ω x u := mem_cluster_iff.mp (hu 0)
      obtain ⟨v, W₀, WA, WB, hW₀, hWA, hWB, hd0A, hd0B, hdAB, hc0, hcA, hcB⟩ :=
        branch_three hu' hw
      refine Set.mem_iUnion.mpr ⟨v, W₀, WA ∪ WB, hW₀, ?_, ?_, hc0, ?_⟩
      · rw [Finset.coe_union]
        exact Set.union_subset hWA hWB
      · refine Finset.disjoint_left.mpr fun e he0 heU => ?_
        rcases Finset.mem_union.mp heU with h | h
        · exact Finset.disjoint_left.mp hd0A he0 h
        · exact Finset.disjoint_left.mp hd0B he0 h
      · refine ⟨WA, WB, by rw [Finset.coe_union]; exact Set.subset_union_left,
          by rw [Finset.coe_union]; exact Set.subset_union_right, hdAB, hcA, ?_⟩
        exact ⟨WB, ∅, by simp, by simp,
          Finset.disjoint_empty_right WB, hcB, trivial⟩
    refine le_trans (measure_mono hsub) (le_trans (measure_iUnion_le _) ?_)
    refine ENNReal.tsum_le_tsum fun v => ?_
    -- the iterated BK inequality
    have hupper : IsUpperSet (Percolation.DisjointOccurrenceList
        [connSet x v, connSet v u, connSet v w]) :=
      Percolation.disjointOccurrenceList_upper _
    have hfin : Percolation.FiniteWitness (Percolation.DisjointOccurrenceList
        [connSet x v, connSet v u, connSet v w]) :=
      Percolation.disjointOccurrenceList_finiteWitness _
    have hbkreal : (edgeMeasure π).real (Percolation.DisjointOccurrenceList
          [connSet x v, connSet v u, connSet v w]) ≤
        (edgeMeasure π).real (connSet x v) * (edgeMeasure π).real (connSet v u) *
          (edgeMeasure π).real (connSet v w) := by
      have h := Percolation.bk_list π hπ
        [connSet x v, connSet v u, connSet v w]
        (by
          intro A hA
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
          rcases hA with rfl | rfl | rfl
          · exact isUpper_connSet x v
          · exact isUpper_connSet v u
          · exact isUpper_connSet v w)
        (by
          intro A hA
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
          rcases hA with rfl | rfl | rfl
          · exact finiteWitness_connSet x v
          · exact finiteWitness_connSet v u
          · exact finiteWitness_connSet v w)
      simpa [List.prod_cons, List.prod_nil, mul_assoc, edgeMeasure_eq_edgeLaw] using h
    -- pass from `ℝ` to `ℝ≥0∞`
    have hne : ∀ s : Set (Config V), (edgeMeasure π) s ≠ ⊤ := fun s => measure_ne_top _ s
    calc (edgeMeasure π) (Percolation.DisjointOccurrenceList
          [connSet x v, connSet v u, connSet v w])
        = ENNReal.ofReal ((edgeMeasure π).real (Percolation.DisjointOccurrenceList
            [connSet x v, connSet v u, connSet v w])) := by
          rw [Measure.real_def, ENNReal.ofReal_toReal (hne _)]
      _ ≤ ENNReal.ofReal ((edgeMeasure π).real (connSet x v) *
            (edgeMeasure π).real (connSet v u) * (edgeMeasure π).real (connSet v w)) :=
          ENNReal.ofReal_le_ofReal hbkreal
      _ = (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
            (edgeMeasure π) (connSet v w) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            Measure.real_def, Measure.real_def, Measure.real_def,
            ENNReal.ofReal_toReal (hne _), ENNReal.ofReal_toReal (hne _),
            ENNReal.ofReal_toReal (hne _)]
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  -- evaluate the free sums
  have hswap : (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x v) *
        (edgeMeasure π) (connSet v u) * (edgeMeasure π) (connSet v w)) =
      ∑' v : V, (edgeMeasure π) (connSet x v) *
        ((∑' u : V, (edgeMeasure π) (connSet v u)) * (edgeMeasure π) (connSet v w)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun v => ?_
    have hpt : ∀ u : V, (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
        (edgeMeasure π) (connSet v w) = (edgeMeasure π) (connSet x v) *
          ((edgeMeasure π) (connSet v u) * (edgeMeasure π) (connSet v w)) :=
      fun u => mul_assoc _ _ _
    rw [tsum_congr hpt, ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
  rw [hswap]
  have h2 : ∀ v : V, (edgeMeasure π) (connSet x v) *
      ((∑' u : V, (edgeMeasure π) (connSet v u)) * (edgeMeasure π) (connSet v w)) =
      χ * ((edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v w)) := by
    intro v
    rw [hχ v, ← mul_assoc, mul_comm ((edgeMeasure π) (connSet x v)) χ, mul_assoc]
  rw [tsum_congr h2, ENNReal.tsum_mul_left]


/-! ## 3. The two-point comparison and the final bound -/

/-- `iterPow k 1 = k`. -/
theorem iterPow_one (k : V → V → ℝ≥0∞) (v w : V) : I417Base.iterPow k 1 v w = k v w := by
  have h : I417Base.iterPow k 1 = I417Base.step k (I417Base.iterPow k 0) := rfl
  rw [h, I417Base.step]
  refine (tsum_eq_single w) ?_ |>.trans ?_
  · intro u hu
    simp [I417Base.iterPow, hu]
  · simp [I417Base.iterPow]

/-- **Monotonicity of the two-point function along a connection**: `T(x,a) T(a,w) ≤ T(x,w)`.
This is Harris/FKG for the two increasing connection events together with transitivity of
connection. It is kept as a separate two-point comparison; the marked bound below is proved by
threefold BK, not by replacing the marked moment with a single two-point factor. -/
theorem tau_mul_le (π : Sym2 V → unitInterval) (x a w : V) :
    (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a w) ≤
      (edgeMeasure π) (connSet x w) := by
  have hne : ∀ s : Set (Config V), (edgeMeasure π) s ≠ ⊤ := fun s => measure_ne_top _ s
  have hreal : (edgeMeasure π).real (connSet x a) * (edgeMeasure π).real (connSet a w) ≤
      (edgeMeasure π).real (connSet x w) := by
    have hfkg := Percolation.association_edge_finiteWitness π (connSet x a) (connSet a w)
      (isUpper_connSet x a) (isUpper_connSet a w)
      (finiteWitness_connSet x a) (finiteWitness_connSet a w)
    have hsub : connSet x a ∩ connSet a w ⊆ connSet x w := by
      rintro ω ⟨h1, h2⟩
      exact connects_trans h1 h2
    have hfkg' : (edgeMeasure π).real (connSet x a) * (edgeMeasure π).real (connSet a w) ≤
        (edgeMeasure π).real (connSet x a ∩ connSet a w) := by
      simpa only [edgeMeasure_eq_edgeLaw] using hfkg
    exact le_trans hfkg' (measureReal_mono hsub)
  calc (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a w)
      = ENNReal.ofReal ((edgeMeasure π).real (connSet x a) *
          (edgeMeasure π).real (connSet a w)) := by
        rw [ENNReal.ofReal_mul (by positivity), Measure.real_def, Measure.real_def,
          ENNReal.ofReal_toReal (hne _), ENNReal.ofReal_toReal (hne _)]
    _ ≤ ENNReal.ofReal ((edgeMeasure π).real (connSet x w)) := ENNReal.ofReal_le_ofReal hreal
    _ = (edgeMeasure π) (connSet x w) := by
        rw [Measure.real_def, ENNReal.ofReal_toReal (hne _)]

/-- `iterPow k 2 v w = ∑_u k v u * k u w`: the two-step power of a kernel. -/
theorem iterPow_two (k : V → V → ℝ≥0∞) (v w : V) :
    I417Base.iterPow k 2 v w = ∑' u : V, k v u * k u w := by
  have h : I417Base.iterPow k 2 = I417Base.step k (I417Base.iterPow k 1) := rfl
  rw [h, I417Base.step]
  exact tsum_congr fun u => by rw [iterPow_one]

/-- **The marked base factor at `p = 1`**, in polygon form:
`E[|K_x| 1(w ∈ K_x)] ≤ χ · T²(x,w)`, `χ` the constant row sum of the two-point function and
`T²` the square of the two-point matrix.

This is the `p = 1` marked tree-graph bound of Lemma I.4.17 in the form the paper's marked diagram
family produces: with `p = 1` the two-leaf diagrams have their marked leaf at tree depth `2`, so
`I417Base.marked_diagram_by_depth` evaluates the family `twoLeafMarked` to
`2 · χ^(2·1+1-2) · T²(x,w) = 2 χ T²(x,w)`, which dominates the bound proved here.  (The `p = 1`
case is *not* bounded by `χ² T(x,w)`: in a line of length `L`, `E[|K_x| 1(w ∈ K_x)]` is of order
`L p^L` while `χ² T(x,w)` is of order `p^L`, so only the depth-`2` diagrams can carry it.) -/
theorem jointPow_one_le_polygon (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x w : V)
    (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y, (edgeMeasure π) (connSet v y) = χ) :
    I417Gen.jointPow π x 1 w ≤
      χ * I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) 2 x w := by
  refine le_trans (jointPow_one_le π hπ x w χ hχ) ?_
  exact le_of_eq (by rw [iterPow_two])

end MarkedP1
end PercLib.CriticalLRP
