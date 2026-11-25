/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# A genuine finite-cutoff long-range percolation model on the box `B_n`

Member m2, swarm direction (E): bridge the abstract finite model of
`VolumeMoments/I58Remainder.lean` to a concrete finite active-edge law with
real clusters, real restored clusters and real finite expectations.

Model (stated exactly, see the fidelity report): the vertex set is the box
`B_n = box d n = {x in Z^d : ||x||_infty <= n}` as a finite type, the edge set
is the set of *unordered* pairs of distinct vertices of `B_n`, each represented
once by the ordered pair `(x,y)` with `x < y` in the (arbitrary, but fixed)
lifted lexicographic order on `B_n`.  The law of a configuration
`omega : Configuration (ES d n) = Finset (ES d n)` is the independent Bernoulli
law `configurationLaw p` with `p e = 1 - exp (-(beta * J (src e, tgt e)))`.
This is the box (finite-volume) version of Hutchcroft's long-range percolation
with a kernel `J`; in particular, instantiating `J` with the paper's cut-off
kernel `cutoffKernel K rho r` (Definition I.1.5, `KernelGeometry.lean`) gives
edges of weight `1(0 < ||x-y|| <= r) (J(||x-y||) - J(r))`, exactly as in the
paper, with all `J_r`-edges of length `> r` open with probability `0`.

What is *not* claimed: `K` here is the cluster of the origin **inside `B_n`**
(the standard finite-volume cluster), not the infinite-lattice cluster of the
paper; and no expectation identity of I.5.7/I.5.8 is proved.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.FiniteBernoulli
public import PercLib.CriticalLRP.FiniteGraphCluster
public import PercLib.CriticalLRP.LatticeGeometry
public import PercLib.CriticalLRP.KernelGeometry
public import PercLib.CriticalLRP.VolumeMoments.I58Model

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset
open PercLib.CriticalLRP.FiniteVolume

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace PercLib.CriticalLRP.M2

variable {d : ℕ}

/-! ## 1. Sites: the box `B_n`, and its complete edge set -/

/-- The finite vertex set `B_n = {x in Z^d : ||x||_infty <= n}`. -/
abbrev V (d n : ℕ) : Type := {x : Fin d → ℤ // x ∈ box d n}

/-- An arbitrary injective numerical code of the box, used only to name each
unordered pair of distinct vertices once.  No probability depends on it. -/
noncomputable def code {d n : ℕ} (x : V d n) : ℕ := (Fintype.equivFin (V d n) x : ℕ)

theorem code_injective {d n : ℕ} : Function.Injective (code (d := d) (n := n)) := by
  intro x y h
  have h' : (Fintype.equivFin (V d n) x : ℕ) = (Fintype.equivFin (V d n) y : ℕ) := h
  have h'' : Fintype.equivFin (V d n) x = Fintype.equivFin (V d n) y := by
    exact Fin.val_injective h'
  exact (Fintype.equivFin (V d n)).injective h''

/-- The edge set: unordered pairs of distinct vertices of `B_n`, represented by
the ordered pair whose code increases. -/
abbrev ES (d n : ℕ) : Type := {p : V d n × V d n // code p.1 < code p.2}

/-- First endpoint. -/
def src {d n : ℕ} (e : ES d n) : V d n := e.1.1

/-- Second endpoint. -/
def tgt {d n : ℕ} (e : ES d n) : V d n := e.1.2

theorem code_src_lt_tgt {d n : ℕ} (e : ES d n) : code (src e) < code (tgt e) := e.2

theorem src_ne_tgt {d n : ℕ} (e : ES d n) : src e ≠ tgt e := by
  intro h
  have h' := code_src_lt_tgt e
  rw [h] at h'
  exact lt_irrefl _ h'

/-- The edge joining `x` and `y` when `code x < code y`. -/
def pairEdge {d n : ℕ} (x y : V d n) (h : code x < code y) : ES d n := ⟨(x, y), h⟩

@[simp] theorem src_pairEdge {d n : ℕ} (x y : V d n) (h : code x < code y) :
    src (pairEdge x y h) = x := rfl

@[simp] theorem tgt_pairEdge {d n : ℕ} (x y : V d n) (h : code x < code y) :
    tgt (pairEdge x y h) = y := rfl

/-- The edge set is exactly the complete graph on `B_n`: every two distinct
vertices are the two endpoints of an edge, in one of the two orders. -/
theorem exists_edge_of_ne {d n : ℕ} {x y : V d n} (h : x ≠ y) :
    (∃ e : ES d n, src e = x ∧ tgt e = y) ∨ (∃ e : ES d n, src e = y ∧ tgt e = x) := by
  have hc : code x ≠ code y := fun hc => h (code_injective hc)
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · exact Or.inl ⟨pairEdge x y hlt, rfl, rfl⟩
  · exact Or.inr ⟨pairEdge y x hgt, rfl, rfl⟩

/-! ## 2. Genuine clusters: the open subgraph and its components

`cl omega u` is the `FiniteVolume.cluster` of `u` in the open subgraph with
edge set `omega`: the genuine cluster of `u`.  `Ksite` maps it into `Z^d`
(the `I58.Site d` type of `I58Remainder`). -/

/-- The genuine cluster of `u` in the configuration `omega`. -/
noncomputable def cl {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) : Finset (V d n) :=
  cluster src tgt ω u

theorem mem_cl {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n} :
    v ∈ cl ω u ↔ Conn src tgt ω u v := by
  rw [cl, mem_cluster]

theorem self_mem_cl {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) : u ∈ cl ω u := by
  rw [mem_cl]; exact conn_refl src tgt ω u

theorem cl_eq_of_conn {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n}
    (h : Conn src tgt ω u v) : cl ω u = cl ω v := by
  rw [cl, cl]; exact cluster_eq_of_conn h

theorem cl_eq_iff {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n} :
    cl ω u = cl ω v ↔ Conn src tgt ω u v := by
  constructor
  · intro h
    have hv : u ∈ cl ω v := h ▸ self_mem_cl ω u
    rw [mem_cl] at hv
    exact conn_symm hv
  · exact cl_eq_of_conn

/-- Clusters are monotone in the configuration. -/
theorem cl_mono {d n : ℕ} {ω ω' : Configuration (ES d n)} (h : ω ⊆ ω') (u : V d n) :
    cl ω u ⊆ cl ω' u := by
  intro v hv
  rw [mem_cl] at hv ⊢
  exact conn_mono h hv

/-- Distinct clusters are disjoint: a vertex in both would connect `u` to `v`. -/
theorem cl_disjoint {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n}
    (h : ¬ Conn src tgt ω u v) : Disjoint (cl ω u) (cl ω v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_cl] at hx hx'
  exact h (conn_symm (hx'.trans (conn_symm hx)))

/-- On the event `y notin K`, the clusters of `u` and `v` are disjoint, hence
their cardinalities add.  This is the set-theoretic content of the paper's
`1(y notin K) |K| |K_y|`. -/
theorem card_union_cl_of_not_conn {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n}
    (h : ¬ Conn src tgt ω u v) :
    (cl ω u ∪ cl ω v).card = (cl ω u).card + (cl ω v).card := by
  rw [Finset.card_union_of_disjoint (cl_disjoint h)]

theorem card_cl_pos {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) :
    0 < (cl ω u).card :=
  Finset.card_pos.mpr ⟨u, self_mem_cl ω u⟩

/-! ### The same cluster seen inside `Z^d` -/

/-- The cluster of `u`, as a finite set of lattice sites (`I58.Site d`). -/
noncomputable def Ksite {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) :
    Finset (I58.Site d) := (cl ω u).image Subtype.val

theorem card_Ksite {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) :
    (Ksite ω u).card = (cl ω u).card :=
  Finset.card_image_of_injective _ Subtype.coe_injective

theorem mem_Ksite {d n : ℕ} {ω : Configuration (ES d n)} {u : V d n} :
    (Subtype.val u) ∈ Ksite ω u :=
  Finset.mem_image.mpr ⟨u, self_mem_cl ω u, rfl⟩

theorem Ksite_mono {d n : ℕ} {ω ω' : Configuration (ES d n)} (h : ω ⊆ ω') (u : V d n) :
    Ksite ω u ⊆ Ksite ω' u := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨v, cl_mono h u hv, rfl⟩

/-- Disjointness survives the injection `V d n -> Z^d`. -/
theorem Ksite_disjoint {d n : ℕ} {ω : Configuration (ES d n)} {u v : V d n}
    (h : ¬ Conn src tgt ω u v) : Disjoint (Ksite ω u) (Ksite ω v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hEq⟩ := Finset.mem_image.mp hx'
  have : b = a := Subtype.coe_injective hEq
  exact Finset.disjoint_left.mp (cl_disjoint h) ha (this ▸ hb)

/-- The cluster of `u` viewed in `Z^d` is contained in the box. -/
theorem Ksite_subset_box {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) :
    Ksite ω u ⊆ box d n := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact v.2

/-- Every vertex of the box is the image of a vertex of `V d n`. -/
theorem image_univ_val {d n : ℕ} : (univ : Finset (V d n)).image Subtype.val = box d n := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
    exact v.2
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

theorem card_Ksite_le {d n : ℕ} (ω : Configuration (ES d n)) (u : V d n) :
    (Ksite ω u).card ≤ (2 * n + 1) ^ d := by
  rw [← card_box]
  exact Finset.card_le_card (Ksite_subset_box ω u)

/-! ## 3. The independent Bernoulli law with the paper's cut-off kernel -/

/-- The edge open-probability `1 - exp(-(beta J(x,y)))` of the edge `e`, for a
symmetric kernel `J` on `Z^d`. -/
noncomputable def pKernel {d n : ℕ} (β : ℝ) (J : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (e : ES d n) : ℝ :=
  PercLib.CriticalLRP.longRangeEdgeProbability β (J (Subtype.val (src e)) (Subtype.val (tgt e)))

theorem pKernel_nonneg {d n : ℕ} {β : ℝ} {J : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    (hβ : 0 ≤ β) (hJ : ∀ x y, 0 ≤ J x y) (e : ES d n) : 0 ≤ pKernel β J e :=
  PercLib.CriticalLRP.longRangeEdgeProbability_nonneg hβ (hJ _ _)

theorem pKernel_le_one {d n : ℕ} {β : ℝ} {J : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    (hβ : 0 ≤ β) (hJ : ∀ x y, 0 ≤ J x y) (e : ES d n) : pKernel β J e ≤ 1 :=
  PercLib.CriticalLRP.longRangeEdgeProbability_le_one hβ (hJ _ _)

/-- The paper's cut-off kernel `J_r` restricted to the box, instantiated at the
radial profile `K` and the lattice distance.  Edges of length `> r` get
probability `1 - exp 0 = 0`, i.e. they are closed almost surely, exactly as in
Definition I.1.5. -/
noncomputable def pCutoff {d n : ℕ} (β r : ℝ) (K : ℝ → ℝ) (e : ES d n) : ℝ :=
  pKernel β (cutoffKernel K (fun x y => latticeDist x y) r) e

/-! ## 4. Non-vacuity: exact computations for the degenerate laws

These show that the abstract interface `K : Omega -> Finset (Site d)` of
`I58Remainder`/`I58Model` is realised by a genuine cluster, and that at the
degenerate parameters the cluster and its expectation can be computed exactly.
-/

/-- In the empty configuration the cluster of `u` is `{u}`. -/
theorem cl_empty {d n : ℕ} (u : V d n) : cl (∅ : Configuration (ES d n)) u = {u} := by
  ext v
  rw [mem_cl, Finset.mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih =>
        obtain ⟨e, he, -⟩ := hbc
        exact absurd he (Finset.notMem_empty e)
  · rintro rfl
    exact conn_refl src tgt (∅ : Configuration (ES d n)) _

theorem card_cl_empty {d n : ℕ} (u : V d n) : (cl (∅ : Configuration (ES d n)) u).card = 1 := by
  rw [cl_empty, Finset.card_singleton]

/-- In the complete configuration (all edges open) the cluster of `u` is the
whole box: the edge set is the complete graph. -/
theorem cl_univ {d n : ℕ} (u : V d n) : cl (univ : Configuration (ES d n)) u = univ := by
  ext v
  rw [mem_cl]
  constructor
  · intro _; exact Finset.mem_univ v
  · intro _
    by_cases h : u = v
    · rw [← h]; exact conn_refl src tgt univ u
    · rcases exists_edge_of_ne h with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
      · exact Relation.ReflTransGen.single ⟨e, Finset.mem_univ e, Or.inl ⟨h1, h2⟩⟩
      · exact Relation.ReflTransGen.single ⟨e, Finset.mem_univ e, Or.inr ⟨h1, h2⟩⟩

/-- The origin of the lattice, as a vertex of the box. -/
def o (d n : ℕ) : V d n := ⟨0, by rw [mem_box_iff]; simp [linfNorm]⟩

@[simp] theorem val_o {d n : ℕ} : Subtype.val (o d n) = (0 : Fin d → ℤ) := rfl

theorem zero_mem_Ksite {d n : ℕ} (ω : Configuration (ES d n)) :
    (0 : Fin d → ℤ) ∈ Ksite ω (o d n) := by
  rw [← val_o (d := d) (n := n)]
  exact mem_Ksite

/-- At the complete configuration the cluster of the origin has exactly the
volume `(2n+1)^d` of the box: a genuine, exact cluster-size computation. -/
theorem card_Ksite_univ {d n : ℕ} :
    (Ksite (univ : Configuration (ES d n)) (o d n)).card = (2 * n + 1) ^ d := by
  rw [card_Ksite, cl_univ, Finset.card_univ, Fintype.card_coe, card_box]

/-- At the empty configuration the cluster of the origin is the single point
`0`. -/
theorem Ksite_empty {d n : ℕ} :
    Ksite (∅ : Configuration (ES d n)) (o d n) = {0} := by
  rw [Ksite, cl_empty, Finset.image_singleton, val_o]

/-! ## 4. The law at degenerate parameters, and the expectation of the cluster size

`configurationLaw p` is the independent product law: `∏ e, (p e if e open, 1-p e
otherwise)`.  At `p = 0` all edges are closed a.s. and at `p = 1` all edges are
open a.s., and in both cases the expectation of the cluster size of the origin
can be computed exactly in the model of Section 1. -/

theorem configurationLaw_zero {E : Type*} [Fintype E] [DecidableEq E]
    (s : Configuration E) :
    configurationLaw (fun _ => (0 : ℝ)) s = if s = ∅ then 1 else 0 := by
  rw [configurationLaw]
  by_cases hs : s = ∅
  · subst hs; simp
  · rw [ite_eq_right hs]
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

theorem configurationLaw_one {E : Type*} [Fintype E] [DecidableEq E]
    (s : Configuration E) :
    configurationLaw (fun _ => (1 : ℝ)) s = if s = univ then 1 else 0 := by
  rw [configurationLaw]
  by_cases hs : s = univ
  · subst hs; simp
  · rw [ite_eq_right hs]
    have h : ∃ e : E, e ∉ s := by
      by_contra h'
      push Not at h'
      exact hs (Finset.eq_univ_of_forall h')
    obtain ⟨e, he⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

theorem ex_configurationLaw_zero {E : Type*} [Fintype E] [DecidableEq E]
    (X : Configuration E → ℝ) :
    PercLib.CriticalLRP.I58.ex (configurationLaw (fun _ => (0 : ℝ))) X = X ∅ := by
  simp only [PercLib.CriticalLRP.I58.ex, configurationLaw_zero]
  rw [Finset.sum_eq_single (∅ : Configuration E)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ (∅ : Configuration E)) hb

theorem ex_configurationLaw_one {E : Type*} [Fintype E] [DecidableEq E]
    (X : Configuration E → ℝ) :
    PercLib.CriticalLRP.I58.ex (configurationLaw (fun _ => (1 : ℝ))) X = X univ := by
  simp only [PercLib.CriticalLRP.I58.ex, configurationLaw_one]
  rw [Finset.sum_eq_single (univ : Configuration E)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ (univ : Configuration E)) hb

/-! ## 5. The genuine cluster observables of `I58Remainder` -/

/-- The cluster of the origin as an `I58.Site d`-valued observable: the `K` of
`I58Remainder`/`I58Model`, realised by a genuine cluster. -/
noncomputable def K0 {d n : ℕ} (ω : Configuration (ES d n)) : Finset (PercLib.CriticalLRP.I58.Site d) :=
  Ksite ω (o d n)

/-- The cluster of `y` if `y` is a vertex of the box (the paper's `K_y`), and
`∅` outside the box.  In the paper `B_r ⊆ B_n` so all summed `y` are vertices. -/
noncomputable def KyBox {d n : ℕ} (y : PercLib.CriticalLRP.I58.Site d)
    (ω : Configuration (ES d n)) : Finset (PercLib.CriticalLRP.I58.Site d) :=
  if h : y ∈ box d n then Ksite ω ⟨y, h⟩ else ∅

theorem KyBox_of_mem {d n : ℕ} {y : PercLib.CriticalLRP.I58.Site d} (h : y ∈ box d n)
    (ω : Configuration (ES d n)) : KyBox y ω = Ksite ω ⟨y, h⟩ := dite_eq_left h

theorem KyBox_of_not_mem {d n : ℕ} {y : PercLib.CriticalLRP.I58.Site d} (h : y ∉ box d n)
    (ω : Configuration (ES d n)) : KyBox y ω = ∅ := dite_eq_right h

theorem mem_Ksite_iff {d n : ℕ} {ω : Configuration (ES d n)} {u : V d n}
    {x : PercLib.CriticalLRP.I58.Site d} :
    x ∈ Ksite ω u ↔ ∃ v : V d n, Subtype.val v = x ∧ Conn src tgt ω u v := by
  constructor
  · intro hx
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hx
    exact ⟨v, hve, (mem_cl.mp hv)⟩
  · rintro ⟨v, rfl, hv⟩
    exact Finset.mem_image.mpr ⟨v, mem_cl.mpr hv, rfl⟩

/-- Membership in the genuine cluster of the origin. -/
theorem mem_K0_iff {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (h : y ∈ box d n) :
    y ∈ K0 ω ↔ Conn src tgt ω (o d n) ⟨y, h⟩ := by
  constructor
  · intro hy
    obtain ⟨v, hv, hc⟩ := mem_Ksite_iff.mp hy
    have : v = ⟨y, h⟩ := Subtype.coe_injective hv
    rwa [this] at hc
  · intro hc
    exact mem_Ksite_iff.mpr ⟨⟨y, h⟩, rfl, hc⟩

/-- **The paper's disjointness fact.**  If `y` is not in the cluster of the
origin, then the cluster of `y` is disjoint from it.  This is the content of the
indicator `1(y notin K)` in `T0, T2, T3, T4` of `eq:x12_derivative`. -/
theorem disjoint_K0_Ky {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (h : y ∈ box d n) (hy : y ∉ K0 ω) :
    Disjoint (K0 ω) (KyBox y ω) := by
  rw [KyBox_of_mem h]
  exact Ksite_disjoint (by rwa [mem_K0_iff h] at hy)

theorem card_union_K0_Ky {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (h : y ∈ box d n) (hy : y ∉ K0 ω) :
    ((cl ω (o d n) ∪ cl ω ⟨y, h⟩).card : ℝ) =
      (cl ω (o d n)).card + (cl ω ⟨y, h⟩).card := by
  rw [card_union_cl_of_not_conn (by rwa [mem_K0_iff h] at hy)]
  push_cast
  ring

theorem indOut_K0_eq_one {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (hy : y ∉ K0 ω) :
    PercLib.CriticalLRP.I58.indOut K0 y ω = 1 := by
  simp [PercLib.CriticalLRP.I58.indOut, hy]

/-- **Restoration by adding edges.**  Adding open edges can only enlarge a
cluster.  The paper's `K~_y` is the cluster of `y` after edges touching `K_0`
are re-sampled; the deterministic half of that construction, which is what the
monotonicity arguments of I.4.12 use, is this monotonicity. -/
theorem cl_subset_insert {d n : ℕ} (e : ES d n) (ω : Configuration (ES d n)) (u : V d n) :
    cl ω u ⊆ cl (insert e ω) u :=
  cl_mono (Finset.subset_insert e ω) u

/-- **Restoration by deleting edges** (the truncated configuration): deleting
edges can only shrink a cluster. -/
theorem cl_sdiff_subset {d n : ℕ} (D ω : Configuration (ES d n)) (u : V d n) :
    cl (ω \ D) u ⊆ cl ω u :=
  cl_mono (Finset.sdiff_subset) u

/-- **The engine of the volume-derivative identity I.4.1, at genuine clusters.**
Opening an edge whose endpoints are not connected merges exactly the two
clusters, so the cluster size adds. -/
theorem card_cl_insert_of_not_conn {d n : ℕ} {ω : Configuration (ES d n)} {e : ES d n}
    (h : ¬ Conn src tgt ω (src e) (tgt e)) :
    (cl (insert e ω) (src e)).card = (cl ω (src e)).card + (cl ω (tgt e)).card :=
  card_cluster_insert_of_not_conn h

/-! ## 6. Exact expectations of the genuine cluster size

The two degenerate computations sandwich the expected cluster size for every
`0 <= p <= 1`: `1 <= E|K| <= (2n+1)^d`.  This is a statement about the genuine
model, not about an abstract weight. -/

theorem kcard_K0_eq {d n : ℕ} (ω : Configuration (ES d n)) :
    PercLib.CriticalLRP.I58.kcard K0 ω = ((K0 ω).card : ℝ) := rfl

theorem one_le_kcard_K0 {d n : ℕ} (ω : Configuration (ES d n)) :
    (1 : ℝ) ≤ PercLib.CriticalLRP.I58.kcard K0 ω := by
  rw [kcard_K0_eq]
  have h : 0 < (K0 ω).card := Finset.card_pos.mpr ⟨_, zero_mem_Ksite ω⟩
  have h1 : 1 ≤ (K0 ω).card := h
  exact_mod_cast h1

theorem kcard_K0_le_vol {d n : ℕ} (ω : Configuration (ES d n)) :
    PercLib.CriticalLRP.I58.kcard K0 ω ≤ ((2 * n + 1) ^ d : ℝ) := by
  rw [kcard_K0_eq]
  have h := card_Ksite_le ω (o d n)
  exact_mod_cast h

/-- `E|K| = 1` when all edges are closed. -/
theorem ex_kcard_K0_zero {d n : ℕ} :
    PercLib.CriticalLRP.I58.ex (configurationLaw (fun _ => (0 : ℝ)))
      (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n))) = 1 := by
  rw [ex_configurationLaw_zero]
  rw [kcard_K0_eq]
  show ((Ksite (∅ : Configuration (ES d n)) (o d n)).card : ℝ) = 1
  rw [Ksite_empty, Finset.card_singleton]
  norm_num

/-- `E|K| = (2n+1)^d` when all edges are open. -/
theorem ex_kcard_K0_one {d n : ℕ} :
    PercLib.CriticalLRP.I58.ex (configurationLaw (fun _ => (1 : ℝ)))
      (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n))) = ((2 * n + 1 : ℕ) : ℝ) ^ d := by
  rw [ex_configurationLaw_one]
  rw [kcard_K0_eq]
  show ((Ksite (univ : Configuration (ES d n)) (o d n)).card : ℝ) = ((2 * n + 1 : ℕ) : ℝ) ^ d
  rw [card_Ksite_univ]
  push_cast
  ring

/-- Expectation of a constant. -/
theorem ex_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (c : ℝ) :
    PercLib.CriticalLRP.I58.ex w (fun _ => c)
      = c * PercLib.CriticalLRP.I58.ex w (fun _ => (1 : ℝ)) := by
  simp only [PercLib.CriticalLRP.I58.ex, mul_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => mul_comm _ _

/-- `1 <= E|K| <= (2n+1)^d` for every independent law with `0 <= p <= 1`: the
genuine cluster of the origin is never empty and never larger than the box. -/
theorem ex_kcard_K0_bounds {d n : ℕ} (p : ES d n → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    1 ≤ PercLib.CriticalLRP.I58.ex (configurationLaw p)
        (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n))) ∧
      PercLib.CriticalLRP.I58.ex (configurationLaw p)
        (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n))) ≤ ((2 * n + 1) ^ d : ℝ) := by
  have hw : ∀ ω, 0 ≤ configurationLaw p ω := configurationLaw_nonneg p hp hp1
  constructor
  · rw [← PercLib.CriticalLRP.I58.ex_configurationLaw_one p]
    exact PercLib.CriticalLRP.I58.ex_mono hw one_le_kcard_K0
  · calc PercLib.CriticalLRP.I58.ex (configurationLaw p)
          (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n)))
        ≤ PercLib.CriticalLRP.I58.ex (configurationLaw p)
            (fun _ => ((2 * n + 1) ^ d : ℝ)) :=
          PercLib.CriticalLRP.I58.ex_mono hw kcard_K0_le_vol
      _ = ((2 * n + 1) ^ d : ℝ) * PercLib.CriticalLRP.I58.ex (configurationLaw p)
            (fun _ => (1 : ℝ)) := ex_const _ _
      _ = ((2 * n + 1) ^ d : ℝ) := by
          rw [PercLib.CriticalLRP.I58.ex_configurationLaw_one p]
          ring

/-! ## 7. The assembly of Lemma I.5.8 at the genuine cluster model

This instantiates `I58Model.lemma_I_5_8_assembly_configurationLaw` at the real
cluster `K0` and the real cluster `KyBox` of Section 5.  The four displayed
remainder estimates stay hypotheses: nothing about BK, restoration, mass
transport or `hgap` is proved here.  What *is* proved is that the model,
the cluster, the restored cluster and the expectations are genuine, and that
`K0`/`KyBox` satisfy the geometric facts (disjointness, cardinality, box
bounds) stated in Sections 2, 3 and 5. -/

open PercLib.CriticalLRP.I58

theorem lemma_I_5_8_assembly_genuine {d n : ℕ} (p : ES d n → ℝ)
    (u : Fin d → ℝ) (B : Finset (Site d)) {r : ℝ}
    (hR0 : |(∑ y ∈ B, ex (configurationLaw p) (T0 u (K0 (d := d) (n := n)) KyBox y)) -
        (ex (configurationLaw p) (kcard (K0 (d := d) (n := n)))) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex (configurationLaw p) (fun ω => (kcard (K0 (d := d) (n := n)) ω) ^ 2 * kap (K0 (d := d) (n := n)) B ω))
    (hR2 : |(∑ y ∈ B, ex (configurationLaw p) (T2 u (K0 (d := d) (n := n)) KyBox y)) -
        (B.card : ℝ) * (ex (configurationLaw p) (kcard (K0 (d := d) (n := n)))) * (ex (configurationLaw p) (kS u (K0 (d := d) (n := n))))|
      ≤ ex (configurationLaw p) (fun ω => kcard (K0 (d := d) (n := n)) ω * kap (K0 (d := d) (n := n)) B ω * kS u (K0 (d := d) (n := n)) ω))
    (hR3 : |∑ y ∈ B, ex (configurationLaw p) (T3 u (K0 (d := d) (n := n)) KyBox y)|
      ≤ (1 / 2) * ex (configurationLaw p) (fun ω => kcard (K0 (d := d) (n := n)) ω * kap (K0 (d := d) (n := n)) B ω * kS u (K0 (d := d) (n := n)) ω))
    (hR4 : |∑ y ∈ B, ex (configurationLaw p) (T4 u (K0 (d := d) (n := n)) KyBox y)|
      ≤ (1 / 2) * ex (configurationLaw p) (fun ω => kcard (K0 (d := d) (n := n)) ω * kap (K0 (d := d) (n := n)) B ω * kS u (K0 (d := d) (n := n)) ω)
        + (1 / 2) * ex (configurationLaw p)
            (fun ω => (kcard (K0 (d := d) (n := n)) ω) ^ 2 * sMoment u ((K0 (d := d) (n := n)) ω ∩ B)))
    (hGq : ex (configurationLaw p) (fun ω => (kcard (K0 (d := d) (n := n)) ω) ^ 2 * sMoment u ((K0 (d := d) (n := n)) ω ∩ B))
      ≤ uNormSq u * r ^ 2 * ex (configurationLaw p) (fun ω => (kcard (K0 (d := d) (n := n)) ω) ^ 2 * kap (K0 (d := d) (n := n)) B ω)) :
    |derivTerm (configurationLaw p) u (K0 (d := d) (n := n)) KyBox B - mainTerm (configurationLaw p) u (K0 (d := d) (n := n)) B|
      ≤ 3 * (uNormSq u * r ^ 2
          * ex (configurationLaw p) (fun ω => (kcard (K0 (d := d) (n := n)) ω) ^ 2 * kap (K0 (d := d) (n := n)) B ω))
        + 5 * ex (configurationLaw p) (fun ω => kcard (K0 (d := d) (n := n)) ω * kap (K0 (d := d) (n := n)) B ω * kS u (K0 (d := d) (n := n)) ω) :=
  PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_configurationLaw p u (K0 (d := d) (n := n))
    (KyBox (d := d) (n := n)) B hR0 hR2 hR3 hR4 hGq


/-! ## 8. Identification of the finite law as an independent product law

`configurationLaw p` is the independent edge law; the split form below exhibits
it as a product of the open-edge marginals `p e` and the closed-edge marginals
`1 - p e`.  Together with `configurationLaw_sum` (normalization),
`configurationLaw_modular` (multiplicative modularity, i.e. independence) and
`expectation_mul_expectation_le` (Harris--FKG for increasing observables), all
from `CriticalPercLib.CriticalLRP.FiniteBernoulli`, this identifies the law
used in Sections 3--7. -/

theorem configurationLaw_split {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → ℝ) (s : Configuration E) :
    configurationLaw p s = (∏ e ∈ s, p e) * ∏ e ∈ univ \ s, (1 - p e) := by
  rw [configurationLaw]
  rw [← Finset.prod_filter_mul_prod_filter_not (univ : Finset E) (fun e => e ∈ s)
    (fun e => if e ∈ s then p e else 1 - p e)]
  rw [show univ.filter (fun e => e ∈ s) = s from by simp,
    show univ.filter (fun e => ¬ e ∈ s) = univ \ s from by ext e; simp]
  congr 1
  · exact Finset.prod_congr rfl fun e he => by simp [he]
  · exact Finset.prod_congr rfl fun e he => by
      have : e ∉ s := by simpa using he
      simp [this]

/-- The abstract `kap` counts the genuine connections from the origin into `B`. -/
theorem kap_K0_eq_filter {d n : ℕ} (ω : Configuration (ES d n))
    (B : Finset (PercLib.CriticalLRP.I58.Site d)) :
    PercLib.CriticalLRP.I58.kap (K0 (d := d) (n := n)) B ω
      = ((B.filter (fun y => y ∈ K0 ω)).card : ℝ) := by
  simp only [PercLib.CriticalLRP.I58.kap, Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem kS_K0_eq {d n : ℕ} (u : Fin d → ℝ) (ω : Configuration (ES d n)) :
    PercLib.CriticalLRP.I58.kS u (K0 (d := d) (n := n)) ω
      = PercLib.CriticalLRP.I58.sMoment u (K0 ω) := rfl

/-- On the event `y notin K`, the weight `|K| 1(y notin K) |K_y|` of `T0` is
the product of the two genuine cluster sizes. -/
theorem restW_K0_KyBox {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (hy : y ∉ K0 ω) :
    PercLib.CriticalLRP.I58.restW (K0 (d := d) (n := n))
        (KyBox (d := d) (n := n)) y ω
      = ((K0 ω).card : ℝ) * ((KyBox y ω).card : ℝ) := by
  simp only [PercLib.CriticalLRP.I58.restW, PercLib.CriticalLRP.I58.indOut,
    PercLib.CriticalLRP.I58.kcard, ite_eq_right hy, zero_mul, one_mul]

/-- **Coordinate independence (odds form).**  Adding the single edge `e` to a
configuration in which it is closed multiplies the weight by `p e` and removes
the factor `1 - p e`: the ratio is independent of the rest of the configuration.
This is the exact sense in which `configurationLaw p` is the independent edge
law.  (The marginal identity `P(e open) = p e` follows from this and
normalization by the algebra `p (1 - P) = (1 - p) P`; the reindexing that the
summation needs is not formalised here.) -/
theorem configurationLaw_odds {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → ℝ) (e : E) (t : Configuration E) (ht : e ∉ t) :
    p e * configurationLaw p t = (1 - p e) * configurationLaw p (insert e t) := by
  rw [configurationLaw, configurationLaw]
  conv_lhs => rw [show (univ : Finset E) = insert e (univ.erase e) from
    (Finset.insert_erase (Finset.mem_univ e)).symm]
  conv_rhs => rw [show (univ : Finset E) = insert e (univ.erase e) from
    (Finset.insert_erase (Finset.mem_univ e)).symm]
  rw [Finset.prod_insert (Finset.notMem_erase e (univ : Finset E)),
    Finset.prod_insert (Finset.notMem_erase e (univ : Finset E))]
  have hQ : (∏ x ∈ univ.erase e, (if x ∈ t then p x else 1 - p x))
      = ∏ x ∈ univ.erase e, (if x ∈ insert e t then p x else 1 - p x) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxe : x ≠ e := Finset.ne_of_mem_erase hx
    have hx : (x ∈ insert e t ↔ x ∈ t) := by
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left hxe, fun h => Or.inr h⟩
    simp only [hx]
  rw [ite_eq_right ht, ite_eq_left (Finset.mem_insert_self e t), hQ]
  ring


/-- **Expected cluster size = sum of connection probabilities.**  In the genuine
finite model the abstract observable `kcard K0` is exactly the number of sites of
the box joined to the origin, so its expectation is the sum over the box of the
two-point connectivity probabilities
`P(x in K0) = ex (configurationLaw p) (1(x in K0))`.  This is the finite-box
form of `E|K| = sum_x P(0 <-> x)`, the identity on which the paper's
mass-transport and BC/DF arguments act. -/
theorem ex_kcard_K0_eq_sum_conn {d n : ℕ} (p : ES d n → ℝ) :
    PercLib.CriticalLRP.I58.ex (configurationLaw p)
      (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n)))
      = ∑ x ∈ box d n, PercLib.CriticalLRP.I58.ex (configurationLaw p)
          (fun ω => if x ∈ K0 ω then (1 : ℝ) else 0) := by
  have hcard : ∀ ω : Configuration (ES d n),
      ((K0 ω).card : ℝ) = ∑ x ∈ box d n, (if x ∈ K0 ω then (1 : ℝ) else 0) := by
    intro ω
    rw [Finset.sum_ite_mem,
      show box d n ∩ K0 ω = K0 ω from Finset.inter_eq_right.mpr (Ksite_subset_box ω (o d n))]
    simp
  calc PercLib.CriticalLRP.I58.ex (configurationLaw p)
        (PercLib.CriticalLRP.I58.kcard (K0 (d := d) (n := n)))
      = ∑ ω, configurationLaw p ω
          * ∑ x ∈ box d n, (if x ∈ K0 ω then (1 : ℝ) else 0) := by
        simp only [PercLib.CriticalLRP.I58.ex, PercLib.CriticalLRP.I58.kcard, hcard]
    _ = ∑ ω, ∑ x ∈ box d n,
          configurationLaw p ω * (if x ∈ K0 ω then (1 : ℝ) else 0) := by
        simp only [Finset.mul_sum]
    _ = ∑ x ∈ box d n, ∑ ω,
          configurationLaw p ω * (if x ∈ K0 ω then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ x ∈ box d n, PercLib.CriticalLRP.I58.ex (configurationLaw p)
          (fun ω => if x ∈ K0 ω then (1 : ℝ) else 0) := rfl

/-- On the event `y notin K`, every site of the cluster `K_y` lies outside `K`:
the inner sums `sum_{z in K_y}` of `T3` and `T4` range over `Z^d \ K`. -/
theorem not_mem_K0_of_mem_KyBox {d n : ℕ} {ω : Configuration (ES d n)}
    {y : PercLib.CriticalLRP.I58.Site d} (h : y ∈ box d n) (hy : y ∉ K0 ω)
    {z : PercLib.CriticalLRP.I58.Site d} (hz : z ∈ KyBox y ω) : z ∉ K0 ω := by
  have hd := disjoint_K0_Ky h hy
  intro hzK
  exact (Finset.disjoint_left.mp hd) hzK hz

/-! ## 9. Edge-relabelling invariance of the law

Every "by translation invariance" step in the BC/DF/hvol arguments is an instance
of the following two facts: the independent law is invariant under any
permutation of the edge set that preserves the edge probabilities, and hence so
is its expectation.  They are proved here for a general finite edge type, so
they apply to the box model of Sections 1--8 and to any torus model with a
translation-invariant kernel, and they make the symmetry input explicit. -/

theorem configurationLaw_perm {E : Type*} [Fintype E] [DecidableEq E] (p : E → ℝ)
    (σ : Equiv.Perm E) (hσ : ∀ e, p (σ e) = p e) (s : Configuration E) :
    configurationLaw p (s.map σ.toEmbedding) = configurationLaw p s := by
  rw [configurationLaw, configurationLaw]
  rw [← Equiv.prod_comp σ (fun e => if e ∈ s.map σ.toEmbedding then p e else 1 - p e)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hmem : (σ e ∈ s.map σ.toEmbedding) ↔ e ∈ s := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨f, hf, hfe⟩
      exact (σ.injective hfe) ▸ hf
    · intro he; exact ⟨e, he, rfl⟩
  by_cases he : e ∈ s
  · rw [ite_eq_left (hmem.mpr he), ite_eq_left he, hσ e]
  · rw [ite_eq_right (fun h => he (hmem.mp h)), ite_eq_right he, hσ e]

theorem ex_perm {E : Type*} [Fintype E] [DecidableEq E] (p : E → ℝ) (σ : Equiv.Perm E)
    (hσ : ∀ e, p (σ e) = p e) (X : Configuration E → ℝ) :
    PercLib.CriticalLRP.I58.ex (configurationLaw p)
        (fun s => X (s.map σ.toEmbedding)) = PercLib.CriticalLRP.I58.ex (configurationLaw p) X := by
  simp only [PercLib.CriticalLRP.I58.ex]
  have hstep : ∀ s : Configuration E,
      configurationLaw p s * X (Equiv.finsetCongr σ s)
        = configurationLaw p (Equiv.finsetCongr σ s) * X (Equiv.finsetCongr σ s) := by
    intro s
    rw [Equiv.finsetCongr_apply, configurationLaw_perm p σ hσ s]
  calc ∑ s, configurationLaw p s * X (s.map σ.toEmbedding)
      = ∑ s, configurationLaw p s * X (Equiv.finsetCongr σ s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Equiv.finsetCongr_apply]
    _ = ∑ s, configurationLaw p (Equiv.finsetCongr σ s) * X (Equiv.finsetCongr σ s) :=
        Finset.sum_congr rfl fun s _ => hstep s
    _ = ∑ t, configurationLaw p t * X t :=
        Equiv.sum_comp (Equiv.finsetCongr σ) (fun t => configurationLaw p t * X t)

/-- The model has at least one edge as soon as `d >= 1` and `n >= 1`: the second
vertex is the unit vector in the first coordinate, and `exists_edge_of_ne`
supplies the edge. -/
theorem exists_ES_of_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) : Nonempty (ES d n) := by
  classical
  let i0 : Fin d := ⟨0, hd⟩
  have h1 : (0 : Fin d → ℤ) ∈ box d n := by
    rw [mem_box_iff]; simp [linfNorm]
  have h2 : (fun i => if i = i0 then (1 : ℤ) else 0) ∈ box d n := by
    rw [mem_box_iff, linfNorm_le_iff]
    intro i
    by_cases hi : i = i0
    · simp [hi]; omega
    · simp [hi]
  have hne : (⟨0, h1⟩ : V d n) ≠ ⟨(fun i => if i = i0 then (1 : ℤ) else 0), h2⟩ := by
    intro hEq
    have hval : (0 : Fin d → ℤ) = (fun i => if i = i0 then (1 : ℤ) else 0) :=
      congrArg Subtype.val hEq
    have hi := congrFun hval i0
    simp at hi
  rcases exists_edge_of_ne hne with ⟨e, -⟩ | ⟨e, -⟩
  · exact ⟨e⟩
  · exact ⟨e⟩

end PercLib.CriticalLRP.M2

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.M2.exists_edge_of_ne
#print axioms PercLib.CriticalLRP.M2.mem_cl
#print axioms PercLib.CriticalLRP.M2.cl_disjoint
#print axioms PercLib.CriticalLRP.M2.card_union_cl_of_not_conn
#print axioms PercLib.CriticalLRP.M2.card_Ksite_univ
#print axioms PercLib.CriticalLRP.M2.mem_K0_iff
#print axioms PercLib.CriticalLRP.M2.disjoint_K0_Ky
#print axioms PercLib.CriticalLRP.M2.card_union_K0_Ky
#print axioms PercLib.CriticalLRP.M2.card_cl_insert_of_not_conn
#print axioms PercLib.CriticalLRP.M2.ex_kcard_K0_zero
#print axioms PercLib.CriticalLRP.M2.ex_kcard_K0_one
#print axioms PercLib.CriticalLRP.M2.ex_kcard_K0_bounds
#print axioms PercLib.CriticalLRP.M2.configurationLaw_split
#print axioms PercLib.CriticalLRP.M2.kap_K0_eq_filter
#print axioms PercLib.CriticalLRP.M2.configurationLaw_odds
#print axioms PercLib.CriticalLRP.M2.configurationLaw_zero
#print axioms PercLib.CriticalLRP.M2.configurationLaw_one
#print axioms PercLib.CriticalLRP.M2.ex_configurationLaw_zero
#print axioms PercLib.CriticalLRP.M2.restW_K0_KyBox
#print axioms PercLib.CriticalLRP.M2.ex_kcard_K0_eq_sum_conn
#print axioms PercLib.CriticalLRP.M2.not_mem_K0_of_mem_KyBox
#print axioms PercLib.CriticalLRP.M2.configurationLaw_perm
#print axioms PercLib.CriticalLRP.M2.ex_perm
#print axioms PercLib.CriticalLRP.M2.exists_ES_of_pos
#print axioms PercLib.CriticalLRP.M2.lemma_I_5_8_assembly_genuine
