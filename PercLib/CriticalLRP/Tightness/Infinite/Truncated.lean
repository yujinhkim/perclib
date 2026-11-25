/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# (2.10) for an ARBITRARY vertex type: finite truncation of the BFS parent tree

Reference: T. Hutchcroft, arXiv:2008.11197v2, Section 2.1, proof of Theorem 2.3, step (2.10).

The repository proves the disjoint-occurrence inclusion (2.10)

  `{|K_max(Λ)| ≥ 3^k λ} ⊆ {|K_max(Λ)| ≥ λ} ∘ ⋯ ∘ {|K_max(Λ)| ≥ λ}`   (`3^(k-1)+1` copies)

only under `[Fintype V]` (`Tightness/MaxClusterPower.meets_disjointOccurrence`), because it applies
the finite tree-piece lemma `exists_tree_pieces` to the **whole** cluster `Cl G ω r`.  For a
countable (or arbitrary) vertex type the cluster of `u` may be infinite, so this file does what the
source's proof of (2.10) actually needs and nothing more: it cuts **not** the whole cluster but the
finite `par`-closed ancestor closure `truncSet G ω r A` of the marked set `A = Λ ∩ K_u`.

* `truncSet G ω r A` is finite (a union of `bdist x + 1` ancestor steps for `x ∈ A`),
  `par`-closed, contains `A` and the root `r`, and lies in the cluster of `r`.
* On the finite subtype `TS G ω r A = ↥(truncSet G ω r A)` the map `par` restricts to
  `parS`, which is a rooted forest (`parS_isRootedForest`), so `exists_tree_pieces` applies.
* The pieces returned are then genuine pairwise disjoint open BK witnesses: `pieceEdgesS` is the
  set of parent edges of a piece, it is contained in `ω` (`pieceEdgesS_subset`), it forces
  `{|K_max(Λ)| ≥ λ}` (`pieceEdgesS_mem_maxMeets`), and distinct pieces have disjoint edge sets
  (`pieceEdgesS_disjoint`).

Nothing finitary about `V` is assumed: the main result `meets_disjointOccurrence_anyV` holds for an
arbitrary vertex type.  The *probability* step (2.8) for an infinite `V` is a separate matter (it
needs either the BK inequality for a countable edge set or the source's exhaustion argument), and is
not claimed here.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.MaxClusterPower
public import PercLib.CriticalLRP.Tightness.Infinite.BFS

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft
namespace Countable

open PercLib.CriticalLRP.Percolation Hutchcroft

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] {E : Type*} [DecidableEq E] [Nonempty E]

/-! ### The finite ancestor closure of a marked set -/

section Trunc

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- **The ancestor closure of a finite marked set.**  `truncSet G ω r A` contains, for every
`x ∈ A`, the whole `par`-chain from `x` down to the root, truncated at the exact step
`bdist x` at which the chain reaches `r`.  It is finite, `par`-closed, and contained in the
cluster of `r`. -/
noncomputable def truncSet (A : Finset V) : Finset V :=
  A.biUnion (fun x => (Finset.range (bdist G ω r x + 1)).image (fun i => (par G ω r)^[i] x))

theorem mem_truncSet {A : Finset V} {y : V} :
    y ∈ truncSet G ω r A ↔ ∃ x ∈ A, ∃ i ≤ bdist G ω r x, (par G ω r)^[i] x = y := by
  classical
  simp only [truncSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, i, hi, rfl⟩
    exact ⟨x, hx, i, by omega, rfl⟩
  · rintro ⟨x, hx, i, hi, rfl⟩
    exact ⟨x, hx, i, by omega, rfl⟩

/-- Every marked vertex belongs to its own ancestor closure. -/
theorem subset_truncSet (A : Finset V) : A ⊆ truncSet G ω r A := by
  intro x hx
  rw [mem_truncSet]
  exact ⟨x, hx, 0, Nat.zero_le _, by simp⟩

/-- The ancestor closure stays inside the cluster of `r`. -/
theorem truncSet_conn_of_mem {A : Finset V} (hAc : ∀ x ∈ A, Conn G ω r x) {y : V}
    (hy : y ∈ truncSet G ω r A) : Conn G ω r y := by
  rw [mem_truncSet] at hy
  obtain ⟨x, hx, i, -, rfl⟩ := hy
  exact par_iterate_conn G ω r (hAc x hx) i

/-- The parent of a point of the ancestor closure stays in it. -/
theorem par_mem_truncSet {A : Finset V} (hAc : ∀ x ∈ A, Conn G ω r x) {y : V}
    (hy : y ∈ truncSet G ω r A) : par G ω r y ∈ truncSet G ω r A := by
  classical
  rw [mem_truncSet] at hy ⊢
  obtain ⟨x, hx, i, hi, rfl⟩ := hy
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · refine ⟨x, hx, i + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply']
  · subst heq
    have hroot : (par G ω r)^[bdist G ω r x] x = r := par_bdist_iterate G ω r (hAc x hx)
    rw [hroot, par_root]
    exact ⟨x, hx, bdist G ω r x, le_rfl, hroot⟩

/-- Every iterate of the parent map stays in the ancestor closure once it starts there. -/
theorem par_iterate_mem_truncSet {A : Finset V} (hAc : ∀ x ∈ A, Conn G ω r x) {y : V}
    (hy : y ∈ truncSet G ω r A) (n : ℕ) : (par G ω r)^[n] y ∈ truncSet G ω r A := by
  induction n with
  | zero => simpa using hy
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact par_mem_truncSet G ω r hAc ih

/-- The root belongs to the ancestor closure of any non-empty marked set. -/
theorem root_mem_truncSet {A : Finset V} (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty) :
    r ∈ truncSet G ω r A := by
  obtain ⟨x, hx⟩ := hne
  rw [mem_truncSet]
  exact ⟨x, hx, bdist G ω r x, le_rfl, par_bdist_iterate G ω r (hAc x hx)⟩

end Trunc

/-! ### The parent map restricted to the ancestor closure -/

section Sub

variable (G : BondGraph V E) (ω : Set E) (r : V)
variable {A : Finset V}

/-- The finite vertex type of the ancestor closure. -/
noncomputable abbrev TS (A : Finset V) : Type _ := ↥(truncSet G ω r A)

/-- **The parent map on the ancestor closure** (a self-map because `truncSet` is `par`-closed). -/
noncomputable def parS (hAc : ∀ x ∈ A, Conn G ω r x) (x : TS G ω r A) : TS G ω r A :=
  ⟨par G ω r (x : V), par_mem_truncSet G ω r hAc x.2⟩

@[simp] theorem parS_val (hAc : ∀ x ∈ A, Conn G ω r x) (x : TS G ω r A) :
    (parS G ω r hAc x : V) = par G ω r (x : V) := rfl

theorem parS_iterate_val (hAc : ∀ x ∈ A, Conn G ω r x) (n : ℕ) (x : TS G ω r A) :
    ((parS G ω r hAc)^[n] x : V) = (par G ω r)^[n] (x : V) := by
  induction n generalizing x with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, parS_val]

/-- **The restriction of the BFS parent map to the ancestor closure is a rooted forest.** -/
theorem parS_isRootedForest (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty) :
    IsRootedForest (parS G ω r hAc) ⟨r, root_mem_truncSet G ω r hAc hne⟩ := by
  constructor
  · exact Subtype.ext (par_root G ω r)
  · intro x
    refine ⟨bdist G ω r (x : V), Subtype.ext ?_⟩
    rw [parS_iterate_val, par_bdist_iterate G ω r (truncSet_conn_of_mem G ω r hAc x.2)]

end Sub

/-! ### The tree pieces of the ancestor closure -/

section Pieces

variable (G : BondGraph V E) (ω : Set E) (r : V)
variable {A : Finset V}

/-- The marked set `A`, regarded as a finite subset of the ancestor closure `TS G ω r A`. -/
noncomputable def markSetS (A : Finset V) : Finset (TS G ω r A) :=
  A.subtype (fun y => y ∈ truncSet G ω r A)

@[simp] theorem mem_markSetS {a : TS G ω r A} :
    a ∈ markSetS G ω r A ↔ (a : V) ∈ A := by
  classical
  simp [markSetS]

theorem card_markSetS (hAS : A ⊆ truncSet G ω r A) : (markSetS G ω r A).card = A.card := by
  classical
  rw [markSetS, Finset.card_subtype, Finset.filter_true_of_mem hAS]

/-- **Tree pieces of the truncated parent tree.**  `3^k * lam` marked vertices of the cluster of
`r` produce `3^(k-1)+1` pairwise edge-disjoint rooted pieces of the finite `par`-closed closure
`truncSet G ω r A`, each carrying between `lam` and `2*lam-1` marked vertices. -/
theorem exists_trunc_pieces (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k) (hA : 3 ^ k * lam ≤ A.card) :
    ∃ s : Finset (TS G ω r A × Finset (TS G ω r A)),
      3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece (parS G ω r hAc) p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ (markSetS G ω r A ∩ p.2).card ∧
        (markSetS G ω r A ∩ p.2).card ≤ 2 * lam - 1) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (p.2.erase p.1) (q.2.erase q.1)) := by
  classical
  have hcard : 3 ^ k * lam ≤ (markSetS G ω r A).card := by
    rw [card_markSetS G ω r (subset_truncSet G ω r A)]
    exact hA
  exact exists_tree_pieces (parS_isRootedForest G ω r hAc hne) (markSetS G ω r A) hlam hk hcard

end Pieces

/-! ### The pieces are disjoint open BK witnesses -/

section Witness

variable (G : BondGraph V E) (ω : Set E) (r : V)
variable {A : Finset V}

/-- The open parent edge of a point `x` of the ancestor closure, with junk value at the root. -/
noncomputable def parEdgeS (hAc : ∀ x ∈ A, Conn G ω r x) (x : TS G ω r A) : E :=
  if h : (x : V) = r then Classical.arbitrary E
  else Classical.choose (par_open G ω r (truncSet_conn_of_mem G ω r hAc x.2) h)

/-- At a non-root point the chosen edge is an open edge to `parS x`. -/
theorem parEdgeS_spec (hAc : ∀ x ∈ A, Conn G ω r x) {x : TS G ω r A} (h : (x : V) ≠ r) :
    parEdgeS G ω r hAc x ∈ ω ∧
      G (parEdgeS G ω r hAc x) = s((x : V), (parS G ω r hAc x : V)) := by
  classical
  rw [parEdgeS, dite_eq_right h]
  exact Classical.choose_spec (par_open G ω r (truncSet_conn_of_mem G ω r hAc x.2) h)

/-- The witness edge set of a piece: the parent edges of its non-root vertices. -/
noncomputable def pieceEdgesS (hAc : ∀ x ∈ A, Conn G ω r x) (p : TS G ω r A × Finset (TS G ω r A)) :
    Finset E :=
  (p.2.erase p.1).image (parEdgeS G ω r hAc)

theorem mem_pieceEdgesS {hAc : ∀ x ∈ A, Conn G ω r x} {p : TS G ω r A × Finset (TS G ω r A)}
    {e : E} : e ∈ pieceEdgesS G ω r hAc p ↔ ∃ x ∈ p.2.erase p.1, parEdgeS G ω r hAc x = e :=
  Finset.mem_image

/-- A non-root vertex of a rooted piece is not the root `r` of the cluster, so its parent edge is a
genuine open edge. -/
theorem piece_erase_ne_root (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {p : TS G ω r A × Finset (TS G ω r A)} (hp : IsRootedPiece (parS G ω r hAc) p.1 p.2)
    {x : TS G ω r A} (hx : x ∈ p.2.erase p.1) : (x : V) ≠ r := by
  classical
  intro hxr
  obtain ⟨hxv, hxP⟩ := Finset.mem_erase.mp hx
  obtain ⟨n, hn⟩ := hp.2.2 x hxP
  have hxroot : x = (⟨r, root_mem_truncSet G ω r hAc hne⟩ : TS G ω r A) := Subtype.ext hxr
  have hpfix : (parS G ω r hAc)^[n] x = (⟨r, root_mem_truncSet G ω r hAc hne⟩ : TS G ω r A) := by
    rw [hxroot, isRootedForest_fix (parS_isRootedForest G ω r hAc hne) n]
  have hpx : p.1 = x := by rw [← hn, hpfix, hxroot]
  exact hxv hpx.symm

/-- **The witness edges of a piece are open.** -/
theorem pieceEdgesS_subset (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {p : TS G ω r A × Finset (TS G ω r A)} (hp : IsRootedPiece (parS G ω r hAc) p.1 p.2) :
    (pieceEdgesS G ω r hAc p : Set E) ⊆ ω := by
  classical
  intro e he
  rw [Finset.mem_coe, mem_pieceEdgesS] at he
  obtain ⟨x, hx, rfl⟩ := he
  exact (parEdgeS_spec G ω r hAc (piece_erase_ne_root G ω r hAc hne hp hx)).1

/-- **Distinct non-root points of the ancestor closure have distinct parent edges.** -/
theorem parEdgeS_inj (hAc : ∀ x ∈ A, Conn G ω r x) {x y : TS G ω r A} (hx : (x : V) ≠ r)
    (hy : (y : V) ≠ r) (h : parEdgeS G ω r hAc x = parEdgeS G ω r hAc y) : x = y := by
  classical
  obtain ⟨-, hx'⟩ := parEdgeS_spec G ω r hAc hx
  obtain ⟨-, hy'⟩ := parEdgeS_spec G ω r hAc hy
  have he : s((x : V), (parS G ω r hAc x : V)) = s((y : V), (parS G ω r hAc y : V)) := by
    rw [← hx', ← hy', h]
  rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Subtype.ext h1
  · exfalso
    have hbx := par_bdist_succ G ω r (truncSet_conn_of_mem G ω r hAc x.2) hx
    have hby := par_bdist_succ G ω r (truncSet_conn_of_mem G ω r hAc y.2) hy
    have hx1 : bdist G ω r (x : V) = bdist G ω r (par G ω r (y : V)) := by rw [h1, parS_val]
    have hx2 : bdist G ω r (par G ω r (x : V)) = bdist G ω r (y : V) := by
      rw [← parS_val (G := G) (ω := ω) (r := r) (A := A) (hAc := hAc) (x := x), h2]
    rw [hx2, hx1] at hbx
    omega

/-- **Distinct pieces have disjoint witness edge sets.** -/
theorem pieceEdgesS_disjoint (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {p q : TS G ω r A × Finset (TS G ω r A)}
    (hp : IsRootedPiece (parS G ω r hAc) p.1 p.2)
    (hq : IsRootedPiece (parS G ω r hAc) q.1 q.2)
    (hdisj : Disjoint (p.2.erase p.1) (q.2.erase q.1)) :
    Disjoint (pieceEdgesS G ω r hAc p) (pieceEdgesS G ω r hAc q) := by
  classical
  rw [Finset.disjoint_left]
  intro e he he'
  rw [mem_pieceEdgesS] at he he'
  obtain ⟨x, hx, hxe⟩ := he
  obtain ⟨y, hy, hye⟩ := he'
  have hxy : x = y :=
    parEdgeS_inj G ω r hAc (piece_erase_ne_root G ω r hAc hne hp hx)
      (piece_erase_ne_root G ω r hAc hne hq hy) (hxe.trans hye.symm)
  subst hxy
  exact Finset.disjoint_left.mp hdisj hx hy

/-- Transport of reachability along the coercion from the closure to `V`. -/
theorem conn_of_reflTransGen_S {W : Set E} {a b : TS G ω r A}
    (h : Relation.ReflTransGen
      (fun x y : TS G ω r A => ∃ e ∈ W, G e = s((x : V), (y : V))) a b) :
    Conn G W (a : V) (b : V) := by
  induction h with
  | refl => exact conn_refl G W _
  | tail _ hstep ih => exact ih.tail hstep

/-- **A piece is connected through its own witness edges.** -/
theorem piece_conn_pieceEdgesS (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty)
    {p : TS G ω r A × Finset (TS G ω r A)} (hp : IsRootedPiece (parS G ω r hAc) p.1 p.2)
    {x y : TS G ω r A} (hx : x ∈ p.2) (hy : y ∈ p.2) :
    Conn G ((pieceEdgesS G ω r hAc p : Finset E) : Set E) (x : V) (y : V) := by
  classical
  have hopen : ∀ a ∈ p.2, a ≠ p.1 →
      ∃ e ∈ ((pieceEdgesS G ω r hAc p : Finset E) : Set E),
        G e = s((a : V), ((parS G ω r hAc) a : V)) := by
    intro a ha hav
    have har : (a : V) ≠ r :=
      piece_erase_ne_root G ω r hAc hne hp (Finset.mem_erase.mpr ⟨hav, ha⟩)
    refine ⟨parEdgeS G ω r hAc a, ?_, (parEdgeS_spec G ω r hAc har).2⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩, rfl⟩)
  have hsymm : Std.Symm fun a b : TS G ω r A =>
      ∃ e ∈ ((pieceEdgesS G ω r hAc p : Finset E) : Set E), G e = s((a : V), (b : V)) := by
    constructor
    rintro a b ⟨e, he, hE⟩
    exact ⟨e, he, by rw [hE, Sym2.eq_swap]⟩
  exact conn_of_reflTransGen_S G ω r
    (isRootedPiece_reachable _ hsymm hp hopen hx hy)

end Witness

/-! ### Each piece forces `{|K_max(Λ)| ≥ λ}`; the inclusion (2.10) for arbitrary `V` -/

section Capstone

variable (G : BondGraph V E) (ω : Set E) (r : V)
variable {A : Finset V}

/-- The marked count of a piece is the same whether computed inside the ancestor closure or in
`V`. -/
theorem card_markSetS_inter (P : Finset (TS G ω r A)) :
    (markSetS G ω r A ∩ P).card = (A ∩ P.image (Subtype.val : TS G ω r A → V)).card := by
  classical
  have himg : (markSetS G ω r A ∩ P).image (Subtype.val : TS G ω r A → V)
      = A ∩ P.image (Subtype.val : TS G ω r A → V) := by
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_inter.mpr
        ⟨(mem_markSetS (G := G) (ω := ω) (r := r) (A := A)).mp (Finset.mem_inter.mp hb).1,
          Finset.mem_image.mpr ⟨b, (Finset.mem_inter.mp hb).2, rfl⟩⟩
    · intro hy
      obtain ⟨hA, hyP⟩ := Finset.mem_inter.mp hy
      obtain ⟨b, hbP, rfl⟩ := Finset.mem_image.mp hyP
      exact Finset.mem_image.mpr
        ⟨b, Finset.mem_inter.mpr ⟨(mem_markSetS (G := G) (ω := ω) (r := r) (A := A)).mpr hA, hbP⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injective _ (fun u v huv => Subtype.ext huv)]

/-- **A piece of the truncated parent tree is a BK witness for `{|K_max(Λ)| ≥ λ}`**: its own
parent edges already put `lam` marked vertices of `Λ` in one cluster. -/
theorem pieceEdgesS_mem_maxMeets {Λ : Finset V} (hAΛ : A ⊆ Λ)
    (hAc : ∀ x ∈ A, Conn G ω r x) (hne : A.Nonempty) {lam : ℕ} (hlam : 1 ≤ lam)
    {p : TS G ω r A × Finset (TS G ω r A)} (hp : IsRootedPiece (parS G ω r hAc) p.1 p.2)
    (hmark : lam ≤ (markSetS G ω r A ∩ p.2).card) :
    (pieceEdgesS G ω r hAc p : Set E) ∈ MaxMeets G Λ lam := by
  classical
  have hpos : 0 < (markSetS G ω r A ∩ p.2).card := lt_of_lt_of_le (by omega : 0 < lam) hmark
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have haA : (a : V) ∈ A := (mem_markSetS (G := G) (ω := ω) (r := r) (A := A)).mp (Finset.mem_inter.mp ha).1
  have haP : a ∈ p.2 := (Finset.mem_inter.mp ha).2
  refine ⟨(markSetS G ω r A ∩ p.2).image (Subtype.val : TS G ω r A → V), ?_, ?_, (a : V), ?_⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hAΛ ((mem_markSetS (G := G) (ω := ω) (r := r) (A := A)).mp (Finset.mem_inter.mp hb).1)
  · rw [Finset.card_image_of_injective _ (fun u v huv => Subtype.ext huv)]
    exact hmark
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact piece_conn_pieceEdgesS G ω r hAc hne hp haP (Finset.mem_inter.mp hb).2

/-- **The disjoint-occurrence inclusion (2.10) for an arbitrary vertex type.**

Let `G` be a bond graph on *any* vertex type `V`, `ω` an edge set and `Λ` a finite window.  If some
cluster of `ω` meets `Λ` in at least `3^k lam` vertices (`lam ≥ 2`, `k ≥ 1`), then there are
`3^(k-1)+1` pairwise disjoint finite sets of open edges each of which on its own already forces
`{|K_max(Λ)| ≥ lam}`.  What is cut here is not the (possibly infinite) cluster but the finite
`par`-closed ancestor closure of its marked vertices. -/
theorem meets_disjointOccurrence_anyV {Λ : Finset V} {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k) :
    MaxMeets G Λ (3 ^ k * lam) ⊆
      DisjointOccurrenceFin (fun _ : Fin (3 ^ (k - 1) + 1) => MaxMeets G Λ lam) := by
  classical
  intro ω hω
  obtain ⟨t, htΛ, htcard, u, hconn⟩ : ∃ t : Finset V, t ⊆ Λ ∧ 3 ^ k * lam ≤ t.card ∧
      ∃ u : V, ∀ y ∈ t, Conn G ω u y := hω
  set A : Finset V := Λ.filter (fun x => Conn G ω u x) with hAdef
  have hAΛ : A ⊆ Λ := Finset.filter_subset _ _
  have hAc : ∀ x ∈ A, Conn G ω u x := fun x hx => (Finset.mem_filter.mp hx).2
  have hAcard : 3 ^ k * lam ≤ A.card := by
    have hsub : t ⊆ A := fun y hy => Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    exact le_trans htcard (Finset.card_le_card hsub)
  have hne : A.Nonempty := by
    refine Finset.card_pos.mp ?_
    have h3 : 0 < 3 ^ k := by positivity
    have hlampos : 0 < lam := by omega
    have : 0 < 3 ^ k * lam := Nat.mul_pos h3 hlampos
    omega
  obtain ⟨s, hscard, hp, hmark, hdisj⟩ := exists_trunc_pieces G ω u hAc hne hlam hk hAcard
  obtain ⟨s', hs'sub, hs'card⟩ : ∃ s' ⊆ s, s'.card = 3 ^ (k - 1) + 1 :=
    Finset.exists_subset_card_eq hscard
  let e : s' ≃ Fin (3 ^ (k - 1) + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hs'card)
  refine ⟨fun i => pieceEdgesS G ω u hAc (e.symm i).1, ?_, ?_, ?_⟩
  · intro i
    exact pieceEdgesS_subset G ω u hAc hne (hp _ (hs'sub (e.symm i).2))
  · intro i
    exact pieceEdgesS_mem_maxMeets G ω u hAΛ hAc hne (by omega) (hp _ (hs'sub (e.symm i).2))
      (hmark _ (hs'sub (e.symm i).2)).1
  · intro i j hij
    have hne' : (e.symm i).1 ≠ (e.symm j).1 := by
      intro h
      exact hij (e.symm.injective (Subtype.ext h))
    exact pieceEdgesS_disjoint G ω u hAc hne (hp _ (hs'sub (e.symm i).2))
      (hp _ (hs'sub (e.symm j).2))
      (hdisj _ (hs'sub (e.symm i).2) _ (hs'sub (e.symm j).2) hne')

/-- **Parent extraction for an infinite graph** (the interface m5's `RootedWindow.lean` leaves open).

If a cluster of `ω` meets the finite window `Λ` in at least `3^k lam` vertices (`lam ≥ 2`,
`k ≥ 1`), then there are a *finite* vertex set `S`, a parent map `pp` on `S` that is a rooted
forest, a root `rt`, and a marked set `A ⊆ Λ` of at least `3^k lam` vertices of one cluster, such
that the parent edge of every non-root vertex of `S` is open in `ω`.

Two differences from the version hypothesised in m5: `S` is the finite `par`-closed ancestor
closure of `A` (so no finiteness or countability of `V` is needed), and the forest hypothesis is
`IsRootedForest pp rt` (`pp rt = rt` and every vertex reaches `rt`) instead of the unsatisfiable
"no periodic point off the root". -/
theorem exists_parent_extraction {Λ : Finset V} {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    {ω : Set E} (hω : ω ∈ MaxMeets G Λ (3 ^ k * lam)) :
    ∃ (S : Finset V) (pp : ↥S → ↥S) (rt : ↥S) (A : Finset V) (u : V),
      A ⊆ Λ ∧ 3 ^ k * lam ≤ A.card ∧ (∀ y ∈ A, Conn G ω u y) ∧
      IsRootedForest pp rt ∧
      (∀ x : ↥S, x ≠ rt → ∃ e ∈ ω, G e = s((x : V), ((pp x : ↥S) : V))) := by
  classical
  obtain ⟨t, htΛ, htcard, u, hconn⟩ : ∃ t : Finset V, t ⊆ Λ ∧ 3 ^ k * lam ≤ t.card ∧
      ∃ u : V, ∀ y ∈ t, Conn G ω u y := hω
  set A : Finset V := Λ.filter (fun x => Conn G ω u x) with hAdef
  have hAΛ : A ⊆ Λ := Finset.filter_subset _ _
  have hAc : ∀ x ∈ A, Conn G ω u x := fun x hx => (Finset.mem_filter.mp hx).2
  have hAcard : 3 ^ k * lam ≤ A.card := by
    have hsub : t ⊆ A := fun y hy => Finset.mem_filter.mpr ⟨htΛ hy, hconn y hy⟩
    exact le_trans htcard (Finset.card_le_card hsub)
  have hne : A.Nonempty := by
    refine Finset.card_pos.mp ?_
    have h3 : 0 < 3 ^ k := by positivity
    have : 0 < 3 ^ k * lam := Nat.mul_pos h3 (by omega)
    omega
  exact ⟨truncSet G ω u A, parS G ω u hAc, ⟨u, root_mem_truncSet G ω u hAc hne⟩, A, u,
    hAΛ, hAcard, hAc, parS_isRootedForest G ω u hAc hne, by
      intro x hx
      have hxr : (x : V) ≠ u := fun h => hx (Subtype.ext h)
      exact par_open G ω u (truncSet_conn_of_mem G ω u hAc x.2) hxr⟩

end Capstone

end Countable
end Hutchcroft
