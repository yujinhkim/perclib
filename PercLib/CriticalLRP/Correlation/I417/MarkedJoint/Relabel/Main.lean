/-
Independently reviewed and integrated UltraMath work: swarm `smwwxbtza`, member `m1`,
direction B. Production integration revision:
`54054b7051903bd4990d0dc78cdfcb61d0676288`, Lean 4.35.0.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Defs

public import PercLib.CriticalLRP.Correlation.I417.Marked.Diagram
public import PercLib.CriticalLRP.Correlation.I417.General.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join

/-! Relabel the canonical marked atlas sum and evaluate it as a polygon diagram. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedRelabel

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos rootPos childPos)
open PercLib.CriticalLRP.I417Marked (Label markLabel armLabel labelledMarkedDiagram)
open PercLib.CriticalLRP.I417Marked (markedExtend markedSubtypeEquiv)


universe u

variable {V : Type*}

/-! ## Compatibility of the vertex maps with the relabelling -/

/-- The root vertex of a relabelled tree is the root vertex of the tree. -/
theorem rootPos_mapLabel {α β : Type u} (f : α → β) (g : β → α) (hg : ∀ a, g (f a) = a)
    (t : RTree α) (φ : t.IPos → V) (y : α → V) :
    rootPos (t.mapLabel f) (fun i => φ (iposMapLabelEquiv f t i)) (fun b => y (g b))
      = rootPos t φ y := by
  induction t with
  | leaf a =>
      change y (g (f a)) = y a
      rw [hg a]
  | node l r ihl ihr =>
      change φ (iposMapLabelEquiv f (RTree.node l r) (Sum.inr (Sum.inr ⟨⟩)))
        = φ (Sum.inr (Sum.inr ⟨⟩))
      rw [iposMapLabelEquiv_inr_inr]

/-- The child vertex of a relabelled tree is the child vertex of the tree. -/
theorem childPos_mapLabel {α β : Type u} (f : α → β) (g : β → α) (hg : ∀ a, g (f a) = a)
    (y : α → V) :
    ∀ (t : RTree α) (φ : t.IPos → V) (i : RTree.IPos (t.mapLabel f)) (b : Bool),
      childPos (t.mapLabel f) (fun i => φ (iposMapLabelEquiv f t i)) (fun b => y (g b)) i b
        = childPos t φ y (iposMapLabelEquiv f t i) b
  | RTree.leaf a, φ, i, b => Empty.elim i
  | RTree.node l r, φ, i, b => by
      rcases i with i | i
      · change childPos (l.mapLabel f) (fun v => φ (Sum.inl (iposMapLabelEquiv f l v)))
            (fun b => y (g b)) i b
          = childPos l (fun v => φ (Sum.inl v)) y (iposMapLabelEquiv f l i) b
        exact childPos_mapLabel f g hg y l (fun v => φ (Sum.inl v)) i b
      · rcases i with j | w
        · change childPos (r.mapLabel f) (fun w => φ (Sum.inr (Sum.inl (iposMapLabelEquiv f r w))))
              (fun b => y (g b)) j b
            = childPos r (fun w => φ (Sum.inr (Sum.inl w))) y (iposMapLabelEquiv f r j) b
          exact childPos_mapLabel f g hg y r (fun w => φ (Sum.inr (Sum.inl w))) j b
        · change (if b then rootPos (r.mapLabel f)
                (fun w => φ (Sum.inr (Sum.inl (iposMapLabelEquiv f r w)))) (fun b => y (g b))
              else rootPos (l.mapLabel f)
                (fun v => φ (Sum.inl (iposMapLabelEquiv f l v))) (fun b => y (g b)))
            = if b then rootPos r (fun w => φ (Sum.inr (Sum.inl w))) y
              else rootPos l (fun v => φ (Sum.inl v)) y
          cases b
          · change rootPos (l.mapLabel f) (fun v => φ (Sum.inl (iposMapLabelEquiv f l v)))
              (fun b => y (g b)) = rootPos l (fun v => φ (Sum.inl v)) y
            exact rootPos_mapLabel f g hg l (fun v => φ (Sum.inl v)) y
          · change rootPos (r.mapLabel f) (fun w => φ (Sum.inr (Sum.inl (iposMapLabelEquiv f r w))))
              (fun b => y (g b)) = rootPos r (fun w => φ (Sum.inr (Sum.inl w))) y
            exact rootPos_mapLabel f g hg r (fun w => φ (Sum.inr (Sum.inl w))) y

/-- The upper end of an atlas edge is preserved by the relabelling. -/
theorem srcPos_mapLabel {α β : Type u} (f : α → β)
    (t : RTree α) (φ : t.IPos → V) (c : V) (e : AEdge (t.mapLabel f)) :
    srcPos (t.mapLabel f) (fun i => φ (iposMapLabelEquiv f t i)) c e
      = srcPos t φ c (aedgeEquiv f t e) := by
  rcases e with ⟨i, b⟩ | w
  · rw [srcPos_inl, aedgeEquiv_inl, srcPos_inl]
  · rw [srcPos_inr, aedgeEquiv_inr, srcPos_inr]

/-- The lower end of an atlas edge is preserved by the relabelling. -/
theorem dstPos_mapLabel {α β : Type u} (f : α → β) (g : β → α) (hg : ∀ a, g (f a) = a)
    (t : RTree α) (φ : t.IPos → V) (y : α → V) (e : AEdge (t.mapLabel f)) :
    dstPos (t.mapLabel f) (fun i => φ (iposMapLabelEquiv f t i)) (fun b => y (g b)) e
      = dstPos t φ y (aedgeEquiv f t e) := by
  rcases e with ⟨i, b⟩ | w
  · rw [dstPos_inl, aedgeEquiv_inl, dstPos_inl]
    exact childPos_mapLabel f g hg y t φ i b
  · rw [dstPos_inr, aedgeEquiv_inr, dstPos_inr]
    exact rootPos_mapLabel f g hg t φ y

/-- **The atlas product is invariant under a leaf relabelling**, provided the terminal values are
carried along a section of the relabelling. -/
theorem atlasEdgeProduct_mapLabel {α β : Type u} (f : α → β) (g : β → α)
    (hg : ∀ a, g (f a) = a) (π : Sym2 V → unitInterval) (x : V) (t : RTree α)
    (φ : t.IPos → V) (y : α → V) :
    atlasEdgeProduct π x (fun b => y (g b)) (t.mapLabel f)
        (fun i => φ (iposMapLabelEquiv f t i))
      = atlasEdgeProduct π x y t φ := by
  unfold atlasEdgeProduct
  rw [← Equiv.prod_comp (aedgeEquiv f t).symm]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [srcPos_mapLabel f, dstPos_mapLabel f g hg, Equiv.apply_symm_apply]

/-- The pin as a product factor is the indicator of `G` on the pinned tuples. -/
theorem pinLast_mul_indicator {W : Type*} {w : W} {p : ℕ}
    (G : (Fin (p + 1) → W) → ℝ≥0∞) (y : Fin (p + 1) → W) :
    pinLast w y * G y
      = ({y' : Fin (p + 1) → W | y' (Fin.last p) = w} : Set (Fin (p + 1) → W)).indicator
          G y := by
  by_cases h : y (Fin.last p) = w
  · rw [pinLast_of_mem h,
      Set.indicator_of_mem (s := {y' : Fin (p + 1) → W | y' (Fin.last p) = w}) (f := G) h,
      one_mul]
  · rw [pinLast_of_notMem h,
      Set.indicator_of_notMem (s := {y' : Fin (p + 1) → W | y' (Fin.last p) = w}) (f := G) h,
      zero_mul]

/-- **The pinning reindexing**: summing the arms with the mark fixed equals summing over all
`p+1`-tuples with the last entry pinned at `w`. -/
theorem tsum_markedExtend {W : Type*} {p : ℕ} (w : W) (G : (Fin (p + 1) → W) → ℝ≥0∞) :
    (∑' f : Fin p → W, G (markedExtend w f)) = ∑' y : Fin (p + 1) → W, pinLast w y * G y := by
  classical
  rw [tsum_congr (pinLast_mul_indicator G), ← tsum_subtype]
  exact Equiv.tsum_eq (markedSubtypeEquiv w p)
    (fun y : {y : Fin (p + 1) → W // y (Fin.last p) = w} => G y.1)

/-- The terminal event of the marked carrier is the marked arm event. -/
theorem labelEvent_markedExtend {W : Type*} [Countable W] (x w : W) {p : ℕ} (f : Fin p → W) :
    I417A.labelEvent x (markedExtend w f) = I417A.labelEvent x f ∩ connSet x w := by
  ext ω
  simp only [I417A.labelEvent, connSet, PercLib.CriticalLRP.mem_cluster_iff, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last p)⟩
  · rintro ⟨hf, hw⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
    · simpa using hf j
    · subst h
      simpa using hw

/-! ## The three reindexings -/

/-- **The pinning reindexing along the label equivalence.** -/
theorem tsum_pin_reindex {W : Type*} {p : ℕ} (w : W) (K : (Fin (p + 1) → W) → ℝ≥0∞) :
    (∑' y : Fin (p + 1) → W, pinLast w y * K y)
      = ∑' y' : Label p → W, pinMark w y' * K (fun i => y' (finLabelEquiv p i)) := by
  classical
  refine (Equiv.tsum_eq (piEquivOfEquiv (finLabelEquiv p) W)
    (fun y => pinLast w y * K y)).symm.trans ?_
  refine tsum_congr fun y' => ?_
  have hpin : (piEquivOfEquiv (finLabelEquiv p) W) y' (Fin.last p) = w ↔ y' (markLabel p) = w := by
    rw [piEquivOfEquiv_apply, finLabelEquiv_last]
  by_cases h : y' (markLabel p) = w
  · rw [pinLast_of_mem (hpin.mpr h), pinMark_of_mem h, one_mul, one_mul,
      piEquivOfEquiv_apply_eq]
  · rw [pinLast_of_notMem (fun hh => h (hpin.mp hh)), pinMark_of_notMem h, zero_mul, zero_mul]

/-- **Reindexing the internal positions along the relabelling.** -/
theorem tsum_atlasEdgeProduct_mapLabel {α β : Type u} (f : α → β) (g : β → α)
    (hg : ∀ a, g (f a) = a) {W : Type*} (π : Sym2 W → unitInterval) (x : W) (t : RTree α)
    (y : α → W) :
    (∑' φ : t.IPos → W, atlasEdgeProduct π x y t φ)
      = ∑' φ' : (t.mapLabel f).IPos → W,
          atlasEdgeProduct π x (fun b => y (g b)) (t.mapLabel f) φ' := by
  let Φ : (t.IPos → W) ≃ ((t.mapLabel f).IPos → W) := piEquivOfEquiv (iposMapLabelEquiv f t) W
  refine (tsum_congr fun φ => (atlasEdgeProduct_mapLabel f g hg π x t φ y).symm).trans ?_
  exact Equiv.tsum_eq Φ
    (fun φ' => atlasEdgeProduct π x (fun b => y (g b)) (t.mapLabel f) φ')

/-- **Reindexing the shape family along the label equivalence.** -/
theorem tsum_shape_reindex {W : Type*} (π : Sym2 W → unitInterval) (x w : W) (p : ℕ) :
    (∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
        ∑' y' : Label p → W, pinMark w y' *
          ∑' φ' : (t.1.mapLabel (finLabelEquiv p)).IPos → W,
            atlasEdgeProduct π x y' (t.1.mapLabel (finLabelEquiv p)) φ')
      = ∑' t' : LTon (Label p) (Finset.univ : Finset (Label p)),
          ∑' y' : Label p → W, pinMark w y' *
            ∑' φ' : t'.1.IPos → W, atlasEdgeProduct π x y' t'.1 φ' :=
  Equiv.tsum_eq (ltOnMapLabelEquiv (finLabelEquiv p))
    (fun t' => ∑' y' : Label p → W, pinMark w y' *
      ∑' φ' : t'.1.IPos → W, atlasEdgeProduct π x y' t'.1 φ')

/-! ## Evaluating the marked atlas sum -/

/-- **The marked atlas sum is the labelled marked diagram** at the two-point kernel
`k u v = edgeMeasure π (connSet u v)`. -/
theorem markedAtlasSum_eq_labelledMarkedDiagram {W : Type*} [DecidableEq W]
    (π : Sym2 W → unitInterval) (x w : W) (p : ℕ) :
    markedAtlasSum π x w p =
      labelledMarkedDiagram (fun u v => edgeMeasure π (connSet u v)) p x w := by
  classical
  have step1 : markedAtlasSum π x w p
      = ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' y : Fin (p + 1) → W, pinLast w y *
            ∑' φ : t.1.IPos → W, atlasEdgeProduct π x y t.1 φ := by
    rw [markedAtlasSum]
    simp only [← atlasEdgeProduct_eq_atlasProduct]
    exact tsum_congr fun t =>
      ENNReal.tsum_comm.trans (tsum_congr fun y => ENNReal.tsum_mul_left)
  have step2 : (∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' y : Fin (p + 1) → W, pinLast w y *
            ∑' φ : t.1.IPos → W, atlasEdgeProduct π x y t.1 φ)
      = ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' y' : Label p → W, pinMark w y' *
            ∑' φ : t.1.IPos → W,
              atlasEdgeProduct π x (fun i => y' (finLabelEquiv p i)) t.1 φ := by
    exact tsum_congr fun t =>
      tsum_pin_reindex w (fun y => ∑' φ : t.1.IPos → W, atlasEdgeProduct π x y t.1 φ)
  have step3 : (∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' y' : Label p → W, pinMark w y' *
            ∑' φ : t.1.IPos → W,
              atlasEdgeProduct π x (fun i => y' (finLabelEquiv p i)) t.1 φ)
      = ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' y' : Label p → W, pinMark w y' *
            ∑' φ' : (t.1.mapLabel (finLabelEquiv p)).IPos → W,
              atlasEdgeProduct π x y' (t.1.mapLabel (finLabelEquiv p)) φ' := by
    refine tsum_congr fun t => tsum_congr fun y' => ?_
    have hcomp := tsum_atlasEdgeProduct_mapLabel (finLabelEquiv p) (finLabelEquiv p).symm
      (fun a => (finLabelEquiv p).symm_apply_apply a) π x t.1
      (fun i => y' (finLabelEquiv p i))
    simp only [Equiv.apply_symm_apply] at hcomp
    exact congrArg (fun z => pinMark w y' * z) hcomp
  rw [step1, step2, step3, tsum_shape_reindex π x w p]
  rw [labelledMarkedDiagram, tsum_fintype]
  refine Finset.sum_congr rfl fun t' _ => tsum_congr fun y' => ?_
  by_cases h : y' (markLabel p) = w
  · rw [pinMark_of_mem h, ite_eq_left h, one_mul, one_mul]
    rfl
  · rw [pinMark_of_notMem h, ite_eq_right h, zero_mul, zero_mul]

/-! ## The marked joint-moment bound and its evaluation -/

/-- **The marked joint-moment bound**: `E[|K_x|^p 1(w ∈ K_x)]` is at most the marked atlas
sum. -/
theorem jointPow_le_markedAtlasSum {W : Type*} [Countable W] (π : Sym2 W → unitInterval)
    (hπ : ∀ e, π e < 1) (x w : W) (p : ℕ) :
    I417Gen.jointPow π x p w ≤ markedAtlasSum π x w p := by
  classical
  have harm : I417Gen.jointPow π x p w
      = ∑' f : Fin p → W, edgeMeasure π (I417A.labelEvent x (markedExtend w f)) := by
    rw [← I417Gen.tsum_labelEvent_inter π x p w]
    exact tsum_congr fun f => by rw [labelEvent_markedExtend]
  rw [harm]
  have hbk : ∀ f : Fin p → W,
      edgeMeasure π (I417A.labelEvent x (markedExtend w f)) ≤
        ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' φ : t.1.IPos → W,
            CanonAtlas.Measure.atlasProduct π x (markedExtend w f) t.1 φ :=
    fun f => CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk π hπ (Nat.succ_pos p) x
      (markedExtend w f)
  refine (ENNReal.tsum_le_tsum hbk).trans (le_of_eq ?_)
  rw [markedAtlasSum]
  have hA : (∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
        ∑' φ : t.1.IPos → W, ∑' y : Fin (p + 1) → W,
          pinLast w y * CanonAtlas.Measure.atlasProduct π x y t.1 φ)
      = ∑' t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
          ∑' φ : t.1.IPos → W, ∑' f : Fin p → W,
            CanonAtlas.Measure.atlasProduct π x (markedExtend w f) t.1 φ := by
    exact tsum_congr fun t => tsum_congr fun φ =>
      (tsum_markedExtend w (fun y => CanonAtlas.Measure.atlasProduct π x y t.1 φ)).symm
  rw [hA]
  rw [ENNReal.tsum_comm (f := fun (f : Fin p → W)
    (t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1)))) =>
      ∑' φ : t.1.IPos → W, CanonAtlas.Measure.atlasProduct π x (markedExtend w f) t.1 φ)]
  exact tsum_congr fun t => ENNReal.tsum_comm

/-- **The canonical arbitrary-`p` marked polygon bound.**

For a countable vertex set, an opening profile `π` with `π e < 1`, a constant two-point row
sum `χ` of the kernel `k u v = edgeMeasure π (connSet u v)`, a root `x`, a marked vertex `w`
and every `p : ℕ`, the marked joint moment is at most the finite diagram expression

  `∑_{ℓ=1}^{p+1} markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)`.

No finiteness of the vertex set, no finite box, and no truncation of any sum is used: the
canonical covering theorem, countable subadditivity, the finite-index canonical BK law and the
`ENNReal` `tsum` reindexings are the whole chain. -/
theorem jointPow_le_markedPolygonBound {W : Type*} [Countable W] [DecidableEq W]
    (π : Sym2 W → unitInterval) (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, edgeMeasure π (connSet v y) = χ) (x w : W) (p : ℕ) :
    I417Gen.jointPow π x p w ≤
      I417Marked.markedPolygonBound χ (fun u v => edgeMeasure π (connSet u v)) p x w := by
  classical
  refine (jointPow_le_markedAtlasSum π hπ x w p).trans (le_of_eq ?_)
  rw [markedAtlasSum_eq_labelledMarkedDiagram]
  exact I417Marked.labelledMarkedDiagram_eq_polygon (fun u v => edgeMeasure π (connSet u v))
    χ hχ p x w

/-! ## Audit -/

namespace RelabelAudit

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417MarkedRelabel.finOfLabel_labelOfFin
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.atlasEdgeProduct_mapLabel
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.ltOnMapLabel_surjective
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.tsum_markedExtend
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.labelEvent_markedExtend
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.tsum_pin_reindex
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.tsum_atlasEdgeProduct_mapLabel
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.tsum_shape_reindex
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.markedAtlasSum_eq_labelledMarkedDiagram
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.jointPow_le_markedAtlasSum
#print axioms PercLib.CriticalLRP.I417MarkedRelabel.jointPow_le_markedPolygonBound
#print PercLib.CriticalLRP.I417MarkedRelabel.jointPow_le_markedPolygonBound

end RelabelAudit

end PercLib.CriticalLRP.I417MarkedRelabel
