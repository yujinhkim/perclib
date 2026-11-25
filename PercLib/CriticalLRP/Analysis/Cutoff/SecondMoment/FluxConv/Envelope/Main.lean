/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvgnqju`, member `m1`, direction (A).

# Pointwise domination of the `p = 2` flip differences by the ghost envelope

`FluxConv.Insertion` asks for a single nonnegative integrable envelope `Env e` on configurations
that dominates, for every edge `e`, both

* `flipDiff (cutFun S |K₀|²) e`, the closed ghost of the *windowed* square, and
* `flipDiff |K₀|² e`, the closed ghost of the untruncated square.

The exact closed ghost is the `ℝ≥0∞` edge weight `quadEdgeWeight (cutRange r)`; it is *not*
monotone, because it carries the exclusion indicator `1(b ↮ c)`.  This file proves the pointwise
half of the estimate:

* on the differentiating support `{e | cutEdgeDeriv r e ≠ 0}` (genuine edges of length `≤ r`) both
  flip differences are dominated by the unexcluded edge weight `unexclEdgeWeight` at the closed
  configuration `ω \ {e}` (the ghost envelope of `Defs.lean`);
* on the complementary edges (diagonal edges, or edges outside the radius window) a definite
  cubic merge majorant `bigEdge` dominates them, which is what lets the landed insertion theorem
  be fed with an envelope defined on *all* edges.

The two inequalities are proved from the exact single-edge merge identity, not from monotonicity of
the cut ghost: the windowed cluster is a subcluster of the full one, so dropping the exclusion
indicator makes the ghost monotone in the configuration.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Insertion
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Binomial
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Defs

/-!
# Domination of the two closed ghosts by the envelope
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The windowed functional ignores edges outside the window -/

/-- The windowed square is invariant under flipping an edge outside the window. -/
theorem flipDiff_cutFun_eq_zero_of_notMem (S : Finset (Sym2 M.V)) {e : Sym2 M.V} (he : e ∉ S)
    (ω : Config M.V) : flipDiff (cutFun S M.clusterVolSqReal) e ω = 0 := by
  simp only [flipDiff, cutFun, cutConfig_forceOn_of_notMem S he, sub_self]

/-! ## 2. The cubic merge majorant -/

/-- The cubic majorant `bigPair` and its unordered-edge form `bigEdge` are defined in
`Envelope/Defs.lean`; this file proves their analytical properties. -/

theorem bigEdge_mk (γ : Config M.V) (x y : M.V) :
    bigEdge M γ s(x, y) = bigPair M γ x y := Sym2.lift_mk ..

/-- The cubic majorant is monotone in the configuration. -/
theorem bigEdge_mono {γ γ' : Config M.V} (h : ∀ e : Sym2 M.V, e ∈ γ → e ∈ γ') (e : Sym2 M.V) :
    bigEdge M γ e ≤ bigEdge M γ' e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [bigEdge_mk, bigEdge_mk]
    have h0 := clusterVol_mono h (0 : M.V)
    have hx := clusterVol_mono h x
    have hy := clusterVol_mono h y
    simp only [bigPair]
    gcongr

/-- The cubic majorant is finite when the cluster volumes are. -/
theorem bigEdge_ne_top (γ : Config M.V) (e : Sym2 M.V)
    (hfin : ∀ v : M.V, clusterVol γ v ≠ ⊤) : bigEdge M γ e ≠ ⊤ := by
  induction e using Sym2.ind with
  | h x y =>
    rw [bigEdge_mk]
    simp only [bigPair]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin 0)),
         ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin x))⟩,
       ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin y))⟩

/-- The cubic majorant is measurable in the configuration. -/
theorem measurable_bigEdge (e : Sym2 M.V) : Measurable fun γ : Config M.V => bigEdge M γ e := by
  induction e using Sym2.ind with
  | h x y =>
    have hfun : (fun γ : Config M.V => bigEdge M γ s(x, y))
        = fun γ => bigPair M γ x y := funext fun γ => bigEdge_mk M γ x y
    rw [hfun]
    simp only [bigPair]
    exact ((((measurable_clusterVol (0 : M.V)).pow_const 2).const_mul 2).add
      (((measurable_clusterVol x).pow_const 2).const_mul 3)).add
      (((measurable_clusterVol y).pow_const 2).const_mul 3)

/-! ## 3. The real increment lemma -/

/-- **Real arithmetic of the `p = 2` increment.**  If `0 ≤ a ≤ a' ≤ a + b + c` then the
increment `a'² - a²` of the square is at most `2a² + 3b² + 3c²`. -/
theorem sq_sub_sq_le (a a' b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ a') (h2 : a' ≤ a + b + c) : a' ^ 2 - a ^ 2 ≤ 2 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- **The `p = 2` increment is nonnegative.**  At a configuration in which the edge is closed and
all cluster volumes are finite, opening the edge only merges clusters, so the square increases. -/
theorem flipDiff_clusterVolSq_nonneg {e : Sym2 M.V} {γ : Config M.V} (hnot : e ∉ γ)
    (hfin : ∀ v : M.V, clusterVol γ v ≠ ⊤) : 0 ≤ flipDiff M.clusterVolSqReal e γ := by
  induction e using Sym2.ind with
  | h x y =>
    have hopen : forceOn {s(x, y)} ({s(x, y)} : Config M.V) γ = γ ∪ {s(x, y)} :=
      forceOn_singleton_open_eq _ _
    have hclosed : forceOn {s(x, y)} (∅ : Config M.V) γ = γ \ {s(x, y)} :=
      forceOn_singleton_closed_eq _ _
    have hsd : γ \ {s(x, y)} = γ := sdiff_singleton_of_notMem hnot
    have hfinU : clusterVol (γ ∪ {s(x, y)}) (0 : M.V) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨hfin 0, hfin x⟩, hfin y⟩)
        (clusterVol_union_pair_le γ (0 : M.V) x y)
    have hmono : (clusterVol γ (0 : M.V)).toReal
        ≤ (clusterVol (γ ∪ {s(x, y)}) (0 : M.V)).toReal :=
      ENNReal.toReal_mono hfinU
        (clusterVol_mono (fun a ha => Set.mem_union_left _ ha) 0)
    have hflip : flipDiff M.clusterVolSqReal s(x, y) γ
        = (clusterVol (γ ∪ {s(x, y)}) (0 : M.V)).toReal ^ 2
            - (clusterVol γ (0 : M.V)).toReal ^ 2 := by
      simp only [flipDiff, SourceModelData.clusterVolSqReal_apply, hopen, hclosed, hsd]
    rw [hflip]
    exact sub_nonneg.mpr (pow_le_pow_left₀ ENNReal.toReal_nonneg hmono 2)

/-- **The `p = 2` increment is dominated by the cubic merge majorant.**  No exclusion indicator and
no connection hypothesis: this holds at *every* edge `e`, at every configuration `γ` in which `e`
is closed and all cluster volumes are finite. -/
theorem flipDiff_clusterVolSq_le_bigEdge {e : Sym2 M.V} {γ : Config M.V} (hnot : e ∉ γ)
    (hfin : ∀ v : M.V, clusterVol γ v ≠ ⊤) :
    flipDiff M.clusterVolSqReal e γ ≤ (bigEdge M γ e).toReal := by
  induction e using Sym2.ind with
  | h x y =>
    have hopen : forceOn {s(x, y)} ({s(x, y)} : Config M.V) γ = γ ∪ {s(x, y)} :=
      forceOn_singleton_open_eq _ _
    have hclosed : forceOn {s(x, y)} (∅ : Config M.V) γ = γ \ {s(x, y)} :=
      forceOn_singleton_closed_eq _ _
    have hsd : γ \ {s(x, y)} = γ := sdiff_singleton_of_notMem hnot
    have hflip : flipDiff M.clusterVolSqReal s(x, y) γ
        = (clusterVol (γ ∪ {s(x, y)}) (0 : M.V)).toReal ^ 2
            - (clusterVol γ (0 : M.V)).toReal ^ 2 := by
      simp only [flipDiff, SourceModelData.clusterVolSqReal_apply, hopen, hclosed, hsd]
    have hfinU : clusterVol (γ ∪ {s(x, y)}) (0 : M.V) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨hfin 0, hfin x⟩, hfin y⟩)
        (clusterVol_union_pair_le γ (0 : M.V) x y)
    have hmono : (clusterVol γ (0 : M.V)).toReal
        ≤ (clusterVol (γ ∪ {s(x, y)}) (0 : M.V)).toReal :=
      ENNReal.toReal_mono hfinU
        (clusterVol_mono (fun a ha => Set.mem_union_left _ ha) 0)
    have hle : (clusterVol (γ ∪ {s(x, y)}) (0 : M.V)).toReal
        ≤ (clusterVol γ (0 : M.V)).toReal + (clusterVol γ x).toReal + (clusterVol γ y).toReal := by
      have hsum : clusterVol γ (0 : M.V) + clusterVol γ x + clusterVol γ y ≠ ⊤ :=
        ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨hfin 0, hfin x⟩, hfin y⟩
      have h2 := ENNReal.toReal_mono hsum (clusterVol_union_pair_le γ (0 : M.V) x y)
      rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfin 0, hfin x⟩) (hfin y),
        ENNReal.toReal_add (hfin 0) (hfin x)] at h2
    have hbig : (bigEdge M γ s(x, y)).toReal
        = 2 * (clusterVol γ (0 : M.V)).toReal ^ 2 + 3 * (clusterVol γ x).toReal ^ 2
          + 3 * (clusterVol γ y).toReal ^ 2 := by
      rw [bigEdge_mk]
      simp only [bigPair]
      rw [ENNReal.toReal_add, ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow,
]
      · simp
      all_goals
        first
        | exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin 0))
        | exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin x))
        | exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin y))
        | exact ENNReal.add_ne_top.mpr
            ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin 0)),
             ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hfin x))⟩
    rw [hflip, hbig]
    exact sq_sub_sq_le _ _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg hmono hle

/-- The flip difference of an edge only depends on the configuration with that edge deleted. -/
theorem flipDiff_congr_sdiff {g : Config M.V → ℝ} {e : Sym2 M.V} {ω ω' : Config M.V}
    (h : ω \ {e} = ω' \ {e}) : flipDiff g e ω = flipDiff g e ω' := by
  simp only [flipDiff, forceOn, h]

/-- **The windowed increment is dominated by the cubic merge majorant.**  For every edge, and every
window, the flip difference of the windowed square at `ω` is the increment of the *windowed*
cluster at the closed windowed configuration, hence is bounded by the cubic majorant. -/
theorem flipDiff_cutFun_le_bigEdge (S : Finset (Sym2 M.V)) (e : Sym2 M.V) (ω : Config M.V) :
    flipDiff (cutFun S M.clusterVolSqReal) e ω
      ≤ (bigEdge M (cutConfig S (ω \ {e})) e).toReal := by
  have hfin : ∀ v : M.V, clusterVol (cutConfig S (ω \ {e})) v ≠ ⊤ :=
    fun v => clusterVol_cutConfig_ne_top S (ω \ {e}) v
  by_cases he : e ∈ S
  · have hsdiff : (cutConfig S ω) \ {e} = cutConfig S (ω \ {e}) := by
      ext a
      simp only [cutConfig, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3⟩, h2⟩
    have hid : flipDiff (cutFun S M.clusterVolSqReal) e ω
        = flipDiff M.clusterVolSqReal e (cutConfig S (ω \ {e})) := by
      rw [show flipDiff (cutFun S M.clusterVolSqReal) e ω
            = flipDiff M.clusterVolSqReal e (cutConfig S ω) by
        simp only [flipDiff, cutFun, cutConfig_forceOn_of_mem S he]]
      have hnotγ : e ∉ cutConfig S (ω \ {e}) := by
        intro h
        exact h.1.2 rfl
      have hsdiff' : cutConfig S ω \ {e} = cutConfig S (ω \ {e}) \ {e} := by
        rw [hsdiff, sdiff_singleton_of_notMem hnotγ]
      exact flipDiff_congr_sdiff M hsdiff'
    rw [hid]
    refine flipDiff_clusterVolSq_le_bigEdge M ?_ hfin
    exact fun h => h.1.2 rfl
  · rw [flipDiff_cutFun_eq_zero_of_notMem M S he]
    exact ENNReal.toReal_nonneg

/-! ## 4. The differentiating support -/

/-- **The support of the radius derivative** consists of genuine edges of length `≤ r`. -/
theorem exists_of_support (r : ℝ) {e : Sym2 M.V} (hs : M.cutEdgeDeriv r e ≠ 0) :
    ∃ x y : M.V, x ≠ y ∧ e = s(x, y) ∧ M.S.dist x y ≤ r := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      exact absurd (M.cutEdgeDeriv_loop r x) hs
    · refine ⟨x, y, hxy, rfl, ?_⟩
      by_contra h
      exact hs (by rw [M.cutEdgeDeriv_eq_coeffRHS_mul,
        M.cutEdgeClosedWeight_eq_zero_of_dist_gt (not_le.mp h), mul_zero])

/-! ## 5. The envelope -/

/-- `envelopeE` and its real-valued form `envelope` are defined in `Envelope/Defs.lean`.
On the differentiating support they reduce to the unexcluded ghost. -/
theorem envelopeE_eq_of_support (r : ℝ) (e : Sym2 M.V) (ω : Config M.V)
    (h : M.cutEdgeDeriv r e ≠ 0) :
    envelopeE M r e ω = unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e := by
  simp only [envelopeE, h, ite_false, add_zero]

/-- The envelope is nonnegative. -/
theorem envelope_nonneg (r : ℝ) (e : Sym2 M.V) (ω : Config M.V) :
    0 ≤ envelope M r e ω := ENNReal.toReal_nonneg

/-- The envelope is measurable in the configuration. -/
theorem measurable_envelopeE (r : ℝ) (e : Sym2 M.V) :
    Measurable fun ω : Config M.V => envelopeE M r e ω := by
  have h1 : Measurable fun ω : Config M.V => unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e :=
    (measurable_unexclEdgeWeight M r (0 : M.V) e).comp
      (PercLib.Probability.measurable_diff_singleton e)
  have h2 : Measurable fun ω : Config M.V =>
      (if M.cutEdgeDeriv r e = 0 then bigEdge M (ω \ {e}) e else 0) := by
    by_cases h : M.cutEdgeDeriv r e = 0
    · simp only [h, ite_true]
      exact (measurable_bigEdge M e).comp (PercLib.Probability.measurable_diff_singleton e)
    · simp only [h, ite_false]
      exact measurable_const
  exact h1.add h2

/-- The envelope is measurable as a real function. -/
theorem measurable_envelope (r : ℝ) (e : Sym2 M.V) :
    Measurable fun ω : Config M.V => envelope M r e ω :=
  ENNReal.measurable_toReal.comp (measurable_envelopeE M r e)

/-- The envelope is finite at a configuration with finite cluster volumes. -/
theorem envelopeE_ne_top (r : ℝ) (e : Sym2 M.V) (ω : Config M.V)
    (hfin : ∀ v : M.V, clusterVol (ω \ {e}) v ≠ ⊤) : envelopeE M r e ω ≠ ⊤ := by
  rw [envelopeE]
  refine ENNReal.add_ne_top.mpr ⟨unexclEdgeWeight_ne_top M r _ (0 : M.V) e hfin, ?_⟩
  by_cases h : M.cutEdgeDeriv r e = 0
  · rw [ite_eq_left h]
    exact bigEdge_ne_top M _ e hfin
  · rw [ite_eq_right h]
    exact ENNReal.zero_ne_top

/-- The envelope dominates the cubic merge majorant where the edge is not differentiated. -/
theorem bigEdge_toReal_le_envelope (r : ℝ) (e : Sym2 M.V) (ω : Config M.V)
    (h : M.cutEdgeDeriv r e = 0) (hfin : ∀ v : M.V, clusterVol (ω \ {e}) v ≠ ⊤) :
    (bigEdge M (ω \ {e}) e).toReal ≤ envelope M r e ω := by
  have hle : bigEdge M (ω \ {e}) e ≤ envelopeE M r e ω := by
    have h0 : bigEdge M (ω \ {e}) e
        ≤ unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e + bigEdge M (ω \ {e}) e :=
      self_le_add_left _ _
    simpa only [envelopeE, h, ite_true] using h0
  exact ENNReal.toReal_mono (envelopeE_ne_top M r e ω hfin) hle

/-! ## 6. The pointwise domination -/

/-- Closed configurations have finite cluster volumes. -/
theorem clusterVol_sdiff_ne_top {ω : Config M.V} (e : Sym2 M.V)
    (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) (v : M.V) : clusterVol (ω \ {e}) v ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin v) (clusterVol_mono (fun _ ha => Set.mem_of_mem_sdiff ha) v)

/-- **The untruncated increment is dominated by the envelope.** -/
theorem flipDiff_clusterVolSqReal_le_envelope (r : ℝ) {e : Sym2 M.V}
    (hs : M.cutEdgeDeriv r e ≠ 0) {ω : Config M.V} (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    flipDiff M.clusterVolSqReal e ω ≤ envelope M r e ω := by
  obtain ⟨x, y, hxy, rfl, hdist⟩ := exists_of_support M r hs
  have hfin' : ∀ v : M.V, clusterVol (ω \ {s(x, y)}) v ≠ ⊤ :=
    fun v => clusterVol_sdiff_ne_top M _ hfin v
  calc flipDiff M.clusterVolSqReal s(x, y) ω
      = (quadEdgeWeight (M.cutRange r) (ω \ {s(x, y)}) (0 : M.V) s(x, y)).toReal :=
        flipDiff_clusterVol_sq_eq_quadEdgeWeight_sdiff M r hxy hdist hfin
    _ ≤ (unexclEdgeWeight M r (ω \ {s(x, y)}) (0 : M.V) s(x, y)).toReal :=
        ENNReal.toReal_mono
          (unexclEdgeWeight_ne_top M r _ (0 : M.V) _ hfin')
          (quadEdgeWeight_le_unexclEdgeWeight M r _ (0 : M.V) _)
    _ = envelope M r s(x, y) ω := by
        rw [envelope, envelopeE_eq_of_support M r _ _ hs]

/-- **The windowed increment is dominated by the envelope** on the differentiating support. -/
theorem flipDiff_cutFun_le_envelope (r : ℝ) (S : Finset (Sym2 M.V)) {e : Sym2 M.V}
    (hs : M.cutEdgeDeriv r e ≠ 0) {ω : Config M.V} (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    flipDiff (cutFun S M.clusterVolSqReal) e ω ≤ envelope M r e ω := by
  obtain ⟨x, y, hxy, rfl, hdist⟩ := exists_of_support M r hs
  have hfin' : ∀ v : M.V, clusterVol (ω \ {s(x, y)}) v ≠ ⊤ :=
    fun v => clusterVol_sdiff_ne_top M _ hfin v
  by_cases he : s(x, y) ∈ S
  · rw [flipDiff_cutFun_clusterVolSqReal_eq M S r hxy hdist he ω]
    have h1 : quadEdgeWeight (M.cutRange r) (cutConfig S (ω \ {s(x, y)})) (0 : M.V) s(x, y)
        ≤ unexclEdgeWeight M r (ω \ {s(x, y)}) (0 : M.V) s(x, y) :=
      le_trans (quadEdgeWeight_le_unexclEdgeWeight M r _ (0 : M.V) _)
        (unexclEdgeWeight_mono M r (fun a ha => ha.1) (0 : M.V) _)
    have h2 : unexclEdgeWeight M r (ω \ {s(x, y)}) (0 : M.V) s(x, y) ≠ ⊤ :=
      unexclEdgeWeight_ne_top M r _ (0 : M.V) _ hfin'
    rw [envelope, envelopeE_eq_of_support M r _ _ hs]
    exact ENNReal.toReal_mono h2 h1
  · rw [flipDiff_cutFun_eq_zero_of_notMem M S he]
    exact envelope_nonneg M r _ ω

/-- **Almost-sure domination of the untruncated ghost**, for every edge. -/
theorem ae_abs_flipDiff_le_envelope (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (e : Sym2 M.V) :
    ∀ᵐ ω ∂(M.cutLaw r), |flipDiff M.clusterVolSqReal e ω| ≤ envelope M r e ω := by
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hfin
  have hnot : e ∉ ω \ {e} := by simp
  have hfin' : ∀ v : M.V, clusterVol (ω \ {e}) v ≠ ⊤ :=
    fun v => clusterVol_sdiff_ne_top M e hfin v
  have hcongr : flipDiff M.clusterVolSqReal e ω = flipDiff M.clusterVolSqReal e (ω \ {e}) :=
    (flipDiff_congr_sdiff M (sdiff_singleton_idem e ω)).symm
  by_cases hs : M.cutEdgeDeriv r e = 0
  · rw [hcongr,
      abs_of_nonneg (flipDiff_clusterVolSq_nonneg M hnot hfin')]
    calc flipDiff M.clusterVolSqReal e (ω \ {e})
        ≤ (bigEdge M (ω \ {e}) e).toReal := flipDiff_clusterVolSq_le_bigEdge M hnot hfin'
      _ ≤ envelope M r e ω := bigEdge_toReal_le_envelope M r e ω hs hfin'
  · have hs' : M.cutEdgeDeriv r e ≠ 0 := hs
    have hnonneg : 0 ≤ flipDiff M.clusterVolSqReal e (ω \ {e}) :=
      flipDiff_clusterVolSq_nonneg M hnot hfin'
    rw [hcongr, abs_of_nonneg hnonneg, ← hcongr]
    exact flipDiff_clusterVolSqReal_le_envelope M r hs' hfin

/-- **Almost-sure domination of the windowed ghost**, for every edge and every window. -/
theorem ae_abs_flipDiff_cutFun_le_envelope (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (S : ℕ → Finset (Sym2 M.V)) (n : ℕ) (e : Sym2 M.V) :
    ∀ᵐ ω ∂(M.cutLaw r),
      |flipDiff (cutFun (S n) M.clusterVolSqReal) e ω| ≤ envelope M r e ω := by
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hfin
  rw [abs_of_nonneg (M.flipDiff_cutFun_clusterVolSqReal_nonneg (S n) e ω)]
  by_cases hs : M.cutEdgeDeriv r e = 0
  · have hfin' : ∀ v : M.V, clusterVol (ω \ {e}) v ≠ ⊤ :=
      fun v => clusterVol_sdiff_ne_top M e hfin v
    calc flipDiff (cutFun (S n) M.clusterVolSqReal) e ω
        ≤ (bigEdge M (cutConfig (S n) (ω \ {e})) e).toReal :=
          flipDiff_cutFun_le_bigEdge M (S n) e ω
      _ ≤ (bigEdge M (ω \ {e}) e).toReal :=
          ENNReal.toReal_mono (bigEdge_ne_top M _ e hfin')
            (bigEdge_mono M (fun a ha => ha.1) e)
      _ ≤ envelope M r e ω := bigEdge_toReal_le_envelope M r e ω hs hfin'
  · exact flipDiff_cutFun_le_envelope M r (S n) hs hfin

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end
