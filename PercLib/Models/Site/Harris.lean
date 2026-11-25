/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New site-percolation corollaries of PercLib's canonical Bernoulli Harris inequality
and monotone coupling. Uses the existing D-3 definitions; no upstream proof copied.
-/
module

public import PercLib.Models.Site.Basic
public import PercLib.Probability.Harris
public import PercLib.Probability.Cylinder
public import PercLib.Probability.Coupling.Monotone

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Models.Site
variable {V : Type*}

/-- Opening more vertices can only add open edges. -/
theorem openSiteGraph_mono (G : SimpleGraph V) : Monotone (openSiteGraph G) := by
  intro ω η h x y hxy
  obtain ⟨hG, hx, hy⟩ := (openSiteGraph_adj_iff' G ω x y).mp hxy
  exact (openSiteGraph_adj_iff' G η x y).mpr ⟨hG, h hx, h hy⟩

/-- A site connection remains a connection after opening vertices. -/
theorem isUpperSet_siteConn (G : SimpleGraph V) (x y : V) : IsUpperSet (siteConn G x y) :=
  fun _ _ h hc => ⟨h hc.1, hc.2.mono (openSiteGraph_mono G h)⟩

theorem isUpperSet_siteConnSet (G : SimpleGraph V) (x : V) (A : Set V) :
    IsUpperSet (siteConnSet G x A) :=
  isUpperSet_iUnion₂ (fun y _ => isUpperSet_siteConn G x y)

theorem siteCluster_mono (G : SimpleGraph V) {ω η : SiteConfig V} (h : ω ⊆ η) (x : V) :
    siteCluster G ω x ⊆ siteCluster G η x :=
  fun _ hy => isUpperSet_siteConn G x _ h hy

theorem isUpperSet_siteInfinite (G : SimpleGraph V) (x : V) :
    IsUpperSet {ω | (siteCluster G ω x).Infinite} :=
  fun _ _ h hi => hi.mono (siteCluster_mono G h x)

/-- Site connections compose, including the required open starting vertex. -/
theorem siteConn_trans (G : SimpleGraph V) {ω : SiteConfig V} {x y z : V}
    (hxy : ω ∈ siteConn G x y) (hyz : ω ∈ siteConn G y z) : ω ∈ siteConn G x z :=
  ⟨hxy.1, hxy.2.trans hyz.2⟩

theorem siteConn_symm (G : SimpleGraph V) {ω : SiteConfig V} {x y : V}
    (hxy : ω ∈ siteConn G x y) : ω ∈ siteConn G y x :=
  ⟨mem_of_mem_siteCluster G ω hxy, hxy.2.symm⟩

/-- Connected open roots have the same cluster. -/
theorem siteCluster_eq_of_conn (G : SimpleGraph V) {ω : SiteConfig V} {x y : V}
    (hxy : ω ∈ siteConn G x y) : siteCluster G ω x = siteCluster G ω y := by
  ext z
  exact ⟨siteConn_trans G (siteConn_symm G hxy), siteConn_trans G hxy⟩

/-- Harris association for any two site-connection events. -/
theorem siteBernoulli_harris_siteConn [Countable V] (G : SimpleGraph V)
    (w : V → unitInterval) (x y u v : V) :
    siteBernoulli w (siteConn G x y) * siteBernoulli w (siteConn G u v) ≤
      siteBernoulli w (siteConn G x y ∩ siteConn G u v) :=
  prodBernoulli_harris w (isUpperSet_siteConn G x y) (isUpperSet_siteConn G u v)
    (measurableSet_siteConn G x y) (measurableSet_siteConn G u v)

/-- Harris association also applies to infinite site clusters. -/
theorem siteBernoulli_harris_siteInfinite [Countable V] (G : SimpleGraph V)
    (w : V → unitInterval) (x y : V) :
    siteBernoulli w {ω | (siteCluster G ω x).Infinite} *
      siteBernoulli w {ω | (siteCluster G ω y).Infinite} ≤
      siteBernoulli w {ω | (siteCluster G ω x).Infinite ∧ (siteCluster G ω y).Infinite} :=
  prodBernoulli_harris w (isUpperSet_siteInfinite G x) (isUpperSet_siteInfinite G y)
    (measurableSet_siteInfinite G x) (measurableSet_siteInfinite G y)

/-- Supermultiplicativity follows from Harris and transitivity. -/
theorem siteBernoulli_siteConn_mul_le [Countable V] (G : SimpleGraph V)
    (w : V → unitInterval) (x y z : V) :
    siteBernoulli w (siteConn G x y) * siteBernoulli w (siteConn G y z) ≤
      siteBernoulli w (siteConn G x z) :=
  (siteBernoulli_harris_siteConn G w x y y z).trans
    (measure_mono (fun _ h => siteConn_trans G h.1 h.2))

/-- A connection transfers an infinite cluster between its two open roots. -/
theorem siteBernoulli_siteConn_mul_infinite_le [Countable V] (G : SimpleGraph V)
    (w : V → unitInterval) (x y : V) :
    siteBernoulli w (siteConn G x y) * siteBernoulli w {ω | (siteCluster G ω x).Infinite} ≤
      siteBernoulli w {ω | (siteCluster G ω y).Infinite} := by
  refine (prodBernoulli_harris w (isUpperSet_siteConn G x y) (isUpperSet_siteInfinite G x)
    (measurableSet_siteConn G x y) (measurableSet_siteInfinite G x)).trans (measure_mono ?_)
  intro ω h
  change (siteCluster G ω y).Infinite
  have hi := h.2
  change (siteCluster G ω x).Infinite at hi
  simpa only [← siteCluster_eq_of_conn G h.1] using hi

/-- Self-connection has probability w(x), not one. -/
theorem siteBernoulli_siteConn_self (G : SimpleGraph V) (w : V → unitInterval) (x : V) :
    siteBernoulli w (siteConn G x x) = (unitInterval.toNNReal (w x) : ℝ≥0∞) := by
  rw [siteConn_self]
  exact prodBernoulli_setOf_mem w x

/-- General profile monotonicity for increasing measurable site events. -/
theorem siteBernoulli_mono_event [Countable V] (w w' : V → unitInterval) (h : w ≤ w')
    {A : Set (SiteConfig V)} (hA : MeasurableSet A) (hup : IsUpperSet A) :
    siteBernoulli w A ≤ siteBernoulli w' A :=
  prodBernoulli_mono_event w w' h hA hup

theorem monotone_thetaSiteOn [Countable V] (G : SimpleGraph V) (x : V) :
    Monotone (thetaSiteOn G x) := by
  intro p q hpq
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact siteBernoulli_mono_event _ _ (fun _ => hpq)
    (measurableSet_siteInfinite G x) (isUpperSet_siteInfinite G x)

theorem monotone_thetaSite (d : ℕ) : Monotone (thetaSite d) :=
  monotone_thetaSiteOn (zdGraph d) 0

/-- Below the capped infimum, the infinite-cluster probability is zero. -/
theorem thetaSite_eq_zero_of_lt_critical (d : ℕ) (p : unitInterval)
    (h : (p : ℝ) < criticalProbSite d) : thetaSite d p = 0 := by
  apply le_antisymm _ ENNReal.toReal_nonneg
  by_contra hn
  have hp : 0 < thetaSite d p := lt_of_not_ge hn
  have hc : criticalProbSite d ≤ (p : ℝ) :=
    csInf_le ⟨0, criticalProbSite_nonneg_mem d⟩ (Or.inl ⟨p.property, hp⟩)
  exact (not_lt_of_ge hc) h

/-- Above the capped infimum, positivity propagates from a smaller percolating parameter.
The adjoined endpoint 1 cannot provide a spurious witness below p≤1. -/
theorem thetaSite_pos_of_critical_lt (d : ℕ) (p : unitInterval)
    (h : criticalProbSite d < (p : ℝ)) : 0 < thetaSite d p := by
  obtain ⟨r, hr, hrp⟩ := exists_lt_of_csInf_lt (show
    ({r : ℝ | ∃ hr : r ∈ unitInterval, 0 < thetaSite d ⟨r, hr⟩} ∪ {1}).Nonempty from
      ⟨1, Or.inr rfl⟩) h
  rcases hr with ⟨hr, hpos⟩ | hr
  · exact hpos.trans_le (monotone_thetaSite d (show (⟨r, hr⟩ : unitInterval) ≤ p from hrp.le))
  · have : r = 1 := hr
    subst r
    exact (not_lt_of_ge p.property.2 hrp).elim

-- Every zero-profile connection has probability zero, including self-connections.
example (G : SimpleGraph V) (x y : V) :
    siteBernoulli (fun _ : V => 0) (siteConn G x y) = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ siteBernoulli (fun _ : V => 0) {ω | x ∈ ω} := measure_mono (fun _ h => h.1)
    _ = 0 := by simp [siteBernoulli, prodBernoulli_setOf_mem]

/-- For adjacent vertices, opening both endpoints is necessary and sufficient. -/
theorem siteBernoulli_siteConn_of_adj (G : SimpleGraph V) (w : V → unitInterval)
    {x y : V} (h : G.Adj x y) :
    siteBernoulli w (siteConn G x y) =
      (unitInterval.toNNReal (w x) : ℝ≥0∞) * (unitInterval.toNNReal (w y) : ℝ≥0∞) := by
  classical
  have heq : siteConn G x y = {ω : Set V | (↑({x,y} : Finset V) : Set V) ⊆ ω} := by
    ext ω
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_ofPred_eq,
      Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨fun hc => siteConn_subset G x y hc, fun hω => siteConn_of_adj G h hω.1 hω.2⟩
  rw [heq]
  simpa [siteBernoulli, h.ne] using prodBernoulli_subset w ({x,y} : Finset V)

-- On two vertices at p=1/2, the supermultiplicative bound can be strict.
example :
    let p : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    siteBernoulli (fun _ : Bool => p) (siteConn ⊤ false true) *
      siteBernoulli (fun _ : Bool => p) (siteConn ⊤ true false) <
      siteBernoulli (fun _ : Bool => p) (siteConn ⊤ false false) := by
  dsimp
  rw [siteBernoulli_siteConn_of_adj ⊤ _ (by simp),
    siteBernoulli_siteConn_of_adj ⊤ _ (by simp), siteBernoulli_siteConn_self]
  simp only [← ENNReal.coe_mul, ENNReal.coe_lt_coe]
  change ((1 / 2 : ℝ≥0) * (1 / 2)) * ((1 / 2) * (1 / 2)) < 1 / 2
  norm_num

end PercLib.Models.Site
