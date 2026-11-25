/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The exhaustion objects: connectivity inside a prescribed set, and the two window volumes

Source: T. Hutchcroft, arXiv:2008.11197v2, proof of Theorem 2.3, final paragraph (the passage
from finite to infinite graphs).
-/
module

public import PercLib.CriticalLRP.Tightness.Exhaustion.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-- **Connectivity inside a prescribed vertex set.**  `PathIn A ω x y` says that `x` and `y` are
joined by a walk all of whose edges are open and all of whose vertices lie in `A`.  Taking
`A = univ` recovers the repository's `PathConnects`. -/
def PathIn (A : Set V) (ω : Config V) (x y : V) : Prop :=
  ∃ p : (⊤ : SimpleGraph V).Walk x y, (∀ e ∈ p.edges, e ∈ ω) ∧ ∀ z ∈ p.support, z ∈ A

lemma pathIn_mono {A B : Set V} (h : A ⊆ B) {ω : Config V} {x y : V} (hp : PathIn A ω x y) :
    PathIn B ω x y := by
  obtain ⟨p, he, hv⟩ := hp
  exact ⟨p, he, fun z hz => h (hv z hz)⟩

lemma pathConnects_of_pathIn {A : Set V} {ω : Config V} {x y : V} (hp : PathIn A ω x y) :
    PathConnects ω x y := by
  obtain ⟨p, he, _⟩ := hp
  exact ⟨p, he⟩

lemma connects_of_pathIn {A : Set V} {ω : Config V} {x y : V} (hp : PathIn A ω x y) :
    Connects ω x y :=
  pathConnects_iff.mp (pathConnects_of_pathIn hp)

/-- Every finite set of vertices is contained in some member of an exhaustion. -/
def Covers (A : ℕ → Set V) : Prop := ∀ s : Finset V, ∃ r, (s : Set V) ⊆ A r

/-- **A connection is a connection inside some member of the exhaustion.**  This is the only
geometric input of the limit passage: an open walk has finite vertex set. -/
lemma exists_pathIn_of_pathConnects {A : ℕ → Set V} (hcover : Covers A) {ω : Config V} {x y : V}
    (h : PathConnects ω x y) : ∃ r, PathIn (A r) ω x y := by
  classical
  obtain ⟨p, hp⟩ := h
  obtain ⟨r, hr⟩ := hcover p.support.toFinset
  refine ⟨r, p, hp, fun z hz => hr ?_⟩
  rw [Finset.mem_coe, List.mem_toFinset]
  exact hz

/-! ### The window volumes -/

/-- Number of vertices of the finite window `W` reachable from `u` by open paths staying in `A`. -/
noncomputable def vol (A : Set V) (ω : Config V) (u : V) (W : Finset V) : ℝ≥0∞ := by
  classical exact ((W.filter (fun y => PathIn A ω u y)).card : ℝ≥0∞)

/-- Number of vertices of the finite window `W` in the cluster of `u` (no restriction). -/
noncomputable def volFull (ω : Config V) (u : V) (W : Finset V) : ℝ≥0∞ := by
  classical exact ((W.filter (fun y => Connects ω u y)).card : ℝ≥0∞)

/-- The largest window volume over the window: `|K_max(W)|` for the restricted cluster. -/
noncomputable def maxVol (A : Set V) (ω : Config V) (W : Finset V) : ℝ≥0∞ :=
  W.sup (fun w => vol A ω w W)

/-- The largest window volume over the window, with unrestricted clusters. -/
noncomputable def maxVolFull (ω : Config V) (W : Finset V) : ℝ≥0∞ :=
  W.sup (fun w => volFull ω w W)

lemma vol_le_volFull (A : Set V) (ω : Config V) (u : V) (W : Finset V) :
    vol A ω u W ≤ volFull ω u W := by
  classical
  simp only [vol, volFull]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, connects_of_pathIn hy.2⟩

lemma vol_mono {A B : Set V} (h : A ⊆ B) (ω : Config V) (u : V) (W : Finset V) :
    vol A ω u W ≤ vol B ω u W := by
  classical
  simp only [vol]
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, pathIn_mono h hy.2⟩

lemma maxVol_mono {A B : Set V} (h : A ⊆ B) (ω : Config V) (W : Finset V) :
    maxVol A ω W ≤ maxVol B ω W := by
  classical
  refine Finset.sup_le (fun w hw => ?_)
  exact (vol_mono h ω w W).trans (Finset.le_sup (f := fun w => vol B ω w W) hw)

/-- **Eventual agreement.**  Along a monotone exhaustion covering `V`, the restricted window
volume eventually equals the true one. -/
lemma vol_eventually_eq {A : ℕ → Set V} (hmono : Monotone A) (hcover : Covers A) (ω : Config V)
    (u : V) (W : Finset V) : ∃ R, vol (A R) ω u W = volFull ω u W := by
  classical
  have hex : ∀ y : V, Connects ω u y → ∃ r, PathIn (A r) ω u y :=
    fun y hy => exists_pathIn_of_pathConnects hcover (pathConnects_iff.mpr hy)
  let rho : V → ℕ := fun y => if h : Connects ω u y then Classical.choose (hex y h) else 0
  refine ⟨W.sup rho, ?_⟩
  have hiff : ∀ y ∈ W, PathIn (A (W.sup rho)) ω u y ↔ Connects ω u y := by
    intro y hy
    constructor
    · exact connects_of_pathIn
    · intro hc
      have hy' : PathIn (A (rho y)) ω u y := by
        simp only [rho, dite_eq_left hc]
        exact Classical.choose_spec (hex y hc)
      exact pathIn_mono (hmono (Finset.le_sup (f := rho) hy)) hy'
  have hfilter : W.filter (fun y => PathIn (A (W.sup rho)) ω u y)
      = W.filter (fun y => Connects ω u y) :=
    Finset.filter_congr (fun y hy => hiff y hy)
  simp only [vol, volFull, hfilter]

/-- Eventual agreement of the window maxima. -/
lemma maxVol_eventually_eq {A : ℕ → Set V} (hmono : Monotone A) (hcover : Covers A) (ω : Config V)
    (W : Finset V) : ∃ R, maxVol (A R) ω W = maxVolFull ω W := by
  classical
  have hex : ∀ w : V, ∃ r, vol (A r) ω w W = volFull ω w W :=
    fun w => vol_eventually_eq hmono hcover ω w W
  let rho : V → ℕ := fun w => Classical.choose (hex w)
  refine ⟨W.sup rho, ?_⟩
  have hterm : ∀ w ∈ W, vol (A (W.sup rho)) ω w W = volFull ω w W := by
    intro w hw
    have hspec : vol (A (rho w)) ω w W = volFull ω w W := Classical.choose_spec (hex w)
    refine le_antisymm (vol_le_volFull _ _ w W) ?_
    calc volFull ω w W = vol (A (rho w)) ω w W := hspec.symm
      _ ≤ vol (A (W.sup rho)) ω w W := vol_mono (hmono (Finset.le_sup (f := rho) hw)) ω w W
  exact Finset.sup_congr rfl hterm

end Exhaustion

end PercLib.CriticalLRP
