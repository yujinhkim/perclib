/-
Translation transport of connection events at the native Bernoulli bond law, and root
independence of the second cluster moment.  Ultramath `smwpq441z` member m3.

These are the reusable inputs that let the `p = 4`, `k = 2` summation move the common
centre off the root.  Everything is derived from the *full* translation invariance
`hq : ∀ x y g, π s(x + g, y + g) = π s(x, y)` of the profile; nothing here is assumed
about `tau` alone.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Defs
public import PercLib.Percolation.Bond.Ergodic
public import PercLib.Percolation.Bond.Transport

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### Shifting an extended sum along the group -/

theorem tsum_add_right [AddGroup V] (f : V → ℝ≥0∞) (c : V) :
    (∑' b, f (b + c)) = ∑' b, f b :=
  Equiv.tsum_eq (Equiv.addRight c) f

theorem tsum_sub_right [AddGroup V] (f : V → ℝ≥0∞) (c : V) :
    (∑' b, f (b - c)) = ∑' b, f b := by
  simpa only [sub_eq_add_neg] using tsum_add_right f (-c)

theorem tsum_add_left [AddCommGroup V] (f : V → ℝ≥0∞) (c : V) :
    (∑' b, f (c + b)) = ∑' b, f b := by
  rw [show (fun b => f (c + b)) = (fun b => f (b + c)) from funext fun b => by rw [add_comm]]
  exact tsum_add_right f c

theorem tsum_sub_left [AddCommGroup V] (f : V → ℝ≥0∞) (c : V) :
    (∑' b, f (c - b)) = ∑' b, f b := by
  have h1 : (fun b : V => f (c - b)) = (fun b : V => f (c + -b)) := by
    funext b; rw [sub_eq_add_neg]
  have h2 : (fun b : V => f (c + -b)) = (fun b : V => f (c + (Equiv.neg V) b)) := rfl
  rw [h1, h2, Equiv.tsum_eq (Equiv.neg V) (fun b => f (c + b))]
  exact tsum_add_left f c

/-! ### Transport of connection events -/

/-- Translating both endpoints by `g` does not change the probability of the connection. -/
theorem law_conn_add [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y g : V) :
    law π (conn (x + g) (y + g)) = law π (conn x y) := by
  have hmp := measurePreserving_image_sym2Map_add π hq g
  have hpre : (fun ω : Config V => Sym2.map (· + g) '' ω) ⁻¹' conn (x + g) (y + g) =
      conn x y := preimage_conn_image (Equiv.addRight g) x y
  have h := hmp.measure_preimage ((measurableSet_conn (x + g) (y + g)).nullMeasurableSet)
  rw [hpre] at h
  exact h.symm

/-- **Two-point translation invariance.**  `tau π a c` depends only on the difference. -/
theorem tau_sub_eq [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a c : V) :
    tau π a c = tau π (a + -c) 0 := by
  have h : law π (conn (a + -c + c) (0 + c)) = law π (conn (a + -c) 0) :=
    law_conn_add π hq (a + -c) 0 c
  simpa [tau] using h

/-- Translation invariance of the two-point function in the form consumed by the
row/column-sum identities. -/
theorem tau_hinv [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∀ a b : V, tau π a b = tau π 0 (b - a) := by
  intro a b
  calc tau π a b = tau π (a + -b) 0 := tau_sub_eq π hq a b
    _ = tau π (0 + -(b - a)) 0 := by rw [show a + -b = 0 + -(b - a) from by abel]
    _ = tau π 0 (b - a) := (tau_sub_eq π hq 0 (b - a)).symm

/-- Row sums of the two-point function are the susceptibility. -/
theorem tau_row [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a : V) :
    (∑' b, tau π a b) = ∑' x, tau π 0 x :=
  tsum_row_eq (tau π) 0 (tau_hinv π hq) a

/-- Column sums of the two-point function are the susceptibility. -/
theorem tau_col [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b : V) :
    (∑' a, tau π a b) = ∑' x, tau π 0 x :=
  tsum_col_eq (tau π) 0 (tau_comm π) (tau_hinv π hq) b

/-! ### The second moment and its root independence -/

theorem jointP_comm (π : Sym2 V → unitInterval) (a b c : V) :
    jointP π a b c = jointP π b a c := by
  rw [jointP, jointP, inter_comm]

/-- The second moment as a double sum of joint connection probabilities. -/
theorem secondMoment_eq [Countable V] (π : Sym2 V → unitInterval) (v : V) :
    secondMoment π v = ∑' a, ∑' b, jointP π a b v := by
  rw [secondMoment, lintegral_cardFun_sq_eq]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [jointP, conn_symm v a, conn_symm v b]

/-- A joint connection probability with centre `c` depends only on the two differences. -/
theorem jointP_translate [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a b c : V) :
    jointP π a b c = jointP π (a + -c) (b + -c) 0 := by
  have hpre1 : (fun ω : Config V => Sym2.map (· + (-c)) '' ω) ⁻¹' conn (a + -c) 0 =
      conn a c := by
    have h := preimage_conn_image (Equiv.addRight (-c)) a c
    simpa using h
  have hpre2 : (fun ω : Config V => Sym2.map (· + (-c)) '' ω) ⁻¹' conn (b + -c) 0 =
      conn b c := by
    have h := preimage_conn_image (Equiv.addRight (-c)) b c
    simpa using h
  have hmp := measurePreserving_image_sym2Map_add π hq (-c)
  have hmeas : MeasurableSet (conn (a + -c) 0 ∩ conn (b + -c) 0) :=
    (measurableSet_conn _ _).inter (measurableSet_conn _ _)
  have h := hmp.measure_preimage hmeas.nullMeasurableSet
  have hsplit : (fun ω : Config V => Sym2.map (· + (-c)) '' ω) ⁻¹'
      (conn (a + -c) 0 ∩ conn (b + -c) 0) = conn a c ∩ conn b c := by
    rw [preimage_inter, hpre1, hpre2]
  rw [hsplit] at h
  rw [jointP, jointP]
  exact h

/-- **Root independence of the second cluster moment**, from full translation invariance. -/
theorem secondMoment_root_independent [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (v : V) :
    secondMoment π v = secondMoment π 0 := by
  rw [secondMoment_eq π v, secondMoment_eq π 0]
  rw [show (∑' a, ∑' b, jointP π a b v) =
      ∑' a, ∑' b, jointP π (a + -v) (b + -v) 0 from
    tsum_congr fun a => tsum_congr fun b => jointP_translate π hq a b v]
  rw [show (∑' a, ∑' b, jointP π (a + -v) (b + -v) 0) =
      ∑' a, ∑' b, jointP π (a + -v) b 0 from
    tsum_congr fun a => tsum_add_right (fun b => jointP π (a + -v) b 0) (-v)]
  rw [show (∑' a, ∑' b, jointP π (a + -v) b 0) = ∑' a, ∑' b, jointP π a b 0 from
    tsum_add_right (fun a => ∑' b, jointP π a b 0) (-v)]

/-- **Double-star at the root.**  Summing the joint connection probability over both free
endpoints and the common centre gives the native second moment, whatever the fixed vertex. -/
theorem tsum_jointP_centre [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (r : V) :
    (∑' c, ∑' q, jointP π r q c) = secondMoment π 0 := by
  rw [show (∑' c, ∑' q, jointP π r q c) = ∑' c, ∑' q, jointP π (r + -c) (q + -c) 0 from
    tsum_congr fun c => tsum_congr fun q => jointP_translate π hq r q c]
  rw [show (∑' c, ∑' q, jointP π (r + -c) (q + -c) 0) =
      ∑' c, ∑' q, jointP π (r + -c) q 0 from
    tsum_congr fun c => tsum_add_right (fun q => jointP π (r + -c) q 0) (-c)]
  rw [ENNReal.tsum_comm]
  have hshift : ∀ q : V, (∑' c, jointP π (r + -c) q 0) = ∑' c, jointP π c q 0 :=
    fun q => by simpa only [sub_eq_add_neg] using tsum_sub_left (fun c => jointP π c q 0) r
  rw [show (∑' q, ∑' c, jointP π (r + -c) q 0) = ∑' q, ∑' c, jointP π c q 0 from
    tsum_congr hshift]
  rw [show (∑' q, ∑' c, jointP π c q 0) = ∑' q, ∑' c, jointP π q c 0 from
    tsum_congr fun q => tsum_congr fun c => jointP_comm π c q 0]
  exact (secondMoment_eq π 0).symm

end PercLib.CriticalLRP.TreeExpansion.FivePoint
