/-
Swarm `smwxk27m7`, member `m2`, direction (A) `SOCKET-ORDER-TO-SHAPE-BOUNDS`.

Definitions for the socket-order-to-shape-bound step of the `p = 5`, `k = 2` critical
long-range percolation moment (`Lemma I.4.16`).

The accepted inputs are

* `SixPoint.SplitEval2.RootSocket`: fifteen socket evaluations, one for each split position
  `j : Fin 7` and each of the two pattern root sockets (`b₀` held and `b₂` held); each is a
  sevenfold nested `tsum` of the five-factor product `slotProd2 π j i₁ i₂ b₀ b₁ b₂ b₃ b₄ t`
  (five comb terminals plus the two interior vertices `i₁, i₂`), and each returns the monomial
  `monomial2 π 0 = (E|K|²)²(E|K|)³`;
* `SixPoint.SplitEval.Bridge`: the event-level union bounds at the split positions
  `j = 0, 5, 6`, plus `SixPoint.SplitPattern.combSystem_twoJointThree_one` at `j = 1`;
* `SixPoint.K2Mass.shapeTotal`: the mass of one six-terminal shape event, five non-root
  terminals summed.

The shape masses are indexed by a *labelled pattern* `k : Fin 15`; the root of the moment sits
in comb slot `0` for the twelve patterns with `pat k 0 = 0` and in comb slot `2` for the other
three (`patSlot2 = 0`).  Fixing the root at the basepoint `0` therefore produces exactly two
kinds of shape mass, and this file gives them their own names:

* `massSlot0` — root `0` in comb slot `0`, so the five summed terminals are
  `b₁, b₂, b₃, b₄, t`;
* `massSlot2` — root `0` in comb slot `2`, so the five summed terminals are
  `b₀, b₁, b₃, b₄, t`.

`slotOne`/`prodOne` supply the missing `j = 1` slot diagram (the `b₀ ↔ b₁` mirror of
`SplitEval.prodZero`), in the literal factor order of the certificate
`combSystem_twoJointThree_one`.

Finally the eight index permutations `perm*` record, for each of the eight off-middle
`(split, root socket)` pairs treated here, in which of the seven nested positions of the
*shape* sum each of the seven nested positions of the *socket* sum sits.  They are pure
reindexings of a nonnegative extended sum (`ENNReal.tsum_comm` in disguise,
`SixPoint.TwoJointEval.tsum_seven_perm` in practice): they carry no mathematical content and
assume nothing about `V` or `π`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation.Bridge
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.RootSocket.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvents.Certificates
public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.RootCollapse.Main

/-!
# Shape masses at the two canonical root sockets, and the missing `j = 1` slot diagram

Definitions only.  The bound theorems are in `Main.lean`.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval3

set_option linter.style.longLine false
set_option linter.style.setOption false

variable {V : Type*}

/-! ## The two canonical root-socket shape masses at the basepoint `0` -/

/-- **Root in comb slot `0`.**  The five summed terminals are `y = b₁`, `z = b₂`, `w = b₃`,
`q = b₄`, `r = t`, exactly as `K2Mass.shapeMass π 0 patSlot0 j` reads them; the four internal
witnesses `c, u, v, w'` stay summed *inside* the measure.  No hypothesis on `V` or `π`. -/
noncomputable def massSlot0 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    ℝ≥0∞ :=
  law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω : PercLib.CriticalLRP.Config V |
      CombSystem (PercLib.CriticalLRP.openGraph ω) x y z w q r u v w' c j})

/-- **Root in comb slot `2`.**  The five summed terminals are `y = b₀`, `z = b₁`, `w = b₃`,
`q = b₄`, `r = t` and the held root is `b₂ = 0`. -/
noncomputable def massSlot2 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    ℝ≥0∞ :=
  law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω : PercLib.CriticalLRP.Config V |
      CombSystem (PercLib.CriticalLRP.openGraph ω) y z x w q r u v w' c j})

/-- The bare shape event whose mass `massSlot0` is; exposed so that the union bounds of
`SplitEval.Bridge` can be applied to it. -/
def evSlot0 (x : V) (j : Fin 7) (y z w q r : V) : Set (PercLib.CriticalLRP.Config V) :=
  ⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω | CombSystem (PercLib.CriticalLRP.openGraph ω) x y z w q r u v w' c j}

/-- The `patSlot2` analogue of `evSlot0`. -/
def evSlot2 (x : V) (j : Fin 7) (y z w q r : V) : Set (PercLib.CriticalLRP.Config V) :=
  ⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
    {ω | CombSystem (PercLib.CriticalLRP.openGraph ω) y z x w q r u v w' c j}

theorem massSlot0_def (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    massSlot0 π x j y z w q r = law π (evSlot0 x j y z w q r) :=
  rfl

theorem massSlot2_def (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (y z w q r : V) :
    massSlot2 π x j y z w q r = law π (evSlot2 x j y z w q r) :=
  rfl

/-! ## The `j = 1` slot diagram

`SixPoint.SplitEval` supplies the slot diagrams at `j = 0, 5, 6` only; production supplies the
event-level certificate at `j = 1` (`SplitPattern.combSystem_twoJointThree_one`: the star at `u`
with leaves `b₀, c, v`, the star at `w` with leaves `b₃, b₄, v`, and the three residual edges
`b₂ — v`, `b₁ — c`, `t — c`).  The two definitions below are that certificate's fivefold BK
product in the `jointP`/`tau` vocabulary, in the certificate's own factor order. -/

/-- **The `j = 1` two-joint product**, in the literal factor order of
`combSystem_twoJointThree_one`. -/
noncomputable def prodOne (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t v c : V) : ℝ≥0∞ :=
  jointP π b0 c v * (jointP π b3 b4 v * (tau π b2 v * (tau π b1 c * tau π t c)))

/-- **The `j = 1` slot**: the two free vertices `v, c` summed in the union-bound order. -/
noncomputable def slotOne (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  ∑' c, ∑' v, prodOne π b0 b1 b2 b3 b4 t v c

/-! ## The eight index permutations

Each is a permutation of `Fin 7` given by a literal tuple; `σ i` is the position, in the
socket-order sevenfold sum of `RootSocket`, of the `i`-th variable of the shape-order sevenfold
sum.  Written as structure literals so that `σ i` is *definitionally* the corresponding
numeral, which is what lets `TwoJointEval.tsum_seven_perm` be applied by unification. -/

/-- `j = 0`, root socket `b₀`: shape order `(b₁,b₂,b₃,b₄,t,c,v)`, socket order
`(c,t,v,b₁,b₂,b₃,b₄)`.  Declared `reducible` so that `permZero0 i` is definitionally the
corresponding numeral, which is what lets `TwoJointEval.tsum_seven_perm` be applied directly. -/
@[reducible] def permZero0 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![3, 4, 5, 6, 1, 0, 2] i
  invFun := fun i => ![5, 4, 6, 0, 1, 2, 3] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 0`, root socket `b₂`: shape order `(b₀,b₁,b₃,b₄,t,c,v)`, socket order
`(v,b₁,c,t,b₀,b₃,b₄)`. -/
@[reducible] def permZero2 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![4, 1, 5, 6, 3, 2, 0] i
  invFun := fun i => ![6, 1, 5, 4, 0, 2, 3] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 1`, root socket `b₀`: socket order `(v,c,b₁,t,b₂,b₃,b₄)`. -/
@[reducible] def permOne0 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![2, 4, 5, 6, 3, 1, 0] i
  invFun := fun i => ![6, 5, 0, 4, 1, 2, 3] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 1`, root socket `b₂`: socket order `(v,b₀,c,t,b₁,b₃,b₄)`. -/
@[reducible] def permOne2 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![1, 4, 5, 6, 3, 2, 0] i
  invFun := fun i => ![6, 0, 5, 4, 1, 2, 3] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 5`, root socket `b₀`: socket order `(c,b₁,t,w,b₂,b₄,b₃)`. -/
@[reducible] def permFive0 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![1, 4, 6, 5, 2, 0, 3] i
  invFun := fun i => ![5, 0, 4, 6, 1, 3, 2] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 5`, root socket `b₂`: socket order `(w,c,t,b₀,b₁,b₄,b₃)`. -/
@[reducible] def permFive2 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![3, 4, 6, 5, 2, 1, 0] i
  invFun := fun i => ![6, 5, 4, 0, 1, 3, 2] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 6`, root socket `b₀`: socket order `(v,b₁,b₂,w,t,b₄,b₃)`. -/
@[reducible] def permSix0 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![1, 2, 6, 5, 4, 0, 3] i
  invFun := fun i => ![5, 0, 1, 6, 4, 3, 2] i
  left_inv := by decide
  right_inv := by decide

/-- `j = 6`, root socket `b₂`: socket order `(v,b₀,b₁,w,t,b₄,b₃)`; the same permutation as
`permSix0`. -/
@[reducible] def permSix2 : Equiv.Perm (Fin 7) where
  toFun := fun i => ![1, 2, 6, 5, 4, 0, 3] i
  invFun := fun i => ![5, 0, 1, 6, 4, 3, 2] i
  left_inv := by decide
  right_inv := by decide

end PercLib.CriticalLRP.SixPoint.SplitEval3
