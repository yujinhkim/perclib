/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwtrtcqs`, member `m8`, direction D7.

The same logarithmic-integrability conclusion at the *plain lattice* open-triangle tail
`PercLib.CriticalLRP.TriTail.openTriangleTail`, which uses the `ℓ^∞` norm `FiniteVolume.linfNorm`
rather than a general `SourceNormData` norm.  This file is the reusable non-model version: it does
not depend on `Orchestration` at all, so a module that only imports `TriTail` can consume it.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTailCore
public import PercLib.CriticalLRP.Analysis.TriTail

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.TriTail

/-- The lattice open-triangle tail is the norm-agnostic radial tail supremum at the `ℓ^∞` distance:
definitionally, with no transfer lemma needed. -/
theorem openTriangleTail_eq_radialTailSup {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (r : ℝ) :
    openTriangleTail J hJ β r =
      Analysis.radialTailSup (fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x)
        (fun x : Fin d → ℤ => openTriangle J hJ β 0 x) r :=
  rfl

/-- **Lemma I.4.3 at the plain lattice tail.**  If the open triangle decays at every point of
positive `ℓ^∞` norm like `C * (log (1 + ‖x‖)) ^ (-p)` with `p > 1`, then the lattice tail
`∇_r` is a logarithmically integrable error function.  Nothing about `x = 0` is needed: the tail at
radius `r > 0` never contains it (`latticeDist 0 0 = 0`). -/
theorem isLogErrorFunction_openTriangleTail {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x)
      (fun x : Fin d → ℤ => openTriangle J hJ β 0 x) C p) :
    Analysis.IsLogErrorFunction (fun r => (openTriangleTail J hJ β r).toReal) := by
  have := Analysis.isLogErrorFunction_radialTailSup (nrm := fun x : Fin d → ℤ =>
    FiniteVolume.latticeDist 0 x) (F := fun x : Fin d → ℤ => openTriangle J hJ β 0 x) hC hp hF
  simpa only [openTriangleTail_eq_radialTailSup] using this

end PercLib.CriticalLRP.TriTail
